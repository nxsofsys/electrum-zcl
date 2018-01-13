#!/usr/bin/env python
#
# Electrum - lightweight Bitcoin client
# Copyright (C) 2012 thomasv@ecdsa.org
#
# Permission is hereby granted, free of charge, to any person
# obtaining a copy of this software and associated documentation files
# (the "Software"), to deal in the Software without restriction,
# including without limitation the rights to use, copy, modify, merge,
# publish, distribute, sublicense, and/or sell copies of the Software,
# and to permit persons to whom the Software is furnished to do so,
# subject to the following conditions:
#
# The above copyright notice and this permission notice shall be
# included in all copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
# EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
# MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
# NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS
# BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN
# ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
# CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
# SOFTWARE.



import os
import util
import threading
import struct
from io import BytesIO

import bitcoin
from bitcoin import *
from equihash import is_gbp_valid
import logging
logging.basicConfig(level=logging.INFO)

MAX_TARGET = 0x00000FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF

def serialize_header(res):
    r = ""
    r += struct.pack("<i", res.get('version'))
    r += ser_uint256(res.get('prev_block_hash'))
    r += ser_uint256(res.get('merkle_root'))
    r += ser_uint256(res.get('hash_reserved'))
    r += struct.pack("<i", res.get('timestamp'))
    r += struct.pack("<i", res.get('bits'))
    r += ser_uint256(res.get('nonce'))
    r += ser_char_vector(res.get('n_solution'))
    return r


def deserialize_header(s, height):
    f = BytesIO(s)
    h = {}
    h['version'] = struct.unpack("<i", f.read(4))[0]
    h['prev_block_hash'] = hash_encode(f.read(32))
    h['merkle_root'] = hash_encode(f.read(32))
    f.read(32)
    h['timestamp'] = struct.unpack("<I", f.read(4))[0]
    h['bits'] = struct.unpack("<I", f.read(4))[0]
    h['nonce'] = hash_encode(f.read(32))
    h['block_height'] = height
    return h

blockchains = {}

def read_blockchains(config):
    blockchains[0] = Blockchain(config, 0, None)
    fdir = os.path.join(util.get_headers_dir(config), 'forks')
    if not os.path.exists(fdir):
        os.mkdir(fdir)
    l = filter(lambda x: x.startswith('fork_'), os.listdir(fdir))
    l = sorted(l, key = lambda x: int(x.split('_')[1]))
    for filename in l:
        checkpoint = int(filename.split('_')[2])
        parent_id = int(filename.split('_')[1])
        b = Blockchain(config, checkpoint, parent_id)
        blockchains[b.checkpoint] = b
    return blockchains

def check_header(header):
    if type(header) is not dict:
        return False
    for b in blockchains.values():
        if b.check_header(header):
            return b
    return False

def can_connect(header):
    for b in blockchains.values():
        if b.can_connect(header):
            return b
    return False


class Blockchain(util.PrintError):

    '''Manages blockchain headers and their verification'''

    def __init__(self, config, checkpoint, parent_id):
        self.config = config
        self.catch_up = None # interface catching up
        self.checkpoint = checkpoint
        self.parent_id = parent_id
        self.lock = threading.Lock()
        with self.lock:
            self.update_size()

    def parent(self):
        return blockchains[self.parent_id]

    def get_max_child(self):
        children = filter(lambda y: y.parent_id==self.checkpoint, blockchains.values())
        return max([x.checkpoint for x in children]) if children else None

    def get_checkpoint(self):
        mc = self.get_max_child()
        return mc if mc is not None else self.checkpoint

    def get_branch_size(self):
        return self.height() - self.get_checkpoint() + 1

    def get_name(self):
        return self.get_hash(self.get_checkpoint()).lstrip('00')[0:10]

    def check_header(self, header):
        header_hash = self.hash_header(header)
        height = header.get('block_height')
        return header_hash == self.get_hash(height)

    def fork(parent, header):
        checkpoint = header.get('block_height')
        self = Blockchain(parent.config, checkpoint, parent.checkpoint)
        open(self.path(), 'w+').close()
        self.save_header(header)
        return self

    def height(self):
        return self.checkpoint + self.size() - 1

    def size(self):
        with self.lock:
            return self._size

    def update_size(self):
        p = self.path()
        self._size = 0
        if os.path.exists(p):
            f = open(p, 'rb')
            f.seek(-1, 2)
            eof = f.tell()
            f.seek(0, 0)
            while True:
                try:
                    f.seek(140, 1)
                    vs = read_vector_size(f)
                    f.seek(vs, 1)
                    if f.tell() < eof:
                        self._size += 1
                except:
                    break

            print(f.tell(), eof, self._size)
            f.close()

    def verify_header(self, header, prev_header, bits, target, nonce, n_solution):
        prev_hash = self.hash_header(prev_header)
        _powhash = uint256_from_str(self.sha256_header(header))
        if prev_hash != header.get('prev_block_hash'):
            raise BaseException("prev hash mismatch: %s vs %s" % (prev_hash, header.get('prev_block_hash')))
        if bitcoin.TESTNET:
            return
        if bits != header.get('bits'):
            raise BaseException("bits mismatch: %s vs %s for height %s" % (bits, header.get('bits'), header.get('block_height')))
        if int('0x' + _powhash, 16) > target:
            raise BaseException("insufficient proof of work: %s vs target %s" % (int('0x' + _powhash, 16), target))
        if not is_gbp_valid(nonce, n_solution):
            raise BaseException("Equihash invalid")

    @util.profiler
    def verify_chunk(self, index, data):
        num = len(data) / 1484
        prev_header = None
        if index != 0:
            prev_header = self.read_header(index*2016 - 1)
        headers = {}
        for i in range(num):
            raw_header = data[i*1484:(i+1) * 1484]
            header = self.deserialize_header(raw_header, index*2016 + i)
            headers[header.get('block_height')] = header
            nonce, n_solution = headers.get('nonce'), header.get('n_solution')
            bits, target = self.get_target(index*2016 + i, headers)
            self.verify_header(header, prev_header, bits, target, nonce, n_solution)
            prev_header = header

    def serialize_header(self, res):
        print res
        r = ""
        r += struct.pack("<i", res.get('version'))
        r += hash_decode(res.get('prev_block_hash'))
        r += hash_decode(res.get('merkle_root'))
        r += '\x00' * 32 # hash_reserved
        r += struct.pack("<I", res.get('timestamp'))
        r += struct.pack("<I", res.get('bits'))
        r += hash_decode(res.get('nonce'))
        r += ser_char_vector("")
        return r

    def deserialize_header(self, s, height):
        hex_to_int = lambda s: int('0x' + s[::-1].encode('hex'), 16)
        f = BytesIO(s)
        h = {}
        h['version'] = struct.unpack("<I", f.read(4))[0]
        h['prev_block_hash'] = deser_uint256(f)
        h['merkle_root'] = deser_uint256(f)
        h['hash_reserved'] = deser_uint256(f)
        h['timestamp'] = struct.unpack("<I", f.read(4))[0]
        h['bits'] = struct.unpack("<I", f.read(4))[0]
        h['nonce'] = struct.unpack("<I", f.read(4))[0]
        h['n_solution'] = deser_char_vector(f)
        h['block_height'] = height
        return h

    def sha256_header(self, header):
        return uint256_from_str(Hash(self.serialize_header(header)))

    def hash_header(self, header):
        if header is None:
            return '0' * 64 
        return hash_encode(self.serialize_header(header))

    def path(self):
        d = util.get_headers_dir(self.config)
        filename = 'blockchain_headers' if self.parent_id is None else os.path.join('forks', 'fork_%d_%d'%(self.parent_id, self.checkpoint))
        return os.path.join(d, filename)

    def save_chunk(self, index, chunk):
        filename = self.path()
        d = (index * 2016 - self.checkpoint) * 1484
        if d < 0:
            chunk = chunk[-d:]
            d = 0
        self.write(chunk, d)
        self.swap_with_parent()

    def swap_with_parent(self):
        if self.parent_id is None:
            return
        parent_branch_size = self.parent().height() - self.checkpoint + 1
        if parent_branch_size >= self.size():
            return
        self.print_error("swap", self.checkpoint, self.parent_id)
        parent_id = self.parent_id
        checkpoint = self.checkpoint
        parent = self.parent()
        with open(self.path(), 'rb') as f:
            my_data = f.read()
        with open(parent.path(), 'rb') as f:
            f.seek((checkpoint - parent.checkpoint)*1484)
            parent_data = f.read(parent_branch_size*1484)
        self.write(parent_data, 0)
        parent.write(my_data, (checkpoint - parent.checkpoint)*1484)
        # store file path
        for b in blockchains.values():
            b.old_path = b.path()
        # swap parameters
        self.parent_id = parent.parent_id; parent.parent_id = parent_id
        self.checkpoint = parent.checkpoint; parent.checkpoint = checkpoint
        self._size = parent._size; parent._size = parent_branch_size
        # move files
        for b in blockchains.values():
            if b in [self, parent]: continue
            if b.old_path != b.path():
                self.print_error("renaming", b.old_path, b.path())
                os.rename(b.old_path, b.path())
        # update pointers
        blockchains[self.checkpoint] = self
        blockchains[parent.checkpoint] = parent

    def write(self, data, offset):
        filename = self.path()
        with self.lock:
            with open(filename, 'rb+') as f:
                if offset != self._size*1484:
                    f.seek(offset)
                    f.truncate()
                f.seek(offset)
                f.write(data)
                f.flush()
                os.fsync(f.fileno())
            self.update_size()

    def save_header(self, header):
        delta = header.get('block_height') - self.checkpoint
        data = serialize_header(header).decode('hex')
        assert delta == self.size()
        assert len(data) == 1484
        self.write(data, delta*1484)
        self.swap_with_parent()

    def read_header(self, height):
        assert self.parent_id != self.checkpoint
        if height < 0:
            return
        if height < self.checkpoint:
            return self.parent().read_header(height)
        if height > self.height():
            return
        delta = height - self.checkpoint
        print 'delta', delta
        name = self.path()
        if os.path.exists(name):
            f = open(name, 'rb')
            for i in range(delta):
                f.seek(140, 1)
                vs = read_vector_size(f)
                f.seek(vs, 1)
            h = f.read(140)
            f.close()
        return deserialize_header(h, height)

    def get_hash(self, height):
        return self.hash_header(self.read_header(height))

    def BIP9(self, height, flag):
        v = self.read_header(height)['version']
        return ((v & 0xE0000000) == 0x20000000) and ((v & flag) == flag)

    def segwit_support(self, N=576):
        h = self.local_height
        return sum([self.BIP9(h-i, 2) for i in range(N)])*10000/N/100.

    def convbits(self, new_target):
        c = ("%064x" % new_target)[2:]
        while c[:2] == '00' and len(c) > 6:
            c = c[2:]
        bitsN, bitsBase = len(c) / 2, int('0x' + c[:6], 16)
        if bitsBase >= 0x800000:
            bitsN += 1
            bitsBase >>= 8
        new_bits = bitsN << 24 | bitsBase
        return new_bits
        
    def convbignum(self, bits):
        bitsN = (bits >> 24) & 0xff
        if not (bitsN >= 0x03 and bitsN <= 0x1e):
            raise BaseException("First part of bits should be in [0x03, 0x1e]")
        bitsBase = bits & 0xffffff
        if not (bitsBase >= 0x8000 and bitsBase <= 0x7fffff):
            raise BaseException("Second part of bits should be in [0x8000, 0x7fffff]")
        target = bitsBase << (8 * (bitsN-3))
        return target
        
        
    def KimotoGravityWell(self, height, chain={}):	
	  BlocksTargetSpacing			= 2.5 * 60; # 2.5 minutes
	  TimeDaySeconds				= 60 * 60 * 24;
	  PastSecondsMin				= TimeDaySeconds * 0.25;
	  PastSecondsMax				= TimeDaySeconds * 7;
	  PastBlocksMin				    = PastSecondsMin / BlocksTargetSpacing;
	  PastBlocksMax				    = PastSecondsMax / BlocksTargetSpacing;

	  
	  BlockReadingIndex             = height - 1
	  BlockLastSolvedIndex          = height - 1
	  TargetBlocksSpacingSeconds    = BlocksTargetSpacing
	  PastRateAdjustmentRatio       = 1.0
	  bnProofOfWorkLimit = 0x00000FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
	  
	  if (BlockLastSolvedIndex<=0 or BlockLastSolvedIndex<PastSecondsMin):
		new_target = bnProofOfWorkLimit
		new_bits = self.convbits(new_target)      
		return new_bits, new_target

	  last = chain.get(BlockLastSolvedIndex)
	  if last == None:
	  	last = self.read_header(BlockLastSolvedIndex)
	  
	  for i in xrange(1,int(PastBlocksMax)+1):
		PastBlocksMass=i

		reading = chain.get(BlockReadingIndex)
   		if reading == None:
		  reading = self.read_header(BlockReadingIndex)
		  chain[BlockReadingIndex] = reading
        
		if (reading == None or last == None):
			raise BaseException("Could not find previous blocks when calculating difficulty reading: " + str(BlockReadingIndex) + ", last: " + str(BlockLastSolvedIndex) + ", height: " + str(height))
        	
		if (i == 1):
		  PastDifficultyAverage=self.convbignum(reading.get('bits'))
		else:
		  PastDifficultyAverage= float((self.convbignum(reading.get('bits')) - PastDifficultyAveragePrev) / float(i)) + PastDifficultyAveragePrev;
         
		PastDifficultyAveragePrev = PastDifficultyAverage;
		
		PastRateActualSeconds   = last.get('timestamp') - reading.get('timestamp');
		PastRateTargetSeconds   = TargetBlocksSpacingSeconds * PastBlocksMass;
		PastRateAdjustmentRatio       = 1.0
		if (PastRateActualSeconds < 0):
		  PastRateActualSeconds = 0.0
		
		if (PastRateActualSeconds != 0 and PastRateTargetSeconds != 0):
		  PastRateAdjustmentRatio			= float(PastRateTargetSeconds) / float(PastRateActualSeconds)
		
		EventHorizonDeviation       = 1 + (0.7084 * pow(float(PastBlocksMass)/float(144), -1.228))
		EventHorizonDeviationFast   = EventHorizonDeviation
		EventHorizonDeviationSlow		= float(1) / float(EventHorizonDeviation)
		
		#print_msg ("EventHorizonDeviation=",EventHorizonDeviation,"EventHorizonDeviationFast=",EventHorizonDeviationFast,"EventHorizonDeviationSlow=",EventHorizonDeviationSlow ) 
		
		if (PastBlocksMass >= PastBlocksMin):
		
		  if ((PastRateAdjustmentRatio <= EventHorizonDeviationSlow) or (PastRateAdjustmentRatio >= EventHorizonDeviationFast)):
			break;
			 
		  if (BlockReadingIndex<1):
			break
				
		BlockReadingIndex = BlockReadingIndex -1;
		#print_msg ("BlockReadingIndex=",BlockReadingIndex )
		
	  #print_msg ("for end: PastBlocksMass=",PastBlocksMass ) 
	  bnNew   = PastDifficultyAverage
	  if (PastRateActualSeconds != 0 and PastRateTargetSeconds != 0):
		bnNew *= float(PastRateActualSeconds);
		bnNew /= float(PastRateTargetSeconds);
		
	  if (bnNew > bnProofOfWorkLimit):
		bnNew = bnProofOfWorkLimit

	  # new target
	  new_target = bnNew
	  new_bits = self.convbits(new_target)

	  #print_msg("bits", new_bits , "(", hex(new_bits),")")
	 #print_msg ("PastRateAdjustmentRatio=",PastRateAdjustmentRatio,"EventHorizonDeviationSlow",EventHorizonDeviationSlow,"PastSecondsMin=",PastSecondsMin,"PastSecondsMax=",PastSecondsMax,"PastBlocksMin=",PastBlocksMin,"PastBlocksMax=",PastBlocksMax)    
	  return new_bits, new_target

    def get_target(self, height, chain={}):
        if bitcoin.TESTNET:
            return 0, 0
        if height == 0 or height == 208301:
            return 0x1e0ffff0, 0x00000FFFF0000000000000000000000000000000000000000000000000000000
        if height == 468741:
            bits = 469820683
            bitsBase = bits & 0xffffff
            bitsN = (bits >> 24) & 0xff
            target = bitsBase << (8 * (bitsN - 3))
            return bits, target 
        if height < 26754:
            # Litecoin: go back the full period unless it's the first retarget
            first = self.read_header((height - 2016 - 1 if height > 2016 else 0))
            last = self.read_header(height - 1)
            if last is None:
                last = chain.get(height - 1)
            assert last is not None
            # bits to target
            bits = last.get('bits')
            bitsN = (bits >> 24) & 0xff
            if not (bitsN >= 0x03 and bitsN <= 0x1e):
                raise BaseException("First part of bits should be in [0x03, 0x1e]")
            bitsBase = bits & 0xffffff
            if not (bitsBase >= 0x8000 and bitsBase <= 0x7fffff):
                raise BaseException("Second part of bits should be in [0x8000, 0x7fffff]")
            target = bitsBase << (8 * (bitsN-3))
            if height % 2016 != 0:
                return bits, target
            # new target
            nActualTimespan = last.get('timestamp') - first.get('timestamp')
            nTargetTimespan = 84 * 60 * 60
            nActualTimespan = max(nActualTimespan, nTargetTimespan / 4)
            nActualTimespan = min(nActualTimespan, nTargetTimespan * 4)
            new_target = min(MAX_TARGET, (target*nActualTimespan) / nTargetTimespan)
            # convert new target to bits
            c = ("%064x" % new_target)[2:]
            while c[:2] == '00' and len(c) > 6:
                c = c[2:]
            bitsN, bitsBase = len(c) / 2, int('0x' + c[:6], 16)
            if bitsBase >= 0x800000:
                bitsN += 1
                bitsBase >>= 8
            new_bits = bitsN << 24 | bitsBase
            return new_bits, bitsBase << (8 * (bitsN-3))                
        else:
            return self.KimotoGravityWell(height, chain)
            

    def can_connect(self, header, check_height=True):
        height = header['block_height']
        if check_height and self.height() != height - 1:
            return False
        if height == 0:
            return self.hash_header(header) == bitcoin.GENESIS
        previous_header = self.read_header(height -1)
        if not previous_header:
            return False
        prev_hash = self.hash_header(previous_header)
        if prev_hash != header.get('prev_block_hash'):
            return False
        nonce, n_solution = headers.get('nonce'), header.get('n_solution')
        bits, target = self.get_target(index*2016 + i, headers)
        try:
            self.verify_header(header, prev_header, bits, target, nonce, n_solution)
        except:
            return False
        return True


    def connect_chunk(self, idx, hexdata):
        try:
            data = hexdata.decode('hex')
            self.verify_chunk(idx, data)
            #self.print_error("validated chunk %d" % idx)
            self.save_chunk(idx, data)
            return True
        except BaseException as e:
            self.print_error('verify_chunk failed', str(e))
            return False
