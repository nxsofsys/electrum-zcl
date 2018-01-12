#!/usr/bin/env python2

# python setup.py sdist --format=zip,gztar

from setuptools import setup
import os
import sys
import platform
import imp
import argparse

version = imp.load_source('version', 'lib/version.py')

if sys.version_info[:3] < (2, 7, 0):
    sys.exit("Error: Electrum requires Python version >= 2.7.0...")

data_files = []

if platform.system() in ['Linux', 'FreeBSD', 'DragonFly']:
    parser = argparse.ArgumentParser()
    parser.add_argument('--root=', dest='root_path', metavar='dir', default='/')
    opts, _ = parser.parse_known_args(sys.argv[1:])
    usr_share = os.path.join(sys.prefix, "share")
    if not os.access(opts.root_path + usr_share, os.W_OK) and \
       not os.access(opts.root_path, os.W_OK):
        if 'XDG_DATA_HOME' in os.environ.keys():
            usr_share = os.environ['XDG_DATA_HOME']
        else:
            usr_share = os.path.expanduser('~/.local/share')
    data_files += [
        (os.path.join(usr_share, 'applications/'), ['electrum-zcl.desktop']),
        (os.path.join(usr_share, 'pixmaps/'), ['icons/electrum-zcl.png'])
    ]

setup(
    name="Electrum-zcl",
    version=version.ELECTRUM_VERSION,
    install_requires=[
        'pyaes',
        'ecdsa>=0.9',
        'pbkdf2',
        'requests',
        'qrcode',
	'ltc_scrypt',
	'lyra2re2_hash',
        'protobuf',
        'dnspython',
        'jsonrpclib',
        'PySocks>=1.6.6',
    ],
    packages=[
        'electrum_zcl',
        'electrum_zcl_gui',
        'electrum_zcl_gui.qt',
        'electrum_zcl_gui.zcl',
        'electrum_zcl_plugins',
        'electrum_zcl_plugins.audio_modem',
        'electrum_zcl_plugins.cosigner_pool',
        'electrum_zcl_plugins.email_requests',
        'electrum_zcl_plugins.hw_wallet',
        'electrum_zcl_plugins.keepkey',
        'electrum_zcl_plugins.labels',
        'electrum_zcl_plugins.ledger',
        'electrum_zcl_plugins.trezor',
        'electrum_zcl_plugins.digitalbitbox',
        'electrum_zcl_plugins.virtualkeyboard',
    ],
    package_dir={
        'electrum_zcl': 'lib',
        'electrum_zcl_gui': 'gui',
        'electrum_zcl_plugins': 'plugins',
    },
    package_data={
        'electrum_zcl': [
            'currencies.json',
            'www/index.html',
            'wordlist/*.txt',
            'locale/*/LC_MESSAGES/electrum.mo',
        ]
    },
    scripts=['electrum-zcl'],
    data_files=data_files,
    description="Lightweight Zclassic Wallet",
    author="Thomas Voegtlin",
    author_email="thomasv@electrum.org",
    license="MIT Licence",
    url="https://github.com/BTCP-community/electrum-zcl",
    long_description="""Lightweight Zclassic Wallet"""
)
