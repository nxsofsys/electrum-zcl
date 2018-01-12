import sys
from PyQt4.QtCore import *
from PyQt4.QtGui import *
import zcltabbar
import icons_rc


class ZclTabWidget(QTabWidget):
    def __init__(self, parent=None):
        super(ZclTabWidget, self).__init__(parent)
        tabBar = zcltabbar.ZclTabBar(self)
        self.setTabBar(tabBar)
        self.setTabPosition(QTabWidget.West)


if __name__ == "__main__":
    app = QApplication(sys.argv)
    window = QMainWindow()
    window.setGeometry(100, 100, 840, 400)
    tabWidget = ZclTabWidget(window)
    tabWidget.addTab(QLabel("Test"), QIcon(":icons/electrum-zcl.png"), "Test")
    tabWidget.addTab(QLabel("Test 2"), "Test 2")
    window.setCentralWidget(tabWidget)
    window.show()
    app.exec_()
