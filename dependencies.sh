#!/bin/bash
if [ ! -d dmd2 ]; then
    SUM1="c622a61e20eb4574e6de06978fab55e6  dmd.2.071.0.linux.tar.xz"
    wget http://downloads.dlang.org/releases/2.x/2.071.0/dmd.2.071.0.linux.tar.xz
    SUM2=`md5sum dmd.2.071.0.linux.tar.xz`
    if [[ $SUM1 != $SUM2 ]]; then
	echo "ERROR: md5 sum mismatch"
    else
	tar xvfJ dmd.2.071.0.linux.tar.xz
    fi
fi
