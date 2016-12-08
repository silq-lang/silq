#!/bin/bash
if [ ! -d dmd2 ]; then
    SUM1="cf9db5363e8fa97c4e5c139898abef71  dmd.2.072.1.linux.zip"
    wget http://downloads.dlang.org/releases/2.x/2.072.1/dmd.2.072.1.linux.zip
    SUM2=`md5sum dmd.2.072.1.linux.zip`
    if [[ $SUM1 != $SUM2 ]]; then
	echo "ERROR: md5 sum mismatch"
    else
	unzip dmd.2.072.1.linux.zip
    fi
fi
