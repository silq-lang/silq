#!/bin/bash
if [ ! -d dmd2 ]; then
    SUM1="c6dc5df0eeac35d37db167b9a80eb08e  dmd.2.072.2.linux.zip"
    wget http://downloads.dlang.org/releases/2.x/2.072.2/dmd.2.072.2.linux.zip
    SUM2=`md5sum dmd.2.072.2.linux.zip`
    if [[ $SUM1 != $SUM2 ]]; then
	echo "ERROR: md5 sum mismatch"
    else
	unzip dmd.2.072.2.linux.zip
    fi
fi
