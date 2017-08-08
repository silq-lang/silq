#!/bin/bash
if [ ! -d dmd2 ]; then
    VERSION="2.075.0"
    if [[ "$OSTYPE" == "linux-gnu" ]]; then
        FILE="dmd.$VERSION.linux.zip"
        SUM1="c0d5461474bd3b100db081280788df06  $FILE"
        MD5="md5sum"
    elif [[ "$OSTYPE" == "darwin"* ]]; then
	  # Note that on macOS gnuplot should be installed with x11 set as terminal. 
	  # Using homebrew: brew install gnuplot --with-x11
        FILE="dmd.$VERSION.osx.zip"
        SUM1="MD5 ($FILE) = 392b46467aba0ba324ba3e02a1d2f6b2"
        MD5="md5"
    else
	>&2 echo "This script does not support your platform at this time."
	>&2 echo "Try to obtain the dmd d compiler manually from:"
	>&2 echo "https://dlang.org"
	>&2 echo "Pull requests for improved build script welcome."
	exit 1;
    fi

    ZIPLINK="http://downloads.dlang.org/releases/2.x/$VERSION/$FILE"
    
    wget $ZIPLINK
    SUM2=`$MD5 $FILE`

    if [[ $SUM1 != $SUM2 ]]; then
	echo "ERROR: md5 sum mismatch"
    else
	unzip $FILE
    fi
fi
