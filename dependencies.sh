#!/bin/bash

if [ ! -d dmd2 ]; then
    VERSION="2.088.1"

    if [[ "$OSTYPE" == "linux-gnu" ]]; then
        FILE="dmd.$VERSION.linux.zip"
        SUM1="98bfc1e1645bdeb4296749e833ec3fcd  $FILE"
        MD5="md5sum"
    elif [[ "$OSTYPE" == "darwin"* ]]; then
        # Note that on macOS gnuplot should be installed with x11 set as terminal. 
        # Using homebrew: brew install gnuplot --with-x11
        FILE="dmd.$VERSION.osx.zip"
        SUM1="MD5 ($FILE) = 9c49109a79433d8a9669d9b000914be1"
        MD5="md5"
    else
        >&2 echo "This script does not support your platform at this time."
        >&2 echo "Try to obtain the dmd d compiler manually from:"
        >&2 echo "https://dlang.org"
        >&2 echo "Pull requests for improved build script welcome."
        exit 1;
    fi

    ZIPLINK="http://downloads.dlang.org/releases/2.x/$VERSION/$FILE"
    
    wget -nc $ZIPLINK
    SUM2=`$MD5 $FILE`

    if [[ $SUM1 != $SUM2 ]]; then
        echo "ERROR: md5 sum mismatch"
        echo "EXPECTED: $SUM1"
        echo "GOT     : $SUM2"
    else
        unzip $FILE
    fi
fi

git submodule init
git submodule update
