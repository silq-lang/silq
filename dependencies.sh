#!/bin/bash

if [ ! -d dmd2 ]; then
    VERSION="2.112.0"

    if [[ "$OSTYPE" == "linux-gnu" ]]; then
        FILE="dmd.$VERSION.linux.zip"
        SUM1="c8ee2e9d42bc156a7dfa58059d173b48  $FILE"
        MD5="md5sum"
    elif [[ "$OSTYPE" == "darwin"* ]]; then
        FILE="dmd.$VERSION.osx.zip"
        SUM1="MD5 ($FILE) = 151cfd5ebfaff7cdb3e7d90c1e847da1"
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
