#!/bin/bash

VERSION="1.18.0"
LINK=https://github.com/ldc-developers/ldc/releases/download/v$VERSION/
NAME="ldc2-$VERSION-windows-x64"
FILE="$NAME.7z"
SUM="aad474ef5ccbfcbbb163800c4ebc3a2e"
if [[ "$OSTYPE" == "linux-gnu" ]]; then
    SUM1="$SUM  $FILE"
    MD5="md5sum"
elif [[ "$OSTYPE" == "darwin"* ]]; then
    SUM1="MD5 ($FILE) = $SUM"
    MD5="md5"
else
    >&2 echo "This script does not support your platform at this time."
    >&2 echo "Try to obtain the ldc d compiler manually from:"
    >&2 echo "https://github.com/ldc-developers/ldc/releases"
    >&2 echo "Pull requests for improved build script welcome."
    exit 1
fi

if [ ! -d $NAME ]; then
    TARLINK="$LINK$FILE"
    wget -nc $TARLINK
    SUM2=`$MD5 $FILE`

    if [[ $SUM1 != $SUM2 ]]; then
        echo "ERROR: md5 sum mismatch"
        echo "EXPECTED: $SUM1"
        echo "GOT     : $SUM2"
    else
        7z x $FILE
    fi
fi
