#!/bin/bash

VERSION="1.16.0-beta2"
LINK=https://github.com/ldc-developers/ldc/releases/download/v$VERSION/
NAME="ldc2-$VERSION-windows-x64"
FILE="$NAME.7z"
SUM1="aad474ef5ccbfcbbb163800c4ebc3a2e  $FILE"
MD5="md5sum"

if [ ! -d $NAME ]; then
    TARLINK="$LINK$FILE"
    wget $TARLINK
    SUM2=`$MD5 $FILE`

    if [[ $SUM1 != $SUM2 ]]; then
        echo "ERROR: md5 sum mismatch"
	echo "EXPECTED: $SUM1"
	echo "GOT: $SUM2"
    else
        7z x $FILE
    fi
fi
