#!/bin/bash

VERSION="1.3.0"
LINK=https://github.com/ldc-developers/ldc/releases/download/v$VERSION/

if [[ "$OSTYPE" == "linux-gnu" ]]; then
    NAME="ldc2-$VERSION-linux-x86_64"
    FILE="$NAME.tar.xz"
    SUM1="66ef495d1169cb94154ea27cebd45073  $FILE"
    MD5="md5sum"
elif [[ "$OSTYPE" == "darwin"* ]]; then
    NAME="ldc2-$VERSION-osx-x86_64"
    FILE="$NAME.tar.xz"
    SUM1="MD5 ($FILE) = 6e4daf6aff35fc319060dea7d2dd6cee"
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
    wget $TARLINK
    SUM2=`$MD5 $FILE`

    if [[ $SUM1 != $SUM2 ]]; then
	echo "ERROR: md5 sum mismatch"
    else
	tar -xf $FILE
    fi
fi
