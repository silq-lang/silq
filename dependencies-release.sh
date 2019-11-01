#!/bin/bash

VERSION="1.18.0"
LINK=https://github.com/ldc-developers/ldc/releases/download/v$VERSION/

if [[ "$OSTYPE" == "linux-gnu" ]]; then
    NAME="ldc2-$VERSION-linux-x86_64"
    FILE="$NAME.tar.xz"
    SUM1="2d00012388e2af2324c5e9bc57d73dcd  $FILE"
    MD5="md5sum"
elif [[ "$OSTYPE" == "darwin"* ]]; then
    NAME="ldc2-$VERSION-osx-x86_64"
    FILE="$NAME.tar.xz"
    SUM1="MD5 ($FILE) = efa70c4a558cdf2ef8d80a79c673bfde"
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
        echo "GOT: $SUM2"
    else
        tar -xf $FILE
    fi
fi

git submodule init
git submodule update
