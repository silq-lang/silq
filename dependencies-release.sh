#!/bin/bash

LINK=https://github.com/ldc-developers/ldc/releases/download/v1.2.0-beta1/

if [[ "$OSTYPE" == "linux-gnu" ]]; then
    NAME="ldc2-1.2.0-beta1-linux-x86_64"
    FILE="$NAME.tar.xz"
    SUM1="b02aafa9ab888c5392da50dd5f4bb959  $FILE"
    MD5="md5sum"
elif [[ "$OSTYPE" == "darwin"* ]]; then
    NAME="ldc2-1.2.0-beta1-osx-x86_64"
    FILE="$NAME.tar.xz"
    SUM1="MD5 ($FILE) = "
    MD5="md5"
else
    >&2 echo "This script does not support your platform at this time."
    >&2 echo "Try to obtain the ldc d compiler manually from:"
    >&2 echo "https://github.com/ldc-developers/ldc/releases"
    >&2 echo "Pull requests for improved build script welcome."
    exit(1);
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
