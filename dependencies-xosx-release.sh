#!/bin/bash

VERSION="1.16.0-beta2"

git clone git@github.com:jacob-carlborg/docker-ldc-darwin.git
cd docker-ldc-darwin
./build.sh --build-arg LDC_VERSION=$VERSION
cd ..

# LINK=https://github.com/ldc-developers/ldc/releases/download/v$VERSION/
# NAME="ldc2-$VERSION-osx-x86_64"
# FILE="$NAME.tar.xz"
# SUM="cc57302988c590036c93f0f3fad3f6fc"
# if [[ "$OSTYPE" == "linux-gnu" ]]; then
#     SUM1="$SUM  $FILE"
#     MD5="md5sum"
# elif [[ "$OSTYPE" == "darwin"* ]]; then
#     SUM1="MD5 ($FILE) = $SUM"
#     MD5="md5"
# else
#     >&2 echo "This script does not support your platform at this time."
#     >&2 echo "Try to obtain the ldc d compiler manually from:"
#     >&2 echo "https://github.com/ldc-developers/ldc/releases"
#     >&2 echo "Pull requests for improved build script welcome."
#     exit 1
# fi

# if [ ! -d $NAME ]; then
#     TARLINK="$LINK$FILE"
#     wget -nc $TARLINK
#     SUM2=`$MD5 $FILE`

#     if [[ $SUM1 != $SUM2 ]]; then
#         echo "ERROR: md5 sum mismatch"
#       echo "EXPECTED: $SUM1"
#       echo "GOT     : $SUM2"
#     else
#         tar -xf $FILE
#     fi
# fi

# if [ ! -d "$NAME/bin.orig" ]; then
#     mv "$NAME/bin/" "$NAME/bin-orig"
#     cp -r "ldc2-$VERSION-linux-x86_64/bin/" "$NAME"
# fi
