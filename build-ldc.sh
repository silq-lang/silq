#!/bin/bash

VERSION=$(cat version-ldc.txt)

if [[ "$OSTYPE" == "linux-gnu" ]]; then
    NAME="ldc2-$VERSION-linux-x86_64"
elif [[ "$OSTYPE" == "darwin"* ]]; then
    NAME="ldc2-$VERSION-osx-x86_64"
fi

if [ -d $NAME ]; then
    LDMD="./$NAME/bin/ldmd2";
else
    LDMD="ldmd2"
fi

$LDMD -J. -Jlibrary *.d ast/*.d util/*.d -ofsilq

