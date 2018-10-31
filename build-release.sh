#!/bin/bash

VERSION="1.7.0"

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

# release build
# TODO: make sure tests run correctly with release build
$LDMD -O -release -inline -boundscheck=off -J. -Jlibrary *.d -ofhql
# ldmd2 -O -release -inline -J. -Jlibrary *.d -ofllhql

if [ ! -f "test/runtests" ]; then
    $LDMD test/runtests.d -oftest/runtests
fi

