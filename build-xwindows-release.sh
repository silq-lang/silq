#!/bin/bash

VERSION="1.16.0-beta2"
NAME="ldc2-$VERSION-windows-x64"

LDMD="wine ./$NAME/bin/ldmd2.exe";

# release build
# TODO: make sure tests run correctly with release build
$LDMD -O -release -inline -boundscheck=off -J. -Jlibrary *.d -ofsilq
# ldmd2 -O -release -inline -J. -Jlibrary *.d -ofllsilq

if [ ! -f "test/runtests" ]; then
    $LDMD test/runtests.d -oftest/runtests
fi

