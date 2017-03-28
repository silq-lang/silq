#!/bin/bash

if [[ "$OSTYPE" == "linux-gnu" ]]; then
    NAME="ldc2-1.2.0-beta1-linux-x86_64"
elif [[ "$OSTYPE" == "darwin"* ]]; then
    NAME="ldc2-1.2.0-beta1-osx-x86_64"
fi

if [ -d $NAME ]; then
    LDMD="./$NAME/bin/ldmd2";
else
    LDMD="ldmd2"
fi

# release build
# TODO: make sure tests run correctly with release build
$LDMD -O -release -inline -boundscheck=off -J. *.d -ofpsi
# ldmd2 -O -release -inline -J. *.d -ofllpsi

if [ ! -f "test/runtests" ]; then
    $DMD test/runtests.d -oftest/runtests
fi

