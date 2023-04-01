#!/bin/bash

VERSION="1.32.0"
NAME="ldc2-$VERSION-windows-x64"

LDMD="wine ./$NAME/bin/ldmd2.exe";

# release build
$LDMD -O -inline -J. -Jlibrary *.d ast/*.d util/*.d -ofsilq
