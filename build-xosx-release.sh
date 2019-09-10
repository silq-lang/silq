#!/bin/bash

cd docker-ldc-darwin
docker run --rm --name=compile -v "$(pwd)/..":"/host" -w /host -e MACOSX_DEPLOYMENT_TARGET=10.9 ldc-darwin ldc2 -O -J. -Jlibrary *.d -of=silq-osx
docker run --rm --name=compile -v "$(pwd)/..":"/host" -w /host ldc-darwin strip silq-osx

# VERSION="1.16.0-beta2"
# NAME="ldc2-$VERSION-osx-x86_64"
# TARGET=10.8

# if [ -d $NAME ]; then
#     LDMD="./$NAME/bin/ldmd2";
# else
#     LDMD="ldmd2"
# fi

# # release build
# MACOSX_DEPLOYMENT_TARGET=$TARGET CROSS_TRIPLE=x86_64-apple-darwin $LDMD -mtriple x86_64-apple-darwin -c -O -inline -J. -Jlibrary *.d -ofsilq-osx.o

