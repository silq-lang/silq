#!/bin/bash

cd docker-ldc-darwin
docker run --rm --name=compile -v "$(pwd)/..":"/host" -w /host -e MACOSX_DEPLOYMENT_TARGET=10.9 ldc-darwin ldc2 -O -J. -Jlibrary *.d ast/*.d util/*.d -of=silq-osx
docker run --rm --name=compile -v "$(pwd)/..":"/host" -w /host ldc-darwin strip silq-osx

