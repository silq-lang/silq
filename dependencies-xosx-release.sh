#!/bin/bash

VERSION=$(cat version-ldc.txt)

git clone git@github.com:jacob-carlborg/docker-ldc-darwin.git
cd docker-ldc-darwin
./build.sh --build-arg LDC_VERSION=$VERSION
cd ..
