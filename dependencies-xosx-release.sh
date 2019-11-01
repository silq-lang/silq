#!/bin/bash

VERSION="1.18.0"

git clone git@github.com:jacob-carlborg/docker-ldc-darwin.git
cd docker-ldc-darwin
./build.sh --build-arg LDC_VERSION=$VERSION
cd ..
