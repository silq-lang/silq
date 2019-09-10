#!/bin/bash
set -eu
rm silq silq-osx silq.exe ||:
sudo ./build-xosx-release.sh
./build-release.sh
./build-xwindows-release.sh
