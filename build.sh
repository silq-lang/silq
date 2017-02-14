#!/bin/bash
if [[ "$OSTYPE" == "linux-gnu" ]]; then
    BIN="linux/bin64"
elif [[ "$OSTYPE" == "darwin"* ]]; then
    BIN="osx/bin"
fi

if [[ -d "dmd2" ]]; then
    DMD="./dmd2/$BIN/dmd"
else
    DMD="dmd"
fi

# debug build
$DMD -gc -debug -J. *.d -ofpsi

if [ ! -f "test/runtests" ]; then
    $DMD test/runtests.d -oftest/runtests
fi
