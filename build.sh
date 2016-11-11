#!/bin/bash
if [ -d "dmd2" ]; then
    DMD="./dmd2/linux/bin64/dmd";
else
    DMD="dmd"
fi

# debug build
$DMD -gc -debug -J. *.d -ofpsi

if [ ! -f "test/runtests" ]; then
    $DMD test/runtests.d -oftest/runtests
fi
