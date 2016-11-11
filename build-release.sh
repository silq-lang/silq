#!/bin/bash
if [ -d "dmd2" ]; then
    DMD="./dmd2/linux/bin64/dmd";
else
    DMD="dmd"
fi

# release build
# TODO: make sure tests run correctly with release build
$ DMD -O -release -inline -J. *.d -ofpsi
# ldmd2 -O -release -inline -J. *.d -ofllpsi

if [ ! -f "test/runtests" ]; then
    $DMD test/runtests.d -oftest/runtests
fi



#!/bin/bash
