#!/bin/bash
# debug build
dmd -g -debug -J. -Jlibrary *.d -ofpsi -L-fuse-ld=gold && time ./psi $@
# dmd -release -inline -J. -O *.d -ofprob && time ./prob $@
