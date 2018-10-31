#!/bin/bash
# debug build
dmd -g -debug -J. -Jlibrary *.d -ofhql -L-fuse-ld=gold && time ./hql $@
# dmd -release -inline -J. -O *.d -ofprob && time ./prob $@
