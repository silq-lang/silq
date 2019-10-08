#!/bin/bash
# debug build
dmd -g -debug -J. -Jlibrary *.d ast/*.d util/*.d -ofsilq -L-fuse-ld=gold && time ./silq $@
# dmd -release -inline -J. -O *.d -ofprob && time ./prob $@
