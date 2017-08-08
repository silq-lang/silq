#!/bin/bash
# debug build
dmd -g -debug -J. *.d -ofpsi && time ./psi $@
# dmd -release -inline -J. -O *.d -ofprob && time ./prob $@
