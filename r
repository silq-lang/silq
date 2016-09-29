#!/bin/bash
# debug build
dmd -gc -debug -J. *.d -ofpsi && time ./psi $@
# dmd -release -inline -J. -O *.d -ofprob && time ./prob $@
