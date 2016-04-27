#!/bin/bash
dmd -gc -debug *.d -ofpsi && time ./psi $@
# dmd -release -inline -O *.d -ofprob && time ./prob $@
