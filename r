#!/bin/bash
dmd -gc -debug *.d -ofprob && time ./prob $@
# dmd -release -inline -O *.d -ofprob && time ./prob $@
