#!/bin/bash
dmd -gc -debug *.d -ofpsy && time ./psy $@
# dmd -release -inline -O *.d -ofprob && time ./prob $@
