#!/bin/bash
dmd -gc *.d -ofprob && time ./prob $@
