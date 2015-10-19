#!/bin/bash
for i in {1..10}; do cat cav-example-1.prb | sed "s/repeat X/repeat $i/" > tmp.prb && time ../../prob tmp.prb; rm tmp.prb; done
