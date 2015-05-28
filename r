#!/bin/bash
dmd -gc prob.d lexer.d parser.d expression.d analysis.d distrib.d dexpr.d error.d terminal.d hashtable.d util.d && time ./prob $@
