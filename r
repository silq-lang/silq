#!/bin/bash
dmd prob.d lexer.d parser.d expression.d error.d terminal.d util.d && time ./prob $@
