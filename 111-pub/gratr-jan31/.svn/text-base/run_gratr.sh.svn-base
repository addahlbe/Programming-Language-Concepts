#!/bin/bash

GTRWDIR=${GTRWDIR:-~/projects/gtrw}

#args+="--print-raw "
args+=" --dump-grammar "
#args+=" --debug-grammar-to-ast "
#args+=" --no-debug-parsing "
#args+=" --debug-local-confluence "
#args+=" --debug-local-confluence-micro "
#args+=" --debug-rewriting "
#args+=" --debug-cps "
#args+=" --print-trs "
#args+=" --debug-construct-automaton "
#args+=" --debug-construct-automaton-micro "
#args+=" --debug-determinization "
#args+=" --debug-determinization-micro "
#args+=" --debug-minimization "
#args+=" --debug-run-rewriting "

#ulimit -S unlimited
#export OCAMLRUNPARAM="l=500M"

${GTRWDIR}/src/gratr/gratr $args $*


#--complete
#  --contextualize-cps
#--debug-contextualize-rules 
#--filter-before-after-by-cps  
