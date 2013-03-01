#!/bin/bash

f=$1
base=${f%.*}

# nfa dfa

for d in nfa dfa min rev_nfa rev ref rewr ; do 
  if [ -f ${base}_$d.gv ] ; then
      echo "generating ${base}_$d.pdf";
      dot -Tpdf -o ${base}_$d.pdf ${base}_$d.gv
  fi
done
