#!/bin/bash

tests="lam.gr ifelse3.gr expr.gr  gjbook_8_11.gr gjbook_8_12.gr gjbook_9_13.gr gjbook_9_23.gr gjbook_10_2_1.gr"
tests+=" lr_countereg.gr"

for f in $tests ; 
do
  echo "------------------------------"
  echo "Beginning regression for $f"
  echo
  (time ../run_gratr.sh $f ) 2>&1
done