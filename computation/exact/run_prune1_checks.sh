#!/usr/bin/env bash
# Deep-state cross-check of rule R3 and its child form: the same decisions with pruning level 1
# (room bound R1 only, whose proof is one line) must give the same counts (and the same set at (27,69)).
# usage: run_prune1_checks.sh EXACT_BIN EXACT_DIR [THREADS]
#        (appends to EXACT_DIR/logs/prune1_deep.log and writes EXACT_DIR/logs/prune1_k*_n*.sets; use a scratch
#        directory if you do not want to touch the committed logs).  About 25 minutes with 8 threads.
BIN="$1"; D="$2"; T="${3:-8}"
mkdir -p "$D/logs"
for kn in "26 66" "27 68" "27 69" "28 70" "28 72"; do
  set -- $kn
  "$BIN" count "$1" "$2" --prune 1 --threads "$T" --sets "$D/logs/prune1_k$1_n$2.sets" 2>/dev/null | tee -a "$D/logs/prune1_deep.log"
done
