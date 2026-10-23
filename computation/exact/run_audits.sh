#!/usr/bin/env bash
# Deep-state audit: at every 20000th visited node the engine re-derives the Lemma-1 candidate set of that
# node by the naive definition (HashSet of block sums, every x in [lo, n] tried) and compares it with the
# bitset-window mask; any difference panics.  One thread (the main run uses 7).
# usage: run_audits.sh EXACT_BIN EXACT_DIR      (appends to EXACT_DIR/logs/audit_deep.log; use a scratch directory
#        if you do not want to touch the committed log).  About 25 minutes in total.
BIN="$1"; D="$2"
mkdir -p "$D/logs"
for kn in "26 66" "27 68" "28 70"; do
  set -- $kn
  "$BIN" count "$1" "$2" --threads 1 --audit 20000 | tee -a "$D/logs/audit_deep.log"
done
