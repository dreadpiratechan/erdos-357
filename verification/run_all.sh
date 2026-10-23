#!/usr/bin/env bash
# Repeat every verification step from a clean build, writing the logs to verification/logs/.
#
# Usage (from the repository root, i.e. the folder that contains lean/ and verification/):
#     bash verification/run_all.sh
# Environment:
#     LEAN4CHECKER   path to a lean4checker executable built from tag v4.27.0 (optional; the step is skipped if unset)
#     FETCH_CACHE=1  run `lake exe cache get` first (needed on a fresh machine; downloads the Mathlib build cache)
#     PYTHON         Python 3 interpreter (default: py on Windows, else python3)
#
# Steps: cache fetch (if FETCH_CACHE=1) -> environment record -> clean `lake build` -> statements (Headline.lean) -> axioms of every declaration
# (AxiomAudit.lean) -> upstream pin (generated from the vendored upstream files) -> kernel replay (lean4checker)
# -> exact-arithmetic checks of the written proofs (paper_checks.py) -> summary.
# Only lean/.lake/build is deleted; lean/.lake/packages (Mathlib) is never written to unless FETCH_CACHE=1.
set -u
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
L="$ROOT/verification/logs"
mkdir -p "$L"
PY="${PYTHON:-$(command -v py >/dev/null 2>&1 && echo py || echo python3)}"
MODS="Erdos.Proofs.P0357 Erdos.Proofs.P0357Skip Erdos.Proofs.P0357Upper Erdos.Proofs.P0357Upper2 Erdos.Proofs.P0357Upper4Gen Erdos.Proofs.P0357Upper4"
cd "$ROOT/lean" || exit 1
START="$(date -u +%Y-%m-%dT%H:%M:%SZ)"

# Fetch first, so that the environment record below sees the Mathlib checkout that Lake has just cloned.
if [ "${FETCH_CACHE:-0}" = "1" ]; then lake exe cache get > "$L/cache_get.log" 2>&1; fi

{
  echo "# run_all.sh started $START"
  echo "os: $(uname -s -r -m)"
  lean --version
  lake --version
  echo "lean-toolchain: $(cat lean-toolchain)"
  "$PY" -c "import json;m=json.load(open('lake-manifest.json'));print('\n'.join('manifest: %s %s %s'%(p['name'],p.get('rev'),p.get('inputRev')) for p in m['packages']))"
  echo "mathlib checkout HEAD: $(git -C .lake/packages/mathlib rev-parse HEAD 2>/dev/null || echo unknown)"
  echo "sha256 of the Lean sources:"
  (cd "$ROOT/lean" && sha256sum Erdos357.lean Erdos/Proofs/*.lean lakefile.toml lake-manifest.json lean-toolchain)
} > "$L/environment.txt" 2>&1

rm -rf .lake/build
( time lake build ) > "$L/build.log" 2>&1; echo "exit=$?" >> "$L/build.log"

( time lake env lean ../verification/Headline.lean ) > "$L/headline.log" 2>&1; echo "exit=$?" >> "$L/headline.log"
( time lake env lean ../verification/AxiomAudit.lean ) > "$L/axioms.log" 2>&1; echo "exit=$?" >> "$L/axioms.log"
( cd "$ROOT" && "$PY" verification/make_upstream_pin.py ) > "$L/upstream_pin.log" 2>&1
( time lake env lean ../verification/generated/UpstreamPin.lean ) >> "$L/upstream_pin.log" 2>&1; echo "exit=$?" >> "$L/upstream_pin.log"

if [ -n "${LEAN4CHECKER:-}" ]; then
  {
    echo "== $(date -u +%Y-%m-%dT%H:%M:%SZ) lean4checker: $(basename "$LEAN4CHECKER")"
    for m in $MODS; do s=$(date +%s); lake env "$LEAN4CHECKER" "$m"; echo "$m exit $? ($(( $(date +%s) - s )) s)"; done
  } > "$L/lean4checker.log" 2>&1
else
  echo "LEAN4CHECKER not set; kernel replay skipped" > "$L/lean4checker.log"
fi

( cd "$ROOT" && time "$PY" verification/paper_checks.py ) > "$L/paper_checks.log" 2>&1; echo "exit=$?" >> "$L/paper_checks.log"

{
  echo "# summary $(date -u +%Y-%m-%dT%H:%M:%SZ)"
  echo "build:        $(grep -E '^(Build completed|error)' "$L/build.log" | tail -1) [$(tail -1 "$L/build.log")]"
  echo "headline:     $(grep -c 'depends on axioms' "$L/headline.log") axiom lines, $(grep -ci 'error' "$L/headline.log") error lines [$(tail -1 "$L/headline.log")]"
  echo "axioms:       $(grep -E 'AXIOM AUDIT|TOTAL' "$L/axioms.log" | tr '\n' ' ') [$(tail -1 "$L/axioms.log")]"
  echo "upstream pin: $(grep -c 'depends on axioms' "$L/upstream_pin.log") axiom lines, $(grep -ci 'error' "$L/upstream_pin.log") error lines [$(tail -1 "$L/upstream_pin.log")]"
  if [ -n "${LEAN4CHECKER:-}" ]; then echo "lean4checker: $(grep -c ' exit 0 ' "$L/lean4checker.log") of 6 modules exit 0"
  else echo "lean4checker: SKIPPED (LEAN4CHECKER not set)"; fi
  echo "paper checks: $(grep -E '^ALL|FAIL|Error' "$L/paper_checks.log" | tr '\n' ' ') [$(tail -1 "$L/paper_checks.log")]"
} | tee "$L/SUMMARY.txt"

# Exit status: 0 only if every step passed (the kernel replay counts only when LEAN4CHECKER is set).
fail=0
grep -q '^Build completed successfully' "$L/build.log" || fail=1
for f in build headline axioms upstream_pin paper_checks; do [ "$(tail -1 "$L/$f.log")" = "exit=0" ] || fail=1; done
for f in headline upstream_pin; do [ "$(grep -ci 'error' "$L/$f.log")" = "0" ] || fail=1; done
grep -q 'AXIOM AUDIT PASSED' "$L/axioms.log" || fail=1
grep -q '^ALL 15 CHECKS PASSED' "$L/paper_checks.log" || fail=1
if [ -n "${LEAN4CHECKER:-}" ]; then [ "$(grep -c ' exit 0 ' "$L/lean4checker.log")" = "6" ] || fail=1; fi
if [ "$fail" != 0 ]; then echo "RESULT: FAIL (see the logs above)"
elif [ -n "${LEAN4CHECKER:-}" ]; then echo "RESULT: PASS"
else echo "RESULT: PASS (kernel replay skipped)"; fi | tee -a "$L/SUMMARY.txt"
exit "$fail"
