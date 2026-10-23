#!/usr/bin/env bash
# Regenerate the 18 reverse-greedy sets with the rgreedy tool in this directory, with the documented command
#     rgreedy rev N --cmax 6.5 --dump rev_N.txt
# usage: run_greedy.sh [RGREEDY_EXE [OUTDIR]]
#   RGREEDY_EXE  the compiled tool.  Default: $RGREEDY if set, else rgreedy/target/release/rgreedy (rgreedy.exe on
#                Windows), i.e. what `cd rgreedy && cargo build --release` produces.
#   OUTDIR       where sets/rev_N.txt and logs/run_greedy.log are written.  Default: ./regen next to this script
#                (the committed sets/ and logs/ are never touched unless you pass this directory itself).
#   env MAXN=N   only the sizes n <= N.  MAXN=1000000 takes about 10 seconds; the full list takes about 25 minutes.
# Before every run the free RAM is checked (the table has 5 * 2^bits bytes: 2.7 GB at n = 10^7, 5.4 GB at
# n = 2*10^7); the script refuses to start a run that would leave less than 3 GB free.  If the free RAM cannot be
# determined on this machine the check is skipped with a note.
# The tool is sequential: one thread per run.
set -u
HERE="$(cd "$(dirname "$0")" && pwd)"
R="${1:-${RGREEDY:-}}"
if [ -z "$R" ]; then
  for c in "$HERE/rgreedy/target/release/rgreedy.exe" "$HERE/rgreedy/target/release/rgreedy"; do
    [ -x "$c" ] && R="$c" && break
  done
fi
if [ -z "$R" ] || [ ! -x "$R" ]; then
  echo "rgreedy binary not found; build it with: (cd \"$HERE/rgreedy\" && cargo build --release)" >&2
  exit 2
fi
OUT="${2:-$HERE/regen}"
MAXN="${MAXN:-0}"
mkdir -p "$OUT/sets" "$OUT/logs"
: > "$OUT/logs/run_greedy.log"
NS="1000 1778 3162 5623 10000 17783 31623 56234 100000 177828 316228 562341 1000000 1778279 3162278 5623413 10000000 20000000"

# free RAM in GB, or "n/a"
free_gb() {
  if command -v powershell.exe >/dev/null 2>&1; then
    powershell.exe -NoProfile -Command "[math]::Round((Get-CimInstance Win32_OperatingSystem).FreePhysicalMemory/1MB,2)" 2>/dev/null | tr -d '\r'
  elif [ -r /proc/meminfo ]; then
    awk '/^MemAvailable:/ {a=$2} /^MemFree:/ {f=$2} END {printf "%.2f\n", (a ? a : f)/1048576}' /proc/meminfo
  else
    echo "n/a"
  fi
}

for N in $NS; do
  if [ "$MAXN" -gt 0 ] && [ "$N" -gt "$MAXN" ]; then continue; fi
  need=3.0; [ "$N" -ge 5000000 ] && need=6.0; [ "$N" -ge 15000000 ] && need=9.0   # table size + 3 GB floor
  f=$(free_gb)
  echo "free RAM before n=$N: ${f} GB (need >= $need)" | tee -a "$OUT/logs/run_greedy.log"
  case "$f" in
    ""|n/a) echo "  (free RAM unknown, check skipped)" | tee -a "$OUT/logs/run_greedy.log" ;;
    *) if awk "BEGIN{exit !($f < $need)}"; then
         echo "ABORT: not enough free RAM for n=$N" | tee -a "$OUT/logs/run_greedy.log"; exit 3
       fi ;;
  esac
  s=$(date +%s)
  "$R" rev "$N" --cmax 6.5 --dump "$OUT/sets/rev_$N.txt" 2>&1 | tee -a "$OUT/logs/run_greedy.log"
  e=$(date +%s)
  echo "  wall ${N}: $((e-s)) s" | tee -a "$OUT/logs/run_greedy.log"
done
