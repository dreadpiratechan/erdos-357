#!/usr/bin/env bash
# Main run, in the order it was executed:
#   1. table 28      : M(1..28) and ALL optimal sets (count(k,n) for n = M(k-1)+1, ... until the first hit)
#   2. ftable ... 68 : for every n = 1..68 separately: count(f(n)+1, n) = 0   (f(n) read from step 1)
#   3. count 28 69   : n = 69 = M(27): no admissible 28-term sequence with a_28 <= 69
#   4. count 29 77   : no admissible 29-term sequence with a_29 <= 77    (this is f(77) = 28)
# The per-n decisions for n = 69..77 are completed by make_f_table.py from steps 1, 3 and 4 using only
# the monotonicity of the predicate "a_k <= n" in n (see README, "f(n) for every n").  Step 2 is capped at
# n = 68 on purpose: a literal per-n run up to 77 would repeat the table's work (~3 h more) for no new
# logical content.  (The first draft of this script ran `ftable ... 77`; it was stopped after step 1 and
# replaced by steps 2-4.)
#
# usage: run_main.sh EXACT_BIN EXACT_DIR CKPT_DIR      [env THREADS, default 8; TABLE_DONE=1 skips step 1]
#   EXACT_BIN  path of the compiled `exact` binary
#   EXACT_DIR  directory in which results/ and logs/ are written.  Use a scratch directory if you do not want
#              to touch the committed results/ and logs/ (the logs are appended to, results/ is overwritten).
#   CKPT_DIR   scratch directory for the resumable task logs (not kept in the package)
# Re-running after an interruption resumes from the task logs; totals are unchanged.
# Total run time about 1.7 hours on an 8-core machine (see README, "Machine and runtimes").
set -eu
BIN="$1"; D="$2"; CK="$3"; T="${THREADS:-8}"

# Informational helpers for the log headers.  They only read machine state and never influence what is computed;
# on a machine without powershell.exe or /proc/meminfo they print "n/a".
now() { date -Is 2>/dev/null || date; }
sha256_of() { { sha256sum "$1" 2>/dev/null || shasum -a 256 "$1"; } | cut -d' ' -f1; }
free_ram_gb() {
  if command -v powershell.exe >/dev/null 2>&1; then
    powershell.exe -NoProfile -Command "[math]::Round((Get-CimInstance Win32_OperatingSystem).FreePhysicalMemory/1MB,2)" 2>/dev/null | tr -d '\r' || echo "n/a"
  elif [ -r /proc/meminfo ]; then
    awk '/^MemAvailable:/ {a=$2} /^MemFree:/ {f=$2} END {printf "%.2f\n", (a ? a : f)/1048576}' /proc/meminfo
  else
    echo "n/a"
  fi
}
cpu_info() {
  if command -v powershell.exe >/dev/null 2>&1; then
    powershell.exe -NoProfile -Command "(Get-CimInstance Win32_Processor).NumberOfLogicalProcessors; (Get-CimInstance Win32_Processor).LoadPercentage" 2>/dev/null | tr -d '\r' | tr '\n' ' ' || echo "n/a"
  elif command -v nproc >/dev/null 2>&1; then
    echo "$(nproc) n/a"
  else
    echo "n/a"
  fi
}

mkdir -p "$D/results" "$D/logs" "$CK"
if [ -z "${TABLE_DONE:-}" ]; then
  {
    echo "# run_main.sh started $(now)"
    echo "# binary sha256: $(sha256_of "$BIN")"
    echo "# free RAM (GB): $(free_ram_gb)"
    echo "# logical CPUs / load %: $(cpu_info)"
  } | tee "$D/logs/main_header.txt"
  "$BIN" table 28 --threads "$T" --out "$D/results" --ckpt "$CK" | tee -a "$D/logs/table_k28.log"
  echo "# table done $(now)" | tee -a "$D/logs/table_k28.log"
fi

"$BIN" ftable "$D/results/M_table.txt" 68 --threads "$T" --out "$D/results" --ckpt "$CK" | tee -a "$D/logs/ftable_n68.log"
echo "# ftable done $(now)" | tee -a "$D/logs/ftable_n68.log"

for kn in "28 69" "29 77"; do
  set -- $kn
  echo "# $(now) free RAM (GB): $(free_ram_gb)" | tee -a "$D/logs/decisions_n69_77.log"
  "$BIN" count "$1" "$2" --threads "$T" --ckpt "$CK/count_k$1_n$2.txt" | tee -a "$D/logs/decisions_n69_77.log"
done
echo "# decisions done $(now)" | tee -a "$D/logs/decisions_n69_77.log"
