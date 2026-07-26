#!/bin/zsh
# Rebuild the LRAT-Catcher-backed size-11 theorem with an auditable progress log.
#
# Usage (from LeanVerification/):
#   zsh scripts/build_lrat11_with_progress.sh [log-file]
#
# `native_decide` evaluates the checker as one closed native computation, so
# LRAT-Catcher does not expose an action-level counter.  The percentage below
# is consequently a wall-clock estimate based on a successful 757-second run,
# not a claim about the number of LRAT actions already checked.

set -euo pipefail

root=${0:A:h:h}
cd "$root"

baseline_seconds=${LRAT11_BASELINE_SECONDS:-757}
interval_seconds=${LRAT11_PROGRESS_INTERVAL_SECONDS:-30}
log_file=${1:-"/private/tmp/wilkies-lrat11-$(date +%Y%m%d-%H%M%S).log"}

exec > >(tee -a "$log_file") 2>&1

echo "[$(date -Iseconds)] LRAT-Catcher replay started"
echo "certificate actions: 6,271,474 additions + 2,323,128 deletions"
echo "baseline: ${baseline_seconds}s; log: $log_file"

lake build Wilkies.LRAT11 &
build_pid=$!
start_seconds=$(date +%s)

while kill -0 "$build_pid" 2>/dev/null; do
  now_seconds=$(date +%s)
  elapsed_seconds=$((now_seconds - start_seconds))
  remaining_seconds=$((baseline_seconds - elapsed_seconds))
  if (( remaining_seconds > 0 )); then
    estimate="about ${remaining_seconds}s remaining (baseline estimate)"
  else
    estimate="past the baseline; continuing"
  fi

  lean_stats=$(ps -ax -o pid=,rss=,etime=,command= |
    awk '/[l]ean .*Wilkies\/LRAT11\.lean/ { printf "pid=%s rss=%sKiB elapsed=%s", $1, $2, $3 }')
  if [[ -z "$lean_stats" ]]; then
    lean_stats="waiting for Lean worker"
  fi
  memory_free=$(memory_pressure -Q 2>/dev/null |
    awk -F': ' '/System-wide memory free percentage/ { print $2 }')
  echo "[$(date -Iseconds)] elapsed=${elapsed_seconds}s; $estimate; $lean_stats; system-free=${memory_free:-unknown}"
  sleep "$interval_seconds"
done

wait "$build_pid"
echo "[$(date -Iseconds)] LRAT-Catcher replay completed successfully"
