#!/bin/zsh
# Rebuild the LRAT-Catcher-backed size-11 theorem with an auditable progress log.
#
# Usage (from LeanVerification/):
#   zsh scripts/build_lrat11_with_progress.sh [log-file]
#
# `native_decide` evaluates the checker as one closed native computation, so
# LRAT-Catcher does not expose an action-level counter.  This script therefore
# reports elapsed wall-clock time only.

set -euo pipefail

root=${0:A:h:h}
cd "$root"

expected_seconds=${LRAT11_EXPECTED_SECONDS:-900}
interval_seconds=${LRAT11_PROGRESS_INTERVAL_SECONDS:-100}
log_file=${1:-"/private/tmp/wilkies-lrat11-$(date +%Y%m%d-%H%M%S).log"}

exec > >(tee -a "$log_file") 2>&1

echo "[$(date -Iseconds)] LRAT-Catcher replay started"
echo "This should take roughly ${expected_seconds} seconds ($((expected_seconds / 60)) minutes)..."
echo "log: $log_file"

lake build Wilkies.LRAT11 &
build_pid=$!
start_seconds=$(date +%s)
next_report=$interval_seconds

while kill -0 "$build_pid" 2>/dev/null; do
  sleep 1
  if ! kill -0 "$build_pid" 2>/dev/null; then
    break
  fi
  now_seconds=$(date +%s)
  elapsed_seconds=$((now_seconds - start_seconds))
  while (( elapsed_seconds >= next_report )); do
    echo "${next_report} seconds elapsed..."
    next_report=$((next_report + interval_seconds))
  done
done

wait "$build_pid"
echo "[$(date -Iseconds)] LRAT-Catcher replay completed successfully"
