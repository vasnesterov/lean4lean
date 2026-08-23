#!/usr/bin/env bash
# Periodic status report to ntfy.
#
# Every INTERVAL seconds: build a status report and POST it to the ntfy
# topic, then emit one stdout line so the orchestrator sees it fired.
#
# Reusable: this is the whole setup. To arm it, run it under the Monitor
# tool (persistent: true). To disable, TaskStop that monitor. To re-enable,
# run this script under Monitor again — no other state to restore.
#
#   Monitor({ command: "bash scripts/monitor-status.sh",
#             description: "2-hourly lean4lean status to ntfy",
#             persistent: true, timeout_ms: 3600000 })
#
# Env overrides: NTFY_TOPIC, INTERVAL (seconds), FIRST_DELAY (seconds).

set -uo pipefail
cd /home/vasilii/lean4lean || exit 1

NTFY_TOPIC="${NTFY_TOPIC:-https://ntfy.sh/claude-1p7eb443qbfeijf1y1ov}"
INTERVAL="${INTERVAL:-7200}"        # 2 hours
FIRST_DELAY="${FIRST_DELAY:-7200}"  # don't fire immediately on arm

sleep "$FIRST_DELAY"

while true; do
  body=$(bash scripts/status-report.sh 2>&1)

  code=$(curl -s -o /dev/null -w "%{http_code}" --max-time 30 \
    -H "Title: lean4lean status" \
    -H "Tags: bar_chart" \
    -d "$body" \
    "$NTFY_TOPIC" 2>/dev/null) || code="curl-failed"

  # One event line per cycle. Includes the HEAD subject so a glance at the
  # notification says whether anything moved, and surfaces push failures
  # rather than failing silently.
  head_subject=$(git log --format=%s -1 2>/dev/null | cut -c1-60)
  if [ "$code" = "200" ]; then
    echo "status pushed to ntfy (HTTP 200) — HEAD: $head_subject"
  else
    echo "STATUS PUSH FAILED (HTTP $code) — HEAD: $head_subject"
  fi

  sleep "$INTERVAL"
done
