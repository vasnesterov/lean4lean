#!/usr/bin/env bash
# Watch vasnesterov/lean4lean for new PR and issue comments.
#
# Emits one stdout line per new comment, so the orchestrator is notified
# when the human reviews a PR or comments on the tracking issue.
#
# Reusable: this is the whole setup. To arm it, run it under the Monitor
# tool (persistent: true). To disable, TaskStop that monitor. To re-enable,
# run this script under Monitor again — the `since` cursor restarts at
# "now", so re-enabling never replays old comments.
#
#   Monitor({ command: "bash scripts/monitor-pr-comments.sh",
#             description: "new comments on vasnesterov/lean4lean PRs and issues",
#             persistent: true, timeout_ms: 3600000 })
#
# The orchestrator posts under the SAME GitHub account as the human, so author
# filtering cannot separate them. Instead the orchestrator appends the marker
# below to every comment it writes, and this script drops those. A comment from
# the human never carries it. Without this the monitor echoes the orchestrator's
# own issue comments back at it, and a real reply would be buried among them.
#
# SELF-TEST BEFORE ARMING. `gh api --jq` does NOT accept `--arg`; passing it makes
# the command fail on every poll, and with stderr swallowed and `|| true` on the
# pipeline the monitor stays alive emitting nothing, forever. That happened on
# 2026-08-30 and the monitor was silently dead for hours. Filtering is now done by
# piping into a real `jq`. Run this script with SELFTEST=1 to check the pipeline
# actually emits a known comment before relying on it.
#
# Env overrides: REPO, POLL (seconds), MARKER, SELFTEST.

set -uo pipefail

REPO="${REPO:-vasnesterov/lean4lean}"
POLL="${POLL:-30}"
MARKER="<!-- l4l-orchestrator -->"   # inlined in the jq exprs below; gh's --jq has no --arg

# Self-test: emit whatever the last 24h holds, then exit. Proves the pipeline works.
if [ "${SELFTEST:-0}" = "1" ]; then
  since=$(date -u -d '24 hours ago' +%Y-%m-%dT%H:%M:%SZ)
  n=$(gh api "repos/$REPO/issues/comments?since=$since&per_page=100" \
      --jq '[.[] | select((.body // "") | contains("<!-- l4l-orchestrator -->") | not)] | length' 2>/dev/null)
  echo "SELFTEST: ${n:-ERROR} unfiltered comment(s) in the last 24h"
  [ -n "$n" ] && [ "$n" != "null" ] && exit 0 || exit 1
fi

last=$(date -u +%Y-%m-%dT%H:%M:%SZ)

while true; do
  now=$(date -u +%Y-%m-%dT%H:%M:%SZ)

  # Both endpoints: issue comments cover PR conversation and issue threads;
  # review comments cover inline code comments, which the other misses.
  # `|| true` on each — one failed request must not kill the monitor.
  gh api "repos/$REPO/issues/comments?since=$last&per_page=100" \
    --jq '.[] | select((.body // "") | contains("<!-- l4l-orchestrator -->") | not)
        | "PR-COMMENT \(.issue_url | split("/") | last) @\(.user.login): \(.body | gsub("\n"; " ") | .[0:400])"' \
    2>/dev/null || true

  gh api "repos/$REPO/pulls/comments?since=$last&per_page=100" \
    --jq '.[] | select((.body // "") | contains("<!-- l4l-orchestrator -->") | not)
        | "PR-REVIEW \(.pull_request_url | split("/") | last) @\(.user.login) on \(.path): \(.body | gsub("\n"; " ") | .[0:400])"' \
    2>/dev/null || true

  last=$now
  sleep "$POLL"
done
