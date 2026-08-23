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
# Env overrides: REPO, POLL (seconds).

set -uo pipefail

REPO="${REPO:-vasnesterov/lean4lean}"
POLL="${POLL:-30}"

last=$(date -u +%Y-%m-%dT%H:%M:%SZ)

while true; do
  now=$(date -u +%Y-%m-%dT%H:%M:%SZ)

  # Both endpoints: issue comments cover PR conversation and issue threads;
  # review comments cover inline code comments, which the other misses.
  # `|| true` on each — one failed request must not kill the monitor.
  gh api "repos/$REPO/issues/comments?since=$last&per_page=100" \
    --jq '.[] | "PR-COMMENT \(.issue_url | split("/") | last) @\(.user.login): \(.body | gsub("\n"; " ") | .[0:400])"' \
    2>/dev/null || true

  gh api "repos/$REPO/pulls/comments?since=$last&per_page=100" \
    --jq '.[] | "PR-REVIEW \(.pull_request_url | split("/") | last) @\(.user.login) on \(.path): \(.body | gsub("\n"; " ") | .[0:400])"' \
    2>/dev/null || true

  last=$now
  sleep "$POLL"
done
