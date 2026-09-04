#!/usr/bin/env bash
# Post a PR/issue comment as the orchestrator, always carrying the suppression marker.
#
# Why this exists. `scripts/monitor-pr-comments.sh` filters out comments containing
# `<!-- l4l-orchestrator -->` so that my own posts do not wake me as if they were the user's.
# I have now forgotten that marker twice: once early in the session (three comments, fixed
# retroactively, selftest 4 -> 2) and once on PR #46, which echoed straight back through the
# monitor. Both times the fix was retroactive editing. Resolve is clearly not the mechanism.
#
# Usage:  scripts/pr-comment.sh <pr-number> <<'BODY'
#         ...markdown...
#         BODY
#
# Reads the body from stdin so heredocs work without quoting games, appends the marker, posts to
# vasnesterov/lean4lean only -- never upstream, per CLAUDE.md.
set -euo pipefail
PR="${1:?usage: pr-comment.sh <pr-number>  (body on stdin)}"
REPO="vasnesterov/lean4lean"
BODY="$(cat)"
if [ -z "${BODY//[[:space:]]/}" ]; then
  echo "refusing to post an empty comment" >&2; exit 1
fi
case "$BODY" in
  *"<!-- l4l-orchestrator -->"*) ;;                       # already marked
  *) BODY="$BODY"$'\n\n'"<!-- l4l-orchestrator -->" ;;
esac
printf '%s' "$BODY" | gh pr comment "$PR" --repo "$REPO" --body-file -
# Selftest: after posting, the monitor should see zero unmarked comments from me on this PR.
UNMARKED=$(gh api "repos/$REPO/issues/$PR/comments" \
  --jq '[.[] | select((.body // "") | contains("<!-- l4l-orchestrator -->") | not)] | length' 2>/dev/null || echo "?")
echo "unmarked comments now visible to the monitor on PR $PR: $UNMARKED (a nonzero count that is not the user's is a bug)"
