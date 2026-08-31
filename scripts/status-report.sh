#!/usr/bin/env bash
# Gather a lean4lean status report and print it to stdout.
#
# Used by scripts/monitor-status.sh (periodic ntfy push) but standalone —
# run it directly any time you want the current picture.
#
# Deliberately cheap and non-interfering: the guard build is optional and
# time-boxed, because subagents hold the lake lock for long stretches and a
# status report must never block or perturb their work.

set -uo pipefail
cd /home/vasilii/lean4lean || exit 1

LAKE="$HOME/.elan/bin/lake"

# --- git facts (always cheap) ---
head_line=$(git log --oneline -1 2>/dev/null)
unpushed=$(git log --oneline origin/master..master 2>/dev/null | wc -l | tr -d ' ')
dirty=$(git status --short 2>/dev/null | wc -l | tr -d ' ')
commits_24h=$(git log --oneline --since='24 hours ago' 2>/dev/null | wc -l | tr -d ' ')

# --- sorry counts (cheap; excludes sorryAx mentions and prose) ---
count_sorries() {
  grep -rn "sorry" --include=*.lean "Lean4Lean/$1" 2>/dev/null \
    | grep -vc "sorryAx\|sorry count\|no sorry\|-- .*sorry" || echo 0
}
s_typing=$(count_sorries Theory/Typing)
s_model=$(count_sorries Theory/SetModel)
s_induct=$(count_sorries Theory/Inductive)
s_verify=$(count_sorries Verify)

# --- guards (optional, time-boxed; another stream may hold the lake lock) ---
guards=$(timeout 600 "$LAKE" build Lean4Lean.Verify.Guard 2>&1 \
  | grep -oE "guard [123]: [^✓]*✓[^)]*\)?" | sed 's/^/  /')
if [ -z "$guards" ]; then
  guards="  (guards not sampled — build busy or failing; see git log)"
fi

# --- empty inductives (vacuity sources; see docs/vacuity-ledger.md) ---
# Time-boxed like the guards: needs a built package, and a stream may hold the lock.
empties=$(timeout 180 "$LAKE" env lean scripts/empty-inductives.lean 2>/dev/null \
  | grep -E "^  Lean4Lean" | sed 's/^/  /')
if [ -z "$empties" ]; then
  empties="  (not sampled -- build busy; run scripts/empty-inductives.lean directly)"
fi

# --- axiom count, read from the guard output rather than grepped ---
axioms=$(printf '%s\n' "$guards" | grep -oE "exactly the [0-9]+ frozen axioms" | grep -oE "[0-9]+")
[ -z "$axioms" ] && axioms="?"

cat <<EOF
HEAD: $head_line
commits/24h: $commits_24h | unpushed: $unpushed | dirty files: $dirty

guards:
$guards

axioms: $axioms
empty inductives (vacuity sources -- docs/vacuity-ledger.md):
$empties
sorries — typing $s_typing | model $s_model | inductive $s_induct | verify $s_verify

goal 1 (arena): run 'uv run lka.py run --checker lean4lean-local' in ~/lean-kernel-arena
goal 2: complete when guard 2 prints "proof COMPLETE"
EOF
