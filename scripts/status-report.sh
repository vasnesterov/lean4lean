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

# --- the REAL hole census, over the whole built population ---
# Not a grep.  On 2026-08-29 a grep over these same trees reported 89 holes when
# the true number was 21: it counted docstrings, prose discussing holes, and the
# word inside identifiers.  `scripts/sorry-census-all.lean` takes its population
# from the filesystem (mirroring the lakefile globs) rather than from a fixed
# import list, so it also sees ORPHAN modules -- built by the glob, imported by
# nothing -- which every other instrument in this repo is blind to.
# Time-boxed like the guards: a stream may hold the lake lock.
census=$(timeout 600 "$LAKE" env lean --run scripts/sorry-census-all.lean 2>/dev/null)
holes=$(printf '%s\n' "$census" | grep -oE "unioned across both passes: [0-9]+" | grep -oE "[0-9]+")
[ -z "$holes" ] && holes="not sampled"
orphans=$(printf '%s\n' "$census" | grep -oE "^ORPHAN modules \(([0-9]+)\)" | grep -oE "[0-9]+")
[ -z "$orphans" ] && orphans="?"
# In a default target, on disk, no .olean.  Usually a stream's in-flight file;
# if it persists with no stream running, something in the tree does not build.
unbuilt=$(printf '%s\n' "$census" | grep -oE "in population but NOT BUILT: [0-9]+" | grep -oE "[0-9]+")
[ -z "$unbuilt" ] && unbuilt="?"
hole_list=$(printf '%s\n' "$census" | grep -E "^  Lean4Lean\..*\[Lean4Lean\." | sed 's/^/  /')
[ -z "$hole_list" ] && hole_list="  (not sampled -- build busy; run scripts/sorry-census-all.lean directly)"

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
holes (real census, whole built population): $holes
$hole_list
orphan modules (built, imported by nothing): $orphans
in a default target but NOT BUILT: $unbuilt  <- in-flight stream files, or something broken

goal 1 (arena): run 'uv run lka.py run --checker lean4lean-local' in ~/lean-kernel-arena
goal 2: complete when guard 2 prints "proof COMPLETE"
EOF
