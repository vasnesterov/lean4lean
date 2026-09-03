#!/usr/bin/env bash
# Is a Kernel Arena re-run actually needed?
#
# Goal 1 (arena) and goal 2 (kernel_sound) have DISJOINT dependency cones: the
# `lean4lean` executable roots at Main.lean and reaches 40 modules, none of them
# under Lean4Lean/Verify/ or Lean4Lean/Theory/.  So no amount of proof-side churn
# -- including a proof-side file that does not compile -- can change an arena
# result.  Re-run the arena only when a file in the exe cone changes.
#
# Usage: scripts/arena-needed.sh [since-commit]
#   default since-commit comes from docs/.arena-last-green
set -uo pipefail
cd "$(dirname "$0")/.."
SINCE="${1:-$(cat docs/.arena-last-green 2>/dev/null || echo '')}"
CONE=$(python3 - <<'PY'
import re,os
def imports(mod):
    p=mod.replace('.','/')+'.lean'
    if not os.path.exists(p): return []
    return re.findall(r'(?m)^\s*import\s+([A-Za-z0-9_.]+)', open(p,encoding='utf-8').read())
seen=set(); stack=['Lean4Lean.Replay','Export.Parse']
while stack:
    m=stack.pop()
    if m in seen: continue
    seen.add(m); stack.extend(imports(m))
for m in sorted(seen):
    p=m.replace('.','/')+'.lean'
    if os.path.exists(p): print(p)
print('Main.lean'); print('lakefile.toml'); print('lean-toolchain')
PY
)
echo "exe cone: $(echo "$CONE" | wc -l) files, 0 under Verify/ or Theory/ by construction"
if [ -z "$SINCE" ]; then
  echo "NO BASELINE: record one after a green run with"
  echo "  git rev-parse HEAD > docs/.arena-last-green"
  exit 2
fi
CHANGED=$(git diff --name-only "$SINCE" HEAD -- $CONE)
if [ -z "$CHANGED" ]; then
  echo "NOT NEEDED: no exe-cone file changed since $SINCE ($(git rev-parse --short "$SINCE"))."
  echo "The last green arena result still applies to HEAD."
else
  echo "RE-RUN NEEDED: these exe-cone files changed since $SINCE:"
  echo "$CHANGED" | sed 's/^/  /'
fi
