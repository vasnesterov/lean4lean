#!/usr/bin/env python3
"""Enforce the refinement chain's direction where it is actually enforceable.

The chain is  Verify/ -> Theory/ -> Theory/SetModel/ -> Foundation.  An import the other way
inverts it.  Four `Theory/` files acquired such an import in one session, and one of them reached
`Theory/SetModel/` -- the deepest layer -- dragging a 46-module `Verify/` sub-closure behind a
single edge that used **zero** constants from it.  Nothing detected that; the build was green
throughout, because a green build only proves the absence of a *cycle*, not of an inversion.

HARD RULE (exit 1): no module under Lean4Lean/Theory/SetModel/ may reach Lean4Lean.Verify.* .
   That layer is the model, below the abstract spec; it can have no legitimate need of the checker.

SOFT REPORT (exit 0): `Theory/` files that import `Verify/` directly, with counts.  This is drift
   to watch, not an error to fail on.  **A file appearing here with a *small* constant count is the
   suspicious case: that is what a parked declaration looks like.**

   Measured 2026-09-04, after the `ProjGen` cluster migration -- four files, one direct import each:
     EtaGuardLand      111 constants (54 from `Verify.Typing.ConstSpine`)  legitimate
     NoConfRepair       95 constants (39 from ConstSpine)                  legitimate
     StructEtaPrice     52 constants (45 from refutation witnesses)        legitimate, weaker
     CommutationLemmas   8 constants                                       NOT legitimate
   The last one is the heuristic working: before the migration it cited **96**, the exact bottom of
   the band this docstring used to cite as evidence of legitimacy.  The migration therefore turned a
   large justified inversion into a small suspicious one -- progress, because the finish is now
   cheap, but not the same as done.  Its 7 residual declarations have a combined cone of 703 of
   which exactly 7 are under `Verify/` (themselves), so extracting them takes it to 0.

Run: python3 scripts/layer-check.py
"""
import re, os, sys, pathlib

def imports(mod):
    p = mod.replace('.', '/') + '.lean'
    if not os.path.exists(p): return []
    return re.findall(r'(?m)^\s*import\s+([A-Za-z0-9_.]+)', open(p, encoding='utf-8').read())

def closure(mod):
    seen, stack = set(), [mod]
    while stack:
        m = stack.pop()
        if m in seen: continue
        seen.add(m); stack.extend(imports(m))
    return seen

def mods_under(prefix):
    root = pathlib.Path(prefix.replace('.', '/'))
    if not root.exists(): return []
    return ['.'.join(p.with_suffix('').parts) for p in sorted(root.rglob('*.lean'))]

fail = 0
print("HARD RULE: no Theory/SetModel/ module may reach Lean4Lean.Verify.*")
setmodel = mods_under('Lean4Lean/Theory/SetModel')
worst = []
for m in setmodel:
    bad = sorted(x for x in closure(m) if x.startswith('Lean4Lean.Verify'))
    if bad:
        worst.append((m, bad)); fail = 1
if worst:
    for m, bad in worst:
        print(f"  VIOLATION {m}")
        print(f"    reaches {len(bad)} Verify module(s), e.g. {bad[:3]}")
    print("\n  Fix by moving the needed declaration DOWN into Theory/SetModel/ or Theory/Inductive/,")
    print("  not by moving the Theory/ file up -- that pushes the inversion deeper.")
else:
    print(f"  ok - {len(setmodel)} module(s) checked, none reaches Verify/")

print("\nSOFT REPORT: Theory/ files importing Verify/ directly (drift, not failure)")
rows = []
theory = mods_under('Lean4Lean.Theory')
for m in theory:
    direct = [x for x in imports(m) if x.startswith('Lean4Lean.Verify')]
    if direct:
        rows.append((m, direct))
rows.sort()
for m, direct in rows:
    print(f"  {m}  <- {len(direct)} direct Verify import(s)")
    for d in direct: print(f"      {d}")
print(f"  ({len(rows)} of {len(theory)} Theory modules import Verify/ directly)")

# TRANSITIVE dependence.  Measured 2026-09-04: 4 direct but *10* transitive -- and the gap
# matters, because citability follows the transitive closure, not the direct edge.  I recorded
# "exactly 4 inversions" in ORCHESTRATOR.md and then found `scripts/can-cite.py` answering YES
# for a `Verify/` declaration from a `Theory/` file with no direct import at all.  A direct-edge
# count answers "who wrote the bad import"; only the closure answers "who is downstream of
# Verify/", which is the question that decides what a Theory file may cite.
print("\nSOFT REPORT: Theory/ files TRANSITIVELY downstream of Verify/")
trans = []
for m in theory:
    v = sorted(x for x in closure(m) if x.startswith('Lean4Lean.Verify'))
    if v:
        gates = sorted({i for i in imports(m)
                        if i.startswith('Lean4Lean.Verify')
                        or any(x.startswith('Lean4Lean.Verify') for x in closure(i))})
        trans.append((m, v, gates))
trans.sort()
for m, v, gates in trans:
    print(f"  {m}  <- {len(v)} Verify module(s), entering via: {', '.join(gates)}")
print(f"  ({len(trans)} of {len(theory)} Theory modules are downstream of Verify/; "
      f"{len(theory) - len(trans)} are clean)")
