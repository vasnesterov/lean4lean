#!/usr/bin/env python3
"""Standing check: every proof module must be inside the census's import closure.

`scripts/sorry-census.lean` and `scripts/dup-names.lean` measure the closure of
`Lean4Lean.Verify.Guard` + `Lean4Lean.Experimental.ConeJoin`.  A module outside that
closure is INVISIBLE to both: its holes are missing from the census and a duplicate
name in it is reported as "no duplicates".

This has now bitten three times:
  * 2026-08-30  `Theory/Typing/PiLevelPin.lean` -- a hole-count rise was misread as
                tree growth when it was really under-measurement.
  * 2026-08-31  `Theory/Equiconsistency.lean` -- the single statement `kernel_sound`
                most needs (`Consistent ZFC+Inacc -> leanTTConsistent`) was a `sorry`
                that NOTHING imported, so it had never been counted at all.
  * 2026-08-31  `SortUniqDown` <- `UniqSort`, a two-module orphan island holding a
                name collision with `BaseUniqChain` that `dup-names` could not see,
                despite `DescendRefute.lean:237` having written "if both survive, dedupe".

Run:  python3 scripts/cone-orphans.py
Exits 1 and lists the offenders if any proof module is orphaned.  Fix by adding the
module to the leaf-import block in `Lean4Lean/Experimental/ConeJoin.lean`.
"""
import os, re, sys

ROOTS = ['Lean4Lean.Verify.Guard', 'Lean4Lean.Experimental.ConeJoin']

# Deliberately outside the measured cone.
def excluded(mod: str) -> bool:
    return (mod.startswith('Lean4Lean.Experimental.')   # scratch space, not the proof
            or mod.startswith('Lean4Lean.Tests.')       # test executables
            or mod in {'Lean4Lean.Tests', 'Lean4Lean.Replay',
                       # stale aggregator stubs that nothing imports; harmless, but they
                       # list only a handful of modules each and are not a cone root.
                       'Lean4Lean.Theory', 'Lean4Lean.Verify'})

def main() -> int:
    mods = {}
    for root, _dirs, files in os.walk('Lean4Lean'):
        for f in files:
            if f.endswith('.lean'):
                path = os.path.join(root, f)
                mods[path[:-5].replace(os.sep, '.')] = path
    imports = {}
    for mod, path in mods.items():
        with open(path, encoding='utf-8') as fh:
            imports[mod] = [m.group(1) for m in
                            (re.match(r'^import\s+(\S+)', line) for line in fh) if m]
    seen, stack = set(), list(ROOTS)
    while stack:
        mod = stack.pop()
        if mod in seen:
            continue
        seen.add(mod)
        stack.extend(imports.get(mod, []))
    orphans = sorted(m for m in mods if m not in seen and not excluded(m))
    print(f"{len(mods)} modules, {len(set(mods) & seen)} in the census cone, "
          f"{len(orphans)} orphaned (excluding Experimental/ and Tests/)")
    if orphans:
        print("\nORPHANED -- invisible to sorry-census.lean and dup-names.lean.")
        print("Add each to the leaf-import block in Lean4Lean/Experimental/ConeJoin.lean:\n")
        for m in orphans:
            print(f"import {m}")
        return 1
    print("no orphaned proof modules")
    return 0

if __name__ == '__main__':
    sys.exit(main())
