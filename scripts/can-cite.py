#!/usr/bin/env python3
"""Can module X actually cite declaration Y -- or is Y downstream of X?

**The blind spot this closes.** `exists.lean`, `shape.lean`, `users.lean` and the ledger audit all
import the whole default-target population into ONE environment and ask questions of it. So they all
answer "does this exist?" and none answers "is it *available where I need it*?" A declaration can be
proved, hole-free, clean on every watched name -- and still be uncitable at the site that needs it,
because its module sits downstream.

That is not hypothetical. Three case arms of the nested flip need content that exists and is proved
(`addInductR_ordered'`, `keysR_induct`, `addInductR_le`), and **none of the three consumers can see
it**: `Theory/Typing/EnvLemmas.lean` cannot cite `Theory/Inductive/NestedOrdered.lean`, and likewise
for two siblings. **Four consecutive documents in this repo listed those as available**, because every
instrument available said they existed.

Usage:
  python3 scripts/can-cite.py Lean4Lean.Theory.Typing.EnvLemmas Lean4Lean.VEnv.addInductR_ordered
  python3 scripts/can-cite.py <consumer-module> <decl> [<decl> ...]

Prints, per declaration: its defining module, whether the consumer's import closure contains it, and
if not, the modules the consumer would have to gain -- so the answer is actionable, not just negative.
A "no" is a *proof-move or a migration*, not necessarily a missing proof; check which before pricing.
"""
import re, os, sys, subprocess, json

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

def defining_module(decl):
    """Ask the compiled environment where a declaration lives, via exists.lean."""
    env = dict(os.environ, NAMES=decl)
    try:
        out = subprocess.run(['lake', 'env', 'lean', '--run', 'scripts/exists.lean'],
                             capture_output=True, text=True, env=env, timeout=900).stdout
    except Exception as e:
        return None, f"could not run exists.lean: {e}"
    if 'NOT FOUND' in out and decl in out:
        return None, "NOT FOUND in the compiled population"
    m = re.search(r'module (\S+), arity', out)
    return (m.group(1) if m else None), (None if m else "could not parse exists.lean output")

if __name__ == '__main__':
    if len(sys.argv) < 3:
        print(__doc__); sys.exit(2)
    consumer, decls = sys.argv[1], sys.argv[2:]
    cl = closure(consumer)
    if not cl - {consumer}:
        print(f"warning: {consumer} has an empty import closure -- check the module name")
    print(f"consumer: {consumer}  (closure {len(cl)} modules)\n")
    bad = 0
    for d in decls:
        mod, err = defining_module(d)
        if mod is None:
            print(f"  ?  {d}\n       {err}"); bad = 1; continue
        ok = mod in cl
        print(f"  {'YES' if ok else 'NO ':3s} {d}\n       defined in {mod}")
        if not ok:
            bad = 1
            print(f"       {consumer} would have to gain {mod} (or the declaration must move upstream)")
    print("\nA NO is an import-order fact, not a missing proof. Ask whether the *statement* elaborates")
    print("at the consumer's position with only upstream data -- if it does, this is a proof move or a")
    print("migration, which is far cheaper than it looks.")
    sys.exit(bad)
