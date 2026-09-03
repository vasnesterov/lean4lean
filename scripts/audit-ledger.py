#!/usr/bin/env python3
"""Re-verify every `cone N` figure in docs/vacuity-ledger.md against the compiled environment.

Why this exists.  Three times in one day I recorded a cone size or arity that was wrong, every
time by copying it from an earlier note of mine instead of re-reading `scripts/exists.lean`'s
output.  My own records had become a source I trusted more than the tool that produced them.
Ledger rows are append-only and quoted in briefs for weeks, so a wrong figure propagates.

Pairs each `cone <N>` / `arity <N>` with the nearest preceding backticked Lean name on the same
row, then checks the pair against the environment.  Heuristic by nature: it reports what it could
not pair rather than guessing, and a MISMATCH is a claim to re-read by hand, not proof of error --
a cone legitimately changes when the tree around a declaration changes.

Usage:  lake env lean --run scripts/exists.lean $(python3 scripts/audit-ledger.py --names)
        python3 scripts/audit-ledger.py --check /tmp/exists-output.txt
Or just: scripts/audit-ledger.sh
"""
import re, sys, pathlib

LEDGER = pathlib.Path("docs/vacuity-ledger.md")
NAME = re.compile(r'`(\.?[A-Za-z_][A-Za-z0-9_.\'!?]*)`')
# How close a name must sit before a figure to be its subject.  Without a window the nearest
# *matching* name can be several declarations back, which produced 59 "mismatches" on the first
# run, nearly all of them pairing artefacts rather than recording errors -- an instrument crying
# wolf, which is the failure I built the arena-needed check to avoid.
WINDOW = 90
FIG  = re.compile(r'\b(cone|arity)\s+\*{0,2}(\d+)\*{0,2}')

def pairs():
    out, unpaired = [], 0
    for lineno, line in enumerate(LEDGER.read_text(encoding='utf-8').splitlines(), 1):
        if not line.startswith('|'):
            continue
        # Rows write follow-on declarations as `.csubstTy_WF`, meaning "same namespace as the
        # last full name".  Resolve those, or every figure after the first on a row pairs wrong.
        names, last_ns = [], None
        for m in NAME.finditer(line):
            raw = m.group(1)
            if raw.startswith('.'):
                if last_ns is None:
                    continue
                full = last_ns + raw
            else:
                if '.' not in raw:
                    continue
                full = raw
                last_ns = raw.rsplit('.', 1)[0]
            names.append((m.start(), full))
        for m in FIG.finditer(line):
            near = [n for pos, n in names if 0 <= m.start() - pos <= WINDOW]
            if not near:
                unpaired += 1
                continue
            out.append((lineno, near[-1], m.group(1), int(m.group(2))))
    return out, unpaired

if __name__ == '__main__':
    ps, unpaired = pairs()
    if '--names' in sys.argv:
        seen, order = set(), []
        for _, n, _, _ in ps:
            for cand in (n if n.startswith('Lean4Lean.') else 'Lean4Lean.' + n, n):
                if cand not in seen:
                    seen.add(cand); order.append(cand)
        print(' '.join(order))
    elif '--check' in sys.argv:
        text = pathlib.Path(sys.argv[sys.argv.index('--check') + 1]).read_text(encoding='utf-8')
        actual = {}
        cur = None
        for line in text.splitlines():
            m = re.match(r'FOUND\s+(\S+)', line)
            if m: cur = m.group(1); continue
            m = re.search(r'arity (\d+), cone (\d+)', line)
            if m and cur: actual[cur] = (int(m.group(1)), int(m.group(2))); cur = None
        bad = miss = ok = 0
        for lineno, name, kind, val in ps:
            key = next((c for c in (name if name.startswith('Lean4Lean.') else 'Lean4Lean.' + name, name) if c in actual), None)
            if key is None:
                miss += 1; continue
            ar, co = actual[key]
            got = ar if kind == 'arity' else co
            if got != val:
                bad += 1
                print(f"MISMATCH row~{lineno}: {name} recorded {kind} {val}, actual {kind} {got}")
            else:
                ok += 1
        print(f"\nchecked {ok+bad} figures against the environment: {ok} agree, {bad} MISMATCH")
        print(f"{miss} figures whose name did not resolve (renamed, or paired to the wrong name)")
        print(f"{unpaired} figures with no backticked name before them on the row")
        print("\nA MISMATCH is a claim to re-read, not proof of error: a cone moves when the tree")
        print("around a declaration moves. What it rules out is a figure nobody has looked at since.")
