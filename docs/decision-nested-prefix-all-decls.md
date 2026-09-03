# Decision needed: extend the `_nested` prefix check from inductives to all declarations

**Status: prepared, not applied. This needs your call, and it is a divergence from the C++ kernel.**

## The one-line change

`Lean4Lean/Environment.lean:12`, in `checkConstantVal`, beside the existing `checkName`:

```lean
  checkName env v.name allowPrimitive
  checkNoNestedAuxName v.name        -- ← the proposed addition
```

`checkNoNestedAuxName` already exists and is already used, for inductives only, from the two
call sites in `Lean4Lean/Inductive/Add.lean` (:1104, :1109) that landed in PR #45 with your
approval.

## Why it came up

Today's round proved that the invariant the restoration layer wants — no `_nested`-prefixed
constant in the environment (`VEnv.NoNestedN`) — is **established for the inductive branch and
only that branch**. This is machine-checked by a `#eval` in
`Lean4Lean/Verify/Inductive/RestoreFaithful.lean` that fails the build if any flag flips:

| declaration | today |
|---|---|
| `inductive _nested.Zzz` | **REJECTED** (the PR #45 check firing; this shape was accepted before) |
| `axiom _nested.zzz` | **ACCEPTED** |
| `def _nested.ddd` | **ACCEPTED** |

`checkConstantVal` → `checkName` (`Lean4Lean/Environment/Basic.lean:54`) tests only "already
declared" and `primitives`. So the invariant cannot be established by induction on `TrEnv'`: the
`axiom` / `defn` / `opaque` / `quot` cases have nothing to supply `VEnv.NoNestedN.addConst`'s
name hypothesis.

## What the change buys

- `NoNestedN` becomes establishable across the whole of `addDecl`, so the spec may **assume**
  environment cleanliness legitimately instead of carrying it. Three `RestoreData` obligations
  are already discharged from the inductive gate alone; the fourth (`RestoreData.head`,
  `NestedRestore.lean:304`) is currently reduced to a residual about `aux2nested`'s values, and
  a global invariant is the route that retires it.
- It removes a real asymmetry: we reject a *nested-inductive* aux name but accept the identical
  name as an axiom, which is the weaker half of a check that exists to protect a namespace.

## What it costs

- **It is a divergence from the C++ kernel, and a wider one than PR #45.** The C++
  `check_name` (`~/lean4/src/kernel/environment.cpp:102`, called from `check_constant_val` at
  :128) tests only already-declared and primitives — verified in the source. So C++ accepts
  `axiom _nested.zzz`, and after this change lean4lean would not. It goes in `divergences.md`.
- **The arena cost is unmeasured.** `Lean4Lean/Environment.lean` **is** in the checker
  executable's dependency cone (confirmed: `scripts/arena-needed.sh`), so this change requires a
  Kernel Arena re-run before it can be trusted. The current green result (185/6/0) would no
  longer apply. I have not measured it because measuring means editing an exe-cone file while
  proof streams are building against the tree.
- It rejects declarations no real Lean code should contain — the elaborator's `_nested` auxiliary
  block never reaches the environment at all (I measured **zero** such constants after declaring
  a genuinely nested inductive) — but "should not" is not "cannot", and only the arena run turns
  that into evidence.

## Options

- **(a) Apply it.** I make the one-line edit, run the arena, record the divergence, and report
  the result. If the arena regresses I revert and tell you.
- **(b) Measure first, then decide.** I apply it locally, run the arena, report the number, and
  revert — you decide with the cost in hand. Costs one arena run and no commitment.
- **(c) Leave it.** The inductive-branch-only invariant stands, `RestoreData.head` keeps its
  residual, and `RestoreFaithful.lean`'s `#eval` guard will tell us if a future toolchain
  changes the answer on its own.

My recommendation is **(b)**: the only real unknown is the arena, it is cheap to measure, and the
proof-side benefit is genuine but not on the critical path — today's round bypassed the hole that
was blocking the nested route, so nothing is waiting on this.

## Related, and not needing a decision

Four stale docstrings were found that overstate what is unchecked; they are documentation-only
and I will fix them regardless:

1. `NestedRestore.lean:299`, `:302` — "Not checked by the implementation" is now false.
2. `NestedRestore.lean:308` — field `auxRec` is derivable from the gate, so it is removable.
3. `Inductive/Add.lean`, `checkNoNestedAuxName`'s docstring — says neither kernel checks this and
   the two fields stay hypotheses; both halves are now false for lean4lean.
4. `Verify/Inductive/ProjNoNested.lean:367` — says `NoNestedN` is "not provable without
   `NestedRestore.lean` §8.2's missing check"; that check landed in PR #45.
5. `docs/decision-nested-prefix.md` still reads as an open decision; option (a) landed.
