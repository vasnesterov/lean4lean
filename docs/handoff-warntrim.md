# handoff-warntrim — the `unusedSectionVars` class, worked to zero in-repo

**Commit base:** `42bf8a5`.  **Date:** 2026-09-03.

## Result

`lake build 2>&1 | grep "automatically included section variable"` printed **18** lines at
the start of this round (17 in `Lean4Lean/`, 1 in the pinned `Foundation` dependency).  It
now prints **1** — the Foundation one, which is out of scope (pinned dep, read-only).

**New baseline: 0 in-repo warnings of this class.**

The fix in every case is the linter's own suggestion, `omit […] in` on the line above the
declaration (above its doc comment — a doc comment must abut its declaration, so
`/-- … -/` then `omit … in` then `theorem` is a **parse error**; `omit … in` then `/-- … -/`
then `theorem` is correct).

## Where the relayed characterisation was right, and where it was wrong

The brief said: *"all 17 in-repo warnings are instance binders with zero explicit
`@`-applications in the tree, so each one's ripple is one `omit … in` line and no consumer
edits — 17 one-line edits waiting on file ownership."*

**Right:** all 17 are instance binders (the linter prints them bracketed).  Zero
`@`-applications at consumers, and in the event **zero consumer proof edits were needed** —
no proof term anywhere was altered.  The binder total is **exactly 34** over 17 theorems in
6 files, as relayed (7×`[Params]` + 4 + 7×3 + 2×1 = 34).  `Verify/` has zero warnings of
this class, as relayed; all in-repo ones are in `Theory/`.

**Wrong, and this is the finding:** the ripple is **not** 17 one-line edits.  It is **35
`omit … in` lines across 8 files** — 17 at the reported sites and **18 cascade declarations**
that became newly-unused-in only *after* an upstream trim.  Two of those files
(`Theory/Typing/KSite7Rows.lean`, `Theory/Typing/KKetaRow.lean`) carried **none** of the 17.

The mechanism is specific and worth remembering.  A `refParams_*` lemma proved by applying
`refParams_no_kstep` at the concrete instance elaborated to `@refParams_no_kstep inst h`,
where `inst` was the *ambient section variable* — silently filling the callee's unused
instance argument.  That is what made `[Params]` "used" at the caller.  Trim the callee and
the caller's own `[Params]` goes unused, so the class propagates **up the call graph, across
module boundaries**, until a fixed point.  Depths observed: `KEta.lean` took two rounds and
went from 1 warning to 9 `omit` lines; `KSite7Rows.lean` took two rounds from a standing
start of zero.

Per-file, `omit` lines added:

| file | reported | cascade | total |
|---|---|---|---|
| `Theory/Typing/KDescend.lean` | 3 | 1 | 4 |
| `Theory/Typing/KEta.lean` | 1 | 8 | 9 |
| `Theory/Typing/KMeasure.lean` | 1 | 3 | 4 |
| `Theory/Typing/KSite7.lean` | 2 | 3 | 5 |
| `Theory/Typing/KSite7Rows.lean` | 0 | 2 | 2 |
| `Theory/Typing/KKetaRow.lean` | 0 | 1 | 1 |
| `Theory/SetModel/Cnst.lean` | 1 | 0 | 1 |
| `Theory/SetModel/IndInterp.lean` | 9 | 0 | 9 |
| **total** | **17** | **18** | **35** |

Note the SetModel side cascaded **not at all** — its unused binders are genuinely leaf
facts, whereas the `Typing` side's `[Params]` was a chain.

**File-ownership note.**  `KSite7Rows.lean` and `KKetaRow.lean` are outside the 6 files that
carried the 17.  They were edited anyway (one `omit [Params] in` line each, plus one more in
`KSite7Rows`), because leaving them would have *introduced* warnings of this class that the
baseline did not have.  Neither is on the concurrent-stream exclusion list and neither was
modified in `git status` at the time.  Flagging it explicitly since it exceeds the literal
grant.

## The stated "mechanical" bar is the wrong bar

The brief set the bar at *"existing proof term accepted unchanged, `#print axioms` identical
before and after."*  The first half held everywhere: **no proof text was changed at all**,
only `omit` lines inserted.  The second half **does not hold, and should not** — trimming an
unused instance binder *shrinks* the axiom set whenever the omitted class's own definition
carries axioms.  Measured, by reconstructing each untrimmed declaration verbatim (same proof
text, binders auto-included) in a scratch module:

| declaration | axioms before | axioms after |
|---|---|---|
| `Lean4Lean.SetModel.oracleExtend_append` | `propext, Classical.choice, Quot.sound` | `propext, Quot.sound` |
| `Lean4Lean.VEnv.refQ_not_noApp` | `propext, Quot.sound` | *none* |
| `Lean4Lean.VEnv.refQ2_not_noApp` | `propext, Quot.sound` | *none* |
| `Lean4Lean.Pattern.Matches.const_shape` | `propext, Quot.sound` | *none* |
| `Lean4Lean.Pattern.Matches.const'` | `propext, Quot.sound` | `Quot.sound` |
| `Lean4Lean.VEnv.measure_witness` | `propext, Quot.sound` | `propext` |
| `Lean4Lean.VEnv.refParams_no_kstep` | `propext, Classical.choice, Quot.sound` | unchanged |

The root cause: **`#print axioms Lean4Lean.VEnv.Params` is `[propext, Quot.sound]`**.  A
theorem whose *type* merely mentions `Params` inherits those, so no `[Params]` binder is
ever axiom-free, however proof-irrelevant it is.  And `oracleExtend_append` was carrying
`Classical.choice` **only** through the four SetModel instance binders its proof never
touched.  So the right bar for this class is *axioms after ⊆ axioms before*, with any strict
shrinkage counted as the point rather than as a red flag.

`#print axioms` for all 35 touched declarations, after the trim, is in the reproduction
recipe below; the 28 not tabulated above are unchanged (each already carried the ambient
`refParams`/`refEnv` cone's `propext, Classical.choice, Quot.sound`, sometimes with
`sorryAx`, from constants their *statements* mention).

## Vacuity, checked rather than assumed

Trimming an instance binder makes a statement **strictly stronger**, so it cannot be
weakened into vacuity — but the *untrimmed* one can have been vacuous, and that matters for
what the tree previously established.  Checked both ways:

- `[Params]` is **inhabited**: `refParams` (`Theory/Typing/DescendRefute.lean:138`) and
  `PropLoopParams`.  So the 17 `[Params]` statements were not vacuous before; the trim is a
  genuine strengthening, not a repair.
- The SetModel binders reach the **strong form**: at `V := ℕ` there is no
  `Membership ℕ ℕ` = `SetStructure ℕ` at all, so the untrimmed `oracleExtend_append` had
  **no instance whatsoever** there, while the trimmed one is applied there; and at `V := Bool`
  with an ad-hoc membership there is no `⊧* 𝗭𝗙` and no `⊧* 𝗔𝗖` instance, while the five
  trimmed `ite_*_definable*` lemmas all instantiate.  Probe and expected output are in
  `docs/soundness-ledger.md` (§ *What the definability apparatus actually assumes*).

## Target 2, re-measured and recorded

The brief's corrected relay is **confirmed exactly**: all 9 `IndInterp` lemmas need no AC;
7 of the 9 need no ZF and no `Nonempty V`; the two exceptions (`indStep₂_eq`,
`indStep_at_mono`) use ZF but not AC; `Cnst.lean:255`'s `oracleExtend_append` needs none of
the four, not even `SetStructure V`.  Full table, method, witnesses and axiom consequence
written into **`docs/soundness-ledger.md`**, § *What the definability apparatus actually
assumes — measured, 2026-09-03*.

## Verification state

- **Census before and after: 13 holes, identical list** (`scripts/sorry-census.lean`).
- **`lake build Lean4Lean.Verify.Guard`: 1144 jobs, completed successfully.**  Guard 1: 24
  frozen axioms ✓.  Guard 2: `kernel_sound` axioms within whitelist ✓ (proof INCOMPLETE,
  `sorryAx` present — unchanged).  Guard 3: 2/2 implementation gaps ✓.
- Frozen files (`Verify/Soundness.lean`, `Verify/Axioms.lean`, `Verify/Guard.lean`) were not
  touched, not even read-modified.  No file on the concurrent-stream exclusion list was
  touched.
- **Full `lake build`: 1593 of 1594 jobs succeed.**  The single failure is
  `Lean4Lean/Verify/Inductive/ValAtPrice.lean`, an **untracked** file another stream is
  mid-writing: `Unknown constant Lean4Lean.VExpr.constsIn_mkPi_body`, `Unknown identifier
  ctxConstsIn_of_onCtx` — lemmas that do not exist in the tree yet.  Nothing to do with this
  stream (it references none of the 35 trimmed declarations).  Two further blockers seen
  earlier in the round (`Theory/Inductive/TeleCongr.lean:182`, an unknown
  `VIndRestore.minorCtorHargs_of_hargs'`; and `Theory/Inductive/FamInhabNTree.lean`) were
  fixed by their owning streams while this round ran.  The tree built at 1589 jobs, exit 0,
  at the start of the round.  Every module this stream touched elaborates clean.

## Reproduction

```bash
# the map
lake build 2>&1 | grep "automatically included section variable"

# the fixed-point trimmer used here (parses the linter's own `omit … in` suggestion,
# inserts it above the declaration's doc comment, re-elaborates, repeats)
python3 /tmp/wt/fixloop.py Lean4Lean/Theory/Typing/KEta.lean
```
The trimmer is throwaway; the two traps it had to handle are worth keeping:
1. the suggested clause contains **nested brackets** (`[V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]`), so a
   `\[[^\]]*\]` scan silently matches nothing and reports the file clean — that bug made
   `Cnst.lean` look already-fixed for one round;
2. the linter reports **fully-qualified** names, so resolving
   `…SetModel.IndSignature₂.WF.at` by last component alone also matches
   `IsStageSignature₂.at` seven lines earlier.  Match the declared name as a suffix of the
   reported name, not the other way round.

Also worth knowing: **`lake env lean <file>` rebuilds that file's imports** (verified by
olean mtime, 16:16:43 against a 16:16:01 source edit).  That is what makes the per-file loop
above cross-module-correct — cascades in a *dependent* file show up on the next `lake env
lean` of that file without a separate full build.
