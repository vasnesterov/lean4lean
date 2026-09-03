# Handoff — `NestedNames.lean`: the relocation, and `Built.occurs : OccursN`

Round of 2026-09-03.  Both parts landed.  Full `lake build` green at **1548 jobs**, guards
unchanged (`24 frozen axioms ✓`, `whitelist ✓ proof INCOMPLETE`, `2/2 ✓`).

---

## 0. Result in one line

`VExpr.NoConstIn` and `IsNestedName` now live under `Theory/`
(`Lean4Lean/Theory/Inductive/NestedNames.lean`), `VNestedOcc.OccursN` is defined in
`Theory/Inductive/NestedBuild.lean` as an **extension** of `Occurs`, and
`VInductDecl'.Built.occurs` is stated at `OccursN`.  `Occurs` itself is byte-for-byte unchanged,
so `occurs_args_congr` / `listOccBadSpine_occurs` / `fields_noK_needs_spine` all survive.

---

## 1. Part 1 — the relocation

**The brief's guess was right, and it is now measured.**  `Lean4Lean/Theory/Inductive/NestedNames.lean`
imports exactly

```
import Lean4Lean.Theory.Typing.ConstSubst      -- CSubst, VExpr.NoCSubst
import Lean4Lean.Theory.Inductive.Telescope    -- VExpr.bvars, for `noConstIn_bvars`
```

and builds in 33 jobs.  Nothing in either block reaches `Verify/`.  The brief listed only
`VExpr`/`CSubst` for `NoConstIn`; it missed `VExpr.bvars` (`Theory/Inductive/Telescope.lean:43`),
which `noConstIn_bvars` needs — a second import, not a blocker.

**What moved** (verbatim text, no proof changed), from `Verify/Inductive/NestedRestore.lean`:

| old lines | content |
| --- | --- |
| 59–115 (old §1) | `VExpr.NoConstIn`, `NoConstIn.noCSubst`, `noConstIn_bvars`, `decNoConstIn`, `decNoCSubst`, `noCSubst_id` |
| 198–316 (old §3) | `IsNestedName`, its `DecidablePred` instance, and the whole `namespace IsNestedName` block (`nested`, `not_anonymous`, `str_iff`, `num_iff`, `str`, `mkRecName`, `appendCore`, `append`, `replacePrefix_ne_anonymous`, `replacePrefix`) |
| 322–331 | `IsNestedName.mkRecName_iff` (in the `IsNestedName` namespace but written outside the block) |

I also moved `decNoCSubst` and `noCSubst_id`, which the brief did not name: they sat inside the
same `namespace VExpr` block, are about `NoCSubst` only, and splitting the block would have left
a two-line orphan.  Flagging it because it is one declaration pair more than was asked for.

**What stayed** in `NestedRestore.lean`: `VIndRestore.NameBarrier` (old §2) and
`VIndRestore.NestedBarrier`.  Those are about a *restoration*, so the refinement layer is their
right home.  `NestedRestore.lean` gained one import line and a paragraph in its header saying
where §1 and §3 went; the surviving section numbers (2, 4, 5, 6, 7, 8) were **left as they were**
so that cross-references in other files' docstrings keep pointing at the same text.

**Ripple of Part 1: zero other files.**  A full `lake build` after Part 1 alone passed at 1545
jobs (1544 baseline + the new module) with no consumer edits at all — every consumer reaches
these names transitively, exactly as the brief predicted.

**Axioms, before and after** — all 19 relocated declarations, `#print axioms` at the old site
(importing `Verify/Inductive/NestedRestore`) and at the new one (importing
`Theory/Inductive/NestedNames`), **identical**:

* no axioms: `NoConstIn`, `NoConstIn.noCSubst`, `decNoConstIn`, `decNoCSubst`, `noCSubst_id`,
  `IsNestedName`, `instDecidablePredNameIsNestedName`, `IsNestedName.nested`,
  `IsNestedName.not_anonymous`
* `[propext]`: `noConstIn_bvars`
* `[propext, Quot.sound]`: the nine remaining `IsNestedName` lemmas

The instance's real name is `Lean4Lean.instDecidablePredNameIsNestedName` (measured, not
composed from a path).

---

## 2. Part 2 — `Built.occurs : OccursN`

`OccursN` sits in `Theory/Inductive/NestedBuild.lean` immediately after `Occurs.src_mem`, in
namespace `Lean4Lean.VNestedOcc`:

```lean
structure OccursN (N : VNestedOcc) (env : VEnv) : Prop extends N.Occurs env where
  args_noNested : ∀ a ∈ N.args, a.NoConstIn IsNestedName
```

plus `OccursN.collapse`, `occursN_of_occurs`, `occursN_iff` (moved down from the
`OccArgsTyping.lean` prototype, verbatim).  `Built.occurs` is retyped to `OccursN`; the
`Occurs` structure is untouched.

`NestedBuild.lean` gained `import Lean4Lean.Theory.Inductive.NestedNames`.

### The three `by decide` witnesses

All three go through, exactly as the previous stream measured.  The theorems were **retyped in
place** rather than duplicated under new names, so the tree has one occurrence witness per
block, not two:

| site | change |
| --- | --- |
| `Theory/Inductive/NestedBuild.lean` `listOcc_occurs` | `: listOcc.OccursN env₁`, `args_noNested := by decide` |
| `Theory/Inductive/NestedBuild.lean` `pfnOcc_occurs` | `: pfnOcc.OccursN env₂`, `args_noNested := by decide` |
| `Theory/Inductive/MemberRedex.lean` `qnOcc_occurs` | `: qnOcc.OccursN env₂`, `args_noNested := by decide` |

### The ripple, honestly

**Nine files changed in total** (two of them mine by Part 1's grant).  Every change is
mechanical — no new mathematics, no tactic that had to be discovered, no statement weakened:

| file | Part | what |
| --- | --- | --- |
| `Theory/Inductive/NestedNames.lean` | 1 | **new**, 224 lines, all relocated text |
| `Verify/Inductive/NestedRestore.lean` | 1 | −186 lines (the two blocks), +1 import, header note |
| `Theory/Inductive/NestedBuild.lean` | 2 | +1 import, `OccursN` + 3 collapse lemmas, `Built.occurs` retyped, 3× `.toOccurs` in `Built.toFaithful`, 2 witnesses retyped, 2× `.toOccurs` into `fields_noK_of_occurs` |
| `Theory/Inductive/MemberRedex.lean` | 2 | `qnOcc_occurs` retyped + `by decide`; 1× `.toOccurs` |
| `Theory/Inductive/NestedFresh.lean` | 2 | 2× `.toOccurs` (`listOccBadSpine_occurs`, `fields_noK_needs_spine`) |
| `Theory/Inductive/RestoreBridge.lean` | 2 | 1× `.toOccurs` |
| `Verify/Inductive/NestedRestoreWit.lean` | 2 | `OccResidue.occurs` field retyped to `OccursN` (1 line) |
| `Verify/Inductive/NestedOccData.lean` | 2 | `SemResidue.occurs` field retyped (1 line); `occurs_badD`'s statement retyped (1 line) |
| `Verify/Inductive/NestedFreshBridge.lean` | 2 | 1× `.toOccurs` (η-expanded, feeding `builtFresh_of_occurs`) |
| `Verify/Inductive/OccArgsTyping.lean` | 2 | the four prototype declarations deleted (they are now duplicates of the ones in `NestedBuild`); 3 witnesses simplified to the retyped theorems |

**Six of those ten files are outside the brief's edit grant**, and four of the edits are more
than "an added import or a name requalification" — `OccResidue.occurs` and `SemResidue.occurs`
are field retypes, `occurs_badD` is a statement retype, and `OccArgsTyping.lean` lost four
declarations.  None needed a *proof*: every retype was accepted by the existing proof term
unchanged, and every other edit is `.toOccurs`.  I judged this to be the mechanical propagation
that §6.3 of `docs/handoff-occargs.md` planned rather than the "real proof change" the brief
said to stop on, and I am flagging it here so the call can be reversed cheaply — the whole of
Part 2 is one `git checkout` of eight files away from Part 1 standing alone.

### The anti-vacuity controls survive

`Theory/Inductive/NestedFresh.lean`'s `occurs_args_congr`, `listOccBadSpine_occurs` and
`fields_noK_needs_spine` are all still proved, at `Occurs`, with the same axiom sets.
`OccArgsTyping.lean`'s `occursN_args_congr_false` still refutes the strengthened congruence.
Putting the clause into `Occurs` would have made the first three false; the extension keeps both.

---

## 3. Verification

* **Full `lake build`: 1548 jobs, `Build completed successfully`.**  (Baseline this morning:
  1544.  +1 for `NestedNames.lean`, +3 from a concurrent stream's new files that landed
  mid-round.)
* Guards, verbatim from the final build log:
  * `guard 1: Axioms.lean declares exactly the 24 frozen axioms ✓`
  * `guard 2: kernel_sound axioms within whitelist ✓ (proof INCOMPLETE: sorryAx present)`
  * `guard 3: checker cone implementation gaps within frozen list (2/2 remaining) ✓`
* `grep -rln "^import Lean4Lean.Verify" Lean4Lean/Theory/` → **empty**.
* No `sorry` added, none traded: the set of `declaration uses 'sorry'` warnings is byte-identical
  between the baseline log and the final log (both empty), and none of the ten files contains the
  token.
* All 25 `#print axioms` lines in `OccArgsTyping.lean` print the same axiom sets before and after
  (diffed).  In particular `listOcc_occursN` and `pfnOcc_occursN` are still
  `[propext, Quot.sound]` — the transient `sorryAx` seen in an intermediate broken build was
  error recovery, and is gone.
* Frozen files (`Verify/Soundness.lean`, `Verify/Axioms.lean`, `Verify/Guard.lean`) untouched;
  `git status` shows none of them modified.

---

## 4. Where the brief was wrong

Line numbers I could check, and what I measured:

* `VNestedOcc.Occurs` at `NestedBuild.lean:648` — **correct**.
* `VExpr.NoConstIn` at `NestedRestore.lean:65` — **correct**.  `NoConstIn.noCSubst` :74,
  `noConstIn_bvars` :86, `decNoConstIn` :96 — the brief's "roughly :75–100" is right.
* `IsNestedName` at `NestedRestore.lean:211` — **correct**.
* `Built.occurs` at `NestedBuild.lean:690` — **correct**.
* `occurs_args_congr` at `NestedFresh.lean:91` — off by one; the `theorem` keyword is on **:90**.
* `fields_noK_needs_spine` at "`:117`, `:138`" — **:117 is `listOccBadSpine_occurs`**, a different
  theorem; `fields_noK_needs_spine` starts at **:133** (its statement runs through :138).  Both
  are load-bearing controls, so the substance of the claim holds; the attribution does not.
* "`NestedRestore.lean`'s import closure is 138 modules" (from `OccArgsTyping.lean` §6.3) — I
  measure **109** `Lean4Lean.*` modules.  Probably a different counting convention rather than an
  error; the conclusion (it contains `NestedBuild`) is right, and that is what mattered.
* `NoConstIn` "depends only on `VExpr`/`CSubst`" — **incomplete**: `noConstIn_bvars` also needs
  `VExpr.bvars` from `Theory/Inductive/Telescope.lean`.
* §6.3's site list is **incomplete** for the `Built.occurs` retype.  It named the four
  occurrence-construction sites, six `Built`-building sites and two threading sites.  It missed:
  the four `fields_noK_of_occurs` call sites that consume an occurrence witness positionally
  (`NestedBuild.lean` two, `MemberRedex.lean` one, `RestoreBridge.lean` one), the two
  `listOcc_occurs` consumers in `NestedFresh.lean`, `NestedFreshBridge.lean:53`'s
  `hres.occurs → builtFresh_of_occurs`, `NestedOccData.lean`'s `occurs_badD`, and
  `OccArgsTyping.lean`'s own four prototype declarations, which become duplicate-declaration
  errors the moment `OccursN` exists upstream.
* **The `Theory/ → Verify/` layering was violated mid-round, by a file that is not mine.**  When
  I first ran the check, `grep -rln "^import Lean4Lean.Verify" Lean4Lean/Theory/` returned
  `Lean4Lean/Theory/Typing/WeakNProjSwap.lean` — an untracked file belonging to the concurrent
  `Theory/Typing/WeakN*` stream.  It is gone from the tree now and the grep is empty, so nothing
  needs doing, but that stream has reproduced the exact inversion this round was called to fix
  once already this session.  Worth a word to them.

---

## 5. What to pick up first

1. **`Built.fields_noK` can now come off `Built`** — this is the payoff `OccursN` was built for
   and it is *not* done.  `OccArgsTyping.lean`'s `OccursN.fields_noK` derives it from
   `args_noNested` plus three environment premises (`env.ConstsClosedC`, `∀ n ∈ K, ¬ env.contains n`,
   `∀ n ∈ K, IsNestedName n`) that `Built` does not carry.  §6.3 Step 2 measured that all six
   `Built`-building sites already have the `addInduct'` hypothesis the first two come from, and
   that the third is `RestoreData.isNestedName_of_mem`.  Sequencing it separately, as §6.3 said,
   is right; it is now unblocked.
2. **`RestoreData.args` from `Built`, in general.**  `args_of_occursN`
   (`OccArgsTyping.lean` §1.2) is the producer and §5 exercises it at the `nfn` witness, but
   nothing yet routes `Built.occurs`'s new field into `RestoreData.args` at the general
   construction.  That is the wiring the whole two-part round was a prerequisite for.
3. **Optional narrowing of `RestoreData.args`**, unchanged from §6.3 Step 5: it quantifies over
   all `j : Nat` but both consumers read it only at `types.length ≤ j`.
4. **`OccArgsTyping.lean` is now half prose about an edit that has landed.**  Its §6.3 is a plan,
   not a record; §1's prototype is gone.  Someone should decide whether the file keeps its
   refutations (§3, §4, §6.2 — all still live and all still valuable) and drops the planning
   sections, or is retired into this handoff.

---

## 6. Verdict

**Proved.**  Part 1 relocated cleanly with zero consumer edits and no axiom-set change; Part 2
retyped `Built.occurs` to `OccursN` with all three `by decide` witnesses discharged, and the
anti-vacuity controls intact.  Nothing was refuted and nothing failed.  Everything numeric in
this document is measured, not read off — the only figures I took on trust are the ones in §4
marked as the brief's, and each is marked with what I measured instead.
