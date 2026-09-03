# Handoff: obligation (B)'s data families, INHABITED at a parameterised nested block

**Written 2026-09-03.**  My files (all new, all mine):

| file | lines | contents |
|---|---|---|
| `Lean4Lean/Theory/Inductive/FamInhabNTree.lean` | 570 | the four families at `ntreeAux`; obligation (B) through the general bundle closure, arity 0 |
| `Lean4Lean/Theory/Inductive/FamInhabC.lean` | 179 | obligation (C) and the **general** (C) closure `hdata_of_recHargs_and_heads`, both instantiated |
| `Lean4Lean/Theory/Inductive/FamInhabScan.lean` | 54 | the conclusion-shape query behind §6's ABSENCE claim |

`lake build` of the three: **85 jobs, exit 0**.  Full `lake build`: **1595 jobs, exit 0**.
Nothing else was edited.  **The flip was not made.**  `Verify/Soundness.lean`,
`Verify/Axioms.lean`, `Verify/Guard.lean`: not read for editing, not written, not `touch`ed
(`git status --short` on the three is empty).

## 0. Verdict, in one line

**Outcome 1.  All three families obligation (C) needs are inhabited jointly at `ntreeAux`
(`D.np = 1`), arity 0 — and so is the fourth, so obligation (B) goes through the bundle closure
too.**  The gap `docs/handoff-rectyped.md` §3b and `docs/handoff-htele.md` §4b both record is
closed at this block.  It cost **five β-steps and one `Lookup` each**; nothing deeper was needed.

What is *not* claimed: no general producer.  The witnesses are restoration-*dependent* (they use
`ntreeRestore.tyArgs`' own β-redex), which is exactly what `instAt_indep_of_tyArgs` says a general
argument cannot be — see §5.1, which is the correction worth reading.

## 1. Result

| | before | after |
|---|---|---|
| `MotiveHargs` inhabited anywhere | **never** | at `ntreeAux`, `t = 1` |
| `MinorCtorHargs` inhabited anywhere | **never** | at `ntreeAux`, `q = 1` and `q = 2` |
| `MinorFldDefEq` inhabited | only `ntree_minorFld_nil` (field-less, disclosed degenerate) | at **all three** `q`, including the two that move |
| `RecBodyHargs` inhabited anywhere | **never** | at `ntreeAux`, `j = 1` |
| `VEnv.recConstsR_wf_of_recHargsD` premise set | reduction, satisfiability unknown at `np > 0` | **jointly satisfiable**, arity 0 |
| `VIndRestore.hdata_of_recHargs_and_heads` premise set | same | **jointly satisfiable**, arity 0 (`fi_hdata_general_inhabited`) |
| obligation (B) at `ntreeAux` via the general closure | no | **yes** (`fi_obligationB_inhabited`, arity 0) |
| obligation (C) at `ntreeAux` via (B)'s data families | reduction (arity 3) | **yes** (`fi_obligationC_inhabited`, arity 0) |

Neither obligation is *newly* true at this block — `ConstSubstNested.lean` §E's
`ntreeAux_recConstsR_wf` had (B) by a hand-built `mkPi` bridge and `HTeleNTree.lean` §3's
`ntree_iotaRulesRS_wf_all_gen` had (C) through `IotaHargsGen` §4.  What is new is that the two
**general, bundle-shaped closures** are certified non-vacuous above `np = 0`.  Before this round
every declaration mentioning any of the four families either *took* it as a hypothesis (arity 16–31)
or was the one degenerate `MinorFldDefEq` — §6.

## 2. What each family actually cost, at this block

The whole content is that `ntreeRestore` presents the companion as `List (NTree α)` while the block
stores it as a *substituted* `(λ α, List (NTree α)) #k`, so every slot whose subject crosses that
boundary is **one β step** (`ConstSubstNested.lean` §E's `rbetaL`) and every other slot is free.

| family | slot | cost at `ntreeAux` |
|---|---|---|
| `MotiveHargs` `t = 1` | `hbody` | `List{u} (NTree{u} #0) : Sort (u+1)` — two `constDF`s and a `Lookup` |
| | `hpi`, `hAs`, `hsort` | **free, and degenerate**: the companion is unindexed, so `As = []` (§4c) |
| `MinorFldDefEq` `q = 0` | | `TeleDefEq.rfl` then one `rbetaL` at `k = 3` |
| `MinorFldDefEq` `q = 1` | | `TeleDefEq.nil` — **degenerate**, `nlistNil` has no fields |
| `MinorFldDefEq` `q = 2` | | `TeleDefEq.rfl` then one `rbetaL` at `k = 5` |
| `MinorCtorHargs` `q = 1` | `hcbody` | `List.nil{u} (NTree{u} #0)`, one `appDF` pair |
| | `hpi` | **`rfl`** |
| | `hfun` | one `rbetaL` at `k = 3` under a `forallEDF`, then `defeqDF` on a `Lookup` |
| `MinorCtorHargs` `q = 2` | `hcbody` | `List.cons{u} (NTree{u} #0)`, one `appDF` pair |
| | `hpi` | **`rfl`** |
| | `hfun` | one `rbetaL` at `k = 8`, same shape, index `6` in a nine-entry context |
| `RecBodyHargs` `j = 1` | head defeq | one `rbetaL` at `k = 5` |
| | `hconcl` | **free** — `appDF` of the motive `Lookup` on `.bvar 0` |

`fi_hAs_cons` is kept as a standalone lemma although the current `MinorCtorHargs` no longer carries
a `HasArgs` conjunct: it is what `VIndRestore.minorCtor_hAs` produces in general, and it is where
the second β lives (two `HasArgs.cons` steps, the second a conversion).

## 3. Hole-freeness (measured) — and it is NOT evidence of content

Names read off each file's own `namespace` lines and its own `#print axioms` block, never composed
from the path.  Everything is under `Lean4Lean.InductiveDeclExamples`.

| declaration | arity | axioms |
|---|---|---|
| `fi_motiveHargs` | 3 | `[propext, Quot.sound]` |
| `fi_minorFld_node` / `fi_minorFld_cons` | 3 | `[propext, Quot.sound]` |
| `fi_hcbody_nil` / `fi_hcbody_cons` | — | `[propext]` |
| `fi_hfun_nil` / `fi_hfun_cons` / `fi_hAs_cons` | — | `[propext]` |
| `fi_minorCtorHargs_nil` / `fi_minorCtorHargs_cons` | 4 | `[propext, Quot.sound]` |
| `fi_recBodyHargs` | 3 | `[propext, Quot.sound]` |
| `fi_hmotD` / `fi_hfldD` / `fi_hbodyD` | 7 | `[propext, Quot.sound]` |
| `fi_hminD` | 12 | `[propext, Quot.sound]` |
| `fi_ntreeAux_obligationB` | — | `[propext, Classical.choice, Quot.sound]` |
| `fi_recHargs_bundles_inhabited` | **0** | `[propext, Quot.sound]` |
| `fi_recHargs_bundles_inhabited₃` | **0** | `[propext, Quot.sound]` |
| `fi_obligationB_inhabited` | **0** | `[propext, Classical.choice, Quot.sound]` |
| `fi_ntreeAux_obligationC` | — | `[propext, Classical.choice, Quot.sound]` |
| `fi_obligationC_inhabited` | **0** | `[propext, Classical.choice, Quot.sound]` |
| `fi_hheadD` | — | `[propext, Quot.sound]` |
| `fi_hdata_general_instantiated` | — | `[propext, Classical.choice, Quot.sound]` |
| `fi_hdata_general_inhabited` | **0** | `[propext, Classical.choice, Quot.sound]` |

`Classical.choice` enters only through `VInductDecl'.ctorApp'_hasType`, pre-existing and not
introduced here (`docs/handoff-htele.md` §7 records the same).

## 4. Inhabitation and degeneracy, stated apart from §3

### 4a The joint checks

* `fi_recHargs_bundles_inhabited` is **arity 0**: one block, one `D`, one `R`, one `σ`, one
  environment `F₂`, and **all four** families at **every index the closure demands them at**,
  simultaneously.  Not per-hypothesis, and not relative to the staging equations —
  `ntree_stage₂_exists` supplies those.
* `fi_recHargs_bundles_inhabited₃` is the same three at `F₃`.  **The two environments are
  different and the distinction is load-bearing**: `F₂` carries the type and constructor constants,
  `F₃` also the restored recursors, and (B) is stated over the first while (C) is stated over the
  second.  `docs/handoff-htele.md` §5.6 records a draft that died by conflating them; the shape that
  survives is the one where the *freshness* inputs stay at the pre-block `env₁`
  (`ntree_csubst_fresh h`) and the *substitution* inputs at the staging pair
  (`ntree_csubst_WFD₂` / `_WFD₃`).  §3 of `FamInhabNTree.lean` keeps all three apart by taking the
  staging equations and letting the closure route them.
* `fi_obligationB_inhabited` and `fi_obligationC_inhabited` are arity 0 with the *conclusions*
  of (B) and (C) — so the families and the twelve non-bundle premises hold **together**, which is
  the check `RecTyped.lean` §6b could only make relative to the bundles.
* Every `include` list is minimal: Lean's `unusedSectionVars` linter is active in these files —
  **verified by deliberately adding `hcons` to `fi_motiveHargs`' include list and watching it warn**,
  then reverting — and it is silent on all of them.  So each constant lookup named in each witness
  is load-bearing.

### 4b The degeneracies, disclosed

Two of the three families are inhabited here with slots that this block cannot exercise.

1. **`MotiveHargs`' `hpi`, `hAs`, `hsort` are the `T.indices = []` identities.**  The companion is
   unindexed (`fi_companion_unindexed`), so the spine `bvars 0 T.indices.length` is `[]`
   (`fi_motive_window_empty`), which forces `As = []` and makes `hAs = HasArgs.nil`.  Only `hbody`
   carries content.  **A block with a genuinely indexed companion would ask for more, and no
   witness in the tree has one** — all three nested witness blocks are unindexed.  So
   `MotiveHargs` should be graded *inhabited, one slot of four exercised*.
2. **`MinorCtorHargs` at `q = 1` is the field-less entry** (`fi_nil_fields_empty`): `hpi`'s `mkPi`
   has no binders.  `q = 2` is the load-bearing one — two fields (`fi_cons_fields_two`), **both
   recursive** so the ih block is two entries (`fi_cons_ihTypes_two`) and `hfun`'s de Bruijn index
   is `6` rather than `2`, arithmetic a field-less witness never exercises.
3. **`MinorFldDefEq` at `q = 1` is `TeleDefEq.nil`** (`fi_fld1_trivial`), as
   `RecTyped.lean`'s `ntree_minorFld_nil` already disclosed.  `q = 0` and `q = 2` both move
   (`fi_fld0_moves`, `fi_fld2_moves`).

### 4c What is measured to move, so none of this is an identity in disguise

`fi_np_pos` (`D.np = 1`, so this is not the `np = 0` case); `fi_companion_in_K` and
`fi_own_head_off_K` (**both** branches of the closure's `T.name ∈ K` split are reached at this one
block, so §6a of `RecTyped.lean`'s `hK`-for-all vacuity is genuinely avoided rather than dodged);
`fi_motBody_ne_stored`; `fi_fld0_moves`; `fi_fld2_moves`; `fi_hAs_second_needs_beta`;
`fi_hfun_cons_type_moves`; `fi_hfun_nil_type_moves`; `fi_recBody_head_moves`.  All `decide`.

## 5. Where the brief and the standing documents are wrong

This is the part worth reading.  Every item I checked myself.

### 5.1 `instAt_indep_of_tyArgs` was being read as an obstruction.  It is not one.

`docs/handoff-rectyped.md` §3b: *"They are `hargs`, and `VIndRestore.instAt_indep_of_tyArgs`
(`NestedRules.lean:1509`) says no restoration-independent argument produces it."*
`docs/handoff-htele.md` §4b repeats it, and the brief I was given repeats it again as the reason to
expect the families uninhabited at `np > 0`.

Read at the source, that lemma's docstring says something narrower: *"`hargs` is not a lemma waiting
to be proved from `Faithful`: no restoration-independent argument can produce it, and it has to be
supplied as data."*  It is a statement about **general producers from `Faithful`**, and it is
consistent with the families being cheap at any *concrete* block — which is what §2's table shows.
The two handoffs quote it in support of "inhabited nowhere", which does not follow, and it is why
nobody tried.  **The gap was a missing witness, not an obstruction.**

### 5.2 `MinorCtorHargs` at the arg-less constructor is **not** free

The brief says the non-degenerate entry to test at is *"the constructor with two recursive fields …
not the arg-less one, where the obligation is free and the target is trivial."*  Half right.  At
`nlistNil` (`nf = 0`) the *field window* is empty and `hpi` is `rfl`, but **`hfun` still costs a β
step** (`fi_hfun_nil`, `fi_hfun_nil_type_moves`): `hfun` looks the minor's motive up at the
**stored** companion application `(λ α, List (NTree α)) #3` and `MinorCtorHargs` demands it at the
**restored** `List (NTree #3)`.  That slot is indexed by the *motive*, not by the fields, so no
amount of field-emptiness makes it free.  The brief's distinction is still the right one to test at
— `q = 2` exercises strictly more — but "the obligation is free" at `q = 1` is false.

### 5.3 `hpi` is data in general and **`rfl`** at the witness

The brief: *"its `hAs` conjunct is removable because its subjects are functions of the block data
alone; `hpi` is not."*  That drop landed mid-session (§5.6) and the bundle is now three conjuncts,
so the count is right.  But at this block `hpi` is discharged by `rfl` at both companion
constructors, and the reason is structural rather than lucky: `hpi`'s right-hand side is
`mkPi (instAllTele (atRecTele (C.fieldTypesR D R)) …) (instAll (tyAppR' …) …)`, and the *type* of
the restored constructor head is that `mkPi` on the nose whenever the restored head is a
pre-existing constant with its declared telescope.  So "`hpi` is data" is a claim about the general
case only; nothing at a witness pays for it.

### 5.4 `handoff-rectyped.md` §7 item 3's guess about `RecBodyHargs` is correct

*"`RecBodyHargs`' `hconcl` looks free and I did not check it… Guess, unmeasured."*  Measured: it is
free (`appDF` of the motive `Lookup` on `.bvar 0`, the same step `rB1` takes), so `RecBodyHargs`
collapses to its head defeq alone — one `rbetaL`.  That is why obligation (B) came out of this round
as well, although the brief only asked for (C)'s three.

### 5.5 `handoff-rectyped.md` §3d's `[]`-collapse check passes, but misses the collapse that matters

§3d certifies that *"no hypothesis of §3–§5 carries a `bvars` spine at a **context** that can be
empty"*, and for `MotiveHargs.hAs` it notes the context has length `ni + t + np`.  True.  But the
slot that is degenerate at every witness is the **spine**, not the context: `bvars 0 ni` with
`ni = 0` is `[]`, so `hAs` is `HasArgs.nil` and `hpi`/`hsort` are identities.  §3d's instrument
cannot see this because it checks the wrong end of the judgement.  §4b above records it.

### 5.6 Two of my imports changed under me mid-session, and one of them changed the bundle

* `RecTyped.lean` (the `hAs`-drop stream's) landed the drop **during** this session:
  `VIndRestore.MinorCtorHargs` went from `∃ As B B', hcbody ∧ hpi ∧ hAs ∧ hfun` to
  `∃ B, hcbody ∧ hpi ∧ hfun`, with `hpi` now fixing `As`/`B'` outright.  My first `nlistCons`
  witness was written against the four-conjunct form and had to be rebuilt.  This is why
  `FamInhabNTree.lean` §1c states the *pieces* (`fi_hcbody_*`, `fi_hfun_*`, `fi_hAs_cons`) as
  standalone lemmas and bundles them in a separate two-line step: a third repackaging costs the
  assembly line and nothing else.
* `HTeleRecB.lean` (the `htele` stream's) was **broken for a stretch** — `:106`
  `Dependent elimination failed`, and `iotaMin_of_recHargs` / `hdata_of_recHargs_and_heads` /
  `ntree_obligationC_of_recHargs` carried `sorryAx` while it was — because it destructured the
  four-conjunct bundle.  It compiles again (`iotaMin_of_recHargs` grew `hσfD`/`hclFD`).  I did not
  touch it.  **Blast-radius decision, recorded in both files**: `FamInhabNTree.lean` imports only
  `RecTyped` and `HTeleGen`, so the whole of §1–§4 and obligation (B) survive a break in
  `HTeleRecB`; only `FamInhabC.lean` depends on it.

### 5.7 Corrections to my own brief's bookkeeping

* The brief's **arities** for the four families are all still right (`MotiveHargs` 6,
  `MinorFldDefEq` 6, `MinorCtorHargs` 7, `RecBodyHargs` 6) — the drop removed conjuncts and two
  existentials, not binders.  One **cone** number moved: `MinorCtorHargs` is **915**, not 695,
  because `hpi` now names `instAllTele`, `atRecTele … fieldTypesR` and `tyAppR'` in the definition
  itself.  Re-measured arities of my *witnesses* are in §3.
* The brief's *"Report your job count and the census (expect 13 holes)"*: 85 jobs for my three
  modules, 1595 for the full build, census **13**, `BUILT: 412`, `NOT BUILT: 0`.

## 6. ABSENCE claim, and how it was measured

**Claim: before `FamInhabNTree.lean` no declaration in the tree inhabited any of the four families
at any block, degenerate `MinorFldDefEq` aside.**

`scripts/exists.lean` on each of my names reports `FOUND … own value is a hole: false; cone reaches
sorryAx: false` — that is a presence check, not an absence one.  The absence claim rests on
`FamInhabScan.lean`, a conclusion-shape query over the **compiled environment** (population: 412
built modules; its own import list is stated in its header and named there rather than left
implicit, which is the failure `handoff-rectyped.md` §5 item 1 records).  Results:

* type mentions `MotiveHargs`: **9** — 4 mine, and 5 closures/reductions that *take* it
  (`recConstsR_wf_of_recHargsD` 26, `hdata_of_recHargs_and_heads` 31, `iotaMot_of_recHargs` 22,
  `ntreeAux_obligationB_of_bundles` 16, `ntree_obligationC_of_recHargs` 19).  **No prior
  inhabitation.**
* `MinorFldDefEq`: **13** — mine, the closures, `minorCtor_hAs` (11), the equation lemma, and
  `ntree_minorFld_nil` (arity 1), the one prior inhabitation, degenerate and disclosed as such.
* `MinorCtorHargs`: **11** — mine, the closures, and `minorCtorHargs_of_hargs` (13), a *producer*
  taking `hcbody`/`hfun`.  **No prior inhabitation.**
* `RecBodyHargs`: **5** — mine plus the two (B) closures.  **No prior inhabitation.**

So the premise of `docs/handoff-rectyped.md` §3b / `docs/handoff-htele.md` §4b was accurate when
written, and is now false.

## 7. Verification record

* `lake build` of `FamInhabNTree` + `FamInhabC` + `FamInhabScan`: **85 jobs, exit 0**.
* Full `lake build`: **1595 jobs, exit 0**, **0** errors.
* `grep -c "automatically included section variable"` over the full build log: **1**, and it is
  `Foundation/FirstOrder/SetTheory/Z.lean` — **none from my files** (baseline 18 is not exceeded;
  the count is low only because most modules replayed from cache).
* `lake env lean --run scripts/sorry-census-all.lean`: **HOLES 13**; `BUILT: 412`;
  `in population but NOT BUILT: 0`.  My three files add **no** holes.
* `scripts/dup-names.lean`: *"no duplicate Lean4Lean declarations across the joined cone"*.
* Layering: `grep -rln "^import Lean4Lean.Verify" Lean4Lean/Theory/` is **empty**.
* Frozen files: `git status --short` on `Verify/Soundness.lean`, `Verify/Axioms.lean`,
  `Verify/Guard.lean` is empty; none was written or `touch`ed.
* `HasArgs.of_mkApp` is **not** used, directly or transitively, and this is *measured* rather than
  asserted: `scripts/exists.lean` reports `HasArgs.of_mkApp`'s cone as **reaching `sorryAx`**, while
  every one of my results reports `cone reaches sorryAx: false`, so `of_mkApp` cannot be in any of
  them.  The only `HasArgs` I build is by `.cons`/`.nil`; `fi_hAs_cons` is two explicit `.cons`
  steps.  This corner stays `PiInv`-free.
* `tryEtaStructCore.WF` / `isDefEqUnitLike.WF` (ledger row 197): untouched.  The flip was not made.
* Files created: `Lean4Lean/Theory/Inductive/FamInhabNTree.lean`,
  `Lean4Lean/Theory/Inductive/FamInhabC.lean`, `Lean4Lean/Theory/Inductive/FamInhabScan.lean`,
  `docs/handoff-faminhab.md`.  **No other file edited.**  `RecTyped.lean`, `HTeleRecB.lean`,
  `HTeleGen.lean`, `HargsShared.lean` were read only (and two of them changed under me — §5.6).

### 7a Measured vs read off

**Measured by me this session:** every axiom line and arity in §3; every `decide` in §0 and §5 of
`FamInhabNTree.lean`; the joint arity-0 inhabitations; that the `unusedSectionVars` linter is live
in these files (by deliberately breaking it); the scan counts 9 / 13 / 11 / 5 in §6 and every arity
quoted there; the census, dup-names, layering and job counts; that `HTeleRecB.lean` was broken and
what broke it (the exact line and the four-versus-three destructuring); that `hpi` is `rfl` at both
companion constructors; that `RecBodyHargs`' `hconcl` is free.

**Read off source, not independently re-derived:** `instAt_indep_of_tyArgs`' docstring (§5.1 — I
quote it, I did not re-prove its claim); `ConstSubstNested.lean` §E's `rbetaL`/`rNC`/`rLC`/`rNilC`/
`rConsC` and the `ntreeF₂_*`/`ntreeF₃_*` constant lookups, which I *use* rather than re-verify;
`HTeleNTree.lean` §2a's two `IotaHeadHargs` witnesses, likewise used;
`(ntreeAux_WF h).iotaCtx`, used.

## 8. Pick up first

1. **A block with an INDEXED companion.**  It is the one thing this round cannot certify:
   `MotiveHargs`' `hpi`/`hAs`/`hsort` and the corresponding `IotaHargs` slots are the
   `T.indices = []` identities at all three nested witness blocks in the tree, so the spine
   machinery of that family has **never** been exercised (§4b item 1, §5.5).  `IndexedNested.lean`
   is where such a block would go.  Until then, grade `MotiveHargs` as *inhabited, one slot of four
   exercised.*
2. **A general producer is still absent, and §5.1 says why that is a separate question.**  What §2
   shows is that at a concrete block the families are β-steps against the restored head's declared
   telescope.  If a general producer exists it will be *restoration-dependent* — it has to read
   `R.tyArgs` — which is precisely the shape `instAt_indep_of_tyArgs` rules out for `Faithful`-only
   arguments and says nothing about otherwise.
3. **`MRedex.MPWit.mpAux`, the second parameterised block, is not covered.**  Its
   `mpAuxB_hdata` (arity 9) is (C)'s bundle there and `docs/handoff-rectyped.md` §5 item 1 notes its
   nine hypotheses were never audited for joint satisfiability.  The four families at *that* block
   would be the second data point, and it is a redex block rather than a canonical one.
4. **Do not** re-derive the entry defeqs by hand: `RecTyped.lean` §3 and `HTeleRecB.lean` §1 do it,
   and §1c's piecewise structure is there so a further repackaging of `MinorCtorHargs` costs two
   lines rather than a proof.
