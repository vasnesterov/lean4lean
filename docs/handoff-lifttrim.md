# handoff-lifttrim — the unused-section-variable warning population, and two trims applied

Date: 2026-09-03.  Stream: "lifttrim".  Tree: `master` + working-tree edits listed in §6.

## 0. Summary

* The warning class is real, was in every build, and **`include` does not suppress it** — the
  belief that it does was wrong, and this file records the counterexample.
* The population is **20** lines, of which **19** are in `Lean4Lean/` and **1** is in the
  `Foundation` dependency.  **None** is in a frozen file.
* Two were fixed (`Ctx.LiftN.exists_instN_typed`, `InductiveDeclExamples.ntreeAux_WF`), and the
  first cascaded into two more (different linter, `unusedVariables`) which were also fixed.
  In-repo count 19 → 17.
* The soundness-ledger claim about `Theory/SetModel/IndInterp.lean` is **confirmed, with the
  numbers corrected**: 9 lemmas there need **no AC**, and 7 of those need **no ZFC and no
  `Nonempty V`**.  A tenth, in `Cnst.lean`, needs not even `SetStructure V`.
* Census before and after: **13 holes, identical list**.  Guards 1/2/3 pass.  Full
  `lake build` green.

## 1. The instrument, and the false belief it was hidden behind

    lake build 2>&1 | grep "automatically included section variable"

**20 lines** on 2026-09-03, before this stream's edits:

| # | file:line | theorem | unused |
|---|---|---|---|
| 1 | `Theory/Typing/StrengthenAxiom.lean:162` | `Ctx.LiftN.exists_instN_typed` | `henv : Ordered env` |
| 2 | `Theory/Inductive/NestedHead.lean:925` | `InductiveDeclExamples.ntreeAux_WF` | `h : …addInduct' listDecl = some env₁` |
| 3–5 | `Theory/Typing/KDescend.lean:391,394,399` | `VEnv.refQ_not_noApp`, `refQ2_not_noApp`, `refParams_no_kstep` | `[Params]` |
| 6 | `Theory/Typing/KEta.lean:775` | `VEnv.kdom_ne_liftN` | `[Params]` |
| 7 | `Theory/Typing/KMeasure.lean:330` | `VEnv.measure_witness` | `[Params]` |
| 8–9 | `Theory/Typing/KSite7.lean:703,708` | `Pattern.Matches.const_shape`, `Pattern.Matches.const'` | `[Params]` |
| 10 | **`Foundation`**`/FirstOrder/SetTheory/Z.lean:35` | `LO.FirstOrder.SetTheory.subset_of_eq` | `[Nonempty V]`, `[V ⊧* 𝗭]` |
| 11 | `Theory/SetModel/Cnst.lean:255` | `SetModel.oracleExtend_append` | `[SetStructure V]`, `[Nonempty V]`, `[V ⊧* 𝗭𝗙]`, `[V ⊧* 𝗔𝗖]` |
| 12–20 | `Theory/SetModel/IndInterp.lean:133,143,153,300,836,846,900,990,1553` | see §4 | ZF/AC/Nonempty instances |

**Where the earlier instruction was wrong.**  Two sessions ago three streams were told the
linter is *suppressed by an explicit `include`*.  It is not.  `Lean4Lean/Std/VariableBang.lean`
expands

    variable! (henv : Ordered env) in thm  ↦  variable (henv : Ordered env) in include henv in thm

and row 1 above is exactly such a site: the warning fires **through** the `include`.  A second,
independent confirmation arrived mid-session: a concurrent stream landed
`Theory/Inductive/HTeleGen.lean` with a hand-written `include hL hN in`, and
`n_minorFldI_nil` was immediately reported by the same linter.  (That stream fixed it within
the session; it is not in the table because it was not in the baseline.)

**Two population facts worth keeping.**

* `lake build`'s output includes the dependency.  Row 10 is `Foundation`, not this repo, and
  is out of reach (pinned commit, no pushes).  Quote **19**, not 20, for in-repo work.
* **No frozen file is in this population.**  `Verify/Soundness.lean`, `Verify/Axioms.lean` and
  `Verify/Guard.lean` produce zero warnings of this class — swept read-only, nothing to report,
  nothing to request.  In fact **no `Verify/` file at all** is in the population; all 19
  in-repo warnings are in `Theory/`.

## 2. Row 1 — `Ctx.LiftN.exists_instN_typed`, trimmed, 9 sites re-pointed

`Theory/Typing/StrengthenAxiom.lean`.  The `variable! (henv : Ordered env) in` was deleted.
The content is purely structural: `Ctx.LiftN`/`Ctx.InstN` are relations on `List VExpr`, the
induction only re-associates `OnCtx` conjuncts, and `VExpr.inst_liftN` is a substitution
identity.  Nothing consults `env`'s constants.

Signature, before → after:

    ∀ {env U}, env.Ordered → ∀ {k Γ Γ'}, Ctx.LiftN 1 k Γ Γ' → OnCtx Γ' (env.IsType U) → ∃ …
    ∀ {env U k Γ Γ'},      Ctx.LiftN 1 k Γ Γ' → OnCtx Γ' (env.IsType U) → ∃ …

**9 sites in 5 files**, each a one-argument deletion, no proof-term change:

| file:line | enclosing theorem | was |
|---|---|---|
| `Verify/Typing/ProjInhab.lean:142` | `constAppTypeStrengthen_of_allTypesInhabited_aux` | `henv` |
| `Verify/Typing/ProjInhab.lean:162` | `VEnv.AllTypesInhabited.strengtheningTarget` | `henv.ordered` |
| `Verify/Typing/ProjInhab.lean:174` | `VEnv.AllTypesInhabited.no_uninhabited_binder` | `henv` |
| `Verify/Typing/ProjWeakInvSplit.lean:188` | `constAppDefeqStrengthen_of_allTypesInhabited_aux` | `henv` |
| `Theory/Typing/StrengthenVerdict.lean:121` | `strengtheningTarget_of_univInhab` | `henv.ordered` |
| `Theory/Typing/StrengthenVerdict.lean:169` | `univInhab_no_uninhabited_entry` | `henv.ordered` |
| `Theory/Typing/ConstVar.lean:511` | `VEnv.AxiomConservativityUninhabWF.strengthening1Uninhab` | `henv` |
| `Theory/Typing/StrengthenAxiom.lean:218` | `VEnv.AxiomConservativityUninhab.strengthening1Uninhab` | `henv` |
| `Theory/Typing/StrengthenAxiom.lean:322` | `VEnv.strengtheningTarget_of_allClosedInhabited` | `henv.ordered` |

### 2.1 Instantiated where the removed hypothesis is refuted

`Theory/Typing/LiftTrimWitness.lean` (new, this stream).  `badEnv` declares one constant
`bad : #0`, a type with a loose de Bruijn index, so `Ordered.closedC` would give
`ClosedN (.bvar 0) 0`, i.e. `0 < 0`:

    not_ordered_badEnv          : ¬ badEnv.Ordered
    exists_instN_typed_badEnv   : ∃ Γ₀ A₀, … (the trimmed lemma applied at badEnv)
    exists_instN_typed_badEnv_sharp : the same with Γ₀ = [] and A₀ = Sort 0 named

So the untrimmed statement had **no instance at all** at `badEnv`, and the trimmed one does.
This is the strong form: not "the hypothesis was inert", but "the hypothesis is false here".

### 2.2 The cascade (observed, then fixed)

Rebuilding after the trim raised the `unusedVariables` count from **66 to 68**:

* `Theory/Typing/StrengthenVerdict.lean:165` — `henv : VEnv.WF env` in
  `univInhab_no_uninhabited_entry` became unused.
* `Verify/Typing/ProjInhab.lean:170` — `henv : env.Ordered` in
  `VEnv.AllTypesInhabited.no_uninhabited_binder` became unused.

Both theorems have **zero** term-level consumers (grep finds only prose), so both binders were
deleted.  Count back to 66.  Cascades are the norm; this one took one rebuild to surface.

### 2.3 What it bought in the axiom ledger

`#print axioms`, all names read off the declarations themselves, before → after:

| declaration | before | after |
|---|---|---|
| `Ctx.LiftN.exists_instN_typed` | `propext, Quot.sound` | **`propext`** |
| `VEnv.AllTypesInhabited.no_uninhabited_binder` | `propext, Quot.sound` | **`propext`** |
| `univInhab_no_uninhabited_entry` | `propext, Classical.choice, Quot.sound` | **`propext, Quot.sound`** |
| `constAppTypeStrengthen_of_allTypesInhabited_aux` | `propext, Quot.sound` | unchanged |
| `VEnv.AllTypesInhabited.strengtheningTarget` | `propext, Classical.choice, Quot.sound` | unchanged |
| `constAppDefeqStrengthen_of_allTypesInhabited_aux` | `propext, Quot.sound` | unchanged |
| `strengtheningTarget_of_univInhab` | `propext, Classical.choice, Quot.sound` | unchanged |
| `VEnv.AxiomConservativityUninhabWF.strengthening1Uninhab` | `propext, Quot.sound` | unchanged |
| `VEnv.AxiomConservativityUninhab.strengthening1Uninhab` | `propext, Quot.sound` | unchanged |
| `VEnv.strengtheningTarget_of_allClosedInhabited` | `propext, Classical.choice, Quot.sound` | unchanged |
| `InductiveDeclExamples.ntreeAux_WF` | `propext, Quot.sound` | unchanged |

Three lines got **strictly smaller** and none grew.  `Quot.sound` was entering
`exists_instN_typed` through `VEnv.Ordered` in its *type*; `Classical.choice` was entering
`univInhab_no_uninhabited_entry` through the `VEnv.WF.ordered` projection at the call.  So
`univInhab_no_uninhabited_entry` is now **choice-free**.

## 3. Row 2 — `ntreeAux_WF`, split rather than re-pointed (ownership, not difficulty)

`Theory/Inductive/NestedHead.lean`.  The strengthening is real:

    ntreeAux_WF'  : ∀ {env₁ : VEnv}, ntreeAux.WF env₁          -- new, no hypothesis
    ntreeAux_WF   : ∀ {env₁}, VEnv.empty.addInduct' listDecl = some env₁ → ntreeAux.WF env₁

`ntreeAux_WF` is now a one-line wrapper `:= ntreeAux_WF'` with an **explicit** `_h` binder (so
the section-variable linter has nothing to report and the `unusedVariables` linter is silenced
by the `_` prefix).  The proof body moved to `ntreeAux_WF'` unchanged.

Why a wrapper and not the flat trim the ripple note asked for.  The application sites are
**27, in 9 files** — not 25 in 8:

| file | sites |
|---|---|
| `Theory/Typing/ConstSubstNested.lean` | 9 |
| **`Theory/Inductive/CtorBeta.lean`** | 6 |
| **`Theory/Inductive/TeleCongr.lean`** | 3 |
| `Theory/Inductive/OwnRule.lean` | 2 |
| `Theory/Inductive/NestedTele.lean` | 2 |
| **`Theory/Inductive/RecTyped.lean`** | 2 |
| `Verify/Inductive/ArgsTypedSupply.lean` | 1 |
| `Theory/Inductive/NestedHead.lean` | 1 |
| `Theory/Inductive/NestedBuild.lean` | 1 |

(plus `NestedBuild.lean:2144`'s `example := @ntreeAux_WF`, which the wrapper keeps valid.)  The
three bolded files are owned by a concurrent stream and this stream was told not to edit them,
`CtorBeta.lean` and `RecTyped.lean` by name.  **11 of the 27 sites are in them**, and there is
no way to flatten the signature without breaking those 11: `ntreeAux.WF env₁` is a structure,
so `ntreeAux_WF h` cannot survive `h`'s removal.  The wrapper delivers the strengthening now at
zero consumer churn.

**Follow-up for whoever owns those files**: re-point all 27 sites `ntreeAux_WF h → ntreeAux_WF'`
and delete the wrapper.  Purely mechanical, no proof changes.

### 3.1 Instantiated where the removed hypothesis is refuted

Also in `LiftTrimWitness.lean`:

    not_addInduct_badEnv : ¬ (VEnv.empty.addInduct' listDecl = some badEnv)
                           -- via listEnv_ordered h : env₁.Ordered, contradicting §2.1
    ntreeAux_WF_badEnv   : ntreeAux.WF badEnv
    not_wf_noTypesDecl   : ¬ noTypesDecl.WF badEnv   -- non-vacuity of the conclusion

The third is the check that `VInductDecl'.WF badEnv` is not a degenerate predicate: a block with
`types = []` fails `types_ne` at `badEnv` too, so `ntreeAux_WF_badEnv` is not "everything is WF
at a junk environment".

`ntreeAux_WF'` : `propext, Quot.sound` — same as `ntreeAux_WF`, and no `sorryAx`.

## 4. The soundness-ledger fact: what the set model does *not* need

This is the item worth more than the fixes, and it **checks out** — with the numbers
different from the ones relayed.

Method (read-only; `IndInterp.lean` and `Cnst.lean` were **not** edited): the file was copied
to `/tmp`, the linter's own suggested `omit … in` inserted above each reported theorem, and the
copy elaborated with `lake env lean`.  Zero errors, zero remaining warnings of the class.  So
each omission is accepted by the compiler, not merely by a reading of the proof.

`Theory/SetModel/IndInterp.lean`, section variables
`{V} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]`:

| line | theorem | `𝗔𝗖` | `𝗭𝗙` | `Nonempty V` |
|---|---|---|---|---|
| 133 | `ite_eq_definable₁` | unused | unused | unused |
| 143 | `ite_eq_definable₂` | unused | unused | unused |
| 153 | `ite_eq_definable₃` | unused | unused | unused |
| 300 | `ite_rel_definable₂` | unused | unused | unused |
| 836 | `IndSignature.at_toTwo` | unused | unused | unused |
| 846 | `indStep₂_eq` | unused | *used* | *used* |
| 900 | `indStep_at_mono` | unused | *used* | *used* |
| 990 | `IndSignature₂.WF.at` | unused | unused | unused |
| 1553 | `ite_eq_snd_definable₂` | unused | unused | unused |

and `Theory/SetModel/Cnst.lean:255` `oracleExtend_append` needs **none** of the four — not even
`SetStructure V`; it is a statement about list append that happens to sit in the section.

**Stated plainly, since it is a fact about what the model requires and not lint:**

* **All 9** of those `IndInterp` lemmas — the definability case-splits, the two-operator
  transfer, the `indStep` monotonicity and equation, and `IndSignature₂.WF.at` — hold **without
  the axiom of choice**.
* **7 of the 9**, plus `oracleExtend_append`, hold **without ZF** and without `V` being
  non-empty: they are consequences of the *definability* apparatus alone, which is
  first-order syntax, not set theory.
* The two that do use ZF (`indStep₂_eq`, `indStep_at_mono`) still do not use AC.

**Correcting the relayed numbers.**  The note said "18 unused *instance* binders … of which 9
in `SetModel/IndInterp.lean` mean those lemmas need no ZFC, and two need no AC."  Measured:

* Unused instance binders in-repo: **34**, over **17** theorems in **6** files —
  7 × `[Params]` (KDescend 3, KEta 1, KMeasure 1, KSite7 2) + 4 (Cnst) + 23 (IndInterp).
  Not 18.
* The ZFC/AC reading is inverted.  **9** IndInterp lemmas need no **AC**; **7** of them need no
  **ZFC**; the "two" are the two that need ZF but not AC.

## 5. The 17 remaining in-repo warnings, with the ripple measured

All 17 are **instance** binders, and instance arguments are synthesized, not written.  Grep
finds **no `@`-application** of any of the 17 theorems anywhere in the tree.  So the ripple of
every remaining fix is:

> **one `omit … in` line, zero consumer edits.**

Reference counts (for prioritisation only — none of them is an edit):

| theorem | refs in tree | fix |
|---|---|---|
| `VEnv.refParams_no_kstep` | 13 | `omit [Params] in` |
| `SetModel.IndSignature₂.WF.at` | 6 | `omit [Nonempty V] [𝗭𝗙] [𝗔𝗖] in` |
| `VEnv.refQ_not_noApp` | 3 | `omit [Params] in` |
| `VEnv.refQ2_not_noApp` | 3 | `omit [Params] in` |
| `VEnv.kdom_ne_liftN` | 3 | `omit [Params] in` |
| `SetModel.oracleExtend_append` | 3 | `omit [SetStructure V] [Nonempty V] [𝗭𝗙] [𝗔𝗖] in` |
| `VEnv.measure_witness` | 2 | `omit [Params] in` |
| `Pattern.Matches.const_shape` | 2 | `omit [Params] in` |
| `Pattern.Matches.const'` | 2 | `omit [Params] in` |
| `SetModel.ite_eq_definable₁/₂/₃`, `ite_rel_definable₂`, `ite_eq_snd_definable₂`, `indStep_at_mono` | 2 each | as §4 |
| `SetModel.IndSignature.at_toTwo`, `indStep₂_eq` | 1 each | as §4 |

They were left alone only because this stream does not own `KDescend.lean`, `KEta.lean`,
`KMeasure.lean`, `KSite7.lean`, `Cnst.lean` or `IndInterp.lean`.  Every one is a single-line
edit with a compiled check already done for `Cnst.lean` and `IndInterp.lean` (§4).

Row 10 (`Foundation/FirstOrder/SetTheory/Z.lean:35`) is out of reach: the dependency is pinned
and this repo sends nothing upstream.  Note for the record that `subset_of_eq` there needs
neither `Nonempty V` nor `V ⊧* 𝗭` — the same shape of fact as §4, one level down.

## 6. Verification, and what did not move

* Full `lake build`: **green, 1587 jobs**, zero errors.
* Warning count, this class: **20 → 18** total, **19 → 17** in-repo.
* `unusedVariables` warnings: 66 → 68 (cascade) → **66** (cascade fixed).
* Hole census (`scripts/sorry-census-all.lean`, whole-filesystem population): **13 before, 13
  after, identical list** — `TrProj.weak'_inv`, `inferProj.WF`, `isDefEqUnitLike.WF`,
  `tryEtaStructCore.WF`, `IsDefEqU.forallE_inv_stratified`, `IsDefEqU.weakN_iff`,
  `NormalEq.descend`, `WF.rigidShapeUniqNS`, `VIndRecArg.exists_indep`, `addDecl.WF`,
  `kernel_complete`, `kernel_sound`, `leanTT_equiconsistent_zfc_omega_inaccessibles`.
* Guards: 1 ✓ (24 frozen axioms), 2 ✓ (whitelist; proof INCOMPLETE, `sorryAx` present — as
  before), 3 ✓ (2/2 gaps).
* Frozen files: not read-modified, not `touch`ed.  Not in this warning population at all.
* `AddInduct` was not flipped; `tryEtaStructCore.WF` and `isDefEqUnitLike.WF` untouched.

Files this stream changed:

    Lean4Lean/Theory/Typing/StrengthenAxiom.lean      trim + docstring
    Lean4Lean/Theory/Inductive/NestedHead.lean        ntreeAux_WF' + wrapper
    Lean4Lean/Verify/Typing/ProjInhab.lean            3 call sites + cascade binder
    Lean4Lean/Verify/Typing/ProjWeakInvSplit.lean     1 call site
    Lean4Lean/Theory/Typing/StrengthenVerdict.lean    2 call sites + cascade binder
    Lean4Lean/Theory/Typing/ConstVar.lean             1 call site
    Lean4Lean/Theory/Typing/LiftTrimWitness.lean      NEW — the witnesses
    docs/handoff-lifttrim.md                          NEW — this file

Untracked files from *other* streams present during the run (not this stream's):
`Theory/Inductive/HTeleGen.lean`, `HTeleNTree.lean`, `TeleMove2.lean`,
`Verify/Typing/NoConfGuard.lean` (the last was reported NOT BUILT by the census — it appeared
after the build; its owner should confirm it compiles, since a hole in an unbuilt module is
invisible to every instrument here).  Modified by other streams: `CtorBeta.lean`,
`RecTyped.lean`, `TeleCongr.lean`.

## 7. Where the brief was wrong

1. **"the linter is suppressed by an explicit `include`"** — false, and it was the reason the
   class looked invisible.  §1 has two independent counterexamples in this tree.
2. **"they are in the warning population — sweep read-only and report"** about the frozen
   files — they are not.  Zero warnings of this class in `Verify/Soundness.lean`,
   `Verify/Axioms.lean`, `Verify/Guard.lean`, or anywhere else under `Verify/`.
3. **"25 sites in 8 files"** for the `ntreeAux_WF` ripple — 27 sites in 9 files (§3), and 11 of
   them are in files this stream was forbidden to touch, which is why the fix is a wrapper.
4. **"18 unused instance binders"** — 34, over 17 theorems in 6 files (§4).
5. **"9 in `IndInterp.lean` mean those lemmas need no ZFC, and two need no AC"** — inverted.
   9 need no AC; 7 of those need no ZFC; the two are the ones needing ZF but not AC (§4).
6. **"20 lines"** is right, but one of them is `Foundation`'s.  In-repo is 19.

Nothing here was sent anywhere.  No `git` state was changed.
