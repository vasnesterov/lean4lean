# handoff-ctorslen — `Lean4Lean.TrIndDeclN.trCtorsLen`, the last open field

Round target: supply `trCtorsLen` generally; arity-0 witness at
`Lean4Lean.InductiveDeclExamples.ntreeAux` through the general route.

## 0. Priors (written BEFORE the first instrument call)

Stated as falsifiable guesses so the measurements can contradict them.

- P1 (0.75) `trCtorsLen` really is a bare `List.length` equation, not a `Forall₂`
  bookkeeping side condition. The brief says so; I expect to confirm by reading
  the structure. If it *were* derivable from a `Forall₂` living in `trCtors`,
  the field would be redundant and someone would have deleted it already — the
  fact that it survived 16 rounds is weak evidence it is genuinely independent.
- P2 (0.85) The `RestoreData` refutation
  (`Lean4Lean.ElimNestedInductive.Result.trCtorsLen_not_of_restoreData`) is real
  and I will not be able to route around it. Doubling a constructor list while
  preserving `RestoreData` is a cheap, robust counterexample shape.
- P3 (0.6) The supplier, if any, is the *same* absent
  `List InductiveType -> VInductDecl'` construction that other fields needed.
  A length equation between a surface `List Constructor` and an abstract
  `VIndType.ctors` can only be true by construction: nothing in the surface data
  constrains the abstract side unless the abstract side was *built* from it.
  So I expect (b) to land on "reduce to the construction", making this the
  fourth field tracing there.
- P4 (0.5) There nevertheless exists a cheap `<->` reduction: `trCtorsLen` should
  be equivalent to a `Forall₂`-existence or a `List.map`-shape premise on the
  abstract ctor list, i.e. `T.ctors = t.ctors.map f` for some `f`. If the abstract
  ctors are literally produced by a `map`/`pmap` over the surface ctors anywhere
  in the tree, `List.length_map` closes it and the round is short.
- P5 (0.4) There may already be a general producer I have not been told about:
  the brief's own census was off by one, and six already-done assignments were
  caught by `shape.lean` this session. I will run `shape.lean` before claiming
  absence. Base rate of "already done" this session is high enough to check first.
- P6 (0.3) `trIndDeclN_of_ownId` (arity 22, cone 1445) already discharges
  `trCtorsLen` internally on the way to `trCtors`; if so, its proof contains the
  general argument I need and I only have to expose it as a standalone lemma.
  This is the cheapest possible outcome. Direction risk: `trIndDeclN_ctorPointwise`
  is the inverse (consumes, does not supply) per the brief, and I will check the
  direction of anything before using it.
- P7 (0.7) `ntreeAux` is non-degenerate (`uvars > 0` or `params <> []`) and so is
  a real arity-0 target, unlike `nfnAux`. I expect the witness to need the
  construction's output to be `rfl`-free.
- P8 (0.55) Round-close will be clean (census 13 / NOT BUILT 0) because my file
  is new and small; the main risk is red builds in the four concurrently-owned
  files, which I must re-poll rather than investigate.

## 1. Measurements (appended one line per instrument call, as made)

- M1 (`sed` read of `Lean4Lean/Verify/Environment/InductR.lean:276-330`): **P1 CONFIRMED.**
  `TrIndDeclN.trCtorsLen` is
  `∀ (j : Nat) t T, types[j]? = some t → D.types[j]? = some T → t.ctors.length = T.ctors.length`
  — a bare length equation, no `Forall₂`, **unstaged** (no `addIndTypesC` premise), unlike
  `trCtors` which is staged over `env.addIndTypesC D K = some env₁` and compares names against
  `R.ctorName C.name`. Field count confirmed at **12**: safe, uvars, np, length, companions,
  trType, trCtorsLen, trCtors, trSpine, ctorName_own, recName_own, recName_aux. So the brief's
  "4 block data + 6 general + trCtors + trCtorsLen" adds up.
  Also noted: `TrIndDeclN.mem_indDeclNamesN` (same file) **consumes** `trCtorsLen` exactly once,
  to turn `q < T.ctors.length` into `q < t.ctors.length` before applying `trCtors`. That is the
  load-bearing use, and it is the *reverse* direction (abstract → surface).
- M2 (`exists.lean`, population 450 built modules):
  - `Lean4Lean.trIndDeclN_of_ownId` — FOUND, module `Lean4Lean.Verify.Inductive.TrIndDeclNProducer`,
    arity 22, cone 1445, hole false, sorryAx false. (Brief's figures exact — cones trustworthy.)
  - `Lean4Lean.trIndDeclN_ctorPointwise` — FOUND, module `Lean4Lean.Verify.Inductive.CtorPointwise`,
    arity 19, cone 713, hole false, sorryAx false. (Brief exact.)
  - `Lean4Lean.ElimNestedInductive.Result.trCtorsLen_not_of_restoreData` — **NOT FOUND.**
    The brief's name for the refutation does not exist. **Brief attribution #8 wrong** (cones
    still exact). Must locate the real refutation by shape before believing or disbelieving it.
  - `Lean4Lean.InductiveDeclExamples.ntreeAux` — FOUND, `Lean4Lean.Theory.Inductive.NestedHead`,
    arity 0, cone 43. `…nfnAux` — FOUND, `Lean4Lean.Theory.Inductive.NestedBuild`, arity 0, cone 40.
- M3 (`grep`/`sed` of `Lean4Lean/Verify/Inductive/CtorPointwise.lean` header + §3):
  the refutation exists under the name **`Lean4Lean.trCtorsLen_not_of_restoreData`**
  (namespace `Lean4Lean`, NOT `Lean4Lean.ElimNestedInductive.Result`). Its stated content matches
  the brief: `RestoreData`'s 14 fields mention `types` only via `types.length` and
  `(types.headD default).name`, never `types[j].ctors`, so `RestoreData.congr_types` gives an
  invariance under changing a member's constructor count and the refutation follows. **P2 holds.**
- M4 (`grep` of `Lean4Lean/Verify/Inductive/TrIndDeclNProducer.lean:69-101`):
  `trIndDeclN_of_ownId` **carries `trCtorsLen` as its hypothesis `hclen`**, verbatim the field
  statement, with an in-source comment "THE ONE FIELD WITH NO GENERAL PRODUCER". So **P6 REFUTED**:
  the arity-22 producer does not discharge it internally, it passes the buck. The brief's census
  is right that this is the one open field, and the producer is the consumer I must feed.
- M5 (`shape.lean`, HEADS=`Lean.InductiveType.ctors Lean4Lean.VIndType.ctors List.length`,
  population 450 modules): 42 constants conclude something mentioning all three heads; 7 are
  structure fields (incl. `Lean4Lean.TrIndDeclN.trCtorsLen` and `Lean4Lean.TrIndDecl.trCtorsLen`
  themselves). **No general producer**: every plain declaration is either a `.rec`/`.mk`/`.casesOn`,
  a consumer (`trIndDeclN_ctorPointwise`, `…_of_run`, `trIndDecl_ctor_name_eq`), a carrier
  (`trIndDeclN_of_ownId`, `trIndDeclN_of_restoreData`, both arity 22), the refutation
  (`Lean4Lean.trCtorsLen_not_of_restoreData`, arity 0), or an arity-0 concrete witness
  (`Lean4Lean.InductiveDeclExamples.ntreeAux_ctorPointwise`,
  `Lean4Lean.InductiveDeclExamples.ntreeAux_trCtors_witness`). **P5 REFUTED** — this is genuinely
  not already done; `shape.lean` did not catch a seventh already-done assignment.
- M6 (`grep` `Lean4Lean/Verify/Environment/Induct.lean:86`): `TrIndType env Us t T` is
  `t.name = T.name ∧ TrExprS env Us [] t.type T.type` — **it does not mention `ctors` at all.**
  So `trType` cannot constrain constructor counts, which is what makes the independence argument
  below available.
- M7 (`grep`/`sed`, `Verify/Inductive/TrExprSGeneral.lean:479-501`, `Verify/Inductive/ValAtParam.lean:189`):
  the surface side at the ntreeAux block is `([ntreeIndType] : List Lean.InductiveType)`, a
  ONE-member list with `ctors := [{name := ``NTree.node, …}]`; the abstract side `ntreeAux.types`
  has TWO members (`NTree` with `[ntreeNode]`, `_nested.List_1` with `[nlistNil, nlistCons]`),
  `numNested = 1`, `ntreeK = [`_nested.List_1]`. So `trCtorsLen` at this block bites at exactly
  `j = 0` (`1 = 1`) and is vacuous at `j = 1` (`types[1]? = none`) — the anti-vacuity conjunct the
  witness needs is "the j=0 pair is reached", same shape as `ntreeAux_trCtors_witness`.
- M8 (`grep` over `Lean4Lean/` for `def`s mentioning `InductiveType` and for anything returning
  `VInductDecl'`): **there is no `List InductiveType → VInductDecl'`, no `InductiveType → VIndType`,
  and no `Constructor → VIndCtor` anywhere in the tree.** Every `VInductDecl'` is either a literal
  `def … : VInductDecl' where` (~30 witness blocks), a record update of one, `resolveC`
  (`VInductDecl' → … → Option VInductDecl'`, abstract→abstract), or `VNestedOcc.member`
  (abstract→abstract, `Theory/Inductive/NestedBuild.lean` Part 8 — it *computes* `ntreeAux.types[1]`
  from `listDecl`, confirming the auxiliary members are built but saying nothing about the surface
  side). **P3 CONFIRMED**: the supplier of `trCtorsLen` can only be the absent surface→abstract
  construction. Note this is only vacuous-free for `j < types.length`: at companion indices
  `types[j]? = none`, so `trCtorsLen` bites *only* on the user's members, which is exactly where
  only a surface→abstract construction can see both sides.
- M9 (`lake build Lean4Lean.Verify.Inductive.CtorsLenGeneral`): **§1 and §2 GREEN** on the second
  attempt (one `rfl` missing after a `rw` in the `none` branch). Proved, all hole-free:
  `Lean4Lean.TrCtorsLen` / `Lean4Lean.CtorNameOwn` / `Lean4Lean.CtorNamesAgree` (the field texts,
  named), `Lean4Lean.trCtorsLen_of_ctorNamesAgree`, `Lean4Lean.ctorNamesAgree_of_trCtorsLen`,
  `Lean4Lean.ctorNamesAgree_iff_trCtorsLen`; `Lean4Lean.surfNameSkel`,
  `Lean4Lean.VInductDecl'.nameSkelV`, `Lean4Lean.SkelPrefix`, `Lean4Lean.skelPrefix_entry`,
  `Lean4Lean.ctorNamesAgree_of_skelPrefix`, `Lean4Lean.trCtorsLen_of_skelPrefix`,
  `Lean4Lean.ctorNameOwn_of_skelPrefix`, `Lean4Lean.name_eq_of_skelPrefix`,
  `Lean4Lean.skelPrefix_iff_trCtorsLen`.
  **P4 CONFIRMED, and better than the prior guessed**: not just a `map`-shaped sufficient premise
  but two *equivalences*, and the skeleton one supplies three fields from one `List` equation.
  Import closure is `Lean4Lean.Verify.Environment.InductR` only (142 modules).
- M10 (`lake build`, 4 attempts): **§3 and §4 GREEN.** The three failures were all one bug — the
  anonymous constructor does **not** flatten through `Exists` inside an `And` chain, so the
  `∃ t T, …` conjunct needs its own `⟨…⟩`. (Two of the four attempts were my own edit-script
  clobbering; recorded because it cost two measurements.) Proved:
  `Lean4Lean.TrIndDeclNSansLen` (the other 11 fields, verbatim), `Lean4Lean.TrIndDeclN.toSansLen`,
  `Lean4Lean.CtorsLenJunk.surf`, `Lean4Lean.CtorsLenJunk.D`, `Lean4Lean.CtorsLenJunk.sansLen`,
  `Lean4Lean.CtorsLenJunk.not_trCtorsLen`, `Lean4Lean.trCtorsLen_not_of_sansLen`,
  `Lean4Lean.InductiveDeclExamples.ntreeSurf`,
  `Lean4Lean.InductiveDeclExamples.ntreeSurf_skelPrefix`,
  `Lean4Lean.InductiveDeclExamples.ntreeSurfDbl`,
  `Lean4Lean.InductiveDeclExamples.ntreeSurfDbl_not_skelPrefix`,
  `Lean4Lean.InductiveDeclExamples.ntreeAux_trCtorsLen_witness`.
- M11 (`exists.lean`, population 452 built modules; then 453 with a custom `WATCH`):
  all hole-free, all `cone reaches sorryAx: false`, all `watched declarations in cone: none of 6`
  (both under the default WATCH set — the six gap declarations — and under
  `WATCH="Lean4Lean.NestedWit.trIndDeclN_wit' Lean4Lean.R10.Wit.trIndDecl_wit Lean4Lean.trIndDecl_eq
  Lean4Lean.trIndDeclN_of_ownId Lean4Lean.trIndDeclN_ctorPointwise
  Lean4Lean.trCtorsLen_not_of_restoreData"`, i.e. **the witness's cone contains none of the
  hand-built `trCtorsLen` instances nor the carrier producer**):
  - `Lean4Lean.InductiveDeclExamples.ntreeAux_trCtorsLen_witness` — arity **0**, cone **752**
  - `Lean4Lean.trCtorsLen_of_skelPrefix` — arity 3, cone **706**
  - `Lean4Lean.skelPrefix_iff_trCtorsLen` — arity 5, cone **750**
  - `Lean4Lean.ctorNamesAgree_iff_trCtorsLen` — arity 3, cone **693**
  - `Lean4Lean.trCtorsLen_not_of_sansLen` — arity 0, cone **1169**
  - `Lean4Lean.InductiveDeclExamples.ntreeSurf_skelPrefix` — arity 0, cone **106**
  For reference, measured in the same run: `Lean4Lean.NestedWit.trIndDeclN_wit'` cone 3994,
  `Lean4Lean.R10.Wit.trIndDecl_wit` cone 924, `Lean4Lean.trIndDecl_eq` cone 1054,
  `Lean4Lean.trCtorsLen_not_of_restoreData` cone 3779.
- M12 (`shape.lean`, HEADS=`Lean4Lean.VIndRestore.SpineHargsN`, population 453): 22 constants;
  general producers exist that do **not** touch the surface side —
  `Lean4Lean.VIndRestore.spineHargsN_of_zeroLevel` (arity 13),
  `Lean4Lean.VIndRestore.spineHargsN_of_spineHargsC` (arity 7),
  `Lean4Lean.VIndRestore.spineHargsN_iff_valStrengthen` (arity 11), plus the arity-0
  `Lean4Lean.InductiveDeclExamples.ntreeAux_spineHargsN`. So **`trSpine` does NOT trace to the
  absent surface→abstract construction**; the brief's "fourth field" is not `trSpine`. I verified
  three fields tracing there (`trType`, `trCtors` — named by `CtorPointwise.lean`'s own header —
  and now `trCtorsLen`); I did not identify a fourth and do not assert one.
- M13 (round-close, all on the same tree):
  - whole-tree `lake build`: **Build completed successfully (1639 jobs)**, zero errors.
  - `lake env lean --run scripts/sorry-census-all.lean --run`: on disk 480; population 456;
    **BUILT 456, NOT BUILT 0**; **HOLES 13** (pass A 13, pass B 0). Orphan modules 54 — my new
    module is among them, as any new leaf file is.
  - guards (`lake build Lean4Lean.Verify.Guard` after deleting its olean): **guard 1** "Axioms.lean
    declares exactly the 24 frozen axioms ✓"; **guard 2** "kernel_sound axioms within whitelist ✓
    (proof INCOMPLETE: sorryAx present)"; **guard 3** "checker cone implementation gaps within
    frozen list (2/2 remaining) ✓".
  - section-variable warnings: **0 in-repo**. The single `automatically included section
    variable(s) unused` warning in the build is `Foundation/FirstOrder/SetTheory/Z.lean:35`, i.e.
    the pinned dependency, not this repo.
  - `python3 scripts/layer-check.py`: hard rule ok (65 modules, none reaches `Verify/`), soft
    report unchanged (4 `Theory/` files with direct `Verify/` imports), **exit 0**.

## 2. Prior scorecard

| prior | verdict |
|---|---|
| P1 bare length equation, genuinely separate | **confirmed** (M1) |
| P2 `RestoreData` route really closed | **confirmed** (M3), though under a different name |
| P3 supplier is the absent `List InductiveType → VInductDecl'` | **confirmed** (M5, M8), and sharpened by §3 |
| P4 a cheap `map`-shaped `↔` reduction exists | **confirmed and beaten** (M9): two equivalences, one supplying three fields |
| P5 might already be done | **refuted** (M5) — `shape.lean` found no seventh already-done assignment |
| P6 `trIndDeclN_of_ownId` discharges it internally | **refuted** (M4) — it carries it as `hclen` |
| P7 `ntreeAux` non-degenerate | **confirmed** (M7): `uvars = 1`, `params = [Type u]`, `numNested = 1` |
| P8 clean round-close | **confirmed** (M13); no red build in another stream's file was observed |

## 3. What `TrIndDeclN` needs after this round — TWO SEPARATE CLAIMS

**Claim A — "all twelve fields are general" (twelve existence claims).**  Satisfied, in the same
sense the other eleven were: every field is either block data or has a general producer whose
hypotheses are stated over the block.  `trCtorsLen` was the last one without such a producer; it
now has `Lean4Lean.trCtorsLen_of_skelPrefix` (from `SkelPrefix`) and
`Lean4Lean.trCtorsLen_of_ctorNamesAgree` (from `CtorNamesAgree`), and by
`Lean4Lean.skelPrefix_iff_trCtorsLen` / `Lean4Lean.ctorNamesAgree_iff_trCtorsLen` neither premise
is a strengthening — each *is* the field, given fields that already have producers.  This claim is
now closed.

**Claim B — "the constructor is constructible" (one theorem, hypotheses jointly dischargeable at a
block from the checker's own data).**  **Still open, and this round did not close it.**  The
premises of `trIndDeclN_of_ownId` plus `SkelPrefix` must be discharged *together* at a block whose
`D` came from the checker, and `SkelPrefix`, `trType` and `trCtors` all require the surface→abstract
construction that M8 shows does not exist.  §3's `Lean4Lean.trCtorsLen_not_of_sansLen` proves this
cannot be routed around inside the relation.  What §2 buys for Claim B is a **reduction in
obligations, not a discharge**: one `List` equation (`SkelPrefix`) now discharges three field
obligations — `trCtorsLen`, `ctorName_own`, and `trType`'s name half — so the construction owes
three fewer separate proofs.  Conflating A with B would be the error here: A is closed, B is not.

**Concretely, the next round's target is a single statement**: build (or axiomatise as a
specification) a map from `ElimNestedInductive.Result.types` to a `VInductDecl'` and prove
`D.nameSkelV = surfNameSkel rtypes`.  Chained with the already-proved
`ElimNestedInductive.runSkelExtends` / `nameSkel_prefix_covers_run` (whose conclusion is
`SkelPrefix`'s right-hand side by `rfl`, since `surfNameSkel`'s body is `nameSkel`'s verbatim),
that yields `SkelPrefix types D` from a `run` success, and with it the three fields above.

## 4. Post-hoc check of the one docstring claim I could not make inside the file

- M14 (`lean_run_code`, importing both `Lean4Lean.Verify.Inductive.CtorsLenGeneral` and
  `Lean4Lean.Verify.Inductive.NestedRunInvariant` — which my file deliberately does not):
  `Lean4Lean.surfNameSkel = Lean4Lean.ElimNestedInductive.nameSkel` holds **by `rfl`**, and
  `⟨tail, h⟩ : SkelPrefix types D` type-checks directly from
  `D.nameSkelV = ElimNestedInductive.nameSkel types ++ tail`. So the §2 docstring's bridge claim is
  measured, not asserted, and the chaining with `runSkelExtends` costs no lemma.
- M15 (`lean_verify`): axiom sets — `Lean4Lean.InductiveDeclExamples.ntreeAux_trCtorsLen_witness`
  uses **`[propext]`** only; `Lean4Lean.trCtorsLen_not_of_sansLen` uses
  `[propext, Classical.choice, Quot.sound]`. No `sorryAx`, nothing outside guard 1's frozen set.
