# Handoff: wiring the `trCtors` producer into the assembled `TrIndDeclN` producer

Owner files this round: `Lean4Lean/Verify/Inductive/FlipWiring.lean` (new),
`Lean4Lean/Verify/Inductive/TrIndDeclNProducer.lean` (existing, editable),
`docs/handoff-flipwiring.md` (this file).
Round opened: 2026-09-04, at commit `cc35ed2`.

Predecessors: `docs/handoff-trinddeclnproducer2.md` (the assembled producer,
`trIndDeclN_of_ownId` 21/1154), `docs/handoff-trexprsgeneral.md` (the `trCtors` producer,
`trCtors_of_ctorTr` 21/1257, built on the inferencer `ctorTr?`).

## §1 — My own priors, recorded BEFORE any measurement

Inputs so far: CLAUDE.md, the brief, `docs/handoff-trinddeclnproducer2.md` in full, the two
commit messages `66af93d` / `cc35ed2`, and `Verify/Inductive/TrIndDeclNProducer.lean` in full.
**Not yet opened**: `TrExprSGeneral.lean`, `StageMono.lean`, `InductR.lean`. No script has been
run, no cone measured, nothing elaborated. Everything below is a guess.

### 1.1 On (a), the wiring

`trIndDeclN_of_ownId` currently carries

    hctors : ∀ env₁, env.addIndTypesC D K = some env₁ → ∀ j t T, … → ∀ q c C, … →
             TrIndCtorR env₁ Us D R j c C

and the producer `trCtors_of_ctorTr` reportedly concludes something of that family from a
`ConstLookup Γc env` table. Predictions:

- The wiring is **not** a drop-in substitution of one hypothesis for another: `trCtors_of_ctorTr`
  will conclude a *single* `TrIndCtorR` at one `(j, q)`, not the ∀-quantified field, so the
  wiring must re-quantify and will need per-`(j,q)` fragment-membership and lookup-table
  hypotheses. I put **70%** on "the replacement hypothesis is a ∀-quantified fragment-membership
  condition plus one lookup table", not a literal copy of `trCtors_of_ctorTr`'s premises.
- Arity: before 21. I predict after in **21–27**, centre 23 (65%). Removing one hypothesis and
  adding 2–4 (a table, a fragment-membership predicate, possibly a `Γc`/`env` link and a
  staging-agreement premise) nets upward.
- Cone: before 1154, `trCtors_of_ctorTr` 1257. Cones here union, so I predict the wired
  theorem's cone in **1500–2600**, centre ~1900 (60%). I do **not** expect 1154+1257 = 2411
  exactly; the two share `TrIndCtorR`/`TrExprS`/`VEnv` infrastructure heavily, so overlap should
  pull it well below the sum. If it lands *above* 2411 I have mis-modelled something.
- I put **35%** on the wired version being strictly *harder to use* than the unwired one at
  `ntreeAux` (i.e. the witness needing more work), because a lookup table at the staged
  environment `env₃` is exactly the environment where `csubstTy`-style facts were reported false
  in round 2's §2.3. This is my main risk for (d).

### 1.2 On (b), `ConstLookup` from the step's own data

The named lemma: every `.const` leaf of a constructor type is either a pre-block constant or one
of `D.typeConstsC K`.

- Attribution to `StageMono.lean`: the brief itself tells me to doubt it, and round 2 measured the
  brief's attributions at **1 of 4** correct while its *numbers* were 4 of 4 exact. So I put only
  **30%** on the lemma living in `StageMono.lean`, **45%** on it existing somewhere else in the
  tree (most likely candidates by name: `NestedOccData.lean`, `SpineClosedLand.lean`,
  `WholeTypeBridge.lean`, or `Theory/Inductive/NestedBuild.lean` — the last because `Built` is
  where the constant inventory of a block is bookkept), and **25%** on it not existing at all.
- Combined: **75%** that the fact exists somewhere hole-free, **30%** that the brief's module is
  right. Six already-done assignments have been caught this session by shape scans, so a scan on
  the *conclusion shape* (not the name) is my first instrument, before I write a line.
- If it does not exist, I predict it is genuinely provable but not in one round at cone <500,
  because "every `.const` leaf" needs an induction over the surface `Lean.Expr` of a constructor
  type, and the surface side is where round 2 said the irreducible work is.

### 1.3 On (c), "all fields general" vs "the constructor is constructible"

I commit to the distinction now, before measuring, so I cannot be accused of retrofitting it:

- **All fields general** = for each of the 12 fields there exists a theorem in the tree
  concluding that field from hypotheses that are not block-specific. This is a statement about
  12 separate theorems.
- **The constructor is constructible** = there is a *single* theorem whose hypotheses are jointly
  dischargeable at a general block and whose conclusion is `TrIndDeclN …`. This additionally needs
  the 12 producers' hypotheses to be *simultaneously* satisfiable at one and the same
  `(env, Us, D, K, R)` — in particular at one and the same *environment*, and the staging
  environments differ (`env` pre-block, `env₁ = addIndTypesC`, `env₃`).
- My prediction: after this round **all 12 fields will be general** and the constructor will
  **not** yet be constructible in the strong sense, because the lookup table's environment and
  the spine clause's environment will not be shown to coincide by any general theorem. **60%.**
  Saying "the flip is done" at the end of this round would therefore be the error the brief
  warns about, and I predict the honest answer is "one environment-agreement lemma short".

### 1.4 On (d), the arity-0 witness

- I predict the witness can be re-routed through the wired producer, **70%**, and that the
  lookup table at `ntreeAux` is discharged by `decide`/`rfl` over a two-entry table
  (`List`, `NTree`, plus possibly `_nested.List_1`), **55%**.
- Structural non-borrowing: my closure must exclude the modules holding the hand-built bridges.
  Round 2's witness used `FlipConstruct.lean`'s `tr_ntreeType` / `tr_ntreeNodeType`; the new one
  must not import `FlipConstruct`. But `TrIndDeclNProducer.lean` **already imports
  `FlipConstruct`**, so if I put the new witness in that file the exclusion is structurally
  impossible — I predict I will have to put the witness in `FlipWiring.lean` and keep
  `FlipConstruct` out of *its* imports, which in turn means `FlipWiring.lean` cannot import
  `TrIndDeclNProducer.lean` either. **This is my sharpest concrete prediction of the round (75%)**
  and if true it dictates the file layout: the wired producer must live in `FlipWiring.lean`, not
  in `TrIndDeclNProducer.lean`, or be duplicated.
- Degeneracy: I will re-assert `uvars = 1` and `params = [.sort (.succ (.param 0))]` inside the
  statement, as round 2 did, so the witness cannot collapse to `nfnAux`.

### 1.5 Predictions I commit to, for a later round to score

| # | Prediction | Conf. |
|---|---|---|
| R1 | The replacement hypothesis is not a literal copy of `trCtors_of_ctorTr`'s premises (needs re-quantification) | 70% |
| R2 | Wired arity in 21–27 | 65% |
| R3 | Wired cone in 1500–2600, and strictly below 2411 | 60% |
| R4 | The `ConstLookup` leaf lemma exists somewhere hole-free in the tree | 75% |
| R5 | …and it is **not** in `StageMono.lean` | 70% |
| R6 | After this round all 12 fields are general | 70% |
| R7 | …but the constructor is still **not** constructible; ≥1 environment-agreement lemma short | 60% |
| R8 | The witness must live outside `TrIndDeclNProducer.lean` to keep `FlipConstruct` out of its closure | 75% |
| R9 | Census stays 13 / NOT BUILT 0 | 90% |
| R10 | At least one brief figure (21/1257, 21/1154) is wrong | 15% — round 2 measured all four exact; the brief's numbers are its reliable half |

§2 onward is written after measurement, appended one line per instrument call.

---

## §2 — Measurements (appended as made)

M1. `TrExprSGeneral.lean` §4 read. `Lean4Lean.trCtors_of_ctorTr`'s **conclusion is
    `trIndDeclN_of_ownId`'s `hctors` hypothesis verbatim**, staging and all:
    `∀ env₁, env.addIndTypesC D K = some env₁ → ∀ j t T, … → ∀ q c C, … → TrIndCtorR env₁ Us D R j c C`.
    Its premises are exactly two: `hΓc : ∀ env₁, env.addIndTypesC D K = some env₁ → ConstLookup Γc env₁`
    and `h : ∀ j t T … q c C …, c.name = R.ctorName C.name ∧ ∃ t', ctorTr? Γc Us c.type [] = some (C.typeR D R j, t')`.
    => **R1 is FALSE**: the wiring IS a literal drop-in, no re-quantification, no extra
    environment link. I mispriced it at 70% by assuming a single-`(j,q)` conclusion.
    Net arity change predicted from this alone: −1 explicit +2 explicit +1 implicit (`Γc`) = 21 → 23.
M2. Locations measured (grep for the definition sites of everything round 2's witness used):
    `ntreeRestore_ownId` → `Theory/Inductive/NestedHead.lean`; `ntreeAux_companions` →
    `Verify/Inductive/ValAtParam.lean`; `ntreeAux_restrictStepCfg` → `RestrictStep.lean`/`SortWitEnv.lean`;
    `ntreeAux_argsTypedK_of_wf` → `ArgsTypedSupply.lean`; `ntree_stage₂_exists`, `list_const₃`,
    `ntree_const₃` → `Theory/Typing/ConstSubstNested.lean`. **Only `tr_ntreeType` and
    `tr_ntreeNodeType` live in `FlipConstruct.lean`**, and `TrExprSGeneral.lean` already re-derives
    the second (`tr_ntreeNodeType_general`) plus `ntree_constLookup`/`ntreeNode_ctorTr`.
    `TrTypeProducer.lean` already has the *first*'s replacement: `trType_of_sortPiTr` (general) and
    `InductiveDeclExamples.ntreeAux_trType_uniform` at `ntreeAux`. Neither module imports FlipConstruct.
M3. Import-closure measurement (script over all `import` lines, transitive):
    `TrIndDeclNProducer` 204 modules, **FlipConstruct in closure: TRUE**;
    `FlipRemainder` 202 / FALSE; `TrExprSGeneral` 196 / FALSE; `TrTypeProducer` 195 / FALSE;
    `NestedRestore` 150 / FALSE; `StageMono` 201 / FALSE.
    => FlipConstruct enters `TrIndDeclNProducer`'s closure **only through its own direct
    `import` line**, which exists solely for §3's witness. So **R8 is half-wrong**: the witness does
    not have to leave the producer's file — it is enough to drop that import and re-route §3
    through `ntreeAux_trType_uniform` + `ctorTr?`. I will still put the new witness in
    `FlipWiring.lean` (my file) and reduce `TrIndDeclNProducer.lean` to the two general producers,
    because that is the honest layering: producers with no example in scope at all.
M4. `exists.lean`, population **447 built modules**, 6 watched. BEFORE figures, all exact:
    `Lean4Lean.trIndDeclN_of_ownId` — module `…TrIndDeclNProducer`, **arity 21, cone 1154**,
      hole false, sorryAx false, watched: none of 6.
    `Lean4Lean.trIndDeclN_of_restoreData` — arity 21, cone 2151, hole false, sorryAx false, none of 6.
    `Lean4Lean.trCtors_of_ctorTr` — module `…TrExprSGeneral`, **arity 21, cone 1257**, hole false,
      sorryAx false, none of 6.
    `Lean4Lean.ctorTr?` — arity 4, cone 912, clean, none of 6.
    `Lean4Lean.ConstLookup` — arity 2, cone 8, clean, none of 6.
    `Lean4Lean.trType_of_sortPiTr` — arity 10, cone 3692, clean, none of 6.
    `Lean4Lean.InductiveDeclExamples.ntreeAux_trType_uniform` — arity 6, cone 3714, clean, none of 6.
    `Lean4Lean.InductiveDeclExamples.ntree_constLookup` — arity 4, cone 1071, clean, none of 6.
    `Lean4Lean.InductiveDeclExamples.ntreeNode_ctorTr` — arity 0, cone 1011, clean, none of 6.
    `Lean4Lean.InductiveDeclExamples.ntreeAux_trIndDeclN` — arity 0, cone 5958, clean, none of 6.
    => **R10 FALSE** (as priced at 15%): both brief figures exact. The brief's numbers remain its
    reliable half, three rounds running.
    Note for the witness route: `ctorTr?` (912) is a **much cheaper** `trType` route than
    `sortPiTr?`'s producer (3692/3714), since `TrIndType` is `name ∧ TrExprS … t.type T.type` and
    `ntreeIndType.type` (`Type u → Type u`) has no `.const` leaf at all.
M5. `StageMono.lean` read in full (138 lines, 7 declarations): `ValAt.mono`, `ValAt.addConstList`,
    `csubstTy_off_ctorConsts`, `csubstTy_off_recConsts`, `valAt_ctorStage`, `valAt_recStage`,
    `valAt_bothStages`. Every one is about `VIndRestore.ValAt` stage monotonicity or the `mkPi`
    bridge congruence. **Nothing about `.const` leaves of constructor types.** And
    `grep -rn ConstLookup` over all of `Lean4Lean/` returns hits in `TrExprSGeneral.lean` and
    **nowhere else**. => **R5 CONFIRMED**: the brief's attribution to `StageMono.lean` is WRONG,
    the sixth wrong attribution measured this session.
M6. Field census re-derived from `Verify/Environment/InductR.lean:276-352` (12 fields, read
    verbatim) against what the tree concludes **generally**:
    block data (4): `safe`, `uvars`, `np`, `length`.
    general (6): `companions` (a `RestoreData` field), `trSpine` (two `VIndRestore.spineHargsN_of_*`
      routes), `ctorName_own` + `recName_own` (proved inside `trIndDeclN_of_ownId`'s body),
      `recName_aux` (`mkRestore_recName_aux`), `trType` (`trType_of_sortPiTr`, 10/3692).
    general as of `66af93d` (7th): `trCtors` (`trCtors_of_ctorTr`).
    **OPEN (1): `trCtorsLen`.** Every instance in the tree is a concrete-block `rfl` inside a
    witness (`Verify/Environment/Induct.lean:283`, `AddDeclWF.lean:277`, `NestedRestoreWit.lean:469`,
    `StagesFiring.lean:170` which just re-projects another witness). And
    `Verify/Inductive/CtorPointwise.lean` §3 **refutes** the obvious supplier:
    `Lean4Lean.ElimNestedInductive.Result.trCtorsLen_not_of_restoreData` — `RestoreData` cannot see
    `types[j].ctors` at all, so no strengthening of `RestoreData.ctor` can produce it.
    => **The brief's "4 block data, 7 general, plus trCtors" (= 12) is off by one.** The true
    reading is 4 + 6 + trCtors = 11 general, **`trCtorsLen` still open**. This is the round's
    correction to the brief and it is what makes (c)'s answer "not all fields general".
M7. `Lean4Lean/Verify/Inductive/FlipWiring.lean` written, **zero diagnostics** (LSP returns an
    empty item list — no errors and no warnings). Content: `VInductDecl'.mem_typeConstsC_of_mem_types`,
    `constLookup_of_split`, `split_of_constLookup`, `constLookup_iff_split`,
    `constLookup_staged_of_split`, `constLookup_staged_of_member_or_pre`, `constLookup_none`.
    The named lemma is proved **as an `↔`**: at a staged environment `ConstLookup Γc env₁` is
    *equivalent* to "every table entry is in `D.typeConstsC K` or is a pre-block constant".
    No induction over `Expr` occurs anywhere in the file.
M8. `lake build` whole tree: **Build completed successfully (1636 jobs)**, green. `CtorPointwise.lean`
    (the only importer of `TrIndDeclNProducer`, and the one consumer of `ntreeAux_trIndDeclN`)
    still builds unchanged.
M9. `exists.lean`, population **450 built modules**, AFTER figures:
    `Lean4Lean.trIndDeclN_of_ownId` — **arity 22, cone 1445** (was 21 / 1154), hole false,
      sorryAx false, watched: none of 6.
    `Lean4Lean.trIndDeclN_of_restoreData` — **arity 22, cone 2373** (was 21 / 2151), clean, none of 6.
    New in `FlipWiring.lean`: `VInductDecl'.mem_typeConstsC_of_mem_types` 5/430;
      `constLookup_of_split` 7/478; `split_of_constLookup` 10/518; `constLookup_iff_split` 6/521;
      `constLookup_staged_of_split` 7/479; `constLookup_staged_of_member_or_pre` 7/517;
      `constLookup_none` 1/53. All hole false, sorryAx false, none of 6.
    New in `TrIndDeclNProducer.lean`: `InductiveDeclExamples.tr_ntreeType_of_ctorTr` 1/1152;
      `InductiveDeclExamples.ntreeGc_constLookup` 4/1075. Both clean, none of 6.
    `InductiveDeclExamples.ntreeAux_trIndDeclN` — **arity 0, cone 6044** (was 5958), clean, none of 6.
    `InductiveDeclExamples.nfnAux_is_degenerate` — arity 0, cone 48, clean, none of 6.
    => **R2 TRUE** (22, inside 21–27). **R3 FALSE**: I predicted cone 1500–2600 and it is **1445**,
    below my band — the "strictly below 2411" half was right and the direction of the overlap
    argument was right, but I under-estimated how much `trIndDeclN_of_ownId` and
    `trCtors_of_ctorTr` share. Note the wired producer costs **+291 cone** over the version that
    *assumed* the field, and the arity went **up by only one** despite gaining two hypotheses,
    because the `∃ env₁, addIndTypesC = some env₁` premise became unnecessary.
M10. Non-borrowing, by cone with an extended watch list (`WATCH=` with 10 names, all 10 resolved):
    `ntreeAux_trIndDeclN` cone 6044 reports **watched declarations in cone: none of 10**, the ten
    being `InductiveDeclExamples.tr_ntreeType`, `…tr_ntreeNodeType`, `NestedWit.trIndDeclN_wit`,
    `NestedWit.trIndDeclN_wit'`, `TrIndDecl.toN`, `InductiveDeclExamples.ntree_constLookup`,
    `trType_of_sortPiTr`, `InductiveDeclExamples.ntreeAux_trType_uniform`, `sortPiTr?`,
    `InductiveDeclExamples.ntreeAux_spineHargsN`. Same line for `tr_ntreeType_of_ctorTr`.
M11. Structural exclusion, measured over the transitive `import` graph:
    `TrIndDeclNProducer` closure **206 modules**, `FlipWiring` closure **197 modules**; in both,
    **`Verify/Inductive/FlipConstruct` is NOT in the closure** and neither is
    `Verify/Inductive/TrTypeProducer`. So `tr_ntreeType`, `tr_ntreeNodeType`, `trS_tac`,
    `type_tac`, `sortPiTr?` and `trType_of_sortPiTr` are **not in scope** at the witness and cannot
    be borrowed by accident.
    **What structural exclusion CANNOT cover, stated rather than glossed:**
    `NestedWit.trIndDeclN_wit` (the degenerate `nfnAux` witness) lives in
    `Verify/Environment/InductR.lean:902` — the module that *defines* `TrIndDeclN`. No module that
    states the relation can exclude it. `trIndDeclN_wit'` (`NestedRestoreWit.lean:456`) is likewise
    unavoidable: `NestedRestoreWit` enters through
    `TrExprSGeneral → ExprConstructionScope → ValAtParam → SpineClause → ValAtPrice →
     RestrictCompanion → ArgsTypedSupply → NestedOccData → NestedRestoreWit`.
    Those two are excluded by **cone measurement only** (M10), not structurally. Every other
    hand-built route is excluded both ways.
M12. `trType` through the same inferencer, added to `FlipWiring.lean` §2 after M11 (it is a
    second, *wider* general producer for the field): `Lean4Lean.trIndType_of_ctorTr` arity 9,
    cone 1156; `Lean4Lean.trType_of_ctorTr` arity 12, **cone 1159** — against
    `trType_of_sortPiTr`'s 10/3692. Both clean on both lines, none of 10 watched.
    Why it is wider and not merely cheaper: `sortPiTr?` accepts only a sort telescope
    (`∀ …, Sort u`), i.e. a **non-indexed** member; `ctorTr?` accepts `.const`/`.app`, so a member
    typed `∀ (α : Type u) (n : Nat), Type u` — `Nat` is a `.const` leaf — is outside `sortPiTr?`'s
    fragment and inside this one. The witness's `trType` branch now routes through
    `trType_of_ctorTr` with the empty table.
M13. Final build after M12: **Build completed successfully (1636 jobs)**, green. Three guards:
    guard 1 `Axioms.lean declares exactly the 24 frozen axioms ✓`;
    guard 2 `kernel_sound axioms within whitelist ✓ (proof INCOMPLETE: sorryAx present)`;
    guard 3 `checker cone implementation gaps within frozen list (2/2 remaining) ✓`.
    In-repo section-variable warnings: **0** (the build's only one is
    `Foundation/FirstOrder/SetTheory/Z.lean:35`, in the pinned dependency).
M14. `scripts/sorry-census-all.lean --run`: `BUILT: 453; in population but NOT BUILT: 0`;
    `HOLES over the WHOLE built population, unioned across both passes: 13` (pass A 13, pass B 0).
    Identical list to round 2's — census did **not** move in either direction.
M15. Final figures. `Lean4Lean.trIndDeclN_of_ownId` **arity 22, cone 1445**;
    `Lean4Lean.trIndDeclN_of_restoreData` **arity 22, cone 2373**;
    `Lean4Lean.InductiveDeclExamples.ntreeAux_trIndDeclN` **arity 0, cone 6045**; all
    hole false, sorryAx false, **none of 10** watched. `lean_verify` on the witness:
    axioms `[propext, Classical.choice, Quot.sound]` only; on `constLookup_iff_split`:
    `[propext, Quot.sound]`. No `sorry`/`admit`/`native_decide`/`axiom`/`partial` in either
    owned file.
M16. `git status`: my changes are exactly `Verify/Inductive/TrIndDeclNProducer.lean` (M),
    `Verify/Inductive/FlipWiring.lean` (new), `docs/handoff-flipwiring.md` (new). Frozen files
    (`Verify/Soundness.lean`, `Verify/Axioms.lean`, `Verify/Guard.lean`) untouched;
    `docs/vacuity-ledger.md` untouched. The other modified/untracked paths belong to concurrent
    streams and I did not touch them.

---

## §3 — Verdicts

### 3.1 (a) The wiring

| | arity | cone | hole | sorryAx | watched |
|---|---|---|---|---|---|
| `Lean4Lean.trIndDeclN_of_ownId` **before** | 21 | 1154 | false | false | none of 6 |
| `Lean4Lean.trIndDeclN_of_ownId` **after** | **22** | **1445** | false | false | none of 10 |
| `Lean4Lean.trIndDeclN_of_restoreData` **before** | 21 | 2151 | false | false | none of 6 |
| `Lean4Lean.trIndDeclN_of_restoreData` **after** | **22** | **2373** | false | false | none of 10 |

The explicit hypothesis `hctors : ∀ env₁, env.addIndTypesC D K = some env₁ → … → TrIndCtorR …`
is gone, replaced by `trCtors_of_ctorTr`'s own two — `hΓc` (the lookup table, now general, §1 of
`FlipWiring.lean`) and `hctr` (the inferencer's `Option` equations). **And the wiring removed a
premise**: `hst : ∃ env₁, env.addIndTypesC D K = some env₁` was carried only so `ctorName_own`
could instantiate the staged `trCtors` field; `hctr`'s name conjunct is unstaged, so the producer
no longer requires the type stage to succeed. Net +1 arity for +2 hypotheses.

### 3.2 (b) `ConstLookup` — verdict

**The attribution to `StageMono.lean` is WRONG.** Read in full: 7 declarations, all about
`VIndRestore.ValAt` stage monotonicity and the `mkPi` bridge congruence. `grep -rn ConstLookup`
over `Lean4Lean/` hits `TrExprSGeneral.lean` and nothing else. Not already done anywhere.

**And the lemma as named is not the lemma that is needed.** It was stated as a claim about the
`.const` *leaves of a constructor type* — needing an induction over a surface `Lean.Expr`.
`ConstLookup Γc env₁` mentions no `Expr` and no constructor type: it is a claim about the
**table**. Proved this round in `FlipWiring.lean`, with no induction anywhere, and proved as an
**`↔`** (`constLookup_iff_split`, 6/521), so nothing weaker suffices and nothing stronger exists:

    ConstLookup Γc env₁  ↔  ∀ c ci, Γc c = some ci → (c, ci) ∈ D.typeConstsC K ∨ env.constants c = some ci   (given env.addIndTypesC D K = some env₁)

Two obligations had been conflated under one name. The **environment** one is now closed
completely and generally. The **expression** one survives, and is a different thing:
`CtorsInFragment Γc Us types` (`TrExprSGeneral.lean` §4a) — each constructor type built from
`.sort/.bvar/.const/.app/.forallE/.mdata` with every `.const` leaf present in `Γc`. That is
where enumerating the leaves is unavoidable (you cannot write `Γc` without them), but it is a
**per-block computation** settled by `rfl`/`decide`, not a theorem a general round can discharge.

### 3.3 (c) What the flip needs next — and the distinction the brief warned about

**Field census, corrected.** The brief's "4 block data, 7 general, and `trCtors` now has a general
producer" sums to 12 with no slot left for `trCtorsLen`. The true census is **4 block data, 6
previously general, `trCtors` general (7th), and `trCtorsLen` OPEN** — 11 of 12.

- `trCtorsLen` has no general producer anywhere: every instance in the tree is a concrete-block
  `rfl` inside a witness.
- Worse, the obvious supplier is **refuted**:
  `Lean4Lean.ElimNestedInductive.Result.trCtorsLen_not_of_restoreData` (`CtorPointwise.lean` §3)
  — `RestoreData` never mentions `types[j].ctors`, so no strengthening of `RestoreData.ctor`
  can produce it. Its real supplier is whatever *constructs* `D` from `types`, which the tree
  does not have.

**"All fields general" ≠ "the constructor is constructible", and both are currently false — for
different reasons.**

*All fields general* is 12 separate existence claims: for each field, some theorem concludes it
from non-block-specific hypotheses. Status: **11 of 12**, `trCtorsLen` missing.

*The constructor is constructible* additionally requires the 12 producers' hypotheses to be
dischargeable **simultaneously, at one and the same `(env, Us, D, K, R)`** — one theorem, not
twelve. `trIndDeclN_of_ownId` (arity 22) is that theorem, and its 12 explicit hypotheses split:

| hypotheses | status |
|---|---|
| `hsafe`, `huv`, `hnp`, `hlen` | block data (inputs of the site) |
| `hown`, `hcomp`, `hrax` | general — `RestoreData`'s `mkRestore_ownId`, `companions`, `mkRestore_recName_aux` |
| `hspine` | general — the two `VIndRestore.spineHargsN_of_*` routes |
| `hΓc` | general **as of this round** — `constLookup_staged_of_split` |
| `hctr` | general **modulo fragment membership**: a computation, not a theorem |
| `hty` | general — `trType_of_sortPiTr`, and now the wider `trType_of_ctorTr` |
| `hclen` | **OPEN, no producer, and `RestoreData` refuted as a source** |

So the constructor is not constructible, and I was **wrong about why**. My prior R7 said the
blocker would be an environment-agreement lemma between the lookup table's environment and the
spine clause's. There is **no such gap**: `hΓc`, `hctr` and `hspine` are all quantified over the
same `env.addIndTypesC D K = some env₁`, and the wiring needed no agreement lemma at all — it
needed one *fewer* premise. The two real blockers are (i) `trCtorsLen`, and (ii) `hctr`'s
fragment restriction, which makes the assembled theorem a theorem about *fragment* blocks rather
than about every nested block. Item (ii) is the one that would be easiest to overstate away.

**`Lean4Lean.AddInduct` cannot be given its constructor, and this round does not move it.**
`AddInduct` (`Verify/Environment/Basic.lean:149`, no constructors) is on the **constant-map**
side. Its intended definition is `∃ K R, AddInductStagesR m₁ env₁ decl K R m₂ env₂`, and its own
docstring lists what the flip needs: `VEnv.addInductR_ordered` (restored ctor/rec types well
typed, restored ι-rules well formed — three obligations in `Theory/Inductive/NestedOrdered.lean`),
a repair of `Theory/Typing/DeltaUnique.lean`'s freshness argument (false for a nested block,
`VEnv.iotaRulesR_major_not_fresh`), the generalisation of `VDecl.WF.induct` to
`VEnv.AddNestedStep`, and four one-line case additions in two files. `TrIndDeclN` is the
*translation* input `AddInductStagesR` consumes; a constructible `TrIndDeclN` is necessary for
the step to fire and nowhere near sufficient for `AddInduct`. Conflating "the translation
relation is constructible" with "`AddInduct` has a constructor" would be the worst available
error here, and the measurement says they are separated by at least the four items above.

**Ranked list of what the flip needs after this round:**
1. `trCtorsLen` in general — i.e. the construction `types ↦ D` that builds `D.types[j].ctors` by
   a `List.map` over `types[j].ctors`. This is the last field, and it is the *same* missing
   construction, not a separate lemma.
2. `CtorsInFragment` for the blocks the kernel actually sees, or a widening of `ctorTr?` past
   the six-case fragment (`.lam`/`.letE`/`.proj`/`.lit`/`.fvar` are the excluded cases).
3. Only then the `AddInduct` items above, which are independent of everything in this round.

### 3.4 (d) The arity-0 witness

`Lean4Lean.InductiveDeclExamples.ntreeAux_trIndDeclN`, **arity 0, cone 6045**:

    ∃ env₁ : VEnv, VEnv.empty.addInduct' listDecl = some env₁ ∧
      ntreeAux.uvars = 1 ∧ ntreeAux.params = [.sort (.succ (.param 0))] ∧
      TrIndDeclN env₁ [`u] 1 [ntreeIndType] false 1 ntreeAux ntreeK ntreeRestore

Both cleanliness lines: `own value is a hole: false; cone reaches sorryAx: false` and
`watched declarations in cone: none of 10`.

Degeneracy guard machine-checked, not asserted: the two numeric conjuncts are inside the
statement and `nfnAux_is_degenerate : nfnAux.uvars = 0 ∧ nfnAux.params = []` (arity 0, cone 48)
sits next to it, so a witness that drifted to `nfnAux` fails them.

**Reached through the wired producer**: `trCtors` is the `hΓc`/`hctr` pair —
`ntreeGc_constLookup` (4/1075) via `constLookup_staged_of_split`, and `ntreeNode_ctorTr`, an
`rfl`. `trType` is `trType_of_ctorTr` with the **empty** table.

**Structural non-borrowing, and exactly how far it reaches.**
`Verify/Inductive/FlipConstruct.lean` is **not** in the witness module's 206-module import
closure (nor in `FlipWiring.lean`'s 197), so `tr_ntreeType`, `tr_ntreeNodeType`, `trS_tac` and
`type_tac` are not in scope. Neither is `Verify/Inductive/TrTypeProducer.lean`, so `sortPiTr?`
and `trType_of_sortPiTr` are out too. Excluded modules named: **`FlipConstruct`,
`TrTypeProducer`**.
What structural exclusion **cannot** reach, stated rather than glossed:
`NestedWit.trIndDeclN_wit` lives in `Verify/Environment/InductR.lean` — the module that *defines*
`TrIndDeclN` — so no module stating the relation can exclude it; and `trIndDeclN_wit'`
(`NestedRestoreWit.lean`) enters unavoidably through
`ExprConstructionScope → ValAtParam → SpineClause → ValAtPrice → RestrictCompanion →
ArgsTypedSupply → NestedOccData → NestedRestoreWit`. Those two are excluded by **cone
measurement only** (none of 10).

## §4 — Scorecard for R1-R10

| # | Prediction | Conf. | Verdict |
|---|---|---|---|
| R1 | Replacement hypothesis needs re-quantification | 70% | **FALSE** — `trCtors_of_ctorTr`'s conclusion is the field verbatim; a literal drop-in |
| R2 | Wired arity in 21–27 | 65% | **TRUE** (22) |
| R3 | Wired cone in 1500–2600 and below 2411 | 60% | **FALSE** on the band (1445, below it); the "below 2411" half and the overlap reasoning were right |
| R4 | The `ConstLookup` leaf lemma exists somewhere | 75% | **FALSE** — nowhere; and the lemma as named is not the one needed |
| R5 | …and it is not in `StageMono.lean` | 70% | **TRUE** |
| R6 | All 12 fields general after this round | 70% | **FALSE** — 11 of 12; `trCtorsLen` |
| R7 | Constructor still not constructible, ≥1 environment-agreement lemma short | 60% | **conclusion TRUE, mechanism FALSE** — no environment gap exists; the blockers are `trCtorsLen` and fragment membership |
| R8 | Witness must leave `TrIndDeclNProducer.lean` | 75% | **FALSE** — dropping the single `import FlipConstruct` line sufficed; `CtorPointwise.lean` consumes the witness by name, so moving it was not even available |
| R9 | Census 13 / NOT BUILT 0 | 90% | **TRUE** |
| R10 | ≥1 brief figure wrong | 15% | **FALSE** — both exact, third round running |

**4 of 10 clean, plus one half.** The pattern across three rounds is now unambiguous and worth
carrying forward: **this brief's numbers are reliable and its attributions are not.** Every
figure it has quoted (six across three rounds) measured exact; its module attributions are now
7 wrong out of 11. R1/R3/R8 are all the same error of mine — assuming friction where a
file committed hours earlier had already removed it, exactly the failure `shape.lean`'s docstring
was written about. R4 is the more interesting miss: I priced 75% that the lemma existed, and the
truth was that it was *unnecessary in the form stated*, which no existence search would have
found.
