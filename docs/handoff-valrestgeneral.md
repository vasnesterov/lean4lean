# Handoff: `VIndRestore.ValRestC` in general — the residue (B)/(C) were left with

**Owner files:** `Lean4Lean/Verify/Inductive/ValRestGeneral.lean` (new, mine) and this file.
**Written incrementally from minute one** — ten predecessors on this file family lost their
handoff by writing it last.

## 0. The brief's premise, re-verified before use — and PARTLY ALREADY IN THE TREE

`scripts/exists.lean`, population 421 built modules.

| name | arity | cone | own hole | reaches `sorryAx` |
|---|---|---|---|---|
| `Lean4Lean.VIndRestore.ValRestC` | 5 | 808 | false | false |
| `Lean4Lean.VIndRestore.csubst_val_cases` | 18 | 1249 | false | false |
| `Lean4Lean.VIndRestore.tyVal_hasType_of_faithful` | 16 | 1539 | false | false |
| `Lean4Lean.VIndRestore.csubst_WF_const` | 24 | 1852 | false | false |
| `Lean4Lean.VIndRestore.substC_ctorType_csubst_eq_csubstTy` | 18 | 1754 | false | false |
| `Lean4Lean.VIndRestore.ctorVal_hasType_of_faithful` | — | — | — | **NOT FOUND** |
| `Lean4Lean.VIndRestore.csubst_WFD_const` | — | — | — | **NOT FOUND** |

**The first correction of the round, and it retires part of the brief.**
`VIndRestore.csubst_val_cases` (`Theory/Inductive/NestedRules.lean` §8.5) already splits
`csubst`'s **whole** `val` clause into two data — `hty` (the type-constant part, the family's)
and `hctor` (the *companion constructors*' part) — and it already **discharges the companion
recursor part outright at the ctor stage**, by freshness: `E₂ = E₁.addIndCtors D` does not
declare `mkRecName T.name`, and `val` is guarded by `env₀.constants c = some ci`.  §8.5's own
docstring says so ("At the second stage … the recursor entries impose nothing … At the third
stage the recursor entry becomes live").

So of `ValRestC`'s two halves:

* the **recursor** half is *already free* at the pair obligation (B) uses, `(E₂, F₂)`.  It is
  live only at the pair obligation (C) uses, `(E₃, F₃)`;
* the **constructor** half is `csubst_val_cases`' `hctor`, and *that* is genuinely open in
  general: nothing in the tree concludes `HasType … (R.ctorVal D j C) …`.

This handoff's own §1 records the search that establishes the second bullet.

## 1. The search that establishes "the constructor half is open" (not asserted)

`scripts/shape.lean`, population 421 built modules.

* `HEADS="Lean4Lean.VIndRestore.ctorVal Lean4Lean.VEnv.HasType"` → **1 hit**, and it is
  `csubst_val_cases` itself (arity 18), i.e. the thing that *asks* for the datum.  0 structure
  fields.  So nothing in the tree concludes a typing for `R.ctorVal`.
* `HEADS="Lean4Lean.VIndRestore.recVal Lean4Lean.VEnv.HasType"` → **0 hits**, heads resolved.

Both heads resolved to real constants, so both counts are meaningful.

## 2. §1–§2 of the owner file — GREEN.  The split is an `↔`, and (B)'s recursor half is free

* `VIndRestore.ValRestCtor`, `VIndRestore.ValRestRec` — the two halves, named.
* `VIndRestore.valRestC_iff` — **`ValRestC ↔ ValRestCtor ∧ ValRestRec`**, side conditions
  `D.allNames.Nodup`, `R.DomNodup D K`, `D.blockNames.Nodup`, all of which an addable block
  already satisfies (`addConstList D.allConsts`, the substitution's key-nodup, `addIndTypes`).
  The `↔` uses `FlipGeneral.lean`'s `csubst_ctor_off_csubstTy` / `csubst_rec_off_csubstTy` in the
  forward direction and `csubst_dom` + `csubstTy_eq_some` in the backward one.
* `VIndRestore.valRestRec_of_fresh`, `valRestRec_ctorStage` — the recursor half holds for
  **every** `F` at the ctor stage, from `E₂.addIndRecs D = some E₃` alone.
* `VIndRestore.valRestC_iff_ctorStage` — **`ValRestC ↔ ValRestCtor` at `(E₂, F)`**, so obligation
  (B)'s residue is the constructor half and nothing else.

Vacuity note, stated rather than buried: `valRestRec_ctorStage` is true because the source lookup
fails, and that *is* the honest content — the clause is guarded by
`env₀.constants c = some ci` and `E₂` has not declared the companion recursor.  It is not a
vacuity **defect** in the ledger's sense because the sibling half is live at the same pair (§7
exhibits two live entries at `ntreeAux`), and because the same clause is non-vacuous one stage up,
where §5 handles it.

## 3. §3–§4 — the constructor half in general, from a spec clause that already exists

* `VIndRestore.ctorVal_hasType_of_faithful` — the mirror of `NestedRules.lean` §8.7's
  `tyVal_hasType_of_faithful` at `Faithful.ctor_agree` instead of `ty_agree`.  Conclusion:
  `F.HasType D.uvars [] (R.ctorVal D j C) (C.typeR D R j)`.  **`hsplit` is dropped** —
  `HargsShared`'s `hsplit_free` makes it free at every head — so the single datum consumed is
  `HargsShared`'s **constructor-head `hargs`**, which that file's §6 had already isolated (F3).
  Nothing new is asked of the specification.
* `VIndRestore.CtorTypeBridge` — the residue: one defeq per companion constructor between
  `C.typeR D R j` and `(C.type D j).substC (R.csubst D K)`.  This is obligation (A)'s `hbridge`
  phenomenon (the restoration's `mkLams D.params` becoming a saturated β-redex under `substC`,
  `NestedRules.lean` §8.8) evaluated at the **companion** constructors instead of the declared
  ones.
* `VIndRestore.ctorConst_ctorStage` — the stage-2 source lookup.
* `VIndRestore.valRestCtor_iff_ctorTyped` — **the second `↔`**: given the bridge, `ValRestCtor` at
  the ctor stage *is* the restored-type typing.  Both directions are one `IsDefEq.defeq`.
* `VIndRestore.valRestC_ctorStage_of_faithful` — the composition: **obligation (B)'s `hσ.val`
  residue, in general, = `Faithful.ctor_agree` + constructor-head `hargs` + the bridge.**

## 4. §5 — the recursor half at obligation (C)'s pair, and it is (B)'s own `hbridge`

* `VIndRestore.RecTypeBridge` — one defeq per companion member between
  `(D.recTypeR R j).substC (R.csubst D K)` and `(D.recType j).substC (R.csubst D K)`.  This is
  exactly the hypothesis of `InductiveDeclExamples.ntreeAux_recConstsR_wf_of_bridge` — obligation
  (B)'s `hbridge` — in undecomposed form: (B) states it as a `mkPi` split plus `TeleDefEq` plus a
  body defeq, which is a *presentation* of the same defeq.
* `VIndRestore.RecValStored`, `valRestRec_iff_recValStored` — **the third `↔`**: at the rec stage
  `ValRestRec` *is* "the renamed recursor inhabits the substituted stored type".
* `VIndRestore.recConst_recStage`, `recConstR_declared`, `recVal_hasType_recTypeR` — the two
  lookups and the free typing at the restored type (`R.recVal` is a **rename**: a constant, no
  `mkLams`, so no β-redex of its own).
* `VIndRestore.recValStored_of_recBridge`, `valRestC_recStage_of_bridges` — the composition.

**Why §5 gives an implication and not an `↔` at `RecTypeBridge`, recorded so it is not
re-reported as an oversight.**  Reading the bridge back off `ValRestRec` is uniqueness of types
applied to the two types `R.recVal` inhabits, and `IsDefEq.uniq` is one of the project's thirteen
holes.  The `↔` is therefore stated at `RecValStored`, where no uniqueness is needed.  Routing
through the hole for a prettier `↔` would put a hole in this file's cone, which item (d) forbids.

## 5. §6 — item (b): `WFD.const`'s defeq disjunct at every declared constructor, GENERAL

* `VIndRestore.csubst_WFD_const` — `NestedRules.lean` §8.4's `csubst_WF_const` with the bridge
  weakened from a syntactic **equation** to a `IsDefEq`.  The equation form is *refuted* at a
  parameterised block (`InductiveDeclExamples.ntreeNode_substC_ne_typeR`), which is exactly why
  `CSubst.WFD` exists; this is the theorem that cashes it in.  Measured: the disjunct is used at
  **one** of the three branches (the declared constructors); the block-name and off-block branches
  produce the left disjunct with `csubst_WF_const`'s own proofs unchanged.
* `VIndRestore.csubst_WFD` — **`(R.csubst D K).WFD E₂ e₂ U` in general at a parameterised block**,
  i.e. obligation (B)'s `hσ`.  `closed` from `csubst_closed`, `defeq` from `csubst_WF_defeq`,
  `const` from `csubst_WFD_const`, `val` from `csubst_val_cases` with `hty` (the family's node) and
  the constructor half from §3/§4.  Arity 32, cone 2978, hole-free.  `csubst_WF` — the `CSubst.WF`
  version — is unavailable at `np ≥ 1`; this is its replacement.

On `D.recUvars ≠ D.uvars`: `U` is left free and the bridge is asked at the same `U`, so a caller at
`D.recUvars` supplies a `D.recUvars`-bridge.  No `D.uvars`-only bridge is silently reused at the
larger count.  The witness (§6 below) supplies `hbridgeD` at `U = ntreeAux.recUvars = 2` with
`ls.length = ntreeAux.uvars = 1`, which is precisely the mixed instantiation the correction was
about.

## 6. §7 — item (c): the arity-0 witness at `ntreeAux`, with anti-vacuity exhibited

`InductiveDeclExamples.ntreeAux_valRestC_both_stages` — **arity 0, cone 3811, hole-free**,
existentially closed over the declaration history and all six staging environments, at `ntreeAux`
(`uvars = 1`, `params = [.sort (.succ (.param 0))]`, `recUvars = 2`; **not** the degenerate
`nfnAux`, whose empty `params` would make `ctorVal`'s `mkLams` empty and §4's bridge `rfl`).  It
exhibits, at one block simultaneously:

* the full stage-3 staging (`ntree_stage₃_exists`);
* `ValRestCtor` and `ValRestRec` at `(E₂, F₂)`, and `ValRestC` there through §1's `↔`;
* the **two instantiated typings** the constructor half fires at (companion `nil` and `cons`), so
  the `∀` is not empty — this is the anti-vacuity check `docs/vacuity-ledger.md` §0 asks for;
* `CtorTypeBridge` at `F₂` — §4's premise, **inhabited**;
* `hbridgeD` at `F₂` and `U = recUvars = 2` — §6's premise, **inhabited**;
* `RecTypeBridge` at `F₃` — §5's premise, inhabited (it *is* `rRecPi1`);
* `ValRestRec` and `ValRestC` at `(E₃, F₃)`, where the recursor half is **live**.

Supporting (all hole-free): `ntree_ctorVal_nil`/`_cons` (`rfl`), `ntree_valRestCtor`,
`ntree_ctorTypeBridge_nil` (cone 986), `ntree_ctorTypeBridge_cons` (987), `ntree_ctorTypeBridge`
(1064), `ntree_hbridgeD` (2056), `ntree_recTypeBridge` (1882).

The two constructor bridges are one and two β-steps respectively, and the asymmetry is content: at
`nlistCons` the `NTree` field does **not** move (it is recursive into a *declared* member, so
`csubst` leaves it alone) while the companion field and the result head both do.  These are the
same β-steps `ConstSubstNested.lean` §D.3 performs *inside*
`nlistNil_val_hasType`/`nlistCons_val_hasType` and never exposes.

No `VEnv.HasArgs.of_mkApp`, no `PiInv`, anywhere in the owner file.

## 7. Measurements — `scripts/exists.lean`, population 423-425 built modules

All hole-free; **none reaches `sorryAx`**.

| name | arity | cone |
|---|---|---|
| `VIndRestore.ValRestCtor` (def) | 5 | 806 |
| `VIndRestore.ValRestRec` (def) | 5 | 806 |
| `VIndRestore.valRestC_iff` | 8 | 1259 |
| `VIndRestore.valRestRec_of_fresh` | 6 | 809 |
| `VIndRestore.valRestRec_ctorStage` | 7 | 1099 |
| `VIndRestore.valRestC_iff_ctorStage` | 10 | 1315 |
| `VIndRestore.ctorVal_hasType_of_faithful` | 17 | 1743 |
| `VIndRestore.CtorTypeBridge` (def) | 4 | 909 |
| `VIndRestore.ctorConst_ctorStage` | 9 | 1062 |
| `VIndRestore.valRestCtor_iff_ctorTyped` | 7 | 924 |
| `VIndRestore.valRestC_ctorStage_of_faithful` | 20 | 2151 |
| `VIndRestore.RecTypeBridge` (def) | 4 | 947 |
| `VIndRestore.RecValStored` (def) | 4 | 867 |
| `VIndRestore.valRestRec_iff_recValStored` | 7 | 1141 |
| `VIndRestore.recConst_recStage` | 7 | 1096 |
| `VIndRestore.recConstR_declared` | 9 | 1203 |
| `VIndRestore.recVal_hasType_recTypeR` | 10 | 1339 |
| `VIndRestore.recValStored_of_recBridge` | 7 | 1402 |
| `VIndRestore.valRestC_recStage_of_bridges` | 14 | 1564 |
| `VIndRestore.csubst_WFD_const` | 25 | 1852 |
| `VIndRestore.csubst_WFD` | 32 | 2978 |
| `InductiveDeclExamples.ntree_ctorVal_nil` | 0 | 366 |
| `InductiveDeclExamples.ntree_ctorVal_cons` | 0 | 366 |
| `InductiveDeclExamples.ntree_valRestCtor` | 7 | 1001 |
| `InductiveDeclExamples.ntree_ctorTypeBridge_nil` | 3 | 986 |
| `InductiveDeclExamples.ntree_ctorTypeBridge_cons` | 3 | 987 |
| `InductiveDeclExamples.ntree_ctorTypeBridge` | 3 | 1064 |
| `InductiveDeclExamples.ntree_hbridgeD` | 15 | 2056 |
| `InductiveDeclExamples.ntree_recTypeBridge` | 6 | 1882 |
| `InductiveDeclExamples.ntreeAux_valRestC_both_stages` | **0** | **3811** |

Axiom bar `after ⊆ before`: `propext`, `Quot.sound`, and `Classical.choice` (only in
`csubst_WFD_const`/`csubst_WFD`, inherited from `csubst_WF_const`'s own cone).  Nothing new.

Zero warnings in the owner file: `lake env lean Lean4Lean/Verify/Inductive/ValRestGeneral.lean`
prints only the `#print axioms` lines.

## 8. Item (d): which of the thirteen holes this routes through — NONE

Measured, not asserted: every declaration above reports `cone reaches sorryAx: false`.  Two holes
were specifically at risk and neither is entered:

* **`IsDefEq.uniq` (unique typing).**  The natural `↔` for the recursor half — reading
  `RecTypeBridge` back off `ValRestRec` — is uniqueness of types applied to the two types
  `R.recVal` inhabits.  §5 therefore states its `↔` at `RecValStored`, where no uniqueness is
  needed, and offers the bridge as an implication into it.  Recorded in the file so a successor does
  not "improve" it into the hole.
* **`VEnv.StrengtheningTarget` / `VEnv.AxiomConservativityWF`.**  Absent: this file never enters
  RestrictStep's cycle.  The strengthening family is `FlipGeneral` §1's business and appears here
  only as `csubst_WFD`'s `hty` hypothesis, passed through.

## 9. What remains of (B) and (C) after this round

| | obligation | what is left |
|---|---|---|
| (A) | restored **constructor** types | `hbridge` — one telescope defeq per *declared* constructor |
| (B) | renamed **recursor** types | `csubst_WFD`'s hypotheses: `hty` (the family's node, `FlipGeneral` §1) + `hargs` (`HargsShared`'s constructor head) + `CtorTypeBridge` + `hbridgeD`; plus the route's own telescope bridge |
| (C) | restored **ι-rules** | the same, **plus** `RecTypeBridge` = (B)'s own `rhbridge`; plus `IotaHargs` per rule |

> **`ValRestC` needs no new specification clause.**  Its recursor half is free at obligation (B)'s
> staging pair and is (B)'s own recursor bridge at (C)'s; its constructor half is
> `Faithful.ctor_agree` — already in the spec — plus `HargsShared`'s constructor-head `hargs` and
> one bridge defeq per companion constructor.  Every residue of (B) and (C) is now either one of
> `HargsShared`'s two data or β-redex arithmetic of the `hbridge` family.  None of it is a
> strengthening, an inhabitation, or a conservativity question.

## 10. What is NOT claimed

1. **`HargsShared`'s constructor-head `hargs` is not produced here.**  §3 consumes it.
   `HargsShared` §6 already measured it as irreducibly distinct from the type head's datum (F3), and
   `VIndRestore.instAt_indep_of_tyArgs` (`NestedRules.lean` §8.7) shows no restoration-independent
   argument can produce either.  That is the one live datum left on the constructor half.
2. **`csubst_WFD` is not instantiated at `ntreeAux`.**  It does not need to be —
   `ntree_csubst_WFD₂` already exists as the concrete `WFD` there — and instantiating it would
   require `Faithful` + `hargs` + `hty` at the witness, which belong to other files.  What §7 does
   instantiate is every premise this file *introduced* (`CtorTypeBridge`, `hbridgeD`,
   `RecTypeBridge`), so no hypothesis of this file is left unshown-satisfiable.
3. **The `ValAt` monotonicity step** between the type stage and the ctor stage
   (`FlipGeneral.lean` §2a caveat (i)) is untouched.
4. **Nothing about obligation (B)/(C)'s own telescope bridges** (`recConstsR_wf_of_substCD'`'s
   `hbridge`, `IotaHargs`).  This file reduces `hσ`; it does not discharge the routes' other
   premises.
5. No frozen file was read for editing, let alone edited; no `sorry`; no git command was run.
