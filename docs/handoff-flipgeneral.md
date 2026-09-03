# Handoff: composing `StrengthenFamily` into the flip's general parameterful obligations

**Owner files:** `Lean4Lean/Verify/Inductive/FlipGeneral.lean` (new, mine) and this file.
**Written incrementally from the first minute** — nine predecessor streams lost their handoff by
writing it at the end; the immediate predecessor on this file family reached 27 lines.

## 0. The two inputs, re-verified before use (`scripts/exists.lean`, population 418 modules)

| name | arity | cone | own hole | reaches `sorryAx` |
|---|---|---|---|---|
| `VIndRestore.argsTypedK_of_succLevel` | 13 | 3335 | false | **false** |
| `VIndRestore.argsTypedK_of_resultSortInhab` | 11 | 3333 | false | **false** |
| `VIndRestore.restrictStep_entry` | 9 | 3257 | false | **false** |
| `VIndRestore.valAt_of_spineHargsC_of_wf` | 13 | 2566 | false | **false** |
| `VIndRestore.spineHargsC_iff_valStrengthen` | 9 | 3258 | false | **false** |
| `VEnv.ctorConstsCR_wf_of_substC'` | 15 | 2453 | false | **false** |
| `VEnv.recConstsR_wf_of_blocksD` | 13 | 2372 | false | **false** |
| `VEnv.recConstsR_wf_of_entriesD` | 13 | 2404 | false | **false** |
| `VEnv.iotaRulesRS_wf_of_hargsD` | 16 | 3131 | false | **false** |
| `VEnv.iotaRulesRS_wf_of_hargsD_of_barrier` | 17 | 3272 | false | **false** |
| `InductiveDeclExamples.ntreeAux_obligationA` | 0 | 3594 | false | **false** |
| `InductiveDeclExamples.ntreeAux_obligationB` | 0 | 5407 | false | **false** |
| `InductiveDeclExamples.ntreeAux_obligationC` | 0 | 5643 | false | **false** |

Note the brief named `valAt_of_spineHargsC_of_wf` and `spineHargsC_iff_valStrengthen` unqualified;
both live in the `VIndRestore` namespace (`Lean4Lean.VIndRestore.…`).  Unqualified they are
`NOT FOUND`, which is exactly the false-absence trap — recorded so nobody re-reports it.

## 1. In progress

## 1. §1 of the owner file — **(A) GENERAL PARAMETERFUL COMPOSES.**  Green as of first build.

Obligation (A)'s general route is `VEnv.ctorConstsCR_wf_of_substC'`
(`Theory/Typing/ConstSubstNested.lean:208`, arity 15, cone 2453, hole-free).  Beyond the four
staging facts it has exactly two premises:

* `hσ : σ.WF env₃ e₁ D.uvars` — at `σ := R.csubstTy D K` this is **node 3 of RestrictStep's
  cycle**, because `VIndRestore.csubstTy_WF_of_val` (`RestrictCompanion.lean`, arity 14,
  cone 2622, hole-free) has `VIndRestore.ValAt D K e₂ e₁` — spelled out, not by name — as its
  only non-staging hypothesis and concludes exactly `(R.csubstTy D K).WF e₂ e₁ D.uvars`;
* `hbridge` — one `TeleDefEq` plus one result conversion per **declared** (non-companion)
  constructor.  This is the parameter β-step and stays.

`StrengthenFamily` delivers node 1 (`D.ArgsTypedK K e₁ occ`) hole-free, `restrictStep_entry` /
`cyc_spine_to_val ∘ cyc_datum_to_spine` moves node 1 → node 3, so `hσ` is discharged.  Three new
theorems in `FlipGeneral.lean` §1:

* `VIndRestore.valAt_of_resultSortInhab` — node 3 from the block's result level;
* `VIndRestore.csubstTy_WF_of_resultSortInhab` — (A)'s `hσ`, from the same;
* `VEnv.ctorConstsCR_wf_of_resultSortInhab` — **(A) in general at `np ≥ 1`, `hσ` gone**, premises
  = `RestrictStepCfg` + datum at `e₂` + `ResultSortInhab` + `hbridge`.

What this replaces: `ntreeAux_ctorConstsCR_wf` (`ConstSubstNested.lean:963`) passes
`ntreeSubst_WF`, a *block-specific* `σ.WF` proved by `type_tac` on the concrete spine
`List.{u} (NTree.{u} #0)`.  That argument is now general.

## 2. The level side condition, checked and NOT assumed away — item (d)

**For (A) it is genuinely the block's own level, and there is no companion mismatch.**  Reason,
and it is structural rather than incidental: `D.lvl` and `D.params` are fields of
`VInductDecl'`, **not** of `VIndType`.  `VIndType.WF.canon` states each member's stored type as
defeq to `VIndType.canonType`, which is `mkPi (D.params ++ T.indices) (.sort D.lvl)` — the *same*
`D.lvl` for the declared members and for the companion members.  So `ResultSortInhab`'s premise at
a companion member is a statement about `Sort D.lvl` over that member's own index telescope, and
`resultSortInhab_of_succ` discharges it from `D.lvl ≈ .succ v` with no per-member level anywhere.
`ntreeAux.lvl = .succ (.param 0)`, so the condition is `decide`-able there.

**For (B)/(C) it FAILS, and at exactly a companion member.**  See §3 below.

## 3. §2 of the owner file — **(B) AND (C) DO NOT COMPOSE.**  The reason, proved.

(B)/(C)'s general routes (`VEnv.recConstsR_wf_of_blocksD` / `_of_entriesD`,
`VEnv.iotaRulesRS_wf_of_hargsD`) share the premise

    hσ : (R.csubst D K).WFD E₂ e₃ D.recUvars

`FlipConstruct.lean` §10 records that premise's `val` field as `VIndRestore.ValAt`.  **That is
true of its type-constant entries and of nothing else.**  `VIndRestore.csubstList`
(`Theory/Inductive/Restore.lean:199`) contributes *three kinds* of entry per companion member —
`csubst_dom` (`Theory/Inductive/NestedRules.lean:145`) is exactly that three-way disjunction:

1. `T.name ↦ R.tyVal D j` — the member's **type constant**.  Its declared type is
   `mkPi (D.params ++ T.indices) (.sort D.lvl)` (`VIndType.WF.canon`).  **This is the family's
   entry**, and §1 uses it.
2. `Lean.mkRecName T.name ↦ R.recVal D _` — the companion's **recursor**.
3. `C.name ↦ R.ctorVal D j C`, one per companion **constructor**.

`R.csubstTy D K` has only kind 1 (`csubstTy_dom`), and the entire five-node cycle — `ValAt`,
`ValStrengthen`, `SpineHargsK`, `SpineStrengthen`, `ArgsTypedK` — is a `∀` over `csubstTy`'s
domain.  So on kinds 2 and 3 the family is **silent, not weak**: the judgements it moves are not
indexed by those names at all.

Proved in `FlipGeneral.lean` §2, generally (no `ntreeAux` in sight):

* `VIndRestore.csubstTy_le_csubst` — the inclusion, at equal values, from `DomNodup`;
* `VIndRestore.csubst_ctor_off_csubstTy` — **strict at every companion constructor**:
  `csubstTy C.name = none ∧ csubst C.name = some (R.ctorVal D j C)`.  Separation hypothesis is
  `D.allNames.Nodup`, which is not an extra assumption (it is what `addConstList D.allConsts`
  already requires of any addable block);
* `VIndRestore.csubst_rec_off_csubstTy` — the same at the companion recursor;
* `VIndRestore.ValRestC` + `csubst_val_of_valAtC_of_valRestC` — **the residue named**: `csubst`'s
  `val` clause is exactly (family-shaped type part) ∧ `ValRestC`.  `ValRestC` is guarded by
  `R.csubstTy D K c = none`, and the two `_off_csubstTy` lemmas show that guard is satisfied at
  every kind-2 and kind-3 name (given `D.allNames.Nodup`) and fails at every kind-1 name (given
  `D.blockNames.Nodup`, which `addIndTypes`' success supplies) — so `ValRestC` is exactly kinds 2
  and 3, not merely a superset.

**Why the family's engine cannot be extended to kinds 2 and 3, stated as a mechanism and not as a
guess.**  The family works by substituting a *junk inhabitant* for the dropped constant
(`StrengthenFamily.lean` §2; `ntree_junkVal_ne_tyVal` shows the junk value is genuinely different
from the intended `ntreeVal`).  `WFD.val` **pins the value** to `R.ctorVal`/`R.recVal`: there is no
freedom to substitute anything else, so the inhabited/uninhabited split
`VEnv.axiomConservativityWF_iff_uninhabWF` exploits is unavailable.  Kinds 2 and 3 are
`Faithful`-flavoured facts about the intended restoration values — at `ntreeAux` they are
`nlistNil_val_hasType` / `nlistCons_val_hasType` / the `NTree.rec_1` clause inside
`ntree_csubst_WFD₂`/`WFD₃` — and they are honest math, not strengthening.

## 4. §3–§4 of the owner file — the level check, and the arity-0 witness

### The level side condition, grounded rather than argued (item (d))

`VIndType.canonType T D = VExpr.mkPi (D.params ++ T.indices) (.sort D.lvl)` — **`rfl`**, recorded in
the owner file as `VIndType.canonType_eq` (`Theory/Inductive/Decl.lean:329` is the definition).
`params` and `lvl` come from `D`; only `indices` comes from `T`.  So `ResultSortInhab`'s three
discharge clauses (`_of_succ`, `_of_zero`, `_of_lookup`) are uniform in the member, and there is
**no companion whose result level differs from the block's** for the condition to be evaluated at
the wrong one.  Checked at the witness too: `ntreeAux_canon_lvl_uniform` (`decide`) says both
members of `ntreeAux.types` — the declared `NTree` *and* the companion `_nested.List_1` — have
canonical type `mkPi (params ++ indices) (Sort (succ (param 0)))`.

`ntreeAux_level_data` (`decide`): `uvars = 1`, `recUvars = 2`, `lvl = .succ (.param 0)`.

**One thing that is NOT an extra obstacle for (B)/(C), recorded so it is not re-reported.**
`WFD` there is at `D.recUvars` while the cycle is at `D.uvars` (2 vs 1 at `ntreeAux`).  For the
`val` clause this costs nothing: `CSubst.val_of_hasType` (`Theory/Typing/ConstSubst.lean:491`)
absorbs the level quantifier entirely, taking a plain `HasType ci.uvars []` and producing the
`∀ Γ ls ls'` form at *any* `U`.  Where `D.recUvars` does bite is `WFD.const`'s defeq disjunct, whose
`∀ ls, (∀ l ∈ ls, l.WF U)` ranges over more level lists at larger `U` — a strengthening of `const`,
not of `val`.  My own first draft of the owner-file docstring listed this as obstacle 3; that was
wrong and is corrected in the file.

**Where the composition really breaks is not a level but a *type*.**  A companion constructor's
declared type ends in `D.tyApp` (an application of the member type constant) and the companion
recursor's ends in the motive applied to the major premise.  Neither is a `Sort`, so a
`Sort`-inhabitation clause has nothing to say about them **at any level**.  That is one kind worse
than a level mismatch, and it is the honest answer to (d): *the composition fails at the companion
constructor/recursor entries of `R.csubst`, because those entries are not sorts and because
`WFD.val` pins the value so the junk substitution has no freedom.*

### The arity-0 witness (item (e))

`InductiveDeclExamples.ntreeAux_obligationA_via_family` — arity 0, existentially closed over the
declaration history and all three staging environments, at `ntreeAux` (`uvars = 1`,
`params = [.sort (.succ (.param 0))]`, **not** the degenerate `nfnAux`).  It exhibits, at one
block simultaneously:

* `VEnv.empty.addInduct' listDecl = some env₁` and the two stagings;
* `RestrictStepCfg ntreeAux ntreeRestore ntreeK env₁ env₂ env₃ (fun _ => listOcc)`;
* the datum at `e₂` (`ntreeAux_argsTypedK_of_wf`, from `D.WF` alone);
* `ntreeAux.ResultSortInhab env₁ ntreeJunk`;
* **`(ntreeRestore.csubstTy ntreeAux ntreeK).WF env₂ env₃ ntreeAux.uvars` — from the family, not
  from `ntreeSubst_WF`**;
* obligation (A): `∀ c ∈ ntreeAux.ctorConstsCR ntreeRestore ntreeK, VConstant.WF env₃ c.2`.

`ntreeAux_obligationA'` strips it to exactly `ntreeAux_obligationA`'s shape, so the two are
directly comparable.  No `VEnv.HasArgs.of_mkApp` and no `PiInv` anywhere in the file.

## 5. Measurements — `scripts/exists.lean`, population 420 built modules

Every declaration of `FlipGeneral.lean`.  **All hole-free; none reaches `sorryAx`.**

| name | arity | cone | reaches `sorryAx` |
|---|---|---|---|
| `VIndRestore.valAt_of_resultSortInhab` | 11 | 3334 | false |
| `VIndRestore.csubstTy_WF_of_resultSortInhab` | 11 | 3335 | false |
| `VEnv.ctorConstsCR_wf_of_resultSortInhab` | 14 | 3440 | false |
| `VIndRestore.csubstTy_le_csubst` | 7 | 1080 | false |
| `VIndRestore.csubst_ctor_off_csubstTy` | 11 | 1223 | false |
| `VIndRestore.csubst_rec_off_csubstTy` | 9 | 1223 | false |
| `VIndRestore.ValRestC` (def) | 5 | 808 | false |
| `VIndRestore.csubst_val_of_valAtC_of_valRestC` | 13 | 1118 | false |
| `VIndRestore.csubst_val_of_valAt_of_valRestC` | 14 | 1128 | false |
| `VIndType.canonType_eq` | 2 | — | no axioms at all |
| `InductiveDeclExamples.ntreeAux_level_data` | 0 | 171 | false (no axioms) |
| `InductiveDeclExamples.ntreeAux_canon_lvl_uniform` | 0 | — | false |
| `InductiveDeclExamples.ntree_csubst_off_csubstTy` | 0 | 511 | false |
| `InductiveDeclExamples.ntreeAux_obligationA_via_family` | 0 | 4180 | false |
| `InductiveDeclExamples.ntreeAux_obligationA'` | 0 | — | false |

Axiom bar `after ⊆ before`: the axioms used are `propext`, `Quot.sound`, and `Classical.choice`
(only in the `ntreeAux` witnesses, exactly as in `ntreeAux_obligationA` and
`ntreeAux_addInductN_nonvacuous`).  Nothing new.

Zero build warnings in the owner file (`lake env lean Lean4Lean/Verify/Inductive/FlipGeneral.lean`
prints only the `#print axioms` lines).

## 6. What the flip needs after this round (item (c))

| | obligation | premise status |
|---|---|---|
| (A) | restored **constructor** types WF at stage 1 | `hσ` **discharged** by the family at `≈`-successor / `≈`-zero result level; **`hbridge` remains** (the parameter β-step, one per declared constructor) |
| (B) | renamed **recursor** types WF at stage 2 | `hσ.val` splits as family part **∧ `ValRestC`**; `ValRestC` and `hσ.const`'s defeq disjunct remain |
| (C) | restored **ι-rules** WF at stage 3 | same `hσ`, same residue, plus `R.IotaHargs` per rule |

> **The constructor for `AddInduct`'s replacement is available at every block whose result level is
> `≈`-a-successor or `≈`-zero as far as obligation (A) is concerned — with only `hbridge` left
> there — provided (B) and (C) are supplied.  (B) and (C) are NOT reduced to the strengthening
> family: their residue is `VIndRestore.ValRestC` (the companion constructors' and recursor's own
> value typings) plus the defeq disjunct of `CSubst.WFD.const` at every declared constructor.**

**Holes routed through: none.**  Verified with `scripts/exists.lean` on every declaration
(table above), not asserted.  `VEnv.StrengtheningTarget` / `VEnv.AxiomConservativityWF` — the hole
`RestrictStep.lean` §2 located the cycle's only entry on — is **not** in §1's cone.

## 7. Open, with the precise reason

1. **`ValAt` at the ctor stage.**  §2a's split wants `R.ValAt D K E₂ F₂`, one `addConstList` above
   the pair `(e₂, e₁)` the cycle runs at.  Moving it up is a source-environment monotonicity step
   (the extra constants at `E₂` are constructor names, hence outside `csubstTy`'s domain, so it
   should be short) — **not written here, and not claimed.**
2. **`ValRestC` in general.**  The companion constructors' and recursor's value typings.  Concretely
   available at `ntreeAux` inside `ntree_csubst_WFD₂` / `ntreeAux_WFD₃_exists`; no general route.
3. **`WFD.const`'s defeq disjunct in general** — the (A)-`hbridge` phenomenon at stages 2 and 3.
4. **`hbridge` in general** for (A) itself.  Unchanged by this round; it is arithmetic about the
   parameter β-redex, not strengthening.

## 8. Frozen files

None touched, none needed.  No edit to `Verify/Soundness.lean`, `Verify/Axioms.lean`,
`Verify/Guard.lean` is required by anything in this round, and no such edit is requested.

## 9. Name-resolution note for future briefs

The brief named `valAt_of_spineHargsC_of_wf` and `spineHargsC_iff_valStrengthen` bare.  Bare they
are `NOT FOUND`; both are in the `VIndRestore` namespace (`ValAtParam.lean`, cones 2566 and 3258,
hole-free).  Recorded because "NOT FOUND under the name I was given" is the shape a false absence
claim takes.
