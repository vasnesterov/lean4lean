import Lean4Lean.Verify.Inductive.StrengthenFamily
import Lean4Lean.Verify.Inductive.ValAtParam

/-!
# `FlipGeneral`: composing the strengthening family into the flip's three obligations

Two results landed on 2026-09-03 and were not joined.

* `Verify/Inductive/FlipConstruct.lean` built `AddInductN` — the payload a constructor for
  `AddInduct` would carry — and isolated the residual as *exactly* the three obligations of
  `VEnv.addInductR_ordered'`: (A) the restored constructor types, (B) the renamed recursor types,
  (C) the restored ι-rules.  It reported all three as theorems **at `D.params = []`** and
  hypothesis-free **at `ntreeAux`**, with the general **parameterful** case open, and named the
  live premise of the general routes as `VIndRestore.ValAt` / the strengthening family.
* `Verify/Inductive/StrengthenFamily.lean` then proved that family hole-free
  (`VIndRestore.argsTypedK_of_resultSortInhab`, `…_of_succLevel`).

This file joins them and reports the join **honestly**, which means reporting one success and one
failure.

**(A) composes.**  §1: obligation (A)'s general parameterful route
(`VEnv.ctorConstsCR_wf_of_substC'`) has two premises beyond the staging — the substitution's
well-formedness `hσ` and the per-constructor bridge `hbridge`.  `hσ` is *exactly* node 3 of
`RestrictStep.lean`'s cycle, so the family discharges it outright, at every block whose result
level is `≈`-a-successor or `≈`-zero.  After §1, **(A) in general at `np ≥ 1` needs `hbridge`
and nothing else**; the hand-built `ntreeSubst_WF` that `ntreeAux_ctorConstsCR_wf` used
disappears.

**(B) and (C) do NOT compose, and the reason is the level side condition at a *companion*
member — precisely the failure mode the brief asked to be checked rather than assumed.**  §2
proves it rather than asserting it.  (B)/(C)'s premise is
`(R.csubst D K).WFD E₂ F₂ D.recUvars`, and three things separate that from the family:

1. **the substitution is bigger.**  `R.csubstTy D K` has *one* entry per companion member (the
   type constant); `R.csubst D K` has *three kinds* — the type constant, the companion's
   recursor, and one per companion constructor (`VIndRestore.csubstList`).  §2.1 proves the
   inclusion is strict in general and exhibits it strict at `ntreeAux`.
2. **the extra entries are not at a sort.**  The family's whole engine is: a companion member's
   declared type is `Π params indices, Sort D.lvl` (`VIndType.WF.canon`), so an inhabitant exists
   as soon as `D.lvl` is `≈ .succ _` or `≈ .zero`.  A companion **constructor**'s declared type
   ends in `D.tyApp _ _` — an application of the member constant, *not* a sort — and a companion
   **recursor**'s ends in the motive applied to the major premise.  §2.2 shows this at
   `ntreeAux` by exhibiting the three values and their three declared types.
3. **the universe count is the recursor's, not the block's.**  `ValAt` and the whole cycle live
   at `D.uvars`; `WFD` for (B)/(C) is at `D.recUvars = if D.isLE then D.uvars + 1 else D.uvars`.
   §2.3: at `ntreeAux` these are `1` and `2`, so even the *type* entry's clause is a different
   statement there — one extra level parameter, the elimination universe.

So `FlipConstruct.lean` §10's sentence "(B) and (C)'s general routes take `hσ …`, whose `val`
field is `VIndRestore.ValAt`" is true of `hσ`'s **type-constant entries only**.  §2 is the
correction, machine-checked.

§3 is the arity-0 witness: obligation (A) at `ntreeAux`, existentially closed, routed through
§1 — i.e. through the family — rather than through the block-specific `ntreeSubst_WF`.

Nothing here is a `sorry`; nothing here uses `VEnv.HasArgs.of_mkApp`; nothing here edits a frozen
file.  §4 audits.
-/

namespace Lean4Lean

open Lean (Name)

/-! ## §1 Obligation (A), general and parameterful, with `hσ` discharged

`VEnv.ctorConstsCR_wf_of_substC'` (`Theory/Typing/ConstSubstNested.lean`) is (A)'s general route.
Instantiated at `σ := R.csubstTy D K` its `hσ` premise is `(R.csubstTy D K).WF e₂ e₁ D.uvars`,
which `VIndRestore.csubstTy_WF_of_val` (`RestrictCompanion.lean` §11a) derives from
`VIndRestore.ValAt D K e₂ e₁` — node 3 of `RestrictStep.lean`'s five-node cycle.  The family
delivers node 1 (`D.ArgsTypedK K e₁ occ`) and the cycle is an `↔`, so node 3 follows.

Everything the route asks about the staging is a field (or a one-line consequence of a field) of
`RestrictStepCfg`, so the composed statement takes the configuration and nothing else. -/

/-- `ValAt` at the configuration, from the family: the cycle entered at the result level. -/
theorem VIndRestore.valAt_of_resultSortInhab {D : VInductDecl'} {R : VIndRestore} {K : List Name}
    {env e₂ e₁ : VEnv} {occ : Nat → VNestedOcc} {b : VIndType → VExpr}
    (Cfg : RestrictStepCfg D R K env e₂ e₁ occ) (H₂ : D.ArgsTypedK K e₂ occ)
    (hb : D.ResultSortInhab env b) : R.ValAt D K e₂ e₁ :=
  cyc_spine_to_val Cfg
    (cyc_datum_to_spine (argsTypedK_of_resultSortInhab Cfg H₂ hb).2)

/-- …hence the substitution's well-formedness, which is (A)'s `hσ`. -/
theorem VIndRestore.csubstTy_WF_of_resultSortInhab {D : VInductDecl'} {R : VIndRestore}
    {K : List Name} {env e₂ e₁ : VEnv} {occ : Nat → VNestedOcc} {b : VIndType → VExpr}
    (Cfg : RestrictStepCfg D R K env e₂ e₁ occ) (H₂ : D.ArgsTypedK K e₂ occ)
    (hb : D.ResultSortInhab env b) : (R.csubstTy D K).WF e₂ e₁ D.uvars :=
  csubstTy_WF_of_val Cfg.ordered Cfg.ordered₁ Cfg.wf Cfg.fresh Cfg.closed Cfg.stage₂ Cfg.stage₁
    (valAt_of_resultSortInhab Cfg H₂ hb)

/-- **OBLIGATION (A), GENERAL, PARAMETERFUL, WITH `hσ` GONE.**  The only premise left beyond the
configuration and the block's result level is `hbridge` — one telescope defeq and one result
conversion per *declared* (non-companion) constructor, which is the parameter β-step and is
genuinely block-specific arithmetic, not a strengthening.

Compare `ntreeAux_ctorConstsCR_wf` (`Theory/Typing/ConstSubstNested.lean`), which passes
`ntreeSubst_WF` — a hand-built `σ.WF` proved by `type_tac` on the concrete spine
`List.{u} (NTree.{u} #0)`.  That argument is replaced here by a general one. -/
theorem VEnv.ctorConstsCR_wf_of_resultSortInhab {D : VInductDecl'} {R : VIndRestore}
    {K : List Name} {env e₂ e₁ : VEnv} {occ : Nat → VNestedOcc} {b : VIndType → VExpr}
    (Cfg : RestrictStepCfg D R K env e₂ e₁ occ) (H₂ : D.ArgsTypedK K e₂ occ)
    (hb : D.ResultSortInhab env b)
    (hbridge : ∀ (j : Nat) (T : VIndType) (C : VIndCtor), D.types[j]? = some T →
      T.name ∉ K → C ∈ T.ctors →
      ∃ v : VLevel,
        e₁.TeleDefEq D.uvars []
          (((C.params ++ C.fields.map (·.type)).map (VExpr.substC · (R.csubstTy D K))))
          ((C.params ++ C.fieldTypesR D R).map (VExpr.substC · (R.csubstTy D K))) ∧
        e₁.IsDefEq D.uvars
          (((C.params ++ C.fields.map (·.type)).map (VExpr.substC · (R.csubstTy D K))).reverse)
          ((C.canonResult D j).substC (R.csubstTy D K))
          ((D.tyAppR R j C.fields.length C.args).substC (R.csubstTy D K)) (.sort v)) :
    ∀ c ∈ D.ctorConstsCR R K, VConstant.WF e₁ c.2 :=
  VEnv.ctorConstsCR_wf_of_substC' Cfg.wf Cfg.stage₂ Cfg.ordered₂ Cfg.ordered₁
    (VIndRestore.csubstTy_WF_of_resultSortInhab Cfg H₂ hb) hbridge

/-! ## §2 (B) and (C): the composition FAILS, and exactly where

Obligations (B) and (C) go through
`VEnv.recConstsR_wf_of_blocksD` / `_of_entriesD` (`Theory/Inductive/NestedTele.lean`) and
`VEnv.iotaRulesRS_wf_of_hargsD` (ditto), whose shared premise is

    hσ : (R.csubst D K).WFD E₂ e₃ D.recUvars

`FlipConstruct.lean` §10 records this premise's `val` field as `VIndRestore.ValAt`.  **That is
true of its type-constant entries and of nothing else**, and the difference is not a technicality:
it is the point at which the strengthening family stops.

`VIndRestore.csubstList` (`Theory/Inductive/Restore.lean`) contributes **three kinds** of entry per
companion member `j`, and `csubst_dom` (`Theory/Inductive/NestedRules.lean`) is that three-way
disjunction:

* `T.name ↦ R.tyVal D j` — the member's **type constant**.  Declared type `T.type`, which
  `VIndType.WF.canon` presents as `mkPi (D.params ++ T.indices) (.sort D.lvl)`.  **This is the
  family's entry**, and §1 uses it.
* `mkRecName T.name ↦ R.recVal D _` — the member's **recursor**.
* `C.name ↦ R.ctorVal D j C`, one per companion **constructor**.

`R.csubstTy D K` has only the first kind (`csubstTy_dom`), and the whole of RestrictStep's
five-node cycle — `ValAt`, `ValStrengthen`, `SpineHargsK`, `ArgsTypedK` — quantifies over
`R.csubstTy D K`'s domain.  So the family is **silent**, not weak, at the other two kinds: the
judgements it moves are not indexed by those names at all. -/

namespace VIndRestore
variable {R : VIndRestore} {D : VInductDecl'} {K : List Name}

/-- `csubstTy`'s domain sits inside `csubst`'s, at the same value. -/
theorem csubstTy_le_csubst (hnd : R.DomNodup D K) {n : Name} {t : VExpr}
    (h : R.csubstTy D K n = some t) : R.csubst D K n = some t := by
  obtain ⟨j, T, hT, rfl, hK, rfl⟩ := csubstTy_dom h
  exact csubst_ty_eq_some hnd hT hK

/-- **AND THE INCLUSION IS STRICT AT EVERY COMPANION CONSTRUCTOR.**  `csubst` has an entry there,
`csubstTy` has none — so `ValAt`/`ValStrengthen`, being `∀` over `csubstTy`'s domain, say nothing
about it.  The separation hypothesis is `D.allNames.Nodup`, which is not an extra assumption: it
is what `VEnv.addConstList D.allConsts` already requires of any addable block. -/
theorem csubst_ctor_off_csubstTy (hnd0 : D.allNames.Nodup) (hnd : R.DomNodup D K)
    {j : Nat} {T : VIndType} (hT : D.types[j]? = some T) (hK : T.name ∈ K)
    {C : VIndCtor} (hC : C ∈ T.ctors) :
    R.csubstTy D K C.name = none ∧ R.csubst D K C.name = some (R.ctorVal D j C) := by
  refine ⟨?_, csubst_ctor_eq_some hnd hT hK hC⟩
  by_contra hne
  have hmem := csubstTy_dom_blockNames (D := D) (K := K) hne
  rw [VInductDecl'.allConsts_names] at hnd0
  have hdis := (List.nodup_append.1 (List.nodup_append.1 hnd0).1).2.2
  refine hdis C.name hmem C.name ?_ rfl
  rw [D.ctorConsts_names, List.mem_map]
  exact ⟨(j, C), VInductDecl'.mem_ctorsAll_of hT hC, rfl⟩

/-- **…and at every companion recursor.**  Same separation, the third block of `allNames`. -/
theorem csubst_rec_off_csubstTy (hnd0 : D.allNames.Nodup) (hnd : R.DomNodup D K)
    {j : Nat} {T : VIndType} (hT : D.types[j]? = some T) (hK : T.name ∈ K) :
    R.csubstTy D K (Lean.mkRecName T.name) = none ∧
      R.csubst D K (Lean.mkRecName T.name)
        = some (R.recVal D (Lean.mkRecName T.name)) := by
  refine ⟨?_, csubst_rec_eq_some hnd hT hK⟩
  by_contra hne
  have hmem := csubstTy_dom_blockNames (D := D) (K := K) hne
  rw [VInductDecl'.allConsts_names] at hnd0
  have hdis := (List.nodup_append.1 hnd0).2.2
  refine hdis (Lean.mkRecName T.name) (List.mem_append_left _ hmem)
    (Lean.mkRecName T.name) ?_ rfl
  rw [D.recConsts_names, List.mem_map]
  exact ⟨T, List.mem_of_getElem? hT, rfl⟩

/-! ### §2a The residue, named rather than hidden

The split is *clean*: `csubst`'s `val` clause is the family's clause on `csubstTy`'s domain plus
`ValRestC` off it, and nothing else.  So (B)/(C)'s `hσ.val` is not "the family" — it is "the
family **and** `ValRestC`", and `ValRestC` is where the companion constructors' and recursor's own
typings live.  Those are `Faithful`-flavoured facts about the *intended* restoration values, and
the family's engine cannot reach them: the family works by substituting a **junk inhabitant** for a
dropped constant (`StrengthenFamily.lean` §2, `ntree_junkVal_ne_tyVal`), whereas `WFD.val` pins the
value to `R.ctorVal`/`R.recVal` and there is no freedom to replace it. -/

/-- **THE RESIDUE.**  The `val` clause of `(R.csubst D K).WFD`, restricted to the entries
`csubstTy` does not have — i.e. the companion constructors and the companion recursor. -/
def ValRestC (R : VIndRestore) (D : VInductDecl') (K : List Name) (E F : VEnv) : Prop :=
  ∀ {c : Name} {t : VExpr} {ci : VConstant}, R.csubstTy D K c = none →
    R.csubst D K c = some t → E.constants c = some ci →
    F.HasType ci.uvars [] t (ci.type.substC (R.csubst D K))

/-- **THE SPLIT.**  `csubst`'s `val` clause, in `HasType` form, is exactly the type-constant part
(which is `ValAt`-shaped, hence the family's) together with `ValRestC`.  This is the sharpest form
of "the family discharges one of the three kinds and is silent on the other two". -/
theorem csubst_val_of_valAtC_of_valRestC (hnd : R.DomNodup D K) {E F : VEnv}
    (hty : ∀ {c : Name} {t : VExpr} {ci : VConstant}, R.csubstTy D K c = some t →
      E.constants c = some ci → F.HasType ci.uvars [] t (ci.type.substC (R.csubst D K)))
    (hrest : R.ValRestC D K E F) {c : Name} {t : VExpr} {ci : VConstant}
    (hs : R.csubst D K c = some t) (hc : E.constants c = some ci) :
    F.HasType ci.uvars [] t (ci.type.substC (R.csubst D K)) := by
  cases hd : R.csubstTy D K c with
  | none => exact hrest hd hs hc
  | some t' =>
    rw [csubstTy_le_csubst hnd hd] at hs
    cases hs
    exact hty hd hc

/-- **…AND WITH THE FAMILY'S OWN NODE PLUGGED IN.**  `ValAt` is exactly the type-constant part
once the declared type is seen to be `csubst`-free — a freshness fact, since `csubst_dom` puts the
whole domain inside the block's own name families while a member's stored type mentions only
pre-block constants (`VInductDecl'.WF.types_constsIn`).  So:

    (B)/(C)'s `hσ.val`  =  the family's node  ∧  `ValRestC`

and `ValRestC` is the whole of what the family does not give.

Two caveats stated rather than buried.  (i) The `ValAt` wanted here is at the **ctor-stage** pair
`(E₂, F₂)`, one `addConstList` above the pair `(e₂, e₁)` the cycle runs at; moving it up is a small
source-environment monotonicity step that this tree does not have written down, and it is *not*
supplied here.  (ii) `val` is only one of `WFD`'s four clauses; `const` at `np ≥ 1` still needs the
per-constructor defeq disjunct (`ntree_node_const_defeq` is the `ntreeAux` instance), which is (A)'s
`hbridge` phenomenon at the next stage and is likewise untouched by the family. -/
theorem csubst_val_of_valAt_of_valRestC (hnd : R.DomNodup D K) {E F : VEnv}
    (hval : R.ValAt D K E F)
    (hclean : ∀ {c : Name} {ci : VConstant}, R.csubstTy D K c ≠ none →
      E.constants c = some ci → ci.type.NoCSubst (R.csubst D K))
    (hrest : R.ValRestC D K E F) {c : Name} {t : VExpr} {ci : VConstant}
    (hs : R.csubst D K c = some t) (hc : E.constants c = some ci) :
    F.HasType ci.uvars [] t (ci.type.substC (R.csubst D K)) :=
  csubst_val_of_valAtC_of_valRestC hnd
    (fun {_ _ _} hd hc => by
      rw [(hclean (by rw [hd]; exact nofun) hc).substC_eq]; exact hval hd hc)
    hrest hs hc

end VIndRestore

/-! ## §3 The level side condition, checked — item (d) of the brief

**For (A) / the family the level is the block's own, and there is no companion mismatch.**  This is
structural, not incidental: `lvl` and `params` are fields of `VInductDecl'`, **not** of `VIndType`.
`VIndType.WF.canon` presents *every* member's stored type — declared members and companion members
alike — as `mkPi (D.params ++ T.indices) (.sort D.lvl)` with the *same* `D.lvl`.  So
`VInductDecl'.ResultSortInhab` asks for a term of type `Sort D.lvl` over each member's own
telescope, and `resultSortInhab_of_succ` discharges it from `D.lvl ≈ .succ v` uniformly in the
member.  There is no per-member level for the condition to be evaluated at the wrong one.

`ntreeAux.lvl = .succ (.param 0)`, `ntreeAux.uvars = 1`, so §4's clause fires by `decide`.

**For (B)/(C) the mismatch is real, and it is not a level mismatch — it is a *type* mismatch, one
kind worse.**  §2's extra entries are not at a sort at all: a companion constructor's declared type
ends in `D.tyApp` (an application of the member type constant) and the companion recursor's ends in
the motive applied to the major premise.  So there is nothing for a `Sort`-inhabitation clause to
say about them, at any level.

**One thing that is NOT an additional obstacle, recorded so nobody re-reports it.**  `WFD` for
(B)/(C) is at `D.recUvars`, while the whole cycle is at `D.uvars`, and these differ
(`ntreeAux`: `2` vs `1`).  For the `val` clause this costs nothing — `CSubst.val_of_hasType`
(`Theory/Typing/ConstSubst.lean`) absorbs the level quantifier entirely, taking a plain
`HasType ci.uvars []` and producing the `∀ Γ ls ls'` form at *any* `U`.  Where `D.recUvars`
does bite is the **`const`** clause's defeq disjunct, whose `∀ ls, (∀ l ∈ ls, l.WF U)` ranges over
more level lists at a larger `U`; that is a strengthening of `const`, not of `val`. -/

/-- **THE LEVEL IS THE BLOCK'S, NOT THE MEMBER'S.**  `rfl`, so the claim above cannot drift: the
canonical type a companion member is inhabited *at* takes `params` and `lvl` from `D` and only
`indices` from `T`.  This is why `ResultSortInhab`'s three discharge clauses are uniform in the
member and why no companion-level side condition exists to be silently assumed. -/
theorem VIndType.canonType_eq (T : VIndType) (D : VInductDecl') :
    T.canonType D = VExpr.mkPi (D.params ++ T.indices) (.sort D.lvl) := rfl

/-! ## §4 The witnesses at `ntreeAux`, arity 0

`ntreeAux`: `NTree α` with a `List (NTree α)` field, `uvars = 1`, `params = [.sort (.succ
(.param 0))]`, `lvl = .succ (.param 0)`, the block Lean's own kernel runs the nested elimination
on (`Theory/Inductive/NestedHead.lean`).  Deliberately **not** `nfnAux`, which has `uvars = 0` and
`params = []` and would make both §3's level clause and the parameter telescope invisible.

No `VEnv.HasArgs.of_mkApp` anywhere below. -/

namespace InductiveDeclExamples

/-- The level facts §3 asserts, at the witness. -/
theorem ntreeAux_level_data :
    ntreeAux.uvars = 1 ∧ ntreeAux.recUvars = 2 ∧ ntreeAux.lvl = .succ (.param 0) := by decide

/-- **THE COMPANION MEMBER SITS AT THE SAME RESULT LEVEL AS THE DECLARED ONE** — `decide`, at both
members of `ntreeAux.types`, `_nested.List_1` included.  This is item (d) of the brief checked at
the witness rather than argued: there is no companion whose level differs, so nothing is being
quietly discharged. -/
theorem ntreeAux_canon_lvl_uniform : ∀ T ∈ ntreeAux.types,
    T.canonType ntreeAux
      = VExpr.mkPi (ntreeAux.params ++ T.indices) (.sort (.succ (.param 0))) := by decide

/-- **THE THREE KINDS OF `csubst` ENTRY, EXHIBITED, AND THE TWO `csubstTy` MISSES.**  `decide`,
so this is not read off a docstring: the companion's constructors and recursor are in `csubst`'s
domain and **absent** from `csubstTy`'s, which is why the cycle cannot see them. -/
theorem ntree_csubst_off_csubstTy :
    ntreeRestore.csubstTy ntreeAux ntreeK `_nested.List_1
        = some (ntreeRestore.tyVal ntreeAux 1) ∧
      ntreeRestore.csubstTy ntreeAux ntreeK `_nested.List_1.nil = none ∧
      ntreeRestore.csubstTy ntreeAux ntreeK `_nested.List_1.cons = none ∧
      ntreeRestore.csubstTy ntreeAux ntreeK (Lean.mkRecName `_nested.List_1) = none ∧
      ntreeRestore.csubst ntreeAux ntreeK `_nested.List_1.nil ≠ none ∧
      ntreeRestore.csubst ntreeAux ntreeK `_nested.List_1.cons ≠ none ∧
      ntreeRestore.csubst ntreeAux ntreeK (Lean.mkRecName `_nested.List_1) ≠ none := by
  decide

/-! ### §4a Obligation (A) at `ntreeAux`, **routed through the family**

`ntreeAux_obligationA` (`Theory/Typing/ConstSubstNested.lean:1013`, arity 0, cone 3594) already
exists, but its `hσ` comes from `ntreeSubst_WF` — a block-specific `type_tac` on the concrete spine.
This is the same conclusion with `hσ` supplied by §1, i.e. by the *general* strengthening family
from the block's result level alone.  `hbridge` is the one thing that stays, and it is the single
parameter β-step (`VEnv.IsDefEq.beta`), exhibited rather than assumed.

The two hypotheses of the general theorem are closed off existentially here, so this is an
inhabitation check in the sense `docs/vacuity-ledger.md` §0 asks for, not a reduction. -/

/-- **THE WITNESS.**  Arity 0: the staging, the configuration, the datum at `e₂`, the result-level
inhabitation, the substitution's `WF` **from the family**, and obligation (A) — all at the
parameterised nested block, with nothing hypothesised. -/
theorem ntreeAux_obligationA_via_family :
    ∃ env₁ env₂ env₃ : VEnv,
      VEnv.empty.addInduct' listDecl = some env₁ ∧
      env₁.addIndTypes ntreeAux = some env₂ ∧
      env₁.addConstList (ntreeAux.typeConstsC ntreeK) = some env₃ ∧
      RestrictStepCfg ntreeAux ntreeRestore ntreeK env₁ env₂ env₃ (fun _ => listOcc) ∧
      ntreeAux.ArgsTypedK ntreeK env₂ (fun _ => listOcc) ∧
      ntreeAux.ResultSortInhab env₁ ntreeJunk ∧
      (ntreeRestore.csubstTy ntreeAux ntreeK).WF env₂ env₃ ntreeAux.uvars ∧
      ∀ c ∈ ntreeAux.ctorConstsCR ntreeRestore ntreeK, VConstant.WF env₃ c.2 := by
  obtain ⟨env₁, env₂, -, env₃, -, h, h₂, -, h₃, -⟩ := ntree_stage₂_exists
  have Cfg := ntreeAux_restrictStepCfg h h₂ h₃
  have H₂ := ntreeAux_argsTypedK_of_wf (env₁ := env₁) h₂
  refine ⟨env₁, env₂, env₃, h, h₂, h₃, Cfg, H₂, ntreeAux_resultSortInhab,
    VIndRestore.csubstTy_WF_of_resultSortInhab Cfg H₂ ntreeAux_resultSortInhab,
    VEnv.ctorConstsCR_wf_of_resultSortInhab Cfg H₂ ntreeAux_resultSortInhab ?_⟩
  have hL := list_const₃ h h₃
  have hN := ntree_const₃ h₃
  rintro j T C hT hK hC
  match j, hT with
  | 0, hT =>
    cases hT
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
    subst hC
    rw [ntree_csubstTy]
    refine ⟨.succ (.param 0), .rfl (.rfl (.cons (u := .succ (.param 0)) ?_ .nil)),
      by type_tac⟩
    refine VEnv.IsDefEq.beta (A := .sort (.succ (.param 0))) (B := .sort (.succ (.param 0)))
      ?_ ?_ <;> type_tac
  | 1, hT =>
    cases hT
    exact absurd (by decide) hK
  | (_ + 2), hT => simp [ntreeAux] at hT

/-- …and the same conclusion stripped to the shape `ntreeAux_obligationA` has, so the two are
directly comparable: same statement, `hσ` now general. -/
theorem ntreeAux_obligationA' :
    ∃ env₁ env₂ env₃ : VEnv, VEnv.empty.addInduct' listDecl = some env₁ ∧
      env₁.addIndTypes ntreeAux = some env₂ ∧
      env₁.addConstList (ntreeAux.typeConstsC ntreeK) = some env₃ ∧
      ∀ c ∈ ntreeAux.ctorConstsCR ntreeRestore ntreeK, VConstant.WF env₃ c.2 := by
  obtain ⟨env₁, env₂, env₃, h, h₂, h₃, -, -, -, -, hA⟩ := ntreeAux_obligationA_via_family
  exact ⟨env₁, env₂, env₃, h, h₂, h₃, hA⟩

end InductiveDeclExamples

end Lean4Lean

/-! ## §6 What the flip needs after this round — item (c)

`FlipConstruct.lean` isolated the residual of `AddInduct`'s constructor as *exactly* the three
obligations of `VEnv.addInductR_ordered'` (`AddInductN.ordered_of_obligations`: the payload supplies
`D.WF env₁`, `R.OwnId D K` and the `addInductR` equation from inside itself).  After this file the
three stand as follows.

| | obligation | general route | premise status after §1/§2 |
|---|---|---|---|
| (A) | restored **constructor** types `VConstant.WF` at stage 1 | `ctorConstsCR_wf_of_substC'` | `hσ` **discharged** by the family at successor/zero result level (§1); **`hbridge` remains** |
| (B) | renamed **recursor** types `VConstant.WF` at stage 2 | `recConstsR_wf_of_blocksD` / `_of_entriesD` | `hσ.val` = family part **∧ `ValRestC`**; `ValRestC` and `hσ.const` remain (§2) |
| (C) | restored **ι-rules** `VDefEq.WF` at stage 3 | `iotaRulesRS_wf_of_hargsD` | same `hσ`, same residue; plus `IotaHargs` per rule |

So the honest statement of what the flip now needs, in the form the brief asked for:

> **The constructor for `AddInduct`'s replacement is available at every block whose result level is
> `≈`-a-successor or `≈`-zero — obligation (A) included, with only `hbridge` left there — provided
> obligations (B) and (C) are supplied.  Those two are *not* reduced to the strengthening family:
> their residue is `VIndRestore.ValRestC` (the companion constructors' and recursor's own value
> typings) together with the defeq disjunct of `CSubst.WFD.const` at every declared constructor.**

**Which of the project's thirteen holes the composed result routes through: none.**  Measured, not
asserted — `scripts/exists.lean` on every declaration of this file reports
`cone reaches sorryAx: false`, and §5's `#print axioms` lines show `propext`, `Quot.sound` and (for
the `Classical.choice`-using witnesses) nothing further.  In particular `VEnv.StrengtheningTarget` /
`VEnv.AxiomConservativityWF` — the hole `RestrictStep.lean` §2 located the cycle's only entry on —
is **not** in the cone of §1: the family replaced it (`StrengthenFamily.lean` §8).

**What is NOT claimed.**  (i) That (B)/(C) are close: §2 measures a gap, it does not narrow one.
(ii) That `ValRestC` is hard — it is ordinary content about the intended restoration values, proved
concretely at `ntreeAux` inside `ntree_csubst_WFD₂`/`WFD₃`; what §2 shows is that the *family* is
not the tool for it.  (iii) Anything about the `ValAt` monotonicity step between the type stage and
the ctor stage (§2a caveat (i)); it is named and left open.  (iv) Anything about the flip's own
edits to `Verify/Environment/Basic.lean` and `Theory/Typing/Env.lean`, which this file does not
touch. -/

/-! ## §5 Axiom audit, per declaration -/

#print axioms Lean4Lean.VIndRestore.valAt_of_resultSortInhab
#print axioms Lean4Lean.VIndRestore.csubstTy_WF_of_resultSortInhab
#print axioms Lean4Lean.VEnv.ctorConstsCR_wf_of_resultSortInhab
#print axioms Lean4Lean.VIndRestore.csubstTy_le_csubst
#print axioms Lean4Lean.VIndRestore.csubst_ctor_off_csubstTy
#print axioms Lean4Lean.VIndRestore.csubst_rec_off_csubstTy
#print axioms Lean4Lean.VIndRestore.csubst_val_of_valAtC_of_valRestC
#print axioms Lean4Lean.VIndRestore.csubst_val_of_valAt_of_valRestC
#print axioms Lean4Lean.VIndType.canonType_eq
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_level_data
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_canon_lvl_uniform
#print axioms Lean4Lean.InductiveDeclExamples.ntree_csubst_off_csubstTy
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_obligationA_via_family
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_obligationA'
