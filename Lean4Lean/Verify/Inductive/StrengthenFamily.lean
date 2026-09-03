import Lean4Lean.Verify.Inductive.RestrictStep
import Lean4Lean.Theory.Typing.WeakNForward

/-!
# The `ValStrengthen` instance family: strictly cheaper than the hole, and why

`Verify/Inductive/RestrictStep.lean` reduced the nested restriction step to one judgement,

    restrictStep_entry : D.ArgsTypedK K e₁ occ  ↔  R.ValStrengthen D K e₂ e₁

and located `VIndRestore.ValStrengthen` as a *plain instance* of `VEnv.AxiomConservativityWF`
(`Theory/Typing/ConstVar.lean`), which is provably equivalent to `VEnv.StrengtheningTarget`, one
of `Theory/Typing/UniqueTyping.lean`'s thirteen holes.  It left open the question this file
answers: **is the instance family strictly weaker than the general statement?**

**It is, and the separation is sharp.**  `ConstVar.lean` proves
`axiomConservativityWF_iff_uninhabWF`: the general statement is *equivalent* to its restriction
to axioms with **no inhabitant**, so all of the hole's content sits in the uninhabited case.
The constants `ValStrengthen` must drop are inductive members' type constants — definitionally
`Π params indices, Sort D.lvl` — and §2 shows that as soon as those types are inhabited at `e₁`
by *any* closed term, the family follows by constant substitution, with no hole and no `PiInv`.
The intended value `R.tyVal D j` is *not* needed as the substituted value: that is the mistake
that made the corner look circular (`RestrictCompanion.lean` §3's sandwich is about the intended
value only).

Contents:

* §0 the family as its own definition, and its general parent for this pair of environments;
* §1 the family **from** the general statement — the direction that pins the ordering, with its
  two prices named (uniqueness of types at `e₂`, and presenting `e₂` as an `addConst` chain);
* §2 the junk substitution: adding constants whose declared types are inhabited at the smaller
  environment is conservative for closed judgements with clean endpoints.  Hole-free,
  `PiInv`-free, `substC` only;
* §3 the family, and hence node 1 of RestrictStep's cycle, from inhabitation;
* §4 discharging inhabitation from the block's result **level** alone;
* §5 the parameterised nested witness `ntreeAux`: everything instantiated, nothing hypothesised,
  and the junk value exhibited *different* from `ntreeVal`;
* §6 the parameterised nested witness, and the junk value exhibited *different* from `ntreeVal`;
* §8 the verdict, and what is left.

**Headline.**  `VIndRestore.argsTypedK_of_succLevel` is hole-free: for every block whose result
level is `≈`-a-successor (which is every non-`Prop` block Lean emits, `ntreeAux` included), the
nested restriction step closes **without** `Theory/Typing/UniqueTyping.lean`'s strengthening
`sorry`.  §8 states this as the bypass it is, and states equally plainly what it does not cover.
-/

namespace Lean4Lean

open Lean (Name)
open VExpr (mkLams mkPi)

/-! ## §0 The family, and its general parent

`ValStrengthen` as RestrictStep.lean uses it is an *instance*: empty context, one
`addConstList`, one closed `HasType` per companion member.  Quantifying over every
configuration turns that instance into a family, which is the object to compare with
`VEnv.AxiomConservativityWF`. -/

/-- **THE INSTANCE FAMILY.**  `VIndRestore.ValStrengthen`, at every configuration RestrictStep's
cycle can be run at.  This is the statement whose strength is measured here. -/
def VIndRestore.StrengthenFamily : Prop :=
  ∀ {D : VInductDecl'} {R : VIndRestore} {K : List Name} {env e₂ e₁ : VEnv}
    {occ : Nat → VNestedOcc}, RestrictStepCfg D R K env e₂ e₁ occ →
    D.ArgsTypedK K e₂ occ → R.ValStrengthen D K e₂ e₁

/-- **The family's general parent, for one pair of environments.**  Closed, typed
conservativity: a typing over the larger environment whose subject and type mention only
constants the smaller one declares holds over the smaller one.  `ValStrengthen` is exactly this
statement's instance at the companion values (§1). -/
def VEnv.ClosedConservativeStep (e₂ e₁ : VEnv) (U : Nat) : Prop :=
  ∀ {t A : VExpr}, t.ConstsIn e₁.contains → A.ConstsIn e₁.contains →
    e₂.HasType U [] t A → e₁.HasType U [] t A

/-- Conservativity composes along a `≤`-chain: cleanliness at the bottom implies cleanliness in
the middle, so the two steps chain with nothing extra. -/
theorem VEnv.ClosedConservativeStep.comp {e₁ e₂ e₃ : VEnv} {U : Nat} (hle : e₁ ≤ e₂)
    (h1 : e₃.ClosedConservativeStep e₂ U) (h2 : e₂.ClosedConservativeStep e₁ U) :
    e₃.ClosedConservativeStep e₁ U := fun ht hA h =>
  h2 ht hA (h1 (ht.mono fun _ hh => hle.contains hh) (hA.mono fun _ hh => hle.contains hh) h)

namespace RestrictStepCfg

variable {D : VInductDecl'} {R : VIndRestore} {K : List Name} {env e₂ e₁ : VEnv}
  {occ : Nat → VNestedOcc}

/-- **The shape of the judgement the family moves.**  `RestrictStep.lean`'s
`valStrengthen_endpoints_clean` opens with this inversion; it is factored out here because §1
needs the universe count and §2 needs the member. -/
theorem constant_of_csubstTy (C : RestrictStepCfg D R K env e₂ e₁ occ) {c : Name} {t : VExpr}
    {ci : VConstant} (hd : R.csubstTy D K c = some t) (hc : e₂.constants c = some ci) :
    ∃ (j : Nat) (T : VIndType), D.types[j]? = some T ∧ T.name = c ∧ T.name ∈ K ∧
      t = R.tyVal D j ∧ ci = ⟨D.uvars, T.type⟩ := by
  obtain ⟨j, T, hT, rfl, hK, rfl⟩ := VIndRestore.csubstTy_dom hd
  have hmem : (T.name, (⟨D.uvars, T.type⟩ : VConstant)) ∈ D.typeConsts :=
    List.mem_map.2 ⟨T, List.mem_of_getElem? hT, rfl⟩
  have h₂ := C.stage₂
  rw [VEnv.addIndTypes] at h₂
  rw [VEnv.addConstList_constants h₂ _ hmem] at hc
  cases hc
  exact ⟨j, T, hT, rfl, hK, rfl, rfl⟩

end RestrictStepCfg

/-! ## §1 The family from the general statement

The easy direction, and the one that pins the ordering: no node of RestrictStep's cycle is
*harder* than the hole.  Two prices are named rather than hidden.

* **The typed form costs uniqueness of types at `e₂`.**  `AxiomConservativityWF` is a statement
  about `IsDefEqU` — it loses the type — so recovering `HasType` needs `IsDefEq.uniqU` at the
  larger environment, i.e. `VEnv.WF e₂`.  That is `RestrictCompanion.lean`'s
  `IsDefEq.restrict_of_conservativity`, used verbatim below.
* **`e₂` must be presented as an `addConst` chain above `e₁`.**  `e₁ ≤ e₂` is proved
  (`VEnv.addIndTypesC_le_addIndTypes`), but the two are `addConstList`s of `D.typeConstsC K` and
  `D.typeConsts` over the *same* `env`, and the second is an interleaving of the first with the
  companion entries, not an append.  So the chain needs a reordering lemma for `addConstList`
  that this tree does not have; `ClosedConservativeStep.comp` is the composition step it would
  feed.  Nothing below hides this: §1's instance is stated for **one** added constant. -/

/-- **One added constant: the general statement gives closed conservativity.** -/
theorem VEnv.closedConservativeStep_of_axiomConservativityWF {e₁ e₂ : VEnv} {U : Nat} {c : Name}
    {ci : VConstant} (henv : VEnv.WF e₁) (henv' : VEnv.WF e₂)
    (H : e₁.AxiomConservativityWF U) (hadd : e₁.addConst c ci = some e₂) (hci : ci.WF e₁)
    (hu : ci.uvars = U) : e₂.ClosedConservativeStep e₁ U := fun ht hA h =>
  VEnv.IsDefEq.restrict_of_conservativity henv henv' H hadd hci hu trivial ht ht hA h

/-- **The family from closed conservativity.**  `RestrictStep.lean`'s
`valStrengthen_endpoints_clean` discharges the side condition, so this is a plain instantiation
— which is the content of "`ValStrengthen` is an *instance*". -/
theorem VIndRestore.valStrengthen_of_closedStep {D : VInductDecl'} {R : VIndRestore}
    {K : List Name} {env e₂ e₁ : VEnv} {occ : Nat → VNestedOcc}
    (C : RestrictStepCfg D R K env e₂ e₁ occ) (H₂ : D.ArgsTypedK K e₂ occ)
    (H : e₂.ClosedConservativeStep e₁ D.uvars) : R.ValStrengthen D K e₂ e₁ := by
  intro c t ci hd hc hty
  obtain ⟨h1, h2⟩ := VIndRestore.valStrengthen_endpoints_clean C H₂ hd hc
  have hu : ci.uvars = D.uvars := by
    obtain ⟨-, -, -, -, -, -, rfl⟩ := C.constant_of_csubstTy hd hc; rfl
  rw [hu] at hty ⊢
  exact H h1 h2 hty

/-! ## §2 The junk substitution: an inhabited axiom is conservative

The general statement's content is entirely in the **uninhabited** case — `ConstVar.lean` proves
`axiomConservativityWF_iff_uninhabWF`, so restricting the residual to axioms with no inhabitant
loses nothing.  This section runs the *other* case, which is not a hole at all: if each dropped
constant's declared type is inhabited at `e₁`, replace the constant by an inhabitant.
`VEnv.IsDefEq.substC` transports the derivation, and endpoints that never mention the dropped
constants come through unchanged (`VEnv.HasType.restrictC`, `RestrictCompanion.lean` §1).

**The value need not be the intended one.**  `RestrictCompanion.lean` §3's sandwich says the
substitution `R.csubstTy D K` — whose value at a companion member is `R.tyVal D j` — has, as its
own hypothesis, the clause the datum would produce.  That is a fact about *that* substitution.
For conservativity any inhabitant will do, and the one §4 builds is a λ-telescope of sorts with
no member constant in it.  `PiInv`-free and `of_mkApp`-free throughout: the only transport used
is `substC`. -/

/-- Inverting `addConstList` at one name: a constant of the extended environment either comes
from the list or was already there. -/
theorem VEnv.addConstList_constants_inv {cs : List (Name × VConstant)} {env env' : VEnv}
    {c : Name} {ci : VConstant} (h : env.addConstList cs = some env')
    (hc : env'.constants c = some ci) : (c, ci) ∈ cs ∨ env.constants c = some ci := by
  by_cases hm : c ∈ cs.map (·.1)
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hm
    rw [VEnv.addConstList_constants h p hp] at hc
    cases hc; exact .inl hp
  · exact .inr (by rw [← VEnv.addConstList_constants_of_not_mem h hm]; exact hc)

/-- A companion name is not among the names `addIndTypesC` declares — that is what the filter in
`typeConstsC` is for. -/
theorem VInductDecl'.not_mem_typeConstsC_names {D : VInductDecl'} {K : List Name} {n : Name}
    (h : n ∈ K) : n ∉ (D.typeConstsC K).map (·.1) := by
  intro hm
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hm
  rw [VInductDecl'.typeConstsC, List.mem_filterMap] at hp
  obtain ⟨a, -, he⟩ := hp
  by_cases hK : a.1 ∈ K
  · rw [if_pos hK] at he; exact absurd he nofun
  · rw [if_neg hK] at he; cases he; exact hK h

/-- **The junk-value data.**  A constant substitution whose domain sits inside the companion
list, which covers every companion member, and whose values inhabit the declared types **at
`e₁`**.  Nothing here asks the value to be the *intended* one (`R.tyVal D j`), and that is the
whole point of §2. -/
structure VInductDecl'.CompanionVals (D : VInductDecl') (K : List Name) (e₂ e₁ : VEnv)
    (σ : CSubst) : Prop where
  /-- The values are closed (`substC` needs it under binders). -/
  closed : σ.Closed
  /-- Nothing outside the companion list is touched. -/
  dom : ∀ {c : Name}, σ c ≠ none → c ∈ K
  /-- Every companion member *is* touched. -/
  covers : ∀ {T : VIndType}, T ∈ D.types → T.name ∈ K → σ T.name ≠ none
  /-- …and the value inhabits the declared type at the smaller environment. -/
  val : ∀ {c : Name} {s : VExpr} {ci : VConstant}, σ c = some s → e₂.constants c = some ci →
    e₁.HasType ci.uvars [] s ci.type

namespace RestrictStepCfg

variable {D : VInductDecl'} {R : VIndRestore} {K : List Name} {env e₂ e₁ : VEnv}
  {occ : Nat → VNestedOcc} {σ : CSubst}

/-- A companion name is undeclared in the pre-block environment (`Built.kfresh.notContains`). -/
theorem constants_eq_none_of_mem_K (C : RestrictStepCfg D R K env e₂ e₁ occ) {c : Name}
    (hK : c ∈ K) : env.constants c = none := by
  cases h : env.constants c with
  | none => rfl
  | some ci => exact absurd ⟨ci, h⟩ (C.built.kfresh.notContains c hK)

/-- …hence a domain inside `K` is fresh in the pre-block environment. -/
theorem freshIn_env (C : RestrictStepCfg D R K env e₂ e₁ occ)
    (hdom : ∀ {c : Name}, σ c ≠ none → c ∈ K) : σ.FreshIn env := by
  intro c ci hc
  cases h : σ c with
  | none => rfl
  | some s =>
    rw [C.constants_eq_none_of_mem_K (hdom (by rw [h]; exact nofun))] at hc
    exact absurd hc nofun

/-- …and in `e₁`, which declares only the **non**-companion members on top of it. -/
theorem freshIn₁ (C : RestrictStepCfg D R K env e₂ e₁ occ)
    (hdom : ∀ {c : Name}, σ c ≠ none → c ∈ K) : σ.FreshIn e₁ := by
  intro c ci hc
  cases h : σ c with
  | none => rfl
  | some s =>
    have hK := hdom (show σ c ≠ none by rw [h]; exact nofun)
    have h₁ := C.stage₁
    rw [VEnv.addIndTypesC] at h₁
    rw [VEnv.addConstList_constants_of_not_mem h₁
        (VInductDecl'.not_mem_typeConstsC_names (D := D) hK),
      C.constants_eq_none_of_mem_K hK] at hc
    exact absurd hc nofun

/-- Every type declared at `e₂` mentions only pre-block constants, hence is untouched by a
substitution whose domain is a companion list. -/
theorem constType_noCSubst (C : RestrictStepCfg D R K env e₂ e₁ occ)
    (hdom : ∀ {c : Name}, σ c ≠ none → c ∈ K) {c : Name} {ci : VConstant}
    (hc : e₂.constants c = some ci) : ci.type.NoCSubst σ := by
  have hfe := C.freshIn_env hdom
  have h₂ := C.stage₂
  rw [VEnv.addIndTypes] at h₂
  rcases VEnv.addConstList_constants_inv h₂ hc with hm | hm
  · obtain ⟨T, hT, he⟩ := List.mem_map.1 hm
    cases he
    exact (C.wf.types_constsIn C.ordered T hT).noCSubst hfe
  · exact C.ordered.noCSubstC hfe hm

end RestrictStepCfg

/-- **THE SUBSTITUTION IS WELL FORMED.**  All four `CSubst.WF` fields, from the configuration and
the inhabitation data alone.  `CSubst.WF_of_hasType` absorbs the level quantifiers, so no level
condition on the values appears. -/
theorem VInductDecl'.CompanionVals.csubst_WF {D : VInductDecl'} {R : VIndRestore} {K : List Name}
    {env e₂ e₁ : VEnv} {occ : Nat → VNestedOcc} {σ : CSubst}
    (C : RestrictStepCfg D R K env e₂ e₁ occ) (hV : D.CompanionVals K e₂ e₁ σ) :
    σ.WF e₂ e₁ D.uvars := by
  have hfe := C.freshIn_env hV.dom
  refine CSubst.WF_of_hasType C.ordered₁ hV.closed (fun {c s ci} hd hc => ?_)
    (fun {c ci} hn hc => ?_) (fun {df} hdf => ?_)
  · rw [(C.constType_noCSubst hV.dom hc).substC_eq]; exact hV.val hd hc
  · rw [(C.constType_noCSubst hV.dom hc).substC_eq]
    have h₂ := C.stage₂
    rw [VEnv.addIndTypes] at h₂
    rcases VEnv.addConstList_constants_inv h₂ hc with hm | hm
    · obtain ⟨T, hT, he⟩ := List.mem_map.1 hm
      cases he
      have hK : T.name ∉ K := fun hK => hV.covers hT hK hn
      have h₁ := C.stage₁
      rw [VEnv.addIndTypesC] at h₁
      refine VEnv.addConstList_constants h₁ (T.name, ⟨D.uvars, T.type⟩) ?_
      rw [VInductDecl'.typeConstsC, List.mem_filterMap]
      exact ⟨_, List.mem_map.2 ⟨T, hT, rfl⟩, if_neg hK⟩
    · exact C.le₁.constants hm
  · have h₂ := C.stage₂
    rw [VEnv.addIndTypes] at h₂
    rw [VEnv.addConstList_defeqs h₂] at hdf
    rw [(C.ordered.noCSubstD hfe hdf).substC_eq]
    exact C.le₁.defeqs hdf

/-! ## §3 The family from inhabitation — and with it node 1 of the cycle -/

/-- **THE FAMILY, FROM INHABITATION.**  No strengthening hole: the only transport is `substC`. -/
theorem VIndRestore.valStrengthen_of_companionVals {D : VInductDecl'} {R : VIndRestore}
    {K : List Name} {env e₂ e₁ : VEnv} {occ : Nat → VNestedOcc} {σ : CSubst}
    (C : RestrictStepCfg D R K env e₂ e₁ occ) (H₂ : D.ArgsTypedK K e₂ occ)
    (hV : D.CompanionVals K e₂ e₁ σ) : R.ValStrengthen D K e₂ e₁ := by
  intro c t ci hd hc hty
  obtain ⟨h1, h2⟩ := VIndRestore.valStrengthen_endpoints_clean C H₂ hd hc
  have hf₁ := C.freshIn₁ hV.dom
  have hu : ci.uvars = D.uvars := by
    obtain ⟨-, -, -, -, -, -, rfl⟩ := C.constant_of_csubstTy hd hc; rfl
  rw [hu] at hty ⊢
  exact VEnv.HasType.restrictC (hV.csubst_WF C) (by simp) (h1.noCSubst hf₁) (h2.noCSubst hf₁) hty

/-- **…AND THE RESTRICTION STEP CLOSES.**  Through `restrictStep_entry`, inhabitation of the
companion members' declared types at `e₁` gives the datum at `e₁` — node 1 of RestrictStep's
five-node cycle, which is what the whole route wanted. -/
theorem VIndRestore.argsTypedK_of_companionVals {D : VInductDecl'} {R : VIndRestore}
    {K : List Name} {env e₂ e₁ : VEnv} {occ : Nat → VNestedOcc} {σ : CSubst}
    (C : RestrictStepCfg D R K env e₂ e₁ occ) (H₂ : D.ArgsTypedK K e₂ occ)
    (hV : D.CompanionVals K e₂ e₁ σ) : D.ArgsTypedK K e₁ occ :=
  (VIndRestore.restrictStep_entry C H₂).2 (valStrengthen_of_companionVals C H₂ hV)

/-! ## §4 Discharging inhabitation from the block's result level

A companion member's declared type is *definitionally* `Π params indices, Sort D.lvl`
(`VIndType.WF.canon`, and `VIndType.canonType` is that telescope on the nose).  So an inhabitant
is a λ-telescope over the same binders with a term of type `Sort D.lvl` inside — and when
`D.lvl ≈ .succ v` the term is `Sort v`.  No `PiInv`: the telescope is never inverted, it is
*read off* `canonType`, which is syntax.

This is where the honest limit of the route sits, and it is a limit about **levels**, not about
strengthening: for a `D.lvl` that is neither `≈ .zero` nor `≈ .succ _` — `.param i` is the
example — `Sort D.lvl` has no closed inhabitant, and the premise has to come from the telescope
instead (a parameter at exactly that level does it; see §6). -/

/-- **The one premise the whole route needs**: the block's result sort is inhabited over each
member's own telescope.  A condition on levels and on the parameter/index telescope — no
judgement about the occurrence spine, and no strengthening. -/
def VInductDecl'.ResultSortInhab (D : VInductDecl') (env : VEnv) (b : VIndType → VExpr) : Prop :=
  ∀ T ∈ D.types, env.HasType D.uvars (T.indices.reverse ++ D.params.reverse) (b T) (.sort D.lvl)

/-- The junk inhabitant of a member's canonical type: the canonical telescope, with the witness
of the result sort inside. -/
def VInductDecl'.junkVal (D : VInductDecl') (b : VIndType → VExpr) (T : VIndType) : VExpr :=
  mkLams (D.params ++ T.indices) (b T)

/-- The junk substitution's association list: one entry per companion member. -/
def VInductDecl'.junkList (D : VInductDecl') (K : List Name) (b : VIndType → VExpr) :
    List (Name × VExpr) :=
  (D.types.filter fun T => decide (T.name ∈ K)).map fun T => (T.name, D.junkVal b T)

/-- **The junk substitution.**  The same shape as `VIndRestore.csubstTy`, and deliberately
different values: no member constant occurs in them at all. -/
def VInductDecl'.junkSubst (D : VInductDecl') (K : List Name) (b : VIndType → VExpr) : CSubst :=
  fun n => (D.junkList K b).lookup n

theorem VInductDecl'.junkSubst_dom {D : VInductDecl'} {K : List Name} {b : VIndType → VExpr}
    {n : Name} {s : VExpr} (h : D.junkSubst K b n = some s) :
    ∃ T, T ∈ D.types ∧ T.name = n ∧ T.name ∈ K ∧ s = D.junkVal b T := by
  have h := Lean4Lean.List.lookup_mem h
  rw [VInductDecl'.junkList, List.mem_map] at h
  obtain ⟨T, hmem, hp⟩ := h
  rw [List.mem_filter] at hmem
  cases hp
  exact ⟨T, hmem.1, rfl, of_decide_eq_true hmem.2, rfl⟩

private theorem lookup_junkList_aux (D : VInductDecl') (K : List Name) (b : VIndType → VExpr) :
    ∀ (L : List VIndType), (L.map (·.name)).Nodup →
      ∀ {T : VIndType}, T ∈ L → T.name ∈ K →
        ((L.filter fun T => decide (T.name ∈ K)).map
            (fun T => (T.name, D.junkVal b T))).lookup T.name = some (D.junkVal b T)
  | [], _, _, hm, _ => absurd hm nofun
  | T₀ :: L, hnd, T, hm, hK => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [List.filter_cons]
    rcases List.mem_cons.1 hm with he | hm
    · cases he
      rw [if_pos (by simpa using hK), List.map_cons, List.lookup_cons]
      simp
    · have hne : T.name ≠ T₀.name := by
        intro hq
        exact hnd.1 (hq ▸ List.mem_map.2 ⟨T, hm, rfl⟩)
      by_cases h0 : T₀.name ∈ K
      · rw [if_pos (decide_eq_true h0), List.map_cons, List.lookup_cons,
          show (T.name == T₀.name) = false from beq_eq_false_iff_ne.2 hne]
        exact lookup_junkList_aux D K b L hnd.2 hm hK
      · rw [if_neg (by simpa using h0)]
        exact lookup_junkList_aux D K b L hnd.2 hm hK

theorem VInductDecl'.junkSubst_eq_some {D : VInductDecl'} {K : List Name} {b : VIndType → VExpr}
    (hnd : (D.types.map (·.name)).Nodup) {T : VIndType} (hT : T ∈ D.types) (hK : T.name ∈ K) :
    D.junkSubst K b T.name = some (D.junkVal b T) :=
  lookup_junkList_aux D K b D.types hnd hT hK

/-- **THE JUNK INHABITANT IS TYPED.**  `VIndType.WF.canon` moves it from the canonical telescope
to the stored type; the stored type is never inverted, so no `PiInv`. -/
theorem VInductDecl'.junkVal_hasType {env : VEnv} {D : VInductDecl'} (hD : D.WF env)
    {b : VIndType → VExpr} (hb : D.ResultSortInhab env b) {T : VIndType} (hT : T ∈ D.types) :
    env.HasType D.uvars [] (D.junkVal b T) T.type := by
  have hTW := hD.types T hT
  have hctx : (D.params ++ T.indices).reverse ++ ([] : List VExpr)
      = T.indices.reverse ++ D.params.reverse := by
    rw [List.append_nil, List.reverse_append]
  obtain ⟨_, hcanon⟩ := hTW.canon
  refine VEnv.IsDefEq.defeqDF hcanon.symm (VEnv.HasType.mkLams ?_ ?_)
  · rw [hctx]; exact hTW.indices
  · rw [hctx]; exact hb T hT

/-- **THE INHABITATION DATA, FROM THE RESULT SORT ALONE.**  Every other side condition is a field
of the configuration. -/
theorem VInductDecl'.companionVals_junk {D : VInductDecl'} {R : VIndRestore} {K : List Name}
    {env e₂ e₁ : VEnv} {occ : Nat → VNestedOcc} (C : RestrictStepCfg D R K env e₂ e₁ occ)
    {b : VIndType → VExpr} (hb : D.ResultSortInhab env b) :
    D.CompanionVals K e₂ e₁ (D.junkSubst K b) := by
  have h₂ := C.stage₂
  rw [VEnv.addIndTypes] at h₂
  have hnd : (D.types.map (·.name)).Nodup := by
    have := (VEnv.addConstList_fresh h₂).2
    rwa [VInductDecl'.typeConsts, List.map_map] at this
  have hval : ∀ {c : Name} {s : VExpr} {ci : VConstant}, D.junkSubst K b c = some s →
      e₂.constants c = some ci → e₁.HasType ci.uvars [] s ci.type := by
    intro c s ci hd hc
    obtain ⟨T, hT, rfl, -, rfl⟩ := VInductDecl'.junkSubst_dom hd
    rw [VEnv.addConstList_constants h₂ (T.name, ⟨D.uvars, T.type⟩)
      (List.mem_map.2 ⟨T, hT, rfl⟩)] at hc
    cases hc
    exact (VInductDecl'.junkVal_hasType C.wf hb hT).mono C.le₁
  refine { closed := ?_, dom := ?_, covers := ?_, val := hval }
  · intro c s hd
    obtain ⟨T, hT, rfl, hK, rfl⟩ := VInductDecl'.junkSubst_dom hd
    exact VEnv.IsDefEq.closedN C.ordered₁
      (hval hd (VEnv.addConstList_constants h₂ (T.name, ⟨D.uvars, T.type⟩)
        (List.mem_map.2 ⟨T, hT, rfl⟩))) trivial
  · intro c hd
    cases hs : D.junkSubst K b c with
    | none => exact absurd hs hd
    | some s => obtain ⟨T, -, rfl, hK, -⟩ := VInductDecl'.junkSubst_dom hs; exact hK
  · intro T hT hK
    rw [VInductDecl'.junkSubst_eq_some hnd hT hK]; exact nofun

/-! ### §4a The result sort is inhabited whenever the level is a successor, or zero

Two clauses, and between them they cover every level the *kernel* can emit for a block that is
not `Sort u`-polymorphic in its result.  `.param i` is exactly the case they miss (§6). -/

/-- `D.lvl ≈ .succ v`: the witness is `Sort v`. -/
theorem VInductDecl'.resultSortInhab_of_succ {env : VEnv} {D : VInductDecl'} {v : VLevel}
    (hv : v.WF D.uvars) (hlv : D.lvl.WF D.uvars) (heq : VLevel.succ v ≈ D.lvl) :
    D.ResultSortInhab env fun _ => .sort v := fun _ _ =>
  VEnv.IsDefEq.defeqDF (VEnv.IsDefEq.sortDF (l := .succ v) (l' := D.lvl) hv hlv heq)
    (VEnv.IsDefEq.sortDF hv hv (.refl _))

/-- `D.lvl ≈ .zero`: the witness is `∀ p : Prop, p`, whose level is `imax 1 0 ≈ 0`. -/
theorem VInductDecl'.resultSortInhab_of_zero {env : VEnv} {D : VInductDecl'}
    (hlv : D.lvl.WF D.uvars) (heq : VLevel.imax (.succ .zero) .zero ≈ D.lvl) :
    D.ResultSortInhab env fun _ => .forallE (.sort .zero) (.bvar 0) := fun _ _ =>
  VEnv.IsDefEq.defeqDF
    (VEnv.IsDefEq.sortDF (l := .imax (.succ .zero) .zero) (l' := D.lvl) ⟨trivial, trivial⟩ hlv heq)
    (VEnv.IsDefEq.forallEDF (VEnv.IsDefEq.sortDF trivial trivial (.refl _))
      (VEnv.IsDefEq.bvar .zero))

/-- **The level-polymorphic case**: a binder sitting at exactly the result sort is a witness.
This is what covers a `PUnit`-shaped block `inductive T (α : Sort u) : Sort u`, whose `D.lvl` is
`.param i` and for which §4a's two clauses fail — the witness is the parameter itself.  (Lifting a
`.sort` is the identity, so a context entry `Sort D.lvl` yields exactly that type at any depth.) -/
theorem VInductDecl'.resultSortInhab_of_lookup {env : VEnv} {D : VInductDecl'}
    {i : VIndType → Nat}
    (h : ∀ T ∈ D.types, Lookup (T.indices.reverse ++ D.params.reverse) (i T) (.sort D.lvl)) :
    D.ResultSortInhab env fun T => .bvar (i T) := fun T hT => .bvar (h T hT)

/-- **A FOURTH CLAUSE, AND IT SUBSUMES THE OTHER THREE.**  One constant declared at `Sort u`
inhabits `Sort D.lvl` for **every** well-formed `D.lvl` — successor, zero, `.param i`, `.imax` —
in every context and with no hypothesis on the environment beyond the constant's presence.
`PUnit.{u}` is such a constant.

This is why §8's residue is empty, and it arrived by **refuting** §8's own reasoning rather than
confirming it: see `VEnv.not_forall_sort_param_uninhabited`
(`Theory/Typing/WeakNForward.lean`), which exhibits a closed inhabitant of `Sort (.param 0)` at a
genuinely well-formed environment.  The omitted case was `.const`. -/
theorem VInductDecl'.resultSortInhab_of_const {env : VEnv} {D : VInductDecl'} {c : Name}
    (hc : env.constants c = some ⟨1, .sort (.param 0)⟩) (hlv : D.lvl.WF D.uvars) :
    D.ResultSortInhab env fun _ => .const c [D.lvl] :=
  fun _ _ => VEnv.hasType_const_sortParam hc hlv

/-! ## §5 The headline: the restriction step closes, with no hole -/

/-- **THE FAMILY, PROVED.**  At every configuration whose block's result sort is inhabited over
its members' telescopes, `ValStrengthen` holds — and therefore, by `restrictStep_entry`, so does
node 1, the datum at `e₁`, which is what the nested restriction step wanted.  No node of
RestrictStep's cycle, and no part of `Theory/Typing/UniqueTyping.lean`'s strengthening hole, is
used: the only transport is `VEnv.IsDefEq.substC`. -/
theorem VIndRestore.argsTypedK_of_resultSortInhab {D : VInductDecl'} {R : VIndRestore}
    {K : List Name} {env e₂ e₁ : VEnv} {occ : Nat → VNestedOcc} {b : VIndType → VExpr}
    (C : RestrictStepCfg D R K env e₂ e₁ occ) (H₂ : D.ArgsTypedK K e₂ occ)
    (hb : D.ResultSortInhab env b) :
    R.ValStrengthen D K e₂ e₁ ∧ D.ArgsTypedK K e₁ occ :=
  ⟨valStrengthen_of_companionVals C H₂ (D.companionVals_junk C hb),
   argsTypedK_of_companionVals C H₂ (D.companionVals_junk C hb)⟩

/-- …and the same at a successor result level, which is the shape every non-`Prop` block Lean
emits has. -/
theorem VIndRestore.argsTypedK_of_succLevel {D : VInductDecl'} {R : VIndRestore}
    {K : List Name} {env e₂ e₁ : VEnv} {occ : Nat → VNestedOcc} {v : VLevel}
    (C : RestrictStepCfg D R K env e₂ e₁ occ) (H₂ : D.ArgsTypedK K e₂ occ)
    (hv : v.WF D.uvars) (hlv : D.lvl.WF D.uvars) (heq : VLevel.succ v ≈ D.lvl) :
    R.ValStrengthen D K e₂ e₁ ∧ D.ArgsTypedK K e₁ occ :=
  argsTypedK_of_resultSortInhab C H₂ (VInductDecl'.resultSortInhab_of_succ hv hlv heq)

/-! ## §6 The parameterised nested witness: instantiated, nothing hypothesised

Working rule "instantiate, don't admire".  The block is `ntreeAux` — `NTree α` with a
`List (NTree α)` field, `np = 1`, `uvars = 1`, `lvl = .succ (.param 0)` — the block Lean's own
kernel runs the nested elimination on, and the one `docs/handoff-valat.md` §4 flagged as not yet
instantiated.  Its result level *is* a successor, so §4a's first clause fires and the level side
condition is `decide`-able.

Two things are exhibited: the inhabitation data at that witness with nothing hypothesised, and
the fact that the junk value is **not** the intended one — so the route really does avoid
`RestrictCompanion.lean` §3's sandwich rather than re-entering it. -/

namespace InductiveDeclExamples

/-- The junk witness at `ntreeAux`: `Sort u` inside the parameter telescope, i.e. `λ α, α` is
*not* what is used — the value is `λ (α : Type u), Sort u`. -/
def ntreeJunk : VIndType → VExpr := fun _ => .sort (.param 0)

/-- **THE STRENGTHENING INSTANCE, DISCHARGED BY THE GENERAL ROUTE, AT THE PARAMETERISED BLOCK.**
Compare `RestrictStep.lean` §3a, which discharges the same instance by `type_tac` on the concrete
spine: here nothing about the spine is used, only the block's result level. -/
theorem ntreeAux_resultSortInhab : ntreeAux.ResultSortInhab env ntreeJunk :=
  VInductDecl'.resultSortInhab_of_succ (v := .param 0) (by decide) (by decide) (.refl _)

/-- …and the whole cycle entered from it: node 5 and node 1, nothing hypothesised. -/
theorem ntreeAux_argsTypedK_of_level :
    ∃ env₁ env₂ env₃ : VEnv,
      RestrictStepCfg ntreeAux ntreeRestore ntreeK env₁ env₂ env₃ (fun _ => listOcc) ∧
      ntreeAux.ArgsTypedK ntreeK env₂ (fun _ => listOcc) ∧
      ntreeAux.CompanionVals ntreeK env₂ env₃ (ntreeAux.junkSubst ntreeK ntreeJunk) ∧
      ntreeRestore.ValStrengthen ntreeAux ntreeK env₂ env₃ ∧
      ntreeAux.ArgsTypedK ntreeK env₃ (fun _ => listOcc) := by
  obtain ⟨env₁, env₂, -, env₃, -, h, h₂, -, h₃, -⟩ := ntree_stage₂_exists
  have C := ntreeAux_restrictStepCfg h h₂ h₃
  have H₂ := ntreeAux_argsTypedK_of_wf (env₁ := env₁) h₂
  obtain ⟨h5, h1⟩ := VIndRestore.argsTypedK_of_resultSortInhab C H₂ ntreeAux_resultSortInhab
  exact ⟨env₁, env₂, env₃, C, H₂, ntreeAux.companionVals_junk C ntreeAux_resultSortInhab, h5, h1⟩

/-- **THE SUBSTITUTION'S DOMAIN IS NOT EMPTY AT THE WITNESS.**  A `CompanionVals` whose `σ` were
everywhere `none` would make §2's transport the identity and the discharge worthless.  It is not:
the companion name is in the domain, with the junk value. -/
theorem ntree_junkSubst_dom_val :
    ntreeAux.junkSubst ntreeK ntreeJunk `_nested.List_1
      = some (.lam (.sort (.succ (.param 0))) (.sort (.param 0))) := by decide

/-- **THE JUNK VALUE IS NOT THE INTENDED ONE.**  `RestrictCompanion.lean` §3's sandwich is about
`R.tyVal D j`; the substitution used above replaces the companion constant by a term with no
member constant in it at all, which is why its `val` clause is not the datum in disguise. -/
theorem ntree_junkVal_ne_tyVal :
    ntreeAux.junkVal ntreeJunk (ntreeAux.types.getD 1 default) ≠ ntreeVal := by decide

end InductiveDeclExamples

end Lean4Lean

/-! ## §8 The verdict: family versus general statement

**The family is strictly cheaper than the general statement, and the separation is not a matter
of degree — it is the inhabited/uninhabited split, which `ConstVar.lean` already isolated.**

`VEnv.axiomConservativityWF_iff_uninhabWF` (`Theory/Typing/ConstVar.lean`) proves that
`AxiomConservativityWF` is *equivalent* to its restriction to axioms whose type has **no**
inhabitant.  So every bit of the hole's content lives in the uninhabited case.  The constants
`ValStrengthen` has to drop are inductive members' type constants, definitionally
`Π params indices, Sort D.lvl` (`VIndType.canonType`, reached from the stored type by
`VIndType.WF.canon`), and §4/§4a inhabit exactly those.  §2 then discharges the family by
substituting an inhabitant, with `VEnv.IsDefEq.substC` as the only transport.

**In the terms the orchestrator asked for: this is a bypass of `Theory/Typing/UniqueTyping.lean`'s
`sorry` (the forward direction of `VEnv.IsDefEqU.weakN_iff`) for the nested restriction step, at
every block whose result sort is inhabited over its members' telescopes.**  `#print axioms` above
and `scripts/exists.lean` agree: `VIndRestore.argsTypedK_of_resultSortInhab` (cone 3333) and
`VIndRestore.argsTypedK_of_succLevel` (cone 3335) do **not** reach `sorryAx`.  Nothing here
attacks `weakN_iff` itself, and nothing here uses `VEnv.HasArgs.of_mkApp` or `PiInv`.

**The direction from the general statement costs a *second* hole, which is the other half of the
measurement.**  `VEnv.closedConservativeStep_of_axiomConservativityWF` (§1) is the "derive the
family from the general statement" leg, and it is *tainted*: cone 3518, reaching `sorryAx` through
`VEnv.IsDefEqU.forallE_inv_stratified` — because `AxiomConservativityWF` is a statement about
`IsDefEqU`, so recovering a *typed* judgement needs `VEnv.IsDefEq.uniqU` (cone 3474, tainted the
same way).  So the ordering is not "family ≤ general": *as stated*, the general statement does not
even imply the family without a second hole, while the route above proves the family outright.

**Why `RestrictStep.lean` §3a's hole-free instance is not special in the way that mattered.**  §3a
discharges its instance by `type_tac` on the concrete spine `List.{u} (NTree.{u} #0)`, which looks
like an accident of a small witness — one could reasonably fear it generalises to nothing.  It is
not an accident, but it is also not the reason the family is cheap: the general reason is that the
*value being moved* never has to be the intended `R.tyVal D j`.  `ntree_junkVal_ne_tyVal` is that
point made machine-checked at the parameterised witness: the substituted value is
`λ (α : Type u), Sort u`, which contains no member constant at all, where `ntreeVal` is
`λ (α : Type u), List.{u} (NTree.{u} α)`.  This is why the route escapes
`RestrictCompanion.lean` §3's sandwich — that sandwich is a statement about `R.csubstTy D K`, and
`R.csubstTy D K` is not the substitution used here.

**What is left, precisely.**  One premise: `VInductDecl'.ResultSortInhab`, i.e. a term of type
`Sort D.lvl` over `T.indices.reverse ++ D.params.reverse`, for each member.  Three clauses
discharge it (`resultSortInhab_of_succ`, `_of_zero`, `_of_lookup`), covering every `D.lvl` that is
`≈`-a-successor, `≈`-zero, or matched by a binder of the member's own telescope.  The residue is a
block whose result level is, say, `.param i` **and** which has no binder at that level — e.g. a
closed `inductive T : Sort u`.  For such a block the premise is not discharged by any of the three
clauses.

**CORRECTED 2026-09-03 — the paragraph that stood here was FALSE, and the residue is EMPTY.**  It
argued informally that a closed inhabitant of `Sort D.lvl` would have to be a `.sort` (forcing
`D.lvl ≈ .succ _`) or a `.forallE` (forcing `D.lvl ≈ .imax _ _`), so that none should exist.  That
case analysis **omits `.const`**.  `IsDefEq.constDF` types `.const c ls` at `ci.type.instL ls`, so
a single constant declared at `Sort u` inhabits **every** sort, in every context, with no
environment hypothesis at all — and `PUnit.{u}` is one.  Machine-checked as
`VEnv.not_forall_sort_param_uninhabited` (`Theory/Typing/WeakNForward.lean`), on an environment
that is well-formed via a plain `VDecl.WF.axiom` rather than inconsistent by construction.

The fourth clause `resultSortInhab_of_const` (§4) therefore covers **every** well-formed `D.lvl`,
subsuming all three of the others — *given* such a constant in the environment.  What the false
paragraph got wrong is the level reasoning; what replaces it is not a level condition but an
**environment** one.

**AND THAT ENVIRONMENT CONDITION IS FALSE HERE — so the residue is NOT empty.**  Measured the same
day in `Verify/Inductive/SortWitEnv.lean`: the environment this corner is actually instantiated at,
`VEnv.empty.addInduct' listDecl`, declares **no constant whose type is a sort at all**
(`InductiveDeclExamples.listEnv_no_sort_const`, cone 1070), and the condition is refuted at all
three of `env`, `e₂` and `e₁` (`not_sortWitness_of_restrictStepCfg₃`, arity 0, cone 3521), so no
reading of "at `e₁`/`e₂`" rescues it.  A prelude environment does satisfy it — `PUnit.{u}` — but the
spec quantifies over environments, and this one arises from a legitimate `addDecl` history.

So the honest position, and it is weaker than the first correction of this paragraph claimed: the
residue is a block with `D.lvl = .param i`, **no** telescope binder at that level, in an
environment with **no** `Sort u`-valued constant.  None of the four clauses discharges that.  What
is *not* affected: the bypass still holds at `ntreeAux` itself, through the **successor** clause —
only this fourth clause's premise fails there.

**What is NOT claimed.**  (i) That the family is *equivalent* to `ResultSortInhab` — the premise is
sufficient, and no reverse implication is proved (a block could satisfy the family for other
reasons).  (ii) That `ResultSortInhab` is necessary.  (iii) Anything about the flip,
`tryEtaStructCore.WF`, `isDefEqUnitLike.WF`, or the twelve other holes.  (iv) That `e₂` is an
`addConst` chain above `e₁` — §1's leg is stated for one added constant precisely because that
reordering lemma for `addConstList` is missing (see §1's docstring).  (v) Note that
`ResultSortInhab` quantifies over *every* member, not only the companions; only the companions are
needed, and weakening it to `T.name ∈ K` is free but was not done because all three discharge
clauses are uniform in `T` anyway. -/

/-! ## §7 Grading: hole-freeness, per declaration -/

#print axioms Lean4Lean.VEnv.ClosedConservativeStep.comp
#print axioms Lean4Lean.RestrictStepCfg.constant_of_csubstTy
#print axioms Lean4Lean.VEnv.closedConservativeStep_of_axiomConservativityWF
#print axioms Lean4Lean.VIndRestore.valStrengthen_of_closedStep
#print axioms Lean4Lean.VEnv.addConstList_constants_inv
#print axioms Lean4Lean.VInductDecl'.not_mem_typeConstsC_names
#print axioms Lean4Lean.RestrictStepCfg.constants_eq_none_of_mem_K
#print axioms Lean4Lean.RestrictStepCfg.freshIn_env
#print axioms Lean4Lean.RestrictStepCfg.freshIn₁
#print axioms Lean4Lean.RestrictStepCfg.constType_noCSubst
#print axioms Lean4Lean.VInductDecl'.CompanionVals.csubst_WF
#print axioms Lean4Lean.VIndRestore.valStrengthen_of_companionVals
#print axioms Lean4Lean.VIndRestore.argsTypedK_of_companionVals
#print axioms Lean4Lean.VInductDecl'.junkSubst_dom
#print axioms Lean4Lean.VInductDecl'.junkSubst_eq_some
#print axioms Lean4Lean.VInductDecl'.junkVal_hasType
#print axioms Lean4Lean.VInductDecl'.companionVals_junk
#print axioms Lean4Lean.VInductDecl'.resultSortInhab_of_succ
#print axioms Lean4Lean.VInductDecl'.resultSortInhab_of_zero
#print axioms Lean4Lean.VInductDecl'.resultSortInhab_of_lookup
#print axioms Lean4Lean.VInductDecl'.resultSortInhab_of_const
#print axioms Lean4Lean.VIndRestore.argsTypedK_of_resultSortInhab
#print axioms Lean4Lean.VIndRestore.argsTypedK_of_succLevel
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_resultSortInhab
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_argsTypedK_of_level
#print axioms Lean4Lean.InductiveDeclExamples.ntree_junkSubst_dom_val
#print axioms Lean4Lean.InductiveDeclExamples.ntree_junkVal_ne_tyVal
