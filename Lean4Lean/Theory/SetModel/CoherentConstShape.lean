import Lean4Lean.Theory.SetModel.FalseProp
import Lean4Lean.Theory.SetModel.CoherentWitness

/-!
# `CoherentOn` at a *reachable* environment, and what it does **not** buy the injectivity corner

Two things are done here, and the second is the point.

## 1. `CoherentOn` is inhabited at an environment some declaration list actually produces

`SetModel/CoherentWitness.lean`'s `coherentOn_witness` inhabits `CoherentOn` at `witEnv c`,
an environment assembled by hand: one constant plus the reflexive defeq
`⟨0, .const c [], .const c [], .sort .zero⟩`.  That environment is `Ordered` — `Ordered.const`
then `Ordered.defeq`, the defeq's `VDefEq.WF` being discharged by `constDF` *after* the constant
is declared.  §5 measures which declaration rule reaches it, and the answer matters: it is
`VEnv.WF` (`witEnv_wf_unsafe`) but **only through `VDecl.unsafeDef`**, the single impure rule,
which `VDecl.noUnsafe` forbids and `CnstRecursion.coherentOn_cnstOf` refuses outright.  The pure
δ-rule step cannot supply that defeq (`not_defStep_witDefEq`), because `VDecl.def` checks the
value in the environment *before* the constant is declared and `.const c []` mentions `c`.  So
`coherentOn_witness` certifies `CoherentOn` at an environment the soundness induction never
visits.

`coherentOn_propAx` and `coherentOn_typeAx` below inhabit `CoherentOn` at environments for
which `VEnv.WF` is machine-checked (`axEnv_wf`), produced by the one-element declaration list
`[.axiom …]`.  They are weaker than `coherentOn_witness` in one respect — `defeq` and
`defeq_type` are vacuous, there being no defeqs — and stronger in the two respects that matter
below: the environment is reachable, and it is **rule-free** (`axEnv_no_defeqs`), so
`VEnv.RuleFreeHead` holds at every name.  Rule-freeness is exactly the hypothesis the
constant-spine conjuncts of `Injectivity.WF.rigidShapeUniqNS` carry.

## 2. The two constant-spine conjuncts are **not** rescued by `Coherent`

`Theory/Typing/InjSortPiModel.lean` classifies the five conjuncts of
`RigidNodeCircle.rigidShapeUniqNS_iff_family` by semantic reachability and records
`RigidConstPiDisj` and `RigidConstSortDisj` as *"negative, needs `Coherent`"*: the residual
`ConstNotUniv` ("a constant never denotes a universe stage") is false unguarded
(`not_constNotUniv`) because `ModelData.cnst` is a free field, and the hope was that the
`Coherent` constraint tying `cnst` to the declarations would rule the counterexample out.

**It does not.**  `CoherentOn.const_type` constrains a constant's value only by
*membership* in the denotation of its declared type, and both shapes are available inside a
declared type:

* `axiom c : Type 0` — its denotation is `U κ 1`, and `U κ 0 ∈ U κ 1` (`U_mem_succ`), so a
  `Coherent` model may set `cnst c us = U κ 0`.  Then `.const c us` and `.sort .zero` have the
  *same* denotation in *every* context at *every* valuation (`coherent_const_denot_eq_sort`).
* `axiom c : Prop` — `⟦∀ p : Prop, p⟧ ∅ = ∅` (`interp_falseProp`) and `∅ ∈ UProp`, so a
  `Coherent` model may set `cnst c us = ∅`, which is the denotation of a `∀`
  (`coherent_const_denot_eq_forallE`).

So `not_coherentConstNotUniv` and `not_coherentConstNotPi` refute the residuals *under*
`CoherentOn`, over a `VEnv.WF` environment with **no defining equations at all** — a hypothesis
strictly stronger than the `RuleFreeHead c` the conjuncts supply.  And the counterexample is not
excluded one level down either: `oracleOK_univ` shows it satisfies `Cnst.OracleOK`, the obligation
`CnstRecursion.OracleFits` imposes at an `.axiom` step, which is the same pair of conditions.  So
the verdict on those two conjuncts is not "blocked on a construction" but **dead for this route**:
no route whose only constraint on `cnst` is `CoherentOn` (equivalently, `OracleFits` at an axiom
name) can separate a rule-free constant spine from a sort or from a `∀`.

## Boundary control, and what is NOT claimed

`CoherentOn` at a one-axiom environment is a *weak* constraint, not a *vacuous* one:
`not_coherentOn_falseProp` shows no model is `CoherentOn` at `axiom cShape : ∀ p : Prop, p`, an
equally well-formed one-axiom environment, once `κ` carries chains of every length.
`coherentOn_axEnv_separates` packages the three facts — satisfiable at `Prop`, satisfiable at
`Type 0`, unsatisfiable at `∀ p : Prop, p` — so the witnesses above measure the presence of a
weak constraint rather than the absence of one.

Not claimed:

* **The conjuncts themselves are not refuted.**  `RigidConstSortDisj` and `RigidConstPiDisj` are
  presumably *true*; what is refuted is the model-side residual any part-4 route to them would
  have to prove.  A syntactic route is untouched.
* **No claim about every conceivable model.**  A model that pins `cnst` by *equation* rather than
  by membership — as `Cnst.coherentOn_defEq` does at a `.def`, and as `InductOracleOK` and
  `QuotOracleOK` are meant to do at their names — could separate the shapes at *those* names.
  What is dead is the route at an **axiom** name, and that suffices, because
  `RigidConstSortDisj` is quantified over every `VEnv.WF` environment and `axEnv ⟨0, .sort
  (.succ .zero)⟩` is one of them.
* **No census movement.**  `Injectivity.WF.rigidShapeUniqNS` still carries its `sorry`; this
  file removes a candidate route rather than closing a hole.
* No obligation here quantifies over `ρ ∈ interpCtx M L Γ`, so `vacuity-ledger` row 24's trap
  (`sortInvSupply_vacuous`) does not apply: `coherent_const_denot_eq_sort` states its equation at
  *all* `Γ` and `ρ` with no membership guard, and the rest live at the empty context, where
  `∅ ∈ interpCtx M L []`.

## Non-degeneracy: this is not an `Above` artefact

`CoherentOn`'s fields are wrapped in `Above M P = ∃ m, IsInaccessibleChain m M.κ → P`, which is
trivially true for a `κ` carrying no chain, so a witness could be vacuous.  It is not:

* `above_iff_of_chain` — for a `κ` carrying chains of every length, `Above M P ↔ P`, so
  `CoherentOn` unwraps completely and the witnesses still stand.
* `typeAx_const_type_unwrapped` — the sort-side field holds with the `Above` **stripped**, given
  a chain of length one.  The Prop-side field never used `Above` at all (`Above.pure`).

## Correction to the brief this file answers

The brief said `ModelData.Coherent` is *"specified in `InterpSound.lean` and constructed
nowhere"*.  That is wrong twice over.  There is no `ModelData.Coherent`; the structure is
`SetModel.CoherentOn`, and it is constructed in two places already:
`CoherentWitness.coherentOn_witness` (a closed witness, arbitrary `L`) and
`CnstRecursion.coherentOn_cnstOf` (the full declaration-list recursion, residual
`InductOracleOK` bounded both ways).  What was genuinely missing is the *measurement* above.
-/

namespace Lean4Lean.SetModel

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V]

/-! ## 1. `Above` is not a free pass -/

section AboveControl
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {M : ModelData V}

/-- **For a `κ` that carries a chain of every length, `Above` is the identity.**  So a witness
that survives `Above`-unwrapping is not exploiting a `κ` with no chain.  `∀ m` is the same
hypothesis `CnstRecursion.consistent_of` takes. -/
theorem above_iff_of_chain (hκ : ∀ m : ℕ, IsInaccessibleChain m M.κ) {P : Prop} :
    Above M P ↔ P :=
  ⟨fun ⟨m, hm⟩ ↦ hm (hκ m), Above.pure⟩

end AboveControl

/-! ## 2. A rule-free, reachable, one-axiom environment -/

/-- The single name declared below. -/
def cShape : Name := `Lean4Lean.SetModel.cShape

/-- One constant at a sort, no defining equations.  `defeqs` is `False`, which is what makes
`VEnv.RuleFreeHead (axEnv ci) c` hold for *every* `c`. -/
def axEnv (ci : VConstant) : VEnv where
  constants n := if cShape = n then some ci else none
  defeqs _ := False

theorem axEnv_addConst (ci : VConstant) : VEnv.empty.addConst cShape ci = some (axEnv ci) := rfl

theorem axEnv_constants {ci : VConstant} {d : Name} :
    (axEnv ci).constants d = if cShape = d then some ci else none := rfl

theorem axEnv_self {ci : VConstant} : (axEnv ci).constants cShape = some ci := by
  rw [axEnv_constants, if_pos rfl]

/-- **No defining equations.**  Stronger than `VEnv.RuleFreeHead (axEnv ci) c`, which is
`∀ df, (axEnv ci).defeqs df → VExpr.headConst? df.lhs ≠ some c` and follows immediately. -/
theorem axEnv_no_defeqs {ci : VConstant} : ∀ df, ¬ (axEnv ci).defeqs df := fun _ h ↦ h

/-- **The environment is reachable**: the one-element declaration list `[.axiom …]` produces it,
for any type that is a type over the empty environment. -/
theorem axEnv_wf' {ci : VConstant} (h : VConstant.WF VEnv.empty ci) : VEnv.WF (axEnv ci) :=
  ⟨[.axiom ⟨ci, cShape⟩], .decl (.axiom h (axEnv_addConst _)) .empty⟩

theorem axEnv_wf {u : VLevel} (hu : u.WF 0) : VEnv.WF (axEnv ⟨0, .sort u⟩) :=
  axEnv_wf' ⟨_, VEnv.HasType.sort hu⟩

/-- `axiom cShape : ∀ p : Prop, p` is *also* a well-formed one-axiom environment — `VDecl.WF`'s
`.axiom` rule asks only that the declared type be a type, never that it be inhabited.  This is
the environment §4's control uses. -/
theorem axEnv_falseProp_wf : VEnv.WF (axEnv ⟨0, falseProp⟩) :=
  axEnv_wf' ⟨_, VEnv.HasType.forallE (VEnv.HasType.sort trivial) (VEnv.HasType.bvar .zero)⟩

/-! ## 3. Two `CoherentOn` witnesses at that environment -/

section Witness
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ}

/-- Every constant denotes `∅`. -/
noncomputable def cnstEmpty (κ : ℕ → V) (ls : List ℕ) : ModelData V := ⟨κ, ls, fun _ _ ↦ ∅⟩

/-- Every constant denotes the propositional stage `U κ 0 = UProp`. -/
noncomputable def cnstUProp (κ : ℕ → V) (ls : List ℕ) : ModelData V := ⟨κ, ls, fun _ _ ↦ U κ 0⟩

/-- `Prop` is level-instantiation-invariant, and denotes `UProp`. -/
theorem interp_sort_zero_instL (M : ModelData V) (L : PropSplit envF nv) (us : List VLevel)
    (Γ : List VExpr) (ρ : V) :
    (interp M L Γ ((VExpr.sort .zero).instL us)).toFun ρ = (UProp : V) := by
  show (interp M L Γ (VExpr.sort .zero)).toFun ρ = _
  rw [interp_sort]; rfl

/-- `Type 0` likewise, denoting the first non-propositional stage. -/
theorem interp_sort_one_instL (M : ModelData V) (L : PropSplit envF nv) (us : List VLevel)
    (Γ : List VExpr) (ρ : V) :
    (interp M L Γ ((VExpr.sort (.succ .zero)).instL us)).toFun ρ = U M.κ 1 := by
  show (interp M L Γ (VExpr.sort (.succ .zero))).toFun ρ = _
  rw [interp_sort]; rfl

/-- **`CoherentOn` at `axiom cShape : Prop`, with every constant denoting `∅`.**  `Above` is
never used non-trivially: `∅ ∈ UProp` needs no chain. -/
theorem coherentOn_propAx (L : PropSplit envF nv) (κ : ℕ → V) (ls : List ℕ) :
    CoherentOn (cnstEmpty (V := V) κ ls) L (axEnv ⟨0, .sort .zero⟩) := by
  refine ⟨fun _ _ _ ↦ Above.pure rfl, fun {d ci us} hd _ _ ↦ ?_, fun h ↦ h.elim, fun h ↦ h.elim⟩
  rw [axEnv_constants] at hd
  split at hd
  · cases hd
    refine Above.pure ?_
    show (∅ : V) ∈ (interp (cnstEmpty κ ls) L [] ((VExpr.sort .zero).instL us)).toFun ∅
    rw [interp_sort_zero_instL]
    exact empty_mem_UProp
  · exact absurd hd nofun

/-- **`CoherentOn` at `axiom cShape : Type 0`, with every constant denoting `U κ 0`.**  The
sort-side field is the only place `Above` does work, and `typeAx_const_type_unwrapped` below
shows it is not doing vacuous work. -/
theorem coherentOn_typeAx (L : PropSplit envF nv) (κ : ℕ → V) (ls : List ℕ) :
    CoherentOn (cnstUProp (V := V) κ ls) L (axEnv ⟨0, .sort (.succ .zero)⟩) := by
  refine ⟨fun _ _ _ ↦ Above.pure rfl, fun {d ci us} hd _ _ ↦ ?_, fun h ↦ h.elim, fun h ↦ h.elim⟩
  rw [axEnv_constants] at hd
  split at hd
  · cases hd
    refine ⟨1, fun hκ ↦ ?_⟩
    show U κ 0 ∈ (interp (cnstUProp κ ls) L [] ((VExpr.sort (.succ .zero)).instL us)).toFun ∅
    rw [interp_sort_one_instL]
    exact U_mem_succ hκ Nat.zero_lt_one
  · exact absurd hd nofun

/-- **Non-degeneracy of the one `Above` used**: with a chain of length one the sort-side field
holds outright, `Above` stripped. -/
theorem typeAx_const_type_unwrapped (L : PropSplit envF nv) {κ : ℕ → V} (ls : List ℕ)
    (hκ : IsInaccessibleChain 1 κ) (us : List VLevel) :
    (cnstUProp (V := V) κ ls).cnst cShape us
      ∈ (interp (cnstUProp (V := V) κ ls) L []
          ((VConstant.mk 0 (.sort (.succ .zero))).type.instL us)).toFun ∅ := by
  show U κ 0 ∈ (interp (cnstUProp κ ls) L [] ((VExpr.sort (.succ .zero)).instL us)).toFun ∅
  rw [interp_sort_one_instL]
  exact U_mem_succ hκ Nat.zero_lt_one

end Witness

/-! ## 4. The two residuals, guarded by `CoherentOn`, and their refutations -/

section Residual
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ}

/-- **`InjSortPi.ConstNotUniv`, guarded by `CoherentOn`.**  The guard is as strong as can be
asked for and still be what the injectivity conjunct supplies: the environment is well formed,
carries **no** defining equations (hence `RuleFreeHead` at every name), the constant is
declared, and the model is `CoherentOn` at it. -/
def CoherentConstNotUniv (L : PropSplit envF nv) (κ : ℕ → V) : Prop :=
  ∀ M : ModelData V, M.κ = κ → ∀ env : VEnv, VEnv.WF env → CoherentOn M L env →
    (∀ df, ¬ env.defeqs df) →
      ∀ (c : Name) (ci : VConstant) (us : List VLevel) (i : ℕ),
        env.constants c = some ci → M.cnst c us ≠ U κ i

/-- The `∀`-shaped companion, for `RigidConstPiDisj`. -/
def CoherentConstNotPi (L : PropSplit envF nv) : Prop :=
  ∀ M : ModelData V, ∀ env : VEnv, VEnv.WF env → CoherentOn M L env →
    (∀ df, ¬ env.defeqs df) →
      ∀ (c : Name) (ci : VConstant) (us : List VLevel) (A B : VExpr),
        env.constants c = some ci →
          M.cnst c us ≠ (interp M L [] (.forallE A B)).toFun ∅

/-- **The sort-side residual is FALSE under `CoherentOn`.**  So `RigidConstSortDisj` is not
reachable from soundness plus coherence, and `InjSortPiModel.lean`'s *"needs `Coherent`"* is a
dead end rather than a pending construction. -/
theorem not_coherentConstNotUniv (L : PropSplit envF nv) (κ : ℕ → V) (ls : List ℕ) :
    ¬ CoherentConstNotUniv (V := V) L κ := by
  intro h
  exact h (cnstUProp κ ls) rfl (axEnv ⟨0, .sort (.succ .zero)⟩) (axEnv_wf trivial)
    (coherentOn_typeAx L κ ls) axEnv_no_defeqs cShape _ [] 0 axEnv_self rfl

/-- **The `∀`-side residual is FALSE under `CoherentOn`**, and this one needs no chain at all:
`⟦∀ p : Prop, p⟧ ∅ = ∅` (`interp_falseProp`) and `∅ ∈ UProp`. -/
theorem not_coherentConstNotPi (L : PropSplit envF nv) (κ : ℕ → V) (ls : List ℕ) :
    ¬ CoherentConstNotPi (V := V) L := by
  intro h
  refine h (cnstEmpty κ ls) (axEnv ⟨0, .sort .zero⟩) (axEnv_wf trivial)
    (coherentOn_propAx L κ ls) axEnv_no_defeqs cShape _ [] (.sort .zero) (.bvar 0)
    axEnv_self ?_
  rw [show (VExpr.forallE (.sort .zero) (.bvar 0)) = falseProp from rfl, interp_falseProp]
  rfl

/-! ### The part-4 data, spelled out

What the semantic route to the two conjuncts would need is that the *denotations* differ.  In
these `CoherentOn` models they coincide, which is the statement the route has to contradict and
cannot. -/

/-- **A declared constant and `Prop` have the same denotation, in every context, at every
valuation, in a `CoherentOn` model over a well-formed rule-free environment.** -/
theorem coherent_const_denot_eq_sort (L : PropSplit envF nv) (κ : ℕ → V) (ls : List ℕ) :
    ∃ M : ModelData V, ∃ env : VEnv, VEnv.WF env ∧ CoherentOn M L env ∧
      (∀ df, ¬ env.defeqs df) ∧ (∃ ci, env.constants cShape = some ci) ∧
      ∀ (Γ : List VExpr) (us : List VLevel) (ρ : V),
        (interp M L Γ (.const cShape us)).toFun ρ = (interp M L Γ (.sort .zero)).toFun ρ :=
  ⟨cnstUProp κ ls, axEnv ⟨0, .sort (.succ .zero)⟩, axEnv_wf trivial, coherentOn_typeAx L κ ls,
    axEnv_no_defeqs, ⟨_, axEnv_self⟩, fun Γ us ρ ↦ by rw [interp_const, interp_sort]; rfl⟩

/-- **A declared constant and `∀ p : Prop, p` have the same denotation** in a `CoherentOn` model
over a well-formed rule-free environment. -/
theorem coherent_const_denot_eq_forallE (L : PropSplit envF nv) (κ : ℕ → V) (ls : List ℕ) :
    ∃ M : ModelData V, ∃ env : VEnv, VEnv.WF env ∧ CoherentOn M L env ∧
      (∀ df, ¬ env.defeqs df) ∧ (∃ ci, env.constants cShape = some ci) ∧
      ∀ us : List VLevel,
        (interp M L [] (.const cShape us)).toFun ∅
          = (interp M L [] (.forallE (.sort .zero) (.bvar 0))).toFun ∅ :=
  ⟨cnstEmpty κ ls, axEnv ⟨0, .sort .zero⟩, axEnv_wf trivial, coherentOn_propAx L κ ls,
    axEnv_no_defeqs, ⟨_, axEnv_self⟩, fun us ↦ by
      rw [interp_const, show (VExpr.forallE (.sort .zero) (.bvar 0)) = falseProp from rfl,
        interp_falseProp]
      rfl⟩

/-- **The counterexample satisfies the *oracle's* obligation too, not merely `CoherentOn`'s.**
`Cnst.OracleOK` at an `.axiom` step is exactly `const_congr` + `const_type` at that one name —
pure membership again — so the refutation is against the assignment
`CnstRecursion.cnstOf`/`OracleFits` actually constructs, not only against the interface
`CoherentOn` exposes.  There is no room in the specification to exclude it. -/
theorem oracleOK_univ (L : PropSplit envF nv) (κ : ℕ → V) (ls : List ℕ) :
    OracleOK L κ ls (fun _ _ ↦ U κ 0) (cnstUProp (V := V) κ ls).cnst cShape
      ⟨0, .sort (.succ .zero)⟩ where
  congr _ _ _ := Above.pure rfl
  type {us} _ _ := ⟨1, fun hκ ↦ by
    show U κ 0 ∈ (interp (cnstUProp (V := V) κ ls) L []
      ((VExpr.sort (.succ .zero)).instL us)).toFun ∅
    rw [interp_sort_one_instL]
    exact U_mem_succ hκ Nat.zero_lt_one⟩

/-! ### Boundary control: `CoherentOn` at a one-axiom environment is NOT always satisfiable

Without this the two refutations above would prove nothing: if `CoherentOn` were satisfiable at
*every* one-axiom environment by an arbitrary `cnst`, the witnesses would be measuring the
absence of a constraint rather than the presence of a weak one.  It is not.  `axiom cShape : ∀ p
: Prop, p` is a well-formed one-axiom environment (`axEnv_falseProp_wf`) at which **no** model
is `CoherentOn`, once `κ` carries chains of every length — the same argument as
`CnstRecursion.not_oracleOK_falseProp`, run at `CoherentOn` itself rather than at the oracle. -/
theorem not_coherentOn_falseProp (L : PropSplit envF nv) {κ : ℕ → V}
    (hκ : ∀ m : ℕ, IsInaccessibleChain m κ) (ls : List ℕ) (cn : Name → List VLevel → V) :
    ¬ CoherentOn (V := V) ⟨κ, ls, cn⟩ L (axEnv ⟨0, falseProp⟩) := by
  intro hC
  have h := hC.const_type (ls := []) axEnv_self nofun rfl
  rw [above_iff_of_chain (M := (⟨κ, ls, cn⟩ : ModelData V)) hκ] at h
  rw [show (VConstant.mk 0 falseProp).type.instL [] = falseProp from rfl, interp_falseProp] at h
  exact absurd h not_mem_empty

/-- So `CoherentOn`'s `const_type` field is doing real work at `axEnv`: it is satisfiable there
for `Prop` and for `Type 0` and unsatisfiable for `∀ p : Prop, p`, all three at environments
`VEnv.WF` accepts. -/
theorem coherentOn_axEnv_separates (L : PropSplit envF nv) {κ : ℕ → V}
    (hκ : ∀ m : ℕ, IsInaccessibleChain m κ) (ls : List ℕ) :
    CoherentOn (cnstEmpty (V := V) κ ls) L (axEnv ⟨0, .sort .zero⟩) ∧
      CoherentOn (cnstUProp (V := V) κ ls) L (axEnv ⟨0, .sort (.succ .zero)⟩) ∧
      ∀ cn : Name → List VLevel → V,
        ¬ CoherentOn (V := V) ⟨κ, ls, cn⟩ L (axEnv ⟨0, falseProp⟩) :=
  ⟨coherentOn_propAx L κ ls, coherentOn_typeAx L κ ls,
    fun cn ↦ not_coherentOn_falseProp L hκ ls cn⟩

/-! ### And the refutations survive full-chain models

The only place `Above` was used non-trivially is `coherentOn_typeAx`'s `const_type`, and
`typeAx_const_type_unwrapped` discharges it with a chain of length one.  So both refutations
hold for a `κ` carrying chains of every length, where `above_iff_of_chain` makes `CoherentOn`
unwrap completely. -/
theorem not_coherentConstNotUniv_chain (L : PropSplit envF nv) {κ : ℕ → V} (ls : List ℕ)
    (_hκ : ∀ m : ℕ, IsInaccessibleChain m κ) : ¬ CoherentConstNotUniv (V := V) L κ :=
  not_coherentConstNotUniv L κ ls

end Residual

/-! ## 5. Which rule reaches `coherentOn_witness`'s environment

Section 1's docstring says `witEnv c` is not known to be `VEnv.WF`.  It **is** — but only through
`VDecl.unsafeDef`, the one impure rule, which `VDecl.noUnsafe` forbids and which
`CnstRecursion.coherentOn_cnstOf` therefore refuses (`(hnu _ (.head _)).elim`).  Both halves are
below.  So `coherentOn_witness` inhabits `CoherentOn` at an environment the soundness induction
never visits, which is what `axEnv` fixes. -/

section WitEnvReach
variable {c : Name}

/-- The `partial`/`unsafe` block whose δ-rule is `witDefEq c`. -/
def witUnsafeVal (c : Name) : VDefVal := ⟨⟨⟨0, .sort .zero⟩, c⟩, .const c []⟩

theorem witUnsafeVal_toDefEq : (witUnsafeVal c).toDefEq = witDefEq c := rfl

/-- `witEnv c` before its δ-rule is added. -/
def witPre (c : Name) : VEnv where
  constants n := if c = n then some witConst else none
  defeqs _ := False

theorem witPre_addConsts : VEnv.empty.addConsts [witUnsafeVal c] = some (witPre c) := rfl

theorem witPre_self : (witPre c).constants c = some witConst := by
  show (if c = c then some witConst else none) = _
  rw [if_pos rfl]

theorem witPre_addDefEqs : (witPre c).addDefEqs [witUnsafeVal c] = witEnv c := rfl

/-- **`witEnv c` is reachable — through the impure rule.**  The value `.const c []` typechecks
only in the environment that already carries `c`, which is exactly the circularity
`VDecl.unsafeDef` permits and no other rule does (`Theory/MutualDefUnsound.lean`). -/
theorem witEnv_wf_unsafe : VEnv.WF (witEnv c) := by
  refine ⟨[.unsafeDef [witUnsafeVal c]], .decl (d := .unsafeDef [witUnsafeVal c]) ?_ .empty⟩
  rw [← witPre_addDefEqs (c := c)]
  refine .unsafeDef ?_ witPre_addConsts ?_
  · intro ci hci
    cases List.mem_singleton.1 hci
    exact ⟨_, VEnv.HasType.sort trivial⟩
  · intro ci hci
    cases List.mem_singleton.1 hci
    exact VEnv.HasType.const (ci := witConst) witPre_self nofun rfl

/-- …and the witnessing list is **not** `noUnsafe`. -/
theorem witEnv_wf_unsafe_impure :
    ¬ ∀ d ∈ [VDecl.unsafeDef [witUnsafeVal c]], VDecl.noUnsafe d :=
  fun h ↦ h _ (.head _)

/-- **The one *pure* rule that adds a δ-rule cannot add this one.**  `VDecl.def` checks the
value in the environment *before* the constant is declared, and `.const c []` mentions `c`; so
`Ordered.constsIn` refutes it.  (`.axiom`, `.opaque` and `.example` add no δ-rule at all;
`.quot` and `.induct` add `quotDefEq` and ι-rules, neither of which is `witDefEq c`.) -/
theorem not_defStep_witDefEq {env env' : VEnv} (henv : env.Ordered) {ci : VDefVal}
    (hdf : ci.toDefEq = witDefEq c) (hadd : env.addConst ci.name ci.toVConstant = some env')
    (hwf : ci.WF env) : False := by
  have hlhs : (VDefVal.toDefEq ci).lhs = (witDefEq c).lhs := by rw [hdf]
  have hrhs : (VDefVal.toDefEq ci).rhs = (witDefEq c).rhs := by rw [hdf]
  have hname : ci.name = c := by
    have := hlhs
    simp [VDefVal.toDefEq, witDefEq] at this
    exact this.1
  have hval : ci.value = .const c [] := by
    simpa [VDefVal.toDefEq, witDefEq] using hrhs
  have hfresh : env.constants c = none := by
    unfold VEnv.addConst at hadd
    rw [hname] at hadd
    split at hadd
    · exact absurd hadd nofun
    · assumption
  have hwf' : env.HasType ci.uvars [] (.const c []) ci.type := hval ▸ hwf
  have hc : (VExpr.const c []).ConstsIn env.contains :=
    (VEnv.IsDefEq.constsIn henv.constsIn hwf' (Γ := []) trivial).1
  obtain ⟨_, h⟩ := VExpr.ConstsIn.const_iff.1 hc
  rw [hfresh] at h
  exact absurd h nofun

end WitEnvReach

section Audit
/-! ## 6. Axiom check -/

#print axioms Lean4Lean.SetModel.above_iff_of_chain
#print axioms Lean4Lean.SetModel.axEnv_wf
#print axioms Lean4Lean.SetModel.axEnv_no_defeqs
#print axioms Lean4Lean.SetModel.coherentOn_propAx
#print axioms Lean4Lean.SetModel.coherentOn_typeAx
#print axioms Lean4Lean.SetModel.typeAx_const_type_unwrapped
#print axioms Lean4Lean.SetModel.not_coherentConstNotUniv
#print axioms Lean4Lean.SetModel.not_coherentConstNotPi
#print axioms Lean4Lean.SetModel.coherent_const_denot_eq_sort
#print axioms Lean4Lean.SetModel.coherent_const_denot_eq_forallE
#print axioms Lean4Lean.SetModel.not_coherentConstNotUniv_chain
#print axioms Lean4Lean.SetModel.oracleOK_univ
#print axioms Lean4Lean.SetModel.axEnv_falseProp_wf
#print axioms Lean4Lean.SetModel.not_coherentOn_falseProp
#print axioms Lean4Lean.SetModel.coherentOn_axEnv_separates
#print axioms Lean4Lean.SetModel.witEnv_wf_unsafe
#print axioms Lean4Lean.SetModel.not_defStep_witDefEq

end Audit

end Lean4Lean.SetModel
