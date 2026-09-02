import Lean4Lean.Theory.SetModel.UnitOracleWitness

/-!
# The `.induct` residual at the **large** eliminator

`UnitOracleWitness.lean` closes `InductOracleOK` at `unitDecl = inductive Unit1 : Prop | mk`
with `isLE := false`, and its §9 identifies the remaining case: `isLE := true`, the eliminator
Lean actually declares (`unitDeclLE_LECond` holds, vacuously, because the constructor has no
fields).  There `interp` takes `mkForallType` and `•` is not a legal value.

**This file closes that case.**  `inductOracleOKL` proves both fields of `InductOracleOK` at
`unitDeclLE`, and `oracleFitsL` extends it to `[.induct unitDeclLE]`.

## The two questions this file was asked

**1. Does the ι-rule still close once the recursor's value is a genuine function?  Yes.**
`interpL_unitRule_eq_of_ne`.  The computational core is `recFnL_beta`:
`((recFnL κ n ‘ f) ‘ m) ‘ • = m`, three set-theoretic applications of the oracle's value.  The
left side of the rule is a real application of it and reduces to the minor premise `m`; the
right side is the η-expanded β-redex `iotaRule` builds, and `interp`'s `lam` clause reduces it
to `m` as well.  Nothing about the rule needed the value to be `•`.

**2. Can `u.eval ls = 0` be handled separately, so the residual is only the `≠ 0` slice?
Yes — and it is *free*.**  `pt_mem_interpL_recType_of_zero` and
`interpL_unitRule_sides_of_zero`: at a `Prop` instantiation every binder of `recType` is
propositional again, `•` is the value, and the proof is §8's copy of the small-eliminator
argument.  So large elimination *into `Prop`* collapses to the small case, and the genuine
content is the `≠ 0` slice alone.

Both slices are non-empty cases (`exists_eq_zero_level`, `exists_ne_zero_level`), so this is a
real split rather than a formality.

## How the oracle is written, and why the branch is forced

`unitOracleL` sends `Unit1 ↦ {•}`, and `Unit1.rec` to `•` when the elimination universe
evaluates to `0` and to `recFnL κ n` otherwise.  The `if` is **forced**:
`pt_not_mem_interpL_recType_of_ne` shows `•` is excluded at `n ≠ 0` given any inhabitant of
the motive space, while at `n = 0` the type is a proposition whose only element is `•`.  So no
level-uniform value can satisfy both — the model-side shadow of `Prop`'s collapse.

The value must be written **without** `interp`, since `interp` reads `M.cnst`.  Two general
lemmas in §4 make that possible and are the reusable part of this file:

* `mem_mkForallType_of_graph` — an extensional entry into `mkForallType`, asking only that `f`
  be a graph over the domain landing in the codomain family.
* `mkLam_mem_mkForallType_of_dom` — `mkLam` lands in `mkForallType` when the two domains merely
  *agree at the valuation*.  `InterpSound.mkLam_mem_mkForallType` needs them to be the same
  term, which is impossible when one comes from the oracle and the other from `interp`.
* `mkForallType_singleton_const` — a `∀` over a singleton domain with constant codomain **is**
  the function space.  This is `interpL_motTyU`: `⟦Unit1 → Sort u⟧ = U_n ^ {•}`, the equation
  the oracle's value is built against.
* `mkLam_ext` — `mkLam` is determined by its domain set and its body's values on it; this is
  what compares the ι-rule's two sides.

## Bounds, and what is not claimed

`Above`-free at an arbitrary `κ`, both fields, both slices: `mem_interp_constsL`,
`defEq_rulesL`.  Every proof goes through `Above.pure`; **no `κ` is chosen anywhere.**

`hle : unitEnvLE ≤ envF` is carried exactly as in `UnitOracleWitness.lean`, and for the same
reason it costs nothing: `oracleFitsL_at_consumer` discharges the step from `VEnv.WF'` plus
`env ≤ envF`, which is what `coherentOn_cnstOf` has in scope
(`eq_unitEnvLE_of_wf'` pins `env = unitEnvLE`).

This is still **one block**: no parameters, no indices, one constructor with no fields.  What
it settles is that neither large elimination nor a genuinely functional recursor value is an
obstacle in principle.  A block with recursive fields needs the fixed point
(`SetModel/IndInterp.lean`), and that is untouched here.
-/

namespace Lean4Lean.SetModel.UnitAudit
open Lean4Lean LO LO.FirstOrder LO.FirstOrder.SetTheory


/-! ## 1. The block, its shapes -/

/-- `motive : Unit1 → Sort u`, at the recursor's own level numbering (`u = .param 0`). -/
abbrev motTyL : VExpr := .forallE (.const `Unit1 []) (.sort (.param 0))

/-- `motive : Unit1 → Sort u` with `u` substituted. -/
abbrev motTyU (u : VLevel) : VExpr := .forallE (.const `Unit1 []) (.sort u)

theorem unitDeclLE_motives : unitDeclLE.motives = [motTyL] := rfl
theorem unitDeclLE_minors : unitDeclLE.minors = [minTy] := rfl
theorem unitDeclLE_typeConsts : unitDeclLE.typeConsts = [(`Unit1, ⟨0, .sort .zero⟩)] := rfl
theorem unitDeclLE_ctorConsts :
    unitDeclLE.ctorConsts = [(`Unit1.mk, ⟨0, .const `Unit1 []⟩)] := rfl
theorem unitDeclLE_recConsts :
    unitDeclLE.recConsts = [(recN, ⟨1, unitDeclLE.recType 0⟩)] := rfl
theorem unitDeclLE_allConsts :
    unitDeclLE.allConsts =
      [(`Unit1, ⟨0, .sort .zero⟩), (`Unit1.mk, ⟨0, .const `Unit1 []⟩),
       (recN, ⟨1, unitDeclLE.recType 0⟩)] := rfl
theorem unitDeclLE_allNames : unitDeclLE.allNames = [`Unit1, `Unit1.mk, recN] := rfl
theorem unitDeclLE_iotaCtx : unitDeclLE.iotaCtx unitCtor = [motTyL, minTy] := rfl
theorem unitDeclLE_iotaRules : unitDeclLE.iotaRules = [unitDeclLE.iotaRule 0 0 unitCtor] := rfl
theorem unitRuleL_uvars : (unitDeclLE.iotaRule 0 0 unitCtor).uvars = 1 := rfl

/-- **The one place the recursor's *own* level shows up in the ι-rule**: `iotaLhs` builds the
recursor constant at `VLevel.params D.recUvars = [.param 0]`, so `instL [u]` puts `u` there.
This is the only syntactic difference from the small-eliminating rule. -/
theorem unitRuleL_lhs_instL (u : VLevel) :
    (unitDeclLE.iotaRule 0 0 unitCtor).lhs.instL [u] =
      .lam (motTyU u) (.lam minTy
        (.app (.app (.app (.const recN [u]) (.bvar 1)) (.bvar 0))
          (.const `Unit1.mk []))) := rfl

theorem unitRuleL_rhs_instL (u : VLevel) :
    (unitDeclLE.iotaRule 0 0 unitCtor).rhs.instL [u] =
      .lam (motTyU u) (.lam minTy
        (.app (.app (.lam (motTyU u) (.lam minTy (.bvar 0))) (.bvar 1)) (.bvar 0))) := rfl

theorem unitRuleL_type_instL (u : VLevel) :
    (unitDeclLE.iotaRule 0 0 unitCtor).type.instL [u] =
      .forallE (motTyU u) (.forallE minTy (.app (.bvar 1) (.const `Unit1.mk []))) := rfl

theorem unitDeclLE_recType_instL (u : VLevel) :
    (unitDeclLE.recType 0).instL [u] =
      .forallE (motTyU u)
        (.forallE minTy (.forallE (.const `Unit1 []) (.app (.bvar 2) (.bvar 0)))) := rfl

/-! ## 2. The environment -/

/-- The environment `addInduct' unitDeclLE` produces over `VEnv.empty`.  Note the recursor's
`uvars = 1`, and the one ι-rule at `uvars = 1`. -/
def unitEnvLE : VEnv where
  constants n :=
    if recN = n then some ⟨1, unitDeclLE.recType 0⟩ else
    if `Unit1.mk = n then some ⟨0, .const `Unit1 []⟩ else
    if `Unit1 = n then some ⟨0, .sort .zero⟩ else none
  defeqs x := x = unitDeclLE.iotaRule 0 0 unitCtor ∨ False

theorem unitEnvLE_add : VEnv.empty.addInduct' unitDeclLE = some unitEnvLE := rfl

theorem unitEnvLE_Unit1 : unitEnvLE.constants `Unit1 = some ⟨0, .sort .zero⟩ := rfl
theorem unitEnvLE_mk : unitEnvLE.constants `Unit1.mk = some ⟨0, .const `Unit1 []⟩ := rfl
theorem unitEnvLE_rec : unitEnvLE.constants recN = some ⟨1, unitDeclLE.recType 0⟩ := rfl

/-- **`unitDeclLE` is well formed over `VEnv.empty`.**  The only field that differs from
`unitDecl_WF` is `isLE`, discharged by `unitDeclLE_LECond`. -/
theorem unitDeclLE_WF : unitDeclLE.WF VEnv.empty where
  types_ne := by simp [unitDeclLE, unitDecl]
  params := trivial
  types := by
    intro T hT
    simp only [unitDeclLE, unitDecl, List.mem_cons, List.not_mem_nil, or_false] at hT
    subst hT
    exact { indices := trivial
            isType := ⟨_, .sortDF trivial trivial (.refl _)⟩
            canon := ⟨_, .sortDF trivial trivial (.refl _)⟩ }
  ctors := by
    intro env₁ he j T hT C hC
    match j, hT with
    | 0, hT =>
      simp only [unitDeclLE, unitDecl, List.getElem?_cons_zero, Option.some.injEq] at hT
      subst hT
      simp only [unitTy, List.mem_cons, List.not_mem_nil, or_false] at hC
      subst hC
      have hU : env₁.constants `Unit1 = some ⟨0, .sort .zero⟩ :=
        VEnv.addConstList_constants (cs := unitDeclLE.typeConsts) he
          (`Unit1, ⟨0, .sort .zero⟩) (by simp [unitDeclLE, unitDecl, unitTy,
            VInductDecl'.typeConsts])
      exact { params_len := rfl
              params_eq := .zero
              fields := nofun
              args_len := rfl
              args_fresh := nofun
              args_ty := .nil
              result := .constDF hU nofun nofun rfl .nil }
  isLE := fun _ ↦ unitDeclLE_LECond

theorem unitDeclLE_history : VEnv.WF' [.induct unitDeclLE] unitEnvLE :=
  .decl (.induct unitDeclLE_WF unitEnvLE_add) .empty

theorem eq_unitEnvLE_of_wf' {env : VEnv} (h : VEnv.WF' [.induct unitDeclLE] env) :
    env = unitEnvLE := by
  obtain ⟨env₀, hd, hds⟩ := wf'_cons_inv h
  cases hds
  cases hd with
  | induct _ hadd => exact Option.some_injective _ (unitEnvLE_add.symm.trans hadd).symm

/-! ## 3. Typing derivations in `unitEnvLE`, at an arbitrary `u` -/

section Typing

variable {Γ : List VExpr} {nv : ℕ} {u : VLevel} (hu : u.WF nv)

theorem hasTypeL_Unit1 : unitEnvLE.HasType nv Γ (.const `Unit1 []) (.sort .zero) :=
  .constDF unitEnvLE_Unit1 nofun nofun rfl .nil

theorem hasTypeL_mk : unitEnvLE.HasType nv Γ (.const `Unit1.mk []) (.const `Unit1 []) :=
  .constDF unitEnvLE_mk nofun nofun rfl .nil

include hu in
theorem hasTypeL_rec :
    unitEnvLE.HasType nv Γ (.const recN [u]) ((unitDeclLE.recType 0).instL [u]) := by
  refine .constDF unitEnvLE_rec ?_ ?_ rfl (.cons (.refl _) .nil)
  · intro l hl; simp only [List.mem_singleton] at hl; exact hl ▸ hu
  · intro l hl; simp only [List.mem_singleton] at hl; exact hl ▸ hu

include hu in
theorem hasTypeL_motTy :
    unitEnvLE.HasType nv Γ (motTyU u) (.sort (.imax .zero (.succ u))) :=
  .forallEDF hasTypeL_Unit1 (.sortDF hu hu (.refl _))

theorem hasTypeL_bvar0 : unitEnvLE.HasType nv (motTyU u :: Γ) (.bvar 0) (motTyU u) :=
  .bvar .zero

theorem hasTypeL_bvar1 {A : VExpr} :
    unitEnvLE.HasType nv (A :: motTyU u :: Γ) (.bvar 1) (motTyU u) :=
  .bvar (.succ .zero)

theorem hasTypeL_bvar2 {A B : VExpr} :
    unitEnvLE.HasType nv (A :: B :: motTyU u :: Γ) (.bvar 2) (motTyU u) :=
  .bvar (.succ (.succ .zero))

/-- `motive mk : Sort u`. -/
theorem hasTypeL_minTy : unitEnvLE.HasType nv (motTyU u :: Γ) minTy (.sort u) :=
  .appDF hasTypeL_bvar0 hasTypeL_mk

/-! ### The block's spine is `OnCtx`-well-formed

Added 2026-09-02 with the `OnCtx` guard on `PropSplit`'s two fields
(`SetModel/Interp.lean`).  Three lemmas, each one entry above the last by the typing
derivation already present; the readings below take `OnCtx Γ` and build what they need. -/

theorem onCtxL_unitTy {Γ : List VExpr} (hΓ : OnCtx Γ (unitEnvLE.IsType nv)) :
    OnCtx (VExpr.const `Unit1 [] :: Γ) (unitEnvLE.IsType nv) := ⟨hΓ, _, hasTypeL_Unit1⟩

theorem onCtxL_mot (hu : u.WF nv) {Γ : List VExpr}
    (hΓ : OnCtx Γ (unitEnvLE.IsType nv)) :
    OnCtx (motTyU u :: Γ) (unitEnvLE.IsType nv) := ⟨hΓ, _, hasTypeL_motTy hu⟩

theorem onCtxL_min (hu : u.WF nv) {Γ : List VExpr}
    (hΓ : OnCtx Γ (unitEnvLE.IsType nv)) :
    OnCtx (minTy :: motTyU u :: Γ) (unitEnvLE.IsType nv) :=
  ⟨onCtxL_mot hu hΓ, _, hasTypeL_minTy⟩

theorem onCtxL_unit (hu : u.WF nv) {Γ : List VExpr}
    (hΓ : OnCtx Γ (unitEnvLE.IsType nv)) :
    OnCtx (VExpr.const `Unit1 [] :: minTy :: motTyU u :: Γ) (unitEnvLE.IsType nv) :=
  ⟨onCtxL_min hu hΓ, _, hasTypeL_Unit1⟩

theorem hasTypeL_minTy1 {A : VExpr} :
    unitEnvLE.HasType nv (A :: motTyU u :: Γ)
      (.app (.bvar 1) (.const `Unit1.mk [])) (.sort u) :=
  .appDF hasTypeL_bvar1 hasTypeL_mk

/-- `motive t : Sort u` — the recursor's result. -/
theorem hasTypeL_recBody :
    unitEnvLE.HasType nv (.const `Unit1 [] :: minTy :: motTyU u :: Γ)
      (.app (.bvar 2) (.bvar 0)) (.sort u) :=
  .appDF hasTypeL_bvar2 (.bvar .zero)

theorem hasTypeL_recB2 :
    unitEnvLE.HasType nv (minTy :: motTyU u :: Γ)
      (.forallE (.const `Unit1 []) (.app (.bvar 2) (.bvar 0)))
      (.sort (.imax .zero u)) :=
  .forallEDF hasTypeL_Unit1 hasTypeL_recBody

theorem hasTypeL_recB1 :
    unitEnvLE.HasType nv (motTyU u :: Γ)
      (.forallE minTy (.forallE (.const `Unit1 []) (.app (.bvar 2) (.bvar 0))))
      (.sort (.imax u (.imax .zero u))) :=
  .forallEDF hasTypeL_minTy hasTypeL_recB2

theorem hasTypeL_ruleB1 :
    unitEnvLE.HasType nv (motTyU u :: Γ)
      (.forallE minTy (.app (.bvar 1) (.const `Unit1.mk [])))
      (.sort (.imax u u)) :=
  .forallEDF hasTypeL_minTy hasTypeL_minTy1

include hu in
theorem hasTypeL_iotaLhsBody :
    unitEnvLE.HasType nv (minTy :: motTyU u :: Γ)
      (.app (.app (.app (.const recN [u]) (.bvar 1)) (.bvar 0)) (.const `Unit1.mk []))
      (.app (.bvar 1) (.const `Unit1.mk [])) := by
  have h1 : unitEnvLE.HasType nv (minTy :: motTyU u :: Γ) (.const recN [u])
      ((unitDeclLE.recType 0).instL [u]) := hasTypeL_rec hu
  rw [unitDeclLE_recType_instL] at h1
  have h2 := VEnv.IsDefEq.appDF h1 (hasTypeL_bvar1 (Γ := Γ) (u := u) (A := minTy))
  have h3 := VEnv.IsDefEq.appDF h2 (VEnv.IsDefEq.bvar (A := minTy.lift) Lookup.zero)
  exact .appDF h3 hasTypeL_mk

include hu in
theorem hasTypeL_iotaLhsLam :
    unitEnvLE.HasType nv (motTyU u :: Γ) (.lam minTy
        (.app (.app (.app (.const recN [u]) (.bvar 1)) (.bvar 0)) (.const `Unit1.mk [])))
      (.forallE minTy (.app (.bvar 1) (.const `Unit1.mk []))) :=
  .lamDF hasTypeL_minTy (hasTypeL_iotaLhsBody hu)

include hu in
theorem hasTypeL_iotaLam :
    unitEnvLE.HasType nv Γ (.lam (motTyU u) (.lam minTy (.bvar 0)))
      (.forallE (motTyU u) (.forallE minTy (.app (.bvar 1) (.const `Unit1.mk [])))) :=
  .lamDF (hasTypeL_motTy hu) (.lamDF hasTypeL_minTy (.bvar .zero))

include hu in
theorem hasTypeL_iotaRhsBody :
    unitEnvLE.HasType nv (minTy :: motTyU u :: Γ)
      (.app (.app (.lam (motTyU u) (.lam minTy (.bvar 0))) (.bvar 1)) (.bvar 0))
      (.app (.bvar 1) (.const `Unit1.mk [])) :=
  .appDF (.appDF (hasTypeL_iotaLam hu) hasTypeL_bvar1) (.bvar .zero)

include hu in
theorem hasTypeL_iotaRhsLam :
    unitEnvLE.HasType nv (motTyU u :: Γ) (.lam minTy
        (.app (.app (.lam (motTyU u) (.lam minTy (.bvar 0))) (.bvar 1)) (.bvar 0)))
      (.forallE minTy (.app (.bvar 1) (.const `Unit1.mk []))) :=
  .lamDF hasTypeL_minTy (hasTypeL_iotaRhsBody hu)

end Typing

/-! ## 4. Two general lemmas about `mkForallType`

Neither mentions `interp`.  They are what lets the oracle's value be written **without**
reference to `interp` — which it must be, since `interp` reads `M.cnst`, i.e. the oracle. -/

section Combinators

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- **An extensional entry into `mkForallType`.**  `mem_mkForallType_iff` phrases membership
through `mkFamUnion`, which is awkward to hit from a set built elsewhere; this asks only that
`f` be a graph over `G ρ` landing in `F ρ`. -/
theorem mem_mkForallType_of_graph {G : V → V} {hG : ℒₛₑₜ-function₁[V] G}
    {F : V → V → V} {hF : ℒₛₑₜ-function₂[V] F} {ρ f : V}
    (hsub : ∀ p ∈ f, ∃ v ∈ G ρ, ∃ y, p = (⟨v, y⟩ₖ : V) ∧ y ∈ F ρ v)
    (htot : ∀ v ∈ G ρ, ∃! y, (⟨v, y⟩ₖ : V) ∈ f) :
    f ∈ mkForallType G hG F hF ρ := by
  refine mem_mkForallType_iff.mpr ⟨mem_function.intro (fun p hp ↦ ?_) htot, ?_⟩
  · obtain ⟨v, hv, y, rfl, hy⟩ := hsub p hp
    exact kpair_mem_iff.mpr ⟨hv, mem_mkFamUnion_iff.mpr ⟨v, hv, hy⟩⟩
  · intro v _ y hy
    obtain ⟨v', hv', y', he, hy'⟩ := hsub _ hy
    obtain ⟨rfl, rfl⟩ := kpair_inj he
    exact hy'

/-- **`mkLam` lands in `mkForallType` when the two domains merely *agree*.**
`InterpSound.mkLam_mem_mkForallType` needs the domain function to be the *same term* on both
sides, which is impossible when the `mkLam` is the oracle's value and the `mkForallType` is
`interp`'s. -/
theorem mkLam_mem_mkForallType_of_dom
    {G G' : V → V} {hG : ℒₛₑₜ-function₁[V] G} {hG' : ℒₛₑₜ-function₁[V] G'}
    {F F' : V → V → V} {hF : ℒₛₑₜ-function₂[V] F} {hF' : ℒₛₑₜ-function₂[V] F'}
    {ρ ρ' : V} (hdom : G' ρ' = G ρ) (hcod : ∀ v ∈ G ρ, F' ρ' v ∈ F ρ v) :
    mkLam G' hG' F' hF' ρ' ∈ mkForallType G hG F hF ρ := by
  refine mem_mkForallType_of_graph (fun p hp ↦ ?_) (fun v hv ↦ ?_)
  · obtain ⟨v, hv, rfl⟩ := mem_mkLam_iff.mp hp
    rw [hdom] at hv
    exact ⟨v, hv, _, rfl, hcod v hv⟩
  · refine ⟨F' ρ' v, mem_mkLam_iff.mpr ⟨v, by rw [hdom]; exact hv, rfl⟩, fun y hy ↦ ?_⟩
    obtain ⟨v', hv', he⟩ := mem_mkLam_iff.mp hy
    obtain ⟨rfl, rfl⟩ := kpair_inj he
    rfl

/-- `⋃_{v ∈ {a}} Y = Y`. -/
theorem mkFamUnion_singleton_const {G : V → V} {hG : ℒₛₑₜ-function₁[V] G}
    {F : V → V → V} {hF : ℒₛₑₜ-function₂[V] F} {ρ a Y : V}
    (hG0 : G ρ = ({a} : V)) (hF0 : F ρ a = Y) : mkFamUnion G hG F hF ρ = Y := by
  rw [mem_ext_iff]
  intro y
  rw [mem_mkFamUnion_iff]
  constructor
  · rintro ⟨v, hv, hy⟩
    rw [hG0] at hv
    obtain rfl := mem_singleton_iff.mp hv
    rwa [hF0] at hy
  · intro hy
    exact ⟨a, by rw [hG0]; simp, by rwa [hF0]⟩

/-- **A `∀` over a singleton domain with a constant codomain is the function space.**  This is
the shape of the recursor's motive binder: `Unit1 → Sort u` denotes `U_n ^ {•}`. -/
theorem mkForallType_singleton_const {G : V → V} {hG : ℒₛₑₜ-function₁[V] G}
    {F : V → V → V} {hF : ℒₛₑₜ-function₂[V] F} {ρ a Y : V}
    (hG0 : G ρ = ({a} : V)) (hF0 : ∀ v ∈ ({a} : V), F ρ v = Y) :
    mkForallType G hG F hF ρ = (Y ^ ({a} : V) : V) := by
  have hFU : mkFamUnion G hG F hF ρ = Y :=
    mkFamUnion_singleton_const hG0 (hF0 a (by simp))
  rw [mem_ext_iff]
  intro f
  rw [mem_mkForallType_iff, hFU, hG0]
  refine ⟨fun h ↦ h.1, fun h ↦ ⟨h, fun v hv y hy ↦ ?_⟩⟩
  rw [hF0 v hv]
  exact (mem_of_mem_functions h hy).2

/-- `mkLam` is determined by its domain *set* and its body's values on it. -/
theorem mkLam_ext {G G' : V → V} {hG : ℒₛₑₜ-function₁[V] G} {hG' : ℒₛₑₜ-function₁[V] G'}
    {F F' : V → V → V} {hF : ℒₛₑₜ-function₂[V] F} {hF' : ℒₛₑₜ-function₂[V] F'}
    {ρ ρ' : V} (hdom : G' ρ' = G ρ) (h : ∀ v ∈ G ρ, F' ρ' v = F ρ v) :
    mkLam G' hG' F' hF' ρ' = mkLam G hG F hF ρ := by
  rw [mem_ext_iff]
  intro y
  rw [mem_mkLam_iff, mem_mkLam_iff, hdom]
  exact exists_congr fun v ↦ and_congr_right fun hv ↦ by rw [h v hv]

end Combinators

/-! ## 5. The oracle for the large eliminator

The value must be written **without** `interp`: `interp` reads `M.cnst`, so an oracle defined
through `interp` at the recursor's own type would be circular.  §4's two lemmas are what make
that possible. -/

section Oracle

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- `λ t : Unit1, m` — the innermost layer.  `m` rides in the valuation slot. -/
noncomputable def recFn3 : V → V :=
  mkLam (fun _ ↦ ({pt} : V)) (by definability) (fun ρ _ ↦ ρ) (by definability)

theorem recFn3_definable : ℒₛₑₜ-function₁[V] (recFn3 (V := V)) := mkLam_definable _ _ _ _

theorem recFn3_apply {m t : V} (ht : t ∈ ({pt} : V)) : (recFn3 m) ‘ t = m :=
  mkLam_value (G := fun _ ↦ ({pt} : V)) ht

/-- `λ (m : motive mk) (t : Unit1), m`.  `f` rides in the valuation slot, and the domain
`f ‘ •` is exactly `⟦motive mk⟧`. -/
noncomputable def recFn2 : V → V :=
  mkLam (fun ρ ↦ ρ ‘ (pt : V)) (by definability) (fun _ m ↦ recFn3 m)
    (by have := recFn3_definable (V := V); definability)

theorem recFn2_definable : ℒₛₑₜ-function₁[V] (recFn2 (V := V)) := mkLam_definable _ _ _ _

theorem recFn2_apply {f m : V} (hm : m ∈ f ‘ (pt : V)) : (recFn2 f) ‘ m = recFn3 m :=
  mkLam_value (G := fun ρ ↦ ρ ‘ (pt : V)) hm

/-- **`λ (motive : Unit1 → Sort u) (m : motive mk) (t : Unit1), m`** — the value the oracle
has to hand `Unit1.rec` once the elimination universe is not `Prop`.  Three genuine `mkLam`
layers; `•` is not an option there (`pt_not_mem_mkForallType_of_nonempty`). -/
noncomputable def recFnL (κ : ℕ → V) (n : ℕ) : V :=
  mkLam (fun _ ↦ ((U κ n) ^ ({pt} : V) : V)) (by definability) (fun _ f ↦ recFn2 f)
    (by have := recFn2_definable (V := V); definability) ∅

theorem recFnL_apply {κ : ℕ → V} {n : ℕ} {f : V} (hf : f ∈ ((U κ n) ^ ({pt} : V) : V)) :
    (recFnL κ n) ‘ f = recFn2 f :=
  mkLam_value (G := fun _ ↦ ((U κ n) ^ ({pt} : V) : V)) hf

/-- **The oracle.**  `Unit1 ↦ {•}` as before; `Unit1.rec` branches on whether the elimination
universe evaluates to `0`.  The branch is **forced**, not a convenience: at `0` the recursor's
type is a proposition and `•` is its only possible value, and at `n ≠ 0` it is a function
space in which `• = ∅` does not lie.  So a large eliminator's oracle value is *not uniform in
the level*, which is the model-side shadow of `Prop`'s collapse. -/
noncomputable def unitOracleL (κ : ℕ → V) (ls : List ℕ) : Name → List VLevel → V :=
  fun m us ↦
    if m = `Unit1 then ({pt} : V)
    else if m = recN then
      (if (us.headD .zero).eval ls = 0 then (pt : V) else recFnL κ ((us.headD .zero).eval ls))
    else (pt : V)

noncomputable def unitML (κ : ℕ → V) (ls : List ℕ) : ModelData V := ⟨κ, ls, unitOracleL κ ls⟩

@[simp] theorem unitOracleL_Unit1 (κ : ℕ → V) (ls : List ℕ) (us : List VLevel) :
    unitOracleL κ ls `Unit1 us = ({pt} : V) := by simp [unitOracleL]

@[simp] theorem unitOracleL_mk (κ : ℕ → V) (ls : List ℕ) (us : List VLevel) :
    unitOracleL κ ls `Unit1.mk us = (pt : V) := by
  simp [unitOracleL, recN, Lean.mkRecName]

theorem unitOracleL_rec (κ : ℕ → V) (ls : List ℕ) (u : VLevel) :
    unitOracleL κ ls recN [u] =
      (if u.eval ls = 0 then (pt : V) else recFnL κ (u.eval ls)) := by
  simp [unitOracleL, recN, Lean.mkRecName]

theorem unitML_cnst (κ : ℕ → V) (ls : List ℕ) : (unitML κ ls).cnst = unitOracleL κ ls := rfl
theorem unitML_ls (κ : ℕ → V) (ls : List ℕ) : (unitML κ ls).ls = ls := rfl
theorem unitML_kappa (κ : ℕ → V) (ls : List ℕ) : (unitML κ ls).κ = κ := rfl

/-! ### The oracle's `congr` field: it depends on `us` only through `u.eval ls` -/

theorem unitOracleL_congr_head (ls : List ℕ) {us us' : List VLevel}
    (h : List.Forall₂ (· ≈ ·) us us') :
    (us.headD .zero).eval ls = (us'.headD .zero).eval ls := by
  cases h with
  | nil => rfl
  | cons hx _ => exact VLevel.equiv_def.mp hx ls

theorem unitOracleL_congr (κ : ℕ → V) (ls : List ℕ) (m : Name) {us us' : List VLevel}
    (h : List.Forall₂ (· ≈ ·) us us') :
    unitOracleL κ ls m us = (unitOracleL κ ls m us' : V) := by
  simp only [unitOracleL]
  rw [unitOracleL_congr_head ls h]

end Oracle

/-! ## 6. The proof-splitting decisions, as `↔ u.eval ls = 0`

Every decision that varies is stated as an **iff**, so the `= 0` and `≠ 0` slices share them
and the split is visible rather than buried. -/

section Split

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {envF : VEnv} {nv : ℕ} (L : PropSplit envF nv) (κ : ℕ → V) (ls : List ℕ)
variable {u : VLevel} (hu : u.WF nv) (hle : unitEnvLE ≤ envF)

theorem hasTypeL_sortU {Γ : List VExpr} (h : u.WF nv) :
    unitEnvLE.HasType nv Γ (.sort u) (.sort (.succ u)) := .sortDF h h (.refl _)

include hu hle in
/-- `Sort u` is never a proposition — its own sort evaluates to `n + 1`. -/
theorem not_isPropL_sortU (Γ : List VExpr) (hΓ : OnCtx Γ (unitEnvLE.IsType nv)) :
    ¬ L.IsProp (unitML κ ls) Γ (.sort u) := by
  rw [isProp_iff hle hΓ (hasTypeL_sortU hu) (u := .succ u) hu]
  simp [VLevel.eval, unitML]

include hu hle in
theorem not_isProofL_bvar0 (Γ : List VExpr) (hΓ : OnCtx Γ (unitEnvLE.IsType nv)) :
    ¬ L.IsProof (unitML κ ls) (motTyU u :: Γ) (.bvar 0) := by
  rw [isProof_iff hle (onCtxL_mot hu hΓ) hasTypeL_bvar0 (hasTypeL_motTy hu)
    (u := .imax .zero (.succ u)) ⟨trivial, hu⟩]
  rw [show (VLevel.imax .zero (.succ u)).eval (unitML κ ls).ls
      = Lean.Nat.imax 0 (u.eval ls + 1) from rfl]
  simp [imax_eq_zero_iff]

include hu hle in
theorem not_isProofL_bvar1 {A : VExpr} (Γ : List VExpr) (hΓ : OnCtx (A :: motTyU u :: Γ) (unitEnvLE.IsType nv)) :
    ¬ L.IsProof (unitML κ ls) (A :: motTyU u :: Γ) (.bvar 1) := by
  rw [isProof_iff hle hΓ hasTypeL_bvar1 (hasTypeL_motTy hu)
    (u := .imax .zero (.succ u)) ⟨trivial, hu⟩]
  rw [show (VLevel.imax .zero (.succ u)).eval (unitML κ ls).ls
      = Lean.Nat.imax 0 (u.eval ls + 1) from rfl]
  simp [imax_eq_zero_iff]

include hu hle in
theorem not_isProofL_bvar2 {A B : VExpr} (Γ : List VExpr) (hΓ : OnCtx (A :: B :: motTyU u :: Γ) (unitEnvLE.IsType nv)) :
    ¬ L.IsProof (unitML κ ls) (A :: B :: motTyU u :: Γ) (.bvar 2) := by
  rw [isProof_iff hle hΓ hasTypeL_bvar2 (hasTypeL_motTy hu)
    (u := .imax .zero (.succ u)) ⟨trivial, hu⟩]
  rw [show (VLevel.imax .zero (.succ u)).eval (unitML κ ls).ls
      = Lean.Nat.imax 0 (u.eval ls + 1) from rfl]
  simp [imax_eq_zero_iff]

include hu hle in
theorem isPropL_recB1_iff (Γ : List VExpr) (hΓ : OnCtx Γ (unitEnvLE.IsType nv)) :
    L.IsProp (unitML κ ls) (motTyU u :: Γ)
      (.forallE minTy (.forallE (.const `Unit1 []) (.app (.bvar 2) (.bvar 0))))
    ↔ u.eval ls = 0 := by
  rw [isProp_iff hle (onCtxL_mot hu hΓ) hasTypeL_recB1 (u := .imax u (.imax .zero u)) ⟨hu, trivial, hu⟩]
  rw [show (VLevel.imax u (.imax .zero u)).eval (unitML κ ls).ls
      = Lean.Nat.imax (u.eval ls) (Lean.Nat.imax 0 (u.eval ls)) from rfl]
  rw [imax_eq_zero_iff, imax_eq_zero_iff]

include hu hle in
theorem isPropL_recB2_iff (Γ : List VExpr) (hΓ : OnCtx Γ (unitEnvLE.IsType nv)) :
    L.IsProp (unitML κ ls) (minTy :: motTyU u :: Γ)
      (.forallE (.const `Unit1 []) (.app (.bvar 2) (.bvar 0)))
    ↔ u.eval ls = 0 := by
  rw [isProp_iff hle (onCtxL_min hu hΓ) hasTypeL_recB2 (u := .imax .zero u) ⟨trivial, hu⟩]
  rw [show (VLevel.imax .zero u).eval (unitML κ ls).ls
      = Lean.Nat.imax 0 (u.eval ls) from rfl, imax_eq_zero_iff]

include hu hle in
theorem isPropL_recB3_iff (Γ : List VExpr) (hΓ : OnCtx Γ (unitEnvLE.IsType nv)) :
    L.IsProp (unitML κ ls) (.const `Unit1 [] :: minTy :: motTyU u :: Γ)
      (.app (.bvar 2) (.bvar 0))
    ↔ u.eval ls = 0 := by
  rw [isProp_iff hle (onCtxL_unit hu hΓ) hasTypeL_recBody (u := u) hu, unitML_ls]

include hu hle in
theorem isPropL_ruleB1_iff (Γ : List VExpr) (hΓ : OnCtx Γ (unitEnvLE.IsType nv)) :
    L.IsProp (unitML κ ls) (motTyU u :: Γ)
      (.forallE minTy (.app (.bvar 1) (.const `Unit1.mk [])))
    ↔ u.eval ls = 0 := by
  rw [isProp_iff hle (onCtxL_mot hu hΓ) hasTypeL_ruleB1 (u := .imax u u) ⟨hu, hu⟩]
  rw [show (VLevel.imax u u).eval (unitML κ ls).ls
      = Lean.Nat.imax (u.eval ls) (u.eval ls) from rfl, imax_eq_zero_iff]

include hu hle in
theorem isPropL_ruleB2_iff {A : VExpr} (Γ : List VExpr) (hΓ : OnCtx (A :: motTyU u :: Γ) (unitEnvLE.IsType nv)) :
    L.IsProp (unitML κ ls) (A :: motTyU u :: Γ) (.app (.bvar 1) (.const `Unit1.mk []))
    ↔ u.eval ls = 0 := by
  rw [isProp_iff hle hΓ hasTypeL_minTy1 (u := u) hu, unitML_ls]

include hu hle in
theorem isProofL_iotaLhsLam_iff (Γ : List VExpr) (hΓ : OnCtx Γ (unitEnvLE.IsType nv)) :
    L.IsProof (unitML κ ls) (motTyU u :: Γ) (.lam minTy
      (.app (.app (.app (.const recN [u]) (.bvar 1)) (.bvar 0)) (.const `Unit1.mk [])))
    ↔ u.eval ls = 0 := by
  rw [isProof_iff hle (onCtxL_mot hu hΓ) (hasTypeL_iotaLhsLam hu) hasTypeL_ruleB1 (u := .imax u u) ⟨hu, hu⟩]
  rw [show (VLevel.imax u u).eval (unitML κ ls).ls
      = Lean.Nat.imax (u.eval ls) (u.eval ls) from rfl, imax_eq_zero_iff]

include hu hle in
theorem isProofL_iotaRhsLam_iff (Γ : List VExpr) (hΓ : OnCtx Γ (unitEnvLE.IsType nv)) :
    L.IsProof (unitML κ ls) (motTyU u :: Γ) (.lam minTy
      (.app (.app (.lam (motTyU u) (.lam minTy (.bvar 0))) (.bvar 1)) (.bvar 0)))
    ↔ u.eval ls = 0 := by
  rw [isProof_iff hle (onCtxL_mot hu hΓ) (hasTypeL_iotaRhsLam hu) hasTypeL_ruleB1 (u := .imax u u) ⟨hu, hu⟩]
  rw [show (VLevel.imax u u).eval (unitML κ ls).ls
      = Lean.Nat.imax (u.eval ls) (u.eval ls) from rfl, imax_eq_zero_iff]

include hu hle in
theorem isProofL_iotaLhsBody_iff (Γ : List VExpr) (hΓ : OnCtx Γ (unitEnvLE.IsType nv)) :
    L.IsProof (unitML κ ls) (minTy :: motTyU u :: Γ)
      (.app (.app (.app (.const recN [u]) (.bvar 1)) (.bvar 0)) (.const `Unit1.mk []))
    ↔ u.eval ls = 0 := by
  rw [isProof_iff hle (onCtxL_min hu hΓ) (hasTypeL_iotaLhsBody hu) hasTypeL_minTy1 (u := u) hu, unitML_ls]

include hu hle in
theorem isProofL_iotaRhsBody_iff (Γ : List VExpr) (hΓ : OnCtx Γ (unitEnvLE.IsType nv)) :
    L.IsProof (unitML κ ls) (minTy :: motTyU u :: Γ)
      (.app (.app (.lam (motTyU u) (.lam minTy (.bvar 0))) (.bvar 1)) (.bvar 0))
    ↔ u.eval ls = 0 := by
  rw [isProof_iff hle (onCtxL_min hu hΓ) (hasTypeL_iotaRhsBody hu) hasTypeL_minTy1 (u := u) hu, unitML_ls]

end Split

/-! ## 7. The denotations, once and for all -/

section Denot

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ} (L : PropSplit envF nv) (κ : ℕ → V) (ls : List ℕ)
variable {u : VLevel} (hu : u.WF nv) (hle : unitEnvLE ≤ envF)

theorem interpL_Unit1 (Γ : List VExpr) (ρ : V) :
    (interp (unitML κ ls) L Γ (.const `Unit1 [])).toFun ρ = ({pt} : V) := by
  rw [interp_const, unitML_cnst]; exact unitOracleL_Unit1 _ _ _

theorem interpL_mk (Γ : List VExpr) (ρ : V) :
    (interp (unitML κ ls) L Γ (.const `Unit1.mk [])).toFun ρ = (pt : V) := by
  rw [interp_const, unitML_cnst]; exact unitOracleL_mk _ _ _

include hu hle in
/-- **The motive binder's domain is the function space `U_n ^ {•}`.**  This is the equation the
oracle's value is built against, and it is why the value can avoid mentioning `interp`. -/
theorem interpL_motTyU (Γ : List VExpr) (hΓ : OnCtx Γ (unitEnvLE.IsType nv)) (ρ : V) :
    (interp (unitML κ ls) L Γ (motTyU u)).toFun ρ
      = ((U κ (u.eval ls)) ^ ({pt} : V) : V) := by
  rw [interp_forallE_type (unitML κ ls) L
    (not_isPropL_sortU L κ ls hu hle _ (onCtxL_unitTy hΓ))]
  refine mkForallType_singleton_const (interpL_Unit1 L κ ls Γ ρ) (fun v _ ↦ ?_)
  rw [interp_sort, unitML_kappa, unitML_ls]

include hu hle in
/-- Hence every motive value applies at `•` into `U_n`. -/
theorem motiveL_app_mem_U {Γ : List VExpr} (hΓ : OnCtx Γ (unitEnvLE.IsType nv)) {ρ f : V}
    (hf : f ∈ (interp (unitML κ ls) L Γ (motTyU u)).toFun ρ) :
    f ‘ (pt : V) ∈ U κ (u.eval ls) := by
  rw [interpL_motTyU L κ ls hu hle _ hΓ] at hf
  have hpt : (pt : V) ∈ ({pt} : V) := by simp
  obtain ⟨y, hy, -⟩ := (mem_function_iff.1 hf).2 pt hpt
  have : IsFunction f := IsFunction.of_mem hf
  have hg : (⟨pt, f ‘ (pt : V)⟩ₖ : V) ∈ f := by rw [value_eq_of_kpair_mem hy]; exact hy
  exact (mem_of_mem_functions hf hg).2

include hu hle in
/-- `⟦motive mk⟧` in the context `motTyU u :: Γ`: the motive sits at index `|Γ|`. -/
theorem interpL_minTy_at (Γ : List VExpr) (hΓ : OnCtx Γ (unitEnvLE.IsType nv)) {ρ f : V}
    (hf : ρ ‘ ((Γ.length : ℕ) : V) = f) :
    (interp (unitML κ ls) L (motTyU u :: Γ) minTy).toFun ρ = f ‘ (pt : V) := by
  rw [show minTy = VExpr.app (.bvar 0) (.const `Unit1.mk []) from rfl,
    interp_app_type (unitML κ ls) L (not_isProofL_bvar0 L κ ls hu hle Γ hΓ), interp_bvar,
    interpL_mk L κ ls]
  simp only [List.length_cons]
  rw [show (Γ.length + 1 - 1 - 0 : ℕ) = Γ.length from rfl, hf]

include hu hle in
/-- `⟦motive mk⟧` in the context `[motTyU u]`. -/
theorem interpL_minTy {ρ f : V} (hf : ρ ‘ ((0 : ℕ) : V) = f) :
    (interp (unitML κ ls) L [motTyU u] minTy).toFun ρ = f ‘ (pt : V) :=
  interpL_minTy_at L κ ls hu hle [] trivial hf

include hu hle in
/-- The same one binder in, in the context `[minTy, motTyU u]`. -/
theorem interpL_minTy1 {ρ f : V} (hf : ρ ‘ ((0 : ℕ) : V) = f) :
    (interp (unitML κ ls) L [minTy, motTyU u]
      (.app (.bvar 1) (.const `Unit1.mk []))).toFun ρ = f ‘ (pt : V) := by
  rw [interp_app_type (unitML κ ls) L (not_isProofL_bvar1 L κ ls hu hle [] (onCtxL_min hu (Γ := []) trivial)), interp_bvar,
    interpL_mk L κ ls]
  simp only [List.length_cons, List.length_nil]
  rw [hf]

include hu hle in
/-- `⟦motive t⟧` in the context `[Unit1, minTy, motTyU u]`. -/
theorem interpL_recBody {ρ f t : V} (hf : ρ ‘ ((0 : ℕ) : V) = f)
    (ht : ρ ‘ ((2 : ℕ) : V) = t) :
    (interp (unitML κ ls) L [.const `Unit1 [], minTy, motTyU u]
      (.app (.bvar 2) (.bvar 0))).toFun ρ = f ‘ t := by
  rw [interp_app_type (unitML κ ls) L (not_isProofL_bvar2 L κ ls hu hle [] (onCtxL_unit hu (Γ := []) trivial)), interp_bvar,
    interp_bvar]
  simp only [List.length_cons, List.length_nil]
  rw [show (2 + 1 - 1 - 2 : ℕ) = 0 from rfl, show (2 + 1 - 1 - 0 : ℕ) = 2 from rfl, hf, ht]

/-! ### The three valuations -/

theorem interpCtxL_nil : (∅ : V) ∈ interpCtx (unitML κ ls) L [] := by
  rw [interpCtx_nil]; simp

end Denot

/-! ## 8. Slice A: `u.eval ls = 0` — the `Prop` instantiation, and it is free

Large elimination *into `Prop`* collapses to the small case: every binder of `recType` is
propositional again, and `•` is the value.  So the residual at `unitDeclLE` is only the
`u.eval ls ≠ 0` slice — which answers the question the coordinator asked. -/

section SliceA

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ} (L : PropSplit envF nv) (κ : ℕ → V) (ls : List ℕ)
variable {u : VLevel} (hu : u.WF nv) (hle : unitEnvLE ≤ envF)

include hu hle in
/-- **The recursor's type is inhabited by `•` at every `Prop` instantiation.** -/
theorem pt_mem_interpL_recType_of_zero (h0 : u.eval ls = 0) :
    (pt : V) ∈ (interp (unitML κ ls) L [] ((unitDeclLE.recType 0).instL [u])).toFun ∅ := by
  rw [unitDeclLE_recType_instL]
  have hρ0 := interpCtxL_nil L κ ls
  refine (mem_interp_forallE_prop_iff (unitML κ ls) L
    ((isPropL_recB1_iff L κ ls hu hle [] trivial).mpr h0)).2 ⟨rfl, fun f hf ↦ ?_⟩
  have hf0 : (snoc (∅ : V) f) ‘ ((0 : ℕ) : V) = f :=
    snoc_value_at_len (Γ := []) (unitML κ ls) L hρ0
  have h1 : snoc (∅ : V) f ∈ interpCtx (unitML κ ls) L [motTyU u] :=
    (mem_interpCtx_cons (unitML κ ls) L).mpr ⟨∅, hρ0, f, hf, rfl⟩
  have hUP : f ‘ (pt : V) ∈ (UProp : V) := by
    have h := motiveL_app_mem_U L κ ls hu hle (Γ := []) trivial hf
    rwa [h0, U_zero] at h
  have hmin : (interp (unitML κ ls) L [motTyU u] minTy).toFun (snoc (∅ : V) f) = f ‘ (pt : V) :=
    interpL_minTy L κ ls hu hle hf0
  refine (mem_interp_forallE_prop_iff (unitML κ ls) L
    ((isPropL_recB2_iff L κ ls hu hle [] trivial).mpr h0)).2 ⟨rfl, fun m hm ↦ ?_⟩
  rw [hmin] at hm
  have h2 : snoc (snoc (∅ : V) f) m ∈ interpCtx (unitML κ ls) L [minTy, motTyU u] :=
    (mem_interpCtx_cons (unitML κ ls) L).mpr ⟨snoc ∅ f, h1, m, by rw [hmin]; exact hm, rfl⟩
  refine (mem_interp_forallE_prop_iff (unitML κ ls) L
    ((isPropL_recB3_iff L κ ls hu hle [] trivial).mpr h0)).2 ⟨rfl, fun t ht ↦ ?_⟩
  rw [interpL_Unit1 L κ ls] at ht
  obtain rfl : t = (pt : V) := mem_singleton_iff.mp ht
  have e0 : (snoc (snoc (snoc (∅ : V) f) m) pt) ‘ ((0 : ℕ) : V) = f :=
    ((snoc_value_of_lt (Γ := [minTy, motTyU u]) (unitML κ ls) L h2 (j := 0) (by simp)).trans
      (snoc_value_of_lt (Γ := [motTyU u]) (unitML κ ls) L h1 (j := 0) (by simp))).trans hf0
  have e2 : (snoc (snoc (snoc (∅ : V) f) m) pt) ‘ ((2 : ℕ) : V) = pt :=
    snoc_value_at_len (Γ := [minTy, motTyU u]) (unitML κ ls) L h2
  rw [interpL_recBody L κ ls hu hle e0 e2]
  rcases eq_empty_or_eq_true_of_mem_UProp hUP with h | h
  · exact absurd (h ▸ hm) not_mem_empty
  · rw [h]; simp

include hu hle in
/-- **And the ι-rule holds at every `Prop` instantiation**: both sides are `•`, because both
bodies are proofs. -/
theorem interpL_unitRule_sides_of_zero (h0 : u.eval ls = 0) :
    (interp (unitML κ ls) L []
        ((unitDeclLE.iotaRule 0 0 unitCtor).lhs.instL [u])).toFun ∅ = (pt : V) ∧
    (interp (unitML κ ls) L []
        ((unitDeclLE.iotaRule 0 0 unitCtor).rhs.instL [u])).toFun ∅ = (pt : V) := by
  rw [unitRuleL_lhs_instL, unitRuleL_rhs_instL]
  exact ⟨interp_lam_proof (unitML κ ls) L
      ((isProofL_iotaLhsLam_iff L κ ls hu hle [] trivial).mpr h0) ∅,
    interp_lam_proof (unitML κ ls) L
      ((isProofL_iotaRhsLam_iff L κ ls hu hle [] trivial).mpr h0) ∅⟩

include hu hle in
theorem pt_mem_interpL_unitRule_type_of_zero (h0 : u.eval ls = 0) :
    (pt : V) ∈ (interp (unitML κ ls) L []
      ((unitDeclLE.iotaRule 0 0 unitCtor).type.instL [u])).toFun ∅ := by
  rw [unitRuleL_type_instL]
  have hρ0 := interpCtxL_nil L κ ls
  refine (mem_interp_forallE_prop_iff (unitML κ ls) L
    ((isPropL_ruleB1_iff L κ ls hu hle [] trivial).mpr h0)).2 ⟨rfl, fun f hf ↦ ?_⟩
  have hf0 : (snoc (∅ : V) f) ‘ ((0 : ℕ) : V) = f :=
    snoc_value_at_len (Γ := []) (unitML κ ls) L hρ0
  have h1 : snoc (∅ : V) f ∈ interpCtx (unitML κ ls) L [motTyU u] :=
    (mem_interpCtx_cons (unitML κ ls) L).mpr ⟨∅, hρ0, f, hf, rfl⟩
  have hUP : f ‘ (pt : V) ∈ (UProp : V) := by
    have h := motiveL_app_mem_U L κ ls hu hle (Γ := []) trivial hf
    rwa [h0, U_zero] at h
  have hmin : (interp (unitML κ ls) L [motTyU u] minTy).toFun (snoc (∅ : V) f) = f ‘ (pt : V) :=
    interpL_minTy L κ ls hu hle hf0
  refine (mem_interp_forallE_prop_iff (unitML κ ls) L
    ((isPropL_ruleB2_iff L κ ls hu hle [] (onCtxL_min hu (Γ := []) trivial)).mpr h0)).2 ⟨rfl, fun m hm ↦ ?_⟩
  rw [hmin] at hm
  have e0 : (snoc (snoc (∅ : V) f) m) ‘ ((0 : ℕ) : V) = f :=
    (snoc_value_of_lt (Γ := [motTyU u]) (unitML κ ls) L h1 (j := 0) (by simp)).trans hf0
  rw [interpL_minTy1 L κ ls hu hle e0]
  rcases eq_empty_or_eq_true_of_mem_UProp hUP with h | h
  · exact absurd (h ▸ hm) not_mem_empty
  · rw [h]; simp

end SliceA

/-! ## 9. Slice B: `u.eval ls ≠ 0` — the genuine three-layer function

Here `•` is not a legal value (`pt_not_mem_mkForallType_of_nonempty`), and the oracle hands
`recFnL κ n` instead. -/

section SliceB

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ} (L : PropSplit envF nv) (κ : ℕ → V) (ls : List ℕ)
variable {u : VLevel} (hu : u.WF nv) (hle : unitEnvLE ≤ envF) (hn : u.eval ls ≠ 0)

include hu hle hn in
/-- **The three-layer `mkLam` inhabits the large recursor's type.**  Three applications of
`mkLam_mem_mkForallType_of_dom`, one per binder; the innermost step is exactly
`m ∈ f ‘ •`, i.e. the minor premise inhabits the motive at the constructor. -/
theorem recFnL_mem_interpL_recType :
    recFnL κ (u.eval ls) ∈
      (interp (unitML κ ls) L [] ((unitDeclLE.recType 0).instL [u])).toFun ∅ := by
  rw [unitDeclLE_recType_instL]
  have hρ0 := interpCtxL_nil L κ ls
  rw [interp_forallE_type (unitML κ ls) L
    (fun h ↦ hn ((isPropL_recB1_iff L κ ls hu hle [] trivial).mp h))]
  refine mkLam_mem_mkForallType_of_dom (interpL_motTyU L κ ls hu hle [] trivial _).symm (fun f hf ↦ ?_)
  have hf0 : (snoc (∅ : V) f) ‘ ((0 : ℕ) : V) = f :=
    snoc_value_at_len (Γ := []) (unitML κ ls) L hρ0
  have h1 : snoc (∅ : V) f ∈ interpCtx (unitML κ ls) L [motTyU u] :=
    (mem_interpCtx_cons (unitML κ ls) L).mpr ⟨∅, hρ0, f, hf, rfl⟩
  have hmin : (interp (unitML κ ls) L [motTyU u] minTy).toFun (snoc (∅ : V) f) = f ‘ (pt : V) :=
    interpL_minTy L κ ls hu hle hf0
  show recFn2 f ∈ _
  rw [interp_forallE_type (unitML κ ls) L
    (fun h ↦ hn ((isPropL_recB2_iff L κ ls hu hle [] trivial).mp h))]
  refine mkLam_mem_mkForallType_of_dom hmin.symm (fun m hm ↦ ?_)
  rw [hmin] at hm
  have h2 : snoc (snoc (∅ : V) f) m ∈ interpCtx (unitML κ ls) L [minTy, motTyU u] :=
    (mem_interpCtx_cons (unitML κ ls) L).mpr ⟨snoc ∅ f, h1, m, by rw [hmin]; exact hm, rfl⟩
  show recFn3 m ∈ _
  rw [interp_forallE_type (unitML κ ls) L
    (fun h ↦ hn ((isPropL_recB3_iff L κ ls hu hle [] trivial).mp h))]
  refine mkLam_mem_mkForallType_of_dom (interpL_Unit1 L κ ls _ _).symm (fun t ht ↦ ?_)
  rw [interpL_Unit1 L κ ls] at ht
  obtain rfl : t = (pt : V) := mem_singleton_iff.mp ht
  have e0 : (snoc (snoc (snoc (∅ : V) f) m) pt) ‘ ((0 : ℕ) : V) = f :=
    ((snoc_value_of_lt (Γ := [minTy, motTyU u]) (unitML κ ls) L h2 (j := 0) (by simp)).trans
      (snoc_value_of_lt (Γ := [motTyU u]) (unitML κ ls) L h1 (j := 0) (by simp))).trans hf0
  have e2 : (snoc (snoc (snoc (∅ : V) f) m) pt) ‘ ((2 : ℕ) : V) = pt :=
    snoc_value_at_len (Γ := [minTy, motTyU u]) (unitML κ ls) L h2
  rw [interpL_recBody L κ ls hu hle e0 e2]
  exact hm

end SliceB

/-! ## 10. Slice B: the ι-rule still closes

**The answer to the first question.**  Once `Unit1.rec`'s value is a genuine function, the
ι-rule's left side is a *real* application of it — three set-theoretic applications — and it
reduces to the minor premise, which is what the right side's β-redex reduces to as well.  The
computational core is `recFnL_beta`; the rest is `interp`'s app/lam clauses. -/

section Beta

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- **`Unit1.rec motive m mk = m` in the model**, as three applications of the oracle's value.
This is the whole computational content of the large ι-rule. -/
theorem recFnL_beta {κ : ℕ → V} {n : ℕ} {f m : V}
    (hf : f ∈ ((U κ n) ^ ({pt} : V) : V)) (hm : m ∈ f ‘ (pt : V)) :
    (((recFnL κ n) ‘ f) ‘ m) ‘ (pt : V) = m := by
  rw [recFnL_apply hf, recFn2_apply hm, recFn3_apply (by simp)]

end Beta

section Iota

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {envF : VEnv} {nv : ℕ} (L : PropSplit envF nv) (κ : ℕ → V) (ls : List ℕ)
variable {u : VLevel} (hu : u.WF nv) (hle : unitEnvLE ≤ envF) (hn : u.eval ls ≠ 0)

/-! ### The partial applications, typed -/

include hu in
theorem hasTypeL_recSort {Γ : List VExpr} :
    unitEnvLE.HasType nv Γ ((unitDeclLE.recType 0).instL [u])
      (.sort (.imax (.imax .zero (.succ u)) (.imax u (.imax .zero u)))) := by
  rw [unitDeclLE_recType_instL]
  exact .forallEDF (hasTypeL_motTy hu) hasTypeL_recB1

include hu in
theorem hasTypeL_recApp1 {Γ : List VExpr} :
    unitEnvLE.HasType nv (minTy :: motTyU u :: Γ) (.app (.const recN [u]) (.bvar 1))
      (.forallE (.app (.bvar 1) (.const `Unit1.mk []))
        (.forallE (.const `Unit1 []) (.app (.bvar 3) (.bvar 0)))) := by
  have h1 : unitEnvLE.HasType nv (minTy :: motTyU u :: Γ) (.const recN [u])
      ((unitDeclLE.recType 0).instL [u]) := hasTypeL_rec hu
  rw [unitDeclLE_recType_instL] at h1
  exact .appDF h1 (hasTypeL_bvar1 (Γ := Γ) (u := u) (A := minTy))

theorem hasTypeL_recApp1Sort {Γ : List VExpr} :
    unitEnvLE.HasType nv (minTy :: motTyU u :: Γ)
      (.forallE (.app (.bvar 1) (.const `Unit1.mk []))
        (.forallE (.const `Unit1 []) (.app (.bvar 3) (.bvar 0))))
      (.sort (.imax u (.imax .zero u))) := by
  refine .forallEDF hasTypeL_minTy1 (.forallEDF hasTypeL_Unit1 ?_)
  have hb : unitEnvLE.HasType nv
      (VExpr.const `Unit1 [] :: VExpr.app (.bvar 1) (.const `Unit1.mk []) ::
        minTy :: motTyU u :: Γ) (.bvar 3) (motTyU u) :=
    .bvar (Lookup.succ (Lookup.succ (Lookup.succ Lookup.zero)))
  exact .appDF hb (.bvar .zero)

include hu in
theorem hasTypeL_recApp2 {Γ : List VExpr} :
    unitEnvLE.HasType nv (minTy :: motTyU u :: Γ)
      (.app (.app (.const recN [u]) (.bvar 1)) (.bvar 0))
      (.forallE (.const `Unit1 []) (.app (.bvar 2) (.bvar 0))) :=
  .appDF (hasTypeL_recApp1 hu) (.bvar .zero)

include hu in
theorem hasTypeL_rhsApp1 {Γ : List VExpr} :
    unitEnvLE.HasType nv (minTy :: motTyU u :: Γ)
      (.app (.lam (motTyU u) (.lam minTy (.bvar 0))) (.bvar 1))
      (.forallE (.app (.bvar 1) (.const `Unit1.mk []))
        (.app (.bvar 2) (.const `Unit1.mk []))) :=
  .appDF (hasTypeL_iotaLam hu) hasTypeL_bvar1

theorem hasTypeL_rhsApp1Sort {Γ : List VExpr} :
    unitEnvLE.HasType nv (minTy :: motTyU u :: Γ)
      (.forallE (.app (.bvar 1) (.const `Unit1.mk []))
        (.app (.bvar 2) (.const `Unit1.mk [])))
      (.sort (.imax u u)) :=
  .forallEDF hasTypeL_minTy1 (.appDF hasTypeL_bvar2 hasTypeL_mk)

include hu in
theorem hasTypeL_iotaLamSort {Γ : List VExpr} :
    unitEnvLE.HasType nv Γ
      (.forallE (motTyU u) (.forallE minTy (.app (.bvar 1) (.const `Unit1.mk []))))
      (.sort (.imax (.imax .zero (.succ u)) (.imax u u))) :=
  .forallEDF (hasTypeL_motTy hu) hasTypeL_ruleB1

theorem hasTypeL_bvar0_minTy {Γ : List VExpr} :
    unitEnvLE.HasType nv (minTy :: motTyU u :: Γ) (.bvar 0)
      (.app (.bvar 1) (.const `Unit1.mk [])) := .bvar .zero

/-! ### …and none of them is a proof, at `u.eval ls ≠ 0` -/

include hu hle hn in
theorem not_isProofL_rec (Γ : List VExpr) (hΓ : OnCtx Γ (unitEnvLE.IsType nv)) :
    ¬ L.IsProof (unitML κ ls) Γ (.const recN [u]) := by
  rw [isProof_iff hle hΓ (hasTypeL_rec hu) (hasTypeL_recSort hu)
    (u := .imax (.imax .zero (.succ u)) (.imax u (.imax .zero u)))
    ⟨⟨trivial, hu⟩, hu, trivial, hu⟩]
  rw [show (VLevel.imax (.imax .zero (.succ u)) (.imax u (.imax .zero u))).eval
      (unitML κ ls).ls
      = Lean.Nat.imax (Lean.Nat.imax 0 (u.eval ls + 1))
          (Lean.Nat.imax (u.eval ls) (Lean.Nat.imax 0 (u.eval ls))) from rfl]
  rw [imax_eq_zero_iff, imax_eq_zero_iff, imax_eq_zero_iff]
  exact hn

include hu hle hn in
theorem not_isProofL_recApp1 (Γ : List VExpr) (hΓ : OnCtx Γ (unitEnvLE.IsType nv)) :
    ¬ L.IsProof (unitML κ ls) (minTy :: motTyU u :: Γ)
      (.app (.const recN [u]) (.bvar 1)) := by
  rw [isProof_iff hle (onCtxL_min hu hΓ) (hasTypeL_recApp1 hu) hasTypeL_recApp1Sort
    (u := .imax u (.imax .zero u)) ⟨hu, trivial, hu⟩]
  rw [show (VLevel.imax u (.imax .zero u)).eval (unitML κ ls).ls
      = Lean.Nat.imax (u.eval ls) (Lean.Nat.imax 0 (u.eval ls)) from rfl]
  rw [imax_eq_zero_iff, imax_eq_zero_iff]
  exact hn

include hu hle hn in
theorem not_isProofL_recApp2 (Γ : List VExpr) (hΓ : OnCtx Γ (unitEnvLE.IsType nv)) :
    ¬ L.IsProof (unitML κ ls) (minTy :: motTyU u :: Γ)
      (.app (.app (.const recN [u]) (.bvar 1)) (.bvar 0)) := by
  rw [isProof_iff hle (onCtxL_min hu hΓ) (hasTypeL_recApp2 hu) hasTypeL_recB2 (u := .imax .zero u) ⟨trivial, hu⟩]
  rw [show (VLevel.imax .zero u).eval (unitML κ ls).ls
      = Lean.Nat.imax 0 (u.eval ls) from rfl, imax_eq_zero_iff]
  exact hn

include hu hle hn in
theorem not_isProofL_iotaLam (Γ : List VExpr) (hΓ : OnCtx Γ (unitEnvLE.IsType nv)) :
    ¬ L.IsProof (unitML κ ls) Γ (.lam (motTyU u) (.lam minTy (.bvar 0))) := by
  rw [isProof_iff hle hΓ (hasTypeL_iotaLam hu) (hasTypeL_iotaLamSort hu)
    (u := .imax (.imax .zero (.succ u)) (.imax u u)) ⟨⟨trivial, hu⟩, hu, hu⟩]
  rw [show (VLevel.imax (.imax .zero (.succ u)) (.imax u u)).eval (unitML κ ls).ls
      = Lean.Nat.imax (Lean.Nat.imax 0 (u.eval ls + 1))
          (Lean.Nat.imax (u.eval ls) (u.eval ls)) from rfl]
  rw [imax_eq_zero_iff, imax_eq_zero_iff]
  exact hn

include hu hle hn in
theorem not_isProofL_rhsApp1 (Γ : List VExpr) (hΓ : OnCtx Γ (unitEnvLE.IsType nv)) :
    ¬ L.IsProof (unitML κ ls) (minTy :: motTyU u :: Γ)
      (.app (.lam (motTyU u) (.lam minTy (.bvar 0))) (.bvar 1)) := by
  rw [isProof_iff hle (onCtxL_min hu hΓ) (hasTypeL_rhsApp1 hu) hasTypeL_rhsApp1Sort (u := .imax u u) ⟨hu, hu⟩]
  rw [show (VLevel.imax u u).eval (unitML κ ls).ls
      = Lean.Nat.imax (u.eval ls) (u.eval ls) from rfl, imax_eq_zero_iff]
  exact hn

include hu hle hn in
theorem not_isProofL_bvar0_minTy (Γ : List VExpr) (hΓ : OnCtx Γ (unitEnvLE.IsType nv)) :
    ¬ L.IsProof (unitML κ ls) (minTy :: motTyU u :: Γ) (.bvar 0) := by
  rw [isProof_iff hle (onCtxL_min hu hΓ) hasTypeL_bvar0_minTy hasTypeL_minTy1 (u := u) hu, unitML_ls]
  exact hn

include hu hle hn in
theorem not_isProofL_innerLam (Γ : List VExpr) (hΓ : OnCtx Γ (unitEnvLE.IsType nv)) :
    ¬ L.IsProof (unitML κ ls) (motTyU u :: Γ) (.lam minTy (.bvar 0)) := by
  rw [isProof_iff hle (onCtxL_mot hu hΓ) (.lamDF hasTypeL_minTy hasTypeL_bvar0_minTy) hasTypeL_ruleB1
    (u := .imax u u) ⟨hu, hu⟩]
  rw [show (VLevel.imax u u).eval (unitML κ ls).ls
      = Lean.Nat.imax (u.eval ls) (u.eval ls) from rfl, imax_eq_zero_iff]
  exact hn

end Iota

/-! ## 11. Slice B: the two sides of the ι-rule, computed

Both reduce to the minor premise `m`.  The left side does so by *applying* the oracle's
value — `recFnL_beta` — and the right side by the η-expanded β-redex `interp` builds. -/

section IotaCompute

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ} (L : PropSplit envF nv) (κ : ℕ → V) (ls : List ℕ)
variable {u : VLevel} (hu : u.WF nv) (hle : unitEnvLE ≤ envF) (hn : u.eval ls ≠ 0)

include hu hle hn in
/-- **The left side's body**: `⟦Unit1.rec motive m mk⟧ = m`.  Three `interp_app_type` steps
onto the oracle's value, then `recFnL_beta`. -/
theorem interpL_lhsBody {f m : V}
    (hf : f ∈ ((U κ (u.eval ls)) ^ ({pt} : V) : V)) (hm : m ∈ f ‘ (pt : V))
    {ρ : V} (h0 : ρ ‘ ((0 : ℕ) : V) = f) (h1 : ρ ‘ ((1 : ℕ) : V) = m) :
    (interp (unitML κ ls) L [minTy, motTyU u]
      (.app (.app (.app (.const recN [u]) (.bvar 1)) (.bvar 0))
        (.const `Unit1.mk []))).toFun ρ = m := by
  rw [interp_app_type (unitML κ ls) L (not_isProofL_recApp2 L κ ls hu hle hn [] trivial),
    interp_app_type (unitML κ ls) L (not_isProofL_recApp1 L κ ls hu hle hn [] trivial),
    interp_app_type (unitML κ ls) L (not_isProofL_rec L κ ls hu hle hn _ (onCtxL_min hu (Γ := []) trivial)),
    interp_const, unitML_cnst, interp_bvar, interp_bvar, interpL_mk L κ ls]
  simp only [List.length_cons, List.length_nil]
  rw [show (2 - 1 - 1 : ℕ) = 0 from rfl, show (2 - 1 - 0 : ℕ) = 1 from rfl, h0, h1,
    unitOracleL_rec, if_neg hn]
  exact recFnL_beta hf hm

include hu hle hn in
/-- **The right side's body**: the η-expansion's β-redex also gives `m`. -/
theorem interpL_rhsBody {f m ρ : V}
    (hfd : f ∈ (interp (unitML κ ls) L [minTy, motTyU u] (motTyU u)).toFun ρ)
    (hmd : m ∈ (interp (unitML κ ls) L (motTyU u :: [minTy, motTyU u]) minTy).toFun (snoc ρ f))
    (hρ : ρ ∈ interpCtx (unitML κ ls) L [minTy, motTyU u])
    (h0 : ρ ‘ ((0 : ℕ) : V) = f) (h1 : ρ ‘ ((1 : ℕ) : V) = m) :
    (interp (unitML κ ls) L [minTy, motTyU u]
      (.app (.app (.lam (motTyU u) (.lam minTy (.bvar 0))) (.bvar 1)) (.bvar 0))).toFun ρ
      = m := by
  have hρf : snoc ρ f ∈ interpCtx (unitML κ ls) L (motTyU u :: [minTy, motTyU u]) :=
    (mem_interpCtx_cons (unitML κ ls) L).mpr ⟨ρ, hρ, f, hfd, rfl⟩
  rw [interp_app_type (unitML κ ls) L (not_isProofL_rhsApp1 L κ ls hu hle hn [] trivial),
    interp_app_type (unitML κ ls) L (not_isProofL_iotaLam L κ ls hu hle hn _ (onCtxL_min hu (Γ := []) trivial)),
    interp_lam_type (unitML κ ls) L (not_isProofL_innerLam L κ ls hu hle hn _ (onCtxL_min hu (Γ := []) trivial)),
    interp_bvar, interp_bvar]
  simp only [List.length_cons, List.length_nil]
  rw [show (2 - 1 - 1 : ℕ) = 0 from rfl, show (2 - 1 - 0 : ℕ) = 1 from rfl, h0, h1,
    mkLam_value hfd,
    interp_lam_type (unitML κ ls) L (not_isProofL_bvar0_minTy L κ ls hu hle hn _ (onCtxL_min hu (Γ := []) trivial)),
    mkLam_value hmd, interp_bvar]
  simp only [List.length_cons, List.length_nil]
  rw [show (3 + 1 - 1 - 0 : ℕ) = 3 from rfl]
  exact snoc_value_at_len (Γ := motTyU u :: [minTy, motTyU u]) (unitML κ ls) L hρf

include hu hle hn in
/-- **The ι-rule's two sides are equal at `u.eval ls ≠ 0`** — the answer to the first
question the coordinator asked: yes, it still closes once the recursor's value is a genuine
function. -/
theorem interpL_unitRule_eq_of_ne :
    (interp (unitML κ ls) L [] ((unitDeclLE.iotaRule 0 0 unitCtor).lhs.instL [u])).toFun ∅
      = (interp (unitML κ ls) L []
          ((unitDeclLE.iotaRule 0 0 unitCtor).rhs.instL [u])).toFun ∅ := by
  rw [unitRuleL_lhs_instL, unitRuleL_rhs_instL,
    interp_lam_type (unitML κ ls) L
      (fun h ↦ hn ((isProofL_iotaLhsLam_iff L κ ls hu hle [] trivial).mp h)),
    interp_lam_type (unitML κ ls) L
      (fun h ↦ hn ((isProofL_iotaRhsLam_iff L κ ls hu hle [] trivial).mp h))]
  have hρ0 := interpCtxL_nil L κ ls
  refine mkLam_ext rfl (fun f hf ↦ ?_)
  have hf' : f ∈ ((U κ (u.eval ls)) ^ ({pt} : V) : V) := by
    rwa [interpL_motTyU L κ ls hu hle [] trivial] at hf
  have hf0 : (snoc (∅ : V) f) ‘ ((0 : ℕ) : V) = f :=
    snoc_value_at_len (Γ := []) (unitML κ ls) L hρ0
  have h1 : snoc (∅ : V) f ∈ interpCtx (unitML κ ls) L [motTyU u] :=
    (mem_interpCtx_cons (unitML κ ls) L).mpr ⟨∅, hρ0, f, hf, rfl⟩
  have hmin : (interp (unitML κ ls) L [motTyU u] minTy).toFun (snoc (∅ : V) f) = f ‘ (pt : V) :=
    interpL_minTy L κ ls hu hle hf0
  rw [interp_lam_type (unitML κ ls) L
      (fun h ↦ hn ((isProofL_iotaLhsBody_iff L κ ls hu hle [] trivial).mp h)),
    interp_lam_type (unitML κ ls) L
      (fun h ↦ hn ((isProofL_iotaRhsBody_iff L κ ls hu hle [] trivial).mp h))]
  refine mkLam_ext rfl (fun m hm ↦ ?_)
  rw [hmin] at hm
  have h2 : snoc (snoc (∅ : V) f) m ∈ interpCtx (unitML κ ls) L [minTy, motTyU u] :=
    (mem_interpCtx_cons (unitML κ ls) L).mpr ⟨snoc ∅ f, h1, m, by rw [hmin]; exact hm, rfl⟩
  have e0 : (snoc (snoc (∅ : V) f) m) ‘ ((0 : ℕ) : V) = f :=
    (snoc_value_of_lt (Γ := [motTyU u]) (unitML κ ls) L h1 (j := 0) (by simp)).trans hf0
  have e1 : (snoc (snoc (∅ : V) f) m) ‘ ((1 : ℕ) : V) = m :=
    snoc_value_at_len (Γ := [motTyU u]) (unitML κ ls) L h1
  have hfd : f ∈ (interp (unitML κ ls) L [minTy, motTyU u] (motTyU u)).toFun
      (snoc (snoc (∅ : V) f) m) := by
    rw [interpL_motTyU L κ ls hu hle [minTy, motTyU u]
      (onCtxL_min hu (Γ := []) trivial)]; exact hf'
  have hmd : m ∈ (interp (unitML κ ls) L (motTyU u :: [minTy, motTyU u]) minTy).toFun
      (snoc (snoc (snoc (∅ : V) f) m) f) := by
    rw [interpL_minTy_at L κ ls hu hle [minTy, motTyU u] (onCtxL_min hu (Γ := []) trivial)
      (f := f) (by
        simpa using snoc_value_at_len (Γ := [minTy, motTyU u]) (unitML κ ls) L h2)]
    exact hm
  rw [interpL_lhsBody L κ ls hu hle hn hf' hm e0 e1,
    interpL_rhsBody L κ ls hu hle hn hfd hmd h2 e0 e1]

end IotaCompute

/-! ## 12. Slice B: the ι-rule's type, and the assembly of both slices -/

section Assemble

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ} (L : PropSplit envF nv) (κ : ℕ → V) (ls : List ℕ)
variable {u : VLevel} (hu : u.WF nv) (hle : unitEnvLE ≤ envF)

include hu hle in
/-- The left side inhabits the equated type, at `u.eval ls ≠ 0`. -/
theorem interpL_lhs_mem_type_of_ne (hn : u.eval ls ≠ 0) :
    (interp (unitML κ ls) L [] ((unitDeclLE.iotaRule 0 0 unitCtor).lhs.instL [u])).toFun ∅
      ∈ (interp (unitML κ ls) L []
          ((unitDeclLE.iotaRule 0 0 unitCtor).type.instL [u])).toFun ∅ := by
  rw [unitRuleL_lhs_instL, unitRuleL_type_instL,
    interp_lam_type (unitML κ ls) L
      (fun h ↦ hn ((isProofL_iotaLhsLam_iff L κ ls hu hle [] trivial).mp h)),
    interp_forallE_type (unitML κ ls) L
      (fun h ↦ hn ((isPropL_ruleB1_iff L κ ls hu hle [] trivial).mp h))]
  have hρ0 := interpCtxL_nil L κ ls
  refine mkLam_mem_mkForallType_of_dom rfl (fun f hf ↦ ?_)
  have hf' : f ∈ ((U κ (u.eval ls)) ^ ({pt} : V) : V) := by
    rwa [interpL_motTyU L κ ls hu hle [] trivial] at hf
  have hf0 : (snoc (∅ : V) f) ‘ ((0 : ℕ) : V) = f :=
    snoc_value_at_len (Γ := []) (unitML κ ls) L hρ0
  have h1 : snoc (∅ : V) f ∈ interpCtx (unitML κ ls) L [motTyU u] :=
    (mem_interpCtx_cons (unitML κ ls) L).mpr ⟨∅, hρ0, f, hf, rfl⟩
  have hmin : (interp (unitML κ ls) L [motTyU u] minTy).toFun (snoc (∅ : V) f) = f ‘ (pt : V) :=
    interpL_minTy L κ ls hu hle hf0
  rw [interp_lam_type (unitML κ ls) L
      (fun h ↦ hn ((isProofL_iotaLhsBody_iff L κ ls hu hle [] trivial).mp h)),
    interp_forallE_type (unitML κ ls) L
      (fun h ↦ hn ((isPropL_ruleB2_iff L κ ls hu hle [] (onCtxL_min hu (Γ := []) trivial)).mp h))]
  refine mkLam_mem_mkForallType_of_dom rfl (fun m hm ↦ ?_)
  rw [hmin] at hm
  have h2 : snoc (snoc (∅ : V) f) m ∈ interpCtx (unitML κ ls) L [minTy, motTyU u] :=
    (mem_interpCtx_cons (unitML κ ls) L).mpr ⟨snoc ∅ f, h1, m, by rw [hmin]; exact hm, rfl⟩
  have e0 : (snoc (snoc (∅ : V) f) m) ‘ ((0 : ℕ) : V) = f :=
    (snoc_value_of_lt (Γ := [motTyU u]) (unitML κ ls) L h1 (j := 0) (by simp)).trans hf0
  have e1 : (snoc (snoc (∅ : V) f) m) ‘ ((1 : ℕ) : V) = m :=
    snoc_value_at_len (Γ := [motTyU u]) (unitML κ ls) L h1
  rw [interpL_lhsBody L κ ls hu hle hn hf' hm e0 e1, interpL_minTy1 L κ ls hu hle e0]
  exact hm

/-! ### The three `OracleOK`s -/

theorem oracleOKL_type :
    OracleOK L κ ls (unitOracleL κ ls) (unitOracleL κ ls) `Unit1 ⟨0, .sort .zero⟩ := by
  refine oracleOK_of (fun _ _ hd ↦ unitOracleL_congr κ ls _ hd) (fun {us} _ _ ↦ ?_)
  rw [unitOracleL_Unit1,
    show ((⟨0, .sort .zero⟩ : VConstant).type.instL us) = VExpr.sort .zero from rfl,
    interp_sort]
  simp [VLevel.eval, unitML]

theorem oracleOKL_mk :
    OracleOK L κ ls (unitOracleL κ ls) (unitOracleL κ ls) `Unit1.mk ⟨0, .const `Unit1 []⟩ := by
  refine oracleOK_of (fun _ _ hd ↦ unitOracleL_congr κ ls _ hd) (fun {us} _ _ ↦ ?_)
  rw [unitOracleL_mk,
    show ((⟨0, .const `Unit1 []⟩ : VConstant).type.instL us) = VExpr.const `Unit1 [] from rfl]
  show (pt : V) ∈ (interp (unitML κ ls) L [] (.const `Unit1 [])).toFun ∅
  rw [interpL_Unit1 L κ ls]; simp

include hle in
/-- **`Unit1.rec` at the large eliminator, both slices.**  At `u.eval ls = 0` the value is `•`
and the type is a proposition; at `u.eval ls ≠ 0` the value is the three-layer function.  The
`if` in `unitOracleL` is exactly this case distinction. -/
theorem oracleOKL_rec :
    OracleOK L κ ls (unitOracleL κ ls) (unitOracleL κ ls) recN ⟨1, unitDeclLE.recType 0⟩ := by
  refine oracleOK_of (fun _ _ hd ↦ unitOracleL_congr κ ls _ hd) (fun {us} hw hlen ↦ ?_)
  obtain ⟨v, rfl⟩ : ∃ v, us = [v] := by
    match us, hlen with | [v], _ => exact ⟨v, rfl⟩
  have hv : v.WF nv := hw v (by simp)
  rw [unitOracleL_rec]
  show (if v.eval ls = 0 then (pt : V) else recFnL κ (v.eval ls)) ∈
    (interp (unitML κ ls) L [] ((unitDeclLE.recType 0).instL [v])).toFun ∅
  by_cases h0 : v.eval ls = 0
  · rw [if_pos h0]; exact pt_mem_interpL_recType_of_zero L κ ls hv hle h0
  · rw [if_neg h0]; exact recFnL_mem_interpL_recType L κ ls hv hle h0

include hle in
theorem inductOracleOKL_consts :
    ∀ p ∈ unitDeclLE.allConsts,
      OracleOK L κ ls (unitOracleL κ ls) (unitOracleL κ ls) p.1 p.2 := by
  intro p hp
  rw [unitDeclLE_allConsts] at hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  obtain rfl | rfl | rfl := hp
  · exact oracleOKL_type L κ ls
  · exact oracleOKL_mk L κ ls
  · exact oracleOKL_rec L κ ls hle

include hle in
/-- **The ι-rule, both slices.** -/
theorem defEqOKL_unitRule :
    DefEqOK L (unitML κ ls) (unitDeclLE.iotaRule 0 0 unitCtor) := by
  intro us hw hlen
  obtain ⟨v, rfl⟩ : ∃ v, us = [v] := by
    match us, hlen with | [v], _ => exact ⟨v, rfl⟩
  have hv : v.WF nv := hw v (by simp)
  by_cases h0 : v.eval ls = 0
  · obtain ⟨hl, hr⟩ := interpL_unitRule_sides_of_zero L κ ls hv hle h0
    exact ⟨Above.pure (hl.trans hr.symm),
      Above.pure (by rw [hl]; exact pt_mem_interpL_unitRule_type_of_zero L κ ls hv hle h0)⟩
  · exact ⟨Above.pure (interpL_unitRule_eq_of_ne L κ ls hv hle h0),
      Above.pure (interpL_lhs_mem_type_of_ne L κ ls hv hle h0)⟩

include hle in
theorem inductOracleOKL_rules :
    ∀ df ∈ unitDeclLE.iotaRules, DefEqOK L (unitML κ ls) df := by
  intro df hdf
  rw [unitDeclLE_iotaRules] at hdf
  simp only [List.mem_singleton] at hdf
  subst hdf
  exact defEqOKL_unitRule L κ ls hle

include hle in
/-- **`InductOracleOK` at `inductive Unit1 : Prop | mk` with its LARGE eliminator** — the case
`UnitOracleWitness.lean` §9 left open.  Both fields, both level slices, no empty domain. -/
theorem inductOracleOKL :
    InductOracleOK L κ ls (unitOracleL κ ls) (unitOracleL κ ls) unitDeclLE :=
  ⟨inductOracleOKL_consts L κ ls hle, inductOracleOKL_rules L κ ls hle⟩

theorem cnstOfL : cnstOf L κ ls (unitOracleL κ ls) [.induct unitDeclLE] = unitOracleL κ ls := by
  show oracleExtend (unitOracleL κ ls) unitDeclLE.allNames
    (cnstOf L κ ls (unitOracleL κ ls) []) = _
  rw [show cnstOf L κ ls (unitOracleL κ ls) ([] : List VDecl) = fun _ _ ↦ (∅ : V) from rfl,
    unitDeclLE_allNames]
  funext m us
  show (oracleExtend (unitOracleL κ ls) [`Unit1, `Unit1.mk, recN] (fun _ _ ↦ (∅ : V))) m us = _
  simp only [oracleExtend, cnstUpdate]
  by_cases h1 : m = recN
  · subst h1; simp [unitOracleL, recN, Lean.mkRecName]
  by_cases h2 : m = `Unit1.mk
  · subst h2; simp [unitOracleL, h1]
  by_cases h3 : m = `Unit1
  · subst h3; simp [unitOracleL, h1, h2]
  simp only [if_neg h1, if_neg h2, if_neg h3]
  rw [show unitOracleL κ ls m us = (pt : V) from by simp [unitOracleL, h1, h3]]
  rfl

include hle in
theorem oracleFitsL : OracleFits L κ ls (unitOracleL κ ls) [.induct unitDeclLE] := by
  refine ⟨?_, trivial⟩
  show InductOracleOK L κ ls (unitOracleL κ ls)
    (cnstOf L κ ls (unitOracleL κ ls) [.induct unitDeclLE]) unitDeclLE
  rw [cnstOfL]
  exact inductOracleOKL L κ ls hle

/-- The same with the `hle` supplied the way `coherentOn_cnstOf` supplies it. -/
theorem oracleFitsL_at_consumer {env : VEnv}
    (hwf : VEnv.WF' [VDecl.induct unitDeclLE] env) (hle' : env ≤ envF) :
    OracleFits L κ ls (unitOracleL κ ls) [.induct unitDeclLE] :=
  oracleFitsL L κ ls (eq_unitEnvLE_of_wf' hwf ▸ hle')

end Assemble

/-! ## 13. The measurement: the split is forced, and neither slice is empty -/

section Measure

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ} (L : PropSplit envF nv) (κ : ℕ → V) (ls : List ℕ)
variable {u : VLevel} (hu : u.WF nv) (hle : unitEnvLE ≤ envF)

include hu hle in
/-- **The `if` in `unitOracleL` is forced, not a convenience.**  Given *any* inhabitant of the
motive space, `•` is not a value of the large recursor's type at `u.eval ls ≠ 0`.  So no
level-uniform oracle can work: at `0` the type is a proposition whose only element is `•`
(`pt_mem_interpL_recType_of_zero`), and here `•` is excluded.

(The hypothesis is exactly right rather than cosmetic: if `U κ n = ∅` — which a junk `κ`
permits — then the motive space is empty, `recFnL κ n` collapses to `∅ = •`, and nothing is
forced.  No `κ` is chosen anywhere in this file.) -/
theorem pt_not_mem_interpL_recType_of_ne (hn : u.eval ls ≠ 0) {g : V}
    (hg : g ∈ (interp (unitML κ ls) L [] (motTyU u)).toFun ∅) :
    (pt : V) ∉ (interp (unitML κ ls) L [] ((unitDeclLE.recType 0).instL [u])).toFun ∅ := by
  rw [unitDeclLE_recType_instL, interp_forallE_type (unitML κ ls) L
    (fun h ↦ hn ((isPropL_recB1_iff L κ ls hu hle [] trivial).mp h))]
  exact pt_not_mem_mkForallType_of_nonempty hg

/-- **Slice B is not an empty case.**  `Sort 1` is a legal instantiation at every `nv`, so the
`u.eval ls ≠ 0` branch is reached; the two slices are a genuine split, not a formality. -/
theorem exists_ne_zero_level : ∃ u : VLevel, u.WF nv ∧ u.eval ls ≠ 0 :=
  ⟨.succ .zero, trivial, by simp [VLevel.eval]⟩

/-- …and slice A is not empty either. -/
theorem exists_eq_zero_level : ∃ u : VLevel, u.WF nv ∧ u.eval ls = 0 :=
  ⟨.zero, trivial, rfl⟩

include hle in
/-- **The `consts` obligation, `Above`-free**, at an arbitrary `κ` and both slices. -/
theorem mem_interp_constsL (v : VLevel) (hv : v.WF nv) :
    (∀ vs : List VLevel, unitOracleL κ ls `Unit1 vs ∈
        (interp (unitML κ ls) L [] ((VExpr.sort .zero).instL vs)).toFun ∅) ∧
    (∀ vs : List VLevel, unitOracleL κ ls `Unit1.mk vs ∈
        (interp (unitML κ ls) L [] ((VExpr.const `Unit1 []).instL vs)).toFun ∅) ∧
    unitOracleL κ ls recN [v] ∈
        (interp (unitML κ ls) L [] ((unitDeclLE.recType 0).instL [v])).toFun ∅ := by
  refine ⟨fun vs ↦ ?_, fun vs ↦ ?_, ?_⟩
  · rw [unitOracleL_Unit1,
      show ((VExpr.sort .zero).instL vs) = VExpr.sort .zero from rfl, interp_sort]
    simp [VLevel.eval, unitML]
  · rw [unitOracleL_mk,
      show ((VExpr.const `Unit1 []).instL vs) = VExpr.const `Unit1 [] from rfl]
    show (pt : V) ∈ (interp (unitML κ ls) L [] (.const `Unit1 [])).toFun ∅
    rw [interpL_Unit1 L κ ls]; simp
  · rw [unitOracleL_rec]
    by_cases h0 : v.eval ls = 0
    · rw [if_pos h0]; exact pt_mem_interpL_recType_of_zero L κ ls hv hle h0
    · rw [if_neg h0]; exact recFnL_mem_interpL_recType L κ ls hv hle h0

include hle in
/-- **The `rules` obligation, `Above`-free**, both slices: the two sides are equal and their
common value lies in the equated type, at an arbitrary `κ` with no chain hypothesis. -/
theorem defEq_rulesL (v : VLevel) (hv : v.WF nv) :
    (interp (unitML κ ls) L []
        ((unitDeclLE.iotaRule 0 0 unitCtor).lhs.instL [v])).toFun ∅
      = (interp (unitML κ ls) L []
          ((unitDeclLE.iotaRule 0 0 unitCtor).rhs.instL [v])).toFun ∅ ∧
    (interp (unitML κ ls) L []
        ((unitDeclLE.iotaRule 0 0 unitCtor).lhs.instL [v])).toFun ∅
      ∈ (interp (unitML κ ls) L []
          ((unitDeclLE.iotaRule 0 0 unitCtor).type.instL [v])).toFun ∅ := by
  by_cases h0 : v.eval ls = 0
  · obtain ⟨hl, hr⟩ := interpL_unitRule_sides_of_zero L κ ls hv hle h0
    exact ⟨hl.trans hr.symm,
      by rw [hl]; exact pt_mem_interpL_unitRule_type_of_zero L κ ls hv hle h0⟩
  · exact ⟨interpL_unitRule_eq_of_ne L κ ls hv hle h0,
      interpL_lhs_mem_type_of_ne L κ ls hv hle h0⟩

end Measure

/-! ## 14. Axiom audit -/

#print axioms Lean4Lean.SetModel.UnitAudit.unitEnvLE_add
#print axioms Lean4Lean.SetModel.UnitAudit.unitDeclLE_WF
#print axioms Lean4Lean.SetModel.UnitAudit.unitDeclLE_history
#print axioms Lean4Lean.SetModel.UnitAudit.recFnL_beta
#print axioms Lean4Lean.SetModel.UnitAudit.interpL_motTyU
#print axioms Lean4Lean.SetModel.UnitAudit.pt_mem_interpL_recType_of_zero
#print axioms Lean4Lean.SetModel.UnitAudit.recFnL_mem_interpL_recType
#print axioms Lean4Lean.SetModel.UnitAudit.interpL_unitRule_eq_of_ne
#print axioms Lean4Lean.SetModel.UnitAudit.inductOracleOKL
#print axioms Lean4Lean.SetModel.UnitAudit.oracleFitsL
#print axioms Lean4Lean.SetModel.UnitAudit.oracleFitsL_at_consumer
#print axioms Lean4Lean.SetModel.UnitAudit.mem_interp_constsL
#print axioms Lean4Lean.SetModel.UnitAudit.defEq_rulesL
#print axioms Lean4Lean.SetModel.UnitAudit.pt_not_mem_interpL_recType_of_ne
#print axioms Lean4Lean.SetModel.UnitAudit.exists_ne_zero_level

end Lean4Lean.SetModel.UnitAudit
