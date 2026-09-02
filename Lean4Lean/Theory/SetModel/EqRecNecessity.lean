import Lean4Lean.Theory.SetModel.EqTypeFormer

/-!
# `EqSpec` is NECESSARY at `eqIndDecl`'s recursor cell — the expensive control, built

Handoff §17.8 item 2 lists this as the one satisfiable-but-unmeasured hypothesis of
`EqZeroSlice.lean`, and notes that the analogous control for `Nonempty` is asserted at
`PreludeOracle.lean:905` **in prose only** — so there is no precedent in the tree and no honest way
to price it from that line.  This file builds it.

## What is proved

```lean
theorem not_pt_mem_interp_eqRecType_badTrue … :
    (pt : V) ∉ (interp (badTrueM κ ls) L [] ((eqIndDecl.recType 0).instL [.zero, .succ .zero])).toFun ∅
```

at any `κ` carrying an inaccessible chain of positive length — so
`EqZeroAudit.pt_mem_interp_eqRecType_of_zero`'s hypothesis `EqSpec M v` cannot be dropped, and its
conclusion is not free.  `eqSpec_necessary_at_recursor` packages it, and
`not_eqSpec_badTrueM` checks that what `badTrueM` violates **is** `EqSpec` (at the non-reflexive
instance, and only there).

## What the control costs, measured rather than read off

Two `mkLam` nests, as §17.8 predicted, and the prediction was right about the *shape*:

* `eqTrueFn` — a constant-`{•}` `Eq` denotation, three layers, a copy of `SetModel.eqFn` with the
  `if` deleted (so `⟦Eq α a b⟧ = {•}` even at `a ≠ b`);
* `sepMot` — a motive separating two elements of `α`, two layers, environment-passing so that the
  inner layer can read both `a` (index 1) and `x` (index 2).

What §17.8 did **not** price, and what actually dominates: the separation needs `α` with two
distinct elements, and at `u.eval ls = 0` — which is where the slice lives — the only carriers
available are subsets of `{•}`.  So the control cannot be run at the `Prop` carrier at all: it
needs `v.eval ls = 1` and `IsInaccessibleChain n κ` with `0 < n`, via
`SetModel.U_mem_succ` (the same lever `PreludeSpec.eqFn_distinct` uses).  **A chosen `κ` is
therefore unavoidable here.**  It appears only in this control — a negative statement — never in a
positive bound; see §4.

## Bounds

`Above` occurs in no statement.  The chain hypothesis `IsInaccessibleChain n κ` with `0 < n` is
**load-bearing and stated, not hidden**: at `n = 0` there is no two-element carrier and the control
is not merely unproven but false in shape.  `hle : eqEnv ≤ envF` and `L : PropSplit envF nv` are
carried exactly as in `EqZeroSlice.lean`, so this control sits on the footing of the theorem it
brackets.
-/

namespace Lean4Lean.SetModel.EqRecNec

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open Lean4Lean.SetModel.EqAudit
open Lean4Lean.SetModel.EqZeroAudit
open scoped Classical

section Defs

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]

/-! ## 1. The constant-true `Eq` denotation

`SetModel.eqFn` with the `if` deleted.  Three `mkLam` layers, same domains, so `eqTrueFn_value` is
`eqFn_value`'s proof with one `rw` fewer. -/

theorem trueFib_definable : ℒₛₑₜ-function₂[V] (fun (_ _ : V) ↦ ({pt} : V)) := by
  suffices ℒₛₑₜ-relation₃[V] (fun T (_ _ : V) ↦ T = ({pt} : V)) by exact this
  have e : ∀ T : V, (T = ({pt} : V)) ↔ ∀ z, z ∈ T ↔ z = pt := by
    intro T; rw [mem_ext_iff]; simp [mem_singleton_iff]
  simp only [e]
  definability

noncomputable def eqTrueFibB : V → V :=
  mkLam (fun ρ ↦ ρ ‘ ((0 : ℕ) : V)) (value_definable _)
    (fun (_ _ : V) ↦ ({pt} : V)) trueFib_definable

theorem eqTrueFibB_definable₁ : ℒₛₑₜ-function₁[V] (eqTrueFibB (V := V)) := mkLam_definable _ _ _ _

noncomputable def eqTrueFibA : V → V :=
  mkLam (fun ρ ↦ ρ ‘ ((0 : ℕ) : V)) (value_definable _)
    (fun ρ a ↦ eqTrueFibB (snoc ρ a))
    (by have := eqTrueFibB_definable₁ (V := V); definability)

theorem eqTrueFibA_definable₁ : ℒₛₑₜ-function₁[V] (eqTrueFibA (V := V)) := mkLam_definable _ _ _ _

/-- **A constant-`{•}` `Eq`**: every instance is true, reflexive or not. -/
noncomputable def eqTrueFn (κ : ℕ → V) (i : ℕ) : V :=
  mkLam (fun _ ↦ U κ i) (by definability) (fun ρ α ↦ eqTrueFibA (snoc ρ α))
    (by have := eqTrueFibA_definable₁ (V := V); definability) ∅

theorem eqTrueFn_value {κ : ℕ → V} {i : ℕ} {α a b : V}
    (hα : α ∈ U κ i) (ha : a ∈ α) (hb : b ∈ α) :
    (((eqTrueFn κ i) ‘ α) ‘ a) ‘ b = ({pt} : V) := by
  have hs1 : IsSeq (snoc (∅ : V) α) 1 := isSeq_empty.snoc'
  have h0 : (snoc (∅ : V) α) ‘ ((0 : ℕ) : V) = α := isSeq_empty.read_top
  have h0' : (snoc (snoc (∅ : V) α) a) ‘ ((0 : ℕ) : V) = α :=
    (hs1.read_lt (by omega)).trans h0
  have v1 : (eqTrueFn κ i) ‘ α = eqTrueFibA (snoc ∅ α) := by
    unfold eqTrueFn; exact mkLam_value hα
  have v2 : (eqTrueFibA (snoc (∅ : V) α)) ‘ a = eqTrueFibB (snoc (snoc ∅ α) a) := by
    unfold eqTrueFibA; exact mkLam_value (by rw [h0]; exact ha)
  have v3 : (eqTrueFibB (snoc (snoc (∅ : V) α) a)) ‘ b = ({pt} : V) := by
    unfold eqTrueFibB; exact mkLam_value (by rw [h0']; exact hb)
  rw [v1, v2, v3]

/-! ## 2. The separating motive

Environment-passing, because the inner layer must read **both** `a` and `x`: at the innermost
environment `snoc (snoc (snoc ∅ α) a) x` those sit at indices 1 and 2. -/

theorem sepFib_definable :
    ℒₛₑₜ-function₂[V]
      (fun (ρ _ : V) ↦ if ρ ‘ ((2 : ℕ) : V) = ρ ‘ ((1 : ℕ) : V) then ({pt} : V) else ∅) := by
  suffices ℒₛₑₜ-relation₃[V]
      (fun T (ρ _ : V) ↦
        T = if ρ ‘ ((2 : ℕ) : V) = ρ ‘ ((1 : ℕ) : V) then ({pt} : V) else ∅) by exact this
  have e : ∀ T ρ : V,
      (T = if ρ ‘ ((2 : ℕ) : V) = ρ ‘ ((1 : ℕ) : V) then ({pt} : V) else ∅) ↔
        ∀ z, z ∈ T ↔ (z = pt ∧ ρ ‘ ((2 : ℕ) : V) = ρ ‘ ((1 : ℕ) : V)) := by
    intro T ρ
    rw [mem_ext_iff]
    by_cases h : ρ ‘ ((2 : ℕ) : V) = ρ ‘ ((1 : ℕ) : V)
    · rw [if_pos h]; simp_all
    · rw [if_neg h]; simp_all
  simp only [e]
  definability

/-- The motive's inner layer: domain `{•}` (which is what `⟦Eq α a x⟧` is under `eqTrueFn`), value
`{•}` when `x = a` and `∅` otherwise. -/
noncomputable def sepW : V → V :=
  mkLam (fun _ ↦ ({pt} : V)) (by definability)
    (fun ρ _ ↦ if ρ ‘ ((2 : ℕ) : V) = ρ ‘ ((1 : ℕ) : V) then ({pt} : V) else ∅) sepFib_definable

theorem sepW_definable₁ : ℒₛₑₜ-function₁[V] (sepW (V := V)) := mkLam_definable _ _ _ _

/-- The motive, read at `snoc (snoc ∅ α) a`: `λ x, λ _, if x = a then {•} else ∅`. -/
noncomputable def sepMot : V → V :=
  mkLam (fun ρ ↦ ρ ‘ ((0 : ℕ) : V)) (value_definable _) (fun ρ x ↦ sepW (snoc ρ x))
    (by have := sepW_definable₁ (V := V); definability)

theorem sepMot_definable₁ : ℒₛₑₜ-function₁[V] (sepMot (V := V)) := mkLam_definable _ _ _ _

theorem sepMot_value {α a x : V} (hx : x ∈ α) :
    (sepMot (snoc (snoc (∅ : V) α) a)) ‘ x = sepW (snoc (snoc (snoc (∅ : V) α) a) x) := by
  unfold sepMot
  exact mkLam_value (by rw [r2_0]; exact hx)

theorem sepW_value {α a x w : V} (hw : w ∈ ({pt} : V)) :
    (sepW (snoc (snoc (snoc (∅ : V) α) a) x)) ‘ w = (if x = a then ({pt} : V) else ∅) := by
  have h : (sepW (snoc (snoc (snoc (∅ : V) α) a) x)) ‘ w
      = if (snoc (snoc (snoc (∅ : V) α) a) x) ‘ ((2 : ℕ) : V)
          = (snoc (snoc (snoc (∅ : V) α) a) x) ‘ ((1 : ℕ) : V) then ({pt} : V) else ∅ := by
    unfold sepW; exact mkLam_value hw
  rw [h, r3_2 (f := x), r3_1 (f := x)]

/-- The two values that make the control work: the motive holds at `a` and fails at anything
else. -/
theorem sepMot_value_self {α a : V} (ha : a ∈ α) :
    ((sepMot (snoc (snoc (∅ : V) α) a)) ‘ a) ‘ (pt : V) = ({pt} : V) := by
  rw [sepMot_value ha, sepW_value (mem_singleton_iff.2 rfl), if_pos rfl]

theorem sepMot_value_other {α a b : V} (hb : b ∈ α) (hne : b ≠ a) :
    ((sepMot (snoc (snoc (∅ : V) α) a)) ‘ b) ‘ (pt : V) = (∅ : V) := by
  rw [sepMot_value hb, sepW_value (mem_singleton_iff.2 rfl), if_neg hne]

end Defs

/-! ## 3. The motive lands in `⟦motive's type⟧`

`sepMot` is a two-layer `mkLam`; `⟦motTyE u v⟧` is a two-layer `mkForallType` (the motive's type is
*not* a proposition — `not_isProp_motInner`), so this is
`UnitAudit.mkLam_mem_mkForallType_of_dom` twice.  The inner domains match because the bad `Eq`
makes `⟦Eq α a x⟧` the constant `{•}`. -/

section Motive

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ} {L : PropSplit envF nv} {M : ModelData V}
variable {u v : VLevel} (hu : u.WF nv) (hv : v.WF nv) (hle : eqEnv ≤ envF)
variable (h0 : u.eval M.ls = 0)

include hu hv hle h0 in
theorem sepMot_mem_interp_motTyE {α a : V}
    (hEq : ∀ x ∈ α, (((M.cnst ``Eq [v]) ‘ α) ‘ a) ‘ x = ({pt} : V)) :
    sepMot (snoc (snoc (∅ : V) α) a) ∈
      (interp M L (ectxP ([] : List VExpr) v) (motTyE u v)).toFun
        (snoc (snoc (∅ : V) α) a) := by
  have hdom : (interp M L (ectxP ([] : List VExpr) v) (.bvar 1)).toFun
      (snoc (snoc (∅ : V) α) a) = α := by
    rw [interp_bvar]
    simp only [List.length_cons, List.length_nil]
    rw [show (2 - 1 - 1 : ℕ) = 0 from rfl]
    exact r2_0
  rw [show motTyE u v = VExpr.forallE (.bvar 1)
      (.forallE (eqAp v (.bvar 2) (.bvar 1) (.bvar 0)) (.sort u)) from rfl,
    interp_forallE_type M L (not_isProp_motInner (Γ := []) hu hv hle trivial)]
  unfold sepMot
  refine UnitAudit.mkLam_mem_mkForallType_of_dom (by rw [hdom]; exact r2_0) (fun x hx ↦ ?_)
  rw [hdom] at hx
  rw [interp_forallE_type M L (not_isProp_sortu (Γ := []) hu hv hle trivial)]
  unfold sepW
  refine UnitAudit.mkLam_mem_mkForallType_of_dom
    (by rw [interp_eqApX_val hv hle, hEq x hx]) (fun w _ ↦ ?_)
  rw [interp_sort, h0, U_zero]
  split
  · exact true_mem_UProp
  · exact empty_mem_UProp

end Motive

/-! ## 4. The refutation

`u := .zero` and `v := .succ .zero` — so `u.eval ls = 0` (the slice's branch) and `v.eval ls = 1`,
which is the *smallest* level at which a carrier with two distinct elements exists.  That is where
the chain hypothesis enters and it cannot be avoided: at `v.eval ls = 0` every carrier is a subset
of `{•}` and no motive can separate two of its elements.

`κ` is **chosen** here (`IsInaccessibleChain n κ`, `0 < n`).  This is a control — a negated
membership — so the choice is not a positive bound; and the hypothesis is stated, not hidden: with
`n = 0` the statement is not merely unproved, `U_mem_succ` is unavailable and the separation does
not exist. -/

section Refute

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]

/-- The model that differs from `preludeWitness` only in its `Eq` entry, which is constant-true. -/
noncomputable def badTrueM (κ : ℕ → V) (ls : List ℕ) : ModelData V where
  κ := κ
  ls := ls
  cnst := fun n us ↦
    if n = ``Eq then (match us with | [w] => eqTrueFn κ (w.eval ls) | _ => ∅) else ∅

theorem badTrueM_cnst (κ : ℕ → V) (ls : List ℕ) (w : VLevel) :
    (badTrueM (V := V) κ ls).cnst ``Eq [w] = eqTrueFn κ (w.eval ls) := rfl

/-- **What `badTrueM` violates is exactly `EqSpec`**, and at the non-reflexive instance only:
`Eq UProp ∅ {•}` is `{•}` where the specification demands `∅`. -/
theorem not_eqSpec_badTrueM {n : ℕ} {κ : ℕ → V} (hκ : IsInaccessibleChain n κ) (h1 : 0 < n)
    (ls : List ℕ) : ¬ EqSpec (badTrueM (V := V) κ ls) (.succ .zero) := by
  intro hspec
  have hm : (UProp : V) ∈ U κ 1 := U_mem_succ hκ h1
  have h := hspec (UProp : V) hm ∅ (mem_UProp_iff.2 (by simp))
    ({pt} : V) (mem_UProp_iff.2 (by simp))
  rw [if_neg empty_ne_singleton_pt] at h
  have hv : ((((badTrueM (V := V) κ ls).cnst ``Eq [.succ .zero]) ‘ (UProp : V)) ‘ ∅) ‘ ({pt} : V)
      = ({pt} : V) :=
    eqTrueFn_value hm (mem_UProp_iff.2 (by simp)) (mem_UProp_iff.2 (by simp))
  rw [hv] at h
  exact empty_ne_singleton_pt h.symm

variable {envF : VEnv} {nv : ℕ} (L : PropSplit envF nv) (hle : eqEnv ≤ envF)

include hle in
/-- **`EqSpec` is NECESSARY at the recursor cell.**  The six-binder telescope's innermost
obligation fails at `α := ℘{•}`, `a := ∅`, motive `sepMot`, minor premise `•`, `b := {•}`,
`h := •`: the motive separates `a` from `b`, the minor premise supplies the motive only at `a`, and
the constant-true `Eq` lets `b ≠ a` through the major premise.  So
`EqZeroAudit.pt_mem_interp_eqRecType_of_zero`'s hypothesis cannot be dropped and its conclusion is
not free. -/
theorem not_pt_mem_interp_eqRecType_badTrue {n : ℕ} {κ : ℕ → V}
    (hκ : IsInaccessibleChain n κ) (h1 : 0 < n) (ls : List ℕ) :
    (pt : V) ∉ (interp (badTrueM (V := V) κ ls) L []
      ((eqIndDecl.recType 0).instL [.zero, .succ .zero])).toFun ∅ := by
  intro h
  have hm : (UProp : V) ∈ U κ 1 := U_mem_succ hκ h1
  have he : (∅ : V) ∈ (UProp : V) := mem_UProp_iff.2 (by simp)
  have hs : ({pt} : V) ∈ (UProp : V) := mem_UProp_iff.2 (by simp)
  have h0 : (VLevel.zero).eval (badTrueM (V := V) κ ls).ls = 0 := rfl
  have hval : ∀ x ∈ (UProp : V),
      ((((badTrueM (V := V) κ ls).cnst ``Eq [.succ .zero]) ‘ (UProp : V)) ‘ ∅) ‘ x
        = ({pt} : V) := fun x hx ↦ by
    rw [badTrueM_cnst]; exact eqTrueFn_value hm he hx
  rw [eqRecType_instL] at h
  obtain ⟨-, h1'⟩ := (mem_interp_forallE_prop_iff _ L
    (isProp_recBA (Γ := []) (u := .zero) (v := .succ .zero) trivial trivial hle trivial h0)).1 h
  have h2 := h1' (UProp : V) (by rw [interp_sort]; exact hm)
  obtain ⟨-, h3⟩ := (mem_interp_forallE_prop_iff _ L
    (isProp_recBM (Γ := []) (u := .zero) (v := .succ .zero) trivial trivial hle trivial h0)).1 h2
  have h4 := h3 (∅ : V) (by
    rw [interp_bvar]
    simp only [List.length_cons, List.length_nil]
    rw [show (1 - 1 - 0 : ℕ) = 0 from rfl, r1_0]
    exact he)
  obtain ⟨-, h5⟩ := (mem_interp_forallE_prop_iff _ L
    (isProp_recBN (Γ := []) (u := .zero) (v := .succ .zero) trivial trivial hle trivial h0)).1 h4
  have h6 := h5 (sepMot (snoc (snoc (∅ : V) (UProp : V)) ∅))
    (sepMot_mem_interp_motTyE (u := .zero) (v := .succ .zero) trivial trivial hle h0 hval)
  obtain ⟨-, h7⟩ := (mem_interp_forallE_prop_iff _ L
    (isProp_recBB (Γ := []) (u := .zero) (v := .succ .zero) trivial trivial hle trivial h0)).1 h6
  have h8 := h7 (pt : V) (by
    rw [interp_minTyE_val (u := .zero) (v := .succ .zero) trivial trivial hle, sepMot_value_self he]
    exact mem_singleton_iff.2 rfl)
  obtain ⟨-, h9⟩ := (mem_interp_forallE_prop_iff _ L
    (isProp_recBH (Γ := []) (u := .zero) (v := .succ .zero) trivial trivial hle trivial h0)).1 h8
  have h10 := h9 ({pt} : V) (by
    rw [interp_bvar]
    simp only [List.length_cons, List.length_nil]
    rw [show (4 - 1 - 3 : ℕ) = 0 from rfl, r4_0]
    exact hs)
  obtain ⟨-, h11⟩ := (mem_interp_forallE_prop_iff _ L
    (isProp_resE (Γ := []) (u := .zero) (v := .succ .zero) trivial trivial hle trivial h0)).1 h10
  have h12 := h11 (pt : V) (by
    rw [interp_majTyE_val (u := .zero) (v := .succ .zero) trivial trivial hle, hval _ hs]
    exact mem_singleton_iff.2 rfl)
  rw [interp_resE_val (u := .zero) (v := .succ .zero) trivial trivial hle,
    sepMot_value_other hs (Ne.symm empty_ne_singleton_pt)] at h12
  exact not_mem_empty h12

include hle in
/-- The control, packaged: a model agreeing with the witness everywhere but at `Eq`, at which the
`= 0` slice's conclusion **fails**. -/
theorem eqSpec_necessary_at_recursor {n : ℕ} {κ : ℕ → V}
    (hκ : IsInaccessibleChain n κ) (h1 : 0 < n) (ls : List ℕ) :
    ∃ M : ModelData V, M.κ = κ ∧ M.ls = ls ∧ ¬ EqSpec M (.succ .zero) ∧
      (pt : V) ∉ (interp M L []
        ((eqIndDecl.recType 0).instL [.zero, .succ .zero])).toFun ∅ :=
  ⟨badTrueM κ ls, rfl, rfl, not_eqSpec_badTrueM hκ h1 ls,
    not_pt_mem_interp_eqRecType_badTrue L hle hκ h1 ls⟩

end Refute

/-! ## 5. The bracket, at one and the same instantiation

The sharpest form, and the one that rules out the degeneracy the corner has been bitten by before
(*"the same conclusion holds everywhere, with or without the hypothesis"*): at the **same** `κ`,
`ls`, `L`, `hle`, `u := .zero`, `v := .succ .zero`, the membership **holds** at `preludeWitness`
and **fails** at `badTrueM`.  So the recursor cell's conclusion discriminates between assignments,
and `EqSpec` is exactly what separates them. -/

section Bracket

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ} (L : PropSplit envF nv) (hle : eqEnv ≤ envF)

include hle in
theorem recCell_discriminates {n : ℕ} {κ : ℕ → V}
    (hκ : IsInaccessibleChain n κ) (h1 : 0 < n) (ls : List ℕ) :
    ((pt : V) ∈ (interp (preludeWitness κ ls) L []
        ((eqIndDecl.recType 0).instL [.zero, .succ .zero])).toFun ∅) ∧
      (pt : V) ∉ (interp (badTrueM (V := V) κ ls) L []
        ((eqIndDecl.recType 0).instL [.zero, .succ .zero])).toFun ∅ :=
  ⟨EqZeroAudit.pt_mem_interp_eqRecType_of_zero (u := .zero) (v := .succ .zero)
      trivial trivial hle rfl (preludeWitness_eq κ ls _),
   not_pt_mem_interp_eqRecType_badTrue L hle hκ h1 ls⟩

end Bracket

end Lean4Lean.SetModel.EqRecNec

#print axioms Lean4Lean.SetModel.EqRecNec.trueFib_definable
#print axioms Lean4Lean.SetModel.EqRecNec.eqTrueFn_value
#print axioms Lean4Lean.SetModel.EqRecNec.sepFib_definable
#print axioms Lean4Lean.SetModel.EqRecNec.sepMot_value
#print axioms Lean4Lean.SetModel.EqRecNec.sepW_value
#print axioms Lean4Lean.SetModel.EqRecNec.sepMot_value_self
#print axioms Lean4Lean.SetModel.EqRecNec.sepMot_value_other
#print axioms Lean4Lean.SetModel.EqRecNec.sepMot_mem_interp_motTyE
#print axioms Lean4Lean.SetModel.EqRecNec.badTrueM_cnst
#print axioms Lean4Lean.SetModel.EqRecNec.not_eqSpec_badTrueM
#print axioms Lean4Lean.SetModel.EqRecNec.not_pt_mem_interp_eqRecType_badTrue
#print axioms Lean4Lean.SetModel.EqRecNec.eqSpec_necessary_at_recursor
#print axioms Lean4Lean.SetModel.EqRecNec.recCell_discriminates
