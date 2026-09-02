import Lean4Lean.Theory.SetModel.EqZeroSlice
import Lean4Lean.Theory.SetModel.UnitOracleLarge

/-!
# `eqIndDecl`'s **type-former** cell: `Eq ↦ eqFn` lands in `⟦∀ (α : Sort v) (a b : α), Prop⟧`

This is the third and last of `InductOracleOK`'s three `consts` cells at `eqIndDecl`.  The other
two are `EqZeroAudit.pt_mem_interp_eqRecType_of_zero` (the `Eq.rec` cell, `= 0` branch) and
`EqZeroAudit.pt_mem_interp_EqReflType` (the `Eq.refl` cell).

## What is proved, and the hypothesis it needs

```lean
theorem eqFn_mem_interp_EqType (hv : v.WF nv) (hle : eqEnv ≤ envF) :
    eqFn M.κ (v.eval M.ls) ∈ (interp M L [] (eqTypeFormerType v)).toFun ∅
```

and its packaging `mem_interp_EqType_of_eqFn`, whose hypothesis is
`hfn : M.cnst ``Eq [v] = eqFn M.κ (v.eval M.ls)`.

**The hypothesis is `hfn`, not `EqSpec`, and that is the substantive finding of this file.**
The other two cells are `• ∈ …` statements: their conclusion is decided by *applied values*, so
`EqSpec M v` (which pins `(M.cnst ``Eq [v] ‘ α ‘ a ‘ b`) is exactly the right strength.  This
cell's conclusion is `M.cnst ``Eq [v] ∈ …`, i.e. a statement about the value's own **graph** —
`mem_mkForallType_iff` asks that it *be* a set of Kuratowski pairs, functional, with domain
`U M.κ (v.eval M.ls)`.  Nothing of that shape follows from an equation about `‘`, because `‘` is
a *read* of a graph and forgets everything the read does not see.  §3 makes this precise rather
than asserting it: `eqSpec_not_sufficient` exhibits, at the `zeroChain`, a `ModelData` satisfying
`EqSpec` over which the conclusion is **false**.

So the type-former cell is **not** free from `EqSpec`, and it is also **not** expensive: it is
three applications of `UnitAudit.mkLam_mem_mkForallType_of_dom`, one per `mkLam` layer of
`SetModel.eqFn`, exactly as `PreludeOracle.mem_interp_NE_type` is one application for
`nonemptyFn`'s single layer.  What it costs is a *different kind* of hypothesis, and the corner
already pays it: `preludeWitness`'s `Eq` entry **is** `eqFn` (`preludeWitness_cnst_eq`, `rfl`).

## Bounds

`Above` occurs in no statement in this file.  §§1–2 are at an **arbitrary** `κ`, an arbitrary
`ModelData`, and an arbitrary `v` — no chain hypothesis, no inaccessibility, nothing chosen.
The only place a `κ` is named is §3's refutation, which is a **control**; there the chosen
`zeroChain` appears in a negative statement, so it is not a positive bound.
-/

namespace Lean4Lean.SetModel.EqTFAudit

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open Lean4Lean.SetModel.EqAudit
open scoped Classical

/-! ## 1. The type former's type, and its three non-`Prop` binders

`eqEnv_EqC` stores `Eq`'s type as `⟨1, ∀ (α : Sort (param 0)) (a : α), α → Prop⟩`; at `[v]` that
is `eqTypeFormerType v`.  Each of the three binders' codomains has a sort that never evaluates to
`0`, so `interp` takes the `mkForallType` branch three times. -/

/-- `Eq.{v}`'s type, instantiated.  Equal to `(⟨1, …⟩ : VConstant).type.instL [v]` by `rfl`
(`eqTypeFormerType_eq`). -/
abbrev eqTypeFormerType (v : VLevel) : VExpr :=
  .forallE (.sort v) (.forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)))

theorem eqTypeFormerType_eq (v : VLevel) :
    (⟨1, .forallE (.sort (.param 0))
      (.forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)))⟩ : VConstant).type.instL [v]
      = eqTypeFormerType v := rfl

theorem eqEnv_EqC' (v : VLevel) :
    ∃ ci : VConstant, eqEnv.constants ``Eq = some ci ∧ ci.uvars = 1 ∧
      ci.type.instL [v] = eqTypeFormerType v :=
  ⟨_, eqEnv_EqC, rfl, rfl⟩

section IsProp

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ} {L : PropSplit envF nv} {M : ModelData V}
variable {v : VLevel} (hv : v.WF nv) (hle : eqEnv ≤ envF)

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]

/-- `α → Prop` in `ectxP`, typed: its sort is `imax v 1`. -/
theorem hasType_tf3 (Γ : List VExpr) :
    eqEnv.HasType nv (ectxP Γ v) (.forallE (.bvar 1) (.sort .zero))
      (.sort (.imax v (.succ .zero))) :=
  .forallEDF (.bvar (.succ .zero)) (.sortDF trivial trivial rfl)

/-- `∀ (a : α), α → Prop` in `ectxA`, typed: its sort is `imax v (imax v 1)`. -/
theorem hasType_tf2 (Γ : List VExpr) :
    eqEnv.HasType nv (ectxA Γ v) (.forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)))
      (.sort (.imax v (.imax v (.succ .zero)))) :=
  .forallEDF (.bvar .zero) (hasType_tf3 Γ)

include hv hle in
/-- Innermost: `Prop` is not a proposition. -/
theorem not_isProp_tf3 {Γ : List VExpr} (hΓ : OnCtx Γ (eqEnv.IsType nv)) :
    ¬ L.IsProp M (ectxX Γ v) (.sort .zero) := by
  rw [isProp_iff hle (EqZeroAudit.onCtx_X hv hΓ) (VEnv.IsDefEq.sortDF trivial trivial rfl)
    (u := .succ .zero) trivial]
  simp [VLevel.eval]

include hv hle in
/-- Middle: `α → Prop` has sort `imax v 1`, never `0`. -/
theorem not_isProp_tf2 {Γ : List VExpr} (hΓ : OnCtx Γ (eqEnv.IsType nv)) :
    ¬ L.IsProp M (ectxP Γ v) (.forallE (.bvar 1) (.sort .zero)) := by
  rw [isProp_iff hle (EqZeroAudit.onCtx_P hv hΓ) (hasType_tf3 Γ) ⟨hv, trivial⟩]
  simp [VLevel.eval, Lean.Nat.imax]

include hv hle in
/-- Outermost: `∀ (a : α), α → Prop` has sort `imax v (imax v 1)`, never `0`. -/
theorem not_isProp_tf1 {Γ : List VExpr} (hΓ : OnCtx Γ (eqEnv.IsType nv)) :
    ¬ L.IsProp M (ectxA Γ v)
      (.forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero))) := by
  rw [isProp_iff hle (EqZeroAudit.onCtx_A hv hΓ) (hasType_tf2 Γ) ⟨hv, hv, trivial⟩]
  simp [VLevel.eval, Lean.Nat.imax]

end IsProp


/-! ## 2. The cell

Three `mkLam` layers of `SetModel.eqFn` against three `mkForallType` layers of the interpretation,
matched by `UnitAudit.mkLam_mem_mkForallType_of_dom` — the lemma that only asks the two domains to
*agree at the valuation*, which is the whole reason the oracle's domain (`U κ i`, a literal) can
meet `interp`'s (`⟦Sort v⟧∅`). -/

section Cell

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ} {L : PropSplit envF nv} {M : ModelData V}
variable {v : VLevel} (hv : v.WF nv) (hle : eqEnv ≤ envF)

include hv hle in
/-- **The type-former cell.**  `eqFn M.κ (v.eval M.ls) ∈ ⟦∀ (α : Sort v) (a b : α), Prop⟧ ∅`.

Read the three layers off `SetModel.eqFn`: the outer `mkLam` has domain `U κ i` and body
`eqFibA`, whose domain is `ρ ‘ 0` — and `⟦.bvar 0⟧` in `ectxA` is `ρ ‘ 0` too, which is why the
two sides meet with no coercion arithmetic beyond `1 - 1 - 0 = 0`.  The innermost body is
`if a = b then {•} else ∅`, and `Prop`'s interpretation is `U κ 0 = ℘{•}`, which contains both. -/
theorem eqFn_mem_interp_EqType :
    (eqFn M.κ (v.eval M.ls)) ∈
      (interp M L [] (eqTypeFormerType v)).toFun ∅ := by
  rw [show eqTypeFormerType v = VExpr.forallE (.sort v)
      (.forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero))) from rfl,
    interp_forallE_type M L (not_isProp_tf1 (Γ := []) hv hle trivial)]
  unfold eqFn
  refine UnitAudit.mkLam_mem_mkForallType_of_dom (by rw [interp_sort]) (fun α hα ↦ ?_)
  -- layer 2: `eqFibA (snoc ∅ α)` against `⟦∀ (a : α), α → Prop⟧ (snoc ∅ α)`
  rw [interp_forallE_type M L (not_isProp_tf2 (Γ := []) hv hle trivial)]
  unfold eqFibA
  refine UnitAudit.mkLam_mem_mkForallType_of_dom ?_ (fun a _ ↦ ?_)
  · rw [interp_bvar]
    simp only [List.length_cons, List.length_nil]
  -- layer 3: `eqFibB (snoc (snoc ∅ α) a)` against `⟦α → Prop⟧ (snoc (snoc ∅ α) a)`
  rw [interp_forallE_type M L (not_isProp_tf3 (Γ := []) hv hle trivial)]
  unfold eqFibB
  refine UnitAudit.mkLam_mem_mkForallType_of_dom ?_ (fun b _ ↦ ?_)
  · rw [interp_bvar]
    simp only [List.length_cons, List.length_nil]
  rw [interp_sort, show (VLevel.zero.eval M.ls) = 0 from rfl, U_zero]
  split
  · exact true_mem_UProp
  · exact empty_mem_UProp

include hv hle in
/-- **The cell as `OracleOK`'s `type` field wants it**: at any model whose `Eq` entry *is*
`eqFn`.  `hfn` is the hypothesis §3 shows cannot be weakened to `EqSpec`. -/
theorem mem_interp_EqType_of_eqFn (hfn : M.cnst ``Eq [v] = eqFn M.κ (v.eval M.ls)) :
    M.cnst ``Eq [v] ∈
      (interp M L []
        ((⟨1, .forallE (.sort (.param 0))
            (.forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)))⟩ : VConstant).type.instL
          [v])).toFun ∅ := by
  rw [eqTypeFormerType_eq, hfn]
  exact eqFn_mem_interp_EqType hv hle

end Cell

/-! ## 3. `hfn` cannot be weakened to `EqSpec` -- a control

`EqSpec M v` constrains `M.cnst ``Eq [v]` only through `‘`, three reads deep, and only at
arguments drawn from `U M.κ (v.eval M.ls)`.  At the `zeroChain` and any `v` with
`v.eval ls ≠ 0` that domain is **empty** (`EqAudit.U_zeroChain_succ`), so `EqSpec` is
*vacuously true* there for **every** assignment -- while the cell's conclusion still has content,
because `mkForallType` over an empty domain is `{∅}`, so only `∅` inhabits it.  Taking the entry
to be `{•}` therefore satisfies `EqSpec` and refutes the cell.

This is the sharpest available form of the point: it is not that the derivation is hard, it is
that `EqSpec ⊬ cell`, machine-checked. -/

section Control

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]

/-- The `zeroChain` model whose `Eq` entry is the *wrong* set. -/
noncomputable def badEqM (ls : List ℕ) : ModelData V where
  κ := zeroChain
  ls := ls
  cnst := fun n _ => if n = ``Eq then ({pt} : V) else ∅

theorem badEqM_cnst (ls : List ℕ) (us : List VLevel) :
    (badEqM (V := V) ls).cnst ``Eq us = ({pt} : V) := by simp [badEqM]

/-- `EqSpec` holds **vacuously** at `badEqM`, for every level whose evaluation is nonzero:
the quantifier `∀ α ∈ U zeroChain (i+1)` ranges over the empty set. -/
theorem eqSpec_badEqM {ls : List ℕ} {v : VLevel} (hv : v.eval ls ≠ 0) :
    EqSpec (badEqM (V := V) ls) v := by
  intro α hα
  rw [show (badEqM (V := V) ls).κ = zeroChain from rfl,
    show (badEqM (V := V) ls).ls = ls from rfl] at hα
  obtain ⟨j, hj⟩ : ∃ j, v.eval ls = j + 1 := ⟨v.eval ls - 1, by omega⟩
  rw [hj, EqAudit.U_zeroChain_succ] at hα
  exact absurd hα not_mem_empty

/-- **The cell FAILS at `badEqM`.**  The domain `U zeroChain (v.eval ls)` is empty, so
`mkForallType`'s underlying function space is `Y ^ ∅`, whose only member is `∅`; the entry `{•}`
has an element, so it is not a subset of `∅ ×ˢ Y = ∅`. -/
theorem not_mem_interp_EqType_badEqM {envF : VEnv} {nv : ℕ} (L : PropSplit envF nv)
    {ls : List ℕ} {v : VLevel} (hv : v.WF nv) (hle : eqEnv ≤ envF) (hvz : v.eval ls ≠ 0) :
    ¬ ((badEqM (V := V) ls).cnst ``Eq [v] ∈
        (interp (badEqM (V := V) ls) L [] (eqTypeFormerType v)).toFun ∅) := by
  intro h
  rw [badEqM_cnst, show eqTypeFormerType v = VExpr.forallE (.sort v)
      (.forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero))) from rfl,
    interp_forallE_type _ L (not_isProp_tf1 (Γ := []) (M := badEqM (V := V) ls) hv hle trivial)]
    at h
  have hdom : (interp (badEqM (V := V) ls) L [] (VExpr.sort v)).toFun ∅ = (∅ : V) := by
    rw [interp_sort, show (badEqM (V := V) ls).κ = zeroChain from rfl,
      show (badEqM (V := V) ls).ls = ls from rfl]
    obtain ⟨j, hj⟩ : ∃ j, v.eval ls = j + 1 := ⟨v.eval ls - 1, by omega⟩
    rw [hj]; exact EqAudit.U_zeroChain_succ j
  have hfn := (mem_mkForallType_iff.1 h).1
  rw [hdom] at hfn
  have := subset_prod_of_mem_function hfn pt (mem_singleton_iff.2 rfl)
  simp at this

/-- **`EqSpec` does not imply the type-former cell.**  One `ModelData`, one level, `EqSpec`
holding and the cell failing — so `hfn` in `mem_interp_EqType_of_eqFn` is not removable, and the
two other `consts` cells' reliance on `EqSpec` alone does **not** transfer to this one.

Both this statement and the positive `eqFn_mem_interp_EqType` are parametric in the same
`L : PropSplit envF nv`, so the control sits on exactly the footing of the thing it brackets: it
is not made free by anything the positive statement does not also assume. -/
theorem eqSpec_not_sufficient {envF : VEnv} {nv : ℕ} (L : PropSplit envF nv)
    (ls : List ℕ) {v : VLevel} (hv : v.WF nv) (hle : eqEnv ≤ envF) (hvz : v.eval ls ≠ 0) :
    ∃ M : ModelData V, EqSpec M v ∧
      ¬ (M.cnst ``Eq [v] ∈ (interp M L [] (eqTypeFormerType v)).toFun ∅) :=
  ⟨badEqM ls, eqSpec_badEqM hvz, not_mem_interp_EqType_badEqM L hv hle hvz⟩

end Control

/-! ## 4. At the corner's own witness, and as an `OracleOK`

`preludeWitness`'s `Eq` entry *is* `eqFn` — by `rfl`, so `hfn` costs nothing at the assignment
this development already carries.  With the `congr` field (a level computation, as
`NEAudit.neOracle_congr_NE` is) the whole `OracleOK` at the name `Eq` follows. -/

section Witness

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ} (L : PropSplit envF nv) (κ : ℕ → V) (ls : List ℕ)

theorem preludeWitness_cnst_eq (w : VLevel) :
    (preludeWitness (V := V) κ ls).cnst ``Eq [w] = eqFn κ (w.eval ls) := rfl

theorem preludeWitness_congr_Eq {us us' : List VLevel}
    (hd : List.Forall₂ (· ≈ ·) us us') :
    (preludeWitness (V := V) κ ls).cnst ``Eq us
      = (preludeWitness (V := V) κ ls).cnst ``Eq us' := by
  rcases hd with _ | ⟨h, ht⟩
  · rfl
  rcases ht with _ | ⟨h2, ht2⟩
  · rw [preludeWitness_cnst_eq, preludeWitness_cnst_eq, VLevel.equiv_def.mp h ls]
  · rfl

/-- **The type-former cell at `preludeWitness`.** -/
theorem mem_interp_EqType_preludeWitness {v : VLevel} (hv : v.WF nv) (hle : eqEnv ≤ envF) :
    (preludeWitness (V := V) κ ls).cnst ``Eq [v] ∈
      (interp (preludeWitness κ ls) L [] (eqTypeFormerType v)).toFun ∅ := by
  rw [preludeWitness_cnst_eq]
  exact eqFn_mem_interp_EqType hv hle

/-- **`OracleOK` at the name `Eq`** — both fields, at `preludeWitness`'s assignment, for any
`envF` above `eqEnv`.  This is one of the three `consts` cells of `InductOracleOK` at
`eqIndDecl`; see the status table in §5 for what the other two are and which slice of the
recursor's cell is still open.

`Above` is discharged by `Above.pure` in both fields (`oracleOK_of`), so **no chain hypothesis is
used and no `κ` is chosen**: the statement is at an arbitrary `κ : ℕ → V`. -/
theorem oracleOK_Eq (hle : eqEnv ≤ envF) :
    OracleOK L κ ls (preludeWitness κ ls).cnst (preludeWitness κ ls).cnst ``Eq
      ⟨1, .forallE (.sort (.param 0))
        (.forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)))⟩ :=
  oracleOK_of (L := L)
    (fun _ _ hd ↦ preludeWitness_congr_Eq κ ls hd)
    (fun {us} hw hlen ↦ by
      obtain ⟨w, rfl⟩ := NEAudit.eq_singleton_of_length_one hlen
      exact mem_interp_EqType_preludeWitness L κ ls (hw w (List.mem_singleton.2 rfl)) hle)

end Witness

/-! ## 5. Status of `InductOracleOK` at `eqIndDecl` after this file

| obligation | status |
|---|---|
| `consts` at `Eq` (the type former) | **PROVED** here (`oracleOK_Eq`), both `OracleOK` fields, arbitrary `κ` |
| `consts` at `Eq.refl` | **proved** (`EqZeroAudit.pt_mem_interp_EqReflType`), from `EqSpec` alone; level-uniform, since `EqAudit.reflSort_eval_eq_zero` is unconditional |
| `consts` at `Eq.rec`, `u.eval ls = 0` | **proved** (`EqZeroAudit.pt_mem_interp_eqRecType_of_zero`), from `EqSpec` alone |
| `consts` at `Eq.rec`, `u.eval ls ≠ 0` | **OPEN**, and `•` is *refuted* there (`EqAudit.pt_not_mem_interp_eqRecType_of_ne`): the value must be a six-layer `mkLam` |
| `rules` (the one ι-rule) | open |

`OracleOK`'s `type` field quantifies over **all** `us` of the right length, so `Eq.rec`'s cell is
one statement covering both level slices: it is not closed by the `= 0` slice, and cannot be, at
any level-uniform value (`EqAudit.no_level_uniform_value`).  What this file closes is a whole cell,
not a slice of one.

**What is not claimed.**  `InductOracleOK` at `eqIndDecl` is not closed; two of its three `consts`
cells are, and the third has one of its two slices.  Nothing here touches `rules`.
-/

end Lean4Lean.SetModel.EqTFAudit

#print axioms Lean4Lean.SetModel.EqTFAudit.eqTypeFormerType_eq
#print axioms Lean4Lean.SetModel.EqTFAudit.eqEnv_EqC'
#print axioms Lean4Lean.SetModel.EqTFAudit.hasType_tf3
#print axioms Lean4Lean.SetModel.EqTFAudit.hasType_tf2
#print axioms Lean4Lean.SetModel.EqTFAudit.not_isProp_tf3
#print axioms Lean4Lean.SetModel.EqTFAudit.not_isProp_tf2
#print axioms Lean4Lean.SetModel.EqTFAudit.not_isProp_tf1
#print axioms Lean4Lean.SetModel.EqTFAudit.eqFn_mem_interp_EqType
#print axioms Lean4Lean.SetModel.EqTFAudit.mem_interp_EqType_of_eqFn
#print axioms Lean4Lean.SetModel.EqTFAudit.badEqM_cnst
#print axioms Lean4Lean.SetModel.EqTFAudit.eqSpec_badEqM
#print axioms Lean4Lean.SetModel.EqTFAudit.not_mem_interp_EqType_badEqM
#print axioms Lean4Lean.SetModel.EqTFAudit.eqSpec_not_sufficient
#print axioms Lean4Lean.SetModel.EqTFAudit.preludeWitness_cnst_eq
#print axioms Lean4Lean.SetModel.EqTFAudit.preludeWitness_congr_Eq
#print axioms Lean4Lean.SetModel.EqTFAudit.mem_interp_EqType_preludeWitness
#print axioms Lean4Lean.SetModel.EqTFAudit.oracleOK_Eq

