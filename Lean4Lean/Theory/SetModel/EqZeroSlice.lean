import Lean4Lean.Theory.SetModel.EqOracle

/-!
# `eqIndDecl`'s `= 0` slice: `• ∈ ⟦Eq.rec's type⟧` at a `Prop` elimination universe

Handoff §16.10 item 1 / ledger row 149c price this as **the cheapest remaining item** in the
prelude-oracle corner, on the argument that `eqRefl_fields = []` and that `SetModel.eqFn_value` is
already a two-directional equation in the tree.  This file **tests that costing**.

## What is proved

```lean
theorem pt_mem_interp_eqRecType_of_zero (hspec : EqSpec M v) (h0 : u.eval M.ls = 0) :
    (pt : V) ∈ (interp M L [] ((eqIndDecl.recType 0).instL [u, v])).toFun ∅
```

i.e. the `consts` obligation of `InductOracleOK` at the *recursor*, on the `= 0` branch of the
level split `EqAudit.eqRecSort_eval_eq_zero_iff` computes.  Together with
`EqAudit.pt_not_mem_interp_eqRecType_of_ne` (the `≠ 0` branch, which *refutes* the same
membership) this settles both sides of `Eq.rec`'s value question for `•`.

## The one hypothesis, and why it is the right one

`EqSpec M v` (`SetModel/PreludeSpec.lean`) pins the *type former's* oracle value:
`M.cnst ``Eq [v] ‘ α ‘ a ‘ b = if a = b then {•} else ∅`.  It is **not** optional: §5 exhibits a
`ModelData` differing from the prelude witness only in that entry, over which the conclusion is
**false** — so this file's hypothesis is bracketed on both sides, as §6.4/§6.5 of `EqOracle.lean`
bracket that file's.

`EqSpec` is satisfied by `SetModel.preludeWitness` (`preludeWitness_eq`), which is
`PreludeSpec.lean`'s own joint witness for all three prelude specifications, so it is an
assumption the corner already carries rather than a new one.

## Where the costing was right and where it was wrong

* **Right** that no model-side `propext` is needed: the recursor's obligation is discharged from
  `EqSpec` alone, and `Eq.refl`'s absence of fields is why (`eqRefl_fields = []`).
* **Wrong** that this makes `eqIndDecl` *cheaper than* `iffIndDecl`: `SetModel.iffFn_value` is a
  two-directional equation of exactly the same shape, and `IffSpec` is exactly the same kind of
  hypothesis, witnessed by the same `preludeWitness`.  §6 states the transfer explicitly.
* **Understated** in one place, and it is the same place as last round: the level branch is cheap,
  the `interp` bookkeeping is not.  §§1–4 are 40-odd lemmas of `snoc`-reading, `OnCtx`, `IsProp`
  and `¬IsProof` before a single set-theoretic step happens.

## Bounds

`Above` occurs in **no statement** in this file.  Every positive statement is at an **arbitrary**
`κ : ℕ → V` and an arbitrary `ModelData`; the only `κ`-specific object anywhere is in §5's
refutation, which is a *control*.  `hle : eqEnv ≤ envF` is discharged at `preludeEnv` by
`EqAudit.eqEnv_le_preludeEnv`.
-/

namespace Lean4Lean.SetModel.EqZeroAudit

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open Lean4Lean.SetModel.EqAudit
open scoped Classical

/-! ## 1. Reading the environment: the six-`snoc` ladder

`interp_bvar` turns `.bvar i` into `ρ ‘ (Γ.length - 1 - i)`, so every step below needs the value
of a `snoc` chain at a numeral.  `NEAudit` has `read1`–`read4`; `Eq.rec` needs six. -/

section Reads

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {α a f m b h : V}

/-- Peel one `snoc` off a read below the top. -/
theorem read_peel {ρ w : V} {n j : ℕ} (hs : IsSeq ρ n) (hj : j < n) {t : V}
    (ht : ρ ‘ ((j : ℕ) : V) = t) : (snoc ρ w) ‘ ((j : ℕ) : V) = t :=
  (hs.read_lt hj).trans ht

local notation "ρ1" => (snoc (∅ : V) α)
local notation "ρ2" => (snoc (snoc (∅ : V) α) a)
local notation "ρ3" => (snoc (snoc (snoc (∅ : V) α) a) f)
local notation "ρ4" => (snoc (snoc (snoc (snoc (∅ : V) α) a) f) m)
local notation "ρ5" => (snoc (snoc (snoc (snoc (snoc (∅ : V) α) a) f) m) b)
local notation "ρ6" => (snoc (snoc (snoc (snoc (snoc (snoc (∅ : V) α) a) f) m) b) h)

theorem s1 : IsSeq (ρ1) 1 := isSeq_empty.snoc'
theorem s2 : IsSeq (ρ2) 2 := s1.snoc'
theorem s3 : IsSeq (ρ3) 3 := s2.snoc'
theorem s4 : IsSeq (ρ4) 4 := s3.snoc'
theorem s5 : IsSeq (ρ5) 5 := s4.snoc'

theorem r1_0 : (ρ1) ‘ ((0 : ℕ) : V) = α := isSeq_empty.read_top
theorem r2_0 : (ρ2) ‘ ((0 : ℕ) : V) = α := read_peel (j := 0) s1 (by omega) r1_0
theorem r2_1 : (ρ2) ‘ ((1 : ℕ) : V) = a := s1.read_top
theorem r3_0 : (ρ3) ‘ ((0 : ℕ) : V) = α := read_peel (j := 0) s2 (by omega) r2_0
theorem r3_1 : (ρ3) ‘ ((1 : ℕ) : V) = a := read_peel (j := 1) s2 (by omega) r2_1
theorem r3_2 : (ρ3) ‘ ((2 : ℕ) : V) = f := s2.read_top
theorem r4_0 : (ρ4) ‘ ((0 : ℕ) : V) = α := read_peel (j := 0) s3 (by omega) r3_0
theorem r4_1 : (ρ4) ‘ ((1 : ℕ) : V) = a := read_peel (j := 1) s3 (by omega) r3_1
theorem r4_2 : (ρ4) ‘ ((2 : ℕ) : V) = f := read_peel (j := 2) s3 (by omega) r3_2
theorem r5_0 : (ρ5) ‘ ((0 : ℕ) : V) = α := read_peel (j := 0) s4 (by omega) r4_0
theorem r5_1 : (ρ5) ‘ ((1 : ℕ) : V) = a := read_peel (j := 1) s4 (by omega) r4_1
theorem r5_2 : (ρ5) ‘ ((2 : ℕ) : V) = f := read_peel (j := 2) s4 (by omega) r4_2
theorem r5_4 : (ρ5) ‘ ((4 : ℕ) : V) = b := s4.read_top
theorem r6_0 : (ρ6) ‘ ((0 : ℕ) : V) = α := read_peel (j := 0) s5 (by omega) r5_0
theorem r6_1 : (ρ6) ‘ ((1 : ℕ) : V) = a := read_peel (j := 1) s5 (by omega) r5_1
theorem r6_2 : (ρ6) ‘ ((2 : ℕ) : V) = f := read_peel (j := 2) s5 (by omega) r5_2
theorem r6_4 : (ρ6) ‘ ((4 : ℕ) : V) = b := read_peel (j := 4) s5 (by omega) r5_4
theorem r6_5 : (ρ6) ‘ ((5 : ℕ) : V) = h := s5.read_top

end Reads

/-! ## 2. `OnCtx` at all six of `Eq.rec`'s contexts

`isProp_iff`/`isProof_iff` each need `OnCtx Γ (eqEnv.IsType nv)` at the context they are used at
(the guard added 2026-09-02, see `PropSplit`'s docstring), so the whole ladder is needed. -/

section Ctx

variable {nv : ℕ} {u v : VLevel} (hu : u.WF nv) (hv : v.WF nv)
variable {Γ : List VExpr} (hΓ : OnCtx Γ (eqEnv.IsType nv))

include hv hΓ in
theorem onCtx_A : OnCtx (ectxA Γ v) (eqEnv.IsType nv) := ⟨hΓ, _, .sortDF hv hv rfl⟩

include hv hΓ in
theorem onCtx_P : OnCtx (ectxP Γ v) (eqEnv.IsType nv) :=
  ⟨onCtx_A hv hΓ, v, .bvar .zero⟩

include hv hΓ in
theorem onCtx_X : OnCtx (ectxX Γ v) (eqEnv.IsType nv) :=
  ⟨onCtx_P hv hΓ, v, hasType_al_ctxP Γ⟩

include hu hv hΓ in
theorem onCtx_M : OnCtx (ectxM Γ u v) (eqEnv.IsType nv) :=
  ⟨onCtx_P hv hΓ, _, hasType_motTyE hu hv Γ⟩

include hu hv hΓ in
theorem onCtx_N : OnCtx (ectxN Γ u v) (eqEnv.IsType nv) :=
  ⟨onCtx_M hu hv hΓ, u, hasType_minTyE hv Γ⟩

include hu hv hΓ in
theorem onCtx_B : OnCtx (ectxB Γ u v) (eqEnv.IsType nv) :=
  ⟨onCtx_N hu hv hΓ, v, hasType_al_ctxN Γ⟩

include hu hv hΓ in
theorem onCtx_H : OnCtx (ectxH Γ u v) (eqEnv.IsType nv) :=
  ⟨onCtx_B hu hv hΓ, .zero, hasType_majTyE hv Γ⟩

end Ctx

/-! ## 3. Propositionhood of all six bodies, at `u.eval M.ls = 0`

Each of `Eq.rec`'s six binders has a `∀`-sort that is `0` exactly when `u` is (§4 of
`EqOracle.lean`), so at `h0 : u.eval M.ls = 0` every one of them takes the **impredicative**
branch of `interp`.  That is what makes the whole value `•`. -/

section IsPropChain

variable {V : Type*} [SetStructure V] [Nonempty V]
variable {envF : VEnv} {nv : ℕ} {L : PropSplit envF nv} {M : ModelData V}
variable {u v : VLevel} (hu : u.WF nv) (hv : v.WF nv) (hle : eqEnv ≤ envF)
variable {Γ : List VExpr} (hΓ : OnCtx Γ (eqEnv.IsType nv)) (h0 : u.eval M.ls = 0)

include hu hv hle hΓ h0 in
theorem isProp_recBA : L.IsProp M (ectxA Γ v) (recBA u v) :=
  (isProp_iff hle (onCtx_A hv hΓ) (hasType_recBA hu hv Γ)
    (sortAE_wf hu hv)).2 (sortAE_eval_eq_zero_iff.2 h0)

include hu hv hle hΓ h0 in
theorem isProp_recBM : L.IsProp M (ectxP Γ v) (recBM u v) :=
  (isProp_iff hle (onCtx_P hv hΓ) (hasType_recBM hu hv Γ)
    (sortME_wf hu hv)).2 (sortME_eval_eq_zero_iff.2 h0)

include hu hv hle hΓ h0 in
theorem isProp_recBN : L.IsProp M (ectxM Γ u v) (recBN v) :=
  (isProp_iff hle (onCtx_M hu hv hΓ) (hasType_recBN hv Γ)
    (sortNE_wf hu hv)).2 (sortNE_eval_eq_zero_iff.2 h0)

include hu hv hle hΓ h0 in
theorem isProp_recBB : L.IsProp M (ectxN Γ u v) (recBB v) :=
  (isProp_iff hle (onCtx_N hu hv hΓ) (hasType_recBB hv Γ)
    (sortBE_wf hu hv)).2 (sortBE_eval_eq_zero_iff.2 h0)

include hu hv hle hΓ h0 in
theorem isProp_recBH : L.IsProp M (ectxB Γ u v) (recBH v) :=
  (isProp_iff hle (onCtx_B hu hv hΓ) (hasType_recBH hv Γ)
    (sortHE_wf hu)).2 (sortHE_eval_eq_zero_iff.2 h0)

include hu hv hle hΓ h0 in
/-- The innermost body `motive b h` is itself a proposition — its sort *is* `u`. -/
theorem isProp_resE : L.IsProp M (ectxH Γ u v) (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0)) :=
  (isProp_iff hle (onCtx_H hu hv hΓ) (hasType_resE Γ) hu).2 h0

end IsPropChain

/-! ## 4. The proof/value split at every application node

`interp`'s `app` clause tests whether the **function** is a proof, so every partial application
in `Eq α a b`, `motive a (Eq.refl α a)` and `motive b h` needs its own decision.  Ten of them,
and the interesting one is `Eq.refl α`: its type `∀ a : α, Eq α a a` has sort `imax v 0 = 0`, so it
**is** a proof and `interp` discards `a` — which is exactly why `Eq.refl`'s absence of fields
(`eqRefl_fields = []`) costs nothing here. -/

section Split

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ} {L : PropSplit envF nv} {M : ModelData V}
variable {u v : VLevel} (hu : u.WF nv) (hv : v.WF nv) (hle : eqEnv ≤ envF)
variable {Γ : List VExpr} (hΓ : OnCtx Γ (eqEnv.IsType nv)) (h0 : u.eval M.ls = 0)

/-! ### Extra `Lookup`s the audit needs -/

theorem hasType_al_ctxH : eqEnv.HasType nv (ectxH Γ u v) (.bvar 5) (.sort v) :=
  .bvar (.succ (.succ (.succ (.succ (.succ .zero)))))

theorem hasType_a_ctxH : eqEnv.HasType nv (ectxH Γ u v) (.bvar 4) (.bvar 5) :=
  .bvar (.succ (.succ (.succ (.succ .zero))))

/-! ### `Eq`'s three partial applications, at the contexts they occur in -/

section EqNodes

variable {Δ : List VExpr} {i j k : ℕ}

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hv in
/-- `Eq α : α → α → Prop`, for `α = .bvar (i+1)` of type `Sort v`.  The index is written `i+1`
so that the substitution in the second step is uniform (at `.bvar 0` it is not). -/
theorem hasType_eqC1 (hα : eqEnv.HasType nv Δ (.bvar (i + 1)) (.sort v)) :
    eqEnv.HasType nv Δ (.app (.const ``Eq [v]) (.bvar (i + 1)))
      (.forallE (.bvar (i + 1)) (.forallE (.bvar (i + 2)) (.sort .zero))) :=
  hasType_app' (hasType_Eq hv Δ) hα
    (by simp [VExpr.inst, VExpr.instVar, VExpr.liftN, liftVar]; omega)

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
theorem hasType_eqC1Ty (hα : eqEnv.HasType nv Δ (.bvar (i + 1)) (.sort v))
    (hα' : eqEnv.HasType nv ((VExpr.bvar (i + 1)) :: Δ) (.bvar (i + 2)) (.sort v)) :
    eqEnv.HasType nv Δ (.forallE (.bvar (i + 1)) (.forallE (.bvar (i + 2)) (.sort .zero)))
      (.sort (.imax v (.imax v (.succ .zero)))) :=
  .forallEDF hα (.forallEDF hα' (.sortDF trivial trivial rfl))

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hv in
/-- `Eq α a : α → Prop`. -/
theorem hasType_eqC2 (hα : eqEnv.HasType nv Δ (.bvar (i + 1)) (.sort v))
    (ha : eqEnv.HasType nv Δ (.bvar j) (.bvar (i + 1))) :
    eqEnv.HasType nv Δ (.app (.app (.const ``Eq [v]) (.bvar (i + 1))) (.bvar j))
      (.forallE (.bvar (i + 1)) (.sort .zero)) :=
  hasType_app' (hasType_eqC1 hv hα) ha
    (by simp [VExpr.inst, VExpr.instVar])

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
theorem hasType_eqC2Ty (hα : eqEnv.HasType nv Δ (.bvar (i + 1)) (.sort v)) :
    eqEnv.HasType nv Δ (.forallE (.bvar (i + 1)) (.sort .zero))
      (.sort (.imax v (.succ .zero))) :=
  .forallEDF hα (.sortDF trivial trivial rfl)

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hv hle in
theorem not_isProof_eqC0 (hΔ : OnCtx Δ (eqEnv.IsType nv)) :
    ¬ L.IsProof M Δ (.const ``Eq [v]) := by
  rw [isProof_iff hle hΔ (hasType_Eq hv Δ) (hasType_EqType hv Δ) ⟨hv, hv, hv, trivial⟩]
  exact fun hz ↦ Nat.succ_ne_zero _
    (imax_eq_zero_iff.1 (imax_eq_zero_iff.1 (imax_eq_zero_iff.1 hz)))

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hv hle in
theorem not_isProof_eqC1 (hΔ : OnCtx Δ (eqEnv.IsType nv))
    (hα : eqEnv.HasType nv Δ (.bvar (i + 1)) (.sort v))
    (hα' : eqEnv.HasType nv ((VExpr.bvar (i + 1)) :: Δ) (.bvar (i + 2)) (.sort v)) :
    ¬ L.IsProof M Δ (.app (.const ``Eq [v]) (.bvar (i + 1))) := by
  rw [isProof_iff hle hΔ (hasType_eqC1 hv hα) (hasType_eqC1Ty hα hα') ⟨hv, hv, trivial⟩]
  exact fun hz ↦ Nat.succ_ne_zero _ (imax_eq_zero_iff.1 (imax_eq_zero_iff.1 hz))

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hv hle in
theorem not_isProof_eqC2 (hΔ : OnCtx Δ (eqEnv.IsType nv))
    (hα : eqEnv.HasType nv Δ (.bvar (i + 1)) (.sort v))
    (ha : eqEnv.HasType nv Δ (.bvar j) (.bvar (i + 1))) :
    ¬ L.IsProof M Δ (.app (.app (.const ``Eq [v]) (.bvar (i + 1))) (.bvar j)) := by
  rw [isProof_iff hle hΔ (hasType_eqC2 hv hα ha) (hasType_eqC2Ty hα) ⟨hv, trivial⟩]
  exact fun hz ↦ Nat.succ_ne_zero _ (imax_eq_zero_iff.1 hz)

include hv hle in
/-- **`⟦Eq α a b⟧ρ = M.cnst ``Eq [v] ‘ ⟦α⟧ ‘ ⟦a⟧ ‘ ⟦b⟧`**, at any context in which the three
arguments are `.bvar`s of the right types.  Stated generically because it is needed at three
different contexts (`ectxB`, `ectxX`, `ectxM`). -/
theorem interp_eqAp_bvars (hΔ : OnCtx Δ (eqEnv.IsType nv))
    (hα : eqEnv.HasType nv Δ (.bvar (i + 1)) (.sort v))
    (hα' : eqEnv.HasType nv ((VExpr.bvar (i + 1)) :: Δ) (.bvar (i + 2)) (.sort v))
    (ha : eqEnv.HasType nv Δ (.bvar j) (.bvar (i + 1))) (ρ : V) :
    (interp M L Δ (eqAp v (.bvar (i + 1)) (.bvar j) (.bvar k))).toFun ρ
      = (((M.cnst ``Eq [v]) ‘ (ρ ‘ ((Δ.length - 1 - (i + 1) : ℕ) : V)))
          ‘ (ρ ‘ ((Δ.length - 1 - j : ℕ) : V))) ‘ (ρ ‘ ((Δ.length - 1 - k : ℕ) : V)) := by
  show (interp M L Δ (.app (.app (.app (.const ``Eq [v]) (.bvar (i + 1))) (.bvar j))
    (.bvar k))).toFun ρ = _
  rw [interp_app_type M L (not_isProof_eqC2 hv hle hΔ hα ha),
    interp_app_type M L (not_isProof_eqC1 hv hle hΔ hα hα'),
    interp_app_type M L (not_isProof_eqC0 hv hle hΔ),
    interp_const, interp_bvar, interp_bvar, interp_bvar]

end EqNodes

/-! ### The motive's nodes, and the constructor's

`Eq.refl α`'s type is `∀ a : α, Eq α a a`, of sort `imax v 0 = 0` — a **proof**.  So `interp`
discards the second argument and `⟦Eq.refl α a⟧ = •` at every `α` and `a`.  That is the whole of
what `eqRefl_fields = []` buys, made explicit. -/

section MotNodes

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hu hv in
theorem hasType_mot_ctxMTy :
    eqEnv.HasType nv (ectxM Γ u v)
      (.forallE (.bvar 2) (.forallE (eqAp v (.bvar 3) (.bvar 2) (.bvar 0)) (.sort u)))
      (.sort (motSortE u v)) :=
  .forallEDF (hasType_al_ctxM Γ)
    (.forallEDF (hasType_eqAp hv (.bvar (.succ (.succ (.succ .zero))))
      (.bvar (.succ (.succ .zero))) (.bvar .zero)) (.sortDF hu hu rfl))

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hu hv hle hΓ in
/-- The motive variable is **not** a proof: its type's sort is `imax v (imax 0 (u+1))`, which is
`max (v.eval) 1 ≥ 1` even at `u.eval = 0`. -/
theorem not_isProof_mot_ctxM : ¬ L.IsProof M (ectxM Γ u v) (.bvar 0) := by
  rw [isProof_iff hle (onCtx_M hu hv hΓ) (hasType_mot_ctxM Γ) (hasType_mot_ctxMTy hu hv)
    (motSortE_wf hu hv)]
  intro hz
  rw [show (motSortE u v).eval M.ls
      = Lean.Nat.imax (v.eval M.ls) (Lean.Nat.imax 0 (u.eval M.ls + 1)) from rfl] at hz
  exact Nat.succ_ne_zero _ (imax_eq_zero_iff.1 (imax_eq_zero_iff.1 hz))

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hu hv in
theorem hasType_motA_ctxMTy :
    eqEnv.HasType nv (ectxM Γ u v)
      (.forallE (eqAp v (.bvar 2) (.bvar 1) (.bvar 1)) (.sort u))
      (.sort (.imax .zero (.succ u))) :=
  .forallEDF (hasType_eqAp hv (hasType_al_ctxM Γ) (hasType_a_ctxM Γ) (hasType_a_ctxM Γ))
    (.sortDF hu hu rfl)

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hu hv hle hΓ in
theorem not_isProof_motA_ctxM : ¬ L.IsProof M (ectxM Γ u v) (.app (.bvar 0) (.bvar 1)) := by
  rw [isProof_iff hle (onCtx_M hu hv hΓ) (hasType_motA_ctxM Γ) (hasType_motA_ctxMTy hu hv)
    ⟨trivial, hu⟩]
  exact fun hz ↦ Nat.succ_ne_zero _ (imax_eq_zero_iff.1 hz)

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hv in
/-- `Eq.refl α : ∀ a : α, Eq α a a`. -/
theorem hasType_reflC1_ctxM :
    eqEnv.HasType nv (ectxM Γ u v) (.app (.const ``Eq.refl [v]) (.bvar 2))
      (.forallE (.bvar 2) (eqAp v (.bvar 3) (.bvar 0) (.bvar 0))) :=
  hasType_app' (hasType_EqRefl hv (ectxM Γ u v)) (hasType_al_ctxM Γ)
    (by simp [VExpr.inst, VExpr.instVar, VExpr.liftN, liftVar])

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hv in
theorem hasType_reflC1Ty_ctxM :
    eqEnv.HasType nv (ectxM Γ u v)
      (.forallE (.bvar 2) (eqAp v (.bvar 3) (.bvar 0) (.bvar 0)))
      (.sort (.imax v .zero)) :=
  .forallEDF (hasType_al_ctxM Γ)
    (hasType_eqAp hv (.bvar (.succ (.succ (.succ .zero)))) (.bvar .zero) (.bvar .zero))

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hu hv hle hΓ in
/-- **`Eq.refl α` IS a proof.**  `imax v 0 = 0` at every `v`, so this holds with no condition on
the block's universe — and it is why `⟦Eq.refl α a⟧ = •` needs no `EqSpec`. -/
theorem isProof_reflC1_ctxM : L.IsProof M (ectxM Γ u v) (.app (.const ``Eq.refl [v]) (.bvar 2)) :=
  (isProof_iff hle (onCtx_M hu hv hΓ) (hasType_reflC1_ctxM hv) (hasType_reflC1Ty_ctxM hv)
    ⟨hv, trivial⟩).2 (imax_eq_zero_iff.2 rfl)

/-! ### The motive at the innermost context -/

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hu hv in
theorem hasType_mot_ctxHTy :
    eqEnv.HasType nv (ectxH Γ u v)
      (.forallE (.bvar 5) (.forallE (eqAp v (.bvar 6) (.bvar 5) (.bvar 0)) (.sort u)))
      (.sort (motSortE u v)) :=
  .forallEDF (hasType_al_ctxH)
    (.forallEDF (hasType_eqAp hv
        (.bvar (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))
        (.bvar (.succ (.succ (.succ (.succ (.succ .zero)))))) (.bvar .zero))
      (.sortDF hu hu rfl))

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hu hv hle hΓ in
theorem not_isProof_mot_ctxH : ¬ L.IsProof M (ectxH Γ u v) (.bvar 3) := by
  rw [isProof_iff hle (onCtx_H hu hv hΓ) (hasType_mot_ctxH Γ) (hasType_mot_ctxHTy hu hv)
    (motSortE_wf hu hv)]
  intro hz
  rw [show (motSortE u v).eval M.ls
      = Lean.Nat.imax (v.eval M.ls) (Lean.Nat.imax 0 (u.eval M.ls + 1)) from rfl] at hz
  exact Nat.succ_ne_zero _ (imax_eq_zero_iff.1 (imax_eq_zero_iff.1 hz))

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hu hv in
theorem hasType_motB_ctxHTy :
    eqEnv.HasType nv (ectxH Γ u v)
      (.forallE (eqAp v (.bvar 5) (.bvar 4) (.bvar 1)) (.sort u))
      (.sort (.imax .zero (.succ u))) :=
  .forallEDF (hasType_eqAp hv (hasType_al_ctxH) (hasType_a_ctxH) (hasType_b_ctxH Γ))
    (.sortDF hu hu rfl)

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hu hv hle hΓ in
theorem not_isProof_motB_ctxH : ¬ L.IsProof M (ectxH Γ u v) (.app (.bvar 3) (.bvar 1)) := by
  rw [isProof_iff hle (onCtx_H hu hv hΓ) (hasType_motB_ctxH Γ) (hasType_motB_ctxHTy hu hv)
    ⟨trivial, hu⟩]
  exact fun hz ↦ Nat.succ_ne_zero _ (imax_eq_zero_iff.1 hz)

end MotNodes

/-! ### The three interpretation values, at the closed context

Stated at `Γ = []`, which is where the `OracleOK` obligation lives, so the `.bvar` arithmetic is
concrete. -/

section Values

variable {α a f m b hh : V}

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
theorem hasType_alLift_ctxB :
    eqEnv.HasType nv ((VExpr.bvar (3 + 1)) :: ectxB ([] : List VExpr) u v) (.bvar (3 + 2))
      (.sort v) :=
  .bvar (.succ (.succ (.succ (.succ (.succ .zero)))))

include hu hv hle in
/-- **`⟦Eq α a b⟧ = M.cnst ``Eq [v] ‘ α ‘ a ‘ b`** at the major premise's context. -/
theorem interp_majTyE_val :
    (interp M L (ectxB ([] : List VExpr) u v) (majTyE v)).toFun
        (snoc (snoc (snoc (snoc (snoc (∅ : V) α) a) f) m) b)
      = (((M.cnst ``Eq [v]) ‘ α) ‘ a) ‘ b := by
  show (interp M L (ectxB ([] : List VExpr) u v)
    (eqAp v (.bvar (3 + 1)) (.bvar 3) (.bvar 0))).toFun _ = _
  rw [interp_eqAp_bvars hv hle (onCtx_B (Γ := []) hu hv trivial) (hasType_al_ctxB []) hasType_alLift_ctxB
    (hasType_a_ctxB [])]
  simp only [List.length_cons, List.length_nil]
  rw [show (5 - 1 - (3 + 1) : ℕ) = 0 from rfl, show (5 - 1 - 3 : ℕ) = 1 from rfl,
    show (5 - 1 - 0 : ℕ) = 4 from rfl, r5_0, r5_1, r5_4]

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
theorem hasType_alLift_ctxX :
    eqEnv.HasType nv ((VExpr.bvar (1 + 1)) :: ectxX ([] : List VExpr) v) (.bvar (1 + 2))
      (.sort v) :=
  .bvar (.succ (.succ (.succ .zero)))

include hv hle in
/-- **`⟦Eq α a x⟧`** inside the motive's first binder — the domain of the motive's *second*
binder, which is what `f`'s membership is read against. -/
theorem interp_eqApX_val {x : V} :
    (interp M L (ectxX ([] : List VExpr) v) (eqAp v (.bvar 2) (.bvar 1) (.bvar 0))).toFun
        (snoc (snoc (snoc (∅ : V) α) a) x)
      = (((M.cnst ``Eq [v]) ‘ α) ‘ a) ‘ x := by
  show (interp M L (ectxX ([] : List VExpr) v)
    (eqAp v (.bvar (1 + 1)) (.bvar 1) (.bvar 0))).toFun _ = _
  rw [interp_eqAp_bvars hv hle (onCtx_X (Γ := []) hv trivial) (hasType_al_ctxX []) hasType_alLift_ctxX
    (hasType_a_ctxX [])]
  simp only [List.length_cons, List.length_nil]
  rw [show (3 - 1 - (1 + 1) : ℕ) = 0 from rfl, show (3 - 1 - 1 : ℕ) = 1 from rfl,
    show (3 - 1 - 0 : ℕ) = 2 from rfl, r3_0, r3_1, r3_2]

include hu hv hle in
/-- **`⟦motive a (Eq.refl α a)⟧ = (f ‘ a) ‘ •`.**  The constructor application is a proof, so
`interp` discards `a` — `eqRefl_fields = []` in action. -/
theorem interp_minTyE_val :
    (interp M L (ectxM ([] : List VExpr) u v) (minTyE v)).toFun
        (snoc (snoc (snoc (∅ : V) α) a) f)
      = (f ‘ a) ‘ (pt : V) := by
  show (interp M L (ectxM ([] : List VExpr) u v)
    (.app (.app (.bvar 0) (.bvar 1)) (.app (.app (.const ``Eq.refl [v]) (.bvar 2))
      (.bvar 1)))).toFun _ = _
  rw [interp_app_type M L (not_isProof_motA_ctxM (Γ := []) hu hv hle trivial),
    interp_app_type M L (not_isProof_mot_ctxM (Γ := []) hu hv hle trivial),
    interp_app_proof M L (isProof_reflC1_ctxM (Γ := []) hu hv hle trivial), interp_bvar, interp_bvar]
  simp only [List.length_cons, List.length_nil]
  rw [show (3 - 1 - 0 : ℕ) = 2 from rfl, show (3 - 1 - 1 : ℕ) = 1 from rfl, r3_1, r3_2]

include hu hv hle in
/-- **`⟦motive b h⟧ = (f ‘ b) ‘ h`** at the innermost context. -/
theorem interp_resE_val :
    (interp M L (ectxH ([] : List VExpr) u v)
        (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0))).toFun
        (snoc (snoc (snoc (snoc (snoc (snoc (∅ : V) α) a) f) m) b) hh)
      = (f ‘ b) ‘ hh := by
  rw [interp_app_type M L (not_isProof_motB_ctxH (Γ := []) hu hv hle trivial),
    interp_app_type M L (not_isProof_mot_ctxH (Γ := []) hu hv hle trivial), interp_bvar, interp_bvar,
    interp_bvar]
  simp only [List.length_cons, List.length_nil]
  rw [show (6 - 1 - 3 : ℕ) = 2 from rfl, show (6 - 1 - 1 : ℕ) = 4 from rfl,
    show (6 - 1 - 0 : ℕ) = 5 from rfl, r6_2, r6_4, r6_5]

end Values

/-! ### The motive's own type: its values land in `UProp`

This is the step the `= 0` slice cannot avoid.  The goal `• ∈ f ‘ b ‘ h` is not implied by the
minor premise's *inhabitation* alone — it needs the set `f ‘ b ‘ h` to be a **subset of `{•}`**,
which is what `motive`'s own type says once it is read at `u.eval = 0`.  Note that the motive's
type is *not* a proposition (its sort is `imax v (imax 0 (u+1))`, which is `≥ 1`), so this is a
`mkForallType`, twice. -/

section MotSpace

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hv hΓ in
theorem onCtx_XH : OnCtx (ectxXH Γ v) (eqEnv.IsType nv) :=
  ⟨onCtx_X hv hΓ, .zero, hasType_eqAp_ctxX hv Γ⟩

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hu hv hle hΓ in
theorem not_isProp_motInner :
    ¬ L.IsProp M (ectxX Γ v) (.forallE (eqAp v (.bvar 2) (.bvar 1) (.bvar 0)) (.sort u)) := by
  rw [isProp_iff hle (onCtx_X hv hΓ)
    (VEnv.IsDefEq.forallEDF (hasType_eqAp_ctxX hv Γ) (.sortDF hu hu rfl)) ⟨trivial, hu⟩]
  exact fun hz ↦ Nat.succ_ne_zero _ (imax_eq_zero_iff.1 hz)

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hu hv hle hΓ in
theorem not_isProp_sortu : ¬ L.IsProp M (ectxXH Γ v) (.sort u) := by
  rw [isProp_iff hle (onCtx_XH hv hΓ) (VEnv.IsDefEq.sortDF hu hu rfl) hu]
  exact fun hz ↦ Nat.succ_ne_zero _ hz

/-- **A member of a `mkForallType` really is a function on the stated domain.**  The graph
condition plus `IsFunction` give the value's membership; the same three lines appear inline in
`QuotInterp.quotLift_fCod`, and this is the reusable form. -/
theorem value_mem_of_mem_mkForallType {G : V → V} {hG : ℒₛₑₜ-function₁[V] G} {F : V → V → V}
    {hF : ℒₛₑₜ-function₂[V] F} {ρ g : V} (hg : g ∈ mkForallType G hG F hF ρ)
    {x : V} (hx : x ∈ G ρ) : g ‘ x ∈ F ρ x := by
  obtain ⟨hfn, hgr⟩ := mem_mkForallType_iff.1 hg
  have hfun : IsFunction g := IsFunction.of_mem hfn
  obtain ⟨y, hy, -⟩ := (mem_function_iff.1 hfn).2 x hx
  exact hgr x hx _ (by rw [value_eq_of_kpair_mem hy]; exact hy)

include hu hv hle h0 in
/-- **What the motive binder gives**: at `u.eval = 0` every value of the motive is a truth
value. -/
theorem motive_value_mem_UProp {α a f x w : V}
    (hf : f ∈ (interp M L (ectxP ([] : List VExpr) v) (motTyE u v)).toFun
      (snoc (snoc (∅ : V) α) a))
    (hxα : x ∈ α) (hw : w ∈ (((M.cnst ``Eq [v]) ‘ α) ‘ a) ‘ x) :
    (f ‘ x) ‘ w ∈ (UProp : V) := by
  rw [show motTyE u v = VExpr.forallE (.bvar 1)
      (.forallE (eqAp v (.bvar 2) (.bvar 1) (.bvar 0)) (.sort u)) from rfl,
    interp_forallE_type M L (not_isProp_motInner (Γ := []) hu hv hle trivial)] at hf
  have hdom : (interp M L (ectxP ([] : List VExpr) v) (.bvar 1)).toFun
      (snoc (snoc (∅ : V) α) a) = α := by
    rw [interp_bvar]
    simp only [List.length_cons, List.length_nil]
    rw [show (2 - 1 - 1 : ℕ) = 0 from rfl]
    exact r2_0
  have h1 := value_mem_of_mem_mkForallType hf (x := x) (by rw [hdom]; exact hxα)
  rw [interp_forallE_type M L (not_isProp_sortu (Γ := []) hu hv hle trivial)] at h1
  have h2 := value_mem_of_mem_mkForallType h1 (x := w)
    (by rw [interp_eqApX_val hv hle]; exact hw)
  rwa [interp_sort, h0, U_zero] at h2

end MotSpace

end Split

/-! ## 5. The `= 0` slice

`InductOracleOK`'s `consts` field at `Eq.rec` on the `= 0` branch of the level split.  Compare
`EqAudit.pt_not_mem_interp_eqRecType_of_ne`, which **refutes** the same membership on the `≠ 0`
branch; together the two are the whole of `Eq.rec`'s value question for `•`. -/

section Slice

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ} {L : PropSplit envF nv} {M : ModelData V}
variable {u v : VLevel} (hu : u.WF nv) (hv : v.WF nv) (hle : eqEnv ≤ envF)
variable (h0 : u.eval M.ls = 0)

include hu hv hle h0 in
/-- **`• ∈ ⟦Eq.rec's type⟧` at every `Prop` instantiation of the elimination universe.**

The six binders are all impredicative at `u.eval M.ls = 0` (§3), so `interp` returns a
`mkForallProp` at each and `•` is the only candidate; the content is the innermost obligation

> for all `α ∈ U κ (v.eval ls)`, `a ∈ α`, every motive `f`, every minor premise `m`, every
> `b ∈ α` and every `w ∈ ⟦Eq α a b⟧`, `• ∈ f ‘ b ‘ w`

and it is discharged from **`EqSpec M v` alone**: `⟦Eq α a b⟧` is `{•}` when `a = b` and `∅`
otherwise, so `w` forces `b = a` and `w = •`, at which point `f ‘ b ‘ w` is literally the minor
premise's own type (`interp_minTyE_val`), inhabited by `m`, and a subset of `{•}` because the
motive's values are truth values at `u.eval = 0` (`motive_value_mem_UProp`).

**No model-side `propext` is spent**, which is the substantive half of ledger row 149c's costing
and the half that is right.  See §6 for the half that is not. -/
theorem pt_mem_interp_eqRecType_of_zero (hspec : EqSpec M v) :
    (pt : V) ∈ (interp M L [] ((eqIndDecl.recType 0).instL [u, v])).toFun ∅ := by
  rw [eqRecType_instL]
  refine (mem_interp_forallE_prop_iff M L
    (isProp_recBA (Γ := []) hu hv hle trivial h0)).2 ⟨rfl, fun α hα ↦ ?_⟩
  rw [interp_sort] at hα
  refine (mem_interp_forallE_prop_iff M L
    (isProp_recBM (Γ := []) hu hv hle trivial h0)).2 ⟨rfl, fun a ha ↦ ?_⟩
  rw [interp_bvar] at ha
  simp only [List.length_cons, List.length_nil] at ha
  rw [show (1 - 1 - 0 : ℕ) = 0 from rfl, r1_0] at ha
  refine (mem_interp_forallE_prop_iff M L
    (isProp_recBN (Γ := []) hu hv hle trivial h0)).2 ⟨rfl, fun f hf ↦ ?_⟩
  refine (mem_interp_forallE_prop_iff M L
    (isProp_recBB (Γ := []) hu hv hle trivial h0)).2 ⟨rfl, fun m hm ↦ ?_⟩
  refine (mem_interp_forallE_prop_iff M L
    (isProp_recBH (Γ := []) hu hv hle trivial h0)).2 ⟨rfl, fun b hb ↦ ?_⟩
  rw [interp_bvar] at hb
  simp only [List.length_cons, List.length_nil] at hb
  rw [show (4 - 1 - 3 : ℕ) = 0 from rfl, r4_0] at hb
  refine (mem_interp_forallE_prop_iff M L
    (isProp_resE (Γ := []) hu hv hle trivial h0)).2 ⟨rfl, fun w hw ↦ ?_⟩
  rw [interp_majTyE_val hu hv hle, hspec α hα a ha b hb] at hw
  by_cases hab : a = b
  · rw [if_pos hab] at hw
    obtain rfl : w = (pt : V) := mem_singleton_iff.mp hw
    subst hab
    rw [interp_resE_val hu hv hle]
    rw [interp_minTyE_val hu hv hle] at hm
    have hU := motive_value_mem_UProp hu hv hle h0 hf ha
      (by rw [hspec α hα a ha a ha, if_pos rfl]; exact mem_singleton_iff.2 rfl)
    have hmp := mem_singleton_iff.mp (mem_UProp_iff.mp hU _ hm)
    exact hmp ▸ hm
  · rw [if_neg hab] at hw
    exact absurd hw not_mem_empty

/-! ### 5.1 `Eq.refl ↦ •`, the second `consts` cell

Handoff §16.10 item 3 calls this "the small-eliminator argument" and the cheapest remaining
`consts` cell.  **Confirmed**: with §§1–4 in place it is nine lines, and `EqSpec` is the only
hypothesis.  Note that `reflSort_eval_eq_zero` holds at **every** `v` and needs no `h0`, so
unlike the recursor this cell has no level branch at all. -/

theorem eqReflType_instL (v : VLevel) :
    ((⟨1, .forallE (.sort (.param 0))
        (.forallE (.bvar 0)
          (.app (.app (.app (.const ``Eq [.param 0]) (.bvar 1)) (.bvar 0)) (.bvar 0)))⟩
      : VConstant).type.instL [v])
      = .forallE (.sort v) (.forallE (.bvar 0) (eqAp v (.bvar 1) (.bvar 0) (.bvar 0))) := rfl

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hv hle in
theorem isProp_reflBody {Γ : List VExpr} (hΓ : OnCtx Γ (eqEnv.IsType nv)) :
    L.IsProp M (ectxA Γ v) (.forallE (.bvar 0) (eqAp v (.bvar 1) (.bvar 0) (.bvar 0))) :=
  (isProp_iff hle (onCtx_A hv hΓ)
    (VEnv.IsDefEq.forallEDF (.bvar .zero)
      (hasType_eqAp hv (hasType_al_ctxP Γ) (hasType_a_ctxP Γ) (hasType_a_ctxP Γ)))
    ⟨hv, trivial⟩).2 (imax_eq_zero_iff.2 rfl)

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hv hle in
theorem isProp_eqApRefl {Γ : List VExpr} (hΓ : OnCtx Γ (eqEnv.IsType nv)) :
    L.IsProp M (ectxP Γ v) (eqAp v (.bvar 1) (.bvar 0) (.bvar 0)) :=
  (isProp_iff hle (onCtx_P hv hΓ)
    (hasType_eqAp hv (hasType_al_ctxP Γ) (hasType_a_ctxP Γ) (hasType_a_ctxP Γ)) trivial).2 rfl

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
theorem hasType_alLift_ctxP :
    eqEnv.HasType nv ((VExpr.bvar (0 + 1)) :: ectxP ([] : List VExpr) v) (.bvar (0 + 2))
      (.sort v) :=
  .bvar (.succ (.succ .zero))

include hv hle in
theorem interp_eqApP_val {α a : V} :
    (interp M L (ectxP ([] : List VExpr) v)
        (eqAp v (.bvar 1) (.bvar 0) (.bvar 0))).toFun (snoc (snoc (∅ : V) α) a)
      = (((M.cnst ``Eq [v]) ‘ α) ‘ a) ‘ a := by
  show (interp M L (ectxP ([] : List VExpr) v)
    (eqAp v (.bvar (0 + 1)) (.bvar 0) (.bvar 0))).toFun _ = _
  rw [interp_eqAp_bvars hv hle (onCtx_P (Γ := []) hv trivial) (hasType_al_ctxP [])
    hasType_alLift_ctxP (hasType_a_ctxP [])]
  simp only [List.length_cons, List.length_nil]
  rw [show (2 - 1 - (0 + 1) : ℕ) = 0 from rfl, show (2 - 1 - 0 : ℕ) = 1 from rfl, r2_0, r2_1]

include hv hle in
/-- **`• ∈ ⟦Eq.refl's type⟧`** — the `consts` obligation at the constructor.  Both binders are
impredicative at **every** `v` (`reflSort_eval_eq_zero`), and the innermost step is `EqSpec` at
`a = a`. -/
theorem pt_mem_interp_EqReflType (hspec : EqSpec M v) :
    (pt : V) ∈ (interp M L []
        (.forallE (.sort v) (.forallE (.bvar 0)
          (eqAp v (.bvar 1) (.bvar 0) (.bvar 0))))).toFun ∅ := by
  refine (mem_interp_forallE_prop_iff M L
    (isProp_reflBody hv hle (Γ := []) trivial)).2 ⟨rfl, fun α hα ↦ ?_⟩
  rw [interp_sort] at hα
  refine (mem_interp_forallE_prop_iff M L
    (isProp_eqApRefl hv hle (Γ := []) trivial)).2 ⟨rfl, fun a ha ↦ ?_⟩
  rw [interp_bvar] at ha
  simp only [List.length_cons, List.length_nil] at ha
  rw [show (1 - 1 - 0 : ℕ) = 0 from rfl, r1_0] at ha
  rw [interp_eqApP_val hv hle, hspec α hα a ha a ha, if_pos rfl]
  exact mem_singleton_iff.2 rfl

include hv hle in
/-- **`EqSpec` is necessary at the constructor cell, and the bound is unconditional in the
oracle.**  If the oracle's `Eq` value is *empty* at any reflexive instance the model actually
reaches, `•` is **not** in `⟦Eq.refl's type⟧` — so `pt_mem_interp_EqReflType`'s hypothesis cannot
be dropped, and the conclusion is not free.

Contrast the *recursor* cell, where the corresponding negative bound needs the oracle to be too
*true* rather than too empty, and therefore needs a motive separating two elements of `α` — a
two-layer `mkLam` this file does **not** build.  `PreludeOracle.lean` line 905 asserts the
analogous control for `Nonempty` in prose; the only negative bound that file actually proves
(`not_mem_interp_zeroOracle_NE_type`) is of *this* cheap shape, at the type former. -/
theorem not_pt_mem_interp_EqReflType_of_empty {α a : V}
    (hα : α ∈ U M.κ (v.eval M.ls)) (ha : a ∈ α)
    (hbad : (((M.cnst ``Eq [v]) ‘ α) ‘ a) ‘ a = (∅ : V)) :
    (pt : V) ∉ (interp M L []
        (.forallE (.sort v) (.forallE (.bvar 0)
          (eqAp v (.bvar 1) (.bvar 0) (.bvar 0))))).toFun ∅ := by
  intro h
  obtain ⟨-, h1⟩ := (mem_interp_forallE_prop_iff M L
    (isProp_reflBody hv hle (Γ := []) trivial)).1 h
  have h2 := h1 α (by rw [interp_sort]; exact hα)
  obtain ⟨-, h3⟩ := (mem_interp_forallE_prop_iff M L
    (isProp_eqApRefl hv hle (Γ := []) trivial)).1 h2
  have h4 := h3 a (by
    rw [interp_bvar]
    simp only [List.length_cons, List.length_nil]
    rw [show (1 - 1 - 0 : ℕ) = 0 from rfl, r1_0]
    exact ha)
  rw [interp_eqApP_val hv hle, hbad] at h4
  exact not_mem_empty h4

end Slice

/-! ## 6. Where ledger row 149c's costing is wrong, and the part of the correction that is
measurable

Row 149c prices `eqIndDecl`'s `= 0` slice below `iffIndDecl`'s on the grounds that
`SetModel.eqFn_value` "is already a two-directional equation in the tree" while `iffIndDecl`
needs the model-side `propext`.  §5 confirms the *conclusion* about `eqIndDecl` — no `propext` is
spent — but **the reason given does not distinguish the two blocks**:

* `SetModel.iffFn_value : ((iffFn : V) ‘ p) ‘ q = if p = q then {•} else ∅` is a two-directional
  equation of **exactly the same shape** (`#check`ed);
* `EqSpec` and `IffSpec` are the same kind of hypothesis, and **both** are discharged by the
  *same* witness, `SetModel.preludeWitness` (`preludeWitness_eq`, `preludeWitness_iff`);
* row 149c's own measurement — `iffIntro_fields_length = 2` versus `eqRefl_fields = []` — is about
  **`Iff.intro`'s** obligation, and §16.5 says so.  It therefore prices the *constructor* cell,
  not the recursor's slice.

What does differ at the recursor, and it is a structural fact of the tree rather than a reading:
`IffAudit.minTyI` (an `abbrev` whose shape is `rfl`) is

```lean
.forallE (.forallE (.bvar 2) (.bvar 2))                    -- x : a → b
  (.forallE (.forallE (.bvar 2) (.bvar 4))                 -- y : b → a
    (.app (.bvar 2) (introAp (.bvar 4) (.bvar 3) (.bvar 1) (.bvar 0))))
```

i.e. `Iff.rec`'s minor premise carries the constructor's **two field binders**, where
`EqAudit.minTyE` carries none.  So extracting `• ∈ f ‘ •` from a minor premise at `iffIndDecl`
must first traverse them, which needs `⟦a → b⟧` and `⟦b → a⟧` to be **inhabited** — and by then
`IffSpec` has already delivered `a = b` from the major premise, so both are `⟦a → a⟧`, whose
inhabitation is `pt_mem_mkForallProp_self` below and costs nothing.

**So the `= 0` slice at `iffIndDecl` should not need the model-side `propext` either**, and row
146b / §15.3's "the hard half is `propext`" looks misattributed at the *recursor* — as §16.5
already suspected for the wrong reason.  **This paragraph is a costing, not a theorem**: the
`iffIndDecl` slice was not attempted (it needs its own copies of §§1–4, about forty lemmas).  The
one crux that *is* measurable without them is below. -/

section Transfer

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]

/-- **`⟦p → p⟧` is inhabited at every truth value `p`.**  This is the crux of §6's claim that
`Iff.rec`'s `= 0` slice needs no model-side `propext`: once `IffSpec` has forced `a = b`, the
constructor's two field binders are both of this shape.  A proposition is a subset of `{•}`, so a
member of the domain *is* `•`, and the codomain is the domain. -/
theorem pt_mem_mkForallProp_self {p : V} (hp : p ∈ (UProp : V))
    {hG : ℒₛₑₜ-function₁[V] (fun _ : V ↦ p)} {hF : ℒₛₑₜ-function₂[V] (fun _ _ : V ↦ p)}
    (ρ : V) : (pt : V) ∈ mkForallProp (fun _ ↦ p) hG (fun _ _ ↦ p) hF ρ :=
  mem_mkForallProp_iff.2 ⟨rfl, fun w hw ↦ mem_singleton_iff.mp (mem_UProp_iff.mp hp w hw) ▸ hw⟩

end Transfer

end Lean4Lean.SetModel.EqZeroAudit
