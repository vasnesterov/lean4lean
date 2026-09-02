import Lean4Lean.Theory.SetModel.PreludeRecGap

/-!
# `iffIndDecl`'s `≠ 0` slice: the five-layer `mkLam` at `Iff.rec`

`PreludeRecGap.lean` §6 prices this file and leaves one question open, in its own words the
sharpest in the corner: `RecGap.preludeWitness_not_mem_interp_iffRecType` is a **negation**, and a
negation is free if `⟦Iff.rec's type⟧` is empty at `u.eval ls ≠ 0`.  So either the cell is
satisfiable by an unwritten `iffRecFn`, or the block's obligation is unsatisfiable and no witness
repair can ever discharge it.

**Answer: the cell is SATISFIABLE.**  `iffRecFn_mem_interp_iffRecType` exhibits a member.
-/

namespace Lean4Lean.SetModel.IffLargeAudit

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open Lean4Lean.SetModel.IffAudit
open Lean4Lean.SetModel.EqZeroAudit
open scoped Classical

/-! ## 1--3. **RELOCATED to `PreludeSpec.lean`**

`mkForallProp_ext`, the three definability lemmas (`iffAt_definable`, `appPt_definable₂`,
`minAppPt_definable₂`), the five-layer `mkLam` nest (`impSet`, `minSet`, `motSetI`, `lamHI`,
`lamNI`, `lamFI`, `lamBI`, `iffRecFn` and their `_definable` companions) and `iffRecVal` used to be
defined here.  They now live in `PreludeSpec.lean`, for the same reason `EqRecLarge.lean` §§1--3 do:
`SetModel.preludeWitness` has to *mention* `iffRecVal`, and `PreludeSpec.lean` sits eight files
upstream.  Compiling the payload against `PreludeSpec.lean`'s own import surface shows it needs
nothing this file adds (`docs/handoff-setmodel.md` §22.5).

Re-exported below, so every `IffLargeAudit.…` use site still resolves unchanged. -/

export Lean4Lean.SetModel (mkForallProp_ext iffAt_definable appPt_definable₂ minAppPt_definable₂
  impSet impSet_definable minSet minSet_definable motSetI motSetI_definable lamHI lamHI_definable
  lamNI lamNI_definable lamFI lamFI_definable lamBI lamBI_definable iffRecFn iffRecVal
  iffRecVal_single)

/-! ## 4. `OnCtx` at all five of `Iff.rec`'s contexts, plus the two inside the minor premise

`isProp_iff`/`isProof_iff` each need `OnCtx Δ (iffEnv.IsType nv)` at the context they are used at,
so the whole ladder is needed.  `IffOracle.lean` supplies the first two (`onCtxI_A`, `onCtxI_B`);
the remaining six are here, and two of them (`ictxPa`, `ictxQb`) are *inside* the constructor's
field types, which is where this block's extra work lives. -/

section Ctx

variable {nv : ℕ} {u : VLevel} (hu : u.WF nv)
variable {Γ : List VExpr} (hΓ : OnCtx Γ (iffEnv.IsType nv))

include hu hΓ in
theorem onCtxI_M : OnCtx (ictxM Γ u) (iffEnv.IsType nv) :=
  ⟨onCtxI_B hΓ, _, hasType_motTyI hu Γ⟩

include hu hΓ in
theorem onCtxI_N : OnCtx (ictxN Γ u) (iffEnv.IsType nv) :=
  ⟨onCtxI_M hu hΓ, _, hasType_minTyI Γ⟩

include hu hΓ in
theorem onCtxI_H : OnCtx (ictxH Γ u) (iffEnv.IsType nv) :=
  ⟨onCtxI_N hu hΓ, .zero, hasType_majTyI Γ⟩

include hu hΓ in
theorem onCtxI_P : OnCtx (ictxP Γ u) (iffEnv.IsType nv) :=
  ⟨onCtxI_M hu hΓ, _, hasType_mpTyI Γ⟩

include hu hΓ in
theorem onCtxI_Q : OnCtx (ictxQ Γ u) (iffEnv.IsType nv) :=
  ⟨onCtxI_P hu hΓ, _, hasType_mprTyI Γ⟩

include hu hΓ in
/-- `x : a` **inside** `mp`'s own arrow. -/
theorem onCtxI_Pa : OnCtx (ictxPa Γ u) (iffEnv.IsType nv) :=
  ⟨onCtxI_M hu hΓ, .zero, hasType_a_ctxM Γ⟩

include hu hΓ in
/-- `y : b` inside `mpr`'s own arrow. -/
theorem onCtxI_Qb : OnCtx (ictxQb Γ u) (iffEnv.IsType nv) :=
  ⟨onCtxI_P hu hΓ, .zero, hasType_b_ctxP Γ⟩

include hΓ in
/-- `x : Iff a b` inside the motive's own domain. -/
theorem onCtxI_I : OnCtx (ictxI Γ) (iffEnv.IsType nv) :=
  ⟨onCtxI_B hΓ, .zero, hasType_iffAp_ctxB Γ⟩

end Ctx

/-! ## 5. The extra typing derivations: the constructor's partial applications and the motive

The three `hasType`s below are the ones `IffOracle.lean` §3 does not isolate: it builds
`hasType_introAp_ctxQ` as one four-fold `.appDF` chain, so the *intermediate* types — which is
what `interp`'s `app` clause tests — never appear.  `hasType_introC3` names the third one, and its
sort is `imax (imax 0 0) 0 = 0`: **`Iff.intro a b mp` is a proof**, so `interp` discards `mpr` and
then the whole application. -/

section Typing

variable {nv : ℕ} {u : VLevel} (hu : u.WF nv)
variable (Γ : List VExpr)

/-- `a : Prop` at the recursor's innermost context. -/
theorem hasType_a_ctxH : iffEnv.HasType nv (ictxH Γ u) (.bvar 4) (.sort .zero) :=
  .bvar (.succ (.succ (.succ (.succ .zero))))

/-- `b : Prop` at the recursor's innermost context. -/
theorem hasType_b_ctxH : iffEnv.HasType nv (ictxH Γ u) (.bvar 3) (.sort .zero) :=
  .bvar (.succ (.succ (.succ .zero)))

/-- `Iff : Prop → Prop → Prop`'s own type, with its sort. -/
theorem hasType_IffTy {Δ : List VExpr} :
    iffEnv.HasType nv Δ (.forallE (.sort .zero) (.forallE (.sort .zero) (.sort .zero)))
      (.sort (.imax (.succ .zero) (.imax (.succ .zero) (.succ .zero)))) :=
  .forallEDF (.sortDF trivial trivial rfl)
    (.forallEDF (.sortDF trivial trivial rfl) (.sortDF trivial trivial rfl))

/-- `Iff p : Prop → Prop`. -/
theorem hasType_iffC1 {Δ : List VExpr} {p : VExpr}
    (hp : iffEnv.HasType nv Δ p (.sort .zero)) :
    iffEnv.HasType nv Δ (.app (.const ``Iff []) p) (.forallE (.sort .zero) (.sort .zero)) :=
  .appDF (hasType_Iff Δ) hp

theorem hasType_iffC1Ty {Δ : List VExpr} :
    iffEnv.HasType nv Δ (.forallE (.sort .zero) (.sort .zero))
      (.sort (.imax (.succ .zero) (.succ .zero))) :=
  .forallEDF (.sortDF trivial trivial rfl) (.sortDF trivial trivial rfl)

/-- **`Iff.intro a b mp : (b → a) → Iff a b`** — the third partial application, the one whose
type is a proposition.  Its shape was **measured** (`#eval` on the `.inst` chain that
`IffOracle.hasType_introAp_ctxQ` leaves implicit), not read off. -/
theorem hasType_introC3 :
    iffEnv.HasType nv (ictxQ Γ u)
      (.app (.app (.app (.const ``Iff.intro []) (.bvar 4)) (.bvar 3)) (.bvar 1))
      (.forallE (.forallE (.bvar 3) (.bvar 5)) (iffAp (.bvar 5) (.bvar 4))) :=
  .appDF (.appDF (.appDF (hasType_IffIntro (ictxQ Γ u)) (hasType_a_ctxQ Γ))
    (hasType_b_ctxQ Γ)) (.bvar (.succ .zero))

/-- …and its sort, `imax (imax 0 0) 0`, which evaluates to `0` at **every** level valuation. -/
theorem hasType_introC3Ty :
    iffEnv.HasType nv (ictxQ Γ u)
      (.forallE (.forallE (.bvar 3) (.bvar 5)) (iffAp (.bvar 5) (.bvar 4)))
      (.sort (.imax mpSortI .zero)) :=
  .forallEDF
    (.forallEDF (hasType_b_ctxQ Γ)
      (.bvar (.succ (.succ (.succ (.succ (.succ .zero)))))))
    (hasType_iffAp (.bvar (.succ (.succ (.succ (.succ (.succ .zero))))))
      (.bvar (.succ (.succ (.succ (.succ .zero))))))

include hu in
/-- The motive's own type, at any context reading `a` at `4` and `b` at `3` — which is both
`ictxQ` and `ictxH`. -/
theorem hasType_motTy_gen {Δ : List VExpr}
    (ha : iffEnv.HasType nv Δ (.bvar 4) (.sort .zero))
    (hb : iffEnv.HasType nv Δ (.bvar 3) (.sort .zero)) :
    iffEnv.HasType nv Δ (.forallE (iffAp (.bvar 4) (.bvar 3)) (.sort u)) (.sort (motSortI u)) :=
  .forallEDF (hasType_iffAp ha hb) (.sortDF hu hu rfl)

/-- The inner half of the minor premise, `∀ mpr : b → a, motive (Iff.intro a b mp mpr)`, with its
sort `imax (imax 0 0) u`. -/
theorem hasType_minInner :
    iffEnv.HasType nv (ictxP Γ u)
      (.forallE (.forallE (.bvar 2) (.bvar 4))
        (.app (.bvar 2) (introAp (.bvar 4) (.bvar 3) (.bvar 1) (.bvar 0))))
      (.sort (.imax mpSortI u)) :=
  .forallEDF (hasType_mprTyI Γ) (hasType_minBodyI Γ)

end Typing

/-! ## 6. The proof/value split, and non-propositionhood of all five bodies at `u.eval ≠ 0`

`EqAudit.sort*_eval_eq_zero_iff`'s twins are `IffAudit.sort{H,N,M,B}_eval_eq_zero_iff`, all already
in the tree, so every one of the five `∀`-sorts is `0` **exactly** when `u` is: at `hn` every
binder takes the `mkForallType` branch.  Two extra decisions have no `Eq` counterpart — the two
field spaces `a → b` and `b → a` are propositions (`isProp_mpCod`, `isProp_mprCod`), so `interp`
takes the *impredicative* branch at them, and `Iff.intro a b mp` **is a proof**
(`isProof_introC3`). -/

section Split

variable {V : Type*} [SetStructure V] [Nonempty V]
variable {envF : VEnv} {nv : ℕ} {L : PropSplit envF nv} {M : ModelData V}
variable {u : VLevel} (hu : u.WF nv) (hle : iffEnv ≤ envF)
variable {Γ : List VExpr} (hΓ : OnCtx Γ (iffEnv.IsType nv)) (hn : u.eval M.ls ≠ 0)

include hu hle hΓ hn in
theorem not_isProp_recBB : ¬ L.IsProp M (ictxA Γ) (recBB u) := fun h ↦
  hn (sortB_eval_eq_zero_iff.1
    ((isProp_iff hle (onCtxI_A hΓ) (hasType_recBB hu Γ) (sortB_wf hu)).1 h))

include hu hle hΓ hn in
theorem not_isProp_recBM : ¬ L.IsProp M (ictxB Γ) (recBM u) := fun h ↦
  hn (sortM_eval_eq_zero_iff.1
    ((isProp_iff hle (onCtxI_B hΓ) (hasType_recBM hu Γ) (sortM_wf hu)).1 h))

include hu hle hΓ hn in
theorem not_isProp_recBN : ¬ L.IsProp M (ictxM Γ u) recBN := fun h ↦
  hn (sortN_eval_eq_zero_iff.1
    ((isProp_iff hle (onCtxI_M hu hΓ) (hasType_recBN Γ) (sortN_wf hu)).1 h))

include hu hle hΓ hn in
theorem not_isProp_recBH : ¬ L.IsProp M (ictxN Γ u) recBH := fun h ↦
  hn (sortH_eval_eq_zero_iff.1
    ((isProp_iff hle (onCtxI_N hu hΓ) (hasType_recBH Γ) (sortH_wf hu)).1 h))

include hu hle hΓ hn in
/-- The innermost body `motive h` has sort `u` itself. -/
theorem not_isProp_resI : ¬ L.IsProp M (ictxH Γ u) (.app (.bvar 2) (.bvar 0)) := fun h ↦
  hn ((isProp_iff hle (onCtxI_H hu hΓ) (hasType_resI Γ) hu).1 h)

include hu hle hΓ hn in
/-- The inner half of the minor premise: sort `imax (imax 0 0) u`. -/
theorem not_isProp_minInner :
    ¬ L.IsProp M (ictxP Γ u)
      (.forallE (.forallE (.bvar 2) (.bvar 4))
        (.app (.bvar 2) (introAp (.bvar 4) (.bvar 3) (.bvar 1) (.bvar 0)))) := fun h ↦
  hn (imax_eq_zero_iff.1
    ((isProp_iff hle (onCtxI_P hu hΓ) (hasType_minInner Γ) ⟨⟨trivial, trivial⟩, hu⟩).1 h))

include hu hle hΓ hn in
theorem not_isProp_minBody :
    ¬ L.IsProp M (ictxQ Γ u)
      (.app (.bvar 2) (introAp (.bvar 4) (.bvar 3) (.bvar 1) (.bvar 0))) := fun h ↦
  hn ((isProp_iff hle (onCtxI_Q hu hΓ) (hasType_minBodyI Γ) hu).1 h)

include hu hle hΓ in
/-- The motive's codomain `Sort u` is never a proposition, at any level. -/
theorem not_isProp_sortuI : ¬ L.IsProp M (ictxI Γ) (.sort u) := by
  rw [isProp_iff hle (onCtxI_I hΓ) (VEnv.IsDefEq.sortDF hu hu rfl) hu]
  exact fun hz ↦ Nat.succ_ne_zero _ hz

include hu hle hΓ in
/-- **`mp`'s codomain `b` IS a proposition** — so `⟦a → b⟧` is `mkForallProp`, the impredicative
branch.  `Eq.rec`'s minor premise had no such binder. -/
theorem isProp_mpCod : L.IsProp M (ictxPa Γ u) (.bvar 2) :=
  (isProp_iff hle (onCtxI_Pa hu hΓ) (hasType_b_ctxPa Γ) trivial).2 rfl

include hu hle hΓ in
theorem isProp_mprCod : L.IsProp M (ictxQb Γ u) (.bvar 4) :=
  (isProp_iff hle (onCtxI_Qb hu hΓ) (hasType_a_ctxQb Γ) trivial).2 rfl

include hle in
theorem not_isProof_iffC0 {Δ : List VExpr} (hΔ : OnCtx Δ (iffEnv.IsType nv)) :
    ¬ L.IsProof M Δ (.const ``Iff []) := by
  rw [isProof_iff hle hΔ (hasType_Iff Δ) hasType_IffTy ⟨trivial, trivial, trivial⟩]
  exact fun hz ↦ Nat.succ_ne_zero _ (imax_eq_zero_iff.1 (imax_eq_zero_iff.1 hz))

include hle in
theorem not_isProof_iffC1 {Δ : List VExpr} {p : VExpr} (hΔ : OnCtx Δ (iffEnv.IsType nv))
    (hp : iffEnv.HasType nv Δ p (.sort .zero)) :
    ¬ L.IsProof M Δ (.app (.const ``Iff []) p) := by
  rw [isProof_iff hle hΔ (hasType_iffC1 hp) hasType_iffC1Ty ⟨trivial, trivial⟩]
  exact fun hz ↦ Nat.succ_ne_zero _ (imax_eq_zero_iff.1 hz)

include hu hle in
/-- The motive variable is **not** a proof: its type's sort is `imax 0 (u+1) = u+1`. -/
theorem not_isProof_mot_gen {Δ : List VExpr} (hΔ : OnCtx Δ (iffEnv.IsType nv))
    (hmot : iffEnv.HasType nv Δ (.bvar 2) (.forallE (iffAp (.bvar 4) (.bvar 3)) (.sort u)))
    (ha : iffEnv.HasType nv Δ (.bvar 4) (.sort .zero))
    (hb : iffEnv.HasType nv Δ (.bvar 3) (.sort .zero)) :
    ¬ L.IsProof M Δ (.bvar 2) := by
  rw [isProof_iff hle hΔ hmot (hasType_motTy_gen hu ha hb) ⟨trivial, hu⟩]
  exact fun hz ↦ Nat.succ_ne_zero _ (imax_eq_zero_iff.1 hz)

include hu hle hΓ in
/-- **`Iff.intro a b mp` IS a proof**, at every level valuation: its type `(b → a) → Iff a b` has
sort `imax (imax 0 0) 0`, and `imax _ 0 = 0`.  So `interp` discards `mpr` and the constructor
application as a whole is `•`.  **This is the step with no counterpart in `EqRecLarge.lean`** —
there the discarded head was `Eq.refl α`, a proof for the same reason but with no field binders
above it. -/
theorem isProof_introC3 :
    L.IsProof M (ictxQ Γ u)
      (.app (.app (.app (.const ``Iff.intro []) (.bvar 4)) (.bvar 3)) (.bvar 1)) :=
  (isProof_iff hle (onCtxI_Q hu hΓ) (hasType_introC3 Γ) (hasType_introC3Ty Γ)
    ⟨⟨trivial, trivial⟩, trivial⟩).2 (imax_eq_zero_iff.2 rfl)

end Split

/-! ## 7. The four interpretation values, at the closed context

Stated at `Γ = []`, which is where the `OracleOK` obligation lives, so the `.bvar` arithmetic is
concrete.  The reads reuse `EqZeroAudit`'s `snoc` ladder verbatim: `Iff.rec`'s five-entry tower
`a, b, f, min, h` sits at the same indices as `Eq.rec`'s first five, so `r2_*`–`r5_*` instantiate
directly. -/

section Values

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ} {L : PropSplit envF nv} {M : ModelData V}
variable {u : VLevel} (hu : u.WF nv) (hle : iffEnv ≤ envF)

include hle in
/-- **`⟦Iff p q⟧ρ = M.cnst ``Iff [] ‘ ⟦p⟧ρ ‘ ⟦q⟧ρ`**, at any context in which the two arguments
are `.bvar`s of type `Prop`.  Stated generically because it is needed at three contexts
(`ictxB`, `ictxN`, and — via the motive's domain — `ictxB` again). -/
theorem interp_iffAp_bvars {Δ : List VExpr} {i j : ℕ} (hΔ : OnCtx Δ (iffEnv.IsType nv))
    (hp : iffEnv.HasType nv Δ (.bvar i) (.sort .zero))
    (_hq : iffEnv.HasType nv Δ (.bvar j) (.sort .zero)) (ρ : V) :
    (interp M L Δ (iffAp (.bvar i) (.bvar j))).toFun ρ
      = ((M.cnst ``Iff []) ‘ (ρ ‘ ((Δ.length - 1 - i : ℕ) : V)))
          ‘ (ρ ‘ ((Δ.length - 1 - j : ℕ) : V)) := by
  show (interp M L Δ (.app (.app (.const ``Iff []) (.bvar i)) (.bvar j))).toFun ρ = _
  rw [interp_app_type M L (not_isProof_iffC1 hle hΔ hp),
    interp_app_type M L (not_isProof_iffC0 hle hΔ), interp_const, interp_bvar, interp_bvar]

variable {a b f m hh : V}

include hle in
/-- `⟦Iff a b⟧` at the two-parameter context — the motive binder's domain. -/
theorem interp_iffAp_ctxB :
    (interp M L (ictxB ([] : List VExpr)) (iffAp (.bvar 1) (.bvar 0))).toFun
        (snoc (snoc (∅ : V) a) b)
      = ((M.cnst ``Iff []) ‘ a) ‘ b := by
  rw [interp_iffAp_bvars hle (onCtxI_B (Γ := []) trivial) (hasType_a_ctxB []) (hasType_b_ctxB [])]
  simp only [List.length_cons, List.length_nil]
  rw [show (2 - 1 - 1 : ℕ) = 0 from rfl, show (2 - 1 - 0 : ℕ) = 1 from rfl,
    EqZeroAudit.r2_0, EqZeroAudit.r2_1]

include hu hle in
/-- `⟦Iff a b⟧` at the major premise's context. -/
theorem interp_majTyI_val :
    (interp M L (ictxN ([] : List VExpr) u) majTyI).toFun
        (snoc (snoc (snoc (snoc (∅ : V) a) b) f) m)
      = ((M.cnst ``Iff []) ‘ a) ‘ b := by
  show (interp M L (ictxN ([] : List VExpr) u) (iffAp (.bvar 3) (.bvar 2))).toFun _ = _
  rw [interp_iffAp_bvars hle (onCtxI_N (Γ := []) hu trivial)
    (.bvar (.succ (.succ (.succ .zero)))) (.bvar (.succ (.succ .zero)))]
  simp only [List.length_cons, List.length_nil]
  rw [show (4 - 1 - 3 : ℕ) = 0 from rfl, show (4 - 1 - 2 : ℕ) = 1 from rfl,
    EqZeroAudit.r4_0, EqZeroAudit.r4_1]

include hu hle in
/-- **`⟦motive h⟧ = f ‘ h`** at the recursor's innermost context. -/
theorem interp_resI_val :
    (interp M L (ictxH ([] : List VExpr) u) (.app (.bvar 2) (.bvar 0))).toFun
        (snoc (snoc (snoc (snoc (snoc (∅ : V) a) b) f) m) hh)
      = f ‘ hh := by
  rw [interp_app_type M L (not_isProof_mot_gen hu hle (onCtxI_H (Γ := []) hu trivial)
      (hasType_mot_ctxH []) (hasType_a_ctxH []) (hasType_b_ctxH [])),
    interp_bvar, interp_bvar]
  simp only [List.length_cons, List.length_nil]
  rw [show (5 - 1 - 2 : ℕ) = 2 from rfl, show (5 - 1 - 0 : ℕ) = 4 from rfl,
    EqZeroAudit.r5_2, EqZeroAudit.r5_4]

include hu hle in
/-- **`⟦motive (Iff.intro a b mp mpr)⟧ = f ‘ •`.**  The constructor application is a proof, so all
four arguments are discarded — the `Iff` analogue of `EqZeroAudit.interp_minTyE_val`, except that
here two of the discarded arguments are *bound variables of the minor premise itself*. -/
theorem interp_minBody_val {mp mpr : V} :
    (interp M L (ictxQ ([] : List VExpr) u)
        (.app (.bvar 2) (introAp (.bvar 4) (.bvar 3) (.bvar 1) (.bvar 0)))).toFun
        (snoc (snoc (snoc (snoc (snoc (∅ : V) a) b) f) mp) mpr)
      = f ‘ (pt : V) := by
  rw [interp_app_type M L (not_isProof_mot_gen hu hle (onCtxI_Q (Γ := []) hu trivial)
      (hasType_mot_ctxQ []) (hasType_a_ctxQ []) (hasType_b_ctxQ [])),
    interp_app_proof M L (isProof_introC3 (Γ := []) hu hle trivial), interp_bvar]
  simp only [List.length_cons, List.length_nil]
  rw [show (5 - 1 - 2 : ℕ) = 2 from rfl, EqZeroAudit.r5_2]

end Values

/-! ## 8. The two domains the oracle must spell for itself

`motSetI` is the motive binder's domain and `minSet` the minor premise's.  Both have to be written
*without* `interp` (the oracle cannot call it) and then identified with `interp`'s spelling.  The
motive's is one `mkForallType` and spends `IffSpec`, exactly as `EqLargeAudit.motSet_eq_interp_motTyE`
spends `EqSpec`.  The minor premise's is **two** `mkForallType`s whose domains are
`mkForallProp`s — four `_ext` steps, and the only place `mkForallProp_ext` is used. -/

section Domains

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ} {L : PropSplit envF nv} {M : ModelData V}
variable {u : VLevel} (hu : u.WF nv) (hle : iffEnv ≤ envF)

include hu hle in
/-- **The motive binder's domain, as the oracle spells it.** -/
theorem motSetI_eq_interp_motTyI (hspec : IffSpec M) {a b : V}
    (ha : a ∈ (UProp : V)) (hb : b ∈ (UProp : V)) :
    motSetI M.κ (u.eval M.ls) (snoc (snoc (∅ : V) a) b)
      = (interp M L (ictxB ([] : List VExpr)) (motTyI u)).toFun (snoc (snoc (∅ : V) a) b) := by
  rw [show motTyI u = VExpr.forallE (iffAp (.bvar 1) (.bvar 0)) (.sort u) from rfl,
    interp_forallE_type M L (not_isProp_sortuI (Γ := []) hu hle trivial)]
  unfold motSetI
  refine EqLargeAudit.mkForallType_ext ?_ (fun x _ ↦ (interp_sort ..).symm)
  rw [interp_iffAp_ctxB hle, EqZeroAudit.r2_0, EqZeroAudit.r2_1, iffFn_value ha hb,
    hspec a ha b hb]

include hu hle in
/-- **`⟦a → b⟧ = impSet 0 1`** — `mp`'s type, the impredicative branch, factored out because
**both** level slices need it: the `≠ 0` slice to match the value's domain, the `= 0` slice to
know the space is inhabited. -/
theorem impSet01_eq_interp_mpTy {a b f : V} :
    impSet 0 1 (snoc (snoc (snoc (∅ : V) a) b) f)
      = (interp M L (ictxM ([] : List VExpr) u) (.forallE (.bvar 2) (.bvar 2))).toFun
          (snoc (snoc (snoc (∅ : V) a) b) f) := by
  rw [interp_forallE_prop M L (isProp_mpCod (Γ := []) hu hle trivial)]
  unfold impSet
  refine mkForallProp_ext ?_ (fun x _ ↦ ?_)
  · rw [interp_bvar]
    simp only [List.length_cons, List.length_nil]
  · rw [interp_bvar]
    simp only [List.length_cons, List.length_nil]
    rw [show (4 - 1 - 2 : ℕ) = 1 from rfl, EqZeroAudit.r3_1,
      EqZeroAudit.read_peel (j := 1) EqZeroAudit.s3 (by omega) EqZeroAudit.r3_1]

include hu hle in
/-- **`⟦b → a⟧ = impSet 1 0`** — `mpr`'s type, one binder further in. -/
theorem impSet10_eq_interp_mprTy {a b f mp : V} :
    impSet 1 0 (snoc (snoc (snoc (snoc (∅ : V) a) b) f) mp)
      = (interp M L (ictxP ([] : List VExpr) u) (.forallE (.bvar 2) (.bvar 4))).toFun
          (snoc (snoc (snoc (snoc (∅ : V) a) b) f) mp) := by
  rw [interp_forallE_prop M L (isProp_mprCod (Γ := []) hu hle trivial)]
  unfold impSet
  refine mkForallProp_ext ?_ (fun y _ ↦ ?_)
  · rw [interp_bvar]
    simp only [List.length_cons, List.length_nil]
  · rw [interp_bvar]
    simp only [List.length_cons, List.length_nil]
    rw [show (5 - 1 - 4 : ℕ) = 0 from rfl, EqZeroAudit.r4_0,
      EqZeroAudit.read_peel (j := 0) EqZeroAudit.s4 (by omega) EqZeroAudit.r4_0]

include hu hle in
/-- **The minor premise's domain, as the oracle spells it.**  The step with no counterpart in
`EqRecLarge.lean`: two `mkForallType` layers over `mkForallProp` domains, with the constructor's
denotation `•` appearing inside the motive's argument.  This one is `≠ 0`-only: at `u.eval = 0`
`minTyI` is itself a proposition and `interp` takes the impredicative branch here too. -/
theorem minSet_eq_interp_minTyI (hn : u.eval M.ls ≠ 0) {a b f : V} :
    minSet (snoc (snoc (snoc (∅ : V) a) b) f)
      = (interp M L (ictxM ([] : List VExpr) u) minTyI).toFun
          (snoc (snoc (snoc (∅ : V) a) b) f) := by
  rw [show (minTyI : VExpr) = .forallE (.forallE (.bvar 2) (.bvar 2))
      (.forallE (.forallE (.bvar 2) (.bvar 4))
        (.app (.bvar 2) (introAp (.bvar 4) (.bvar 3) (.bvar 1) (.bvar 0)))) from rfl,
    interp_forallE_type M L (not_isProp_minInner (Γ := []) hu hle trivial hn)]
  unfold minSet
  refine EqLargeAudit.mkForallType_ext (impSet01_eq_interp_mpTy hu hle) (fun mp _ ↦ ?_)
  rw [interp_forallE_type M L (not_isProp_minBody (Γ := []) hu hle trivial hn)]
  refine EqLargeAudit.mkForallType_ext (impSet10_eq_interp_mprTy hu hle) (fun mpr _ ↦ ?_)
  rw [interp_minBody_val hu hle, EqZeroAudit.r4_2]

end Domains

/-! ## 9. Inhabitation of the two field spaces

Once the major premise exists, `IffSpec` has already forced `a = b`, so both field spaces are
`⟦a → a⟧` and `•` inhabits each — the crux `EqZeroSlice.lean` §6 flagged as the reason
`Iff.rec` needs **no** model-side `propext`.  Confirmed here, and it is what makes the value's body
`min • •` legal. -/

section Inhabit

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]

theorem pt_mem_impSet01 {a b f : V} (ha : a ∈ (UProp : V)) (hab : a = b) :
    (pt : V) ∈ impSet 0 1 (snoc (snoc (snoc (∅ : V) a) b) f) := by
  unfold impSet
  refine mem_mkForallProp_iff.2 ⟨rfl, fun v hv ↦ ?_⟩
  rw [EqZeroAudit.r3_0] at hv
  rw [EqZeroAudit.r3_1, ← hab]
  exact mem_singleton_iff.mp (mem_UProp_iff.mp ha v hv) ▸ hv

theorem pt_mem_impSet10 {a b f mp : V} (ha : a ∈ (UProp : V)) (hab : a = b) :
    (pt : V) ∈ impSet 1 0 (snoc (snoc (snoc (snoc (∅ : V) a) b) f) mp) := by
  unfold impSet
  refine mem_mkForallProp_iff.2 ⟨rfl, fun v hv ↦ ?_⟩
  rw [EqZeroAudit.r4_1, ← hab] at hv
  rw [EqZeroAudit.r4_0]
  exact mem_singleton_iff.mp (mem_UProp_iff.mp ha v hv) ▸ hv

end Inhabit

/-! ## 10. The `≠ 0` slice — **the answer to `PreludeRecGap` §6's open question**

Five applications of `UnitAudit.mkLam_mem_mkForallType_of_dom`, one per binder, and one hypothesis:
`IffSpec M`, the same one the type-former cell needs.

The innermost step is where this block differs in kind from `Eq.rec`.  There the goal was
`m ∈ f ‘ b ‘ h` with `m` the minor premise itself.  Here it is `(m ‘ • ) ‘ • ∈ f ‘ h`: the minor
premise has to be **applied to the constructor's two fields** first, `IffSpec` collapses `h` to `•`
and `a` to `b`, and §9 supplies the two field values. -/

section Slice

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ} {L : PropSplit envF nv} {M : ModelData V}
variable {u : VLevel} (hu : u.WF nv) (hle : iffEnv ≤ envF)

include hu hle in
/-- **`iffRecFn ∈ ⟦Iff.rec's type⟧` at every non-`Prop` instantiation of the elimination
universe.**  So the `Iff.rec` cell is **SATISFIABLE**: `⟦Iff.rec's type⟧` is *not* empty at
`u.eval M.ls ≠ 0`, and `RecGap.preludeWitness_not_mem_interp_iffRecType` is therefore a refutation
of the shared witness rather than a free negation. -/
theorem iffRecFn_mem_interp_iffRecType (hspec : IffSpec M) (hn : u.eval M.ls ≠ 0) :
    iffRecFn M.κ (u.eval M.ls) ∈
      (interp M L [] ((iffIndDecl.recType 0).instL [u])).toFun ∅ := by
  rw [iffRecType_instL, interp_forallE_type M L (not_isProp_recBB (Γ := []) hu hle trivial hn)]
  unfold iffRecFn
  refine UnitAudit.mkLam_mem_mkForallType_of_dom (by rw [interp_sort]; rfl) (fun a ha ↦ ?_)
  have ha' : a ∈ (UProp : V) := by rw [interp_sort] at ha; exact ha
  -- layer 2: the second parameter `b : Prop`
  rw [interp_forallE_type M L (not_isProp_recBM (Γ := []) hu hle trivial hn)]
  unfold lamBI
  refine UnitAudit.mkLam_mem_mkForallType_of_dom (by rw [interp_sort]; rfl) (fun b hb ↦ ?_)
  have hb' : b ∈ (UProp : V) := by rw [interp_sort] at hb; exact hb
  -- layer 3: the motive
  rw [interp_forallE_type M L (not_isProp_recBN (Γ := []) hu hle trivial hn)]
  unfold lamFI
  refine UnitAudit.mkLam_mem_mkForallType_of_dom
    (motSetI_eq_interp_motTyI hu hle hspec ha' hb') (fun f hf ↦ ?_)
  -- layer 4: the minor premise
  rw [interp_forallE_type M L (not_isProp_recBH (Γ := []) hu hle trivial hn)]
  unfold lamNI
  refine UnitAudit.mkLam_mem_mkForallType_of_dom
    (minSet_eq_interp_minTyI hu hle hn) (fun m hm ↦ ?_)
  rw [← minSet_eq_interp_minTyI hu hle hn] at hm
  -- layer 5: the major premise `h : Iff a b`
  rw [interp_forallE_type M L (not_isProp_resI (Γ := []) hu hle trivial hn)]
  unfold lamHI
  refine UnitAudit.mkLam_mem_mkForallType_of_dom
    (by rw [EqZeroAudit.r4_0, EqZeroAudit.r4_1, iffFn_value ha' hb',
      interp_majTyI_val hu hle, hspec a ha' b hb']) (fun hh hhh ↦ ?_)
  rw [interp_majTyI_val hu hle, hspec a ha' b hb'] at hhh
  rw [interp_resI_val hu hle, EqLargeAudit.r4_3]
  by_cases hab : a = b
  · rw [if_pos hab] at hhh
    obtain rfl : hh = (pt : V) := mem_singleton_iff.mp hhh
    unfold minSet at hm
    have h1 := EqZeroAudit.value_mem_of_mem_mkForallType hm
      (x := (pt : V)) (pt_mem_impSet01 ha' hab)
    have h2 := EqZeroAudit.value_mem_of_mem_mkForallType h1
      (x := (pt : V)) (pt_mem_impSet10 ha' hab)
    rwa [EqZeroAudit.r4_2] at h2
  · rw [if_neg hab] at hhh
    exact absurd hhh not_mem_empty

end Slice

/-! ## 11. The `= 0` slice — `IffOracle.lean` §7's fourth row, **CLOSED**

`IffAudit`'s status table lists `• ∈ ⟦Iff.rec's type⟧` at `u.eval = 0` as OPEN, and its §7
prediction was that this slice would need **`iffFn`'s faithfulness in both directions**, i.e. the
model-side shadow of `propext`.  `EqZeroSlice.lean` §6 then argued the opposite, as a *costing*.
The costing is **right**: `IffSpec` alone suffices, and the reason is exactly the one §6 gave —
once the major premise exists, `a = b`, so the constructor's two field spaces are both `⟦a → a⟧`
and `•` inhabits each (§9).  `PreludeSpec.propext_of_mem_UProp` is **not** used.

With both slices in hand the whole `Iff.rec` `consts` cell closes (§13). -/

section SliceZero

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ} {L : PropSplit envF nv} {M : ModelData V}
variable {u : VLevel} (hu : u.WF nv) (hle : iffEnv ≤ envF)
variable {Γ : List VExpr} (hΓ : OnCtx Γ (iffEnv.IsType nv)) (h0 : u.eval M.ls = 0)

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hu hle hΓ h0 in
theorem isProp_recBB_of_zero : L.IsProp M (ictxA Γ) (recBB u) :=
  (isProp_iff hle (onCtxI_A hΓ) (hasType_recBB hu Γ) (sortB_wf hu)).2
    (sortB_eval_eq_zero_iff.2 h0)

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hu hle hΓ h0 in
theorem isProp_recBM_of_zero : L.IsProp M (ictxB Γ) (recBM u) :=
  (isProp_iff hle (onCtxI_B hΓ) (hasType_recBM hu Γ) (sortM_wf hu)).2
    (sortM_eval_eq_zero_iff.2 h0)

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hu hle hΓ h0 in
theorem isProp_recBN_of_zero : L.IsProp M (ictxM Γ u) recBN :=
  (isProp_iff hle (onCtxI_M hu hΓ) (hasType_recBN Γ) (sortN_wf hu)).2
    (sortN_eval_eq_zero_iff.2 h0)

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hu hle hΓ h0 in
theorem isProp_recBH_of_zero : L.IsProp M (ictxN Γ u) recBH :=
  (isProp_iff hle (onCtxI_N hu hΓ) (hasType_recBH Γ) (sortH_wf hu)).2
    (sortH_eval_eq_zero_iff.2 h0)

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hu hle hΓ h0 in
theorem isProp_resI_of_zero : L.IsProp M (ictxH Γ u) (.app (.bvar 2) (.bvar 0)) :=
  (isProp_iff hle (onCtxI_H hu hΓ) (hasType_resI Γ) hu).2 h0

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hu hle hΓ h0 in
/-- At `u.eval = 0` the minor premise is itself a proposition, so `interp` takes the
**impredicative** branch at the two field binders too — which is why `minSet` is `≠ 0`-only. -/
theorem isProp_minInner_of_zero :
    L.IsProp M (ictxP Γ u)
      (.forallE (.forallE (.bvar 2) (.bvar 4))
        (.app (.bvar 2) (introAp (.bvar 4) (.bvar 3) (.bvar 1) (.bvar 0)))) :=
  (isProp_iff hle (onCtxI_P hu hΓ) (hasType_minInner Γ) ⟨⟨trivial, trivial⟩, hu⟩).2
    (imax_eq_zero_iff.2 h0)

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hu hle hΓ h0 in
theorem isProp_minBody_of_zero :
    L.IsProp M (ictxQ Γ u)
      (.app (.bvar 2) (introAp (.bvar 4) (.bvar 3) (.bvar 1) (.bvar 0))) :=
  (isProp_iff hle (onCtxI_Q hu hΓ) (hasType_minBodyI Γ) hu).2 h0

include hu hle h0 in
/-- **`• ∈ ⟦Iff.rec's type⟧` at every `Prop` instantiation of the elimination universe.**  The
hypothesis is `IffSpec M` and nothing else — no model-side `propext`. -/
theorem pt_mem_interp_iffRecType_of_zero (hspec : IffSpec M) :
    (pt : V) ∈ (interp M L [] ((iffIndDecl.recType 0).instL [u])).toFun ∅ := by
  rw [iffRecType_instL]
  refine (mem_interp_forallE_prop_iff M L
    (isProp_recBB_of_zero (Γ := []) hu hle trivial h0)).2 ⟨rfl, fun a ha ↦ ?_⟩
  rw [interp_sort] at ha
  have ha' : a ∈ (UProp : V) := ha
  refine (mem_interp_forallE_prop_iff M L
    (isProp_recBM_of_zero (Γ := []) hu hle trivial h0)).2 ⟨rfl, fun b hb ↦ ?_⟩
  rw [interp_sort] at hb
  have hb' : b ∈ (UProp : V) := hb
  refine (mem_interp_forallE_prop_iff M L
    (isProp_recBN_of_zero (Γ := []) hu hle trivial h0)).2 ⟨rfl, fun f _ ↦ ?_⟩
  refine (mem_interp_forallE_prop_iff M L
    (isProp_recBH_of_zero (Γ := []) hu hle trivial h0)).2 ⟨rfl, fun m hm ↦ ?_⟩
  refine (mem_interp_forallE_prop_iff M L
    (isProp_resI_of_zero (Γ := []) hu hle trivial h0)).2 ⟨rfl, fun hh hhh ↦ ?_⟩
  rw [interp_majTyI_val hu hle, hspec a ha' b hb'] at hhh
  by_cases hab : a = b
  · rw [if_pos hab] at hhh
    obtain rfl : hh = (pt : V) := mem_singleton_iff.mp hhh
    rw [interp_resI_val hu hle]
    rw [show (minTyI : VExpr) = .forallE (.forallE (.bvar 2) (.bvar 2))
        (.forallE (.forallE (.bvar 2) (.bvar 4))
          (.app (.bvar 2) (introAp (.bvar 4) (.bvar 3) (.bvar 1) (.bvar 0)))) from rfl] at hm
    obtain ⟨rfl, hm2⟩ := (mem_interp_forallE_prop_iff M L
      (isProp_minInner_of_zero (Γ := []) hu hle trivial h0)).1 hm
    have h1 := hm2 (pt : V)
      (by rw [← impSet01_eq_interp_mpTy hu hle]; exact pt_mem_impSet01 ha' hab)
    obtain ⟨-, h2⟩ := (mem_interp_forallE_prop_iff M L
      (isProp_minBody_of_zero (Γ := []) hu hle trivial h0)).1 h1
    have h3 := h2 (pt : V)
      (by rw [← impSet10_eq_interp_mprTy hu hle]; exact pt_mem_impSet10 ha' hab)
    rwa [interp_minBody_val hu hle] at h3
  · rw [if_neg hab] at hhh
    exact absurd hhh not_mem_empty

end SliceZero

/-! ## 12. Anti-vacuity: the conclusion is not free

The form `RecGap.repair_discriminates` fixes: **one `L`, one `M`, one `u`, one `interp`** — a good
value is in the interpretation and a bad one is not, at the *same* instantiation.  Checking only
that the hypotheses are satisfiable would not catch a conclusion every set satisfies, and
`mkForallType`-membership is exactly the kind of statement that degenerates (over an *empty* domain
`mkForallType` is `{∅}`).

The bad value is `•`, excluded by `IffAudit.pt_not_mem_interp_iffRecType_of_ne` — and note that at
this block **the exclusion needs no parameter-space inhabitant** (`Iff`'s outermost binder is a
parameter over `Prop` and `∅ ∈ U κ 0` at every `κ`), so unlike `EqRecLarge` §7 there is no `hx`
here at all.  No `κ` is chosen and `Above` does not occur. -/

section Discriminate

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ} (L : PropSplit envF nv) (M : ModelData V)
variable {u : VLevel} (hu : u.WF nv) (hle : iffEnv ≤ envF)

include hu hle in
/-- **The cell discriminates.**  One environment, one `L`, one `M`, one `u`: `iffRecFn` is a
member of the interpretation and `•` is not.  So neither the type nor the interpretation is
degenerate at this instantiation, and `iffRecFn_mem_interp_iffRecType` is not an instance of
"everything is in there". -/
theorem iffRecCell_discriminates (hspec : IffSpec M) (hn : u.eval M.ls ≠ 0) :
    iffRecFn M.κ (u.eval M.ls) ∈
        (interp M L [] ((iffIndDecl.recType 0).instL [u])).toFun ∅ ∧
      (pt : V) ∉ (interp M L [] ((iffIndDecl.recType 0).instL [u])).toFun ∅ :=
  ⟨iffRecFn_mem_interp_iffRecType hu hle hspec hn,
    IffAudit.pt_not_mem_interp_iffRecType_of_ne L M hu hle hn⟩

include L M hu hle in
/-- …and the two values really are different sets, which is what makes the conjunction above
informative rather than a statement about one set under two names. -/
theorem iffRecFn_ne_pt (hspec : IffSpec M) (hn : u.eval M.ls ≠ 0) :
    iffRecFn M.κ (u.eval M.ls) ≠ (pt : V) := by
  intro h
  exact (iffRecCell_discriminates L M hu hle hspec hn).2
    (h ▸ (iffRecCell_discriminates L M hu hle hspec hn).1)

end Discriminate

/-! ## 13. Both slices in one value: the `consts` cell at `Iff.rec`

`OracleOK`'s `type` field quantifies over **all** `us` of length `iffIndDecl.recUvars = 1`, so the
cell is one statement covering both level slices, and `IffAudit.no_level_uniform_value` says no
level-uniform value can serve it.  `iffRecVal` is therefore an `if` on `u.eval ls = 0` — the same
shape `EqLargeAudit.eqRecVal` uses, with a **one**-element `match` rather than two. -/

section Oracle

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]

theorem iffRecVal_congr (κ : ℕ → V) (ls : List ℕ) {us us' : List VLevel}
    (hd : List.Forall₂ (· ≈ ·) us us') : iffRecVal (V := V) κ ls us = iffRecVal κ ls us' := by
  rcases hd with _ | ⟨h1, ht1⟩
  · rfl
  rcases ht1 with _ | ⟨h2, ht2⟩
  · rw [iffRecVal_single, iffRecVal_single, VLevel.equiv_def.mp h1 ls]
  · rfl

theorem eq_single_of_length_one {us : List VLevel} (h : us.length = 1) : ∃ u, us = [u] := by
  rcases us with _ | ⟨u, us⟩
  · simp at h
  rcases us with _ | ⟨v, us⟩
  · exact ⟨u, rfl⟩
  · simp at h

theorem iffIndDecl_recUvars : iffIndDecl.recUvars = 1 := rfl

variable {envF : VEnv} {nv : ℕ} (L : PropSplit envF nv) (κ : ℕ → V) (ls : List ℕ)

/-- **The `consts` cell at `Iff.rec`, both slices, in one `OracleOK`.**

The hypothesis is `IffSpec ⟨κ, ls, c⟩` — the *ambient* assignment `c` that `interp` reads must
denote `Iff` correctly, which `preludeWitness` supplies (`SetModel.preludeWitness_iff`); what it
does **not** supply is the `Iff.rec` entry itself, which is why the oracle `o` is a separate
parameter here, pinned by `ho`.

`Above` is discharged by `Above.pure` in both fields (`oracleOK_of`), so no chain hypothesis is
used and **no `κ` is chosen**. -/
theorem oracleOK_IffRec (hle : iffEnv ≤ envF) {c : Name → List VLevel → V}
    (hspec : IffSpec (⟨κ, ls, c⟩ : ModelData V))
    {o : Name → List VLevel → V} (ho : ∀ us, o ``Iff.rec us = iffRecVal κ ls us) :
    OracleOK L κ ls o c ``Iff.rec ⟨iffIndDecl.recUvars, iffIndDecl.recType 0⟩ :=
  oracleOK_of (L := L)
    (fun _ _ hd ↦ by rw [ho, ho]; exact iffRecVal_congr κ ls hd)
    (fun {us} hw hlen ↦ by
      obtain ⟨u, rfl⟩ := eq_single_of_length_one (iffIndDecl_recUvars ▸ hlen)
      rw [ho, iffRecVal_single]
      have hu : u.WF nv := hw u (by simp)
      by_cases h0 : u.eval ls = 0
      · rw [if_pos h0]
        exact pt_mem_interp_iffRecType_of_zero hu hle h0 hspec
      · rw [if_neg h0]
        exact iffRecFn_mem_interp_iffRecType hu hle hspec h0)

end Oracle

/-! ## 14. The **joint** repair: both arms at one witness

`PreludeRecGap` §3 could repair only the `Eq.rec` arm, because `iffRecFn` did not exist.  It now
does, so the shared witness can be repaired at **both** cells at once — and doing it in one step is
not a convenience: `RecGap.preludeWitness_not_mem_interp_iffRecType` still refutes
`preludeWitnessR`, so a witness repaired only at `Eq.rec` is refuted by exactly the theorem this
file makes non-vacuous.

`preludeWitnessRR` is still a **measuring instrument** and `PreludeSpec.lean` is still untouched:
the real edit is the relocation `PreludeRecGap`'s header describes, now over *eight* definitions
more (`impSet`, `minSet`, `motSetI`, `lamHI`, `lamNI`, `lamFI`, `lamBI`, `iffRecFn`, plus §2's
three definability lemmas and `mkForallProp_ext`).  Note also §20.4a's kernel trap: every
`preludeWitnessRR_cnst_*` below is `simp`, never `rfl`, precisely so the kernel is never asked to
whnf the `if`-cascade through the two new arms' bodies. -/

section JointRepair

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]

/-- **`preludeWitness` with level-branching `Eq.rec` *and* `Iff.rec` entries.**  Identical to
`RecGap.preludeWitnessR` except for the fifth arm. -/
noncomputable def preludeWitnessRR (κ : ℕ → V) (ls : List ℕ) : ModelData V where
  κ := κ
  ls := ls
  cnst := fun n us ↦
    if n = ``Eq then (match us with | [w] => eqFn κ (w.eval ls) | _ => ∅)
    else if n = ``Iff then (match us with | [] => (iffFn : V) | _ => ∅)
    else if n = ``Nonempty then (match us with | [w] => nonemptyFn κ (w.eval ls) | _ => ∅)
    else if n = ``Eq.rec then EqLargeAudit.eqRecVal κ ls us
    else if n = ``Iff.rec then iffRecVal κ ls us
    else ∅

theorem preludeWitnessRR_eq (κ : ℕ → V) (ls : List ℕ) (u : VLevel) :
    EqSpec (preludeWitnessRR κ ls) u := fun _ hα _ ha _ hb ↦ eqFn_value hα ha hb

theorem preludeWitnessRR_iff (κ : ℕ → V) (ls : List ℕ) :
    IffSpec (preludeWitnessRR κ ls) := fun _ hp _ hq ↦ iffFn_value hp hq

theorem preludeWitnessRR_nonempty (κ : ℕ → V) (ls : List ℕ) (u : VLevel) :
    NonemptySpec (preludeWitnessRR κ ls) u := fun _ hα ↦ nonemptyFn_value hα

/-- `preludeSpec_satisfiable`, verbatim, at the jointly repaired witness. -/
theorem preludeSpecRR_satisfiable (κ : ℕ → V) (ls : List ℕ) :
    ∃ M : ModelData V, M.κ = κ ∧ M.ls = ls ∧
      (∀ u, EqSpec M u) ∧ IffSpec M ∧ (∀ u, NonemptySpec M u) :=
  ⟨preludeWitnessRR κ ls, rfl, rfl, preludeWitnessRR_eq κ ls,
    preludeWitnessRR_iff κ ls, preludeWitnessRR_nonempty κ ls⟩

/-- Still `rfl`, as at `preludeWitnessR`: the `Eq` test is the first arm, so neither new arm
enters the reduction. -/
theorem preludeWitnessRR_cnst_eq (κ : ℕ → V) (ls : List ℕ) (w : VLevel) :
    (preludeWitnessRR (V := V) κ ls).cnst ``Eq [w] = eqFn κ (w.eval ls) := rfl

theorem preludeWitnessRR_cnst_eqRec (κ : ℕ → V) (ls : List ℕ) (us : List VLevel) :
    (preludeWitnessRR (V := V) κ ls).cnst ``Eq.rec us = EqLargeAudit.eqRecVal κ ls us := by
  simp [preludeWitnessRR]

theorem preludeWitnessRR_cnst_iffRec (κ : ℕ → V) (ls : List ℕ) (us : List VLevel) :
    (preludeWitnessRR (V := V) κ ls).cnst ``Iff.rec us = iffRecVal κ ls us := by
  simp [preludeWitnessRR]

theorem preludeWitnessRR_cnst_neRec (κ : ℕ → V) (ls : List ℕ) (us : List VLevel) :
    (preludeWitnessRR (V := V) κ ls).cnst ``Nonempty.rec us = (pt : V) := by
  simp [preludeWitnessRR, pt]

variable {envF : VEnv} {nv : ℕ} (L : PropSplit envF nv) (κ : ℕ → V) (ls : List ℕ)

/-- **`OracleOK` at `Iff.rec`, both level slices, at the jointly repaired witness** — no side
oracle parameter, no chain hypothesis, no chosen `κ`. -/
theorem oracleOK_IffRec_preludeWitnessRR (hle : iffEnv ≤ envF) :
    OracleOK L κ ls (preludeWitnessRR κ ls).cnst (preludeWitnessRR κ ls).cnst ``Iff.rec
      ⟨iffIndDecl.recUvars, iffIndDecl.recType 0⟩ :=
  oracleOK_IffRec L κ ls hle (preludeWitnessRR_iff κ ls) (preludeWitnessRR_cnst_iffRec κ ls)

/-- …and the `Eq.rec` cell is still discharged, so the joint repair loses nothing. -/
theorem oracleOK_EqRec_preludeWitnessRR (hle : eqEnv ≤ envF) :
    OracleOK L κ ls (preludeWitnessRR κ ls).cnst (preludeWitnessRR κ ls).cnst ``Eq.rec
      ⟨eqIndDecl.recUvars, eqIndDecl.recType 0⟩ :=
  EqLargeAudit.oracleOK_EqRec L κ ls hle
    (fun w ↦ preludeWitnessRR_eq κ ls w) (preludeWitnessRR_cnst_eqRec κ ls)

/-- **`Nonempty.rec` is unaffected**, exactly as `RecGap.preludeWitness_mem_interp_neRecType` says:
the fallback stays `•` there, which `NEAudit.oracleOK_NE_rec` depends on. -/
theorem preludeWitnessRR_mem_interp_neRecType {u : VLevel} (hu : u.WF nv)
    (hle : nonemptyEnv ≤ envF) :
    (preludeWitnessRR (V := V) κ ls).cnst ``Nonempty.rec [u] ∈
      (interp (preludeWitnessRR κ ls) L [] ((nonemptyIndDecl.recType 0).instL [u])).toFun ∅ := by
  rw [preludeWitnessRR_cnst_neRec]
  exact NEAudit.pt_mem_interp_NE_recType L κ ls hu hle

variable {u v : VLevel} (hu : u.WF nv) (hv : v.WF nv)

include hu hv in
/-- **The joint repair discriminates at BOTH cells, at one witness and one interpretation each.**
This is what "do not land a half" means concretely: the `Iff.rec` half is the one
`RecGap.preludeWitness_not_mem_interp_iffRecType` kills at `preludeWitnessR`. -/
theorem joint_repair_discriminates (hleE : eqEnv ≤ envF) (hleI : iffEnv ≤ envF)
    (hn : u.eval ls ≠ 0) {x : V} (hx : x ∈ U κ (v.eval ls)) :
    ((preludeWitnessRR (V := V) κ ls).cnst ``Eq.rec [u, v] ∈
        (interp (preludeWitnessRR κ ls) L [] ((eqIndDecl.recType 0).instL [u, v])).toFun ∅ ∧
      (preludeWitnessPt (V := V) κ ls).cnst ``Eq.rec [u, v] ∉
        (interp (preludeWitnessRR κ ls) L [] ((eqIndDecl.recType 0).instL [u, v])).toFun ∅) ∧
    ((preludeWitnessRR (V := V) κ ls).cnst ``Iff.rec [u] ∈
        (interp (preludeWitnessRR κ ls) L [] ((iffIndDecl.recType 0).instL [u])).toFun ∅ ∧
      (preludeWitnessPt (V := V) κ ls).cnst ``Iff.rec [u] ∉
        (interp (preludeWitnessRR κ ls) L [] ((iffIndDecl.recType 0).instL [u])).toFun ∅) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [preludeWitnessRR_cnst_eqRec, EqLargeAudit.eqRecVal_pair, if_neg hn]
    exact EqLargeAudit.eqRecFn_mem_interp_eqRecType hu hv hleE
      (preludeWitnessRR_eq κ ls v) hn
  · rw [preludeWitnessPt_cnst_eqRec]
    exact EqAudit.pt_not_mem_interp_eqRecType_of_ne L (preludeWitnessRR κ ls) hu hv hleE hn hx
  · rw [preludeWitnessRR_cnst_iffRec, iffRecVal_single, if_neg hn]
    exact iffRecFn_mem_interp_iffRecType hu hleI (preludeWitnessRR_iff κ ls) hn
  · rw [preludeWitnessPt_cnst_iffRec]
    exact IffAudit.pt_not_mem_interp_iffRecType_of_ne L (preludeWitnessRR κ ls) hu hleI hn

include L hu in
/-- …and the `Iff.rec` entry really changes: the two witnesses give different sets there. -/
theorem joint_repair_changes_the_iffRec_value (hleI : iffEnv ≤ envF) (hn : u.eval ls ≠ 0) :
    (preludeWitnessRR (V := V) κ ls).cnst ``Iff.rec [u]
      ≠ (preludeWitnessPt (V := V) κ ls).cnst ``Iff.rec [u] := by
  intro h
  rw [preludeWitnessRR_cnst_iffRec, iffRecVal_single, if_neg hn,
    preludeWitnessPt_cnst_iffRec] at h
  exact iffRecFn_ne_pt L (preludeWitnessRR κ ls) hu hleI (preludeWitnessRR_iff κ ls) hn h

end JointRepair

/-! ### 14.1 The kernel trap, **reproduced at five arms**

`PreludeRecGap` §20.4a (handoff §20.4a) records that `EqTFAudit.preludeWitness_congr_Eq`'s proof
does **not** transfer to `preludeWitnessR`: its last `rfl` — the degenerate branch, `us` of length
≥ 2, both sides `∅` — hits `(kernel) deterministic timeout`, after the declaration has *elaborated*
and `#print axioms` has reported it clean.

**Measured again here, at five arms**, and it is worse: the naive proof takes between two and eight
minutes of wall clock before the kernel rejects it (at four arms it was fast enough that the
previous stream saw the error immediately), and `#print axioms` on the rejected declaration reports
`does not depend on any axioms`.  So the trap scales with the number of `if` arms, which is the
number the relocation will keep adding.  The fix is `PreludeRecGap`'s: name the `Eq` arm once by
`simp` and never let `rfl` see the cascade. -/

section TypeFormerTransfer

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ} (L : PropSplit envF nv) (κ : ℕ → V) (ls : List ℕ)

theorem preludeWitnessRR_cnst_Eq_arm (us : List VLevel) :
    (preludeWitnessRR (V := V) κ ls).cnst ``Eq us
      = (match us with | [w] => eqFn κ (w.eval ls) | _ => (∅ : V)) := by
  simp [preludeWitnessRR]

/-- The repaired shape, at five arms.  The last branch is `rw`, not `rfl` — see §14.1. -/
theorem preludeWitnessRR_congr_Eq {us us' : List VLevel}
    (hd : List.Forall₂ (· ≈ ·) us us') :
    (preludeWitnessRR (V := V) κ ls).cnst ``Eq us
      = (preludeWitnessRR (V := V) κ ls).cnst ``Eq us' := by
  rcases hd with _ | ⟨h, ht⟩
  · rfl
  rcases ht with _ | ⟨h2, ht2⟩
  · rw [preludeWitnessRR_cnst_eq, preludeWitnessRR_cnst_eq, VLevel.equiv_def.mp h ls]
  · rw [preludeWitnessRR_cnst_Eq_arm, preludeWitnessRR_cnst_Eq_arm]

theorem mem_interp_EqType_preludeWitnessRR {v : VLevel} (hv : v.WF nv) (hle : eqEnv ≤ envF) :
    (preludeWitnessRR (V := V) κ ls).cnst ``Eq [v] ∈
      (interp (preludeWitnessRR κ ls) L [] (EqTFAudit.eqTypeFormerType v)).toFun ∅ := by
  rw [preludeWitnessRR_cnst_eq]
  exact EqTFAudit.eqFn_mem_interp_EqType hv hle

/-- **The `Eq` type-former cell survives the joint repair** — so `preludeWitnessRR` is not a
regression on `RecGap.preludeWitnessR` at any cell the latter discharged. -/
theorem oracleOK_Eq_preludeWitnessRR (hle : eqEnv ≤ envF) :
    OracleOK L κ ls (preludeWitnessRR κ ls).cnst (preludeWitnessRR κ ls).cnst ``Eq
      ⟨1, .forallE (.sort (.param 0))
        (.forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)))⟩ :=
  oracleOK_of (L := L)
    (fun _ _ hd ↦ preludeWitnessRR_congr_Eq κ ls hd)
    (fun {us} hw hlen ↦ by
      obtain ⟨w, rfl⟩ := NEAudit.eq_singleton_of_length_one hlen
      exact mem_interp_EqType_preludeWitnessRR L κ ls (hw w (List.mem_singleton.2 rfl)) hle)

end TypeFormerTransfer

/-! ## 15. The repair, **installed**: both cells at `SetModel.preludeWitness` itself

§14's `preludeWitnessRR` was a measuring instrument living downstream.  The relocation it priced has
been performed -- `motSet`/`lam*`/`eqRecFn`/`eqRecVal` and the `Iff` analogues now live in
`PreludeSpec.lean`, and `SetModel.preludeWitness` carries both recursor arms -- so the same
statements can now be made about the assignment `PreludeOracle.lean` really uses
(`NEAudit.neOracle` is `(preludeWitness κ ls).cnst` byte for byte, `NEAudit.neM_eq`).

Everything below is the same proof as its `preludeWitnessRR` counterpart with the witness swapped;
none of it needed the `_cnst_Eq_arm` + `rw` detour §14.1 prescribes, because `preludeWitness` is
written in the η-contracted shape (`docs/handoff-setmodel.md` §22.4) and its cells are `rfl`. -/

section Installed

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ} (L : PropSplit envF nv) (κ : ℕ → V) (ls : List ℕ)

/-- **`OracleOK` at `Iff.rec`, both level slices, at the shared witness.** -/
theorem oracleOK_IffRec_preludeWitness (hle : iffEnv ≤ envF) :
    OracleOK L κ ls (preludeWitness κ ls).cnst (preludeWitness κ ls).cnst ``Iff.rec
      ⟨iffIndDecl.recUvars, iffIndDecl.recType 0⟩ :=
  oracleOK_IffRec L κ ls hle (preludeWitness_iff κ ls) (preludeWitness_cnst_iffRec κ ls)

/-- **`OracleOK` at `Eq.rec`, both level slices, at the shared witness.** -/
theorem oracleOK_EqRec_preludeWitness (hle : eqEnv ≤ envF) :
    OracleOK L κ ls (preludeWitness κ ls).cnst (preludeWitness κ ls).cnst ``Eq.rec
      ⟨eqIndDecl.recUvars, eqIndDecl.recType 0⟩ :=
  EqLargeAudit.oracleOK_EqRec L κ ls hle
    (fun w ↦ preludeWitness_eq κ ls w) (preludeWitness_cnst_eqRec κ ls)

variable {u : VLevel} (hu : u.WF nv)

include hu in
/-- The `≠ 0` slice at `Iff.rec`, at the shared witness -- what
`RecGap.preludeWitnessPt_not_mem_interp_iffRecType` is the negation of at the pre-repair
assignment. -/
theorem preludeWitness_mem_interp_iffRecType (hle : iffEnv ≤ envF) (hn : u.eval ls ≠ 0) :
    (preludeWitness (V := V) κ ls).cnst ``Iff.rec [u] ∈
      (interp (preludeWitness κ ls) L [] ((iffIndDecl.recType 0).instL [u])).toFun ∅ := by
  rw [preludeWitness_cnst_iffRec, iffRecVal_single, if_neg hn]
  exact iffRecFn_mem_interp_iffRecType hu hle (preludeWitness_iff κ ls) hn

variable {v : VLevel} (hv : v.WF nv)

include hu hv in
/-- **The installed repair discriminates at BOTH cells**, at one `L`, one `κ`, one `ls`, one level
tuple and **one `interp`** -- the interpretation of the *repaired* witness in all four conjuncts, so
the two `∉` halves are not statements about a different model.  The bad witness is
`SetModel.preludeWitnessPt`, the pre-repair assignment, which meets all three prelude
specifications and agrees with `preludeWitness` at all three type formers, so the only difference
exercised here is the one the repair makes. -/
theorem installed_repair_discriminates (hleE : eqEnv ≤ envF) (hleI : iffEnv ≤ envF)
    (hn : u.eval ls ≠ 0) {x : V} (hx : x ∈ U κ (v.eval ls)) :
    ((preludeWitness (V := V) κ ls).cnst ``Eq.rec [u, v] ∈
        (interp (preludeWitness κ ls) L [] ((eqIndDecl.recType 0).instL [u, v])).toFun ∅ ∧
      (preludeWitnessPt (V := V) κ ls).cnst ``Eq.rec [u, v] ∉
        (interp (preludeWitness κ ls) L [] ((eqIndDecl.recType 0).instL [u, v])).toFun ∅) ∧
    ((preludeWitness (V := V) κ ls).cnst ``Iff.rec [u] ∈
        (interp (preludeWitness κ ls) L [] ((iffIndDecl.recType 0).instL [u])).toFun ∅ ∧
      (preludeWitnessPt (V := V) κ ls).cnst ``Iff.rec [u] ∉
        (interp (preludeWitness κ ls) L [] ((iffIndDecl.recType 0).instL [u])).toFun ∅) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [preludeWitness_cnst_eqRec, EqLargeAudit.eqRecVal_pair, if_neg hn]
    exact EqLargeAudit.eqRecFn_mem_interp_eqRecType hu hv hleE (preludeWitness_eq κ ls v) hn
  · rw [preludeWitnessPt_cnst_eqRec]
    exact EqAudit.pt_not_mem_interp_eqRecType_of_ne L (preludeWitness κ ls) hu hv hleE hn hx
  · rw [preludeWitness_cnst_iffRec, iffRecVal_single, if_neg hn]
    exact iffRecFn_mem_interp_iffRecType hu hleI (preludeWitness_iff κ ls) hn
  · rw [preludeWitnessPt_cnst_iffRec]
    exact IffAudit.pt_not_mem_interp_iffRecType_of_ne L (preludeWitness κ ls) hu hleI hn

include L hu in
/-- ...and the two assignments' `Iff.rec` entries really are different sets. -/
theorem installed_repair_changes_the_iffRec_value (hleI : iffEnv ≤ envF) (hn : u.eval ls ≠ 0) :
    (preludeWitness (V := V) κ ls).cnst ``Iff.rec [u]
      ≠ (preludeWitnessPt (V := V) κ ls).cnst ``Iff.rec [u] := by
  intro h
  rw [preludeWitness_cnst_iffRec, iffRecVal_single, if_neg hn,
    preludeWitnessPt_cnst_iffRec] at h
  exact iffRecFn_ne_pt L (preludeWitness κ ls) hu hleI (preludeWitness_iff κ ls) hn h

end Installed

/-! ## 16. Axiom audit, **by namespace**

Not by filename: this file declares into `Lean4Lean.SetModel.IffLargeAudit`, and the names it
reuses live in `Lean4Lean.SetModel` (`iffFn_value`, `preludeWitness`), `…IffAudit`, `…EqZeroAudit`,
`…EqLargeAudit` and `…RecGap`.  Every name below is `Lean4Lean.SetModel.IffLargeAudit.*`. -/

#print axioms Lean4Lean.SetModel.mkForallProp_ext
#print axioms Lean4Lean.SetModel.iffAt_definable
#print axioms Lean4Lean.SetModel.appPt_definable₂
#print axioms Lean4Lean.SetModel.minAppPt_definable₂
#print axioms Lean4Lean.SetModel.impSet_definable
#print axioms Lean4Lean.SetModel.minSet_definable
#print axioms Lean4Lean.SetModel.motSetI_definable
#print axioms Lean4Lean.SetModel.lamHI_definable
#print axioms Lean4Lean.SetModel.lamNI_definable
#print axioms Lean4Lean.SetModel.lamFI_definable
#print axioms Lean4Lean.SetModel.lamBI_definable
#print axioms Lean4Lean.SetModel.IffLargeAudit.onCtxI_M
#print axioms Lean4Lean.SetModel.IffLargeAudit.onCtxI_N
#print axioms Lean4Lean.SetModel.IffLargeAudit.onCtxI_H
#print axioms Lean4Lean.SetModel.IffLargeAudit.onCtxI_P
#print axioms Lean4Lean.SetModel.IffLargeAudit.onCtxI_Q
#print axioms Lean4Lean.SetModel.IffLargeAudit.onCtxI_Pa
#print axioms Lean4Lean.SetModel.IffLargeAudit.onCtxI_Qb
#print axioms Lean4Lean.SetModel.IffLargeAudit.onCtxI_I
#print axioms Lean4Lean.SetModel.IffLargeAudit.hasType_a_ctxH
#print axioms Lean4Lean.SetModel.IffLargeAudit.hasType_b_ctxH
#print axioms Lean4Lean.SetModel.IffLargeAudit.hasType_IffTy
#print axioms Lean4Lean.SetModel.IffLargeAudit.hasType_iffC1
#print axioms Lean4Lean.SetModel.IffLargeAudit.hasType_iffC1Ty
#print axioms Lean4Lean.SetModel.IffLargeAudit.hasType_introC3
#print axioms Lean4Lean.SetModel.IffLargeAudit.hasType_introC3Ty
#print axioms Lean4Lean.SetModel.IffLargeAudit.hasType_motTy_gen
#print axioms Lean4Lean.SetModel.IffLargeAudit.hasType_minInner
#print axioms Lean4Lean.SetModel.IffLargeAudit.not_isProp_recBB
#print axioms Lean4Lean.SetModel.IffLargeAudit.not_isProp_recBM
#print axioms Lean4Lean.SetModel.IffLargeAudit.not_isProp_recBN
#print axioms Lean4Lean.SetModel.IffLargeAudit.not_isProp_recBH
#print axioms Lean4Lean.SetModel.IffLargeAudit.not_isProp_resI
#print axioms Lean4Lean.SetModel.IffLargeAudit.not_isProp_minInner
#print axioms Lean4Lean.SetModel.IffLargeAudit.not_isProp_minBody
#print axioms Lean4Lean.SetModel.IffLargeAudit.not_isProp_sortuI
#print axioms Lean4Lean.SetModel.IffLargeAudit.isProp_mpCod
#print axioms Lean4Lean.SetModel.IffLargeAudit.isProp_mprCod
#print axioms Lean4Lean.SetModel.IffLargeAudit.not_isProof_iffC0
#print axioms Lean4Lean.SetModel.IffLargeAudit.not_isProof_iffC1
#print axioms Lean4Lean.SetModel.IffLargeAudit.not_isProof_mot_gen
#print axioms Lean4Lean.SetModel.IffLargeAudit.isProof_introC3
#print axioms Lean4Lean.SetModel.IffLargeAudit.interp_iffAp_bvars
#print axioms Lean4Lean.SetModel.IffLargeAudit.interp_iffAp_ctxB
#print axioms Lean4Lean.SetModel.IffLargeAudit.interp_majTyI_val
#print axioms Lean4Lean.SetModel.IffLargeAudit.interp_resI_val
#print axioms Lean4Lean.SetModel.IffLargeAudit.interp_minBody_val
#print axioms Lean4Lean.SetModel.IffLargeAudit.motSetI_eq_interp_motTyI
#print axioms Lean4Lean.SetModel.IffLargeAudit.impSet01_eq_interp_mpTy
#print axioms Lean4Lean.SetModel.IffLargeAudit.impSet10_eq_interp_mprTy
#print axioms Lean4Lean.SetModel.IffLargeAudit.minSet_eq_interp_minTyI
#print axioms Lean4Lean.SetModel.IffLargeAudit.pt_mem_impSet01
#print axioms Lean4Lean.SetModel.IffLargeAudit.pt_mem_impSet10
#print axioms Lean4Lean.SetModel.IffLargeAudit.iffRecFn_mem_interp_iffRecType
#print axioms Lean4Lean.SetModel.IffLargeAudit.isProp_recBB_of_zero
#print axioms Lean4Lean.SetModel.IffLargeAudit.isProp_recBM_of_zero
#print axioms Lean4Lean.SetModel.IffLargeAudit.isProp_recBN_of_zero
#print axioms Lean4Lean.SetModel.IffLargeAudit.isProp_recBH_of_zero
#print axioms Lean4Lean.SetModel.IffLargeAudit.isProp_resI_of_zero
#print axioms Lean4Lean.SetModel.IffLargeAudit.isProp_minInner_of_zero
#print axioms Lean4Lean.SetModel.IffLargeAudit.isProp_minBody_of_zero
#print axioms Lean4Lean.SetModel.IffLargeAudit.pt_mem_interp_iffRecType_of_zero
#print axioms Lean4Lean.SetModel.IffLargeAudit.iffRecCell_discriminates
#print axioms Lean4Lean.SetModel.IffLargeAudit.iffRecFn_ne_pt
#print axioms Lean4Lean.SetModel.iffRecVal_single
#print axioms Lean4Lean.SetModel.IffLargeAudit.iffRecVal_congr
#print axioms Lean4Lean.SetModel.IffLargeAudit.eq_single_of_length_one
#print axioms Lean4Lean.SetModel.IffLargeAudit.iffIndDecl_recUvars
#print axioms Lean4Lean.SetModel.IffLargeAudit.oracleOK_IffRec
#print axioms Lean4Lean.SetModel.IffLargeAudit.preludeWitnessRR_eq
#print axioms Lean4Lean.SetModel.IffLargeAudit.preludeWitnessRR_iff
#print axioms Lean4Lean.SetModel.IffLargeAudit.preludeWitnessRR_nonempty
#print axioms Lean4Lean.SetModel.IffLargeAudit.preludeSpecRR_satisfiable
#print axioms Lean4Lean.SetModel.IffLargeAudit.preludeWitnessRR_cnst_eq
#print axioms Lean4Lean.SetModel.IffLargeAudit.preludeWitnessRR_cnst_eqRec
#print axioms Lean4Lean.SetModel.IffLargeAudit.preludeWitnessRR_cnst_iffRec
#print axioms Lean4Lean.SetModel.IffLargeAudit.preludeWitnessRR_cnst_neRec
#print axioms Lean4Lean.SetModel.IffLargeAudit.oracleOK_IffRec_preludeWitnessRR
#print axioms Lean4Lean.SetModel.IffLargeAudit.oracleOK_EqRec_preludeWitnessRR
#print axioms Lean4Lean.SetModel.IffLargeAudit.preludeWitnessRR_mem_interp_neRecType
#print axioms Lean4Lean.SetModel.IffLargeAudit.joint_repair_discriminates
#print axioms Lean4Lean.SetModel.IffLargeAudit.joint_repair_changes_the_iffRec_value
#print axioms Lean4Lean.SetModel.IffLargeAudit.preludeWitnessRR_cnst_Eq_arm
#print axioms Lean4Lean.SetModel.IffLargeAudit.preludeWitnessRR_congr_Eq
#print axioms Lean4Lean.SetModel.IffLargeAudit.mem_interp_EqType_preludeWitnessRR
#print axioms Lean4Lean.SetModel.IffLargeAudit.oracleOK_Eq_preludeWitnessRR
#print axioms Lean4Lean.SetModel.IffLargeAudit.oracleOK_IffRec_preludeWitness
#print axioms Lean4Lean.SetModel.IffLargeAudit.oracleOK_EqRec_preludeWitness
#print axioms Lean4Lean.SetModel.IffLargeAudit.preludeWitness_mem_interp_iffRecType
#print axioms Lean4Lean.SetModel.IffLargeAudit.installed_repair_discriminates
#print axioms Lean4Lean.SetModel.IffLargeAudit.installed_repair_changes_the_iffRec_value
