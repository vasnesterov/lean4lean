import Lean4Lean.Theory.SetModel.IffRecLarge

/-!
# `iffIndDecl`'s other two `consts` cells: the type former and `Iff.intro`

`IffRecLarge.lean` §15 closes `InductOracleOK`'s `consts` cell at `Iff.rec`, both level slices, at
the shared `SetModel.preludeWitness`.  This file closes the remaining two, so the `consts` field at
this block is complete:

* **`Iff ↦ iffFn`** lands in `⟦Prop → Prop → Prop⟧`.  Two `mkLam` layers against two
  `mkForallType` layers, exactly as `EqTFAudit.eqFn_mem_interp_EqType` is three; and as there, the
  hypothesis is the *value's identity* (`preludeWitness_cnst_Iff`, `rfl`) and **not** `IffSpec` --
  `EqTFAudit.eqSpec_not_sufficient` is the control for why an applied-value spec cannot do it, and
  the argument transfers verbatim.
* **`Iff.intro ↦ •`**.  `Iff.intro`'s type is a proposition at *every* binder (`imax _ 0 = 0` four
  times), so the interpretation is a four-fold `mkForallProp` and the obligation is
  `• ∈ ⟦Iff a b⟧` under the two field binders.  That is **not** free: `⟦Iff a b⟧` is
  `{•}` only when `a = b`.  What makes it true is that `a = b` is *derivable from the two field
  binders' own inhabitation* -- if `a ≠ b` then one of `⟦a → b⟧`, `⟦b → a⟧` is empty and the
  corresponding `∀` is vacuous.  §3 is that argument, and it is the one place in this corner where
  a constructor cell needs its own fields rather than only its result type.

## Bounds

`Above` occurs in **no statement** in this file.  Everything is at an arbitrary `κ : ℕ → V`, an
arbitrary `ModelData`, and an arbitrary `L : PropSplit envF nv` with `hle : iffEnv ≤ envF`, which
`IffAudit.iffEnv_le_preludeEnv` discharges at `preludeEnv`.  No chain hypothesis, no chosen `κ`.
-/

namespace Lean4Lean.SetModel.IffConstsAudit

open Lean4Lean LO LO.FirstOrder LO.FirstOrder.SetTheory
open Lean4Lean.SetModel.IffAudit
open Lean4Lean.SetModel.EqZeroAudit (r2_0 r2_1 r3_1 r4_0 r4_1)
open scoped Classical

/-! ## 1. The two types, and the contexts `Iff.intro`'s fields need -/

section Shapes

/-- `Iff`'s type former, instantiated (`iffIndDecl.uvars = 0`, so `instL []` is the identity). -/
abbrev iffTypeFormerType : VExpr :=
  .forallE (.sort .zero) (.forallE (.sort .zero) (.sort .zero))

/-- `mp`'s type, `a → b`, over `[b, a]`. -/
abbrev mpTyC : VExpr := .forallE (.bvar 1) (.bvar 1)
/-- `mpr`'s type, `b → a`, over `[mp, b, a]`. -/
abbrev mprTyC : VExpr := .forallE (.bvar 1) (.bvar 3)

/-- `Iff.intro`'s type: `∀ (a b : Prop), (a → b) → (b → a) → Iff a b`. -/
abbrev iffIntroType : VExpr :=
  .forallE (.sort .zero) (.forallE (.sort .zero)
    (.forallE mpTyC (.forallE mprTyC (iffAp (.bvar 3) (.bvar 2)))))

theorem iffTypeFormerType_eq :
    (⟨0, .forallE (.sort .zero) (.forallE (.sort .zero) (.sort .zero))⟩ : VConstant).type.instL []
      = iffTypeFormerType := rfl

theorem iffIntroType_eq :
    (⟨0, .forallE (.sort .zero) (.forallE (.sort .zero)
      (.forallE (.forallE (.bvar 1) (.bvar 1))
        (.forallE (.forallE (.bvar 1) (.bvar 3))
          (.app (.app (.const ``Iff []) (.bvar 3)) (.bvar 2)))))⟩ : VConstant).type.instL []
      = iffIntroType := rfl

variable (Γ : List VExpr)

/-- `mp : a → b` bound. -/
abbrev ictxMp : List VExpr := mpTyC :: ictxB Γ
/-- `mpr : b → a` bound. -/
abbrev ictxMpr : List VExpr := mprTyC :: ictxMp Γ
/-- inside `mp`'s own arrow. -/
abbrev ictxMpD : List VExpr := (.bvar 1 : VExpr) :: ictxB Γ
/-- inside `mpr`'s own arrow. -/
abbrev ictxMprD : List VExpr := (.bvar 1 : VExpr) :: ictxMp Γ

end Shapes

/-! ## 2. Typing and propositionhood

Every sort below has `0` in codomain position, so every one of `Iff.intro`'s four binders is a
`mkForallProp` -- unlike `Iff.rec`, where the branch depends on the elimination universe. -/

section Typing

variable {nv : ℕ} (Γ : List VExpr)

theorem hasType_mpTyC : iffEnv.HasType nv (ictxB Γ) mpTyC (.sort (.imax .zero .zero)) :=
  .forallEDF (.bvar (.succ .zero)) (.bvar (.succ .zero))

theorem hasType_mprTyC : iffEnv.HasType nv (ictxMp Γ) mprTyC (.sort (.imax .zero .zero)) :=
  .forallEDF (.bvar (.succ .zero)) (.bvar (.succ (.succ (.succ .zero))))

theorem hasType_introBody :
    iffEnv.HasType nv (ictxMpr Γ) (iffAp (.bvar 3) (.bvar 2)) (.sort .zero) :=
  hasType_iffAp (.bvar (.succ (.succ (.succ .zero)))) (.bvar (.succ (.succ .zero)))

theorem hasType_introB3 :
    iffEnv.HasType nv (ictxMp Γ) (.forallE mprTyC (iffAp (.bvar 3) (.bvar 2)))
      (.sort (.imax (.imax .zero .zero) .zero)) :=
  .forallEDF (hasType_mprTyC Γ) (hasType_introBody Γ)

theorem hasType_introB2 :
    iffEnv.HasType nv (ictxB Γ) (.forallE mpTyC (.forallE mprTyC (iffAp (.bvar 3) (.bvar 2))))
      (.sort (.imax (.imax .zero .zero) (.imax (.imax .zero .zero) .zero))) :=
  .forallEDF (hasType_mpTyC Γ) (hasType_introB3 Γ)

theorem hasType_introB1 :
    iffEnv.HasType nv (ictxA Γ)
      (.forallE (.sort .zero)
        (.forallE mpTyC (.forallE mprTyC (iffAp (.bvar 3) (.bvar 2)))))
      (.sort (.imax (.succ .zero)
        (.imax (.imax .zero .zero) (.imax (.imax .zero .zero) .zero)))) :=
  .forallEDF (.sortDF trivial trivial rfl) (hasType_introB2 Γ)

theorem hasType_tfI2 :
    iffEnv.HasType nv (ictxA Γ) (.forallE (.sort .zero) (.sort .zero))
      (.sort (.imax (.succ .zero) (.succ .zero))) :=
  .forallEDF (.sortDF trivial trivial rfl) (.sortDF trivial trivial rfl)

/-! ### `OnCtx` at the four contexts `Iff.intro` introduces -/

variable {Γ} (hΓ : OnCtx Γ (iffEnv.IsType nv))

include hΓ in
theorem onCtxC_Mp : OnCtx (ictxMp Γ) (iffEnv.IsType nv) := ⟨onCtxI_B hΓ, _, hasType_mpTyC Γ⟩

include hΓ in
theorem onCtxC_Mpr : OnCtx (ictxMpr Γ) (iffEnv.IsType nv) :=
  ⟨onCtxC_Mp hΓ, _, hasType_mprTyC Γ⟩

include hΓ in
theorem onCtxC_MpD : OnCtx (ictxMpD Γ) (iffEnv.IsType nv) :=
  ⟨onCtxI_B hΓ, .zero, .bvar (.succ .zero)⟩

include hΓ in
theorem onCtxC_MprD : OnCtx (ictxMprD Γ) (iffEnv.IsType nv) :=
  ⟨onCtxC_Mp hΓ, .zero, .bvar (.succ .zero)⟩

end Typing

section Split

variable {V : Type*} [SetStructure V] [Nonempty V]
variable {envF : VEnv} {nv : ℕ} {L : PropSplit envF nv} {M : ModelData V}
variable (hle : iffEnv ≤ envF) {Γ : List VExpr} (hΓ : OnCtx Γ (iffEnv.IsType nv))

include hle hΓ in
theorem not_isProp_tfI2 : ¬ L.IsProp M (ictxA Γ) (.forallE (.sort .zero) (.sort .zero)) := by
  rw [isProp_iff hle (onCtxI_A hΓ) (hasType_tfI2 Γ) ⟨trivial, trivial⟩]
  simp [VLevel.eval, Lean.Nat.imax]

include hle hΓ in
theorem not_isProp_tfI3 : ¬ L.IsProp M (ictxB Γ) (.sort .zero) := by
  rw [isProp_iff hle (onCtxI_B hΓ) (VEnv.IsDefEq.sortDF trivial trivial rfl)
    (u := .succ .zero) trivial]
  simp [VLevel.eval]

include hle hΓ in
theorem isProp_introB1 :
    L.IsProp M (ictxA Γ)
      (.forallE (.sort .zero) (.forallE mpTyC (.forallE mprTyC (iffAp (.bvar 3) (.bvar 2))))) :=
  (isProp_iff hle (onCtxI_A hΓ) (hasType_introB1 Γ)
    ⟨trivial, ⟨trivial, trivial⟩, ⟨trivial, trivial⟩, trivial⟩).2
    (by simp [VLevel.eval, Lean.Nat.imax])

include hle hΓ in
theorem isProp_introB2 :
    L.IsProp M (ictxB Γ) (.forallE mpTyC (.forallE mprTyC (iffAp (.bvar 3) (.bvar 2)))) :=
  (isProp_iff hle (onCtxI_B hΓ) (hasType_introB2 Γ)
    ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩, trivial⟩).2
    (by simp [VLevel.eval, Lean.Nat.imax])

include hle hΓ in
theorem isProp_introB3 :
    L.IsProp M (ictxMp Γ) (.forallE mprTyC (iffAp (.bvar 3) (.bvar 2))) :=
  (isProp_iff hle (onCtxC_Mp hΓ) (hasType_introB3 Γ) ⟨⟨trivial, trivial⟩, trivial⟩).2
    (by simp [VLevel.eval, Lean.Nat.imax])

include hle hΓ in
theorem isProp_introBody : L.IsProp M (ictxMpr Γ) (iffAp (.bvar 3) (.bvar 2)) :=
  (isProp_iff hle (onCtxC_Mpr hΓ) (hasType_introBody Γ) trivial).2 rfl

include hle hΓ in
/-- **`mp`'s codomain is a proposition** — so `⟦a → b⟧` is the impredicative `mkForallProp`. -/
theorem isProp_mpCodC : L.IsProp M (ictxMpD Γ) (.bvar 1) :=
  (isProp_iff hle (onCtxC_MpD hΓ) (.bvar (.succ .zero)) trivial).2 rfl

include hle hΓ in
theorem isProp_mprCodC : L.IsProp M (ictxMprD Γ) (.bvar 3) :=
  (isProp_iff hle (onCtxC_MprD hΓ) (.bvar (.succ (.succ (.succ .zero)))) trivial).2 rfl

end Split

/-! ## 3. The two cells -/

section Cells

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ} {L : PropSplit envF nv} {M : ModelData V}
variable (hle : iffEnv ≤ envF)

include hle in
/-- **The type-former cell.**  `iffFn ∈ ⟦Prop → Prop → Prop⟧∅`.  Both `mkLam` layers of
`SetModel.iffFn` have domain `UProp`, and `⟦Prop⟧ = U κ 0 = UProp` (`U_zero`), so the two sides
meet with no arithmetic at all -- the `Eq` analogue needs `1 - 1 - 0 = 0` because its domains are
read off the valuation. -/
theorem iffFn_mem_interp_IffType :
    (iffFn : V) ∈ (interp M L ([] : List VExpr) iffTypeFormerType).toFun ∅ := by
  rw [show iffTypeFormerType = VExpr.forallE (.sort .zero) (.forallE (.sort .zero) (.sort .zero))
      from rfl,
    interp_forallE_type M L (not_isProp_tfI2 (Γ := ([] : List VExpr)) hle trivial)]
  unfold iffFn
  refine UnitAudit.mkLam_mem_mkForallType_of_dom ?_ (fun p hp ↦ ?_)
  · rw [interp_sort, show (VLevel.zero.eval M.ls) = 0 from rfl, U_zero]
  rw [interp_forallE_type M L (not_isProp_tfI3 (Γ := ([] : List VExpr)) hle trivial)]
  unfold iffFibQ
  refine UnitAudit.mkLam_mem_mkForallType_of_dom ?_ (fun q _ ↦ ?_)
  · rw [interp_sort, show (VLevel.zero.eval M.ls) = 0 from rfl, U_zero]
  rw [interp_sort, show (VLevel.zero.eval M.ls) = 0 from rfl, U_zero]
  by_cases h : (snoc (∅ : V) p) ‘ ((0 : ℕ) : V) = q
  · rw [if_pos h]; exact true_mem_UProp
  · rw [if_neg h]; exact empty_mem_UProp

include hle in
/-- `⟦Iff a b⟧` at `Iff.intro`'s innermost context. -/
theorem interp_iffAp_ctxMpr {p q x y : V} :
    (interp M L (ictxMpr ([] : List VExpr)) (iffAp (.bvar 3) (.bvar 2))).toFun
        (snoc (snoc (snoc (snoc (∅ : V) p) q) x) y)
      = (((M.cnst ``Iff []) ‘ p) ‘ q) := by
  rw [IffLargeAudit.interp_iffAp_bvars hle (onCtxC_Mpr (Γ := ([] : List VExpr)) trivial)
    (.bvar (.succ (.succ (.succ .zero)))) (.bvar (.succ (.succ .zero)))]
  simp only [List.length_cons, List.length_nil]
  rw [show (4 - 1 - 3 : ℕ) = 0 from rfl, show (4 - 1 - 2 : ℕ) = 1 from rfl, r4_0, r4_1]

include hle in
/-- **The two field binders force `a = b`.**  `⟦a → b⟧` and `⟦b → a⟧` are `mkForallProp`s over
truth values; each being inhabited is an implication between them, and `UProp` has two elements, so
inhabitation of both is `a = b`.  This is what makes `Iff.intro`'s cell true rather than vacuous. -/
theorem eq_of_mem_mpTy_mprTy {p q x y : V} (hp : p ∈ (UProp : V)) (hq : q ∈ (UProp : V))
    (hx : x ∈ (interp M L (ictxB ([] : List VExpr)) mpTyC).toFun (snoc (snoc (∅ : V) p) q))
    (hy : y ∈ (interp M L (ictxMp ([] : List VExpr)) mprTyC).toFun
      (snoc (snoc (snoc (∅ : V) p) q) x)) : p = q := by
  obtain ⟨-, hxf⟩ :=
    (mem_interp_forallE_prop_iff M L (isProp_mpCodC (Γ := ([] : List VExpr)) hle trivial)).1 hx
  obtain ⟨-, hyf⟩ :=
    (mem_interp_forallE_prop_iff M L (isProp_mprCodC (Γ := ([] : List VExpr)) hle trivial)).1 hy
  have hxf' : ∀ w ∈ p, x ∈ q := by
    intro w hw
    have h1 := hxf w (by rw [interp_bvar]; simpa only [List.length_cons, List.length_nil] using
      (by rw [show (2 - 1 - 1 : ℕ) = 0 from rfl, r2_0]; exact hw :
        w ∈ (snoc (snoc (∅ : V) p) q) ‘ (((2 - 1 - 1 : ℕ) : ℕ) : V)))
    rw [interp_bvar] at h1
    simp only [List.length_cons, List.length_nil] at h1
    rwa [show (3 - 1 - 1 : ℕ) = 1 from rfl, r3_1] at h1
  have hyf' : ∀ w ∈ q, y ∈ p := by
    intro w hw
    have h1 := hyf w (by rw [interp_bvar]; simpa only [List.length_cons, List.length_nil] using
      (by rw [show (3 - 1 - 1 : ℕ) = 1 from rfl, r3_1]; exact hw :
        w ∈ (snoc (snoc (snoc (∅ : V) p) q) x) ‘ (((3 - 1 - 1 : ℕ) : ℕ) : V)))
    rw [interp_bvar] at h1
    simp only [List.length_cons, List.length_nil] at h1
    rwa [show (4 - 1 - 3 : ℕ) = 0 from rfl, r4_0] at h1
  rcases eq_empty_or_eq_true_of_mem_UProp hp with rfl | rfl
  · rcases eq_empty_or_eq_true_of_mem_UProp hq with rfl | rfl
    · rfl
    · exact absurd (hyf' pt (mem_singleton_iff.2 rfl)) not_mem_empty
  · rcases eq_empty_or_eq_true_of_mem_UProp hq with rfl | rfl
    · exact absurd (hxf' pt (mem_singleton_iff.2 rfl)) not_mem_empty
    · rfl

include hle in
/-- **The `Iff.intro` cell.**  `• ∈ ⟦∀ (a b : Prop), (a → b) → (b → a) → Iff a b⟧∅`. -/
theorem pt_mem_interp_IffIntroType (hspec : IffSpec M) :
    (pt : V) ∈ (interp M L ([] : List VExpr) iffIntroType).toFun ∅ := by
  refine (mem_interp_forallE_prop_iff M L
    (isProp_introB1 (Γ := ([] : List VExpr)) hle trivial)).2 ⟨rfl, fun p hp ↦ ?_⟩
  rw [interp_sort, show (VLevel.zero.eval M.ls) = 0 from rfl, U_zero] at hp
  refine (mem_interp_forallE_prop_iff M L
    (isProp_introB2 (Γ := ([] : List VExpr)) hle trivial)).2 ⟨rfl, fun q hq ↦ ?_⟩
  rw [interp_sort, show (VLevel.zero.eval M.ls) = 0 from rfl, U_zero] at hq
  refine (mem_interp_forallE_prop_iff M L
    (isProp_introB3 (Γ := ([] : List VExpr)) hle trivial)).2 ⟨rfl, fun x hx ↦ ?_⟩
  refine (mem_interp_forallE_prop_iff M L
    (isProp_introBody (Γ := ([] : List VExpr)) hle trivial)).2 ⟨rfl, fun y hy ↦ ?_⟩
  rw [interp_iffAp_ctxMpr hle, hspec p hp q hq,
    if_pos (eq_of_mem_mpTy_mprTy hle hp hq hx hy)]
  exact mem_singleton_iff.2 rfl

end Cells


/-! ## 4. At the shared witness, and the `consts` field of `InductOracleOK` at `iffIndDecl`

`preludeWitness`'s `Iff` entry **is** `iffFn` (`preludeWitness_cnst_Iff`, `rfl`) and its `Iff.intro`
entry falls through to `∅`, which is `pt` (`SetModel.pt` is `∅` by definition).  With
`IffLargeAudit.oracleOK_IffRec_preludeWitness` this completes `consts` at the block. -/

section Witness

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ} (L : PropSplit envF nv) (κ : ℕ → V) (ls : List ℕ)

/-- The block's three constants **with their types**; `rfl`, so a measurement of `iffIndDecl`. -/
theorem iff_allConsts' : iffIndDecl.allConsts =
    [(``Iff, ⟨0, iffTypeFormerType⟩),
     (``Iff.intro, ⟨0, iffIntroType⟩),
     (``Iff.rec, ⟨iffIndDecl.recUvars, iffIndDecl.recType 0⟩)] := rfl

theorem preludeWitness_congr_Iff {us us' : List VLevel}
    (hd : List.Forall₂ (· ≈ ·) us us') :
    (preludeWitness (V := V) κ ls).cnst ``Iff us
      = (preludeWitness (V := V) κ ls).cnst ``Iff us' := by
  rcases hd with _ | ⟨h, ht⟩
  · rfl
  · rfl

theorem preludeWitness_cnst_iffIntro (us : List VLevel) :
    (preludeWitness (V := V) κ ls).cnst ``Iff.intro us = (pt : V) := by
  simp [preludeWitness, pt]

/-- **`OracleOK` at the name `Iff`.** -/
theorem oracleOK_Iff (hle : iffEnv ≤ envF) :
    OracleOK L κ ls (preludeWitness κ ls).cnst (preludeWitness κ ls).cnst ``Iff
      ⟨0, iffTypeFormerType⟩ :=
  oracleOK_of (L := L)
    (fun _ _ hd ↦ preludeWitness_congr_Iff κ ls hd)
    (fun {us} _ hlen ↦ by
      obtain rfl : us = [] := List.eq_nil_of_length_eq_zero hlen
      rw [show (preludeWitness (V := V) κ ls).cnst ``Iff [] = (iffFn : V) from rfl]
      exact iffFn_mem_interp_IffType hle)

/-- **`OracleOK` at the name `Iff.intro`.** -/
theorem oracleOK_IffIntro (hle : iffEnv ≤ envF) :
    OracleOK L κ ls (preludeWitness κ ls).cnst (preludeWitness κ ls).cnst ``Iff.intro
      ⟨0, iffIntroType⟩ :=
  oracleOK_of (L := L)
    (fun _ _ _ ↦ by rw [preludeWitness_cnst_iffIntro, preludeWitness_cnst_iffIntro])
    (fun {us} _ hlen ↦ by
      obtain rfl : us = [] := List.eq_nil_of_length_eq_zero hlen
      rw [preludeWitness_cnst_iffIntro]
      exact pt_mem_interp_IffIntroType hle (preludeWitness_iff κ ls))

/-- **The `consts` field of `InductOracleOK` at `iffIndDecl`**, all three cells. -/
theorem inductOracleOK_consts_Iff (hle : iffEnv ≤ envF) :
    ∀ p ∈ iffIndDecl.allConsts,
      OracleOK L κ ls (preludeWitness κ ls).cnst (preludeWitness κ ls).cnst p.1 p.2 := by
  intro p hp
  rw [iff_allConsts'] at hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  obtain rfl | rfl | rfl := hp
  · exact oracleOK_Iff L κ ls hle
  · exact oracleOK_IffIntro L κ ls hle
  · exact IffLargeAudit.oracleOK_IffRec_preludeWitness L κ ls hle

end Witness

/-! ## 5. Axiom audit, **by namespace**

This file declares into `Lean4Lean.SetModel.IffConstsAudit`; the names it reuses live in
`Lean4Lean.SetModel` (`iffFn`, `preludeWitness`, `UProp`), `…IffAudit`, `…IffLargeAudit`,
`…EqZeroAudit` and `…UnitAudit`. -/

#print axioms Lean4Lean.SetModel.IffConstsAudit.iffTypeFormerType_eq
#print axioms Lean4Lean.SetModel.IffConstsAudit.iffIntroType_eq
#print axioms Lean4Lean.SetModel.IffConstsAudit.hasType_mpTyC
#print axioms Lean4Lean.SetModel.IffConstsAudit.hasType_mprTyC
#print axioms Lean4Lean.SetModel.IffConstsAudit.hasType_introBody
#print axioms Lean4Lean.SetModel.IffConstsAudit.hasType_introB1
#print axioms Lean4Lean.SetModel.IffConstsAudit.hasType_tfI2
#print axioms Lean4Lean.SetModel.IffConstsAudit.onCtxC_Mpr
#print axioms Lean4Lean.SetModel.IffConstsAudit.not_isProp_tfI2
#print axioms Lean4Lean.SetModel.IffConstsAudit.not_isProp_tfI3
#print axioms Lean4Lean.SetModel.IffConstsAudit.isProp_introB1
#print axioms Lean4Lean.SetModel.IffConstsAudit.isProp_introBody
#print axioms Lean4Lean.SetModel.IffConstsAudit.isProp_mpCodC
#print axioms Lean4Lean.SetModel.IffConstsAudit.isProp_mprCodC
#print axioms Lean4Lean.SetModel.IffConstsAudit.iffFn_mem_interp_IffType
#print axioms Lean4Lean.SetModel.IffConstsAudit.interp_iffAp_ctxMpr
#print axioms Lean4Lean.SetModel.IffConstsAudit.eq_of_mem_mpTy_mprTy
#print axioms Lean4Lean.SetModel.IffConstsAudit.pt_mem_interp_IffIntroType
#print axioms Lean4Lean.SetModel.IffConstsAudit.iff_allConsts'
#print axioms Lean4Lean.SetModel.IffConstsAudit.preludeWitness_congr_Iff
#print axioms Lean4Lean.SetModel.IffConstsAudit.preludeWitness_cnst_iffIntro
#print axioms Lean4Lean.SetModel.IffConstsAudit.oracleOK_Iff
#print axioms Lean4Lean.SetModel.IffConstsAudit.oracleOK_IffIntro
#print axioms Lean4Lean.SetModel.IffConstsAudit.inductOracleOK_consts_Iff

end Lean4Lean.SetModel.IffConstsAudit
