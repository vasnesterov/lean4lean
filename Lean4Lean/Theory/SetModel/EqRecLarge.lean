import Lean4Lean.Theory.SetModel.EqRecNecessity

/-!
# `eqIndDecl`'s `≠ 0` slice: the six-layer `mkLam` at `Eq.rec`

Work in progress — see §5 for the status table.
-/

namespace Lean4Lean.SetModel.EqLargeAudit

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open Lean4Lean.SetModel.EqAudit
open Lean4Lean.SetModel.EqZeroAudit
open scoped Classical

/-! ## 1. Two missing combinators

`UnitAudit.mkLam_ext` says a `mkLam` is determined by its domain *set* and its body's values.
The `≠ 0` slice needs the same for `mkForallType`, because the motive binder's domain has to be
*written down* by the oracle (it cannot call `interp`) and then matched against `interp`'s. -/

section Combinators

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem mkFamUnion_ext {G G' : V → V} {hG : ℒₛₑₜ-function₁[V] G} {hG' : ℒₛₑₜ-function₁[V] G'}
    {F F' : V → V → V} {hF : ℒₛₑₜ-function₂[V] F} {hF' : ℒₛₑₜ-function₂[V] F'}
    {ρ ρ' : V} (hdom : G' ρ' = G ρ) (h : ∀ v ∈ G ρ, F' ρ' v = F ρ v) :
    mkFamUnion G' hG' F' hF' ρ' = mkFamUnion G hG F hF ρ := by
  rw [mem_ext_iff]
  intro y
  rw [mem_mkFamUnion_iff, mem_mkFamUnion_iff, hdom]
  exact exists_congr fun v ↦ and_congr_right fun hv ↦ by rw [h v hv]

/-- **`mkForallType` is determined by its domain set and its fibres on it.**  The analogue of
`UnitAudit.mkLam_ext`, and the lemma that lets the oracle's own spelling of the motive's type
be identified with `interp`'s. -/
theorem mkForallType_ext {G G' : V → V} {hG : ℒₛₑₜ-function₁[V] G} {hG' : ℒₛₑₜ-function₁[V] G'}
    {F F' : V → V → V} {hF : ℒₛₑₜ-function₂[V] F} {hF' : ℒₛₑₜ-function₂[V] F'}
    {ρ ρ' : V} (hdom : G' ρ' = G ρ) (h : ∀ v ∈ G ρ, F' ρ' v = F ρ v) :
    mkForallType G' hG' F' hF' ρ' = mkForallType G hG F hF ρ := by
  have hFU : mkFamUnion G' hG' F' hF' ρ' = mkFamUnion G hG F hF ρ :=
    mkFamUnion_ext (hG := hG) (hG' := hG') (hF := hF) (hF' := hF') hdom h
  rw [mem_ext_iff]
  intro f
  rw [mem_mkForallType_iff, mem_mkForallType_iff, hFU, hdom]
  refine and_congr_right fun _ ↦ forall_congr' fun v ↦ imp_congr_right fun hv ↦ ?_
  rw [h v hv]

end Combinators

/-! ## 2. Definability of the four domain shapes the value needs -/

section Definable

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- `ρ ↦ E ‘ (ρ ‘ i) ‘ (ρ ‘ j) ‘ (ρ ‘ k)` — the shape of `⟦Eq α a b⟧` read out of a valuation. -/
theorem eqAt_definable (E : V) (i j k : ℕ) :
    ℒₛₑₜ-function₁[V]
      (fun ρ ↦ ((E ‘ (ρ ‘ ((i : ℕ) : V))) ‘ (ρ ‘ ((j : ℕ) : V))) ‘ (ρ ‘ ((k : ℕ) : V))) := by
  definability

theorem eqAt_definable₂ (E : V) (i j k : ℕ) :
    ℒₛₑₜ-function₂[V]
      (fun (ρ _ : V) ↦
        ((E ‘ (ρ ‘ ((i : ℕ) : V))) ‘ (ρ ‘ ((j : ℕ) : V))) ‘ (ρ ‘ ((k : ℕ) : V))) := by
  definability

/-- `ρ ↦ (ρ ‘ i) ‘ (ρ ‘ j) ‘ •` — the shape of `⟦motive a (Eq.refl α a)⟧`. -/
theorem minAt_definable (i j : ℕ) :
    ℒₛₑₜ-function₁[V]
      (fun ρ ↦ ((ρ ‘ ((i : ℕ) : V)) ‘ (ρ ‘ ((j : ℕ) : V))) ‘ (pt : V)) := by
  definability

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem const_definable₂ (X : V) : ℒₛₑₜ-function₂[V] (fun (_ _ : V) ↦ X) := by definability

end Definable

/-! ## 3. The value: `λ α a motive m b h, m`

Six `mkLam` layers, written in the **environment-passing** style `Definability.lean` prescribes:
each layer's domain is read out of the valuation rather than captured, so the nest composes and
the definability proofs are one `definability` call each.

The indices are the ones `EqZeroAudit`'s `r`-ladder reads: at the innermost valuation
`snoc⁶ ∅ α a f m b h` the six values sit at `0,1,2,3,4,5`.  The body is `ρ ‘ 3`, the **minor
premise** — that is the whole computational content of `Eq.rec` in the model, and it is the same
content as `UnitAudit.recFn3`'s body, one index further in. -/

section Value

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]

/-- The `motive` binder's domain, spelled **without** `interp`: `Π x ∈ α, Π w ∈ ⟦Eq α a x⟧, U κ nu`.
Read at `snoc (snoc ∅ α) a`. -/
noncomputable def motSet (κ : ℕ → V) (nu nv : ℕ) : V → V :=
  mkForallType (fun ρ ↦ ρ ‘ ((0 : ℕ) : V)) (value_definable _)
    (fun ρ x ↦
      mkForallType
        (fun σ ↦ (((eqFn κ nv) ‘ (σ ‘ ((0 : ℕ) : V))) ‘ (σ ‘ ((1 : ℕ) : V))) ‘ (σ ‘ ((2 : ℕ) : V)))
        (eqAt_definable _ 0 1 2) (fun _ _ ↦ U κ nu) (const_definable₂ _) (snoc ρ x))
    (by
      have := mkForallType_definable
        (V := V)
        (fun σ ↦ (((eqFn κ nv) ‘ (σ ‘ ((0 : ℕ) : V))) ‘ (σ ‘ ((1 : ℕ) : V))) ‘ (σ ‘ ((2 : ℕ) : V)))
        (eqAt_definable _ 0 1 2) (fun _ _ ↦ U κ nu) (const_definable₂ _)
      definability)

theorem motSet_definable (κ : ℕ → V) (nu nv : ℕ) : ℒₛₑₜ-function₁[V] (motSet κ nu nv) :=
  mkForallType_definable _ _ _ _

/-- Layer 6: `λ (h : Eq α a b), m`. -/
noncomputable def lamH (κ : ℕ → V) (nv : ℕ) : V → V :=
  mkLam
    (fun ρ ↦ (((eqFn κ nv) ‘ (ρ ‘ ((0 : ℕ) : V))) ‘ (ρ ‘ ((1 : ℕ) : V))) ‘ (ρ ‘ ((4 : ℕ) : V)))
    (eqAt_definable _ 0 1 4) (fun ρ _ ↦ ρ ‘ ((3 : ℕ) : V)) (value_definable₂ _)

theorem lamH_definable (κ : ℕ → V) (nv : ℕ) : ℒₛₑₜ-function₁[V] (lamH κ nv) :=
  mkLam_definable _ _ _ _

/-- Layer 5: `λ (b : α), λ (h : Eq α a b), m`. -/
noncomputable def lamB (κ : ℕ → V) (nv : ℕ) : V → V :=
  mkLam (fun ρ ↦ ρ ‘ ((0 : ℕ) : V)) (value_definable _) (fun ρ b ↦ lamH κ nv (snoc ρ b))
    (by have := lamH_definable (V := V) κ nv; definability)

theorem lamB_definable (κ : ℕ → V) (nv : ℕ) : ℒₛₑₜ-function₁[V] (lamB κ nv) :=
  mkLam_definable _ _ _ _

/-- Layer 4: `λ (m : motive a (Eq.refl α a)), …`.  Its domain is `(f ‘ a) ‘ •`, which is what
`EqZeroAudit.interp_minTyE_val` computes the minor premise's type to be. -/
noncomputable def lamM (κ : ℕ → V) (nv : ℕ) : V → V :=
  mkLam (fun ρ ↦ ((ρ ‘ ((2 : ℕ) : V)) ‘ (ρ ‘ ((1 : ℕ) : V))) ‘ (pt : V)) (minAt_definable 2 1)
    (fun ρ m ↦ lamB κ nv (snoc ρ m)) (by have := lamB_definable (V := V) κ nv; definability)

theorem lamM_definable (κ : ℕ → V) (nv : ℕ) : ℒₛₑₜ-function₁[V] (lamM κ nv) :=
  mkLam_definable _ _ _ _

/-- Layer 3: `λ (motive : ∀ x : α, Eq α a x → Sort u), …`. -/
noncomputable def lamF (κ : ℕ → V) (nu nv : ℕ) : V → V :=
  mkLam (motSet κ nu nv) (motSet_definable κ nu nv) (fun ρ f ↦ lamM κ nv (snoc ρ f))
    (by have := lamM_definable (V := V) κ nv; definability)

theorem lamF_definable (κ : ℕ → V) (nu nv : ℕ) : ℒₛₑₜ-function₁[V] (lamF κ nu nv) :=
  mkLam_definable _ _ _ _

/-- Layer 2: `λ (a : α), …`. -/
noncomputable def lamA (κ : ℕ → V) (nu nv : ℕ) : V → V :=
  mkLam (fun ρ ↦ ρ ‘ ((0 : ℕ) : V)) (value_definable _) (fun ρ a ↦ lamF κ nu nv (snoc ρ a))
    (by have := lamF_definable (V := V) κ nu nv; definability)

theorem lamA_definable (κ : ℕ → V) (nu nv : ℕ) : ℒₛₑₜ-function₁[V] (lamA κ nu nv) :=
  mkLam_definable _ _ _ _

/-- **The value the oracle must hand `Eq.rec` once the elimination universe is not `Prop`.**
`nu` is `u.eval ls`, `nv` is `v.eval ls`. -/
noncomputable def eqRecFn (κ : ℕ → V) (nu nv : ℕ) : V :=
  mkLam (fun _ ↦ U κ nv) (by definability) (fun ρ α ↦ lamA κ nu nv (snoc ρ α))
    (by have := lamA_definable (V := V) κ nu nv; definability) ∅

end Value

/-! ## 4. Non-propositionhood of all six bodies, at `u.eval M.ls ≠ 0`

The mirror of `EqZeroAudit`'s §3.  Every one of the six `∀`-sorts is `0` **exactly** when `u` is
(`EqAudit.sort*_eval_eq_zero_iff`), so at `hn` every binder takes the `mkForallType` branch and the
value must be a genuine six-layer function.  The level split is therefore not a choice about how to
write the oracle: it is forced twice over, once per branch. -/

section NotIsProp

variable {V : Type*} [SetStructure V] [Nonempty V]
variable {envF : VEnv} {nv : ℕ} {L : PropSplit envF nv} {M : ModelData V}
variable {u v : VLevel} (hu : u.WF nv) (hv : v.WF nv) (hle : eqEnv ≤ envF)
variable {Γ : List VExpr} (hΓ : OnCtx Γ (eqEnv.IsType nv)) (hn : u.eval M.ls ≠ 0)

include hu hv hle hΓ hn in
theorem not_isProp_recBA : ¬ L.IsProp M (ectxA Γ v) (recBA u v) := fun h ↦
  hn (sortAE_eval_eq_zero_iff.1
    ((isProp_iff hle (onCtx_A hv hΓ) (hasType_recBA hu hv Γ) (sortAE_wf hu hv)).1 h))

include hu hv hle hΓ hn in
theorem not_isProp_recBM : ¬ L.IsProp M (ectxP Γ v) (recBM u v) := fun h ↦
  hn (sortME_eval_eq_zero_iff.1
    ((isProp_iff hle (onCtx_P hv hΓ) (hasType_recBM hu hv Γ) (sortME_wf hu hv)).1 h))

include hu hv hle hΓ hn in
theorem not_isProp_recBN : ¬ L.IsProp M (ectxM Γ u v) (recBN v) := fun h ↦
  hn (sortNE_eval_eq_zero_iff.1
    ((isProp_iff hle (onCtx_M hu hv hΓ) (hasType_recBN hv Γ) (sortNE_wf hu hv)).1 h))

include hu hv hle hΓ hn in
theorem not_isProp_recBB : ¬ L.IsProp M (ectxN Γ u v) (recBB v) := fun h ↦
  hn (sortBE_eval_eq_zero_iff.1
    ((isProp_iff hle (onCtx_N hu hv hΓ) (hasType_recBB hv Γ) (sortBE_wf hu hv)).1 h))

include hu hv hle hΓ hn in
theorem not_isProp_recBH : ¬ L.IsProp M (ectxB Γ u v) (recBH v) := fun h ↦
  hn (sortHE_eval_eq_zero_iff.1
    ((isProp_iff hle (onCtx_B hu hv hΓ) (hasType_recBH hv Γ) (sortHE_wf hu)).1 h))

include hu hv hle hΓ hn in
/-- The innermost body `motive b h` has sort `u` itself. -/
theorem not_isProp_resE :
    ¬ L.IsProp M (ectxH Γ u v) (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0)) := fun h ↦
  hn ((isProp_iff hle (onCtx_H hu hv hΓ) (hasType_resE Γ) hu).1 h)

end NotIsProp

/-! ## 5. The three domains `EqZeroAudit` does not already compute

`EqZeroAudit.interp_minTyE_val`, `interp_majTyE_val` and `interp_resE_val` are level-agnostic (no
`h0`), so three of the six layers' domains and the body are already in the tree.  What is missing
is `α` read twice (at `ectxA` and at `ectxN`) and — the substantive one — the **motive binder's**
domain, which the oracle has to spell out for itself. -/

section Domains

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ} {L : PropSplit envF nv} {M : ModelData V}
variable {u v : VLevel} (hu : u.WF nv) (hv : v.WF nv) (hle : eqEnv ≤ envF)

/-- `⟦α⟧` at the outermost binder's context. -/
theorem interp_alTy_ctxA (α : V) :
    (interp M L (ectxA ([] : List VExpr) v) (.bvar 0)).toFun (snoc (∅ : V) α)
      = (snoc (∅ : V) α) ‘ ((0 : ℕ) : V) := by
  rw [interp_bvar]
  simp only [List.length_cons, List.length_nil]

/-- `⟦α⟧` at the index binder's context — index `3` in a context of length `4`. -/
theorem interp_alTy_ctxN (α a f m : V) :
    (interp M L (ectxN ([] : List VExpr) u v) (.bvar 3)).toFun
        (snoc (snoc (snoc (snoc (∅ : V) α) a) f) m)
      = (snoc (snoc (snoc (snoc (∅ : V) α) a) f) m) ‘ ((0 : ℕ) : V) := by
  rw [interp_bvar]
  simp only [List.length_cons, List.length_nil]

/-- `ρ4 ‘ 3 = m` — the read `EqZeroAudit`'s ladder skips, because the `= 0` slice never needs the
minor premise's *position*, only its type. -/
theorem r4_3 {α a f m : V} :
    (snoc (snoc (snoc (snoc (∅ : V) α) a) f) m) ‘ ((3 : ℕ) : V) = m := s3.read_top

theorem r5_3 {α a f m b : V} :
    (snoc (snoc (snoc (snoc (snoc (∅ : V) α) a) f) m) b) ‘ ((3 : ℕ) : V) = m :=
  read_peel (j := 3) s4 (by omega) r4_3

theorem r6_3 {α a f m b h : V} :
    (snoc (snoc (snoc (snoc (snoc (snoc (∅ : V) α) a) f) m) b) h) ‘ ((3 : ℕ) : V) = m :=
  read_peel (j := 3) s5 (by omega) r5_3

include hu hv hle in
/-- **The motive binder's domain, as the oracle spells it.**  `motSet` is two `mkForallType`
layers written without `interp`; `⟦motive's type⟧` is two written by `interp`.  They agree because
their domains and fibres agree pointwise (`mkForallType_ext`), and the only step with content is
the inner domain, where `EqSpec` identifies `M.cnst ``Eq [v] ‘ α ‘ a ‘ x` with
`eqFn M.κ (v.eval M.ls) ‘ α ‘ a ‘ x`. -/
theorem motSet_eq_interp_motTyE (hspec : EqSpec M v) {α a : V}
    (hα : α ∈ U M.κ (v.eval M.ls)) (ha : a ∈ α) :
    motSet M.κ (u.eval M.ls) (v.eval M.ls) (snoc (snoc (∅ : V) α) a)
      = (interp M L (ectxP ([] : List VExpr) v) (motTyE u v)).toFun (snoc (snoc (∅ : V) α) a) := by
  have hdom : (interp M L (ectxP ([] : List VExpr) v) (.bvar 1)).toFun
      (snoc (snoc (∅ : V) α) a) = α := by
    rw [interp_bvar]
    simp only [List.length_cons, List.length_nil]
    rw [show (2 - 1 - 1 : ℕ) = 0 from rfl]
    exact r2_0
  rw [show motTyE u v = VExpr.forallE (.bvar 1)
      (.forallE (eqAp v (.bvar 2) (.bvar 1) (.bvar 0)) (.sort u)) from rfl,
    interp_forallE_type M L (not_isProp_motInner (Γ := []) hu hv hle trivial)]
  unfold motSet
  refine mkForallType_ext (by rw [hdom]; exact r2_0) (fun x hx ↦ ?_)
  rw [hdom] at hx
  rw [interp_forallE_type M L (not_isProp_sortu (Γ := []) hu hv hle trivial)]
  refine mkForallType_ext ?_ (fun w _ ↦ (interp_sort ..).symm)
  rw [interp_eqApX_val hv hle, hspec α hα a ha x hx,
    r3_0 (f := x), r3_1 (f := x), r3_2 (f := x), eqFn_value hα ha hx]

end Domains

/-! ## 6. The `≠ 0` slice

`InductOracleOK`'s `consts` field at `Eq.rec` on the branch `EqAudit.eqRecSort_eval_eq_zero_iff`
does *not* take.  Six applications of `UnitAudit.mkLam_mem_mkForallType_of_dom`, one per binder,
and one hypothesis: `EqSpec M v`, the same one the `= 0` slice needs.

The innermost step is where the two slices differ in kind.  At `u.eval M.ls = 0` the goal is
`• ∈ f ‘ b ‘ w` and the motive's values had to be shown to be *truth values*
(`EqZeroAudit.motive_value_mem_UProp`, which is where `h0` is spent).  Here the goal is
`m ∈ f ‘ b ‘ h` with `m` the minor premise itself, and `EqSpec` collapses `b` to `a` and `h` to `•`,
so `f ‘ b ‘ h` **is** the minor premise's own type.  Nothing about `U κ 0` is needed, and no
`propext`. -/

section Slice

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ} {L : PropSplit envF nv} {M : ModelData V}
variable {u v : VLevel} (hu : u.WF nv) (hv : v.WF nv) (hle : eqEnv ≤ envF)

include hu hv hle in
/-- **`eqRecFn ∈ ⟦Eq.rec's type⟧` at every non-`Prop` instantiation of the elimination
universe.** -/
theorem eqRecFn_mem_interp_eqRecType (hspec : EqSpec M v) (hn : u.eval M.ls ≠ 0) :
    eqRecFn M.κ (u.eval M.ls) (v.eval M.ls) ∈
      (interp M L [] ((eqIndDecl.recType 0).instL [u, v])).toFun ∅ := by
  rw [eqRecType_instL,
    interp_forallE_type M L (not_isProp_recBA (Γ := []) hu hv hle trivial hn)]
  unfold eqRecFn
  refine UnitAudit.mkLam_mem_mkForallType_of_dom (by rw [interp_sort]) (fun α hα ↦ ?_)
  rw [interp_sort] at hα
  -- layer 2: the parameter `a : α`
  rw [interp_forallE_type M L (not_isProp_recBM (Γ := []) hu hv hle trivial hn)]
  unfold lamA
  refine UnitAudit.mkLam_mem_mkForallType_of_dom (interp_alTy_ctxA α).symm (fun a ha ↦ ?_)
  rw [interp_alTy_ctxA, r1_0] at ha
  -- layer 3: the motive
  rw [interp_forallE_type M L (not_isProp_recBN (Γ := []) hu hv hle trivial hn)]
  unfold lamF
  refine UnitAudit.mkLam_mem_mkForallType_of_dom
    (motSet_eq_interp_motTyE hu hv hle hspec hα ha) (fun f hf ↦ ?_)
  -- layer 4: the minor premise
  rw [interp_forallE_type M L (not_isProp_recBB (Γ := []) hu hv hle trivial hn)]
  unfold lamM
  refine UnitAudit.mkLam_mem_mkForallType_of_dom
    (by rw [r3_2, r3_1, interp_minTyE_val hu hv hle]) (fun m hm ↦ ?_)
  rw [interp_minTyE_val hu hv hle] at hm
  -- layer 5: the index `b : α`
  rw [interp_forallE_type M L (not_isProp_recBH (Γ := []) hu hv hle trivial hn)]
  unfold lamB
  refine UnitAudit.mkLam_mem_mkForallType_of_dom
    (interp_alTy_ctxN α a f m).symm (fun b hb ↦ ?_)
  rw [interp_alTy_ctxN, r4_0] at hb
  -- layer 6: the major premise `h : Eq α a b`
  rw [interp_forallE_type M L (not_isProp_resE (Γ := []) hu hv hle trivial hn)]
  unfold lamH
  refine UnitAudit.mkLam_mem_mkForallType_of_dom
    (by rw [r5_0, r5_1, r5_4, eqFn_value hα ha hb, interp_majTyE_val hu hv hle,
      hspec α hα a ha b hb]) (fun h hh ↦ ?_)
  rw [interp_majTyE_val hu hv hle, hspec α hα a ha b hb] at hh
  rw [interp_resE_val hu hv hle, r5_3]
  by_cases hab : a = b
  · rw [if_pos hab] at hh
    obtain rfl : h = (pt : V) := mem_singleton_iff.mp hh
    subst hab
    exact hm
  · rw [if_neg hab] at hh
    exact absurd hh not_mem_empty

end Slice

/-! ## 7. Anti-vacuity: the conclusion is not free

The form `EqRecNec.recCell_discriminates` fixes: **at one and the same parameter tuple** the
membership holds at the good value and fails at a bad one.  Checking only that the hypotheses are
satisfiable would not catch a conclusion that every set satisfies, and `mkForallType`-membership is
exactly the kind of statement that can degenerate (over an *empty* domain `mkForallType` is `{∅}`).
Here the bad value is `•`, excluded by `EqAudit.pt_not_mem_interp_eqRecType_of_ne`, whose own
hypothesis (`x ∈ U M.κ (v.eval M.ls)`) is the parameter-space inhabitant that §6.4–6.5 of
`EqOracle.lean` show satisfiable and necessary.

**Note which side of the slice needs that inhabitant.**  It is the *exclusion* of `•`, not the
positive slice: `eqRecFn_mem_interp_eqRecType` carries no such hypothesis.  So the brief's
"the `≠ 0` side condition needs a parameter-space inhabitant" is right about the exclusion and
does **not** apply to the value's own membership. -/

section Discriminate

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ} (L : PropSplit envF nv) (M : ModelData V)
variable {u v : VLevel} (hu : u.WF nv) (hv : v.WF nv) (hle : eqEnv ≤ envF)

include hu hv hle in
/-- **The cell discriminates.**  One environment, one `L`, one `M`, one `(u, v)`: `eqRecFn` is a
member and `•` is not.  So neither the type nor the interpretation is degenerate at this
instantiation, and the positive theorem is not an instance of "everything is in there". -/
theorem recCell_discriminates_of_ne (hspec : EqSpec M v) (hn : u.eval M.ls ≠ 0)
    {x : V} (hx : x ∈ U M.κ (v.eval M.ls)) :
    eqRecFn M.κ (u.eval M.ls) (v.eval M.ls) ∈
        (interp M L [] ((eqIndDecl.recType 0).instL [u, v])).toFun ∅ ∧
      (pt : V) ∉ (interp M L [] ((eqIndDecl.recType 0).instL [u, v])).toFun ∅ :=
  ⟨eqRecFn_mem_interp_eqRecType hu hv hle hspec hn,
    pt_not_mem_interp_eqRecType_of_ne L M hu hv hle hn hx⟩

include L M hu hv hle in
/-- …and the two values really are different sets, which is what makes the conjunction above
informative rather than a statement about one set under two names. -/
theorem eqRecFn_ne_pt (hspec : EqSpec M v) (hn : u.eval M.ls ≠ 0)
    {x : V} (hx : x ∈ U M.κ (v.eval M.ls)) :
    eqRecFn M.κ (u.eval M.ls) (v.eval M.ls) ≠ (pt : V) := by
  intro h
  exact (recCell_discriminates_of_ne L M hu hv hle hspec hn hx).2
    (h ▸ (recCell_discriminates_of_ne L M hu hv hle hspec hn hx).1)

end Discriminate

/-! ## 8. `preludeWitness` is **REFUTED** at this cell

`SetModel.preludeWitness` — the joint witness for `EqSpec`, `IffSpec` and `NonemptySpec`, and the
assignment `EqTypeFormer.lean` §4 uses to close the type-former cell — sends every name outside
`{Eq, Iff, Nonempty}` to `∅`, and `SetModel.pt` **is** `∅` (`Universe.lean`).  So its `Eq.rec`
entry is `•`:

* on the `= 0` slice that is *correct* (`EqZeroAudit.pt_mem_interp_eqRecType_of_zero` applies, since
  `preludeWitness_eq` gives `EqSpec`);
* on the `≠ 0` slice it is **refuted**, as soon as the block's own universe is inhabited in the
  model.

This is a real gap in the corner's assembly and it was not visible before the `≠ 0` slice existed:
`InductOracleOK` at `eqIndDecl` cannot be discharged at `preludeWitness` as it stands.  What is
needed is a level-branching `Eq.rec` entry, which is exactly `eqRecVal` in §9 — the same shape
`UnitOracleLarge.unitOracleL` already uses at `unitDeclLE`, so the fix is known, not new
mathematics.  I have **not** edited `PreludeSpec.lean`: `preludeWitness` is consumed by
`PreludeWitness.lean`, `EqTypeFormer.lean` and the `preludeSpec_satisfiable` packaging, and changing
its `cnst` is a decision about the corner's shared witness rather than about this slice. -/

section PreludeGap

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ} (L : PropSplit envF nv) (κ : ℕ → V) (ls : List ℕ)

theorem preludeWitness_cnst_eqRec (us : List VLevel) :
    (preludeWitness (V := V) κ ls).cnst ``Eq.rec us = (pt : V) := by
  simp [preludeWitness, pt]

variable {u v : VLevel} (hu : u.WF nv) (hv : v.WF nv) (hle : eqEnv ≤ envF)

include hu hv hle in
/-- **The `Eq.rec` cell FAILS at `preludeWitness` on the `≠ 0` slice.** -/
theorem preludeWitness_not_mem_interp_eqRecType (hn : u.eval ls ≠ 0)
    {x : V} (hx : x ∈ U κ (v.eval ls)) :
    (preludeWitness (V := V) κ ls).cnst ``Eq.rec [u, v] ∉
      (interp (preludeWitness κ ls) L [] ((eqIndDecl.recType 0).instL [u, v])).toFun ∅ := by
  rw [preludeWitness_cnst_eqRec]
  exact pt_not_mem_interp_eqRecType_of_ne L (preludeWitness κ ls) hu hv hle hn hx

include hu hv hle in
/-- …and it *holds* at `preludeWitness` on the `= 0` slice, which is what makes the previous
theorem a statement about the **level branch** rather than about `preludeWitness` being wrong
everywhere. -/
theorem preludeWitness_mem_interp_eqRecType_of_zero (h0 : u.eval ls = 0) :
    (preludeWitness (V := V) κ ls).cnst ``Eq.rec [u, v] ∈
      (interp (preludeWitness κ ls) L [] ((eqIndDecl.recType 0).instL [u, v])).toFun ∅ := by
  rw [preludeWitness_cnst_eqRec]
  exact EqZeroAudit.pt_mem_interp_eqRecType_of_zero hu hv hle h0 (preludeWitness_eq κ ls v)

end PreludeGap

/-! ## 9. Both slices in one value: the `consts` cell at `Eq.rec`

`OracleOK`'s `type` field quantifies over **all** `us` of length `eqIndDecl.recUvars = 2`, so the
cell is one statement covering both level slices, and `EqAudit.no_level_uniform_value` says no
level-uniform value can serve it.  `eqRecVal` is therefore an `if` on `u.eval ls = 0` — the same
shape `UnitOracleLarge.unitOracleL` uses at `unitDeclLE`, and forced for the same reason. -/

section Oracle

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]

/-- **`Eq.rec`'s oracle value.**  `•` on the `Prop` branch, the six-layer function otherwise. -/
noncomputable def eqRecVal (κ : ℕ → V) (ls : List ℕ) : List VLevel → V
  | [u, v] => if u.eval ls = 0 then (pt : V) else eqRecFn κ (u.eval ls) (v.eval ls)
  | _ => ∅

theorem eqRecVal_pair (κ : ℕ → V) (ls : List ℕ) (u v : VLevel) :
    eqRecVal (V := V) κ ls [u, v]
      = if u.eval ls = 0 then (pt : V) else eqRecFn κ (u.eval ls) (v.eval ls) := rfl

theorem eqRecVal_congr (κ : ℕ → V) (ls : List ℕ) {us us' : List VLevel}
    (hd : List.Forall₂ (· ≈ ·) us us') : eqRecVal (V := V) κ ls us = eqRecVal κ ls us' := by
  rcases hd with _ | ⟨h1, ht1⟩
  · rfl
  rcases ht1 with _ | ⟨h2, ht2⟩
  · rfl
  rcases ht2 with _ | ⟨h3, ht3⟩
  · rw [eqRecVal_pair, eqRecVal_pair, VLevel.equiv_def.mp h1 ls, VLevel.equiv_def.mp h2 ls]
  · rfl

theorem eq_pair_of_length_two {us : List VLevel} (h : us.length = 2) : ∃ u v, us = [u, v] := by
  rcases us with _ | ⟨u, us⟩
  · simp at h
  rcases us with _ | ⟨v, us⟩
  · simp at h
  rcases us with _ | ⟨w, us⟩
  · exact ⟨u, v, rfl⟩
  · simp at h

theorem eqIndDecl_recUvars : eqIndDecl.recUvars = 2 := rfl

variable {envF : VEnv} {nv : ℕ} (L : PropSplit envF nv) (κ : ℕ → V) (ls : List ℕ)

/-- **The `consts` cell at `Eq.rec`, both slices, in one `OracleOK`.**

The hypothesis is `EqSpec ⟨κ, ls, c⟩ w` at every `w` — i.e. the *ambient* assignment `c` that
`interp` reads must denote `Eq` correctly.  That is what `preludeWitness` supplies
(`preludeWitness_eq`); what `preludeWitness` does **not** supply is the `Eq.rec` entry itself (§8),
which is why the oracle `o` is a separate parameter here, pinned by `ho`.

`Above` is discharged by `Above.pure` in both fields (`oracleOK_of`), so no chain hypothesis is used
and **no `κ` is chosen**: the statement is at an arbitrary `κ : ℕ → V`. -/
theorem oracleOK_EqRec (hle : eqEnv ≤ envF) {c : Name → List VLevel → V}
    (hspec : ∀ w : VLevel, EqSpec (⟨κ, ls, c⟩ : ModelData V) w)
    {o : Name → List VLevel → V} (ho : ∀ us, o ``Eq.rec us = eqRecVal κ ls us) :
    OracleOK L κ ls o c ``Eq.rec ⟨eqIndDecl.recUvars, eqIndDecl.recType 0⟩ :=
  oracleOK_of (L := L)
    (fun _ _ hd ↦ by rw [ho, ho]; exact eqRecVal_congr κ ls hd)
    (fun {us} hw hlen ↦ by
      obtain ⟨u, v, rfl⟩ := eq_pair_of_length_two (eqIndDecl_recUvars ▸ hlen)
      rw [ho, eqRecVal_pair]
      have hu : u.WF nv := hw u (by simp)
      have hv : v.WF nv := hw v (by simp)
      by_cases h0 : u.eval ls = 0
      · rw [if_pos h0]
        exact EqZeroAudit.pt_mem_interp_eqRecType_of_zero hu hv hle h0 (hspec v)
      · rw [if_neg h0]
        exact eqRecFn_mem_interp_eqRecType hu hv hle (hspec v) h0)

end Oracle

/-! ## 10. The ι-rule: its shape, **measured**

`EqAudit.eq_iotaRules_length = 1`, and the one rule's three components are below.  Every equation
here is `rfl` — the shapes were *guessed and checked*, not read off the definitions, which matters
because `iotaRule`'s `rhs` is deliberately an η-expansion (`Decl.lean`: "do not simplify `rhs` to
`iotaLam`'s body") and so carries a four-fold β-redex that a reading of `iotaLam` alone would
miss. -/

section IotaShape

/-- `Eq.refl`, as the block stores it. -/
abbrev eqCtor : VIndCtor := ((eqIndDecl.types.getD 0 default).ctors.getD 0 default)

theorem eq_iotaRules_eq : eqIndDecl.iotaRules = [eqIndDecl.iotaRule 0 0 eqCtor] := rfl

theorem eqRule_uvars : (eqIndDecl.iotaRule 0 0 eqCtor).uvars = 2 := rfl

/-- The rule's binder telescope is `params ++ motives ++ minors` — no fields, because
`eqRefl_fields = []`.  Reversed, it is `EqAudit.ectxN`. -/
theorem eq_iotaCtx : eqIndDecl.iotaCtx eqCtor
    = [.sort (.param 1), .bvar 0, motTyE (.param 0) (.param 1), minTyE (.param 1)] := rfl

theorem eq_iotaCtx_reverse (u v : VLevel) :
    ((eqIndDecl.iotaCtx eqCtor).map (VExpr.instL [u, v])).reverse = ectxN [] u v := rfl

/-- **The left-hand side**: `λ α a motive m, Eq.rec α a motive m a (Eq.refl α a)` — six
application nodes, one of which (`Eq.refl α`) is a *proof*, so `interp` discards its argument. -/
theorem eqRule_lhs_instL (u v : VLevel) :
    (eqIndDecl.iotaRule 0 0 eqCtor).lhs.instL [u, v]
      = .lam (.sort v) (.lam (.bvar 0) (.lam (motTyE u v) (.lam (minTyE v)
          (.app (.app (.app (.app (.app (.app (.const ``Eq.rec [u, v]) (.bvar 3)) (.bvar 2))
            (.bvar 1)) (.bvar 0)) (.bvar 2)) (reflAp v (.bvar 3) (.bvar 2)))))) := rfl

/-- **The right-hand side**: the η-expansion, i.e. a four-fold β-redex over `λ α a motive m, m`. -/
theorem eqRule_rhs_instL (u v : VLevel) :
    (eqIndDecl.iotaRule 0 0 eqCtor).rhs.instL [u, v]
      = .lam (.sort v) (.lam (.bvar 0) (.lam (motTyE u v) (.lam (minTyE v)
          (.app (.app (.app (.app
            (.lam (.sort v) (.lam (.bvar 0) (.lam (motTyE u v) (.lam (minTyE v) (.bvar 0)))))
            (.bvar 3)) (.bvar 2)) (.bvar 1)) (.bvar 0))))) := rfl

/-- **The common type**: `∀ α a motive m, motive a (Eq.refl α a)` — i.e. `minTyE` one binder
deeper.  So the ι-rule's type is the *minor premise's* type generalised, which is why its own
sort has the same level branch as the recursor's. -/
theorem eqRule_type_instL (u v : VLevel) :
    (eqIndDecl.iotaRule 0 0 eqCtor).type.instL [u, v]
      = .forallE (.sort v) (.forallE (.bvar 0) (.forallE (motTyE u v) (.forallE (minTyE v)
          (.app (.app (.bvar 1) (.bvar 2)) (reflAp v (.bvar 3) (.bvar 2)))))) := rfl

/-- The rule's sort, in the shape `.forallEDF` produces it. -/
abbrev eqRuleSort (u v : VLevel) : VLevel :=
  .imax (.succ v) (.imax v (.imax (motSortE u v) (.imax u u)))

/-- **The ι-rule has the same level branch as the recursor**: its type is a proposition exactly
when the elimination universe is.  Pure level arithmetic — no typing derivation, so this is
available before the rule's own `HasType` is built, and it is what says the ι-rule must be attacked
in two slices too. -/
theorem eqRuleSort_eval_eq_zero_iff (u v : VLevel) (ls : List ℕ) :
    (eqRuleSort u v).eval ls = 0 ↔ u.eval ls = 0 :=
  imax_eq_zero_iff.trans (imax_eq_zero_iff.trans (imax_eq_zero_iff.trans imax_eq_zero_iff))

end IotaShape

/-! ### 10.1 The ι-rule's **typing is free** — from the general inductive machinery

The expensive-looking part of the ι-rule is typing the saturated recursor spine
`Eq.rec α a motive m a (Eq.refl α a)`: six `hasType_app'` steps, each needing its own `.inst`
equation, which is the trap `EqTypeFormer.lean` §18.8 carries forward.  **None of it has to be
written.**  `Theory/Inductive/Lemmas.lean` proves `VInductDecl'.iotaRules_WF` for *every* block
from `D.IotaCtx env`, and `VInductDecl'.WF.iotaCtx` produces that from the three staged
`addConstList`s — all of which are `rfl` at `VEnv.empty` for this block.

So both sides of `eqIndDecl`'s ι-rule are typed at `eqEnv`, at the rule's own `uvars = 2`, with no
`VExpr` arithmetic at all.  This is the single most useful thing to know before attacking the rule,
and it was not in any handoff. -/

section RuleWF

noncomputable def eqE1 : VEnv := (VEnv.empty.addIndTypes eqIndDecl).getD .empty
theorem eqE1_add : VEnv.empty.addIndTypes eqIndDecl = some eqE1 := rfl

noncomputable def eqE2 : VEnv := (eqE1.addIndCtors eqIndDecl).getD .empty
theorem eqE2_add : eqE1.addIndCtors eqIndDecl = some eqE2 := rfl

noncomputable def eqE3 : VEnv := (eqE2.addIndRecs eqIndDecl).getD .empty
theorem eqE3_add : eqE2.addIndRecs eqIndDecl = some eqE3 := rfl

theorem eqIotaCtx : eqIndDecl.IotaCtx eqE3 :=
  (eqIndDecl_WF _).iotaCtx .empty eqE1_add eqE2_add eqE3_add

theorem eqE3_le_eqEnv : eqE3 ≤ eqEnv := by
  rw [show eqEnv = eqE3.addIndRules eqIndDecl from rfl]
  exact VEnv.addIndRules_le

theorem eqRule_mem : eqIndDecl.iotaRule 0 0 eqCtor ∈ eqIndDecl.iotaRules := by
  rw [eq_iotaRules_eq]; simp

/-- **Both sides of the ι-rule are typed at `eqEnv`** — `VDefEq.WF` unfolds to
`HasType 2 [] lhs type ∧ HasType 2 [] rhs type`. -/
theorem eqRule_WF : VDefEq.WF eqEnv (eqIndDecl.iotaRule 0 0 eqCtor) :=
  ⟨((VInductDecl'.iotaRules_WF eqIotaCtx _ eqRule_mem).1).mono eqE3_le_eqEnv,
    ((VInductDecl'.iotaRules_WF eqIotaCtx _ eqRule_mem).2).mono eqE3_le_eqEnv⟩

/-- The recursor spine, typed, with no `.inst` arithmetic written by hand — this is the
statement §10.1 says comes for free, isolated so the next stream can use it directly. -/
theorem eqRule_lhs_hasType :
    eqEnv.HasType 2 [] (eqIndDecl.iotaRule 0 0 eqCtor).lhs
      (eqIndDecl.iotaRule 0 0 eqCtor).type := eqRule_WF.1

theorem eqRule_rhs_hasType :
    eqEnv.HasType 2 [] (eqIndDecl.iotaRule 0 0 eqCtor).rhs
      (eqIndDecl.iotaRule 0 0 eqCtor).type := eqRule_WF.2

end RuleWF

#print axioms Lean4Lean.SetModel.EqLargeAudit.mkFamUnion_ext
#print axioms Lean4Lean.SetModel.EqLargeAudit.mkForallType_ext
#print axioms Lean4Lean.SetModel.EqLargeAudit.eqAt_definable
#print axioms Lean4Lean.SetModel.EqLargeAudit.eqAt_definable₂
#print axioms Lean4Lean.SetModel.EqLargeAudit.minAt_definable
#print axioms Lean4Lean.SetModel.EqLargeAudit.const_definable₂
#print axioms Lean4Lean.SetModel.EqLargeAudit.motSet_definable
#print axioms Lean4Lean.SetModel.EqLargeAudit.lamH_definable
#print axioms Lean4Lean.SetModel.EqLargeAudit.lamB_definable
#print axioms Lean4Lean.SetModel.EqLargeAudit.lamM_definable
#print axioms Lean4Lean.SetModel.EqLargeAudit.lamF_definable
#print axioms Lean4Lean.SetModel.EqLargeAudit.lamA_definable
#print axioms Lean4Lean.SetModel.EqLargeAudit.not_isProp_recBA
#print axioms Lean4Lean.SetModel.EqLargeAudit.not_isProp_recBM
#print axioms Lean4Lean.SetModel.EqLargeAudit.not_isProp_recBN
#print axioms Lean4Lean.SetModel.EqLargeAudit.not_isProp_recBB
#print axioms Lean4Lean.SetModel.EqLargeAudit.not_isProp_recBH
#print axioms Lean4Lean.SetModel.EqLargeAudit.not_isProp_resE
#print axioms Lean4Lean.SetModel.EqLargeAudit.interp_alTy_ctxA
#print axioms Lean4Lean.SetModel.EqLargeAudit.interp_alTy_ctxN
#print axioms Lean4Lean.SetModel.EqLargeAudit.r4_3
#print axioms Lean4Lean.SetModel.EqLargeAudit.r5_3
#print axioms Lean4Lean.SetModel.EqLargeAudit.r6_3
#print axioms Lean4Lean.SetModel.EqLargeAudit.motSet_eq_interp_motTyE
#print axioms Lean4Lean.SetModel.EqLargeAudit.eqRecFn_mem_interp_eqRecType
#print axioms Lean4Lean.SetModel.EqLargeAudit.recCell_discriminates_of_ne
#print axioms Lean4Lean.SetModel.EqLargeAudit.eqRecFn_ne_pt
#print axioms Lean4Lean.SetModel.EqLargeAudit.preludeWitness_cnst_eqRec
#print axioms Lean4Lean.SetModel.EqLargeAudit.preludeWitness_not_mem_interp_eqRecType
#print axioms Lean4Lean.SetModel.EqLargeAudit.preludeWitness_mem_interp_eqRecType_of_zero
#print axioms Lean4Lean.SetModel.EqLargeAudit.eqRecVal_pair
#print axioms Lean4Lean.SetModel.EqLargeAudit.eqRecVal_congr
#print axioms Lean4Lean.SetModel.EqLargeAudit.eq_pair_of_length_two
#print axioms Lean4Lean.SetModel.EqLargeAudit.eqIndDecl_recUvars
#print axioms Lean4Lean.SetModel.EqLargeAudit.oracleOK_EqRec
#print axioms Lean4Lean.SetModel.EqLargeAudit.eq_iotaRules_eq
#print axioms Lean4Lean.SetModel.EqLargeAudit.eqRule_uvars
#print axioms Lean4Lean.SetModel.EqLargeAudit.eq_iotaCtx
#print axioms Lean4Lean.SetModel.EqLargeAudit.eq_iotaCtx_reverse
#print axioms Lean4Lean.SetModel.EqLargeAudit.eqRule_lhs_instL
#print axioms Lean4Lean.SetModel.EqLargeAudit.eqRule_rhs_instL
#print axioms Lean4Lean.SetModel.EqLargeAudit.eqRule_type_instL
#print axioms Lean4Lean.SetModel.EqLargeAudit.eqRuleSort_eval_eq_zero_iff
#print axioms Lean4Lean.SetModel.EqLargeAudit.eqIotaCtx
#print axioms Lean4Lean.SetModel.EqLargeAudit.eqE3_le_eqEnv
#print axioms Lean4Lean.SetModel.EqLargeAudit.eqRule_WF
#print axioms Lean4Lean.SetModel.EqLargeAudit.eqRule_lhs_hasType
#print axioms Lean4Lean.SetModel.EqLargeAudit.eqRule_rhs_hasType
