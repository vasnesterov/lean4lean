import Lean4Lean.Theory.SetModel.RecTypePeel
import Lean4Lean.Theory.Inductive.Lemmas
import Lean4Lean.Theory.SetModel.StablePrelude

/-!
# `TeleWF` from `OnCtx`: the level bookkeeping, and the recursor telescope

`Theory/SetModel/RecTypePeel.lean`'s closing section names exactly one thing as missing:

> A general `TeleWF env (D.recPiTele j)` from `D.RecCtx env`: the telescope typings exist
> (`VInductDecl'.RecCtx.onCtxParams`, `onCtxMotives`, `onCtxMinors`, `recType_isType` in
> `Theory/Inductive/Lemmas.lean`) but they carry `OnCtx`, which does not record level
> well-formedness, and `PropSplit`'s two fields do need it.  Bridging that is level bookkeeping
> over `IsDefEq.levelWF`/`CtxStrong.levelWF`, not new mathematics …

That diagnosis is **correct**, and this file discharges it.  Two independent halves:

* **§1, the generic half.**  `TeleWF env nv Γ As` is *equivalent* to `OnCtx (As.reverse ++ Γ)`.
  The level well-formedness `TeleWF.cons` carries is not extra information: `OnCtx` gives
  `∃ u, HasType Γ A (.sort u)`, and `IsDefEq.levelWF` reads `u.WF nv` straight off that typing,
  because `(VExpr.sort u).LevelWF nv` *is* `u.WF nv` by definition of `VExpr.LevelWF`.  So
  `TeleWF.of_onCtx` is the converse of the existing `TeleWF.onCtx`, and the two make an `Iff`.
  Nothing about the `.sort` introduction rule is needed — the level is read off the *type*.

* **§2, the recursor telescope.**  `OnCtx ((D.recPiTele j).reverse) (env.IsType D.recUvars)` from
  `D.RecCtx env` alone.  `recType_isType`'s own proof already builds both halves of it at exactly
  the right contexts (`OnCtx.weakTele` for the index block over parameters/motives/minors, and
  `tyApp'_hasType` for the major premise); `recPiTele.reverse` is that context with the major
  premise on top.  **No inversion of `mkPi` typing is involved** — that was the one thing that
  could have made this real mathematics rather than bookkeeping.

## What this does and does not unlock

`RecTypePeel.lean` continues: "it is the one thing between §7 and a `D`-quantified
surjective-pairing theorem with no `interp` equations left as hypotheses."  **The second clause
of that sentence is an over-claim, and this file is the measurement that shows it.**  What the
bridge discharges is exactly the `TeleWF` side condition of

* `SetModel.exists_sort_mkPi`,
* `SetModel.isProp_mkPi_iff`,
* `SetModel.not_isProof_of_typeFormer` and `not_isProof_bvar_of_typeFormer`,

and hence, through `isProp_mkPi_iff`, the three `IsProp` hypotheses `hpm`/`hpp`/`hpx` of
`SetModel.eq_singleton_of_mem_interp_mkPi3` — which is what reduces three per-binder decisions to
one decision about the body.  It says **nothing** about that theorem's other four hypotheses
`hmot`/`hmin`/`hmaj`/`hbody`: those are `interp` *equations*, not typing facts, and the tree has
them only per-declaration (`UnitOracleLarge.interpL_motTyU` at `unitDeclLE`,
`EqRecLarge.motSet_eq_interp_motTyE` under `EqSpec`, `IffRecLarge.motSetI_eq_interp_motTyI` under
`IffSpec`).  No general `interp (mkPi …) = _ ^ _` equation exists in `Theory/SetModel/`.  The
bridge is an *input* to building those in general, not a substitute for them.
-/

namespace Lean4Lean

open VExpr (mkPi liftTele bvars)

/-! ## 1. The generic half: `OnCtx` + `IsDefEq.levelWF` = `TeleWF` -/

namespace SetModel

variable {env : VEnv} {nv : ℕ}

/-- **The converse of `TeleWF.onCtx`.**  A declaration-order telescope whose reversal is a
well-formed context *is* a `TeleWF`: the per-binder level well-formedness is not extra data, it is
`IsDefEq.levelWF` applied to the binder's own typing, since `(VExpr.sort u).LevelWF nv` unfolds to
`u.WF nv`.  This is the whole of the "level bookkeeping" `RecTypePeel.lean` §11 asks for. -/
theorem TeleWF.of_onCtx : ∀ {As Γ : List VExpr},
    OnCtx (As.reverse ++ Γ) (env.IsType nv) → TeleWF env nv Γ As
  | [], _, _ => .nil
  | A :: As, Γ, h => by
    rw [VExpr.tele_ctx_cons] at h
    obtain ⟨hΓ, u, hA⟩ : OnCtx (A :: Γ) (env.IsType nv) := OnCtx.append_right h
    exact .cons (VEnv.IsDefEq.levelWF hA (StablePrelude.onCtx_levelWF hΓ)).2.2 hA (TeleWF.of_onCtx h)

/-- `TeleWF` and `OnCtx` over a telescope are interchangeable, given the base context. -/
theorem teleWF_iff_onCtx {Γ As : List VExpr} (hΓ : OnCtx Γ (env.IsType nv)) :
    TeleWF env nv Γ As ↔ OnCtx (As.reverse ++ Γ) (env.IsType nv) :=
  ⟨fun h => h.onCtx hΓ, TeleWF.of_onCtx⟩

/-- **A `TeleWF` splits at any point.**  The suffix is a `TeleWF` over the context the prefix
builds.  This is the shape §8's three-binder composition consumes: `hpm`/`hpp`/`hpx` each need a
`TeleWF` for a *tail* of the telescope at an extended context. -/
theorem TeleWF.split_right {Γ As Bs : List VExpr} (hΓ : OnCtx Γ (env.IsType nv))
    (h : TeleWF env nv Γ (As ++ Bs)) : TeleWF env nv (As.reverse ++ Γ) Bs :=
  TeleWF.of_onCtx (by simpa using h.onCtx hΓ)

/-- The prefix of a split is itself a `TeleWF`. -/
theorem TeleWF.split_left {Γ As Bs : List VExpr} (hΓ : OnCtx Γ (env.IsType nv))
    (h : TeleWF env nv Γ (As ++ Bs)) : TeleWF env nv Γ As :=
  TeleWF.of_onCtx (OnCtx.append_right (Δ := Bs.reverse) (by simpa using h.onCtx hΓ))

end SetModel

/-! ## 2. The recursor telescope, for an arbitrary block -/

namespace VInductDecl'

variable {env : VEnv} {D : VInductDecl'}

/-- **`recPiTele` reversed is the context `recType_isType` works in, with the major premise on
top.**  Pure list algebra; the only typing input is `getD_types`. -/
theorem recPiTele_reverse {j : Nat} {T : VIndType} (hT : D.types[j]? = some T) :
    (D.recPiTele j).reverse
      = D.tyApp' j (T.indices.length + D.nmin + D.nm) (bvars 0 T.indices.length)
        :: ((liftTele (D.nm + D.nmin) (D.atRecTele T.indices)).reverse
            ++ (D.minors.reverse ++ D.motives.reverse ++ (D.atRecTele D.params).reverse)) := by
  rw [VInductDecl'.recPiTele, getD_types hT]; simp

/-- **The recursor's complete binder telescope is a well-formed context**, from `RecCtx` alone.
Both halves come from `recType_isType`'s own proof: `OnCtx.weakTele` lifts the index block over
the motives and minors, and `tyApp'_hasType` types the major premise. -/
theorem recPiTele_onCtx (hR : D.RecCtx env) {j : Nat} {T : VIndType}
    (hT : D.types[j]? = some T) :
    OnCtx ((D.recPiTele j).reverse) (env.IsType D.recUvars) := by
  have hmem : T ∈ D.types := List.mem_of_getElem? hT
  have hmin := VInductDecl'.onCtxMinors hR
  have hlenEM : (D.minors.reverse ++ D.motives.reverse).length = D.nm + D.nmin := by
    simp; omega
  have W : Ctx.LiftN (D.nm + D.nmin) 0 (D.atRecTele D.params).reverse
      (D.minors.reverse ++ D.motives.reverse ++ (D.atRecTele D.params).reverse) := .zero _ hlenEM
  have hI := VEnv.OnCtx.weakTele hR.ordered W hmin (hR.onCtxIndices hmem)
  have hdom := VInductDecl'.tyApp'_hasType hR hT W hmin
  rw [show T.indices.length + (D.nm + D.nmin) = T.indices.length + D.nmin + D.nm from by omega]
    at hdom
  rw [recPiTele_reverse hT]
  exact ⟨by simpa using hI, _, by simpa using hdom⟩

/-- **THE BRIDGE.**  `TeleWF env (D.recPiTele j)` from `D.RecCtx env` — the statement
`RecTypePeel.lean` names as the one thing missing from a declaration-quantified peel.  `RecCtx` is
the *only* hypothesis besides naming the block member. -/
theorem recPiTele_teleWF (hR : D.RecCtx env) {j : Nat} {T : VIndType}
    (hT : D.types[j]? = some T) :
    SetModel.TeleWF env D.recUvars [] (D.recPiTele j) :=
  SetModel.TeleWF.of_onCtx (by simpa using recPiTele_onCtx hR hT)

/-- The same with the member named by an index bound rather than by its value. -/
theorem recPiTele_teleWF' (hR : D.RecCtx env) {j : Nat} (hj : j < D.types.length) :
    SetModel.TeleWF env D.recUvars [] (D.recPiTele j) :=
  recPiTele_teleWF hR (T := D.types[j]) (List.getElem?_eq_getElem hj)

/-- **The recursor type's body, typed at the telescope's context.**  Extracted from
`recType_isType`'s own proof (its `hcod`) and restated over `recPiTele`/`recPiBody`, which is the
form `exists_sort_mkPi` and `isProp_mkPi_iff` consume.  This is the *second* input those two need
beside the bridge -- and, measured, it costs **less** than the bridge: `RecCtx` is not needed at
all, only that `j` names a member of the block.  (`recType_isType` passes `hR` in at this point
but never uses it here; `lookup_motive` and `HasArgs.bvars` are both `env`-free.) -/
theorem recPiBody_hasType {j : Nat} {T : VIndType}
    (hT : D.types[j]? = some T) (hj : j < D.nm) :
    env.HasType D.recUvars ((D.recPiTele j).reverse) (D.recPiBody j) (.sort D.elimLvl) := by
  have hcod : env.HasType D.recUvars
      (D.tyApp' j (T.indices.length + D.nmin + D.nm) (bvars 0 T.indices.length)
        :: ((liftTele (D.nm + D.nmin) (D.atRecTele T.indices)).reverse
            ++ (D.minors.reverse ++ D.motives.reverse ++ (D.atRecTele D.params).reverse)))
      ((VExpr.bvar (1 + T.indices.length + D.nmin + (D.nm - 1 - j))).mkApp
        (bvars 1 T.indices.length ++ [.bvar 0])) (.sort D.elimLvl) := by
    refine VInductDecl'.motiveApp_hasType hT hj ?_ .zero ?_
    · have h := VInductDecl'.lookup_motive (D := D) hj
        (D.tyApp' j (T.indices.length + D.nmin + D.nm) (bvars 0 T.indices.length)
          :: (liftTele (D.nm + D.nmin) (D.atRecTele T.indices)).reverse ++ D.minors.reverse)
        (D.atRecTele D.params).reverse
      simp only [List.length_cons, List.length_append, List.length_reverse,
        VExpr.length_liftTele, VInductDecl'.length_atRecTele,
        VInductDecl'.length_minors] at h
      rw [show T.indices.length + 1 + D.nmin = 1 + T.indices.length + D.nmin from by omega] at h
      simpa using h
    · have h := VEnv.HasArgs.bvars (env := env) (U := D.recUvars)
        (Δ := [D.tyApp' j (T.indices.length + D.nmin + D.nm) (bvars 0 T.indices.length)])
        (As := liftTele (D.nm + D.nmin) (D.atRecTele T.indices))
        (Γ₀ := D.minors.reverse ++ D.motives.reverse ++ (D.atRecTele D.params).reverse)
      simp only [List.length_cons, List.length_nil, VExpr.length_liftTele,
        VInductDecl'.length_atRecTele, Nat.zero_add] at h
      simpa using h
  rw [recPiTele_reverse hT, VInductDecl'.recPiBody, getD_types hT]
  exact hcod

/-- **The structure-eta shape has exactly three binders.**  `eq_singleton_of_mem_interp_mkPi3`
is a *three*-binder composition, so a `D`-quantified surjective-pairing theorem built on it can
only quantify over blocks whose `recPiTele` has length 3 -- and that is exactly the shape
`eq_singleton_of_recProp` is about: no parameters, one member, one constructor, no indices.  So
the shape restriction costs nothing, and the bridge's telescope IS that theorem's `[Am, Ap, Ax]`.
-/
theorem recPiTele_length_eq_three {j : Nat} (hp : D.np = 0) (hm : D.nm = 1) (hc : D.nmin = 1)
    (hi : (D.types.getD j default).indices = []) : (D.recPiTele j).length = 3 := by
  rw [recPiTele_length, hp, hm, hc, hi]; rfl

end VInductDecl'

/-! ## 3. What the bridge unlocks, declaration-quantified

`isProp_mkPi_iff` fired at `D.recType j` for an arbitrary block: **every one of the recursor
type's binder-by-binder `IsProp` decisions is the same decision, and it is the body's.**  This is
the general form of the three per-binder `IsProp` hypotheses `hpm`/`hpp`/`hpx` of
`eq_singleton_of_mem_interp_mkPi3`, and it is what the bridge buys.  Its two inputs are the
bridge (`recPiTele_teleWF`) and `recPiBody_hasType`; nothing else about `D` enters. -/

namespace SetModel

open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-- **The recursor type's `IsProp` decision is its body's**, for an arbitrary declaration and an
arbitrary `PropSplit`.  Declaration-quantified — there was no such statement before the bridge,
because `isProp_mkPi_iff` needs `TeleWF` and only `OnCtx` was available. -/
theorem isProp_recType_iff {V : Type*} [SetStructure V] [Nonempty V]
    [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
    {envF env₀ : VEnv} {M : ModelData V} {D : VInductDecl'} {L : PropSplit envF D.recUvars}
    (hle : env₀ ≤ envF) {j : Nat} {T : VIndType}
    (hR : D.RecCtx env₀) (hT : D.types[j]? = some T) (hj : j < D.nm) :
    L.IsProp M [] (D.recType j) ↔ L.IsProp M ((D.recPiTele j).reverse) (D.recPiBody j) := by
  have h := isProp_mkPi_iff (M := M) (L := L) (env₀ := env₀) hle (Γ := [])
    (As := D.recPiTele j) (B := D.recPiBody j) (v := D.elimLvl) trivial
    (VInductDecl'.recPiTele_teleWF hR hT) VInductDecl'.elimLvl_wf
    (by simpa using VInductDecl'.recPiBody_hasType hT hj)
  simpa [D.recType_eq_mkPi j] using h

/-- The same with the member named by an index bound (`D.nm` is `D.types.length` by definition). -/
theorem isProp_recType_iff' {V : Type*} [SetStructure V] [Nonempty V]
    [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
    {envF env₀ : VEnv} {M : ModelData V} {D : VInductDecl'} {L : PropSplit envF D.recUvars}
    (hle : env₀ ≤ envF) {j : Nat} (hR : D.RecCtx env₀) (hj : j < D.types.length) :
    L.IsProp M [] (D.recType j) ↔ L.IsProp M ((D.recPiTele j).reverse) (D.recPiBody j) :=
  isProp_recType_iff hle hR (T := D.types[j]) (List.getElem?_eq_getElem hj) hj

end SetModel

/-! ## 4. Firing the bridge at a real declaration: the parameterised nested block

`InductiveDeclExamples.ntreeAux` is `NTree` together with its nested `List` companion — a
parameterised (`np = 1`), two-member (`nm = 2`), three-minor (`nmin = 3`), index-free block.  The
staging is the same one `Theory/Typing/ConstSubstNested.lean` §D.6 uses: `addIndTypes` then
`addIndCtors`, and `WF.recCtx` at the resulting environment.

The telescope the bridge produces has **7** entries — `np 1 + nm 2 + nmin 3 + 0 indices + 1 major`
— which the audit line below checks against the previously measured
`SetModel.InductiveDeclExamples.ntreeAux_recPiTele_length`, so the telescope is the one it is
claimed to be. -/

namespace InductiveDeclExamples

open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-- **The bridge, fired.**  `TeleWF` for the whole 7-binder recursor telescope of the
parameterised nested block, at the staged environment where its recursors are added. -/
theorem ntreeAux_recPiTele_teleWF {env₁ E₁ E₂ : VEnv} (henv₁ : env₁.Ordered)
    (hE₁ : env₁.addIndTypes ntreeAux = some E₁)
    (hE₂ : E₁.addIndCtors ntreeAux = some E₂) :
    SetModel.TeleWF E₂ ntreeAux.recUvars [] (ntreeAux.recPiTele 0) := by
  have o1 := VInductDecl'.addIndTypes_ordered henv₁ ntreeAux_WF' hE₁
  have o2 := VInductDecl'.addIndCtors_ordered o1 ntreeAux_WF' hE₁ hE₂
  have hR : ntreeAux.RecCtx E₂ := ntreeAux_WF'.recCtx hE₁ hE₂ VEnv.LE.rfl o2
  exact VInductDecl'.recPiTele_teleWF' hR (by simp [ntreeAux])

/-- The same at the block's second member (the nested `List` companion). -/
theorem ntreeAux_recPiTele_teleWF₁ {env₁ E₁ E₂ : VEnv} (henv₁ : env₁.Ordered)
    (hE₁ : env₁.addIndTypes ntreeAux = some E₁)
    (hE₂ : E₁.addIndCtors ntreeAux = some E₂) :
    SetModel.TeleWF E₂ ntreeAux.recUvars [] (ntreeAux.recPiTele 1) := by
  have o1 := VInductDecl'.addIndTypes_ordered henv₁ ntreeAux_WF' hE₁
  have o2 := VInductDecl'.addIndCtors_ordered o1 ntreeAux_WF' hE₁ hE₂
  have hR : ntreeAux.RecCtx E₂ := ntreeAux_WF'.recCtx hE₁ hE₂ VEnv.LE.rfl o2
  exact VInductDecl'.recPiTele_teleWF' hR (by simp [ntreeAux])

/-- **Cross-check.**  The telescope the bridge was fired at is the 7-entry one a previous round
measured: `np 1 + nm 2 + nmin 3 + 0 indices + major`. -/
theorem ntreeAux_recPiTele_teleWF_length : (ntreeAux.recPiTele 0).length = 7 :=
  SetModel.InductiveDeclExamples.ntreeAux_recPiTele_length

/-- **The §3 unlock, fired at the nested block.**  All 7 binder decisions collapse to the body's,
at the staged environment, for any model and any `PropSplit` above it. -/
theorem ntreeAux_isProp_recType_iff {V : Type*} [SetStructure V] [Nonempty V]
    [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
    {envF : VEnv} {M : SetModel.ModelData V} {L : SetModel.PropSplit envF ntreeAux.recUvars}
    {env₁ E₁ E₂ : VEnv} (henv₁ : env₁.Ordered)
    (hE₁ : env₁.addIndTypes ntreeAux = some E₁)
    (hE₂ : E₁.addIndCtors ntreeAux = some E₂) (hle : E₂ ≤ envF) :
    L.IsProp M [] (ntreeAux.recType 0) ↔
      L.IsProp M ((ntreeAux.recPiTele 0).reverse) (ntreeAux.recPiBody 0) := by
  have o1 := VInductDecl'.addIndTypes_ordered henv₁ ntreeAux_WF' hE₁
  have o2 := VInductDecl'.addIndCtors_ordered o1 ntreeAux_WF' hE₁ hE₂
  have hR : ntreeAux.RecCtx E₂ := ntreeAux_WF'.recCtx hE₁ hE₂ VEnv.LE.rfl o2
  exact SetModel.isProp_recType_iff' hle hR (by simp [ntreeAux])

end InductiveDeclExamples

end Lean4Lean

/-! ## 5. Audit

Every statement above is axiom-free beyond the tree's frozen whitelist; the `#print axioms` lines
are the record.  `Lean4Lean.SetModel.TeleWF.of_onCtx` is the whole of the "level bookkeeping"
`RecTypePeel.lean` §11 asks for, and `Lean4Lean.VInductDecl'.recPiTele_teleWF` is the bridge
itself. -/

#print axioms Lean4Lean.SetModel.TeleWF.of_onCtx
#print axioms Lean4Lean.SetModel.teleWF_iff_onCtx
#print axioms Lean4Lean.SetModel.TeleWF.split_right
#print axioms Lean4Lean.SetModel.TeleWF.split_left
#print axioms Lean4Lean.VInductDecl'.recPiTele_reverse
#print axioms Lean4Lean.VInductDecl'.recPiTele_onCtx
#print axioms Lean4Lean.VInductDecl'.recPiTele_teleWF
#print axioms Lean4Lean.VInductDecl'.recPiTele_teleWF'
#print axioms Lean4Lean.VInductDecl'.recPiBody_hasType
#print axioms Lean4Lean.VInductDecl'.recPiTele_length_eq_three
#print axioms Lean4Lean.SetModel.isProp_recType_iff
#print axioms Lean4Lean.SetModel.isProp_recType_iff'
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_recPiTele_teleWF
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_recPiTele_teleWF₁
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_recPiTele_teleWF_length
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_isProp_recType_iff
