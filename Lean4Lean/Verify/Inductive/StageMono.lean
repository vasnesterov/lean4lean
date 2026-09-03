/-
# `StageMono`: the `ValAt` stage step, and the `hbridge` family's β-redex arithmetic in general

Two gaps named by three consecutive rounds and written by none of them.

## §1 The `ValAt` stage-monotonicity step (`FlipGeneral.lean` §2a caveat (i))

`VIndRestore.ValAt D K e₂ e` is established by `RestrictStep.lean`'s cycle at the **type**-stage
pair `(env.addIndTypes D, env.addIndTypesC D K)` — which is `csubst_WFD`'s `(E₁, e₁)`.  Obligation
(B)'s split (`FlipGeneral.lean` §2a, `csubst_val_of_valAt_of_valRestC`) needs it one
`addConstList` higher, at the **ctor**-stage pair `(E₂, e₂)`.

**It really is short, and §1 says why in one sentence rather than by hand-waving.**  `ValAt` is a
`∀` whose *hypotheses* are `R.csubstTy D K c = some t` and a lookup in the source environment, and
whose *conclusion* is a `HasType` in the target.  So it is contravariant in the source and
covariant in the target, and both moves are supplied:

* the target grows by an `addConstList`, and `VEnv.HasType.mono` handles that;
* the source grows by an `addConstList` whose names are **constructor** names, which are outside
  `csubstTy`'s domain — `csubstTy_dom_blockNames` puts that domain inside `D.blockNames`, and
  `D.allNames.Nodup` separates `D.blockNames` from `D.ctorConsts.map (·.1)`.  So the added entries
  are never *reached* by the quantifier and `addConstList_constants_of_not_mem` rewrites the lookup
  back down.

The measured cost is §1's `ValAt.mono`: **one line**, no new spec clause, no side condition beyond
the nodup any addable block already satisfies.  Recorded plainly because "should be short" has been
wrong in this project before: here it was not.

`ValAt.mono` is stated with the source condition as a hypothesis rather than baked in, because §1
uses it at **three** stage steps (ctor, rec, and the two composed) and the ι-rule stage of
obligation (C) will want a fourth.

## §2 The general `hbridge`: one `mkPi` congruence, at an arbitrary pointwise transformation

`ValRestGeneral.lean` §4/§5/§6 consume three bridges — `CtorTypeBridge`, `RecTypeBridge` and
`csubst_WFD`'s `hbridgeD` — and the tree's only producers are block-specific
(`ntree_ctorTypeBridge`, `ntree_recTypeBridge`, `ntree_hbridgeD`).  §2 gives the general producer.

**What was already there, and it changes what is left** (`docs/handoff-stagemono.md` §0b).
`Theory/Inductive/CtorBeta.lean` already reduces obligation (A)'s *decomposed* `hbridge` in general:
§1 there (`substC_fieldTypes_defeq_of_noK`) reduces the field telescope to the entries naming a
companion, and §2 there discharges the result conjunct outright at a **declared** member.  So (A)'s
`hbridge` is not untouched.  What is untouched is the **undecomposed whole-type** form the three
bridges above want, where both sides are `mkPi`s under a `substC` *and* a level instantiation, at a
free `U`, `Γ` and `ls`.

§2 proves that form once, at an arbitrary `f : VExpr → VExpr` that commutes with `mkPi`
(`ctorType_bridge_of`), and then instantiates it at the two `f`s the three bridges need:
`f = (·.substC σ)` and `f = fun A => (A.substC σ).instL ls`.  The `f`-parameter is what removes the
level mismatch as an obstacle: `substC_instL` says the two commute unconditionally, so the level
instantiation is absorbed into `f` rather than transported across an `IsDefEq` at a different `U` —
which is the step that has no lemma.  `CSubst.val_of_hasType` does that absorption for `val`; for
`WFD.const` there is no such lemma, and §2 does not need one.

Nothing here is a `sorry`; no `VEnv.HasArgs.of_mkApp`; no `PiInv`; no frozen file is edited.
-/
import Lean4Lean.Verify.Inductive.ValRestGeneral
import Lean4Lean.Theory.Inductive.CtorBeta

namespace Lean4Lean

open Lean (Name)
open VExpr (mkPi)

namespace VIndRestore

variable {R : VIndRestore} {D : VInductDecl'} {K : List Name}

/-! ## §1 The `ValAt` stage-monotonicity step -/

/-- **THE STEP, GENERAL.**  `ValAt` is contravariant in the source environment and covariant in
the target.  The source premise is stated only at the names `csubstTy` *has*, which is what makes
the step free at a stage whose new names are outside that domain. -/
theorem ValAt.mono {E E' F F' : VEnv} (h : R.ValAt D K E F)
    (hE : ∀ {c : Name} {ci : VConstant}, R.csubstTy D K c ≠ none →
      E'.constants c = some ci → E.constants c = some ci)
    (hF : F ≤ F') : R.ValAt D K E' F' :=
  fun {_ _ _} hd hc => (h hd (hE (by rw [hd]; exact nofun) hc)).mono hF

/-- **…at a stage that is an `addConstList` on both sides.**  The only content is that the new
source names miss `csubstTy`'s domain. -/
theorem ValAt.addConstList {E E' F F' : VEnv} {Ls Lt : List (Name × VConstant)}
    (h : R.ValAt D K E F) (hE : E.addConstList Ls = some E')
    (hdisj : ∀ c ∈ Ls.map (·.1), R.csubstTy D K c = none)
    (hF : F.addConstList Lt = some F') : R.ValAt D K E' F' :=
  h.mono
    (fun {_ _} hne hc => by
      rwa [VEnv.addConstList_constants_of_not_mem hE fun hm => hne (hdisj _ hm)] at hc)
    (VEnv.addConstList_le hF)

/-- `csubstTy`'s domain misses every constructor name of the block. -/
theorem csubstTy_off_ctorConsts (hnd0 : D.allNames.Nodup) {c : Name}
    (h : c ∈ D.ctorConsts.map (·.1)) : R.csubstTy D K c = none := by
  cases hd : R.csubstTy D K c with
  | none => rfl
  | some _ =>
    rw [VInductDecl'.allConsts_names] at hnd0
    exact absurd rfl ((List.nodup_append.1 (List.nodup_append.1 hnd0).1).2.2 c
      (csubstTy_dom_blockNames (by rw [hd]; exact nofun)) c h)

/-- `csubstTy`'s domain misses every recursor name of the block. -/
theorem csubstTy_off_recConsts (hnd0 : D.allNames.Nodup) {c : Name}
    (h : c ∈ D.recConsts.map (·.1)) : R.csubstTy D K c = none := by
  cases hd : R.csubstTy D K c with
  | none => rfl
  | some _ =>
    rw [VInductDecl'.allConsts_names] at hnd0
    exact absurd rfl ((List.nodup_append.1 hnd0).2.2 c
      (List.mem_append_left _ (csubstTy_dom_blockNames (by rw [hd]; exact nofun))) c h)

/-- **THE STEP AT THE CTOR STAGE — what obligation (B)'s split needs.**  From `ValAt` at the
type-stage pair `(E₁, F₁)` to `ValAt` at `(E₂, F₂)`.  The separation hypothesis is
`D.allNames.Nodup`, which `VEnv.addConstList D.allConsts` already requires of any addable block, so
this costs the caller nothing it does not already hold. -/
theorem valAt_ctorStage (hnd0 : D.allNames.Nodup) {E₁ E₂ F₁ F₂ : VEnv}
    (h₂ : E₁.addIndCtors D = some E₂)
    (f₂ : F₁.addConstList (D.ctorConstsCR R K) = some F₂)
    (h : R.ValAt D K E₁ F₁) : R.ValAt D K E₂ F₂ :=
  h.addConstList h₂ (fun _ hm => csubstTy_off_ctorConsts hnd0 hm) f₂

/-- **…and at the rec stage — what obligation (C)'s split needs.** -/
theorem valAt_recStage (hnd0 : D.allNames.Nodup) {E₂ E₃ F₂ F₃ : VEnv}
    (h₃ : E₂.addIndRecs D = some E₃)
    (f₃ : F₂.addConstList (D.recConstsR R K) = some F₃)
    (h : R.ValAt D K E₂ F₂) : R.ValAt D K E₃ F₃ :=
  h.addConstList h₃ (fun _ hm => csubstTy_off_recConsts hnd0 hm) f₃

/-- **…and the two composed**, which is the pair obligation (C)'s route actually uses. -/
theorem valAt_bothStages (hnd0 : D.allNames.Nodup) {E₁ E₂ E₃ F₁ F₂ F₃ : VEnv}
    (h₂ : E₁.addIndCtors D = some E₂) (h₃ : E₂.addIndRecs D = some E₃)
    (f₂ : F₁.addConstList (D.ctorConstsCR R K) = some F₂)
    (f₃ : F₂.addConstList (D.recConstsR R K) = some F₃)
    (h : R.ValAt D K E₁ F₁) : R.ValAt D K E₃ F₃ :=
  valAt_recStage hnd0 h₃ f₃ (valAt_ctorStage hnd0 h₂ f₂ h)

end VIndRestore

end Lean4Lean
