import Lean4Lean.Theory.Typing.EtaOrient

/-!
# A `VEnv.Params` instance at a structure environment, and the SE rules with the pin off

Round of 2026-09-04, `docs/handoff-paramsstruct.md`.

`Theory/Typing/EtaOrient.lean` fired the three new structure-eta rules eight times, each
pinned to a concrete environment by a hypothesis `(he : env = MutField.unitEnv)` /
`(he : env = MutField.declEnv)`, and concluded that **no `Params` instance satisfying those
hypotheses exists**, on the grounds that a structure site forces ι-rules into `env.defeqs`,
`Params.extra_pat` forces them `Pat`-registered, and that is `PatWF`'s ι case.

**That conclusion is false, and this file exhibits the instances.**  Three facts, each already
in the tree at the time `EtaOrient.lean` was written and all three inside its own import
closure:

* `VEnv.patWF` / `VEnv.paramsOfPiInv` (`Theory/Typing/PatWFIota.lean`) close **all three** of
  `Pat`'s constructors — the ι case included — at an *arbitrary* `VEnv.WF` environment, with
  `VEnv.PiInv` as the only extra hypothesis; and `VEnv.piInv_axiom`
  (`Theory/Typing/Injectivity.lean`) supplies `PiInv` from the existing census holes.  So
  `PatWF`'s ι case is not open; it is *tainted*, which is a different verdict.
* `MutField.declEnv_wf : VEnv.WF declEnv` and `MutField.unitEnv_wf : VEnv.WF unitEnv`
  (`Verify/TypeChecker/EtaUnitRefute.lean:9,33`) are **proved and `sorry`-free**.
  `EtaOrient.lean`'s prose says "`VEnv.WF declEnv` is open for everybody"; it is not, and has
  not been.  `MutField.decl_WF` is likewise `sorry`-free, and `declEnv_eq` is `⟨_, rfl⟩` — the
  block is added to the **empty** environment, where `addInduct'` computes, so **none of this
  touches the `AddInduct` flip**.
* `VEnv.paramsOfWF` (`Theory/Typing/ParamsBuild.lean`) is `sorry`-free and supplies the other
  nine fields.

So the instance is a composition, and this file is mostly bookkeeping around it.  What is new
is §1: the eight firings do not need the concrete environment *at all*.  A `StructEtaSite` at
**any** well-formed environment fires all three rules at `paramsOfPiInv`, so `MutField` is
demoted from "the only place the rule can be stated" to "one instantiation".

## Price

Everything in §1 and §3 inherits, and adds nothing to, the cone of `piInv_axiom`:
`IsDefEqU.forallE_inv_stratified` and `VEnv.WF.rigidShapeUniqNS` — **two** census holes, not
one, and `VEnv.IsDefEq.uniq` / `IsDefEq.uniqU` in the cone as watched-by-policy names.  §2's
`VEnv.WF` witnesses and §5's refutations are `sorry`-free.  Per-name axiom sets are printed at
the bottom of this file and tabulated in the handoff.

## What this does **not** do, stated up front

`MutField.unitEnv_not_structEtaG` (`Verify/TypeChecker/EtaUnitRefute.lean`) refutes
`unitEnv.StructEtaG`.  So at the very environments where the SE rules now fire
unconditionally, the eta rule they encode is **not** derivable from `IsDefEq` — §5 records
that as `unitParams_fires_but_rule_false`.  The instance is a witness that the SE relations
are *inhabited*, not evidence that they are sound over the 13-constructor judgment.  §5 also
shows `¬ declEnv.IotaFree`, so the hole-free route (`paramsOfIotaFree`, `paramsOfDelta`) is
genuinely unavailable here and the two `piInv` holes are load-bearing, not laziness.
-/

namespace Lean4Lean

open VExpr

namespace VEnv

/-! ## §1 The three structure-eta rules at an **arbitrary** well-formed environment

`paramsOfPiInv henv U (piInv_axiom henv)` is a `Params` instance whose `env` is `env` and
whose `univs` is `U`, both by `rfl`.  So a `StructEtaSite` stated about a bare `env`/`U` is
already a site *at that instance*, and each rule fires by its own constructor with no rewriting
and no equation hypothesis.  This is `EtaOrient.lean` §6's content with `MutField` deleted. -/

section
variable {env : VEnv} {U : Nat} {Γ : List VExpr} {S : Lean.Name} {D : VInductDecl'} {j : Nat}
  {T : VIndType} {C : VIndCtor} {us : List VLevel} {ps : List VExpr} {e e₂ : VExpr}

/-- The canonical `Params` instance at a well-formed environment: `paramsOfPiInv` with
Π-injectivity taken from the census holes rather than carried. -/
@[instance_reducible] noncomputable def paramsOfWFAx (henv : env.WF) (U : Nat) : Params :=
  paramsOfPiInv henv U (piInv_axiom henv)

theorem paramsOfWFAx_env (henv : env.WF) (U : Nat) : (paramsOfWFAx henv U).env = env := rfl
theorem paramsOfWFAx_univs (henv : env.WF) (U : Nat) : (paramsOfWFAx henv U).univs = U := rfl

/-- **`ParRedSE.structEta` — expansion orientation — at an arbitrary well-formed environment.** -/
theorem parRedSE_structEta_of_wf (henv : env.WF)
    (h : StructEtaSite env U Γ S D j T C us ps e) :
    @ParRedSE (paramsOfWFAx henv U) Γ e (D.etaExpansionG T C us ps j e) := by
  exact @ParRedSE.structEta (paramsOfWFAx henv U) _ _ _ _ _ _ _ _ _ h

/-- **`ParRedSEC.structEtaC` — contraction orientation — at an arbitrary well-formed
environment.**  This is the rule `EtaOrient.lean` argues for, now with no pin. -/
theorem parRedSEC_structEtaC_of_wf (henv : env.WF)
    (h : StructEtaSite env U Γ S D j T C us ps e) :
    @ParRedSEC (paramsOfWFAx henv U) Γ (D.etaExpansionG T C us ps j e) e := by
  exact @ParRedSEC.structEtaC (paramsOfWFAx henv U) _ _ _ _ _ _ _ _ _ h

/-- **`NormalEqSE.structEtaL` at an arbitrary well-formed environment.** -/
theorem normalEqSE_structEtaL_of_wf (henv : env.WF)
    (h : StructEtaSite env U Γ S D j T C us ps e)
    (h2 : @NormalEqSE (paramsOfWFAx henv U) Γ (D.etaExpansionG T C us ps j e) e₂) :
    @NormalEqSE (paramsOfWFAx henv U) Γ e e₂ := by
  exact @NormalEqSE.structEtaL (paramsOfWFAx henv U) _ _ _ _ _ _ _ _ _ _ h h2

/-- **`NormalEqSE.structEtaR` at an arbitrary well-formed environment.** -/
theorem normalEqSE_structEtaR_of_wf (henv : env.WF)
    (h : StructEtaSite env U Γ S D j T C us ps e)
    (h2 : @NormalEqSE (paramsOfWFAx henv U) Γ e₂ (D.etaExpansionG T C us ps j e)) :
    @NormalEqSE (paramsOfWFAx henv U) Γ e₂ e := by
  exact @NormalEqSE.structEtaR (paramsOfWFAx henv U) _ _ _ _ _ _ _ _ _ _ h h2

/-- **The contraction step, and the `sizeOf` decrease with it, at an arbitrary well-formed
environment with a positive-field site.**  `EtaOrient.lean` §5 proves the decrease at every
`Params` instance already; what is new is that the *site* no longer has to be `MutField`'s. -/
theorem structEtaStepC_of_wf (henv : env.WF) (hf : 0 < C.fields.length)
    (h : StructEtaSite env U Γ S D j T C us ps e) :
    @StructEtaStepC (paramsOfWFAx henv U) Γ (D.etaExpansionG T C us ps j e) e :=
  ⟨S, D, j, T, C, us, ps, h, hf, rfl⟩

end

end VEnv

/-! ## §2 The two concrete instances

Both are `noncomputable` only because `MutField.declEnv` is (`declEnv_eq.choose`). -/

namespace MutField

/-- **A `VEnv.Params` instance whose environment contains a two-type mutual inductive block
whose projected member has a positive field.**  This is the object `EtaOrient.lean` says does
not exist. -/
@[instance_reducible] noncomputable def declParams : VEnv.Params := VEnv.paramsOfWFAx declEnv_wf 0

/-- The same over `unitEnv`, which additionally has the axiom `MutField.foo`. -/
@[instance_reducible] noncomputable def unitParams : VEnv.Params := VEnv.paramsOfWFAx unitEnv_wf 0

theorem declParams_env : declParams.env = declEnv := rfl
theorem declParams_univs : declParams.univs = 0 := rfl
theorem unitParams_env : unitParams.env = unitEnv := rfl
theorem unitParams_univs : unitParams.univs = 0 := rfl

/-- **The eight pinned firings' hypotheses are satisfiable** — "instantiate, don't admire".
Each of `EtaOrient.lean`'s §6 theorems takes `(he : env = declEnv) (hu : univs = 0)`; this is
the witness that the pair is not vacuous. -/
theorem declParams_pin_satisfiable : ∃ I : VEnv.Params, I.env = declEnv ∧ I.univs = 0 :=
  ⟨declParams, rfl, rfl⟩

theorem unitParams_pin_satisfiable : ∃ I : VEnv.Params, I.env = unitEnv ∧ I.univs = 0 :=
  ⟨unitParams, rfl, rfl⟩

/-! ## §3 The eight firings, unpinned

Each is `EtaOrient.lean`'s statement with `(he) (hu)` discharged by `rfl` at the instance of
§2, so what was a conditional becomes a theorem. -/

theorem unitEnv_parRedSE_structEta' :
    @VEnv.ParRedSE unitParams [] ((VExpr.const `MutField.foo []).mkApp [])
      (decl.etaExpansionG aTy aCtor [] [] 0 ((VExpr.const `MutField.foo []).mkApp [])) :=
  @unitEnv_parRedSE_structEta unitParams rfl rfl

theorem declEnv_parRedSE_structEta' :
    @VEnv.ParRedSE declParams bCtx (.bvar 0) (decl.etaExpansionG bTy bCtor [] [] 1 (.bvar 0)) :=
  @declEnv_parRedSE_structEta declParams rfl rfl

theorem unitEnv_parRedSEC_structEtaC' :
    @VEnv.ParRedSEC unitParams []
      (decl.etaExpansionG aTy aCtor [] [] 0 ((VExpr.const `MutField.foo []).mkApp []))
      ((VExpr.const `MutField.foo []).mkApp []) :=
  @unitEnv_parRedSEC_structEtaC unitParams rfl rfl

theorem declEnv_parRedSEC_structEtaC' :
    @VEnv.ParRedSEC declParams bCtx (decl.etaExpansionG bTy bCtor [] [] 1 (.bvar 0)) (.bvar 0) :=
  @declEnv_parRedSEC_structEtaC declParams rfl rfl

theorem unitEnv_normalEqSE_structEtaL' :
    @VEnv.NormalEqSE unitParams [] ((VExpr.const `MutField.foo []).mkApp [])
      (decl.etaExpansionG aTy aCtor [] [] 0 ((VExpr.const `MutField.foo []).mkApp [])) :=
  @unitEnv_normalEqSE_structEtaL unitParams rfl rfl

theorem unitEnv_normalEqSE_structEtaR' :
    @VEnv.NormalEqSE unitParams []
      (decl.etaExpansionG aTy aCtor [] [] 0 ((VExpr.const `MutField.foo []).mkApp []))
      ((VExpr.const `MutField.foo []).mkApp []) :=
  @unitEnv_normalEqSE_structEtaR unitParams rfl rfl

theorem declEnv_normalEqSE_structEtaL' :
    @VEnv.NormalEqSE declParams bCtx (.bvar 0)
      (decl.etaExpansionG bTy bCtor [] [] 1 (.bvar 0)) :=
  @declEnv_normalEqSE_structEtaL declParams rfl rfl

theorem declEnv_normalEqSE_structEtaR' :
    @VEnv.NormalEqSE declParams bCtx (decl.etaExpansionG bTy bCtor [] [] 1 (.bvar 0))
      (.bvar 0) :=
  @declEnv_normalEqSE_structEtaR declParams rfl rfl

/-- **`EtaOrient.lean`'s before/after, unpinned.**  Left: the expansion orientation makes
`parRedSES_rigid`'s hypothesis false at this site.  Right: the contraction makes it true. -/
theorem declEnv_rigidity_flips' :
    (¬ ∀ o, @VEnv.ParRedSE declParams bCtx (.bvar 0) o → o = .bvar 0) ∧
    (∀ o, @VEnv.ParRedSEC declParams bCtx (.bvar 0) o → o = .bvar 0) :=
  @declEnv_rigidity_flips declParams rfl rfl

end MutField

/-! ## §4 Both rules, re-derived at the general instance and re-fired at the concrete one

A round-trip check that §1 really is a generalisation of §3 rather than a parallel statement:
§1's general lemma, instantiated at `declEnv_wf` and `declEnv_structEtaSite`, is §3's theorem. -/

namespace MutField

theorem declEnv_parRedSEC_from_general :
    @VEnv.ParRedSEC declParams bCtx (decl.etaExpansionG bTy bCtor [] [] 1 (.bvar 0)) (.bvar 0) :=
  VEnv.parRedSEC_structEtaC_of_wf declEnv_wf declEnv_structEtaSite

theorem unitEnv_parRedSE_from_general :
    @VEnv.ParRedSE unitParams [] ((VExpr.const `MutField.foo []).mkApp [])
      (decl.etaExpansionG aTy aCtor [] [] 0 ((VExpr.const `MutField.foo []).mkApp [])) :=
  VEnv.parRedSE_structEta_of_wf unitEnv_wf unitEnv_structEtaSite

/-! ## §5 The limits, and they are the interesting part

### 5.1 The ι-free shortcut is unavailable, so the two `piInv` holes are load-bearing

`Theory/Typing/PatWF.lean` proves `PatWF` outright for `IotaFree` environments
(`patWF_of_iotaFree`) and for δ-fragment ones (`patWF_of_deltaFragment`, hole-free).  Neither
applies here: adding an inductive block *is* adding ι-rules.  So `declParams` cannot be built
by the cheap route, and its two holes are not an artefact of choosing `paramsOfPiInv`. -/

theorem declEnv_defeqs_iotaRule :
    declEnv.defeqs (decl.iotaRule 0 0 aCtor) :=
  VEnv.addInduct'_defeqs declEnv_eq.choose_spec _ (decl.iotaRule_mem (q := 0) rfl)

/-- **`declEnv` is not ι-free.** -/
theorem declEnv_not_iotaFree : ¬ declEnv.IotaFree :=
  fun h => h declEnv_defeqs_iotaRule

theorem unitEnv_defeqs_iotaRule : unitEnv.defeqs (decl.iotaRule 0 0 aCtor) :=
  declEnv_le_unitEnv.defeqs declEnv_defeqs_iotaRule

theorem unitEnv_not_iotaFree : ¬ unitEnv.IotaFree :=
  fun h => h unitEnv_defeqs_iotaRule

/-! ### 5.2 The instance fires the rule at an environment where the rule is false

`unitEnv_not_structEtaG` refutes `unitEnv.StructEtaG`, i.e. structure eta is **not** derivable
from `VEnv.IsDefEq` there.  Yet §3 fires `ParRedSE`/`ParRedSEC`/`NormalEqSE`'s eta
constructors at `unitParams`, whose environment is exactly `unitEnv`.  Both at once: the SE
relations are inhabited at a `Params` instance whose environment refutes the rule they encode.
That is the honest reading of this round — the instance removes the *pin*, not the *gap*. -/

theorem unitParams_fires_but_rule_false :
    (@VEnv.ParRedSEC unitParams []
        (decl.etaExpansionG aTy aCtor [] [] 0 ((VExpr.const `MutField.foo []).mkApp []))
        ((VExpr.const `MutField.foo []).mkApp [])) ∧
    ¬ unitParams.env.StructEtaG :=
  ⟨unitEnv_parRedSEC_structEtaC', unitEnv_not_structEtaG⟩

/-- The same at the positive-field member, where `declEnv ≤ unitEnv` carries the refutation
back: `StructEtaG` is a statement about an environment, and `declEnv`'s failure is not implied
by `unitEnv`'s, so this is stated only where it is proved. -/
theorem declParams_env_eq_declEnv : declParams.env = declEnv := rfl

/-! ### 5.3 §1's hypotheses are jointly satisfiable

The one statement that makes §1 more than an admiration: there **is** a well-formed
environment carrying a structure-eta site whose constructor has a positive field, so
`parRedSE_structEta_of_wf` and its three siblings are not vacuously true. -/

theorem exists_wf_structEtaSite_pos :
    ∃ (env : VEnv) (_ : env.WF) (U : Nat) (Γ : List VExpr) (S : Lean.Name) (D : VInductDecl')
      (j : Nat) (T : VIndType) (C : VIndCtor) (us : List VLevel) (ps : List VExpr) (e : VExpr),
      VEnv.StructEtaSite env U Γ S D j T C us ps e ∧ 0 < C.fields.length :=
  ⟨declEnv, declEnv_wf, 0, bCtx, `MutField.B, decl, 1, bTy, bCtor, [], [], .bvar 0,
    declEnv_structEtaSite, bCtor_fields_pos⟩

/-- …and the general contraction step therefore fires, with the `sizeOf` decrease, at a site
that is not named `MutField` in its statement. -/
theorem declEnv_structEtaStepC_from_general :
    @VEnv.StructEtaStepC declParams bCtx (decl.etaExpansionG bTy bCtor [] [] 1 (.bvar 0))
      (.bvar 0) :=
  VEnv.structEtaStepC_of_wf declEnv_wf bCtor_fields_pos declEnv_structEtaSite

end MutField

end Lean4Lean

/-! ## Axiom census for this file -/

#print axioms Lean4Lean.VEnv.paramsOfWFAx
#print axioms Lean4Lean.VEnv.parRedSE_structEta_of_wf
#print axioms Lean4Lean.VEnv.parRedSEC_structEtaC_of_wf
#print axioms Lean4Lean.VEnv.normalEqSE_structEtaL_of_wf
#print axioms Lean4Lean.VEnv.normalEqSE_structEtaR_of_wf
#print axioms Lean4Lean.VEnv.structEtaStepC_of_wf
#print axioms Lean4Lean.MutField.declParams
#print axioms Lean4Lean.MutField.unitParams
#print axioms Lean4Lean.MutField.declParams_pin_satisfiable
#print axioms Lean4Lean.MutField.declEnv_parRedSEC_structEtaC'
#print axioms Lean4Lean.MutField.declEnv_normalEqSE_structEtaL'
#print axioms Lean4Lean.MutField.declEnv_rigidity_flips'
#print axioms Lean4Lean.MutField.declEnv_not_iotaFree
#print axioms Lean4Lean.MutField.unitEnv_not_iotaFree
#print axioms Lean4Lean.MutField.unitParams_fires_but_rule_false
#print axioms Lean4Lean.MutField.exists_wf_structEtaSite_pos
#print axioms Lean4Lean.MutField.declEnv_structEtaStepC_from_general
