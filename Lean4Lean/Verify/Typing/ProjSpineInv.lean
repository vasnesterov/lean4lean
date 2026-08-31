import Lean4Lean.Verify.Typing.ConstSpineWF
import Lean4Lean.Verify.Typing.RecTypePeel
import Lean4Lean.Theory.Typing.StructureRuleFree
import Lean4Lean.Verify.Typing.Expr

/-!
# `TrProj.uniq`, reduced to a congruence

`TrProj.uniq` (`Verify/Typing/Lemmas.lean`) carried four obligations.  Three are now
discharged, and this file discharges the last *environment-side* one, leaving a single
residual that mentions no environment invariant at all:

| # | obligation | status |
|---|---|---|
| 1 | `IsStructure` uniqueness (ledger G4) | `VEnv.WF.structureUniq` (`Verify/Typing/RecTypePeel.lean`) |
| 2 | (B) `IsDefEqU.const_app_inv` at the two recorded typings | **here**, `VEnv.IsStructure.spine_inv` |
| 3 | (D) no-confusion, i.e. `s₁ = s₂` | **here**, same lemma |
| 4 | congruence for `VInductDecl'.projTerm` | open — `VEnv.ProjTermCongr` below |

(2) and (3) were blocked on one thing: `VEnv.RuleFreeHead env s` at a structure name.
`Theory/Typing/StructureRuleFree.lean` now proves it from `VEnv.WF env` and `IsStructure` as
it stands — see that file's header for why the earlier rounds' "not derivable" verdict was
wrong — so both fall out of `VEnv.constApp_inv_of_wf` in one application.

What is left, `VEnv.ProjTermCongr`, is deliberately stated at **one** context and **one**
structure name: transporting the second derivation across `hΓ` and identifying the two names
is exactly the part this file does.  It is *not* a weakened restatement of `uniq` — it is
`uniq` minus every use of an environment invariant.

## Why the residual is stated over two `TrProj` derivations rather than over the agreements

The tempting form is "`StructureAgree` + `us₁ ≈ us₂` + `ps₁ ≡ ps₂` + `ιs₁ ≡ ιs₂` + `e₁ ≡ e₂`
implies the `projTerm`s are defeq", and `VEnv.IsStructure.projData_uniq` below produces
exactly that data.  It is the wrong statement to hand to whoever proves it: a `projTerm`
congruence needs both sides *well-typed* (every step is `IsDefEq.mkAppDF`, `betaMkLams`,
`instAllCongrSort`, each of which types its subject), and the agreements alone do not give
that.  Taking the two `TrProj` derivations keeps `TrProj.wf`'s typing route available, and
costs nothing: `projData_uniq` recovers the agreements from them.
-/

namespace Lean4Lean

/-! ## 1. Obligations (B) and (D)

One application of `VEnv.constApp_inv_of_wf`, with both `RuleFreeHead` side conditions
supplied by `VEnv.IsStructure.ruleFreeHead`.  Note what is *not* needed: no `VEnv.PatWF`
(discharged in `Verify/Typing/ConstSpineWF.lean`), no `VEnv.Params`, and no hypothesis
relating `S₁` to `S₂` — the names being equal is a *conclusion*. -/

/-- **Injectivity of a structure's recorded typing.**  Two terms of two structures' types,
definitionally equal, force the structure names equal, the recorded levels equivalent, and
the recorded spines definitionally equal pointwise. -/
theorem VEnv.IsStructure.spine_inv {env : VEnv} {U : Nat} {Γ : List VExpr}
    {S₁ S₂ : Lean.Name} {D₁ D₂ : VInductDecl'} {T₁ T₂ : VIndType} {C₁ C₂ : VIndCtor}
    {us₁ us₂ : List VLevel} {as₁ as₂ : List VExpr} {e₁ e₂ : VExpr}
    (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (h₁ : env.IsStructure S₁ D₁ T₁ C₁) (h₂ : env.IsStructure S₂ D₂ T₂ C₂)
    (ht₁ : env.HasType U Γ e₁ ((VExpr.const S₁ us₁).mkApp as₁))
    (ht₂ : env.HasType U Γ e₂ ((VExpr.const S₂ us₂).mkApp as₂))
    (H : env.IsDefEqU U Γ e₁ e₂) :
    S₁ = S₂ ∧ List.Forall₂ (· ≈ ·) us₁ us₂ ∧ List.Forall₂ (env.IsDefEqU U Γ) as₁ as₂ :=
  VEnv.constApp_inv_of_wf henv U hΓ (h₁.ruleFreeHead henv) (h₂.ruleFreeHead henv)
    (ht₁.isType henv hΓ) ((H.of_l henv hΓ ht₁).uniqU henv hΓ ht₂)

/-- **Everything `TrProj.uniq` can extract about the two derivations' data.**  The name, the
block records (up to the slack `addInduct'` genuinely loses), the levels, and the two spines
split at the parameter/index boundary.

The split is where the two `length` fields of `TrProj.mk` are spent: `Forall₂` over an append
does not split without knowing the left lengths agree, and they agree only because both
derivations record `ps.length = D.np` and `StructureAgree` equates the parameter
telescopes. -/
theorem VEnv.IsStructure.projData_uniq {env : VEnv} {U : Nat} {Γ : List VExpr}
    {S₁ S₂ : Lean.Name} {D₁ D₂ : VInductDecl'} {T₁ T₂ : VIndType} {C₁ C₂ : VIndCtor}
    {us₁ us₂ : List VLevel} {ps₁ ps₂ ιs₁ ιs₂ : List VExpr} {e₁ e₂ : VExpr}
    (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (h₁ : env.IsStructure S₁ D₁ T₁ C₁) (h₂ : env.IsStructure S₂ D₂ T₂ C₂)
    (ht₁ : env.HasType U Γ e₁ ((VExpr.const S₁ us₁).mkApp (ps₁ ++ ιs₁)))
    (ht₂ : env.HasType U Γ e₂ ((VExpr.const S₂ us₂).mkApp (ps₂ ++ ιs₂)))
    (hp₁ : ps₁.length = D₁.np) (hp₂ : ps₂.length = D₂.np)
    (H : env.IsDefEqU U Γ e₁ e₂) :
    S₁ = S₂ ∧ StructureAgree D₁ T₁ C₁ D₂ T₂ C₂ ∧ StructureLvlAgree D₁ C₁ D₂ C₂ ∧
      List.Forall₂ (· ≈ ·) us₁ us₂ ∧
      List.Forall₂ (env.IsDefEqU U Γ) ps₁ ps₂ ∧ List.Forall₂ (env.IsDefEqU U Γ) ιs₁ ιs₂ := by
  obtain ⟨hS, hus, has⟩ := h₁.spine_inv henv hΓ h₂ ht₁ ht₂ H
  subst hS
  obtain ⟨hag, hlvl⟩ := henv.structureUniq _ _ _ _ _ _ _ h₁ h₂
  have hlen : ps₁.length = ps₂.length := by rw [hp₁, hp₂, VInductDecl'.np, hag.params]
  obtain ⟨hps, hιs⟩ := (List.Forall₂.append_of_left hlen).1 has
  exact ⟨rfl, hag, hlvl, hus, hps, hιs⟩

/-! ## 2. The residual, and the reduction -/

/-- **The one open obligation of `TrProj.uniq`.**  Congruence for the projection encoding, at
a single context and a single structure name.

Everything environment-shaped has been stripped: this asks only that `VInductDecl'.projTerm`
respects definitional equality of its subject and of the arguments the two derivations
recorded.  `VEnv.IsStructure.projData_uniq` says what that difference can be — the records
agree except for `VInductDecl'.lvl` and `VIndField.lvl` (which are `≈`), the levels are `≈`,
and the parameter/index spines are pointwise `IsDefEqU`.

Scope of the remaining work, for whoever takes it: the `≈`-in-levels half goes through
`VEnv.IsDefEq.instL_r`; the spine half is `VEnv.IsDefEq.mkAppDF` at the recursor's telescope,
whose motive and minor arguments contain `ps` *under binders* and, through
`VInductDecl'.projArgs`, contain the earlier projections — so it recurses on `i` exactly as
`projArgs` does, and each step needs the typing the `Verify/Typing/ProjGen*` family provides
for `TrProj.wf`.  It is mechanical and it is not small. -/
def VEnv.ProjTermCongr (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {S : Lean.Name} {i : Nat} {e₁ e₂ e₁' e₂' : VExpr},
    OnCtx Γ (env.IsType U) →
    TrProj env U Γ S i e₁ e₁' → TrProj env U Γ S i e₂ e₂' →
    env.IsDefEqU U Γ e₁ e₂ → env.IsDefEqU U Γ e₁' e₂'

/-- **`TrProj.uniq` from the residual.**  The two things this adds to `ProjTermCongr` are the
two the residual is not asked to do: moving the second derivation across the definitionally
equal context, and *proving the two structure names equal* rather than assuming it.

The transport is `TrProj.mk`'s fields one at a time — deliberately inline rather than via
`TrProj.defeqDFC_target` (`Verify/Typing/DefEqCtx.lean`), which is the same three lines but
sits *downstream* of `Verify/Typing/Lemmas.lean`; this file must stay upstream of it so that
`TrProj.uniq` itself can be closed here-from once the residual lands. -/
theorem TrProj.uniq_of_projTermCongr {env : VEnv} {U : Nat} {Γ₁ Γ₂ : List VExpr}
    {s₁ s₂ : Lean.Name} {i : Nat} {e₁ e₂ e₁' e₂' : VExpr}
    (henv : VEnv.WF env) (hΓ : env.IsDefEqCtx U [] Γ₁ Γ₂)
    (hcongr : env.ProjTermCongr U)
    (H1 : TrProj env U Γ₁ s₁ i e₁ e₁') (H2 : TrProj env U Γ₂ s₂ i e₂ e₂')
    (H : env.IsDefEqU U Γ₁ e₁ e₂) :
    env.IsDefEqU U Γ₁ e₁' e₂' := by
  have hΓ₁ := hΓ.isType
  -- move the second derivation into `Γ₁`, target and all
  have H2' : TrProj env U Γ₁ s₂ i e₂ e₂' := by
    let .mk hS hty hus hps hιs hi hlv hargs hιargs hF17 := H2
    exact .mk hS (hty.defeqDFC henv.ordered (hΓ.symm henv.ordered)) hus hps hιs hi hlv
      (hargs.defeqDFC henv.ordered (hΓ.symm henv.ordered))
      (hιargs.defeqDFC henv.ordered (hΓ.symm henv.ordered)) hF17
  -- the names are equal: obligation (D)
  have hname : s₁ = s₂ := by
    let .mk hS1 hty1 _ _ _ _ _ _ _ _ := H1
    let .mk hS2 hty2 _ _ _ _ _ _ _ _ := H2'
    exact (hS1.spine_inv henv hΓ₁ hS2 hty1 hty2 H).1
  subst hname
  exact hcongr hΓ₁ H1 H2' H

/-! ## 3. Non-vacuity

`ProjTermCongr` is not trivially satisfiable-by-accident and not trivially false:

* it is **implied by** `TrProj.uniq` (take `Γ₁ = Γ₂ = Γ`, `hΓ := IsDefEqCtx.refl`), so
  assuming it assumes nothing beyond the goal — no hypothesis has been smuggled in;
* it is **not vacuous**, because `TrProj` derivations exist at real environments:
  `Verify/StructureBridge.lean` builds them, and `Verify/Typing/ProjLevelWitness.lean`'s
  `barEnv_IsStructure` supplies the `IsStructure` they need.

A reflexivity check on the statement is *not* available in this file: it needs `TrProj.wf`
to know the encoded term is well-typed, and `wf` lives downstream in
`Verify/Typing/Lemmas.lean`.  That is a fact about file order, not about the statement. -/

end Lean4Lean
