import Lean4Lean.Theory.Typing.ConstSubst
import Lean4Lean.Theory.Typing.EnvLemmas
import Lean4Lean.Theory.Inductive.NestedBuild
import Lean4Lean.Theory.Inductive.NestedOrdered

/-!
# The nested step's remaining obligation, at a witness

`VEnv.addInductR_ordered'` (`Theory/Inductive/NestedOrdered.lean`) reduces "a nested
declaration step preserves `VEnv.Ordered`" to three obligations, of which **(A)** is

> a *declared* constructor's **restored** stored type is a type in the environment carrying
> the step's type constants —
> `∀ c ∈ D.ctorConstsCR R K, c.2.WF e₁` with `env.addConstList (D.typeConstsC K) = some e₁`.

What is available is `D.WF env`, whose `ctors` clause types the constructor in `env₃`, the
environment carrying **all** the block's type constants — the auxiliary ones included.  The
gap between the two is precisely one constant substitution, and this file closes it at the
`NFn`/`PFn` witness of `Theory/Inductive/NestedBuild.lean`, using
`VEnv.IsDefEq.substC` (`Theory/Typing/ConstSubst.lean`).

The witness is the one with a non-empty `ξ` (`nfnAux`), and it is an **exact** fit: `NFn`
has no parameters, so the restoration `_nested.PFn_1 ↦ PFn NFn` replaces a constant by a
*closed* term with no lambda, and `VIndCtor.typeR` **is** `VExpr.substC` on the nose
(`nfnNode_substC`, `rfl`).  For a block with parameters that is no longer true — see
`ntreeNode_substC_redex` / `ntreeNode_substC_ne_typeR` / `ntreeNode_typeR_reduct` at the end,
which measure exactly what is missing.  (This sentence used to cite `ntreeAux_substC_beta`, which
does not exist.)
-/

namespace Lean4Lean

open Lean (Name)

/-! ## The general reduction

Obligation **(A)** is not about inductives at all once the substitution theorem exists: it
is the statement that the *restored* constructor type is the *stored* one with the
auxiliary constants substituted away.  This theorem says exactly that, and nothing else is
left of (A). -/

/-- **Obligation (A) reduces to one constant substitution plus a syntactic bridge.**

`hσ` is what `Theory/Typing/ConstSubst.lean` provides: the auxiliary constants of the
staging environment `env₃` are replaced by the terms the restoration presents them as, and
`e₁` — the environment the nested step really declares the constructors in — has everything
else.  `hbridge` is the syntactic half: for a member the step *declares*, `VIndCtor.typeR`
is `VExpr.substC` of `VIndCtor.type`.

Nothing about inductives is used beyond `VInductDecl'.WF.ctors` and
`VIndCtor.WF.constant_wf`, which are exactly what the non-nested `addIndCtors_ordered` uses. -/
theorem VEnv.ctorConstsCR_wf_of_substC {env env₃ e₁ : VEnv} {D : VInductDecl'}
    {K : List Name} {R : VIndRestore} {σ : CSubst}
    (hD : D.WF env) (h₃ : env.addIndTypes D = some env₃) (henv₃ : env₃.Ordered)
    (hσ : σ.WF env₃ e₁ D.uvars)
    (hbridge : ∀ (j : Nat) (T : VIndType) (C : VIndCtor), D.types[j]? = some T →
      T.name ∉ K → C ∈ T.ctors →
      (C.type D j).substC σ = (C.typeR D R j).substC (R.csubstTy D K)) :
    ∀ c ∈ D.ctorConstsCR R K, VConstant.WF e₁ c.2 := by
  intro c hc
  rw [VInductDecl'.ctorConstsCR, List.mem_filterMap] at hc
  obtain ⟨⟨j, C⟩, hjC, hce⟩ := hc
  simp only [] at hce
  by_cases hK : (D.types.getD j default).name ∈ K
  · rw [if_pos hK] at hce; exact absurd hce (by simp)
  · rw [if_neg hK] at hce
    cases hce
    obtain ⟨T, hT, hCT⟩ := VInductDecl'.mem_ctorsAll hjC
    have hTe : D.types.getD j default = T := by
      rw [List.getD_eq_getElem?_getD, hT]; rfl
    rw [hTe] at hK
    have hwf : VConstant.WF env₃ ⟨D.uvars, C.type D j⟩ :=
      (hD.ctors env₃ h₃ j T hT C hCT).constant_wf henv₃
    have hsub := hwf.substC hσ
    rw [hbridge j T C hT hK hCT] at hsub
    exact hsub

/-- **Obligation (B) reduces the same way.**  `hsrc` is what `addInduct'_ordered_final`
already proves for the ordinary block (its recursor stage); `hbridge` says the *renamed*
recursor's type is the ordinary one substituted. -/
theorem VEnv.recConstsR_wf_of_substC {E₂ e₂ : VEnv} {D : VInductDecl'} {R : VIndRestore}
    {σ : CSubst}
    (hsrc : ∀ c ∈ D.recConsts, VConstant.WF E₂ c.2)
    (hσ : σ.WF E₂ e₂ D.recUvars)
    (hbridge : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T →
      (D.recType j).substC σ = (D.recTypeR R j).substC (R.csubst D K)) :
    ∀ c ∈ D.recConstsR R K, VConstant.WF e₂ c.2 := by
  intro c hc
  simp only [VInductDecl'.recConstsR, List.mem_map] at hc
  obtain ⟨⟨T, j⟩, hTj, rfl⟩ := hc
  have hT : D.types[j]? = some T := List.mk_mem_zipIdx_iff_getElem?.1 hTj
  have := (hsrc (Lean.mkRecName T.name, ⟨D.recUvars, D.recType j⟩)
    (by simp only [VInductDecl'.recConsts, List.mem_map]; exact ⟨(T, j), hTj, rfl⟩)).substC hσ
  rw [hbridge j T hT] at this
  exact this

/-- **Obligation (C) reduces the same way.**  `hsrc` is `VInductDecl'.iotaRules_WF`.

Stated about `D.iotaRulesR R` — the rules *before* the step's own substitution.  Since
2026-08-31 `VEnv.addIndRulesR` registers `D.iotaRulesRS R K` instead, so the obligation
`VEnv.addInductR_ordered'` actually asks for is `iotaRulesRS_wf_of_substC` below; this one is
kept because it is what a block on which the substitution is the identity supplies. -/
theorem VEnv.iotaRulesR_wf_of_substC {E₃ e₃ : VEnv} {D : VInductDecl'} {R : VIndRestore}
    {σ : CSubst}
    (hsrc : ∀ df ∈ D.iotaRules, VDefEq.WF E₃ df)
    (hσ : ∀ df ∈ D.iotaRules, σ.WF E₃ e₃ df.uvars)
    (hbridge : D.iotaRules.map (·.substC σ) = D.iotaRulesR R) :
    ∀ df ∈ D.iotaRulesR R, VDefEq.WF e₃ df := by
  intro df hdf
  rw [← hbridge, List.mem_map] at hdf
  obtain ⟨df₀, hdf₀, rfl⟩ := hdf
  exact VDefEq.WF.substC (hσ df₀ hdf₀) (hsrc df₀ hdf₀)

/-- **Obligation (C), for the rules the step really registers.**

`VEnv.addIndRulesR` folds `D.iotaRulesRS R K = (D.iotaRulesR R).map (·.substC (R.csubst D K))`,
so the bridge is now the *same shape* as (A)'s and (B)'s — both sides substituted — rather than
the asymmetric `map (·.substC σ) = iotaRulesR` the unsubstituted fold forced.  That asymmetry
is exactly what made (C) false at `InductiveDeclExamples.nfnAuxDirty`
(`nfnNodeDirty_fieldTypesR_dirty`): `iotaCtxR` splices the *unsubstituted* field telescope, and
nothing downstream removed the companion constant sitting in a non-recursive entry of it.

The proof is unchanged from `iotaRulesR_wf_of_substC` — the content of the repair is in the
definition, not here. -/
theorem VEnv.iotaRulesRS_wf_of_substC {E₃ e₃ : VEnv} {D : VInductDecl'} {R : VIndRestore}
    {K : List Name} {σ : CSubst}
    (hsrc : ∀ df ∈ D.iotaRules, VDefEq.WF E₃ df)
    (hσ : ∀ df ∈ D.iotaRules, σ.WF E₃ e₃ df.uvars)
    (hbridge : D.iotaRules.map (·.substC σ) = D.iotaRulesRS R K) :
    ∀ df ∈ D.iotaRulesRS R K, VDefEq.WF e₃ df := by
  intro df hdf
  rw [← hbridge, List.mem_map] at hdf
  obtain ⟨df₀, hdf₀, rfl⟩ := hdf
  exact VDefEq.WF.substC (hσ df₀ hdf₀) (hsrc df₀ hdf₀)

/-! ## The congruence half of the β-bridge, in general

`ntreeNode_beta_bridge` (below) does one β-step inside a three-entry pi-telescope by hand.
The reusable content is a **telescope congruence**: replacing entries of a pi-telescope by
definitionally equal ones — each in the context it lives in — keeps the telescope a type.
`VEnv.IsType.forallE_congr` is the single-binder case; `VEnv.TeleDefEq` iterates it.

`TeleDefEq.rfl` is there so an *unchanged* entry costs nothing: without it the caller would
have to supply a reflexivity derivation, i.e. re-type every entry it is not touching. -/

/-- Two telescopes, related entrywise in the context each entry lives in.  `rfl` skips an
entry that does not move. -/
inductive VEnv.TeleDefEq (env : VEnv) (U : Nat) : List VExpr → List VExpr → List VExpr → Prop
  | nil : env.TeleDefEq U Γ [] []
  | rfl : env.TeleDefEq U (A::Γ) As As' → env.TeleDefEq U Γ (A::As) (A::As')
  | cons {u : VLevel} : env.IsDefEq U Γ A A' (.sort u) →
      env.TeleDefEq U (A::Γ) As As' → env.TeleDefEq U Γ (A::As) (A'::As')

/-- **The telescope congruence, body fixed.** -/
theorem VEnv.IsType.mkPi_congr {env : VEnv} {U : Nat} (henv : env.Ordered) :
    ∀ {Γ As As' : List VExpr} {B : VExpr}, env.TeleDefEq U Γ As As' →
      env.IsType U Γ (VExpr.mkPi As B) → env.IsType U Γ (VExpr.mkPi As' B) := by
  intro Γ As As' B h
  induction h with
  | nil => exact id
  | rfl _ ih =>
    intro H
    obtain ⟨hA0, H1⟩ := (VExpr.mkPi_cons ▸ H).forallE_inv henv
    exact VExpr.mkPi_cons ▸ VEnv.IsType.forallE hA0 (ih H1)
  | cons hA _ ih =>
    intro H
    obtain ⟨hA0, H1⟩ := (VExpr.mkPi_cons ▸ H).forallE_inv henv
    exact VExpr.mkPi_cons ▸
      VEnv.IsType.forallE_congr henv hA (VEnv.IsType.forallE hA0 (ih H1))

/-- **…and with the body moving too.**  The body's defeq is stated in the *old* telescope's
context, which is where the substituted term is typed. -/
theorem VEnv.IsType.mkPi_congr' {env : VEnv} {U : Nat} {v : VLevel} (henv : env.Ordered) :
    ∀ {Γ As As' : List VExpr} {B B' : VExpr}, env.TeleDefEq U Γ As As' →
      env.IsDefEq U (As.reverse ++ Γ) B B' (.sort v) →
      env.IsType U Γ (VExpr.mkPi As B) → env.IsType U Γ (VExpr.mkPi As' B') := by
  intro Γ As As' B B' h
  induction h with
  | nil => intro hB _; exact ⟨_, hB.hasType.2⟩
  | rfl _ ih =>
    intro hB H
    rw [List.reverse_cons, List.append_assoc] at hB
    obtain ⟨hA0, H1⟩ := (VExpr.mkPi_cons ▸ H).forallE_inv henv
    exact VExpr.mkPi_cons ▸ VEnv.IsType.forallE hA0 (ih hB H1)
  | cons hA _ ih =>
    intro hB H
    rw [List.reverse_cons, List.append_assoc] at hB
    obtain ⟨hA0, H1⟩ := (VExpr.mkPi_cons ▸ H).forallE_inv henv
    exact VExpr.mkPi_cons ▸
      VEnv.IsType.forallE_congr henv hA (VEnv.IsType.forallE hA0 (ih hB H1))

/-- `substC` commutes with `mkPi` — it is structural, so this is an induction on the
telescope and nothing else. -/
theorem VExpr.substC_mkPi {σ : CSubst} :
    ∀ {As : List VExpr} {B : VExpr},
      (VExpr.mkPi As B).substC σ = VExpr.mkPi (As.map (VExpr.substC · σ)) (B.substC σ)
  | [], _ => rfl
  | _ :: As, B => by
    rw [VExpr.mkPi_cons, List.map_cons, VExpr.mkPi_cons, VExpr.substC_forallE,
      substC_mkPi (As := As)]

/-- **Obligation (A), with a *definitional* bridge instead of a syntactic one.**

`VEnv.ctorConstsCR_wf_of_substC` needs
`(C.type D j).substC σ = (C.typeR D R j).substC (R.csubstTy D K)` on the nose.
That equation holds when the block has no parameters, and **fails** when it has: the
restoration replaces a companion constant by a `mkLams` and every occurrence is saturated, so
the two sides differ by one β-step per parameter per occurrence.  This is the same reduction
with the equality weakened to a telescope defeq, which is what a parameterised block can
actually supply. -/
theorem VEnv.ctorConstsCR_wf_of_substC' {env env₃ e₁ : VEnv} {D : VInductDecl'}
    {K : List Name} {R : VIndRestore} {σ : CSubst}
    (hD : D.WF env) (h₃ : env.addIndTypes D = some env₃) (henv₃ : env₃.Ordered)
    (he₁ : e₁.Ordered) (hσ : σ.WF env₃ e₁ D.uvars)
    (hbridge : ∀ (j : Nat) (T : VIndType) (C : VIndCtor), D.types[j]? = some T →
      T.name ∉ K → C ∈ T.ctors →
      ∃ v : VLevel,
        e₁.TeleDefEq D.uvars []
          (((C.params ++ C.fields.map (·.type)).map (VExpr.substC · σ)))
          ((C.params ++ C.fieldTypesR D R).map (VExpr.substC · (R.csubstTy D K))) ∧
        e₁.IsDefEq D.uvars
          (((C.params ++ C.fields.map (·.type)).map (VExpr.substC · σ)).reverse)
          ((C.canonResult D j).substC σ)
          ((D.tyAppR R j C.fields.length C.args).substC (R.csubstTy D K)) (.sort v)) :
    ∀ c ∈ D.ctorConstsCR R K, VConstant.WF e₁ c.2 := by
  intro c hc
  rw [VInductDecl'.ctorConstsCR, List.mem_filterMap] at hc
  obtain ⟨⟨j, C⟩, hjC, hce⟩ := hc
  simp only [] at hce
  by_cases hK : (D.types.getD j default).name ∈ K
  · rw [if_pos hK] at hce; exact absurd hce (by simp)
  · rw [if_neg hK] at hce
    cases hce
    obtain ⟨T, hT, hCT⟩ := VInductDecl'.mem_ctorsAll hjC
    have hTe : D.types.getD j default = T := by
      rw [List.getD_eq_getElem?_getD, hT]; rfl
    rw [hTe] at hK
    have hwf : VConstant.WF env₃ ⟨D.uvars, C.type D j⟩ :=
      (hD.ctors env₃ h₃ j T hT C hCT).constant_wf henv₃
    have hsub := hwf.substC hσ
    obtain ⟨v, htele, hbody⟩ := hbridge j T C hT hK hCT
    rw [show ((C.typeR D R j).substC (R.csubstTy D K))
        = VExpr.mkPi ((C.params ++ C.fieldTypesR D R).map (VExpr.substC · (R.csubstTy D K)))
            ((D.tyAppR R j C.fields.length C.args).substC (R.csubstTy D K)) from
      by rw [VIndCtor.typeR, VExpr.substC_mkPi]]
    refine VEnv.IsType.mkPi_congr' (v := v) he₁ htele (by simpa using hbody) ?_
    have : ((C.type D j).substC σ) = VExpr.mkPi
        ((C.params ++ C.fields.map (·.type)).map (VExpr.substC · σ))
        ((C.canonResult D j).substC σ) := VExpr.substC_mkPi
    exact this ▸ hsub

/-! ## §A The two missing defeq-tolerant bridges, and the congruences they run on

`ctorConstsCR_wf_of_substC'` above is obligation **(A)** with the syntactic bridge equation
weakened to a telescope defeq.  Obligations **(B)** and **(C)** had no such analogue: only the
strict-equality `recConstsR_wf_of_substC` / `iotaRulesRS_wf_of_substC` existed, so the
parameterised block — where the two sides differ by one β-step per parameter per occurrence —
could not reach them even after `VIndRestore.substC_tyApp_defeq_tyAppR_comp`
(`Theory/Inductive/NestedRules.lean` §8.8) removed the bound on `D.np` at the head.

Two congruences are new here, both trivial iterations of a *primitive* `IsDefEq`
constructor and neither needing `env.Ordered`:

* `VEnv.IsDefEq.mkLams_congr` iterates `lamDF` — (C) needs it because an ι-rule's `lhs`/`rhs`
  are `mkLams` over `iotaCtx`, not `mkPi`, so `IsType.mkPi_congr'` does not apply;
* `VEnv.IsDefEq.mkPi_congrU` iterates `forallEDF` and gives a *defeq of two pis at a sort*,
  which `IsType.mkPi_congr'` (whose conclusion is only `IsType`) does not.

**Where (C)' differs in kind from (A)' and (B)'.**  (A)' and (B)' keep their strict
counterpart's `hsrc`/`hσ`: the source's `IsType` pays for every telescope entry the bridge does
*not* move, which is exactly what `TeleDefEq.rfl` is for.  (C)' cannot: `VDefEq.WF` is two
`HasType`s at a `mkLams`, and peeling a λ-telescope off a typing is `HasType.mkLams_inv`
(`Theory/Typing/PatWF.lean`), which needs `env.WF` and `env.PiInv` — circular here.  So the
`lhs`/`rhs` components of (C)'s bridge have to be *typed* defeqs, and a typed defeq already
carries both sides' typing; `hsrc`/`hσ` are then redundant and are **not** hypotheses of
`iotaRulesRS_wf_of_substC'`.  That asymmetry is a fact about `VDefEq.WF`, not an oversight. -/

/-- An unchanged telescope, as a `TeleDefEq`.  Free: `TeleDefEq.rfl` carries no typing. -/
theorem VEnv.TeleDefEq.refl {env : VEnv} {U : Nat} :
    ∀ {As Γ : List VExpr}, env.TeleDefEq U Γ As As
  | [], _ => .nil
  | _ :: _, _ => .rfl refl

/-- **The λ-telescope congruence.**  `IsDefEq.lamDF` iterated; the type is the *left*
telescope's `mkPi`, exactly as `lamDF` gives the left domain.  `OnCtx` is what pays for the
entries `TeleDefEq.rfl` skips — the source typing cannot, because peeling a `mkLams` needs
`HasType.mkLams_inv`. -/
theorem VEnv.IsDefEq.mkLams_congr {env : VEnv} {U : Nat} :
    ∀ {Γ As As' : List VExpr} {b b' B : VExpr}, env.TeleDefEq U Γ As As' →
      OnCtx (As.reverse ++ Γ) (env.IsType U) →
      env.IsDefEq U (As.reverse ++ Γ) b b' B →
      env.IsDefEq U Γ (VExpr.mkLams As b) (VExpr.mkLams As' b') (VExpr.mkPi As B) := by
  intro Γ As As' b b' B h
  induction h with
  | nil => intro _ hb; exact hb
  | rfl _ ih =>
    intro hOn hb
    rw [VExpr.tele_ctx_cons] at hOn hb
    obtain ⟨u, hA⟩ := OnCtx.head_of_append hOn
    rw [VExpr.mkLams_cons, VExpr.mkLams_cons, VExpr.mkPi_cons]
    exact .lamDF hA (ih hOn hb)
  | cons hA _ ih =>
    intro hOn hb
    rw [VExpr.tele_ctx_cons] at hOn hb
    rw [VExpr.mkLams_cons, VExpr.mkLams_cons, VExpr.mkPi_cons]
    exact .lamDF hA (ih hOn hb)

/-- **The pi-telescope congruence, as a defeq at a sort.**  `IsType.mkPi_congr'` concludes
`IsType`, which is enough for a `VConstant.WF` but not for the `type` component of a
`VDefEq.WF` transport, where the two types must be related.  The result level is existential
because `forallEDF` builds a nested `imax`. -/
theorem VEnv.IsDefEq.mkPi_congrU {env : VEnv} {U : Nat} :
    ∀ {Γ As As' : List VExpr} {B B' : VExpr}, env.TeleDefEq U Γ As As' →
      OnCtx (As.reverse ++ Γ) (env.IsType U) →
      (∃ v : VLevel, env.IsDefEq U (As.reverse ++ Γ) B B' (.sort v)) →
      ∃ u : VLevel, env.IsDefEq U Γ (VExpr.mkPi As B) (VExpr.mkPi As' B') (.sort u) := by
  intro Γ As As' B B' h
  induction h with
  | nil => intro _ hb; exact hb
  | rfl _ ih =>
    intro hOn hb
    rw [VExpr.tele_ctx_cons] at hOn hb
    obtain ⟨u, hA⟩ := OnCtx.head_of_append hOn
    obtain ⟨w, hw⟩ := ih hOn hb
    exact ⟨_, VExpr.mkPi_cons ▸ VExpr.mkPi_cons ▸ VEnv.IsDefEq.forallEDF hA hw⟩
  | cons hA _ ih =>
    intro hOn hb
    rw [VExpr.tele_ctx_cons] at hOn hb
    obtain ⟨w, hw⟩ := ih hOn hb
    exact ⟨_, VExpr.mkPi_cons ▸ VExpr.mkPi_cons ▸ VEnv.IsDefEq.forallEDF hA hw⟩

/-- **Obligation (B), with a *definitional* bridge instead of a syntactic one.**

`VEnv.recConstsR_wf_of_substC` needs `(D.recType j).substC σ = (D.recTypeR R j).substC σ'` on
the nose; that holds at `D.params = []` and fails above it by one β-step per parameter per
companion-head occurrence.  Here the caller instead picks a `mkPi` decomposition of each side —
it need not be the one `recType`/`recTypeR` are written with — and relates the two entrywise.
`he₂` is the same `Ordered` hypothesis `ctorConstsCR_wf_of_substC'` takes, for the same reason
(`IsType.forallE_congr` moves the body between the two domains with `defeqDFC`). -/
theorem VEnv.recConstsR_wf_of_substC' {E₂ e₂ : VEnv} {D : VInductDecl'} {R : VIndRestore}
    {K : List Name} {σ : CSubst}
    (hsrc : ∀ c ∈ D.recConsts, VConstant.WF E₂ c.2)
    (hσ : σ.WF E₂ e₂ D.recUvars) (he₂ : e₂.Ordered)
    (hbridge : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T →
      ∃ (As As' : List VExpr) (B B' : VExpr) (v : VLevel),
        (D.recType j).substC σ = VExpr.mkPi As B ∧
        (D.recTypeR R j).substC (R.csubst D K) = VExpr.mkPi As' B' ∧
        e₂.TeleDefEq D.recUvars [] As As' ∧
        e₂.IsDefEq D.recUvars As.reverse B B' (.sort v)) :
    ∀ c ∈ D.recConstsR R K, VConstant.WF e₂ c.2 := by
  intro c hc
  simp only [VInductDecl'.recConstsR, List.mem_map] at hc
  obtain ⟨⟨T, j⟩, hTj, rfl⟩ := hc
  have hT : D.types[j]? = some T := List.mk_mem_zipIdx_iff_getElem?.1 hTj
  have hs := (hsrc (Lean.mkRecName T.name, ⟨D.recUvars, D.recType j⟩)
    (by simp only [VInductDecl'.recConsts, List.mem_map]; exact ⟨(T, j), hTj, rfl⟩)).substC hσ
  obtain ⟨As, As', B, B', v, hL, hRr, htele, hbody⟩ := hbridge j T hT
  refine (show ((D.recTypeR R j).substC (R.csubst D K)) = VExpr.mkPi As' B' from hRr) ▸ ?_
  exact VEnv.IsType.mkPi_congr' (v := v) he₂ htele (by simpa using hbody) (hL ▸ hs)

/-- **`VDefEq.WF` transported along defeqs of the three components.**

`defeqDF` moves each side's typing from the old `type` to the new one.  No source
`VDefEq.WF` is needed: a typed defeq already contains both sides' typing.  This is why (C)'s
defeq-tolerant bridge cannot keep the `hsrc`/`hσ` of `iotaRulesRS_wf_of_substC`. -/
theorem VDefEq.WF.of_congr {env : VEnv} {df df' : VDefEq} {v : VLevel}
    (hu : df'.uvars = df.uvars)
    (hty : env.IsDefEq df.uvars [] df.type df'.type (.sort v))
    (hl : env.IsDefEq df.uvars [] df.lhs df'.lhs df.type)
    (hr : env.IsDefEq df.uvars [] df.rhs df'.rhs df.type) :
    VDefEq.WF env df' :=
  ⟨hu ▸ hty.defeqDF hl.hasType.2, hu ▸ hty.defeqDF hr.hasType.2⟩

/-- **Obligation (C), with a *definitional* bridge instead of a syntactic one.**

`VEnv.iotaRulesRS_wf_of_substC` needs the list equation
`D.iotaRules.map (·.substC σ) = D.iotaRulesRS R K`; this replaces it by, for each registered
rule, a source rule and a componentwise defeq at the *source's* substituted type.  The three
components come from `IsDefEq.mkLams_congr` (`lhs`, `rhs`) and `IsDefEq.mkPi_congrU` (`type`)
over `VInductDecl'.iotaCtx`; see the §A note above for why `hsrc`/`hσ` are absent. -/
theorem VEnv.iotaRulesRS_wf_of_substC' {e₃ : VEnv} {D : VInductDecl'} {R : VIndRestore}
    {K : List Name} {σ : CSubst}
    (hbridge : ∀ df' ∈ D.iotaRulesRS R K, ∃ df ∈ D.iotaRules, ∃ v : VLevel,
      df'.uvars = df.uvars ∧
      e₃.IsDefEq df.uvars [] (df.type.substC σ) df'.type (.sort v) ∧
      e₃.IsDefEq df.uvars [] (df.lhs.substC σ) df'.lhs (df.type.substC σ) ∧
      e₃.IsDefEq df.uvars [] (df.rhs.substC σ) df'.rhs (df.type.substC σ)) :
    ∀ df ∈ D.iotaRulesRS R K, VDefEq.WF e₃ df := by
  intro df' hdf'
  obtain ⟨df, -, v, hu, hty, hl, hr⟩ := hbridge df' hdf'
  exact VDefEq.WF.of_congr (df := df.substC σ) (v := v) hu hty hl hr

/-! ### §A.1 The two primed bridges are weakenings, not replacements

`docs/vacuity-ledger.md` §5: a bridge nothing satisfies is not a bridge.  These two show that
the strict-equality hypothesis of `recConstsR_wf_of_substC` / `iotaRulesRS_wf_of_substC`
*implies* the primed bridge's, so everything already discharged at `D.params = []` (§7.7's
`csubst_recType_eq` / `csubst_iotaRules_eq`) still goes through, and (B)'/(C)' cannot be
vacuous.

**(C) needs one thing (B) does not.**  Factoring (B) is free: `hsrc`'s `VConstant.WF` **is** an
`IsType`, so the reflexive body defeq comes from it.  Factoring (C) needs `htype` — the rule's
substituted `type` is a type in `e₃` — because `VDefEq.WF` is two `HasType`s and says nothing
about its `type` field, and "the type of a typed term is a type" is regularity, which is not
available here (`Theory/Typing/PropShadow.lean`'s `regularity_two_typing_false` shows the
stratified two-typing form of it is outright *false*).  So `htype` is data, and it is data the
strict (C) route never had to produce. -/

theorem VEnv.recConstsR_wf_of_substC_of_eq {E₂ e₂ : VEnv} {D : VInductDecl'} {R : VIndRestore}
    {K : List Name} {σ : CSubst}
    (hsrc : ∀ c ∈ D.recConsts, VConstant.WF E₂ c.2)
    (hσ : σ.WF E₂ e₂ D.recUvars) (he₂ : e₂.Ordered)
    (heq : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T →
      (D.recType j).substC σ = (D.recTypeR R j).substC (R.csubst D K)) :
    ∀ c ∈ D.recConstsR R K, VConstant.WF e₂ c.2 := by
  refine VEnv.recConstsR_wf_of_substC' hsrc hσ he₂ fun j T hT => ?_
  obtain ⟨v, hv⟩ := (hsrc (Lean.mkRecName T.name, ⟨D.recUvars, D.recType j⟩)
    (by simp only [VInductDecl'.recConsts, List.mem_map]
        exact ⟨(T, j), List.mk_mem_zipIdx_iff_getElem?.2 hT, rfl⟩)).substC hσ
  simp only [] at hv
  exact ⟨[], [], (D.recType j).substC σ, (D.recTypeR R j).substC (R.csubst D K), v,
    rfl, rfl, .nil, (heq j T hT) ▸ hv⟩

theorem VEnv.iotaRulesRS_wf_of_substC_of_eq {E₃ e₃ : VEnv} {D : VInductDecl'}
    {R : VIndRestore} {K : List Name} {σ : CSubst}
    (hsrc : ∀ df ∈ D.iotaRules, VDefEq.WF E₃ df)
    (hσ : ∀ df ∈ D.iotaRules, σ.WF E₃ e₃ df.uvars)
    (htype : ∀ df ∈ D.iotaRules, e₃.IsType df.uvars [] (df.type.substC σ))
    (heq : D.iotaRules.map (·.substC σ) = D.iotaRulesRS R K) :
    ∀ df ∈ D.iotaRulesRS R K, VDefEq.WF e₃ df := by
  refine VEnv.iotaRulesRS_wf_of_substC' (σ := σ) fun df' hdf' => ?_
  rw [← heq, List.mem_map] at hdf'
  obtain ⟨df, hdf, rfl⟩ := hdf'
  obtain ⟨v, hv⟩ := htype df hdf
  obtain ⟨hl, hr⟩ := VDefEq.WF.substC (hσ df hdf) (hsrc df hdf)
  exact ⟨df, hdf, v, rfl, hv, hl, hr⟩

/-! ## The restoration, as a constant substitution

`VIndRestore` has five fields — `tyName`, `tyLvls`, `tyArgs`, `ctorName`, `recName` — and
that is exactly the data of a `CSubst`: member `j` of the block is *presented* as
`R.tyName j |>.{R.tyLvls j} (R.tyArgs j)`, and `R.tyArgs j` is a telescope over the block's
own parameters, so the term the constant stands for is that application abstracted over
`D.params`.  A constructor is presented at the *same* spine, and a recursor is a bare
rename.

Two things make this work without any further data:

* `substC` instantiates the value at **the occurrence's** levels (`substC_const_some`), and
  the block's constructions mention a block head at two different level numberings —
  `D.ownLvls` in `tyApp`/`ctorApp`, `D.selfLvls` in `tyApp'`/`ctorApp'`/the recursor.  One
  σ covers both, because `instL` distributes over the value
  (`VIndRestore.tyVal_instL` below); no second substitution is needed.
* the domain is exactly the **companion** members (`T.name ∈ K`).  Off `K`,
  `VIndRestore.OwnId` says the restoration renames nothing, so a σ entry there would be an
  η-expansion rather than the identity — which is why the domain is guarded by `K` and not
  by "is a block name". -/

namespace VIndRestore

open VExpr (mkLams mkApp)

/-! `tyVal`, `ctorVal`, `recVal`, `csubstTyList`, `csubstList`, `csubstTy` and `csubst` are
**no longer defined here**: they moved down to `Theory/Inductive/Restore.lean`, because
`VIndCtor.typeR` now uses `csubstTy` (at the restoration's own domain `R.aux`) to rewrite the
positions it used to copy verbatim.  Everything below is unchanged. -/

/-- `List.lookup` returns an entry of the list.  (Core has the `isSome` form but not this
one at the pin.) -/
theorem _root_.Lean4Lean.List.lookup_mem {β : Type _} {n : Lean.Name} {v : β} :
    ∀ {l : List (Lean.Name × β)}, l.lookup n = some v → (n, v) ∈ l
  | [], h => by simp [List.lookup] at h
  | (a, b) :: l, h => by
    rw [List.lookup_cons] at h
    split at h
    · next hb => cases h; cases (beq_iff_eq.1 hb); exact List.Mem.head _
    · exact List.Mem.tail _ (lookup_mem h)

theorem mem_csubstList_closed {R : VIndRestore} {D : VInductDecl'} {K : List Lean.Name}
    (hp : VExpr.ClosedTele D.params 0)
    (ha : ∀ j, ∀ a ∈ R.tyArgs j, a.ClosedN D.np)
    {p : Lean.Name × VExpr} (h : p ∈ R.csubstList D K) : p.2.ClosedN 0 := by
  rw [csubstList, List.mem_flatMap] at h
  obtain ⟨⟨T, j⟩, -, hp'⟩ := h
  have hval : ∀ (n : Lean.Name) (ls : List VLevel),
      (mkLams D.params ((VExpr.const n ls).mkApp (R.tyArgs j))).ClosedN 0 := by
    intro n ls
    rw [VExpr.closedN_mkLams]
    refine ⟨hp, ?_⟩
    rw [Nat.zero_add, VExpr.closedN_mkApp]
    exact ⟨trivial, ha j⟩
  simp only [List.mem_cons, List.mem_map] at hp'
  obtain rfl | rfl | ⟨C, -, rfl⟩ := hp'
  · exact hval _ _
  · exact trivial
  · exact hval _ _

/-- **Closedness of the general substitution.**  The two hypotheses are the natural ones:
the block's parameter telescope is closed, and each companion's presented spine mentions no
variable beyond the parameters.  Both are `decide`/`rfl`-checkable at a concrete block. -/
theorem csubst_closed (R : VIndRestore) (D : VInductDecl') (K : List Lean.Name)
    (hp : VExpr.ClosedTele D.params 0)
    (ha : ∀ j, ∀ a ∈ R.tyArgs j, a.ClosedN D.np) : (R.csubst D K).Closed :=
  fun {_ _} hc => mem_csubstList_closed hp ha (List.lookup_mem hc)

theorem csubstTy_closed (R : VIndRestore) (D : VInductDecl') (K : List Lean.Name)
    (hp : VExpr.ClosedTele D.params 0)
    (ha : ∀ j, ∀ a ∈ R.tyArgs j, a.ClosedN D.np) : (R.csubstTy D K).Closed := by
  intro c t hc
  have h := List.lookup_mem hc
  rw [csubstTyList, List.mem_map] at h
  obtain ⟨⟨T, j⟩, -, hp'⟩ := h
  cases hp'
  show (mkLams D.params _).ClosedN 0
  rw [VExpr.closedN_mkLams]
  refine ⟨hp, ?_⟩
  rw [Nat.zero_add, VExpr.closedN_mkApp]
  exact ⟨trivial, ha j⟩

end VIndRestore

namespace InductiveDeclExamples

/-! ## The substitution -/

/-- The value the restoration gives the auxiliary constant: `PFn NFn`.  Closed, and — since
`NFn` has no parameters — not a lambda. -/
def nfnVal : VExpr := .app (.const ``PFn []) (.const ``NFn [])

/-- The nested step's constant substitution at the `NFn` witness. -/
def nfnSubst : CSubst := CSubst.one `_nested.PFn_1 nfnVal

theorem nfnSubst_aux : nfnSubst `_nested.PFn_1 = some nfnVal := rfl

theorem nfnSubst_of_ne (h : n ≠ `_nested.PFn_1) : nfnSubst n = none := CSubst.one_of_ne h

/-- **The bridge.**  `VIndCtor.typeR` — the restored stored type, which is what
`Environment.addInductive` actually declares — *is* `VExpr.substC` applied to the stored
type the auxiliary block was checked at. -/
theorem nfnNode_substC :
    (nfnNode.type nfnAux 0).substC nfnSubst = nfnNode.typeR nfnAux nfnRestore 0 := rfl

/-- …and it is a real substitution: the checked type mentions the constant that the
restored one does not. -/
theorem nfnNode_type_mentions_aux : ¬ (nfnNode.type nfnAux 0).NoCSubst nfnSubst := by
  intro h
  have h1 : nfnSubst `_nested.PFn_1 = none := h.1
  simp [nfnSubst_aux] at h1

/-- Lean's own kernel agrees about what the restored type is. -/
example : nfnNode.typeR nfnAux nfnRestore 0 = (vconst(type_of% @NFn.node)).type := rfl

/-! ## The history block is well formed, so the hypothesis above is not vacuous

`Theory/Inductive/NestedBuild.lean` states `nfnAux_WF` over an *abstract* `env₂` given by
`VEnv.empty.addInduct' pfnDecl = some env₂`.  `VEnv.Ordered env₂` is not among the facts it
proves, and without it the substitution's hypotheses cannot be discharged.  It follows from
`pfnDecl.WF VEnv.empty`, which is proved here. -/

theorem pfnDecl_WF : pfnDecl.WF VEnv.empty where
  types_ne := by simp [pfnDecl]
  params := ⟨trivial, _, by type_tac⟩
  types := by
    intro T hT
    simp only [pfnDecl, List.mem_cons, List.not_mem_nil, or_false] at hT
    subst hT
    exact { indices := ⟨trivial, _, by type_tac⟩, isType := ⟨_, by type_tac⟩,
            canon := ⟨_, by type_tac⟩ }
  ctors := by
    intro env₁ hs j T hT C hC
    have hPFn : env₁.constants ``PFn = some ⟨0, pfnType.type⟩ :=
      VEnv.addConstList_constants hs (``PFn, ⟨0, pfnType.type⟩) (by exact List.Mem.head _)
    match j, hT with
    | 0, hT =>
      simp only [pfnDecl] at hT
      cases hT
      simp only [pfnType, List.mem_cons, List.not_mem_nil, or_false] at hC
      subst hC
      refine { params_len := rfl, params_eq := .succ .zero (by type_tac), fields := ?_,
               args_len := rfl, args_fresh := nofun, args_ty := .nil, result := by type_tac }
      intro i F hF
      match i, hF with
      | 0, hF =>
        simp only [pfnMk, List.getElem?_cons_zero, Option.some.injEq] at hF
        subst hF
        exact { hasType := by type_tac
                level := fun ls => by simp [VLevel.eval, pfnDecl, Lean.Nat.imax]
                binders_indep := nofun
                pos := ⟨.bvar 0, by simp [VInductDecl'.NoBlock, VExpr.NoConsts],
                        _, by type_tac⟩ }
      | 1, hF =>
        simp only [pfnMk, List.getElem?_cons_succ, List.getElem?_cons_zero,
          Option.some.injEq] at hF
        subst hF
        exact { hasType := by
                  refine VEnv.HasType.forallE (u := .succ .zero) (v := .succ .zero) ?_ ?_ <;>
                    type_tac
                level := fun ls => by simp [VLevel.eval, pfnDecl, Lean.Nat.imax]
                binders_indep := nofun
                pos := ⟨.forallE (.sort .zero) (.bvar 2),
                        by simp [VInductDecl'.NoBlock, VExpr.NoConsts], _, by
                  refine VEnv.HasType.forallE (u := .succ .zero) (v := .succ .zero) ?_ ?_ <;>
                    type_tac⟩ }
      | (_ + 2), hF => simp [pfnMk] at hF
  isLE := fun _ => .inl (by simp [VLevel.IsNeverZero, VLevel.eval, pfnDecl])

/-- …hence the staging environment of the nested step really is `Ordered`. -/
theorem pfnEnv_ordered {env₂ : VEnv} (h : VEnv.empty.addInduct' pfnDecl = some env₂) :
    env₂.Ordered :=
  VInductDecl'.addInduct'_ordered_final .empty pfnDecl_WF h


/-! ## Obligation (A) at the witness -/

section
variable {env₂ env₃ env₄ : VEnv}
variable (h : VEnv.empty.addInduct' pfnDecl = some env₂) (henv₂ : env₂.Ordered)
variable (h₃ : env₂.addIndTypes nfnAux = some env₃)
variable (h₄ : env₂.addConstList (nfnAux.typeConstsC nfnK) = some env₄)

include h in
/-- `_nested.PFn_1` is fresh in the history environment: `PFn`'s own block never mentions
it, so `Ordered.noCSubst` applies. -/
theorem nfnSubst_fresh : nfnSubst.FreshIn env₂ := by
  intro c ci hc
  cases hn : nfnSubst c with
  | none => rfl
  | some t =>
    have : c = `_nested.PFn_1 := by
      by_cases he : c = `_nested.PFn_1
      · exact he
      · rw [nfnSubst_of_ne he] at hn; exact absurd hn nofun
    subst this
    rw [VEnv.addInduct'_constants_of_not_mem h (by decide)] at hc
    exact absurd hc nofun

include h₄ in
theorem nfn_const₄ : env₄.constants ``NFn = some ⟨0, .sort (.succ .zero)⟩ :=
  VEnv.addConstList_constants h₄ (``NFn, ⟨0, .sort (.succ .zero)⟩) (by exact List.Mem.head _)

include h h₄ in
theorem pfn_const₄ : env₄.constants ``PFn = some ⟨0, pfnType.type⟩ :=
  (VEnv.addConstList_le h₄).constants (pfn_const h)

include h h₄ in
/-- The restoration value is well typed where the step declares the constructor. -/
theorem nfnVal_hasType : env₄.HasType 0 [] nfnVal (.sort (.succ .zero)) := by
  have hp := pfn_const₄ h h₄
  have hn := nfn_const₄ h₄
  type_tac

include henv₂ h₄ in
theorem env₄_ordered : env₄.Ordered :=
  VEnv.addConstList_ordered henv₂ (VEnv.addInductR_typeConstsC_wf nfnAux_WF) h₄

include henv₂ h₃ in
theorem env₃_ordered : env₃.Ordered :=
  VInductDecl'.addIndTypes_ordered henv₂ nfnAux_WF h₃

include h henv₂ h₃ h₄ in
/-- **The substitution is well-formed between the two staging environments.** -/
theorem nfnSubst_WF : nfnSubst.WF env₃ env₄ 0 := by
  have hfresh := nfnSubst_fresh h
  refine CSubst.one_WF (env₀ := env₃) (ci := ⟨0, .sort (.succ .zero)⟩)
    (env₄_ordered henv₂ h₄) ⟨trivial, trivial⟩ ⟨nofun, nofun⟩ trivial
    (pfnaux_const_staged h₃) rfl trivial (nfnVal_hasType h h₄) ?_ ?_
  · intro c' ci' hne hc'
    by_cases hN : c' = ``NFn
    · subst hN
      rw [nfn_const_staged h₃] at hc'; cases hc'
      exact ⟨nfn_const₄ h₄, trivial⟩
    · have hmem : c' ∉ (nfnAux.typeConsts.map (·.1)) := by
        show c' ∉ [``NFn, `_nested.PFn_1]
        simp [hN, hne]
      rw [VEnv.addConstList_constants_of_not_mem h₃ hmem] at hc'
      refine ⟨?_, henv₂.noCSubstC hfresh hc'⟩
      have hmem₄ : c' ∉ ((nfnAux.typeConstsC nfnK).map (·.1)) := by
        show c' ∉ [``NFn]
        simp [hN]
      rw [VEnv.addConstList_constants_of_not_mem h₄ hmem₄]; exact hc'
  · intro df hdf
    rw [VEnv.addConstList_defeqs h₃] at hdf
    exact ⟨(VEnv.addConstList_defeqs h₄) ▸ hdf, henv₂.noCSubstD hfresh hdf⟩

include h henv₂ h₃ h₄ in
/-- **Obligation (A), discharged at the witness.**  The declared constructor's *restored*
type is a type in the environment the nested step actually declares it in — one that does
**not** hold `_nested.PFn_1`. -/
theorem nfnAux_ctorConstsCR_wf :
    ∀ c ∈ nfnAux.ctorConstsCR nfnRestore nfnK, VConstant.WF env₄ c.2 := by
  have hct : VIndCtor.WF env₃ nfnAux 0 (nfnAux.types.getD 0 default) nfnNode :=
    nfnAux_WF.ctors env₃ h₃ 0 _ rfl nfnNode (by simp)
  have hwf : VConstant.WF env₃ ⟨0, nfnNode.type nfnAux 0⟩ :=
    hct.constant_wf (env₃_ordered henv₂ h₃)
  have := hwf.substC (nfnSubst_WF h henv₂ h₃ h₄)
  rw [nfnNode_substC] at this
  intro c hc
  have : nfnAux.ctorConstsCR nfnRestore nfnK
      = [(``NFn.node, ⟨0, nfnNode.typeR nfnAux nfnRestore 0⟩)] := rfl
  rw [this] at hc
  simp only [List.mem_singleton] at hc
  subst hc
  exact ‹VConstant.WF env₄ ⟨0, nfnNode.typeR nfnAux nfnRestore 0⟩›

end


/-! ## …with no hypotheses left

The three environment hypotheses above are all discharged by computation, so obligation (A)
at this witness is an unconditional theorem. -/

theorem nfn_fresh' {env₂ : VEnv} (h : VEnv.empty.addInduct' pfnDecl = some env₂)
    (n : Name) (hn : n ∈ [``NFn, `_nested.PFn_1]) : env₂.constants n = none := by
  rw [VEnv.addInduct'_constants_of_not_mem h (by revert hn; revert n; decide)]
  rfl

theorem nfnAux_staged_exists {env₂ : VEnv} (h : VEnv.empty.addInduct' pfnDecl = some env₂) :
    ∃ env₃, env₂.addIndTypes nfnAux = some env₃ :=
  VEnv.addConstList_eq_some_iff.2 ⟨fun n hn => nfn_fresh' h n hn, by decide⟩

theorem nfnAux_declared_exists {env₂ : VEnv} (h : VEnv.empty.addInduct' pfnDecl = some env₂) :
    ∃ env₄, env₂.addConstList (nfnAux.typeConstsC nfnK) = some env₄ :=
  VEnv.addConstList_eq_some_iff.2
    ⟨fun n hn => nfn_fresh' h n (by revert hn; revert n; decide), by decide⟩

/-- **Obligation (A) at the `NFn`/`PFn` nested witness, unconditionally.** -/
theorem nfnAux_obligationA :
    ∃ env₂ env₃ env₄ : VEnv, VEnv.empty.addInduct' pfnDecl = some env₂ ∧
      env₂.addIndTypes nfnAux = some env₃ ∧
      env₂.addConstList (nfnAux.typeConstsC nfnK) = some env₄ ∧
      ∀ c ∈ nfnAux.ctorConstsCR nfnRestore nfnK, VConstant.WF env₄ c.2 := by
  obtain ⟨env₂, h⟩ : ∃ e, VEnv.empty.addInduct' pfnDecl = some e := ⟨_, rfl⟩
  obtain ⟨env₃, h₃⟩ := nfnAux_staged_exists h
  obtain ⟨env₄, h₄⟩ := nfnAux_declared_exists h
  exact ⟨env₂, env₃, env₄, h, h₃, h₄, nfnAux_ctorConstsCR_wf h (pfnEnv_ordered h) h₃ h₄⟩

/-! ## The parameterised witness: `NTree`/`List`, and the β-step

`NFn` has no parameters, so `_nested.PFn_1` is replaced by a *closed application* and
`VIndCtor.typeR` is `VExpr.substC` on the nose.  A block **with** parameters is different:
`_nested.List_1` has arity `1`, so the term replacing it is a **lambda**, and every
occurrence — which is always saturated, by `VIndCtor.Canonical` — becomes a β-redex.  The
substituted type and the restored type are therefore β-related, not equal.

Both halves are closed here: the substitution theorem produces the redex form, and
`VEnv.IsType.forallE_congr` (`Theory/Typing/Lemmas.lean`) plus `IsDefEq.beta` converts it. -/

/-- The body of the restoration value for `_nested.List_1`: `List.{u} (NTree.{u} α)`. -/
def ntreeBody : VExpr :=
  .app (.const ``List [.param 0]) (.app (.const ``NTree [.param 0]) (.bvar 0))

/-- The value itself: `fun α : Type u => List.{u} (NTree.{u} α)`.  A **lambda**, because the
block has a parameter. -/
def ntreeVal : VExpr := .lam (.sort (.succ (.param 0))) ntreeBody

def ntreeSubst : CSubst := CSubst.one `_nested.List_1 ntreeVal

theorem ntreeSubst_of_ne (h : n ≠ `_nested.List_1) : ntreeSubst n = none := CSubst.one_of_ne h

/-- **The substitution produces a β-redex in a binder domain.** -/
theorem ntreeNode_substC_redex :
    (ntreeNode.type ntreeAux 0).substC ntreeSubst
      = .forallE (.sort (.succ (.param 0)))
          (.forallE (.bvar 0)
            (.forallE (.app ntreeVal (.bvar 1))
              (.app (.const ``NTree [.param 0]) (.bvar 2)))) := rfl

/-- **Negative control: the *syntactic* bridge is false at a parameterised block.**

`VEnv.ctorConstsCR_wf_of_substC` asks for `(C.type D j).substC σ = C.typeR D R j`.  That
equation is not merely unproved for a block with parameters — it is **false**, here, at a real
one.  This is why `ctorConstsCR_wf_of_substC'` (the defeq bridge) exists. -/
theorem ntreeNode_substC_ne_typeR :
    (ntreeNode.type ntreeAux 0).substC ntreeSubst ≠ ntreeNode.typeR ntreeAux ntreeRestore 0 := by
  decide

/-- **…and the restoration is its contractum**, at the same position and nowhere else. -/
theorem ntreeNode_typeR_reduct :
    ntreeNode.typeR ntreeAux ntreeRestore 0
      = .forallE (.sort (.succ (.param 0)))
          (.forallE (.bvar 0)
            (.forallE (ntreeBody.inst (.bvar 1))
              (.app (.const ``NTree [.param 0]) (.bvar 2)))) := rfl

/-! ### `List`'s own block is well formed

`NestedHead.lean` states every `NTree` result over an *abstract* `env₁` given by
`VEnv.empty.addInduct' listDecl = some env₁`, and never proves `env₁.Ordered`.  This is the
missing fact — the analogue of `pfnDecl_WF` for the parameterised witness.  Unlike `pfnDecl`,
`listDecl` has a **recursive** field, so `VIndField.WF.pos` is reached in its `some r` branch
and every one of its nine clauses is discharged. -/

theorem list_const_staged {env₁ : VEnv} (h : VEnv.empty.addIndTypes listDecl = some env₁) :
    env₁.constants ``List = some ⟨1, listType.type⟩ :=
  VEnv.addConstList_constants h (``List, ⟨1, listType.type⟩) (by exact List.Mem.head _)

theorem listDecl_WF : listDecl.WF VEnv.empty where
  types_ne := by simp [listDecl]
  params := ⟨trivial, _, by type_tac⟩
  types := by
    intro T hT
    simp only [listDecl, List.mem_cons, List.not_mem_nil, or_false] at hT
    subst hT
    exact { indices := ⟨trivial, _, by type_tac⟩, isType := ⟨_, by type_tac⟩,
            canon := ⟨_, by type_tac⟩ }
  ctors := by
    intro env₁ hs j T hT C hC
    have hList := list_const_staged hs
    match j, hT with
    | 0, hT =>
      simp only [listDecl] at hT
      cases hT
      simp only [listType, List.mem_cons, List.not_mem_nil, or_false] at hC
      obtain rfl | rfl := hC
      · exact { params_len := rfl, params_eq := .succ .zero (by type_tac), fields := nofun,
                args_len := rfl, args_fresh := nofun, args_ty := .nil, result := by type_tac }
      · refine { params_len := rfl, params_eq := .succ .zero (by type_tac), fields := ?_,
                 args_len := rfl, args_fresh := nofun, args_ty := .nil, result := by type_tac }
        intro i F hF
        match i, hF with
        | 0, hF =>
          simp only [listCons, List.getElem?_cons_zero, Option.some.injEq] at hF
          subst hF
          exact { hasType := by type_tac
                  level := fun ls => by simp [VLevel.eval, listDecl, Lean.Nat.imax]
                  binders_indep := nofun
                  pos := ⟨.bvar 0, by simp [VInductDecl'.NoBlock, VExpr.NoConsts],
                          _, by type_tac⟩ }
        | 1, hF =>
          simp only [listCons, List.getElem?_cons_succ, List.getElem?_cons_zero,
            Option.some.injEq] at hF
          subst hF
          refine { hasType := by type_tac
                   level := fun ls => by simp [VLevel.eval, listDecl, Lean.Nat.imax]
                   binders_indep := ?_
                   pos := ⟨by decide, rfl, nofun, nofun,
                           ⟨⟨trivial, _, by type_tac⟩, _, by type_tac⟩, by type_tac,
                           fun T' hT' => by cases hT'; exact .nil, _, by type_tac⟩ }
          rintro r hr
          cases hr
          rintro i' t F' - - - k B hB
          exact absurd hB nofun
        | (_ + 2), hF => simp [listCons] at hF
  isLE := fun _ => .inl (by simp [VLevel.IsNeverZero, VLevel.eval, listDecl])

/-- …hence the history environment of the `NTree` step really is `Ordered`. -/
theorem listEnv_ordered {env₁ : VEnv} (h : VEnv.empty.addInduct' listDecl = some env₁) :
    env₁.Ordered :=
  VInductDecl'.addInduct'_ordered_final .empty listDecl_WF h

section
variable {env₁ env₂ env₃ : VEnv}
variable (h : VEnv.empty.addInduct' listDecl = some env₁) (henv₁ : env₁.Ordered)
variable (h₂ : env₁.addIndTypes ntreeAux = some env₂)
variable (h₃ : env₁.addConstList (ntreeAux.typeConstsC ntreeK) = some env₃)

include h in
theorem ntreeSubst_fresh : ntreeSubst.FreshIn env₁ := by
  intro c ci hc
  cases hn : ntreeSubst c with
  | none => rfl
  | some t =>
    have hce : c = `_nested.List_1 := by
      by_cases he : c = `_nested.List_1
      · exact he
      · rw [ntreeSubst_of_ne he] at hn; exact absurd hn nofun
    subst hce
    rw [VEnv.addInduct'_constants_of_not_mem h (by decide)] at hc
    exact absurd hc nofun

include h₃ in
theorem ntree_const₃ : env₃.constants ``NTree
    = some ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩ :=
  VEnv.addConstList_constants h₃
    (``NTree, ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩)
    (by exact List.Mem.head _)

include h h₃ in
theorem list_const₃ : env₃.constants ``List = some ⟨1, listType.type⟩ :=
  (VEnv.addConstList_le h₃).constants (list_const h)

include h h₃ in
/-- The `val` clause, by hand: the value is a lambda over a sort with a constant-headed
body, and both `sortDF` and `constDF` are already congruences for `≈`, so the two level
instantiations are related without any general level-congruence theorem. -/
theorem ntreeVal_val {Γ : List VExpr} {ls ls' : List VLevel}
    (hls : ∀ l ∈ ls, l.WF 1) (hls' : ∀ l ∈ ls', l.WF 1)
    (heq : List.Forall₂ (· ≈ ·) ls ls') (hlen : ls.length = 1) :
    env₃.IsDefEq 1 Γ (ntreeVal.instL ls) (ntreeVal.instL ls')
      ((VExpr.forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))).instL ls) := by
  match ls, hlen with
  | [l], _ =>
  cases heq with | cons hl heq' =>
  cases heq' with | nil =>
  rename_i l'
  have hlw : l.WF 1 := hls _ List.mem_cons_self
  have hlw' : l'.WF 1 := hls' _ List.mem_cons_self
  have hL := list_const₃ h h₃
  have hN := ntree_const₃ h₃
  show env₃.IsDefEq 1 Γ
    (.lam (.sort (.succ l)) (.app (.const ``List [l]) (.app (.const ``NTree [l]) (.bvar 0))))
    (.lam (.sort (.succ l')) (.app (.const ``List [l']) (.app (.const ``NTree [l']) (.bvar 0))))
    (.forallE (.sort (.succ l)) (.sort (.succ l)))
  refine VEnv.IsDefEq.lamDF (.sortDF hlw hlw' (VLevel.succ_congr hl)) ?_
  refine VEnv.IsDefEq.appDF (A := .sort (.succ l)) (B := .sort (.succ l)) ?_ ?_
  · exact .constDF hL (by simpa using hlw) (by simpa using hlw') rfl (.cons hl .nil)
  · refine VEnv.IsDefEq.appDF (A := .sort (.succ l)) (B := .sort (.succ l)) ?_
      (.bvar (by exact .zero))
    exact .constDF hN (by simpa using hlw) (by simpa using hlw') rfl (.cons hl .nil)

include h henv₁ h₂ h₃ in
/-- **The substitution, through the general builder.**  `CSubst.one_WF_of_hasType`
(`Theory/Typing/ConstSubst.lean`) asks only that the value *has the constant's type*: the
`≈`-congruence that `ntreeVal_val` establishes by hand is `VEnv.IsDefEq.instL_r`, and is no
longer a per-witness obligation.  `ntreeVal_val` is kept above as the hand computation it
supersedes. -/
theorem ntreeSubst_WF : ntreeSubst.WF env₂ env₃ 1 := by
  have hfresh := ntreeSubst_fresh h
  have henv₃ : env₃.Ordered :=
    VEnv.addConstList_ordered henv₁ (VEnv.addInductR_typeConstsC_wf (ntreeAux_WF h)) h₃
  have hL := list_const₃ h h₃
  have hN := ntree_const₃ h₃
  refine CSubst.one_WF_of_hasType (U := 1) (ci := ⟨1, _⟩) henv₃
    ⟨trivial, trivial, trivial, Nat.zero_lt_one⟩
    (nlist_const_staged h h₂) ⟨trivial, trivial⟩ (by type_tac) ?_ ?_
  · intro c' ci' hne hc'
    by_cases hN : c' = ``NTree
    · subst hN
      rw [ntree_const_staged h h₂] at hc'; cases hc'
      exact ⟨ntree_const₃ h₃, trivial, trivial⟩
    · have hmem : c' ∉ (ntreeAux.typeConsts.map (·.1)) := by
        show c' ∉ [``NTree, `_nested.List_1]
        simp [hN, hne]
      rw [VEnv.addConstList_constants_of_not_mem h₂ hmem] at hc'
      refine ⟨?_, henv₁.noCSubstC hfresh hc'⟩
      have hmem₃ : c' ∉ ((ntreeAux.typeConstsC ntreeK).map (·.1)) := by
        show c' ∉ [``NTree]
        simp [hN]
      rw [VEnv.addConstList_constants_of_not_mem h₃ hmem₃]; exact hc'
  · intro df hdf
    rw [VEnv.addConstList_defeqs h₂] at hdf
    exact ⟨(VEnv.addConstList_defeqs h₃) ▸ hdf, henv₁.noCSubstD hfresh hdf⟩

include h henv₁ h₃ in
/-- **The β-step, absorbed.**  This is the half `VExpr.substC` cannot do, and the only half
that is not already in `Theory/Typing/ConstSubst.lean`. -/
theorem ntreeNode_beta_bridge
    (H : env₃.IsType 1 [] ((ntreeNode.type ntreeAux 0).substC ntreeSubst)) :
    env₃.IsType 1 [] (ntreeNode.typeR ntreeAux ntreeRestore 0) := by
  have henv₃ : env₃.Ordered :=
    VEnv.addConstList_ordered henv₁ (VEnv.addInductR_typeConstsC_wf (ntreeAux_WF h)) h₃
  have hL := list_const₃ h h₃
  have hN := ntree_const₃ h₃
  rw [ntreeNode_substC_redex] at H
  obtain ⟨hP0, H1⟩ := H.forallE_inv henv₃
  obtain ⟨hP1, H2⟩ := H1.forallE_inv henv₃
  have hbeta : env₃.IsDefEq 1 [.bvar 0, .sort (.succ (.param 0))]
      (.app ntreeVal (.bvar 1)) (ntreeBody.inst (.bvar 1)) (.sort (.succ (.param 0))) := by
    refine VEnv.IsDefEq.beta (A := .sort (.succ (.param 0))) (B := .sort (.succ (.param 0)))
      ?_ ?_ <;> type_tac
  rw [ntreeNode_typeR_reduct]
  exact VEnv.IsType.forallE hP0 (VEnv.IsType.forallE hP1 (H2.forallE_congr henv₃ hbeta))

include h henv₁ h₂ h₃ in
/-- **Obligation (A) at the parameterised nested witness, through the general reduction.**

`VEnv.ctorConstsCR_wf_of_substC'` is what is used, not the bespoke bridge: the block-specific
input is exactly one `IsDefEq.beta`, and the two unchanged telescope entries cost nothing
because of `TeleDefEq.rfl`.  `ntreeNode_beta_bridge` above is the same step done by hand, kept
as the measurement it was. -/
theorem ntreeAux_ctorConstsCR_wf :
    ∀ c ∈ ntreeAux.ctorConstsCR ntreeRestore ntreeK, VConstant.WF env₃ c.2 := by
  have henv₂ : env₂.Ordered :=
    VInductDecl'.addIndTypes_ordered henv₁ (ntreeAux_WF h) h₂
  have henv₃ : env₃.Ordered :=
    VEnv.addConstList_ordered henv₁ (VEnv.addInductR_typeConstsC_wf (ntreeAux_WF h)) h₃
  have hL := list_const₃ h h₃
  have hN := ntree_const₃ h₃
  refine VEnv.ctorConstsCR_wf_of_substC' (ntreeAux_WF h) h₂ henv₂ henv₃
    (ntreeSubst_WF h henv₁ h₂ h₃) ?_
  rintro j T C hT hK hC
  match j, hT with
  | 0, hT =>
    cases hT
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
    subst hC
    refine ⟨.succ (.param 0), .rfl (.rfl (.cons (u := .succ (.param 0)) ?_ .nil)),
      by type_tac⟩
    refine VEnv.IsDefEq.beta (A := .sort (.succ (.param 0))) (B := .sort (.succ (.param 0)))
      ?_ ?_ <;> type_tac
  | 1, hT =>
    cases hT
    exact absurd (by decide) hK
  | (_ + 2), hT => simp [ntreeAux] at hT

end

/-! ## …with no hypotheses left, at the parameterised witness too

`listDecl_WF` makes the `NTree` development unconditional exactly the way `pfnDecl_WF` makes
the `NFn` one unconditional. -/

theorem ntree_fresh' {env₁ : VEnv} (h : VEnv.empty.addInduct' listDecl = some env₁)
    (n : Name) (hn : n ∈ [``NTree, `_nested.List_1]) : env₁.constants n = none := by
  rw [VEnv.addInduct'_constants_of_not_mem h (by revert hn; revert n; decide)]
  rfl

theorem ntreeAux_staged_exists {env₁ : VEnv} (h : VEnv.empty.addInduct' listDecl = some env₁) :
    ∃ env₂, env₁.addIndTypes ntreeAux = some env₂ :=
  VEnv.addConstList_eq_some_iff.2 ⟨fun n hn => ntree_fresh' h n hn, by decide⟩

theorem ntreeAux_declared_exists {env₁ : VEnv}
    (h : VEnv.empty.addInduct' listDecl = some env₁) :
    ∃ env₃, env₁.addConstList (ntreeAux.typeConstsC ntreeK) = some env₃ :=
  VEnv.addConstList_eq_some_iff.2
    ⟨fun n hn => ntree_fresh' h n (by revert hn; revert n; decide), by decide⟩

/-- **Obligation (A) at the `NTree`/`List` nested witness, unconditionally.**  This is the
parameterised counterpart of `nfnAux_obligationA`: one constant substitution and one β-step,
over a history environment now known to be `Ordered`. -/
theorem ntreeAux_obligationA :
    ∃ env₁ env₂ env₃ : VEnv, VEnv.empty.addInduct' listDecl = some env₁ ∧
      env₁.addIndTypes ntreeAux = some env₂ ∧
      env₁.addConstList (ntreeAux.typeConstsC ntreeK) = some env₃ ∧
      ∀ c ∈ ntreeAux.ctorConstsCR ntreeRestore ntreeK, VConstant.WF env₃ c.2 := by
  obtain ⟨env₁, h⟩ : ∃ e, VEnv.empty.addInduct' listDecl = some e := ⟨_, rfl⟩
  obtain ⟨env₂, h₂⟩ := ntreeAux_staged_exists h
  obtain ⟨env₃, h₃⟩ := ntreeAux_declared_exists h
  exact ⟨env₁, env₂, env₃, h, h₂, h₃,
    ntreeAux_ctorConstsCR_wf h (listEnv_ordered h) h₂ h₃⟩

/-! ## The whole restoration is one constant substitution

`VEnv.addInductR_ordered'` leaves three obligations, **(A)** the declared constructors,
**(B)** the renamed recursors and **(C)** the restored ι-rules.  All three are the *same*
substitution: extend `nfnSubst` to the auxiliary block's constructor and recursor names as
well, and every restored construction is the stored one substituted — `rfl`, below.

So the nested step is not three separate soundness statements.  It is one constant
substitution, applied at three consecutive staging environments, on top of the facts
`addInduct'_ordered_final` already proves for the *non-nested* block. -/

/-- `_nested.PFn_1.mk ↦ PFn.mk NFn`. -/
def nfnValMk : VExpr := .app (.const ``PFn.mk []) (.const ``NFn [])

/-- `_nested.PFn_1.rec ↦ NFn.rec_1` — `mkAuxRecNameMap`'s renaming, as a substitution. -/
def nfnValRec : VExpr := .const ``NFn.rec_1 [.param 0]

/-- The restoration of `nfnAux`, in full, as a constant substitution. -/
def nfnSubstAll : CSubst := fun n =>
  if n = `_nested.PFn_1 then some nfnVal
  else if n = `_nested.PFn_1.mk then some nfnValMk
  else if n = `_nested.PFn_1.rec then some nfnValRec
  else none

theorem nfnSubstAll_1 : nfnSubstAll `_nested.PFn_1 = some nfnVal := rfl
theorem nfnSubstAll_2 : nfnSubstAll `_nested.PFn_1.mk = some nfnValMk := rfl
theorem nfnSubstAll_3 : nfnSubstAll `_nested.PFn_1.rec = some nfnValRec := rfl

/-- **(A)'s bridge, for the full substitution.** -/
theorem nfnNode_substCAll :
    (nfnNode.type nfnAux 0).substC nfnSubstAll = nfnNode.typeR nfnAux nfnRestore 0 := rfl

/-- **(B)'s bridge**: the recursor types, the user's and the renamed companion's. -/
theorem nfn_recType_substC_0 :
    (nfnAux.recType 0).substC nfnSubstAll = nfnAux.recTypeR nfnRestore 0 := rfl

theorem nfn_recType_substC_1 :
    (nfnAux.recType 1).substC nfnSubstAll = nfnAux.recTypeR nfnRestore 1 := rfl

/-- **(C)'s bridge**: every ι-rule the nested step emits — including the two keyed to
`List`/`PFn`'s own constructors — is a rule of the ordinary block, substituted. -/
theorem nfn_iotaRules_substC :
    nfnAux.iotaRules.map (·.substC nfnSubstAll) = nfnAux.iotaRulesR nfnRestore := rfl

theorem nfnSubstAll_closed : nfnSubstAll.Closed := by
  intro c t hct
  unfold nfnSubstAll at hct
  split at hct
  · cases hct; exact ⟨trivial, trivial⟩
  split at hct
  · cases hct; exact ⟨trivial, trivial⟩
  split at hct
  · cases hct; exact trivial
  · exact absurd hct nofun

theorem nfnSubstAll_ne {c : Name} (hn : nfnSubstAll c = none) :
    c ≠ `_nested.PFn_1 ∧ c ≠ `_nested.PFn_1.mk ∧ c ≠ `_nested.PFn_1.rec := by
  refine ⟨?_, ?_, ?_⟩ <;> rintro rfl
  · rw [nfnSubstAll_1] at hn; exact absurd hn nofun
  · rw [nfnSubstAll_2] at hn; exact absurd hn nofun
  · rw [nfnSubstAll_3] at hn; exact absurd hn nofun

section
variable {env₂ E₁ E₂ E₃ F₁ F₂ F₃ : VEnv}
variable (h : VEnv.empty.addInduct' pfnDecl = some env₂)
variable (hE₁ : env₂.addIndTypes nfnAux = some E₁)
variable (hE₂ : E₁.addIndCtors nfnAux = some E₂)
variable (hE₃ : E₂.addIndRecs nfnAux = some E₃)
variable (hF₁ : env₂.addConstList (nfnAux.typeConstsC nfnK) = some F₁)
variable (hF₂ : F₁.addConstList (nfnAux.ctorConstsCR nfnRestore nfnK) = some F₂)
variable (hF₃ : F₂.addConstList (nfnAux.recConstsR nfnRestore nfnK) = some F₃)

include h in
theorem nfnSubstAll_fresh : nfnSubstAll.FreshIn env₂ := by
  intro c ci hc
  cases hn : nfnSubstAll c with
  | none => rfl
  | some t =>
    exfalso
    revert hn
    unfold nfnSubstAll
    split
    · rename_i he; subst he
      rw [VEnv.addInduct'_constants_of_not_mem h (by decide)] at hc; exact absurd hc nofun
    split
    · rename_i he; subst he
      rw [VEnv.addInduct'_constants_of_not_mem h (by decide)] at hc; exact absurd hc nofun
    split
    · rename_i he; subst he
      rw [VEnv.addInduct'_constants_of_not_mem h (by decide)] at hc; exact absurd hc nofun
    · exact nofun

/-! ### The constants of the two chains -/

include hF₁ in
theorem nfnF₁_nfn : F₁.constants ``NFn = some ⟨0, .sort (.succ .zero)⟩ :=
  VEnv.addConstList_constants hF₁ (``NFn, ⟨0, .sort (.succ .zero)⟩) (by exact List.Mem.head _)

include hF₂ in
theorem nfnF₂_node : F₂.constants ``NFn.node
    = some ⟨0, nfnNode.typeR nfnAux nfnRestore 0⟩ :=
  VEnv.addConstList_constants hF₂ (``NFn.node, ⟨0, nfnNode.typeR nfnAux nfnRestore 0⟩)
    (by exact List.Mem.head _)

include hF₃ in
theorem nfnF₃_rec1 : F₃.constants ``NFn.rec_1
    = some ⟨1, nfnAux.recTypeR nfnRestore 1⟩ :=
  VEnv.addConstList_constants hF₃ (``NFn.rec_1, ⟨1, nfnAux.recTypeR nfnRestore 1⟩)
    (by exact List.Mem.tail _ (List.Mem.head _))

/-! ### Stage (B): the recursor constants -/

include h hE₁ hE₂ in
/-- The **non-nested** recursor obligation, at the auxiliary block.  This is
`VInductDecl'.addInduct'_ordered'`'s inner argument, which is not exposed as a lemma. -/
theorem nfn_recConsts_wf : ∀ c ∈ nfnAux.recConsts, VConstant.WF E₂ c.2 := by
  intro c hc
  have henv₂ := pfnEnv_ordered h
  have o1 := VInductDecl'.addIndTypes_ordered henv₂ nfnAux_WF hE₁
  have o2 := VInductDecl'.addIndCtors_ordered o1 nfnAux_WF hE₁ hE₂
  have hR : nfnAux.RecCtx E₂ := nfnAux_WF.recCtx hE₁ hE₂ VEnv.LE.rfl o2
  simp only [VInductDecl'.recConsts, List.mem_map] at hc
  obtain ⟨⟨T, j⟩, hTj, rfl⟩ := hc
  have hT : nfnAux.types[j]? = some T := List.mk_mem_zipIdx_iff_getElem?.1 hTj
  have hj : j < nfnAux.nm := by
    rcases Nat.lt_or_ge j nfnAux.types.length with hlt | hle
    · exact hlt
    · rw [List.getElem?_eq_none hle] at hT; exact absurd hT (by simp)
  exact VInductDecl'.recType_isType hR hT hj (VInductDecl'.onCtxMinors hR)

include h hE₁ hE₂ hF₁ hF₂ in
theorem nfnF₂_ordered : F₂.Ordered := by
  have henv₂ := pfnEnv_ordered h
  have o1 := VEnv.addConstList_ordered henv₂
    (VEnv.addInductR_typeConstsC_wf nfnAux_WF) hF₁
  exact VEnv.addConstList_ordered o1
    (fun c hc => by
      have := nfnAux_ctorConstsCR_wf h henv₂ hE₁ hF₁ c hc
      exact this) hF₂

include h hF₁ hF₂ in
theorem nfnF₂_pfn : F₂.constants ``PFn = some ⟨0, pfnType.type⟩ :=
  (VEnv.addConstList_le hF₂).constants ((VEnv.addConstList_le hF₁).constants (pfn_const h))

include h hF₁ hF₂ in
theorem nfnF₂_pfnMk : F₂.constants ``PFn.mk = some ⟨0, pfnMk.type pfnDecl 0⟩ :=
  (VEnv.addConstList_le hF₂).constants ((VEnv.addConstList_le hF₁).constants (pfnMk_const h))

include hF₁ hF₂ in
theorem nfnF₂_nfn : F₂.constants ``NFn = some ⟨0, .sort (.succ .zero)⟩ :=
  (VEnv.addConstList_le hF₂).constants (nfnF₁_nfn hF₁)

include h hE₁ hE₂ hF₁ hF₂ in
/-- **The substitution, at the constructor stage.** -/
theorem nfnSubstAll_WF₂ : nfnSubstAll.WF E₂ F₂ 1 := by
  have henv₂ := pfnEnv_ordered h
  have hfresh := nfnSubstAll_fresh h
  have hFo := nfnF₂_ordered h hE₁ hE₂ hF₁ hF₂
  have hPFn := nfnF₂_pfn h hF₁ hF₂
  have hPFnMk := nfnF₂_pfnMk h hF₁ hF₂
  have hNFn := nfnF₂_nfn hF₁ hF₂
  have hNode := nfnF₂_node hF₂
  refine ⟨nfnSubstAll_closed, ?_, ?_, ?_⟩
  · intro c' ci' hn hc'
    obtain ⟨hn1, hn2, -⟩ := nfnSubstAll_ne hn
    by_cases hN : c' = ``NFn
    · subst hN
      rw [(VEnv.addConstList_constants_of_not_mem hE₂
        (by show ``NFn ∉ [``NFn.node, `_nested.PFn_1.mk]; simp)), nfn_const_staged hE₁] at hc'
      cases hc'; exact hNFn
    by_cases hD : c' = ``NFn.node
    · subst hD
      rw [VEnv.addConstList_constants hE₂
        (``NFn.node, ⟨0, nfnNode.type nfnAux 0⟩) (by exact List.Mem.head _)] at hc'
      cases hc'; rw [nfnNode_substCAll]; exact hNode
    · have hm₂ : c' ∉ (nfnAux.ctorConsts.map (·.1)) := by
        show c' ∉ [``NFn.node, `_nested.PFn_1.mk]; simp [hD, hn2]
      have hm₁ : c' ∉ (nfnAux.typeConsts.map (·.1)) := by
        show c' ∉ [``NFn, `_nested.PFn_1]; simp [hN, hn1]
      rw [VEnv.addConstList_constants_of_not_mem hE₂ hm₂,
        VEnv.addConstList_constants_of_not_mem hE₁ hm₁] at hc'
      rw [(henv₂.noCSubstC hfresh hc').substC_eq]
      have hm₄ : c' ∉ ((nfnAux.ctorConstsCR nfnRestore nfnK).map (·.1)) := by
        show c' ∉ [``NFn.node]; simp [hD]
      have hm₃ : c' ∉ ((nfnAux.typeConstsC nfnK).map (·.1)) := by
        show c' ∉ [``NFn]; simp [hN]
      rw [VEnv.addConstList_constants_of_not_mem hF₂ hm₄,
        VEnv.addConstList_constants_of_not_mem hF₁ hm₃]
      exact hc'
  · intro df hdf
    rw [VEnv.addConstList_defeqs hE₂, VEnv.addConstList_defeqs hE₁] at hdf
    rw [(henv₂.noCSubstD hfresh hdf).substC_eq,
      VEnv.addConstList_defeqs hF₂, VEnv.addConstList_defeqs hF₁]
    exact hdf
  · intro c' t' ci' Γ ls ls' hσ hc'
    revert hσ hc'
    unfold nfnSubstAll
    split
    · rename_i he; subst he
      intro hσ hc'
      cases hσ
      rw [VEnv.addConstList_constants_of_not_mem hE₂
        (by show `_nested.PFn_1 ∉ [``NFn.node, `_nested.PFn_1.mk]; simp),
        pfnaux_const_staged hE₁] at hc'
      cases hc'
      exact CSubst.val_zero' hFo rfl rfl rfl (by type_tac)
    split
    · rename_i he; subst he
      intro hσ hc'
      cases hσ
      rw [VEnv.addConstList_constants hE₂
        (`_nested.PFn_1.mk, ⟨0, pfnAuxMk.type nfnAux 1⟩)
        (by exact List.Mem.tail _ (List.Mem.head _))] at hc'
      cases hc'
      exact CSubst.val_zero' hFo rfl rfl rfl (by type_tac)
    split
    · rename_i he; subst he
      intro hσ hc'
      exfalso
      rw [VEnv.addConstList_constants_of_not_mem hE₂
        (by show `_nested.PFn_1.rec ∉ [``NFn.node, `_nested.PFn_1.mk]; simp),
        VEnv.addConstList_constants_of_not_mem hE₁
        (by show `_nested.PFn_1.rec ∉ [``NFn, `_nested.PFn_1]; simp),
        VEnv.addInduct'_constants_of_not_mem h (by decide)] at hc'
      exact absurd hc' nofun
    · exact fun hσ => absurd hσ nofun

include h hE₁ hE₂ hF₁ hF₂ in
/-- **Obligation (B), discharged at the witness.** -/
theorem nfnAux_recConstsR_wf :
    ∀ c ∈ nfnAux.recConstsR nfnRestore nfnK, VConstant.WF F₂ c.2 := by
  have hσ := nfnSubstAll_WF₂ h hE₁ hE₂ hF₁ hF₂
  have hsrc := nfn_recConsts_wf h hE₁ hE₂
  have h0 := (hsrc _ (by exact List.Mem.head _)).substC (ci := ⟨1, nfnAux.recType 0⟩) hσ
  have h1 := (hsrc _ (by exact List.Mem.tail _ (List.Mem.head _))).substC
    (ci := ⟨1, nfnAux.recType 1⟩) hσ
  rw [nfn_recType_substC_0] at h0
  rw [nfn_recType_substC_1] at h1
  intro c hc
  have hl : nfnAux.recConstsR nfnRestore nfnK
      = [(``NFn.rec, ⟨1, nfnAux.recTypeR nfnRestore 0⟩),
         (``NFn.rec_1, ⟨1, nfnAux.recTypeR nfnRestore 1⟩)] := rfl
  rw [hl] at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  obtain rfl | rfl := hc
  · exact h0
  · exact h1

end

/-! ### Stage (C): the ι-rules -/

theorem nfn_iotaRules_uvars : ∀ df ∈ nfnAux.iotaRules, df.uvars = 1 := by decide

section
variable {env₂ E₁ E₂ E₃ F₁ F₂ F₃ : VEnv}
variable (h : VEnv.empty.addInduct' pfnDecl = some env₂)
variable (hE₁ : env₂.addIndTypes nfnAux = some E₁)
variable (hE₂ : E₁.addIndCtors nfnAux = some E₂)
variable (hE₃ : E₂.addIndRecs nfnAux = some E₃)
variable (hF₁ : env₂.addConstList (nfnAux.typeConstsC nfnK) = some F₁)
variable (hF₂ : F₁.addConstList (nfnAux.ctorConstsCR nfnRestore nfnK) = some F₂)
variable (hF₃ : F₂.addConstList (nfnAux.recConstsR nfnRestore nfnK) = some F₃)

include h hE₁ hE₂ hF₁ hF₂ hF₃ in
theorem nfnF₃_ordered : F₃.Ordered :=
  VEnv.addConstList_ordered (nfnF₂_ordered h hE₁ hE₂ hF₁ hF₂)
    (fun c hc => nfnAux_recConstsR_wf h hE₁ hE₂ hF₁ hF₂ c hc) hF₃

include h hE₁ hE₂ hE₃ hF₁ hF₂ hF₃ in
/-- **The substitution, at the recursor stage.** -/
theorem nfnSubstAll_WF₃ : nfnSubstAll.WF E₃ F₃ 1 := by
  have hσ₂ := nfnSubstAll_WF₂ h hE₁ hE₂ hF₁ hF₂
  have hFo := nfnF₃_ordered h hE₁ hE₂ hF₁ hF₂ hF₃
  have hle := VEnv.addConstList_le hF₃
  have hPFn := hle.constants (nfnF₂_pfn h hF₁ hF₂)
  have hPFnMk := hle.constants (nfnF₂_pfnMk h hF₁ hF₂)
  have hNFn := hle.constants (nfnF₂_nfn hF₁ hF₂)
  have hRec1 := nfnF₃_rec1 hF₃
  refine ⟨nfnSubstAll_closed, ?_, ?_, ?_⟩
  · intro c' ci' hn hc'
    obtain ⟨-, -, hn3⟩ := nfnSubstAll_ne hn
    by_cases hR : c' = ``NFn.rec
    · subst hR
      rw [VEnv.addConstList_constants hE₃
        (``NFn.rec, ⟨1, nfnAux.recType 0⟩) (by exact List.Mem.head _)] at hc'
      cases hc'
      rw [nfn_recType_substC_0]
      exact VEnv.addConstList_constants hF₃
        (``NFn.rec, ⟨1, nfnAux.recTypeR nfnRestore 0⟩) (by exact List.Mem.head _)
    · have hm : c' ∉ (nfnAux.recConsts.map (·.1)) := by
        show c' ∉ [``NFn.rec, `_nested.PFn_1.rec]; simp [hR, hn3]
      rw [VEnv.addConstList_constants_of_not_mem hE₃ hm] at hc'
      exact hle.constants (hσ₂.const hn hc')
  · intro df hdf
    rw [VEnv.addConstList_defeqs hE₃] at hdf
    exact hle.defeqs (hσ₂.defeq hdf)
  · intro c' t' ci' Γ ls ls' hσ hc'
    revert hσ hc'
    unfold nfnSubstAll
    split
    · rename_i he; subst he
      intro hσ hc'
      cases hσ
      rw [VEnv.addConstList_constants_of_not_mem hE₃
        (by show `_nested.PFn_1 ∉ [``NFn.rec, `_nested.PFn_1.rec]; simp),
        VEnv.addConstList_constants_of_not_mem hE₂
        (by show `_nested.PFn_1 ∉ [``NFn.node, `_nested.PFn_1.mk]; simp),
        pfnaux_const_staged hE₁] at hc'
      cases hc'
      exact CSubst.val_zero' hFo rfl rfl rfl (by type_tac)
    split
    · rename_i he; subst he
      intro hσ hc'
      cases hσ
      rw [VEnv.addConstList_constants_of_not_mem hE₃
        (by show `_nested.PFn_1.mk ∉ [``NFn.rec, `_nested.PFn_1.rec]; simp),
        VEnv.addConstList_constants hE₂
        (`_nested.PFn_1.mk, ⟨0, pfnAuxMk.type nfnAux 1⟩)
        (by exact List.Mem.tail _ (List.Mem.head _))] at hc'
      cases hc'
      exact CSubst.val_zero' hFo rfl rfl rfl (by type_tac)
    split
    · rename_i he; subst he
      intro hσ hc'
      cases hσ
      rw [VEnv.addConstList_constants hE₃
        (`_nested.PFn_1.rec, ⟨1, nfnAux.recType 1⟩)
        (by exact List.Mem.tail _ (List.Mem.head _))] at hc'
      cases hc'
      -- the one place a value has universe parameters; `val_of_hasType` handles it
      refine CSubst.val_of_hasType hFo ?_
      show F₃.HasType 1 [] nfnValRec ((nfnAux.recType 1).substC nfnSubstAll)
      rw [nfn_recType_substC_1]
      exact .constDF hRec1 (by simp [VLevel.WF]) (by simp [VLevel.WF]) rfl (.cons rfl .nil)
    · exact fun hσ => absurd hσ nofun

include h hE₁ hE₂ hE₃ hF₁ hF₂ hF₃ in
/-- **Obligation (C), discharged at the witness.**  Note what the substitution does here that
no environment weakening could: the companion's ι-rule is keyed to `PFn.mk`, a constant the
history already holds, and its right-hand side calls `NFn.rec_1`, a constant this step
declares under a name the auxiliary block never had. -/
theorem nfnAux_iotaRulesR_wf :
    ∀ df ∈ nfnAux.iotaRulesR nfnRestore, VDefEq.WF F₃ df := by
  have henv₂ := pfnEnv_ordered h
  have hσ := nfnSubstAll_WF₃ h hE₁ hE₂ hE₃ hF₁ hF₂ hF₃
  have hsrc : ∀ df ∈ nfnAux.iotaRules, VDefEq.WF E₃ df :=
    VInductDecl'.iotaRules_WF (nfnAux_WF.iotaCtx henv₂ hE₁ hE₂ hE₃)
  intro df hdf
  rw [← nfn_iotaRules_substC, List.mem_map] at hdf
  obtain ⟨df₀, hdf₀, rfl⟩ := hdf
  exact VDefEq.WF.substC (by rw [nfn_iotaRules_uvars df₀ hdf₀]; exact hσ) (hsrc df₀ hdf₀)

end

/-! ## The nested step preserves `Ordered`, at a real nested block

`VEnv.addInductR_ordered'` (`Theory/Inductive/NestedOrdered.lean`) says: given `OwnId`,
`D.WF env` and the three obligations, a nested declaration step preserves `VEnv.Ordered`.
All three are now theorems at `nfnAux`, so the conclusion is too. -/

theorem nfnAux_stages {env₂ : VEnv} (h : VEnv.empty.addInduct' pfnDecl = some env₂) :
    ∃ E₁ E₂ E₃, env₂.addIndTypes nfnAux = some E₁ ∧ E₁.addIndCtors nfnAux = some E₂ ∧
      E₂.addIndRecs nfnAux = some E₃ := by
  have : ∃ env', env₂.addInduct' nfnAux = some env' := by
    refine VEnv.addInduct'_eq_some_iff.2 ⟨fun n hn => ?_, by decide⟩
    have hn' : n ∈ [``NFn, `_nested.PFn_1, ``NFn.node, `_nested.PFn_1.mk,
        ``NFn.rec, `_nested.PFn_1.rec] := hn
    rw [VEnv.addInduct'_constants_of_not_mem h (by revert hn'; revert n; decide)]
    rfl
  obtain ⟨env', he⟩ := this
  obtain ⟨E₁, E₂, E₃, h1, h2, h3, -⟩ := VEnv.addInduct'_stages he
  exact ⟨E₁, E₂, E₃, h1, h2, h3⟩

theorem nfnAux_declaredR_exists {env₂ : VEnv}
    (h : VEnv.empty.addInduct' pfnDecl = some env₂) :
    ∃ F₁ F₂ F₃, env₂.addConstList (nfnAux.typeConstsC nfnK) = some F₁ ∧
      F₁.addConstList (nfnAux.ctorConstsCR nfnRestore nfnK) = some F₂ ∧
      F₂.addConstList (nfnAux.recConstsR nfnRestore nfnK) = some F₃ := by
  obtain ⟨env', he⟩ := nfnAux_admitted h
  rw [VEnv.addInductR, Option.map_eq_some_iff] at he
  obtain ⟨F₃, h1, -⟩ := he
  rw [VInductDecl'.allConstsCR, VEnv.addConstList_append, Option.bind_eq_some_iff] at h1
  obtain ⟨F₂, h12, h3⟩ := h1
  rw [VEnv.addConstList_append, Option.bind_eq_some_iff] at h12
  obtain ⟨F₁, h1, h2⟩ := h12
  exact ⟨F₁, F₂, F₃, h1, h2, h3⟩

/-- **The nested declaration step preserves `VEnv.Ordered`, at `NFn`/`PFn`.**

This is `VEnv.addInductR_ordered'` with all three of its open obligations supplied.  Every
one of them was a constant substitution away from a fact `addInduct'_ordered_final` already
proves for the ordinary block. -/
theorem nfnAux_addInductR_ordered :
    ∃ env₂ env', VEnv.empty.addInduct' pfnDecl = some env₂ ∧
      env₂.addInductR nfnAux nfnK nfnRestore = some env' ∧ env'.Ordered := by
  obtain ⟨env₂, h⟩ : ∃ e, VEnv.empty.addInduct' pfnDecl = some e := ⟨_, rfl⟩
  obtain ⟨env', he⟩ := nfnAux_admitted h
  obtain ⟨E₁, E₂, E₃, hE₁, hE₂, hE₃⟩ := nfnAux_stages h
  refine ⟨env₂, env', h, he, ?_⟩
  refine VEnv.addInductR_ordered' (pfnEnv_ordered h) nfnAux_WF nfnRestore_ownId
    (fun {F₁} hF₁ => ?_) (fun {F₁ F₂} hF₁ hF₂ => ?_) (fun {F₁ F₂ F₃} hF₁ hF₂ hF₃ => ?_) he
  · exact nfnAux_ctorConstsCR_wf h (pfnEnv_ordered h) hE₁ hF₁
  · exact nfnAux_recConstsR_wf h hE₁ hE₂ hF₁ hF₂
  · exact nfnAux_iotaRulesR_wf h hE₁ hE₂ hE₃ hF₁ hF₂ hF₃

/-! ## The general σ, at both witnesses

The three substitutions above were written out by hand.  `VIndRestore.csubst` builds them
from the restoration's five fields, and these are the checks that it builds *those* — not
something that merely resembles them.  Every equation below is by `funext` plus computation:
no hypothesis about the block enters. -/

/-- **The general type-entry substitution is `nfnSubst`.** -/
theorem nfn_csubstTy : nfnRestore.csubstTy nfnAux nfnK = nfnSubst := by
  funext n
  show List.lookup n [(`_nested.PFn_1, nfnVal)] = _
  rw [List.lookup_cons]
  by_cases h : n = `_nested.PFn_1
  · subst h; rfl
  · rw [show (n == `_nested.PFn_1) = false from beq_eq_false_iff_ne.2 h]
    exact (CSubst.one_of_ne h).symm

/-- **The general substitution is `nfnSubstAll`** — including the recursor rename, which is
`mkAuxRecNameMap`'s entry read off `R.recName`. -/
theorem nfn_csubst : nfnRestore.csubst nfnAux nfnK = nfnSubstAll := by
  funext n
  show List.lookup n [(`_nested.PFn_1, nfnVal), (`_nested.PFn_1.rec, nfnValRec),
    (`_nested.PFn_1.mk, nfnValMk)] = _
  by_cases h1 : n = `_nested.PFn_1
  · subst h1; rfl
  by_cases h2 : n = `_nested.PFn_1.mk
  · subst h2; rfl
  by_cases h3 : n = `_nested.PFn_1.rec
  · subst h3; rfl
  rw [List.lookup_cons, show (n == `_nested.PFn_1) = false from beq_eq_false_iff_ne.2 h1,
    List.lookup_cons, show (n == `_nested.PFn_1.rec) = false from beq_eq_false_iff_ne.2 h3,
    List.lookup_cons, show (n == `_nested.PFn_1.mk) = false from beq_eq_false_iff_ne.2 h2]
  show none = _
  rw [nfnSubstAll, if_neg h1, if_neg h2, if_neg h3]

/-- **The general type-entry substitution is `ntreeSubst`** — and here the value really is a
lambda, because `NTree` has a parameter.  `VIndRestore.tyVal`'s `mkLams` is that lambda. -/
theorem ntree_csubstTy : ntreeRestore.csubstTy ntreeAux ntreeK = ntreeSubst := by
  funext n
  show List.lookup n [(`_nested.List_1, ntreeVal)] = _
  rw [List.lookup_cons]
  by_cases h : n = `_nested.List_1
  · subst h; rfl
  · rw [show (n == `_nested.List_1) = false from beq_eq_false_iff_ne.2 h]
    exact (CSubst.one_of_ne h).symm

/-- **The domain is the companion members and nothing else.**  The block's *own* member is not
in σ's domain: under `VIndRestore.OwnId` an entry there would be an η-expansion, not the
identity, so `csubst` is guarded by `K` rather than by "is a block name". -/
theorem nfn_csubst_own_none : nfnRestore.csubst nfnAux nfnK ``NFn = none := rfl

theorem nfn_csubst_ownRec_none : nfnRestore.csubst nfnAux nfnK (Lean.mkRecName ``NFn) = none := rfl

theorem ntree_csubstTy_own_none : ntreeRestore.csubstTy ntreeAux ntreeK ``NTree = none := rfl

/-- …and the value at the companion member is the presented application, on the nose. -/
theorem ntree_csubst_ty_val :
    ntreeRestore.csubstTy ntreeAux ntreeK `_nested.List_1 = some ntreeVal := rfl

/-- The two closedness side conditions hold at both witnesses. -/
theorem nfn_csubst_closed : (nfnRestore.csubst nfnAux nfnK).Closed := by
  refine VIndRestore.csubst_closed nfnRestore nfnAux nfnK trivial ?_
  intro j a ha
  show a.ClosedN 0
  revert ha
  rw [show nfnRestore.tyArgs j = if j = 1 then [VExpr.const ``NFn []] else [] from rfl]
  split
  · intro h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h; subst h; trivial
  · intro h; simp at h

theorem ntree_csubstTy_closed : (ntreeRestore.csubstTy ntreeAux ntreeK).Closed := by
  refine VIndRestore.csubstTy_closed ntreeRestore ntreeAux ntreeK ⟨trivial, trivial⟩ ?_
  intro j a ha
  show a.ClosedN 1
  revert ha
  rw [show ntreeRestore.tyArgs j
      = if j = 1 then [VExpr.app (.const ``NTree [.param 0]) (.bvar 0)] else [VExpr.bvar 0]
    from rfl]
  split <;>
  · intro h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    subst h
    first
      | exact ⟨trivial, Nat.zero_lt_one⟩
      | exact Nat.zero_lt_one

end InductiveDeclExamples

/-! ## §B The `nfnSubstAll_WF` template does **not** instantiate at `np = 1` — `hσ` is FALSE there

`docs/handoff-iota-stored.md` §21/§25 and ledger row 132b record the residual of obligations
(B)/(C) at a parameterised block as *"instantiating the `nfnSubstAll_WF₂`/`₃` template at
`np = 1`, not new apparatus"*.  **That is refuted below.**  The template's *conclusion* —
`(R.csubst D K).WF E₂ F₂ U`, the shared hypothesis of `VEnv.recConstsR_wf_of_substC'`,
`recConstsR_wf_of_blocks`, `recConstsR_wf_of_entries` and (through `iotaRulesRS_wf_of_substC`)
of the strict (C) route — is **false** at `ntreeAux`, for every `U` and, more sharply, for
**every** constant substitution whatsoever.

The reason is one clause and it is not `val`, which is where every previous costing of this
corner looked:

* `CSubst.WF.const` demands, of every constant of `E₂` outside `σ`'s domain, that `F₂` hold it
  at `ci.type.substC σ`;
* the constant `NTree.node` is in `E₂` at `ntreeNode.type ntreeAux 0` and in `F₂` at
  `(ntreeNode.typeR ntreeAux ntreeRestore 0).substC (R.csubstTy …)`, because that is what
  `VInductDecl'.ctorConstsCR` declares;
* so `const` *is* the syntactic bridge `VEnv.ctorConstsCR_wf_of_substC` asks for as `hbridge`
  — and `ctorConstsCR_wf_of_substC'` exists precisely because that bridge is **false** above
  `D.np = 0` (`ntreeNode_substC_ne_typeR`, in this file since it was written).

So obligation (A) was given a defeq-tolerant bridge, and (B) was given one too (§A) — but (B)'
kept the **strict** `hσ`, which re-imposes (A)'s refuted syntactic equation through the back door.
(C)' *dropped* `hσ` altogether, for the reason §A's note gives, so what is refuted here is (B)'
and the **strict** (C) route `iotaRulesRS_wf_of_substC` (`ntree_csubst_WF₃_false`), not (C)'.
§A.1 shows the primed bridges are not vacuous *in `hbridge`*; this section shows (B)' is unusable
at `np ≥ 1` *in `hσ`*, at the staging pair its consumer `VEnv.addInductR_ordered'` fixes. -/

/-- **The obstruction, in its minimal form.**  `CSubst.WF`'s `const` clause is an *equation*
between what one environment holds and what the other holds substituted, so a single constant
carried at a definitionally-equal-but-different type refutes the whole substitution — whatever
else it does.  Everything in §B is this lemma plus a computation. -/
theorem VEnv.subst_WF_false_of_const_ne {E F : VEnv} {σ : CSubst} {U : Nat} {c : Name}
    {ci : VConstant} {A : VExpr}
    (hE : E.constants c = some ci) (hF : F.constants c = some ⟨ci.uvars, A⟩)
    (hdom : σ c = none) (hne : A ≠ ci.type.substC σ) : ¬ σ.WF E F U := by
  intro hσ
  have h := hσ.const hdom hE
  rw [hF] at h
  exact hne (by injection h with h; exact congrArg VConstant.type h)

/-- **The general obstruction.**  If a *declared* constructor's stored type is not literally
its restored type under the substitution, then no `σ` at all is well formed between the two
staging environments — because `CSubst.WF.const` at that constructor *is* that equation.

Nothing about `np` enters here: `np ≥ 1` is what makes `hne` true (one β-redex per parameter),
and `hne` is what makes the conclusion bite. -/
theorem VEnv.csubst_WF_staged_false {E₁ E₂ F₁ F₂ : VEnv} {D : VInductDecl'} {R : VIndRestore}
    {K : List Name} {σ : CSubst} {U j : Nat} {C : VIndCtor}
    (hE₂ : E₁.addIndCtors D = some E₂)
    (hF₂ : F₁.addConstList (D.ctorConstsCR R K) = some F₂)
    (hjC : (j, C) ∈ D.ctorsAll)
    (hK : (D.types.getD j default).name ∉ K)
    (hname : R.ctorName C.name = C.name)
    (hdom : σ C.name = none)
    (hne : (C.type D j).substC σ ≠ (C.typeR D R j).substC (R.csubstTy D K)) :
    ¬ σ.WF E₂ F₂ U := by
  intro hσ
  have hE : E₂.constants C.name = some ⟨D.uvars, C.type D j⟩ :=
    VEnv.addConstList_constants hE₂ (C.name, ⟨D.uvars, C.type D j⟩)
      (List.mem_map.2 ⟨(j, C), hjC, rfl⟩)
  have hF : F₂.constants C.name
      = some ⟨D.uvars, (C.typeR D R j).substC (R.csubstTy D K)⟩ := by
    have := VEnv.addConstList_constants hF₂
      (R.ctorName C.name, ⟨D.uvars, (C.typeR D R j).substC (R.csubstTy D K)⟩)
      (by rw [VInductDecl'.ctorConstsCR, List.mem_filterMap]
          exact ⟨(j, C), hjC, by simp only []; rw [if_neg hK]⟩)
    rwa [hname] at this
  exact VEnv.subst_WF_false_of_const_ne hE hF hdom (fun hh => hne hh.symm) hσ

/-! ## §C The repair, and why the other candidate repair is refuted

There are exactly two ways to make `const` satisfiable at `np ≥ 1`:

1. **change what the step declares** — let `ctorConstsCR` declare `(C.type D j).substC (R.csubst D K)`
   (the β-redex form) instead of `(C.typeR D R j).substC (R.csubstTy D K)`.  **Refuted**:
   `ntreeNode_typeR` anchors the current form against `type_of% @NTree.node`, i.e. against what
   Lean's own kernel declares, and `ntree_node_redex_ne_declared` below shows the redex form is
   *not* that.  This repair would trade obligation (B) for faithfulness, which is the wrong trade.
2. **weaken `const` to a definitional equation**, which is what obligation (A) already did to its
   own bridge (`ctorConstsCR_wf_of_substC'`).  That is `CSubst.WFD` below.

`CSubst.WFD` differs from `CSubst.WF` in one clause and one disjunct: `const` may present the
constant at *any* type `A`, provided either `A` is literally `ci.type.substC σ` (the old clause,
so `CSubst.WF.wfd` is a weakening and `WFD` inherits every instance `WF` has — in particular
`nfnSubstAll_WF₂.wfd` and `nfnSubstAll_WF₃.wfd` at `np = 0`) or `A` is definitionally equal to it
at every level instantiation.  `IsDefEq.substCD` is then the same induction as
`VEnv.IsDefEq.substC`, with `constDF` routed through one `defeqDF`; every other case is
byte-identical, which is the measurement that this is a *weakening* and not a new system.

`Theory/Typing/ConstSubst.lean` is another stream's file, so `WFD` lives here rather than beside
`CSubst.WF`.  If it survives, it belongs there. -/

/-- **`CSubst.WF` with a defeq-tolerant `const` clause.**  See §C. -/
structure CSubst.WFD (σ : CSubst) (env₀ env₁ : VEnv) (U : Nat) : Prop where
  /-- Every value is closed. -/
  closed : σ.Closed
  /-- Constants outside `σ`'s domain survive — at their substituted type, **or at any type
  definitionally equal to it**.  This is the one clause `CSubst.WF` states too strictly for a
  parameterised nested block (§B). -/
  const : ∀ {c ci}, σ c = none → env₀.constants c = some ci →
    ∃ A, env₁.constants c = some ⟨ci.uvars, A⟩ ∧
      (A = ci.type.substC σ ∨
        ∀ {Γ : List VExpr} {ls : List VLevel}, (∀ l ∈ ls, l.WF U) → ls.length = ci.uvars →
          ∃ v, env₁.IsDefEq U Γ (A.instL ls) ((ci.type.substC σ).instL ls) (.sort v))
  /-- Definitional equations survive, substituted. -/
  defeq : ∀ {df}, env₀.defeqs df → env₁.defeqs (df.substC σ)
  /-- A value inhabits the declared type of the constant it replaces. -/
  val : ∀ {c t ci Γ ls ls'}, σ c = some t → env₀.constants c = some ci →
    (∀ l ∈ ls, l.WF U) → (∀ l ∈ ls', l.WF U) → List.Forall₂ (· ≈ ·) ls ls' →
    ls.length = ci.uvars →
    env₁.IsDefEq U Γ (t.instL ls) (t.instL ls') ((ci.type.substC σ).instL ls)

/-- **`WFD` is a weakening**: every `CSubst.WF` is one, so `WFD` is inhabited wherever `WF` is —
`nfnSubstAll_WF₂` and `nfnSubstAll_WF₃` at `np = 0`, `ntreeSubst_WF` at the type stage. -/
theorem CSubst.WF.wfd {env₀ env₁ : VEnv} {σ : CSubst} {U : Nat} (h : σ.WF env₀ env₁ U) :
    σ.WFD env₀ env₁ U where
  closed := h.closed
  const hn hc := ⟨_, h.const hn hc, .inl rfl⟩
  defeq := h.defeq
  val := h.val

namespace VEnv

variable {env₀ env₁ : VEnv} {σ : CSubst}

/-- The `constDF` case: one `defeqDF` more than `VEnv.IsDefEq.substC_constDF`. -/
theorem IsDefEq.substCD_constDF (hσ : σ.WFD env₀ env₁ U)
    (h1 : env₀.constants c = some ci) (h2 : ∀ l ∈ ls, l.WF U) (h3 : ∀ l ∈ ls', l.WF U)
    (h4 : ls.length = ci.uvars) (h5 : List.Forall₂ (· ≈ ·) ls ls') :
    env₁.IsDefEq U Γ ((VExpr.const c ls).substC σ) ((VExpr.const c ls').substC σ)
      ((ci.type.instL ls).substC σ) := by
  rw [VExpr.substC_instL]
  cases h : σ c with
  | none =>
    rw [VExpr.substC_const_none h, VExpr.substC_const_none h]
    obtain ⟨A, hA, hor⟩ := hσ.const h h1
    match hor with
    | .inl he => subst he; exact .constDF hA h2 h3 h4 h5
    | .inr hd =>
      obtain ⟨v, hv⟩ := hd (Γ := Γ) h2 h4
      exact hv.defeqDF (.constDF hA h2 h3 h4 h5)
  | some t =>
    rw [VExpr.substC_const_some h, VExpr.substC_const_some h]
    exact hσ.val h h1 h2 h3 h5 h4

/-- The `extra` case, which reads only `defeq` and so is unchanged. -/
theorem IsDefEq.substCD_extra (hσ : σ.WFD env₀ env₁ U)
    (h1 : env₀.defeqs df) (h2 : ∀ l ∈ ls, l.WF U) (h3 : ls.length = df.uvars) :
    env₁.IsDefEq U Γ ((df.lhs.instL ls).substC σ) ((df.rhs.instL ls).substC σ)
      ((df.type.instL ls).substC σ) := by
  simp only [VExpr.substC_instL]
  exact .extra (hσ.defeq h1) h2 h3

/-- **Substitution of constants preserves typing, under the weakened hypothesis.**  The same
induction as `VEnv.IsDefEq.substC`; only `constDF` differs. -/
theorem IsDefEq.substCD (hσ : σ.WFD env₀ env₁ U) (H : env₀.IsDefEq U Γ e1 e2 A) :
    env₁.IsDefEq U (Γ.map (VExpr.substC · σ)) (e1.substC σ) (e2.substC σ) (A.substC σ) := by
  induction H with
  | bvar h => exact .bvar (h.substC hσ.closed)
  | symm _ ih => exact .symm ih
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  | constDF h1 h2 h3 h4 h5 => exact substCD_constDF hσ h1 h2 h3 h4 h5
  | appDF _ _ ih1 ih2 => rw [VExpr.substC_inst hσ.closed]; exact .appDF ih1 ih2
  | lamDF _ _ ih1 ih2 => exact .lamDF ih1 ih2
  | forallEDF _ _ ih1 ih2 => exact .forallEDF ih1 ih2
  | defeqDF _ _ ih1 ih2 => exact .defeqDF ih1 ih2
  | beta _ _ ih1 ih2 =>
    rw [VExpr.substC_inst hσ.closed, VExpr.substC_inst hσ.closed]; exact .beta ih1 ih2
  | eta _ ih =>
    rw [VExpr.substC_lam, VExpr.substC_app, VExpr.substC_lift hσ.closed]
    exact .eta ih
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel ih1 ih2 ih3
  | extra h1 h2 h3 => exact substCD_extra hσ h1 h2 h3

theorem HasType.substCD (hσ : σ.WFD env₀ env₁ U) (H : env₀.HasType U Γ e A) :
    env₁.HasType U (Γ.map (VExpr.substC · σ)) (e.substC σ) (A.substC σ) :=
  IsDefEq.substCD hσ H

theorem IsType.substCD (hσ : σ.WFD env₀ env₁ U) (H : env₀.IsType U Γ A) :
    env₁.IsType U (Γ.map (VExpr.substC · σ)) (A.substC σ) :=
  let ⟨_, h⟩ := H; ⟨_, h.substCD hσ⟩

end VEnv

theorem VConstant.WF.substCD {env₀ env₁ : VEnv} {σ : CSubst} {ci : VConstant}
    (hσ : σ.WFD env₀ env₁ ci.uvars) (H : ci.WF env₀) :
    VConstant.WF env₁ ⟨ci.uvars, ci.type.substC σ⟩ := by
  show env₁.IsType ci.uvars [] (ci.type.substC σ)
  simpa using VEnv.IsType.substCD hσ H

theorem VDefEq.WF.substCD {env₀ env₁ : VEnv} {σ : CSubst} {df : VDefEq}
    (hσ : σ.WFD env₀ env₁ df.uvars) (H : df.WF env₀) : (df.substC σ).WF env₁ :=
  ⟨by simpa using VEnv.HasType.substCD hσ H.1, by simpa using VEnv.HasType.substCD hσ H.2⟩

/-- **Obligation (B)'s `np`-free route, with `hσ` weakened to `WFD`.**  Identical to
`VEnv.recConstsR_wf_of_substC'` except for the hypothesis — which is the point: §B shows the
unweakened one is false at `np ≥ 1`, and `CSubst.WF.wfd` shows nothing is lost at `np = 0`.

`recConstsR_wf_of_blocks` and `recConstsR_wf_of_entries` (`Theory/Inductive/NestedTele.lean`)
factor through `recConstsR_wf_of_substC'` and would each acquire a `WFD` form the same way; they
are another file's to restate. -/
theorem VEnv.recConstsR_wf_of_substCD' {E₂ e₂ : VEnv} {D : VInductDecl'} {R : VIndRestore}
    {K : List Name} {σ : CSubst}
    (hsrc : ∀ c ∈ D.recConsts, VConstant.WF E₂ c.2)
    (hσ : σ.WFD E₂ e₂ D.recUvars) (he₂ : e₂.Ordered)
    (hbridge : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T →
      ∃ (As As' : List VExpr) (B B' : VExpr) (v : VLevel),
        (D.recType j).substC σ = VExpr.mkPi As B ∧
        (D.recTypeR R j).substC (R.csubst D K) = VExpr.mkPi As' B' ∧
        e₂.TeleDefEq D.recUvars [] As As' ∧
        e₂.IsDefEq D.recUvars As.reverse B B' (.sort v)) :
    ∀ c ∈ D.recConstsR R K, VConstant.WF e₂ c.2 := by
  intro c hc
  simp only [VInductDecl'.recConstsR, List.mem_map] at hc
  obtain ⟨⟨T, j⟩, hTj, rfl⟩ := hc
  have hT : D.types[j]? = some T := List.mk_mem_zipIdx_iff_getElem?.1 hTj
  have hs := (hsrc (Lean.mkRecName T.name, ⟨D.recUvars, D.recType j⟩)
    (by simp only [VInductDecl'.recConsts, List.mem_map]; exact ⟨(T, j), hTj, rfl⟩)).substCD hσ
  obtain ⟨As, As', B, B', v, hL, hRr, htele, hbody⟩ := hbridge j T hT
  refine (show ((D.recTypeR R j).substC (R.csubst D K)) = VExpr.mkPi As' B' from hRr) ▸ ?_
  exact VEnv.IsType.mkPi_congr' (v := v) he₂ htele (by simpa using hbody) (hL ▸ hs)

namespace InductiveDeclExamples

/-- The `const` clause's equation at `NTree.node`, refuted by computation.  This is
`ntreeNode_substC_ne_typeR` with the *full* substitution on the left and the type
`ctorConstsCR` really declares on the right — i.e. exactly the two sides `CSubst.WF.const`
identifies. -/
theorem ntree_const_clause_ne :
    (ntreeNode.type ntreeAux 0).substC (ntreeRestore.csubst ntreeAux ntreeK)
      ≠ (ntreeNode.typeR ntreeAux ntreeRestore 0).substC
          (ntreeRestore.csubstTy ntreeAux ntreeK) := by decide

/-- **…and no constant substitution can satisfy it**, which is the structural half: `substC`
replaces a constant in *head* position, so the third pi-domain of the stored type is
`.app t (.bvar 1)` for whatever `t` is chosen, while the declared one is
`.app (const List) (.app (const NTree) (.bvar 1))`.  Matching them would need `substC` to
re-associate an application, and it cannot.  So the failure is not "the wrong value was
picked". -/
theorem ntree_node_no_substC (σ : CSubst) :
    (ntreeNode.type ntreeAux 0).substC σ
      ≠ (ntreeNode.typeR ntreeAux ntreeRestore 0).substC
          (ntreeRestore.csubstTy ntreeAux ntreeK) := by
  intro h
  rw [show ntreeNode.type ntreeAux 0
      = .forallE (.sort (.succ (.param 0)))
        (.forallE (.bvar 0)
          (.forallE (.app (.const `_nested.List_1 [.param 0]) (.bvar 1))
            (.app (.const ``NTree [.param 0]) (.bvar 2)))) from rfl,
    show (ntreeNode.typeR ntreeAux ntreeRestore 0).substC
        (ntreeRestore.csubstTy ntreeAux ntreeK)
      = .forallE (.sort (.succ (.param 0)))
        (.forallE (.bvar 0)
          (.forallE (.app (.const ``List [.param 0]) (.app (.const ``NTree [.param 0]) (.bvar 1)))
            (.app (.const ``NTree [.param 0]) (.bvar 2)))) from rfl] at h
  simp only [VExpr.substC] at h
  injection h with _ h
  injection h with _ h
  injection h with h _
  injection h with _ h
  exact absurd h nofun

theorem ntree_node_mem : (0, ntreeNode) ∈ ntreeAux.ctorsAll := by
  rw [show ntreeAux.ctorsAll = [((0 : Nat), ntreeNode), (1, nlistNil), (1, nlistCons)] from rfl]
  exact List.Mem.head _

/-- **`hσ` is false at the parameterised witness.**  The `np = 1` counterpart of
`nfnSubstAll_WF₂` — and it is a *refutation*, not a gap: two staging equations are all it
takes.  `U` is unconstrained, so in particular `U = ntreeAux.recUvars = 2`, which is the
instance `VEnv.recConstsR_wf_of_entries` needs. -/
theorem ntree_csubst_WF₂_false {E₁ E₂ F₁ F₂ : VEnv} {U : Nat}
    (hE₂ : E₁.addIndCtors ntreeAux = some E₂)
    (hF₂ : F₁.addConstList (ntreeAux.ctorConstsCR ntreeRestore ntreeK) = some F₂) :
    ¬ (ntreeRestore.csubst ntreeAux ntreeK).WF E₂ F₂ U :=
  VEnv.csubst_WF_staged_false hE₂ hF₂ ntree_node_mem (by decide) rfl rfl
    ntree_const_clause_ne

/-- …and **for every substitution that leaves the declared constructor alone** — which is
every substitution the nested step could mean, since `NTree.node` is a constant this step
*declares* and `R.csubst` is guarded by `K`.  So obligation (B)'s `np`-free route is not
merely missing a witness at `ntreeAux`: `VEnv.recConstsR_wf_of_substC'`'s `hσ` cannot be
discharged at the staging pair by any such `σ`, however chosen. -/
theorem ntree_any_WF₂_false {E₁ E₂ F₁ F₂ : VEnv} {U : Nat} (σ : CSubst)
    (hdom : σ ``NTree.node = none)
    (hE₂ : E₁.addIndCtors ntreeAux = some E₂)
    (hF₂ : F₁.addConstList (ntreeAux.ctorConstsCR ntreeRestore ntreeK) = some F₂) :
    ¬ σ.WF E₂ F₂ U :=
  VEnv.csubst_WF_staged_false hE₂ hF₂ ntree_node_mem (by decide) rfl hdom
    (ntree_node_no_substC σ)

/-- **…and the same refutation at the ι-rule stage**, which is where the *strict* obligation-(C)
route (`VEnv.iotaRulesRS_wf_of_substC`) asks for `hσ`.  `NTree.node` is carried up both chains
unchanged, so the same disagreement refutes `σ.WF E₃ F₃` too.  (Obligation (C)'s *defeq-tolerant*
route `iotaRulesRS_wf_of_substC'` has **no** `hσ` at all — see §A's note on why `VDefEq.WF` cannot
keep one — so (C) is blocked only on its strict route, not on both.) -/
theorem ntree_csubst_WF₃_false {E₁ E₂ E₃ F₁ F₂ F₃ : VEnv} {U : Nat}
    (hE₂ : E₁.addIndCtors ntreeAux = some E₂)
    (hE₃ : E₂.addIndRecs ntreeAux = some E₃)
    (hF₂ : F₁.addConstList (ntreeAux.ctorConstsCR ntreeRestore ntreeK) = some F₂)
    (hF₃ : F₂.addConstList (ntreeAux.recConstsR ntreeRestore ntreeK) = some F₃) :
    ¬ (ntreeRestore.csubst ntreeAux ntreeK).WF E₃ F₃ U :=
  VEnv.subst_WF_false_of_const_ne
    ((VEnv.addConstList_le hE₃).constants
      (VEnv.addConstList_constants hE₂ (``NTree.node, ⟨1, ntreeNode.type ntreeAux 0⟩)
        (by exact List.Mem.head _)))
    ((VEnv.addConstList_le hF₃).constants
      (VEnv.addConstList_constants hF₂
        (``NTree.node, ⟨1, (ntreeNode.typeR ntreeAux ntreeRestore 0).substC
          (ntreeRestore.csubstTy ntreeAux ntreeK)⟩) (by exact List.Mem.head _)))
    rfl (fun hh => ntree_const_clause_ne hh.symm)

/-- The staging pair the refutation is about really exists — so `ntree_csubst_WF₂_false` is
not a statement about an empty configuration.  (`ntreeAux_staged_exists` /
`ntreeAux_declared_exists` give the first stage of each chain; these are the second.) -/
theorem ntree_stage₂_exists :
    ∃ (env₁ E₁ E₂ F₁ F₂ : VEnv), VEnv.empty.addInduct' listDecl = some env₁ ∧
      env₁.addIndTypes ntreeAux = some E₁ ∧ E₁.addIndCtors ntreeAux = some E₂ ∧
      env₁.addConstList (ntreeAux.typeConstsC ntreeK) = some F₁ ∧
      F₁.addConstList (ntreeAux.ctorConstsCR ntreeRestore ntreeK) = some F₂ := by
  obtain ⟨env₁, h⟩ : ∃ e, VEnv.empty.addInduct' listDecl = some e := ⟨_, rfl⟩
  have hfresh : ∀ n ∈ [``NTree, `_nested.List_1, ``NTree.node,
      `_nested.List_1.nil, `_nested.List_1.cons], env₁.constants n = none := by
    intro n hn
    rw [VEnv.addInduct'_constants_of_not_mem h (by revert hn; revert n; decide)]
    rfl
  obtain ⟨E₁, hE₁⟩ : ∃ e, env₁.addIndTypes ntreeAux = some e :=
    VEnv.addConstList_eq_some_iff.2
      ⟨fun n hn => hfresh n (by revert hn; revert n; decide), by decide⟩
  obtain ⟨F₁, hF₁⟩ : ∃ e, env₁.addConstList (ntreeAux.typeConstsC ntreeK) = some e :=
    VEnv.addConstList_eq_some_iff.2
      ⟨fun n hn => hfresh n (by revert hn; revert n; decide), by decide⟩
  obtain ⟨E₂, hE₂⟩ : ∃ e, E₁.addIndCtors ntreeAux = some e := by
    refine VEnv.addConstList_eq_some_iff.2 ⟨fun n hn => ?_, by decide⟩
    rw [VEnv.addConstList_constants_of_not_mem hE₁ (by revert hn; revert n; decide)]
    exact hfresh n (by revert hn; revert n; decide)
  obtain ⟨F₂, hF₂⟩ : ∃ e, F₁.addConstList (ntreeAux.ctorConstsCR ntreeRestore ntreeK) = some e := by
    refine VEnv.addConstList_eq_some_iff.2 ⟨fun n hn => ?_, by decide⟩
    rw [VEnv.addConstList_constants_of_not_mem hF₁ (by revert hn; revert n; decide)]
    exact hfresh n (by revert hn; revert n; decide)
  exact ⟨env₁, E₁, E₂, F₁, F₂, h, hE₁, hE₂, hF₁, hF₂⟩

/-! ## §D The repair, instantiated at `np = 1` — `hσ`'s corrected form, proved

§B refutes the template; §C states what replaces it.  This section supplies the instance, so that
`CSubst.WFD` is not a hypothesis nobody meets at the place `CSubst.WF` fails (ledger §5: *a bridge
nothing satisfies is not a bridge*).  Everything is at `ntreeAux`, `np = 1`, `uvars = 1`,
`recUvars = 2`, over the history environment `listDecl_WF` makes `Ordered`.

The four substituted names are `_nested.List_1` and its recursor and two constructors; the fourth
(`_nested.List_1.rec`) is not yet in `E₂`, exactly as `nfnSubstAll_WF₂`'s third split records at
`np = 0`, so its `val` obligation is discharged by `exfalso` there too. -/

/-- §D.1 The full substitution is closed at the parameterised block — `csubstTy`'s companion
(`ntree_csubstTy_closed`) for all four entries. -/
theorem ntree_csubst_closed : (ntreeRestore.csubst ntreeAux ntreeK).Closed := by
  refine VIndRestore.csubst_closed ntreeRestore ntreeAux ntreeK ⟨trivial, trivial⟩ ?_
  intro j a ha
  show a.ClosedN 1
  revert ha
  rw [show ntreeRestore.tyArgs j
      = if j = 1 then [VExpr.app (.const ``NTree [.param 0]) (.bvar 0)] else [VExpr.bvar 0]
    from rfl]
  split <;>
  · intro hh
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
    subst hh
    first
      | exact ⟨trivial, Nat.zero_lt_one⟩
      | exact Nat.zero_lt_one

/-- The domain, as four disequations — `nfnSubstAll_ne` one entry longer. -/
theorem ntree_csubst_ne {c : Name} (hn : ntreeRestore.csubst ntreeAux ntreeK c = none) :
    c ≠ `_nested.List_1 ∧ c ≠ `_nested.List_1.rec ∧
      c ≠ `_nested.List_1.nil ∧ c ≠ `_nested.List_1.cons := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rintro rfl <;> exact absurd hn nofun

/-- …and it is fresh in the history environment. -/
theorem ntree_csubst_fresh {env₁ : VEnv} (h : VEnv.empty.addInduct' listDecl = some env₁) :
    (ntreeRestore.csubst ntreeAux ntreeK).FreshIn env₁ := by
  intro c ci hc
  cases hn : ntreeRestore.csubst ntreeAux ntreeK c with
  | none => rfl
  | some t =>
    exfalso
    by_cases h1 : c = `_nested.List_1
    · subst h1
      rw [VEnv.addInduct'_constants_of_not_mem h (by decide)] at hc; exact absurd hc nofun
    by_cases h2 : c = `_nested.List_1.rec
    · subst h2
      rw [VEnv.addInduct'_constants_of_not_mem h (by decide)] at hc; exact absurd hc nofun
    by_cases h3 : c = `_nested.List_1.nil
    · subst h3
      rw [VEnv.addInduct'_constants_of_not_mem h (by decide)] at hc; exact absurd hc nofun
    by_cases h4 : c = `_nested.List_1.cons
    · subst h4
      rw [VEnv.addInduct'_constants_of_not_mem h (by decide)] at hc; exact absurd hc nofun
    · rw [show ntreeRestore.csubst ntreeAux ntreeK c = none from by
        show List.lookup c [(`_nested.List_1, _), (`_nested.List_1.rec, _),
          (`_nested.List_1.nil, _), (`_nested.List_1.cons, _)] = none
        rw [List.lookup_cons, show (c == `_nested.List_1) = false from beq_eq_false_iff_ne.2 h1,
          List.lookup_cons, show (c == `_nested.List_1.rec) = false from beq_eq_false_iff_ne.2 h2,
          List.lookup_cons, show (c == `_nested.List_1.nil) = false from beq_eq_false_iff_ne.2 h3,
          List.lookup_cons, show (c == `_nested.List_1.cons) = false from beq_eq_false_iff_ne.2 h4]
        rfl] at hn
      exact absurd hn nofun


/-- **§D.2 The datum `CSubst.WF` cannot hold and `CSubst.WFD` asks for.**  At `NTree.node` the
type `ctorConstsCR` declares and the type the substitution produces are **definitionally equal**
in `F₂`, at every level instantiation: one `IsDefEq.beta` under two `forallEDF`s.  Contrast
`ntree_node_no_substC`, which shows they are never *equal*.  This is the whole content of the
repair: obligation (A)'s β-step, moved into the substitution's own interface. -/
theorem ntree_node_const_defeq {F₂ : VEnv} {U : Nat} {l : VLevel}
    (hL : F₂.constants ``List = some ⟨1, listType.type⟩)
    (hN : F₂.constants ``NTree
      = some ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩)
    (hl : l.WF U) :
    ∃ v, F₂.IsDefEq U []
      (((ntreeNode.typeR ntreeAux ntreeRestore 0).substC
        (ntreeRestore.csubstTy ntreeAux ntreeK)).instL [l])
      (((ntreeNode.type ntreeAux 0).substC (ntreeRestore.csubst ntreeAux ntreeK)).instL [l])
      (.sort v) := by
  show ∃ v, F₂.IsDefEq U []
      (.forallE (.sort (.succ l))
        (.forallE (.bvar 0)
          (.forallE (.app (.const ``List [l]) (.app (.const ``NTree [l]) (.bvar 1)))
            (.app (.const ``NTree [l]) (.bvar 2)))))
      (.forallE (.sort (.succ l))
        (.forallE (.bvar 0)
          (.forallE (.app (.lam (.sort (.succ l))
              (.app (.const ``List [l]) (.app (.const ``NTree [l]) (.bvar 0)))) (.bvar 1))
            (.app (.const ``NTree [l]) (.bvar 2))))) (.sort v)
  have hlw : ∀ l' ∈ [l], VLevel.WF U l' := by
    intro l' hl'; simp only [List.mem_cons, List.not_mem_nil, or_false] at hl'; exact hl' ▸ hl
  have hNc : ∀ {Γ : List VExpr}, F₂.IsDefEq U Γ (.const ``NTree [l]) (.const ``NTree [l])
      (.forallE (.sort (.succ l)) (.sort (.succ l))) := fun {_} =>
    .constDF hN hlw hlw rfl (.cons rfl .nil)
  have hLc : ∀ {Γ : List VExpr}, F₂.IsDefEq U Γ (.const ``List [l]) (.const ``List [l])
      (.forallE (.sort (.succ l)) (.sort (.succ l))) := fun {_} =>
    .constDF hL hlw hlw rfl (.cons rfl .nil)
  have hs : F₂.IsDefEq U [] (.sort (.succ l)) (.sort (.succ l)) (.sort (.succ (.succ l))) :=
    .sortDF (show VLevel.WF U (.succ l) from hl) (show VLevel.WF U (.succ l) from hl) rfl
  have hα : F₂.IsDefEq U [.sort (.succ l)] (.bvar 0) (.bvar 0) (.sort (.succ l)) :=
    .bvar (by exact .zero)
  -- the β-step at the third domain, in Γ₂ = [bvar 0, sort (succ l)]
  have hbeta : F₂.IsDefEq U [.bvar 0, .sort (.succ l)]
      (.app (.const ``List [l]) (.app (.const ``NTree [l]) (.bvar 1)))
      (.app (.lam (.sort (.succ l))
        (.app (.const ``List [l]) (.app (.const ``NTree [l]) (.bvar 0)))) (.bvar 1))
      (.sort (.succ l)) := by
    refine .symm (.beta (A := .sort (.succ l)) (B := .sort (.succ l)) ?_ ?_)
    · exact .appDF hLc (.appDF hNc (.bvar (by exact .zero)))
    · exact .bvar (by exact .succ .zero)
  have hres : F₂.IsDefEq U
      [.app (.const ``List [l]) (.app (.const ``NTree [l]) (.bvar 1)), .bvar 0, .sort (.succ l)]
      (.app (.const ``NTree [l]) (.bvar 2)) (.app (.const ``NTree [l]) (.bvar 2))
      (.sort (.succ l)) :=
    .appDF hNc (.bvar (by exact .succ (.succ .zero)))
  exact ⟨_, .forallEDF hs (.forallEDF hα (.forallEDF hbeta hres))⟩


section
variable {F : VEnv}
variable (hL : F.constants ``List = some ⟨1, listType.type⟩)
variable (hN : F.constants ``NTree
  = some ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩)
variable (hnil : F.constants ``List.nil = some ⟨1, listNil.type listDecl 0⟩)
variable (hcons : F.constants ``List.cons = some ⟨1, listCons.type listDecl 0⟩)

/-! ### §D.3 The three values of the substitution are well typed in `F₂` -/

theorem ntree_p0_wf : ∀ l ∈ [(VLevel.param 0)], VLevel.WF 1 l := by
  intro l hl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  exact hl ▸ Nat.zero_lt_one

include hN in
theorem ntree_NTreeC {Γ : List VExpr} : F.IsDefEq 1 Γ (.const ``NTree [.param 0])
    (.const ``NTree [.param 0])
    (.forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))) :=
  .constDF hN ntree_p0_wf ntree_p0_wf rfl (.cons rfl .nil)

include hL in
theorem ntree_ListC {Γ : List VExpr} : F.IsDefEq 1 Γ (.const ``List [.param 0])
    (.const ``List [.param 0])
    (.forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))) :=
  .constDF hL ntree_p0_wf ntree_p0_wf rfl (.cons rfl .nil)

include hnil in
theorem ntree_NilC {Γ : List VExpr} : F.IsDefEq 1 Γ (.const ``List.nil [.param 0])
    (.const ``List.nil [.param 0])
    (.forallE (.sort (.succ (.param 0))) (.app (.const ``List [.param 0]) (.bvar 0))) :=
  .constDF hnil ntree_p0_wf ntree_p0_wf rfl (.cons rfl .nil)

include hcons in
theorem ntree_ConsC {Γ : List VExpr} : F.IsDefEq 1 Γ (.const ``List.cons [.param 0])
    (.const ``List.cons [.param 0])
    (.forallE (.sort (.succ (.param 0)))
      (.forallE (.bvar 0)
        (.forallE (.app (.const ``List [.param 0]) (.bvar 1))
          (.app (.const ``List [.param 0]) (.bvar 2))))) :=
  .constDF hcons ntree_p0_wf ntree_p0_wf rfl (.cons rfl .nil)

include hL hN in
theorem ntreeVal_hasType :
    F.HasType 1 [] ntreeVal
      (.forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))) :=
  .lamDF (.sortDF Nat.zero_lt_one Nat.zero_lt_one rfl)
    (.appDF (ntree_ListC hL) (.appDF (ntree_NTreeC hN) (.bvar (by exact .zero))))

include hL hN hnil in
theorem nlistNil_val_hasType :
    F.HasType 1 [] (.lam (.sort (.succ (.param 0)))
        (.app (.const ``List.nil [.param 0]) (.app (.const ``NTree [.param 0]) (.bvar 0))))
      ((nlistNil.type ntreeAux 1).substC (ntreeRestore.csubst ntreeAux ntreeK)) := by
  have hval : F.HasType 1 [] (.lam (.sort (.succ (.param 0)))
      (.app (.const ``List.nil [.param 0]) (.app (.const ``NTree [.param 0]) (.bvar 0))))
      (.forallE (.sort (.succ (.param 0)))
        (.app (.const ``List [.param 0]) (.app (.const ``NTree [.param 0]) (.bvar 0)))) :=
    .lamDF (.sortDF Nat.zero_lt_one Nat.zero_lt_one rfl)
      (.appDF (ntree_NilC hnil) (.appDF (ntree_NTreeC hN) (.bvar (by exact .zero))))
  have hbeta : F.IsDefEq 1 [.sort (.succ (.param 0))]
      (.app (.const ``List [.param 0]) (.app (.const ``NTree [.param 0]) (.bvar 0)))
      (.app ntreeVal (.bvar 0)) (.sort (.succ (.param 0))) := by
    refine .symm (.beta (A := .sort (.succ (.param 0))) (B := .sort (.succ (.param 0))) ?_ ?_)
    · exact .appDF (ntree_ListC hL) (.appDF (ntree_NTreeC hN) (.bvar (by exact .zero)))
    · exact .bvar (by exact .zero)
  exact .defeqDF (.forallEDF (.sortDF (l := .succ (.param 0)) (l' := .succ (.param 0))
    Nat.zero_lt_one Nat.zero_lt_one rfl) hbeta) hval

include hL hN hcons in
theorem nlistCons_val_hasType :
    F.HasType 1 [] (.lam (.sort (.succ (.param 0)))
        (.app (.const ``List.cons [.param 0]) (.app (.const ``NTree [.param 0]) (.bvar 0))))
      ((nlistCons.type ntreeAux 1).substC (ntreeRestore.csubst ntreeAux ntreeK)) := by
  have hval : F.HasType 1 [] (.lam (.sort (.succ (.param 0)))
      (.app (.const ``List.cons [.param 0]) (.app (.const ``NTree [.param 0]) (.bvar 0))))
      (.forallE (.sort (.succ (.param 0)))
        (.forallE (.app (.const ``NTree [.param 0]) (.bvar 0))
          (.forallE (.app (.const ``List [.param 0]) (.app (.const ``NTree [.param 0]) (.bvar 1)))
            (.app (.const ``List [.param 0]) (.app (.const ``NTree [.param 0]) (.bvar 2)))))) :=
    .lamDF (.sortDF Nat.zero_lt_one Nat.zero_lt_one rfl)
      (.appDF (ntree_ConsC hcons) (.appDF (ntree_NTreeC hN) (.bvar (by exact .zero))))
  have hb1 : F.IsDefEq 1 [.app (.const ``NTree [.param 0]) (.bvar 0), .sort (.succ (.param 0))]
      (.app (.const ``List [.param 0]) (.app (.const ``NTree [.param 0]) (.bvar 1)))
      (.app ntreeVal (.bvar 1)) (.sort (.succ (.param 0))) := by
    refine .symm (.beta (A := .sort (.succ (.param 0))) (B := .sort (.succ (.param 0))) ?_ ?_)
    · exact .appDF (ntree_ListC hL) (.appDF (ntree_NTreeC hN) (.bvar (by exact .zero)))
    · exact .bvar (by exact .succ .zero)
  have hb2 : F.IsDefEq 1
      [.app (.const ``List [.param 0]) (.app (.const ``NTree [.param 0]) (.bvar 1)),
        .app (.const ``NTree [.param 0]) (.bvar 0), .sort (.succ (.param 0))]
      (.app (.const ``List [.param 0]) (.app (.const ``NTree [.param 0]) (.bvar 2)))
      (.app ntreeVal (.bvar 2)) (.sort (.succ (.param 0))) := by
    refine .symm (.beta (A := .sort (.succ (.param 0))) (B := .sort (.succ (.param 0))) ?_ ?_)
    · exact .appDF (ntree_ListC hL) (.appDF (ntree_NTreeC hN) (.bvar (by exact .zero)))
    · exact .bvar (by exact .succ (.succ .zero))
  refine .defeqDF (.forallEDF (.sortDF (l := .succ (.param 0)) (l' := .succ (.param 0))
      Nat.zero_lt_one Nat.zero_lt_one rfl)
    (.forallEDF (.appDF (ntree_NTreeC hN) (.bvar (by exact .zero))) (.forallEDF hb1 hb2))) hval

end

section
variable {env₁ E₁ E₂ F₁ F₂ : VEnv}
variable (h : VEnv.empty.addInduct' listDecl = some env₁)
variable (hE₁ : env₁.addIndTypes ntreeAux = some E₁)
variable (hE₂ : E₁.addIndCtors ntreeAux = some E₂)
variable (hF₁ : env₁.addConstList (ntreeAux.typeConstsC ntreeK) = some F₁)
variable (hF₂ : F₁.addConstList (ntreeAux.ctorConstsCR ntreeRestore ntreeK) = some F₂)

/-! ### §D.4 The staging environments -/

include h hF₁ in
theorem ntreeF₁_ordered : F₁.Ordered :=
  VEnv.addConstList_ordered (listEnv_ordered h) (VEnv.addInductR_typeConstsC_wf (ntreeAux_WF h)) hF₁

include h hE₁ hF₁ hF₂ in
theorem ntreeF₂_ordered : F₂.Ordered :=
  VEnv.addConstList_ordered (ntreeF₁_ordered h hF₁)
    (ntreeAux_ctorConstsCR_wf h (listEnv_ordered h) hE₁ hF₁) hF₂

include h hF₁ hF₂ in
theorem ntreeF₂_list : F₂.constants ``List = some ⟨1, listType.type⟩ :=
  (VEnv.addConstList_le hF₂).constants ((VEnv.addConstList_le hF₁).constants (list_const h))

include h hF₁ hF₂ in
theorem ntreeF₂_nil : F₂.constants ``List.nil = some ⟨1, listNil.type listDecl 0⟩ :=
  (VEnv.addConstList_le hF₂).constants ((VEnv.addConstList_le hF₁).constants (listNil_const h))

include h hF₁ hF₂ in
theorem ntreeF₂_cons : F₂.constants ``List.cons = some ⟨1, listCons.type listDecl 0⟩ :=
  (VEnv.addConstList_le hF₂).constants ((VEnv.addConstList_le hF₁).constants (listCons_const h))

include hF₁ hF₂ in
theorem ntreeF₂_ntree : F₂.constants ``NTree
    = some ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩ :=
  (VEnv.addConstList_le hF₂).constants (VEnv.addConstList_constants hF₁
    (``NTree, ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩)
    (by exact List.Mem.head _))

include hF₂ in
theorem ntreeF₂_node : F₂.constants ``NTree.node
    = some ⟨1, (ntreeNode.typeR ntreeAux ntreeRestore 0).substC
        (ntreeRestore.csubstTy ntreeAux ntreeK)⟩ :=
  VEnv.addConstList_constants hF₂
    (``NTree.node, ⟨1, (ntreeNode.typeR ntreeAux ntreeRestore 0).substC
      (ntreeRestore.csubstTy ntreeAux ntreeK)⟩) (by exact List.Mem.head _)

end

section
variable {env₁ E₁ E₂ F₁ F₂ : VEnv}
variable (h : VEnv.empty.addInduct' listDecl = some env₁)
variable (hE₁ : env₁.addIndTypes ntreeAux = some E₁)
variable (hE₂ : E₁.addIndCtors ntreeAux = some E₂)
variable (hF₁ : env₁.addConstList (ntreeAux.typeConstsC ntreeK) = some F₁)
variable (hF₂ : F₁.addConstList (ntreeAux.ctorConstsCR ntreeRestore ntreeK) = some F₂)

include h hE₁ hE₂ hF₁ hF₂ in
/-- **§D.5 `hσ` at `np = 1`, in its corrected form.**  This is what §B proves the *unweakened*
statement cannot be: a well-formed substitution between the two staging environments at a
**parameterised** nested block.  Every clause is discharged, and exactly one of them uses the new
freedom — `const` at `NTree.node`, through `ntree_node_const_defeq`'s right disjunct.  The other
six constants take the left disjunct, i.e. the old clause verbatim, which is the measurement that
`WFD` is a weakening applied in one place and not a different hypothesis.

`U = 2 = ntreeAux.recUvars`, which is the instantiation obligation (B)'s route wants. -/
theorem ntree_csubst_WFD₂ : (ntreeRestore.csubst ntreeAux ntreeK).WFD E₂ F₂ 2 := by
  have henv₁ := listEnv_ordered h
  have hFo := ntreeF₂_ordered h hE₁ hF₁ hF₂
  have hfresh := ntree_csubst_fresh h
  have hL := ntreeF₂_list h hF₁ hF₂
  have hN := ntreeF₂_ntree hF₁ hF₂
  have hnil := ntreeF₂_nil h hF₁ hF₂
  have hcons := ntreeF₂_cons h hF₁ hF₂
  refine ⟨ntree_csubst_closed, ?_, ?_, ?_⟩
  · intro c ci hn hc
    obtain ⟨hd1, hd2, hd3, hd4⟩ := ntree_csubst_ne hn
    by_cases hNT : c = ``NTree
    · subst hNT
      rw [VEnv.addConstList_constants_of_not_mem hE₂
          (by show ``NTree ∉ [``NTree.node, `_nested.List_1.nil, `_nested.List_1.cons]; simp),
        ntree_const_staged h hE₁] at hc
      cases hc
      exact ⟨_, hN, .inl rfl⟩
    by_cases hND : c = ``NTree.node
    · subst hND
      rw [VEnv.addConstList_constants hE₂ (``NTree.node, ⟨1, ntreeNode.type ntreeAux 0⟩)
        (by exact List.Mem.head _)] at hc
      cases hc
      refine ⟨_, ntreeF₂_node hF₂, .inr ?_⟩
      intro Γ ls hls hlen
      match ls, hlen with
      | [l], _ =>
        obtain ⟨v, hv⟩ := ntree_node_const_defeq (U := 2) (l := l) hL hN
          (hls _ List.mem_cons_self)
        exact ⟨v, hv.weak0 hFo⟩
    · have hm₂ : c ∉ (ntreeAux.ctorConsts.map (·.1)) := by
        show c ∉ [``NTree.node, `_nested.List_1.nil, `_nested.List_1.cons]
        simp [hND, hd3, hd4]
      have hm₁ : c ∉ (ntreeAux.typeConsts.map (·.1)) := by
        show c ∉ [``NTree, `_nested.List_1]
        simp [hNT, hd1]
      rw [VEnv.addConstList_constants_of_not_mem hE₂ hm₂,
        VEnv.addConstList_constants_of_not_mem hE₁ hm₁] at hc
      refine ⟨_, ?_, .inl rfl⟩
      rw [(henv₁.noCSubstC hfresh hc).substC_eq]
      have hm₄ : c ∉ ((ntreeAux.ctorConstsCR ntreeRestore ntreeK).map (·.1)) := by
        show c ∉ [``NTree.node]; simp [hND]
      have hm₃ : c ∉ ((ntreeAux.typeConstsC ntreeK).map (·.1)) := by
        show c ∉ [``NTree]; simp [hNT]
      rw [VEnv.addConstList_constants_of_not_mem hF₂ hm₄,
        VEnv.addConstList_constants_of_not_mem hF₁ hm₃]
      exact hc
  · intro df hdf
    rw [VEnv.addConstList_defeqs hE₂, VEnv.addConstList_defeqs hE₁] at hdf
    rw [(henv₁.noCSubstD hfresh hdf).substC_eq,
      VEnv.addConstList_defeqs hF₂, VEnv.addConstList_defeqs hF₁]
    exact hdf
  · intro c t ci Γ ls ls' hσv hc
    by_cases hd1 : c = `_nested.List_1
    · subst hd1
      rw [show ntreeRestore.csubst ntreeAux ntreeK `_nested.List_1 = some ntreeVal from rfl] at hσv
      cases hσv
      rw [VEnv.addConstList_constants_of_not_mem hE₂
          (by show `_nested.List_1 ∉ [``NTree.node, `_nested.List_1.nil, `_nested.List_1.cons];
              simp),
        nlist_const_staged h hE₁] at hc
      cases hc
      exact CSubst.val_of_hasType hFo (ntreeVal_hasType hL hN)
    by_cases hd3 : c = `_nested.List_1.nil
    · subst hd3
      rw [show ntreeRestore.csubst ntreeAux ntreeK `_nested.List_1.nil
        = some (.lam (.sort (.succ (.param 0)))
            (.app (.const ``List.nil [.param 0])
              (.app (.const ``NTree [.param 0]) (.bvar 0)))) from rfl] at hσv
      cases hσv
      rw [VEnv.addConstList_constants hE₂
        (`_nested.List_1.nil, ⟨1, nlistNil.type ntreeAux 1⟩)
        (by exact List.Mem.tail _ (List.Mem.head _))] at hc
      cases hc
      exact CSubst.val_of_hasType hFo (nlistNil_val_hasType hL hN hnil)
    by_cases hd4 : c = `_nested.List_1.cons
    · subst hd4
      rw [show ntreeRestore.csubst ntreeAux ntreeK `_nested.List_1.cons
        = some (.lam (.sort (.succ (.param 0)))
            (.app (.const ``List.cons [.param 0])
              (.app (.const ``NTree [.param 0]) (.bvar 0)))) from rfl] at hσv
      cases hσv
      rw [VEnv.addConstList_constants hE₂
        (`_nested.List_1.cons, ⟨1, nlistCons.type ntreeAux 1⟩)
        (by exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))] at hc
      cases hc
      exact CSubst.val_of_hasType hFo (nlistCons_val_hasType hL hN hcons)
    by_cases hd2 : c = `_nested.List_1.rec
    · subst hd2
      exfalso
      rw [VEnv.addConstList_constants_of_not_mem hE₂
          (by show `_nested.List_1.rec ∉ [``NTree.node, `_nested.List_1.nil,
                `_nested.List_1.cons]; simp),
        VEnv.addConstList_constants_of_not_mem hE₁
          (by show `_nested.List_1.rec ∉ [``NTree, `_nested.List_1]; simp),
        VEnv.addInduct'_constants_of_not_mem h (by decide)] at hc
      exact absurd hc nofun
    · exfalso
      rw [show ntreeRestore.csubst ntreeAux ntreeK c = none from by
        show List.lookup c [(`_nested.List_1, _), (`_nested.List_1.rec, _),
          (`_nested.List_1.nil, _), (`_nested.List_1.cons, _)] = none
        rw [List.lookup_cons, show (c == `_nested.List_1) = false from beq_eq_false_iff_ne.2 hd1,
          List.lookup_cons,
          show (c == `_nested.List_1.rec) = false from beq_eq_false_iff_ne.2 hd2,
          List.lookup_cons,
          show (c == `_nested.List_1.nil) = false from beq_eq_false_iff_ne.2 hd3,
          List.lookup_cons,
          show (c == `_nested.List_1.cons) = false from beq_eq_false_iff_ne.2 hd4]
        rfl] at hσv
      exact absurd hσv nofun

end

/-- **The other candidate repair, refuted.**  If `ctorConstsCR` declared the substituted stored
type instead of the restored one, `const` would be `rfl` — but the substituted stored type is
**not** what Lean's kernel declares for `NTree.node` (contrast `ntreeNode_typeR`, which is `rfl`
against `type_of% @NTree.node`).  So that repair buys obligation (B) by giving up faithfulness,
and `CSubst.WFD` is the remaining option. -/
theorem ntree_node_redex_ne_declared :
    (ntreeNode.type ntreeAux 0).substC (ntreeRestore.csubst ntreeAux ntreeK)
      ≠ (vconst(type_of% @NTree.node)).type := by decide

section
variable {env₁ E₁ E₂ F₁ F₂ : VEnv}
variable (h : VEnv.empty.addInduct' listDecl = some env₁)
variable (hE₁ : env₁.addIndTypes ntreeAux = some E₁)
variable (hE₂ : E₁.addIndCtors ntreeAux = some E₂)
variable (hF₁ : env₁.addConstList (ntreeAux.typeConstsC ntreeK) = some F₁)
variable (hF₂ : F₁.addConstList (ntreeAux.ctorConstsCR ntreeRestore ntreeK) = some F₂)

include h hE₁ hE₂ in
/-- **§D.6 `hsrc` at `np = 1`.**  `nfn_recConsts_wf`'s proof verbatim at the parameterised block:
the *unrestored* recursor constants are types in `E₂`, from `ntreeAux_WF` and the two staging
`Ordered`s.  Nothing about `np` enters. -/
theorem ntree_recConsts_wf : ∀ c ∈ ntreeAux.recConsts, VConstant.WF E₂ c.2 := by
  intro c hc
  have henv₁ := listEnv_ordered h
  have o1 := VInductDecl'.addIndTypes_ordered henv₁ (ntreeAux_WF h) hE₁
  have o2 := VInductDecl'.addIndCtors_ordered o1 (ntreeAux_WF h) hE₁ hE₂
  have hR : ntreeAux.RecCtx E₂ := (ntreeAux_WF h).recCtx hE₁ hE₂ VEnv.LE.rfl o2
  simp only [VInductDecl'.recConsts, List.mem_map] at hc
  obtain ⟨⟨T, j⟩, hTj, rfl⟩ := hc
  have hT : ntreeAux.types[j]? = some T := List.mk_mem_zipIdx_iff_getElem?.1 hTj
  have hj : j < ntreeAux.nm := by
    rcases Nat.lt_or_ge j ntreeAux.types.length with hlt | hle
    · exact hlt
    · rw [List.getElem?_eq_none hle] at hT; exact absurd hT (by simp)
  exact VInductDecl'.recType_isType hR hT hj (VInductDecl'.onCtxMinors hR)

include h hE₁ hE₂ hF₁ hF₂ in
/-- **Obligation (B) at a PARAMETERISED nested block, reduced to `hbridge` alone.**

Every environment-level input is discharged: `hsrc` (§D.6), `hσ` in its corrected form (§D.5),
`he₂` (§D.4).  What is left is the telescope bridge — §T5's motive entries, §T6's minor entries
(whose `hfld` `Theory/Inductive/ParamRedex.lean` §5 supplies at a parameterised block) and the
head `hbody` — and *nothing else*.

Compare `nfnAux_recConstsR_wf`, which discharges (B) outright at `np = 0` because there the
bridge is `rfl` (`nfn_recType_substC_0`/`_1`) — and `mp_recTypeR_bridge_false` /
`ntreeNode_substC_ne_typeR`, which show it is not `rfl` here.  So the `np ≥ 1` form of (B)'s
`csubst_recType_eq` is not a patched equation: it is this `hbridge`, a telescope defeq, and the
equation is *provably* unavailable. -/
theorem ntreeAux_recConstsR_wf_of_bridge
    (hbridge : ∀ (j : Nat) (T : VIndType), ntreeAux.types[j]? = some T →
      ∃ (As As' : List VExpr) (B B' : VExpr) (v : VLevel),
        (ntreeAux.recType j).substC (ntreeRestore.csubst ntreeAux ntreeK) = VExpr.mkPi As B ∧
        (ntreeAux.recTypeR ntreeRestore j).substC (ntreeRestore.csubst ntreeAux ntreeK)
          = VExpr.mkPi As' B' ∧
        F₂.TeleDefEq ntreeAux.recUvars [] As As' ∧
        F₂.IsDefEq ntreeAux.recUvars As.reverse B B' (.sort v)) :
    ∀ c ∈ ntreeAux.recConstsR ntreeRestore ntreeK, VConstant.WF F₂ c.2 :=
  VEnv.recConstsR_wf_of_substCD' (ntree_recConsts_wf h hE₁ hE₂)
    (ntree_csubst_WFD₂ h hE₁ hE₂ hF₁ hF₂) (ntreeF₂_ordered h hE₁ hF₁ hF₂) hbridge

end

/-! ## §E `hbridge` at the parameterised witness — obligation (B) DISCHARGED at `ntreeAux`

§D reduced obligation (B) at `ntreeAux` to `hbridge` alone
(`ntreeAux_recConstsR_wf_of_bridge`).  This section **proves** `hbridge`, so (B) holds outright
at a parameterised nested block.

What `hbridge` asks for is a `mkPi` decomposition of each side plus a `VEnv.TeleDefEq` and a body
defeq.  At `ntreeAux` the two substituted telescopes are

    A₀ = Sort (u+1)                                          -- the parameter α
    A₁ = Π (NTree.{u} #0), Sort v                             -- motive for `NTree`
    A₂ = Π ((λ α, List.{u} (NTree.{u} α)) #1), Sort v         -- motive for the companion
    A₃ = the `NTree.node` minor
    A₄ = the `List.nil` minor
    A₅ = the `List.cons` minor

against the same list with each `(λ α, c.{u} (NTree.{u} α)) #k` β-contracted to
`c.{u} (NTree.{u} #k)`, for `c ∈ {List, List.nil, List.cons}`.  Entries `A₀`/`A₁` do not move
(`VEnv.TeleDefEq.rfl`, free); the other four do, and each moves by **exactly one β step** —
`rbetaL`/`rbetaNil`/`rbetaCons` below.  The body moves at `j = 1` and not at `j = 0`, because the
major premise of `NTree.rec_1` is a companion application and that of `NTree.rec` is not.

Everything is at `U = ntreeAux.recUvars = 2`: the block's own universe is `.param 1` (the
recursor's numbering, `ntreeAux.selfLvls = [.param 1]`) and `.param 0` is the fresh elimination
universe.  That is why §D.3's helpers, which are at `U = 1` and `.param 0`, are not reused. -/


def rV : VExpr := .lam (.sort (.succ (.param 1)))
  (.app (.const ``List [.param 1]) (.app (.const ``NTree [.param 1]) (.bvar 0)))
def rVnil : VExpr := .lam (.sort (.succ (.param 1)))
  (.app (.const ``List.nil [.param 1]) (.app (.const ``NTree [.param 1]) (.bvar 0)))
def rVcons : VExpr := .lam (.sort (.succ (.param 1)))
  (.app (.const ``List.cons [.param 1]) (.app (.const ``NTree [.param 1]) (.bvar 0)))

section
variable {F : VEnv}
variable (hL : F.constants ``List = some ⟨1, listType.type⟩)
variable (hN : F.constants ``NTree
  = some ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩)
variable (hnil : F.constants ``List.nil = some ⟨1, listNil.type listDecl 0⟩)
variable (hcons : F.constants ``List.cons = some ⟨1, listCons.type listDecl 0⟩)
variable (hnode : F.constants ``NTree.node
  = some ⟨1, (ntreeNode.typeR ntreeAux ntreeRestore 0).substC
      (ntreeRestore.csubstTy ntreeAux ntreeK)⟩)

theorem ntree_p1_wf : ∀ l ∈ [(VLevel.param 1)], VLevel.WF 2 l := by
  intro l hl; simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  exact hl ▸ (by decide)

include hN in
theorem rNC {Γ : List VExpr} : F.IsDefEq 2 Γ (.const ``NTree [.param 1])
    (.const ``NTree [.param 1])
    (.forallE (.sort (.succ (.param 1))) (.sort (.succ (.param 1)))) :=
  .constDF hN ntree_p1_wf ntree_p1_wf rfl (.cons rfl .nil)

include hL in
theorem rLC {Γ : List VExpr} : F.IsDefEq 2 Γ (.const ``List [.param 1])
    (.const ``List [.param 1])
    (.forallE (.sort (.succ (.param 1))) (.sort (.succ (.param 1)))) :=
  .constDF hL ntree_p1_wf ntree_p1_wf rfl (.cons rfl .nil)

include hnil in
theorem rNilC {Γ : List VExpr} : F.IsDefEq 2 Γ (.const ``List.nil [.param 1])
    (.const ``List.nil [.param 1])
    (.forallE (.sort (.succ (.param 1))) (.app (.const ``List [.param 1]) (.bvar 0))) :=
  .constDF hnil ntree_p1_wf ntree_p1_wf rfl (.cons rfl .nil)

include hcons in
theorem rConsC {Γ : List VExpr} : F.IsDefEq 2 Γ (.const ``List.cons [.param 1])
    (.const ``List.cons [.param 1])
    (.forallE (.sort (.succ (.param 1)))
      (.forallE (.bvar 0)
        (.forallE (.app (.const ``List [.param 1]) (.bvar 1))
          (.app (.const ``List [.param 1]) (.bvar 2))))) :=
  .constDF hcons ntree_p1_wf ntree_p1_wf rfl (.cons rfl .nil)

include hnode in
theorem rNodeC {Γ : List VExpr} : F.IsDefEq 2 Γ (.const ``NTree.node [.param 1])
    (.const ``NTree.node [.param 1])
    (.forallE (.sort (.succ (.param 1)))
      (.forallE (.bvar 0)
        (.forallE (.app (.const ``List [.param 1])
            (.app (.const ``NTree [.param 1]) (.bvar 1)))
          (.app (.const ``NTree [.param 1]) (.bvar 2))))) :=
  .constDF hnode ntree_p1_wf ntree_p1_wf rfl (.cons rfl .nil)

/-! ### The three β-steps -/

include hL hN in
theorem rbetaL {Γ : List VExpr} {k : Nat} (hk : Lookup Γ k (.sort (.succ (.param 1)))) :
    F.IsDefEq 2 Γ (.app rV (.bvar k))
      (.app (.const ``List [.param 1]) (.app (.const ``NTree [.param 1]) (.bvar k)))
      (.sort (.succ (.param 1))) := by
  have h := VEnv.IsDefEq.beta (env := F) (uvars := 2) (Γ := Γ)
    (A := .sort (.succ (.param 1))) (B := .sort (.succ (.param 1)))
    (.appDF (rLC hL) (.appDF (rNC hN) (.bvar .zero))) (.bvar hk)
  simpa [rV, VExpr.inst] using h

include hN hnil in
theorem rbetaNil {Γ : List VExpr} {k : Nat} (hk : Lookup Γ k (.sort (.succ (.param 1)))) :
    F.IsDefEq 2 Γ (.app rVnil (.bvar k))
      (.app (.const ``List.nil [.param 1]) (.app (.const ``NTree [.param 1]) (.bvar k)))
      (.app (.const ``List [.param 1]) (.app (.const ``NTree [.param 1]) (.bvar k))) := by
  have h := VEnv.IsDefEq.beta (env := F) (uvars := 2) (Γ := Γ)
    (A := .sort (.succ (.param 1)))
    (e := .app (.const ``List.nil [.param 1]) (.app (.const ``NTree [.param 1]) (.bvar 0)))
    (.appDF (rNilC hnil) (.appDF (rNC hN) (.bvar .zero))) (.bvar hk)
  simpa [rVnil, VExpr.inst] using h

include hN hcons in
theorem rbetaCons {Γ : List VExpr} {k : Nat} (hk : Lookup Γ k (.sort (.succ (.param 1)))) :
    F.IsDefEq 2 Γ (.app rVcons (.bvar k))
      (.app (.const ``List.cons [.param 1]) (.app (.const ``NTree [.param 1]) (.bvar k)))
      (.forallE (.app (.const ``NTree [.param 1]) (.bvar k))
        (.forallE (.app (.const ``List [.param 1])
            (.app (.const ``NTree [.param 1]) (.bvar (k+1))))
          (.app (.const ``List [.param 1])
            (.app (.const ``NTree [.param 1]) (.bvar (k+2)))))) := by
  have h := VEnv.IsDefEq.beta (env := F) (uvars := 2) (Γ := Γ)
    (A := .sort (.succ (.param 1)))
    (e := .app (.const ``List.cons [.param 1]) (.app (.const ``NTree [.param 1]) (.bvar 0)))
    (.appDF (rConsC hcons) (.appDF (rNC hN) (.bvar .zero))) (.bvar hk)
  have e2 : 1 + (k + 1) = k + 2 := by omega
  simpa [rVcons, VExpr.inst, VExpr.lift, VExpr.liftN, e2] using h

end

/-! ### §E.1 The two substituted telescopes, written out -/

def rNt : VExpr := .const ``NTree [.param 1]
def rLt : VExpr := .const ``List [.param 1]

def rA0 : VExpr := .sort (.succ (.param 1))
def rA1 : VExpr := .forallE (.app rNt (.bvar 0)) (.sort (.param 0))
def rA2 : VExpr := .forallE (.app rV (.bvar 1)) (.sort (.param 0))
def rA2' : VExpr := .forallE (.app rLt (.app rNt (.bvar 1))) (.sort (.param 0))
def rA3 : VExpr :=
  .forallE (.bvar 2) (.forallE (.app rV (.bvar 3)) (.forallE (.app (.bvar 2) (.bvar 0))
    (.app (.bvar 4) (.app (.app (.app (.const ``NTree.node [.param 1]) (.bvar 5)) (.bvar 2))
      (.bvar 1)))))
def rA3' : VExpr :=
  .forallE (.bvar 2) (.forallE (.app rLt (.app rNt (.bvar 3)))
    (.forallE (.app (.bvar 2) (.bvar 0))
      (.app (.bvar 4) (.app (.app (.app (.const ``NTree.node [.param 1]) (.bvar 5)) (.bvar 2))
        (.bvar 1)))))
def rA4 : VExpr := .app (.bvar 1) (.app rVnil (.bvar 3))
def rA4' : VExpr := .app (.bvar 1) (.app (.const ``List.nil [.param 1]) (.app rNt (.bvar 3)))
def rA5 : VExpr :=
  .forallE (.app rNt (.bvar 4)) (.forallE (.app rV (.bvar 5))
    (.forallE (.app (.bvar 5) (.bvar 1)) (.forallE (.app (.bvar 5) (.bvar 1))
      (.app (.bvar 6) (.app (.app (.app rVcons (.bvar 8)) (.bvar 3)) (.bvar 2))))))
def rA5' : VExpr :=
  .forallE (.app rNt (.bvar 4)) (.forallE (.app rLt (.app rNt (.bvar 5)))
    (.forallE (.app (.bvar 5) (.bvar 1)) (.forallE (.app (.bvar 5) (.bvar 1))
      (.app (.bvar 6) (.app (.app (.app (.const ``List.cons [.param 1]) (.app rNt (.bvar 8)))
        (.bvar 3)) (.bvar 2))))))

def rTele : List VExpr := [rA0, rA1, rA2, rA3, rA4, rA5]
def rTeleR : List VExpr := [rA0, rA1, rA2', rA3', rA4', rA5']

def rBody0 : VExpr := .forallE (.app rNt (.bvar 5)) (.app (.bvar 5) (.bvar 0))
def rBody1 : VExpr := .forallE (.app rV (.bvar 5)) (.app (.bvar 4) (.bvar 0))
def rBody1' : VExpr := .forallE (.app rLt (.app rNt (.bvar 5))) (.app (.bvar 4) (.bvar 0))

/-- The decompositions `hbridge` asks for, both `rfl`. -/
theorem rrecType_eq_0 :
    (ntreeAux.recType 0).substC (ntreeRestore.csubst ntreeAux ntreeK)
      = VExpr.mkPi rTele rBody0 := rfl
theorem rrecType_eq_1 :
    (ntreeAux.recType 1).substC (ntreeRestore.csubst ntreeAux ntreeK)
      = VExpr.mkPi rTele rBody1 := rfl
theorem rrecTypeR_eq_0 :
    (ntreeAux.recTypeR ntreeRestore 0).substC (ntreeRestore.csubst ntreeAux ntreeK)
      = VExpr.mkPi rTeleR rBody0 := rfl
theorem rrecTypeR_eq_1 :
    (ntreeAux.recTypeR ntreeRestore 1).substC (ntreeRestore.csubst ntreeAux ntreeK)
      = VExpr.mkPi rTeleR rBody1' := rfl


section
variable {F : VEnv}
variable (hL : F.constants ``List = some ⟨1, listType.type⟩)
variable (hN : F.constants ``NTree
  = some ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩)
variable (hnil : F.constants ``List.nil = some ⟨1, listNil.type listDecl 0⟩)
variable (hcons : F.constants ``List.cons = some ⟨1, listCons.type listDecl 0⟩)
variable (hnode : F.constants ``NTree.node
  = some ⟨1, (ntreeNode.typeR ntreeAux ntreeRestore 0).substC
      (ntreeRestore.csubstTy ntreeAux ntreeK)⟩)

theorem rp0_wf : VLevel.WF 2 (.param 0) := by decide
theorem rp1_wf : VLevel.WF 2 (.param 1) := by decide

include hL hN in
theorem rE2 : F.IsDefEq 2 [rA1, rA0] rA2 rA2'
    (.sort (.imax (.succ (.param 1)) (.succ (.param 0)))) :=
  .forallEDF (rbetaL hL hN (Γ := [rA1, rA0]) (k := 1) (.succ .zero))
    (.sortDF rp0_wf rp0_wf rfl)

include hL hN hnode in
theorem rE3 : ∃ u, F.IsDefEq 2 [rA2, rA1, rA0] rA3 rA3' (.sort u) := by
  refine ⟨_, .forallEDF (.bvar (show Lookup [rA2, rA1, rA0] 2 (.sort (.succ (.param 1))) from
      .succ (.succ .zero)))
    (.forallEDF (rbetaL hL hN (k := 3) (.succ (.succ (.succ .zero))))
      (.forallEDF (v := .param 0) (.appDF (B := .sort (.param 0))
        (.bvar (.succ (.succ .zero))) (.bvar .zero)) ?_))⟩
  refine .appDF (.bvar (show Lookup _ 4 (.forallE (.app rNt (.bvar 5)) (.sort (.param 0))) from
      .succ (.succ (.succ (.succ .zero)))))
    (.appDF (.appDF (.appDF (rNodeC hnode)
        (.bvar (show Lookup _ 5 (.sort (.succ (.param 1))) from
          .succ (.succ (.succ (.succ (.succ .zero))))))) (.bvar (.succ (.succ .zero))))
      (.defeqDF (rbetaL hL hN (k := 5)
        (.succ (.succ (.succ (.succ (.succ .zero)))))) (.bvar (.succ .zero))))

include hL hN hnil in
theorem rE4 : ∃ u, F.IsDefEq 2 [rA3, rA2, rA1, rA0] rA4 rA4' (.sort u) :=
  ⟨_, .appDF (.bvar (show Lookup [rA3, rA2, rA1, rA0] 1
      (.forallE (.app rV (.bvar 3)) (.sort (.param 0))) from .succ .zero))
    (.defeqDF (.symm (rbetaL hL hN (k := 3) (.succ (.succ (.succ .zero)))))
      (rbetaNil hN hnil (k := 3) (.succ (.succ (.succ .zero)))))⟩

include hL hN hcons in
theorem rE5 : ∃ u, F.IsDefEq 2 [rA4, rA3, rA2, rA1, rA0] rA5 rA5' (.sort u) := by
  refine ⟨_, .forallEDF (.appDF (rNC hN) (.bvar (show Lookup [rA4, rA3, rA2, rA1, rA0] 4
      (.sort (.succ (.param 1))) from .succ (.succ (.succ (.succ .zero))))))
    (.forallEDF (rbetaL hL hN (k := 5) (.succ (.succ (.succ (.succ (.succ .zero))))))
      (.forallEDF (.appDF (B := .sort (.param 0))
          (.bvar (.succ (.succ (.succ (.succ (.succ .zero)))))) (.bvar (.succ .zero)))
        (.forallEDF (v := .param 0) (.appDF (B := .sort (.param 0))
            (.bvar (.succ (.succ (.succ (.succ (.succ .zero)))))) (.bvar (.succ .zero))) ?_)))⟩
  refine .appDF (.bvar (show Lookup _ 6 (.forallE (.app rV (.bvar 8)) (.sort (.param 0))) from
      .succ (.succ (.succ (.succ (.succ (.succ .zero)))))))
    (.defeqDF (.symm (rbetaL hL hN (k := 8) ?hk8))
      (.appDF (.appDF (rbetaCons hN hcons (k := 8) ?hk8) (.bvar (.succ (.succ (.succ .zero)))))
        (.defeqDF (rbetaL hL hN (k := 8) ?hk8) (.bvar (.succ (.succ .zero))))))
  case hk8 => exact .succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))

/-! ### The body defeqs -/

include hN in
theorem rB0 : ∃ v, F.IsDefEq 2 rTele.reverse rBody0 rBody0 (.sort v) :=
  ⟨_, .forallEDF (.appDF (rNC hN) (.bvar (show Lookup rTele.reverse 5
      (.sort (.succ (.param 1))) from .succ (.succ (.succ (.succ (.succ .zero)))))))
    (.appDF (B := .sort (.param 0))
      (.bvar (.succ (.succ (.succ (.succ (.succ .zero)))))) (.bvar .zero))⟩

include hL hN in
theorem rB1 : ∃ v, F.IsDefEq 2 rTele.reverse rBody1 rBody1' (.sort v) :=
  ⟨_, .forallEDF (rbetaL hL hN (k := 5)
      (show Lookup rTele.reverse 5 (.sort (.succ (.param 1))) from
        .succ (.succ (.succ (.succ (.succ .zero))))))
    (.appDF (B := .sort (.param 0))
      (.bvar (.succ (.succ (.succ (.succ .zero))))) (.bvar .zero))⟩

/-! ### The telescope defeq and `hbridge` -/

include hL hN hnil hcons hnode in
theorem rTeleDefEq : F.TeleDefEq 2 [] rTele rTeleR := by
  obtain ⟨u2, h2⟩ : ∃ u, F.IsDefEq 2 [rA1, rA0] rA2 rA2' (.sort u) := ⟨_, rE2 hL hN⟩
  obtain ⟨u3, h3⟩ := rE3 hL hN hnode
  obtain ⟨u4, h4⟩ := rE4 hL hN hnil
  obtain ⟨u5, h5⟩ := rE5 hL hN hcons
  exact .rfl (.rfl (.cons h2 (.cons h3 (.cons h4 (.cons h5 .nil)))))

include hL hN hnil hcons hnode in
/-- **`hbridge` at `ntreeAux`, proved.**  Both recursors of the parameterised nested block. -/
theorem rhbridge : ∀ (j : Nat) (T : VIndType), ntreeAux.types[j]? = some T →
    ∃ (As As' : List VExpr) (B B' : VExpr) (v : VLevel),
      (ntreeAux.recType j).substC (ntreeRestore.csubst ntreeAux ntreeK) = VExpr.mkPi As B ∧
      (ntreeAux.recTypeR ntreeRestore j).substC (ntreeRestore.csubst ntreeAux ntreeK)
        = VExpr.mkPi As' B' ∧
      F.TeleDefEq ntreeAux.recUvars [] As As' ∧
      F.IsDefEq ntreeAux.recUvars As.reverse B B' (.sort v) := by
  have htd := rTeleDefEq hL hN hnil hcons hnode
  rintro (_ | _ | j) T hT
  · obtain ⟨v, hv⟩ := rB0 hN
    exact ⟨rTele, rTeleR, rBody0, rBody0, v, rrecType_eq_0, rrecTypeR_eq_0, htd, hv⟩
  · obtain ⟨v, hv⟩ := rB1 hL hN
    exact ⟨rTele, rTeleR, rBody1, rBody1', v, rrecType_eq_1, rrecTypeR_eq_1, htd, hv⟩
  · simp [ntreeAux] at hT

end

/-! ### §E.5 Anti-vacuity: the bridge carries genuine conversion content

`docs/vacuity-ledger.md` §5.  Four of the six telescope entries actually **move** under the
bridge, so `VEnv.TeleDefEq.cons` — the disjunct that costs a real `IsDefEq` — is taken four times
and the free `VEnv.TeleDefEq.rfl` only twice.  And the *equation* form of the bridge, which is
what `VEnv.recConstsR_wf_of_substC`/`_of_substC_of_eq` ask for, is **false** at both recursors, so
`hbridge` is not an identity in disguise. -/

theorem rA2_ne : rA2 ≠ rA2' := by decide
theorem rA3_ne : rA3 ≠ rA3' := by decide
theorem rA4_ne : rA4 ≠ rA4' := by decide
theorem rA5_ne : rA5 ≠ rA5' := by decide
theorem rTele_ne : rTele ≠ rTeleR := by decide

/-- The `j = 1` body moves… -/
theorem rBody1_ne : rBody1 ≠ rBody1' := by decide

/-- …and the `j = 0` body does **not**: `NTree.rec`'s major premise is an application of the
member the step declares, on which the restoration is the identity (`ntreeRestore_ownId`).  A
negative result, recorded as one: at `j = 0` only the *telescope* carries content. -/
theorem rBody0_eq : (ntreeAux.recType 0).substC (ntreeRestore.csubst ntreeAux ntreeK)
    = VExpr.mkPi rTele rBody0
    ∧ (ntreeAux.recTypeR ntreeRestore 0).substC (ntreeRestore.csubst ntreeAux ntreeK)
      = VExpr.mkPi rTeleR rBody0 := ⟨rrecType_eq_0, rrecTypeR_eq_0⟩

/-- **The strict bridge is false at both recursors of `ntreeAux`** — the `np ≥ 1` analogue of
`mp_recTypeR_bridge_false` (`Theory/Inductive/ParamRedex.lean` §6) at the *canonical*
parameterised block.  So `hbridge` above cannot be obtained from
`VEnv.recConstsR_wf_of_substC_of_eq`. -/
theorem ntree_recTypeR_bridge_false_0 :
    (ntreeAux.recType 0).substC (ntreeRestore.csubst ntreeAux ntreeK)
      ≠ (ntreeAux.recTypeR ntreeRestore 0).substC (ntreeRestore.csubst ntreeAux ntreeK) := by
  decide

theorem ntree_recTypeR_bridge_false_1 :
    (ntreeAux.recType 1).substC (ntreeRestore.csubst ntreeAux ntreeK)
      ≠ (ntreeAux.recTypeR ntreeRestore 1).substC (ntreeRestore.csubst ntreeAux ntreeK) := by
  decide

section
variable {env₁ E₁ E₂ F₁ F₂ : VEnv}
variable (h : VEnv.empty.addInduct' listDecl = some env₁)
variable (hE₁ : env₁.addIndTypes ntreeAux = some E₁)
variable (hE₂ : E₁.addIndCtors ntreeAux = some E₂)
variable (hF₁ : env₁.addConstList (ntreeAux.typeConstsC ntreeK) = some F₁)
variable (hF₂ : F₁.addConstList (ntreeAux.ctorConstsCR ntreeRestore ntreeK) = some F₂)

include h hE₁ hE₂ hF₁ hF₂ in
/-- **Obligation (B) at a PARAMETERISED nested block, DISCHARGED.** -/
theorem ntreeAux_recConstsR_wf :
    ∀ c ∈ ntreeAux.recConstsR ntreeRestore ntreeK, VConstant.WF F₂ c.2 :=
  ntreeAux_recConstsR_wf_of_bridge h hE₁ hE₂ hF₁ hF₂
    (rhbridge (ntreeF₂_list h hF₁ hF₂) (ntreeF₂_ntree hF₁ hF₂) (ntreeF₂_nil h hF₁ hF₂)
      (ntreeF₂_cons h hF₁ hF₂) (ntreeF₂_node hF₂))

end


/-! ## §F Obligation (C) at `ntreeAux`: what it actually needs, measured

The brief this section answers asked for (C) *after* (B), and warned that the residual list §21
carried for it over-counted.  It did, and in a specific way: **(C)' has no `hσ` at all**
(`VEnv.iotaRulesRS_wf_of_substC'`, §A), so the obstruction §B refutes — `CSubst.WF`'s `const`
clause — was never one of (C)'s inputs.  What (C) at `ntreeAux` actually needs, measured rather
than read off:

* **three rules**, `iotaRules.length = iotaRulesRS.length = 3`, all at `uvars = 2`, so the
  `df'.uvars = df.uvars` clause of (C)'s bridge is free (`ntree_iotaRulesRS_uvars`);
* **nine componentwise conversions** — `type`, `lhs`, `rhs` for each rule — and *every one of the
  nine moves* (`ntree_iota_components_ne`), on terms of size 83–273 against 93–253 substituted;
  none is an identity, so (C) is nine real conversions and no `TeleDefEq.rfl`-style discount
  applies to any of them;
* the strict form is refuted here too (`ntree_iotaRules_bridge_false`), the `ntreeAux` analogue of
  `ParamRedex.lean`'s `mp_iotaRules_bridge_false`;
* and the two pieces of *data* the strict route never had to produce, which §A.1 already names and
  this measurement confirms are what is left: `htype` — `e₃.IsType 2 [] (df.type.substC σ)`, from
  which §T7's `iotaRule_tele_onCtx_of_type_defeq` gets the substituted ι-context's `OnCtx` — and
  `D.IotaCtx`, which §T16.5's `iotaLhsPre_hasType` needs to type the recursor spine in the `lhs`.
  Neither is an environment-level `CSubst` obligation, which is the correction: **(C)'s residual is
  a typing residual, not a substitution residual.**

So (C) is *not* the same shape of job as (B).  (B) at `ntreeAux` came down to six telescope entries
of which two were free and four moved by one β step each, plus one body — §E closes it.  (C) is
nine conversions over λ-telescopes with recursor-application bodies, none free, and it needs
`htype`/`IotaCtx` first.  It is **not** attempted here; what is here is the measurement that says
how big it is and which of §21's items were phantom. -/

theorem ntree_iotaRules_len : ntreeAux.iotaRules.length = 3 := rfl
theorem ntree_iotaRulesRS_len :
    (ntreeAux.iotaRulesRS ntreeRestore ntreeK).length = 3 := rfl

theorem ntree_iotaRules_uvars : ∀ df ∈ ntreeAux.iotaRules, VDefEq.uvars df = 2 := by decide
theorem ntree_iotaRulesRS_uvars :
    ∀ df ∈ ntreeAux.iotaRulesRS ntreeRestore ntreeK, VDefEq.uvars df = 2 := by decide

/-- The strict (C) bridge, refuted at the canonical parameterised block. -/
theorem ntree_iotaRules_bridge_false :
    ((ntreeAux.iotaRules.map (·.substC (ntreeRestore.csubst ntreeAux ntreeK))).map
        VDefEq.type, (ntreeAux.iotaRules.map
        (·.substC (ntreeRestore.csubst ntreeAux ntreeK))).map VDefEq.lhs)
      ≠ ((ntreeAux.iotaRulesRS ntreeRestore ntreeK).map VDefEq.type,
        (ntreeAux.iotaRulesRS ntreeRestore ntreeK).map VDefEq.lhs) := by decide

/-- All **nine** components of (C)'s defeq-tolerant bridge move: for every one of the three
rules, none of `type`/`lhs`/`rhs` is an identity under the substitution.  So (C) at `ntreeAux` is
nine genuine conversions, not a repackaging. -/
theorem ntree_iota_components_ne :
    ∀ p ∈ (ntreeAux.iotaRules.map (·.substC (ntreeRestore.csubst ntreeAux ntreeK))).zip
        (ntreeAux.iotaRulesRS ntreeRestore ntreeK),
      VDefEq.type p.1 ≠ VDefEq.type p.2 ∧ VDefEq.lhs p.1 ≠ VDefEq.lhs p.2 ∧
        VDefEq.rhs p.1 ≠ VDefEq.rhs p.2 := by decide


end InductiveDeclExamples
end Lean4Lean
