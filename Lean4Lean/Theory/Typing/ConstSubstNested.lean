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
`ntreeAux_substC_beta` at the end, which measures exactly what is missing.
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
      T.name ∉ K → C ∈ T.ctors → (C.type D j).substC σ = C.typeR D R j) :
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
      (D.recType j).substC σ = D.recTypeR R j) :
    ∀ c ∈ D.recConstsR R, VConstant.WF e₂ c.2 := by
  intro c hc
  simp only [VInductDecl'.recConstsR, List.mem_map] at hc
  obtain ⟨⟨T, j⟩, hTj, rfl⟩ := hc
  have hT : D.types[j]? = some T := List.mk_mem_zipIdx_iff_getElem?.1 hTj
  have := (hsrc (Lean.mkRecName T.name, ⟨D.recUvars, D.recType j⟩)
    (by simp only [VInductDecl'.recConsts, List.mem_map]; exact ⟨(T, j), hTj, rfl⟩)).substC hσ
  rw [hbridge j T hT] at this
  exact this

/-- **Obligation (C) reduces the same way.**  `hsrc` is `VInductDecl'.iotaRules_WF`. -/
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

/-- **…and the restoration is its contractum**, at the same position and nowhere else. -/
theorem ntreeNode_typeR_reduct :
    ntreeNode.typeR ntreeAux ntreeRestore 0
      = .forallE (.sort (.succ (.param 0)))
          (.forallE (.bvar 0)
            (.forallE (ntreeBody.inst (.bvar 1))
              (.app (.const ``NTree [.param 0]) (.bvar 2)))) := rfl

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
theorem ntreeSubst_WF : ntreeSubst.WF env₂ env₃ 1 := by
  have hfresh := ntreeSubst_fresh h
  refine CSubst.one_WF' (U := 1) (ci := ⟨1, _⟩)
    ⟨trivial, trivial, trivial, Nat.zero_lt_one⟩
    (nlist_const_staged h h₂) ⟨trivial, trivial⟩ (fun {_ _ _} => ntreeVal_val h h₃) ?_ ?_
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
/-- **Obligation (A) at the parameterised nested witness.**  Substitution, then one β-step. -/
theorem ntreeAux_ctorConstsCR_wf :
    ∀ c ∈ ntreeAux.ctorConstsCR ntreeRestore ntreeK, VConstant.WF env₃ c.2 := by
  have henv₂ : env₂.Ordered :=
    VInductDecl'.addIndTypes_ordered henv₁ (ntreeAux_WF h) h₂
  have hct : VIndCtor.WF env₂ ntreeAux 0 (ntreeAux.types.getD 0 default) ntreeNode :=
    (ntreeAux_WF h).ctors env₂ h₂ 0 _ rfl ntreeNode (by simp)
  have hwf : VConstant.WF env₂ ⟨1, ntreeNode.type ntreeAux 0⟩ := hct.constant_wf henv₂
  have hsub := hwf.substC (ntreeSubst_WF h henv₁ h₂ h₃)
  have hres := ntreeNode_beta_bridge h henv₁ h₃ hsub
  intro c hc
  have hlist : ntreeAux.ctorConstsCR ntreeRestore ntreeK
      = [(``NTree.node, ⟨1, ntreeNode.typeR ntreeAux ntreeRestore 0⟩)] := rfl
  rw [hlist] at hc
  simp only [List.mem_singleton] at hc
  subst hc
  exact hres

end

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
variable (hF₃ : F₂.addConstList (nfnAux.recConstsR nfnRestore) = some F₃)

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
    ∀ c ∈ nfnAux.recConstsR nfnRestore, VConstant.WF F₂ c.2 := by
  have hσ := nfnSubstAll_WF₂ h hE₁ hE₂ hF₁ hF₂
  have hsrc := nfn_recConsts_wf h hE₁ hE₂
  have h0 := (hsrc _ (by exact List.Mem.head _)).substC (ci := ⟨1, nfnAux.recType 0⟩) hσ
  have h1 := (hsrc _ (by exact List.Mem.tail _ (List.Mem.head _))).substC
    (ci := ⟨1, nfnAux.recType 1⟩) hσ
  rw [nfn_recType_substC_0] at h0
  rw [nfn_recType_substC_1] at h1
  intro c hc
  have hl : nfnAux.recConstsR nfnRestore
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
variable (hF₃ : F₂.addConstList (nfnAux.recConstsR nfnRestore) = some F₃)

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
      intro hls hls' hfa hlen
      match ls, hlen with
      | [l], _ =>
      cases hfa with | cons hl hfa' =>
      cases hfa' with | nil =>
      rename_i l'
      have hlw : l.WF 1 := hls _ List.mem_cons_self
      have hlw' : l'.WF 1 := hls' _ List.mem_cons_self
      show F₃.IsDefEq 1 Γ (.const ``NFn.rec_1 [l]) (.const ``NFn.rec_1 [l'])
        (VExpr.instL [l] (nfnAux.recTypeR nfnRestore 1))
      exact .constDF hRec1 (by simpa using hlw) (by simpa using hlw') rfl (.cons hl .nil)
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
      F₂.addConstList (nfnAux.recConstsR nfnRestore) = some F₃ := by
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

end InductiveDeclExamples
end Lean4Lean
