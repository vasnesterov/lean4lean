import Lean4Lean.Verify.Inductive.StrengthenFamily

/-!
# Is the `Sort u`-constant condition automatic at the nested restriction step?  **No.**

`Verify/Inductive/StrengthenFamily.lean` §5 proves the bypass of the strengthening hole

    VIndRestore.argsTypedK_of_resultSortInhab
      (C : RestrictStepCfg D R K env e₂ e₁ occ) (H₂ : D.ArgsTypedK K e₂ occ)
      (hb : D.ResultSortInhab env b) : R.ValStrengthen D K e₂ e₁ ∧ D.ArgsTypedK K e₁ occ

hole-free, and its §4 gives four clauses that discharge `hb`.  The fourth,
`VInductDecl'.resultSortInhab_of_const`, subsumes the other three: it needs only

    hc : env.constants c = some ⟨1, .sort (.param 0)⟩

— one universe-polymorphic `Sort u`-valued constant in the pre-block environment, `PUnit.{u}`
being the standard example.  §8 there records the resulting residue as "not a level condition but
an environment one: that the environment at `RestrictStepCfg`'s `e₁`/`e₂` actually declares such a
constant", and leaves it open.

**This file settles it, and the answer is that the condition is not automatic.**

* §0 names the condition (`VEnv.SortWitness`) and states the bypass with it explicit.
* §1 refutes "it always holds": `RestrictStepCfg` does not imply it, and the counterexample is
  not a contrived environment but *the project's own real nested witness* — the environment
  `VEnv.empty.addInduct' listDecl` at which `ntreeAux_restrictStepCfg` is instantiated declares
  no constant whose type is a sort at all.  Refuted at `env`, at `e₂` and at `e₁`.
* §2 shows the condition is satisfiable at a real environment *of the nested step*: `listDecl`'s
  environment with one `Sort u` axiom on top stages `ntreeAux` exactly as before, and the whole
  bypass runs there.  Arity-0, existentially closed, nothing hypothesised.
* §2a tightens the premise from the pre-block `env` to `e₁`, which is the environment
  `StrengthenFamily.lean` §8's residue actually names, and re-runs §1's refutation at `e₁` and at
  `e₂` so that no reading of the residue makes the condition automatic.
* §3 the two vacuity controls: the condition is not trivially true (§1 is the witness that it can
  fail) and not trivially false (§2 is the witness that it can hold), and the substitution it
  feeds is non-degenerate.
* §4 which of the thirteen holes this routes through: **none**.
-/

namespace Lean4Lean

open Lean (Name)

/-! ## §0 The condition, named, and the bypass stated with it

The condition is a fact about the environment alone: no block, no occurrence data, no judgement.
That is what makes it *statable* as a side condition rather than a hidden premise. -/

/-- **THE CONDITION.**  The environment declares one universe-polymorphic `Sort u`-valued
constant.  `PUnit.{u} : Sort u` is such a constant, and its `VConstant` is exactly
`⟨1, .sort (.param 0)⟩`; `VEnv.sortWitCV` (`Theory/Typing/WeakNForward.lean` §4.3) is the same
datum as a `VConstVal`. -/
def VEnv.SortWitness (env : VEnv) : Prop :=
  ∃ c : Name, env.constants c = some ⟨1, .sort (.param 0)⟩

/-- The semantic content: with a sort witness, **every** well-formed level's sort is inhabited by
a closed term, in every context.  `Theory/Typing/WeakNForward.lean` §4.1 is the one-constant
form; this is it packaged at the condition. -/
theorem VEnv.SortWitness.sortInhab {env : VEnv} (hw : env.SortWitness) {U : Nat} {l : VLevel}
    (hl : l.WF U) (Γ : List VExpr) : ∃ e, env.HasType U Γ e (.sort l) :=
  let ⟨_, hc⟩ := hw; ⟨_, VEnv.hasType_const_sortParam hc hl⟩

/-- …hence the block's result sort is inhabited over each member's telescope, which is exactly
`StrengthenFamily.lean` §4's premise, with the witness exhibited. -/
theorem VInductDecl'.resultSortInhab_of_sortWitness {env : VEnv} {D : VInductDecl'}
    (hw : env.SortWitness) (hlv : D.lvl.WF D.uvars) :
    ∃ b : VIndType → VExpr, D.ResultSortInhab env b :=
  let ⟨c, hc⟩ := hw
  ⟨fun _ => .const c [D.lvl], VInductDecl'.resultSortInhab_of_const hc hlv⟩

/-- **THE BYPASS, WITH THE CONDITION EXPLICIT AND NOTHING ELSE HIDDEN.**  This is
`VIndRestore.argsTypedK_of_resultSortInhab` with its one premise replaced by the environment
condition `§0` names, and the block-side residue reduced to level well-formedness — which
`VInductDecl'.WF` supplies at every block the kernel accepts, and which is `decide`-able at a
concrete block.  No hole, no `PiInv`, no `VEnv.HasArgs.of_mkApp`. -/
theorem VIndRestore.argsTypedK_of_sortWitness {D : VInductDecl'} {R : VIndRestore}
    {K : List Name} {env e₂ e₁ : VEnv} {occ : Nat → VNestedOcc}
    (C : RestrictStepCfg D R K env e₂ e₁ occ) (H₂ : D.ArgsTypedK K e₂ occ)
    (hw : env.SortWitness) (hlv : D.lvl.WF D.uvars) :
    R.ValStrengthen D K e₂ e₁ ∧ D.ArgsTypedK K e₁ occ :=
  let ⟨_, hb⟩ := VInductDecl'.resultSortInhab_of_sortWitness (D := D) hw hlv
  VIndRestore.argsTypedK_of_resultSortInhab C H₂ hb

/-! ## §1 The verdict: the condition is **not** automatic

Three statements, in increasing sharpness.

* (a) `addInduct'` inverted at one name — a constant of the extended environment either is one the
  block declared or was already there.  The `addConstList` form is
  `VEnv.addConstList_constants_inv` (`StrengthenFamily.lean` §2); the missing step is that
  `addIndRules` does not touch `constants`.
* (b) **The real nested witness has no sort-typed constant at all.**  `env₁ = VEnv.empty.addInduct'
  listDecl` — the environment `ntreeAux_restrictStepCfg` is instantiated at — declares exactly
  `List`, `List.nil`, `List.cons` and `List.rec`, and every one of those four types is a
  `.forallE`.  So *no* constant of `env₁` has a type of the form `Sort l`, for any level and any
  universe count: the condition fails there for the strongest possible reason.
* (c) **Hence `RestrictStepCfg` does not imply it**, at any of its three environments.  This is
  the honest answer to "is it (i) always, (ii) mildly hypothesised, or (iii) not at all": it is
  (ii)/(iii) — a genuine side condition, refuted at the tree's own parameterised nested witness
  rather than at a manufactured environment. -/

/-- The decidable test §1(b) needs.  A `∀ n l, ci ≠ ⟨n, .sort l⟩` is not decidable as written
(the level is quantified); its `Bool` shadow is, and one `decide` over `listDecl.allConsts`
settles the whole environment. -/
def VConstant.typeIsSort (ci : VConstant) : Bool :=
  match ci.type with
  | .sort _ => true
  | _ => false

theorem VConstant.typeIsSort_eq_true {n : Nat} {l : VLevel} :
    (⟨n, .sort l⟩ : VConstant).typeIsSort = true := rfl

/-- **§1(a) `addInduct'` inverted at one name.** -/
theorem VEnv.addInduct'_constants_inv {env env' : VEnv} {D : VInductDecl'} {c : Name}
    {ci : VConstant} (h : env.addInduct' D = some env') (hc : env'.constants c = some ci) :
    (c, ci) ∈ D.allConsts ∨ env.constants c = some ci := by
  rw [VEnv.addInduct'_eq, Option.map_eq_some_iff] at h
  obtain ⟨e, h1, rfl⟩ := h
  rw [VEnv.addIndRules_constants] at hc
  exact VEnv.addConstList_constants_inv h1 hc

namespace InductiveDeclExamples

/-- `listDecl` declares nothing whose type is a sort — one `decide` over the four entries. -/
theorem listDecl_allConsts_no_sort :
    ∀ p ∈ listDecl.allConsts, p.2.typeIsSort = false := by decide

/-- **§1(b) THE REAL NESTED WITNESS HAS NO SORT-TYPED CONSTANT.**  Not merely "no `PUnit`-shaped
one": no constant at all whose type is a `Sort`, at any universe count and any level. -/
theorem listEnv_no_sort_const {env₁ : VEnv} (h : VEnv.empty.addInduct' listDecl = some env₁)
    {c : Name} {n : Nat} {l : VLevel} : env₁.constants c ≠ some ⟨n, .sort l⟩ := by
  intro hc
  rcases VEnv.addInduct'_constants_inv h hc with hm | hm
  · have := listDecl_allConsts_no_sort _ hm
    rw [VConstant.typeIsSort_eq_true] at this
    exact absurd this (by simp)
  · exact absurd hm nofun

/-- …so the condition fails at the pre-block environment of the parameterised nested witness. -/
theorem listEnv_not_sortWitness {env₁ : VEnv} (h : VEnv.empty.addInduct' listDecl = some env₁) :
    ¬ env₁.SortWitness := fun ⟨_, hc⟩ => listEnv_no_sort_const h hc

end InductiveDeclExamples

/-- **§1(c) THE CONDITION IS NOT A CONSEQUENCE OF `RestrictStepCfg`.**  Refuted at the
configuration `RestrictStep.lean` §3 exhibits — `ntreeAux`, `np = 1`, `uvars = 1`, the block Lean's
own kernel runs the nested elimination on.  So `VIndRestore.argsTypedK_of_sortWitness`'s `hw` is a
real hypothesis and the bypass is **conditional**. -/
theorem not_sortWitness_of_restrictStepCfg :
    ¬ ∀ (D : VInductDecl') (R : VIndRestore) (K : List Name) (env e₂ e₁ : VEnv)
        (occ : Nat → VNestedOcc), RestrictStepCfg D R K env e₂ e₁ occ → env.SortWitness := by
  intro H
  obtain ⟨env₁, env₂, -, env₃, -, h, h₂, -, h₃, -⟩ := InductiveDeclExamples.ntree_stage₂_exists
  exact InductiveDeclExamples.listEnv_not_sortWitness h
    (H _ _ _ _ _ _ _ (InductiveDeclExamples.ntreeAux_restrictStepCfg h h₂ h₃))

/-! ## §2 The condition is satisfiable **at the nested step itself**

§1 says the condition can fail; a condition that could only fail would be worthless.  This section
exhibits it holding at a real configuration of the *same* nested block: `listDecl`'s environment
with one `Sort u` axiom declared on top of it.  Nothing about `ntreeAux` changes — the axiom's name
is disjoint from every name the block introduces, so the two staging equations still hold and every
field of `RestrictStepCfg` survives.

Working rule "instantiate, don't admire": the section ends with an **arity-0** existentially closed
theorem carrying the configuration, the condition, and both halves of the bypass's conclusion.

The two monotonicity steps that are needed and were not in the tree (`OccursN`, `KFresh` under one
`addConst`) are proved here; both are one-liners once written down, and neither is specific to this
witness. -/

/-- `VNestedOcc.OccursN` is monotone in the environment: every clause is either an equation between
lengths, a `Declared`, a `constants` lookup, or the environment-free spine clause. -/
theorem VNestedOcc.OccursN.mono {N : VNestedOcc} {env env' : VEnv} (ho : N.OccursN env)
    (hle : env ≤ env') : N.OccursN env' where
  hist := ho.hist.mono hle
  idx_lt := ho.idx_lt
  lvls_len := ho.lvls_len
  args_len := ho.args_len
  ty_const := hle.constants ho.ty_const
  ctor_params := ho.ctor_params
  ctor_const := fun C hC => hle.constants (ho.ctor_const C hC)
  args_noNested := ho.args_noNested

/-- `VEnv.ConstsClosedC` survives one `addConst` whose declared type is a sort — a sort mentions no
constants, so the new entry is closed for free and the old ones only need `contains` to grow.
(`ConstsClosedC` is *not* monotone in general, which is why this is stated for the shape at hand.) -/
theorem VEnv.ConstsClosedC.addConst_sort {env env' : VEnv} {c : Name} {n : Nat} {l : VLevel}
    (hcc : env.ConstsClosedC) (hadd : env.addConst c ⟨n, .sort l⟩ = some env') :
    env'.ConstsClosedC := by
  intro m ci hm
  by_cases hcm : c = m
  · subst hcm
    have he : env'.constants c = some ⟨n, .sort l⟩ := by
      rw [VEnv.addConst_constants_eq hadd]; simp
    rw [he] at hm; cases hm; exact trivial
  · rw [VEnv.addConst_constants_ne hadd hcm] at hm
    exact (hcc hm).mono fun _ hh => (VEnv.addConst_le hadd).contains hh

/-- `VInductDecl'.KFresh` likewise, provided the added name is not a companion name. -/
theorem VInductDecl'.KFresh.addConst_sort {D : VInductDecl'} {K : List Name} {env env' : VEnv}
    {occ : Nat → VNestedOcc} {c : Name} {n : Nat} {l : VLevel} (hf : D.KFresh K env occ)
    (hadd : env.addConst c ⟨n, .sort l⟩ = some env') (hcK : c ∉ K) : D.KFresh K env' occ where
  constsClosedC := VEnv.ConstsClosedC.addConst_sort hf.constsClosedC hadd
  notContains := by
    intro m hm ⟨ci, hci⟩
    by_cases hcm : c = m
    · subst hcm; exact hcK hm
    · rw [VEnv.addConst_constants_ne hadd hcm] at hci
      exact hf.notContains m hm ⟨ci, hci⟩
  argsNoK := hf.argsNoK

namespace InductiveDeclExamples

/-- The five names the `NTree` step introduces stay fresh after one `sortWit` axiom: `sortWit` is
none of them, and `listDecl` declares none of them either. -/
theorem ntree_sortWit_fresh {env₀ env₁ : VEnv} (h : VEnv.empty.addInduct' listDecl = some env₀)
    (hadd : env₀.addConst `sortWit ⟨1, .sort (.param 0)⟩ = some env₁) :
    ∀ n ∈ [``NTree, `_nested.List_1, ``NTree.node, `_nested.List_1.nil, `_nested.List_1.cons],
      env₁.constants n = none := by
  intro n hn
  rw [VEnv.addConst_constants_ne hadd (by revert hn; revert n; decide),
    VEnv.addInduct'_constants_of_not_mem h (by revert hn; revert n; decide)]
  rfl

/-- **THE EXTENDED STAGING EXISTS.**  `listDecl`, then one `Sort u` axiom, then the two `NTree`
stagings — the same two `addConstList`s `ntree_stage₂_exists` supplies, over the extended
environment. -/
theorem ntree_sortWit_stage_exists :
    ∃ env₀ env₁ env₂ env₃ : VEnv,
      VEnv.empty.addInduct' listDecl = some env₀ ∧
      env₀.addConst `sortWit ⟨1, .sort (.param 0)⟩ = some env₁ ∧
      env₁.addIndTypes ntreeAux = some env₂ ∧
      env₁.addConstList (ntreeAux.typeConstsC ntreeK) = some env₃ := by
  obtain ⟨env₀, h⟩ : ∃ e, VEnv.empty.addInduct' listDecl = some e := ⟨_, rfl⟩
  obtain ⟨env₁, hadd⟩ : ∃ e, env₀.addConst `sortWit ⟨1, .sort (.param 0)⟩ = some e :=
    VEnv.addConst_eq_none (by rw [VEnv.addInduct'_constants_of_not_mem h (by decide)]; rfl)
  have hfresh := ntree_sortWit_fresh h hadd
  obtain ⟨env₂, h₂⟩ : ∃ e, env₁.addIndTypes ntreeAux = some e :=
    VEnv.addConstList_eq_some_iff.2
      ⟨fun n hn => hfresh n (by revert hn; revert n; decide), by decide⟩
  obtain ⟨env₃, h₃⟩ : ∃ e, env₁.addConstList (ntreeAux.typeConstsC ntreeK) = some e :=
    VEnv.addConstList_eq_some_iff.2
      ⟨fun n hn => hfresh n (by revert hn; revert n; decide), by decide⟩
  exact ⟨env₀, env₁, env₂, env₃, h, hadd, h₂, h₃⟩

/-- The sort witness is where we put it. -/
theorem ntree_sortWit_const {env₀ env₁ : VEnv}
    (hadd : env₀.addConst `sortWit ⟨1, .sort (.param 0)⟩ = some env₁) :
    env₁.constants `sortWit = some ⟨1, .sort (.param 0)⟩ := by
  rw [VEnv.addConst_constants_eq hadd]; simp

/-- …i.e. the condition holds at the extended environment. -/
theorem ntree_sortWitness {env₀ env₁ : VEnv}
    (hadd : env₀.addConst `sortWit ⟨1, .sort (.param 0)⟩ = some env₁) : env₁.SortWitness :=
  ⟨_, ntree_sortWit_const hadd⟩

/-- **`Built` at the extended environment**, from `ntreeAux_built` and §2's two monotonicity
lemmas.  The seven name/member clauses are environment-free and come across verbatim. -/
theorem ntreeAux_built_sortWit {env₀ env₁ : VEnv}
    (h : VEnv.empty.addInduct' listDecl = some env₀)
    (hadd : env₀.addConst `sortWit ⟨1, .sort (.param 0)⟩ = some env₁) :
    ntreeAux.Built ntreeRestore ntreeK env₁ (fun _ => listOcc) where
  member := (ntreeAux_built h).member
  occurs := fun j T hT hK =>
    ((ntreeAux_built h).occurs j T hT hK).mono (VEnv.addConst_le hadd)
  tyName := (ntreeAux_built h).tyName
  tyLvls := (ntreeAux_built h).tyLvls
  tyArgs := (ntreeAux_built h).tyArgs
  ctorName_inv := (ntreeAux_built h).ctorName_inv
  own := (ntreeAux_built h).own
  nodup := (ntreeAux_built h).nodup
  kfresh := (ntreeAux_built h).kfresh.addConst_sort hadd (by decide)

/-- **THE CONFIGURATION AT THE EXTENDED ENVIRONMENT.**  Field for field the same as
`ntreeAux_restrictStepCfg`, with `Ordered` extended by one `VEnv.Ordered.const` step and `Built`
by §2. -/
theorem ntreeAux_restrictStepCfg_sortWit {env₀ env₁ env₂ env₃ : VEnv}
    (h : VEnv.empty.addInduct' listDecl = some env₀)
    (hadd : env₀.addConst `sortWit ⟨1, .sort (.param 0)⟩ = some env₁)
    (h₂ : env₁.addIndTypes ntreeAux = some env₂)
    (h₃ : env₁.addConstList (ntreeAux.typeConstsC ntreeK) = some env₃) :
    RestrictStepCfg ntreeAux ntreeRestore ntreeK env₁ env₂ env₃ (fun _ => listOcc) where
  ordered := .const (listEnv_ordered h) (VEnv.sortWitCV_wf _) hadd
  ordered₁ := VEnv.addConstList_ordered
    (.const (listEnv_ordered h) (VEnv.sortWitCV_wf _) hadd)
    (VEnv.addInductR_typeConstsC_wf ntreeAux_WF') h₃
  wf := ntreeAux_WF'
  built := ntreeAux_built_sortWit h hadd
  fresh := by
    rw [ntree_csubstTy]
    intro c ci hc
    cases hn : ntreeSubst c with
    | none => rfl
    | some t =>
      have hce : c = `_nested.List_1 := by
        by_cases he : c = `_nested.List_1
        · exact he
        · rw [ntreeSubst_of_ne he] at hn; exact absurd hn nofun
      subst hce
      rw [ntree_sortWit_fresh h hadd _ (by decide)] at hc
      exact absurd hc nofun
  closed := ntree_csubstTy_closed
  stage₂ := h₂
  stage₁ := h₃
  lvls := fun j _ _ _ => by
    rw [show ntreeRestore.tyLvls j = [VLevel.param 0] from rfl]; decide

end InductiveDeclExamples

namespace InductiveDeclExamples

/-- The junk witness the *sort-witness* route builds at `ntreeAux`: the axiom instantiated at the
block's own result level.  Compare `StrengthenFamily.lean` §6's `ntreeJunk = fun _ => .sort
(.param 0)`, which is what the *successor* clause builds; the two are different terms, so this
witness really is exercising the fourth clause and not the first. -/
def ntreeSortWitJunk : VIndType → VExpr := fun _ => .const `sortWit [.succ (.param 0)]

/-- **THE CONDITION, AND THE WHOLE BYPASS, AT THE PARAMETERISED NESTED WITNESS — ARITY 0.**

Everything is existentially closed: the pre-block environment (`listDecl` plus one `Sort u`
axiom), the two staging environments, the configuration, the condition `VEnv.SortWitness`, the
datum at `e₂`, the inhabitation data, and both halves of the bypass's conclusion — node 5
(`ValStrengthen`) and node 1 (the datum at `e₁`).  Nothing is hypothesised, and the block is
`ntreeAux`: `uvars = 1`, `params = [.sort (.succ (.param 0))]`, `np = 1`, the parameterised
nested block, **not** the degenerate `nfnAux` (`uvars = 0`, `params = []`). -/
theorem ntreeAux_sortWitness_bypass :
    ∃ env₁ env₂ env₃ : VEnv,
      RestrictStepCfg ntreeAux ntreeRestore ntreeK env₁ env₂ env₃ (fun _ => listOcc) ∧
      env₁.SortWitness ∧
      ntreeAux.ArgsTypedK ntreeK env₂ (fun _ => listOcc) ∧
      ntreeAux.ResultSortInhab env₁ ntreeSortWitJunk ∧
      ntreeAux.CompanionVals ntreeK env₂ env₃ (ntreeAux.junkSubst ntreeK ntreeSortWitJunk) ∧
      ntreeRestore.ValStrengthen ntreeAux ntreeK env₂ env₃ ∧
      ntreeAux.ArgsTypedK ntreeK env₃ (fun _ => listOcc) := by
  obtain ⟨env₀, env₁, env₂, env₃, h, hadd, h₂, h₃⟩ := ntree_sortWit_stage_exists
  have C := ntreeAux_restrictStepCfg_sortWit h hadd h₂ h₃
  have H₂ := ntreeAux_argsTypedK_of_wf (env₁ := env₁) h₂
  have hb : ntreeAux.ResultSortInhab env₁ ntreeSortWitJunk :=
    VInductDecl'.resultSortInhab_of_const (ntree_sortWit_const hadd) (by decide)
  obtain ⟨h5, h1⟩ := VIndRestore.argsTypedK_of_resultSortInhab C H₂ hb
  exact ⟨env₁, env₂, env₃, C, ntree_sortWitness hadd, H₂, hb,
    ntreeAux.companionVals_junk C hb, h5, h1⟩

/-- **AND NODE 5 IS NOT VACUOUS AT THE EXTENDED WITNESS EITHER.**  `ValStrengthen` is a `∀` over
`csubstTy`'s domain; here the companion name is in that domain, `env₂` declares it, and the
judgement moved is the concrete typing `ntreeVal : Type u → Type u`, landed at `env₃`.  So the
`Sort u` axiom has not made the conclusion cheap. -/
theorem ntreeAux_sortWit_valStrengthen_nonvacuous :
    ∃ env₂ env₃ : VEnv,
      ntreeRestore.csubstTy ntreeAux ntreeK `_nested.List_1 = some ntreeVal ∧
      env₂.constants `_nested.List_1
        = some ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩ ∧
      ntreeRestore.ValStrengthen ntreeAux ntreeK env₂ env₃ ∧
      env₃.HasType 1 [] ntreeVal
        (.forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))) := by
  obtain ⟨env₀, env₁, env₂, env₃, h, hadd, h₂, h₃⟩ := ntree_sortWit_stage_exists
  have C := ntreeAux_restrictStepCfg_sortWit h hadd h₂ h₃
  have H₂ := ntreeAux_argsTypedK_of_wf (env₁ := env₁) h₂
  have hd := ntree_csubst_ty_val
  have hc := nlist_const_staged h₂
  obtain ⟨h5, -⟩ := VIndRestore.argsTypedK_of_sortWitness C H₂ (ntree_sortWitness hadd) (by decide)
  exact ⟨env₂, env₃, hd, hc, h5, h5 hd hc (VIndRestore.valAt_e₂ C H₂ hd hc)⟩

/-- …and the same read off the packaged form `VIndRestore.argsTypedK_of_sortWitness`, so that §0's
statement is exhibited satisfiable at the witness and not only its unfolded ingredients. -/
theorem ntreeAux_argsTypedK_of_sortWitness :
    ∃ env₁ env₂ env₃ : VEnv,
      RestrictStepCfg ntreeAux ntreeRestore ntreeK env₁ env₂ env₃ (fun _ => listOcc) ∧
      env₁.SortWitness ∧
      ntreeRestore.ValStrengthen ntreeAux ntreeK env₂ env₃ ∧
      ntreeAux.ArgsTypedK ntreeK env₃ (fun _ => listOcc) := by
  obtain ⟨env₀, env₁, env₂, env₃, h, hadd, h₂, h₃⟩ := ntree_sortWit_stage_exists
  have C := ntreeAux_restrictStepCfg_sortWit h hadd h₂ h₃
  obtain ⟨h5, h1⟩ := VIndRestore.argsTypedK_of_sortWitness C
    (ntreeAux_argsTypedK_of_wf (env₁ := env₁) h₂) (ntree_sortWitness hadd) (by decide)
  exact ⟨env₁, env₂, env₃, C, ntree_sortWitness hadd, h5, h1⟩

end InductiveDeclExamples


/-! ## §2a The witness need only be in `e₁` — the brief's phrasing, made exact

`StrengthenFamily.lean` §8 asks about "the environment at `RestrictStepCfg`'s `e₁`/`e₂`", while
`ResultSortInhab` is stated at the **pre-block** `env` and moved up by `.mono C.le₁`.  Those are not
the same condition, and the `e₁` form is strictly weaker, so it is the one worth having: this
section reproves the route with inhabitation demanded only at `e₁`.

The change is local: `VInductDecl'.junkVal_hasType` types the junk telescope at `env` and then
monotonises the *whole* judgement; instead, monotonise the two ingredients that come from `D.WF env`
(the canonical-type defeq and the index context) and take the result-sort witness at `e₁`.  Nothing
else in `StrengthenFamily.lean` §2–§3 depends on where the witness came from.

Note what this does *not* buy at a nested block: `e₁` is `env` plus the block's **non**-companion
type constants, whose declared types are `Π params indices, Sort D.lvl` — a sort only when the
block has no parameters and the member no indices.  At `ntreeAux` (params `[Type u]`) they are
`.forallE`s, so the `e₁` form fails there exactly as the `env` form does (§1). -/

/-- `VInductDecl'.junkVal_hasType` with the result-sort witness demanded at the **larger**
environment.  `D.WF env` is still used, but only for the two ingredients that monotonise. -/
theorem VInductDecl'.junkVal_hasType₁ {env e₁ : VEnv} {D : VInductDecl'} (hD : D.WF env)
    (hle : env ≤ e₁) {b : VIndType → VExpr} (hb : D.ResultSortInhab e₁ b)
    {T : VIndType} (hT : T ∈ D.types) :
    e₁.HasType D.uvars [] (D.junkVal b T) T.type := by
  have hTW := hD.types T hT
  have hctx : (D.params ++ T.indices).reverse ++ ([] : List VExpr)
      = T.indices.reverse ++ D.params.reverse := by
    rw [List.append_nil, List.reverse_append]
  obtain ⟨_, hcanon⟩ := hTW.canon
  refine VEnv.IsDefEq.defeqDF (hcanon.symm.mono hle) (VEnv.HasType.mkLams ?_ ?_)
  · rw [hctx]; exact OnCtx.mono (fun h => h.mono hle) hTW.indices
  · rw [hctx]; exact hb T hT

/-- `VInductDecl'.companionVals_junk` at the `e₁` form of the premise. -/
theorem VInductDecl'.companionVals_junk₁ {D : VInductDecl'} {R : VIndRestore} {K : List Name}
    {env e₂ e₁ : VEnv} {occ : Nat → VNestedOcc} (C : RestrictStepCfg D R K env e₂ e₁ occ)
    {b : VIndType → VExpr} (hb : D.ResultSortInhab e₁ b) :
    D.CompanionVals K e₂ e₁ (D.junkSubst K b) := by
  have h₂ := C.stage₂
  rw [VEnv.addIndTypes] at h₂
  have hnd : (D.types.map (·.name)).Nodup := by
    have := (VEnv.addConstList_fresh h₂).2
    rwa [VInductDecl'.typeConsts, List.map_map] at this
  have hval : ∀ {c : Name} {s : VExpr} {ci : VConstant}, D.junkSubst K b c = some s →
      e₂.constants c = some ci → e₁.HasType ci.uvars [] s ci.type := by
    intro c s ci hd hc
    obtain ⟨T, hT, rfl, -, rfl⟩ := VInductDecl'.junkSubst_dom hd
    rw [VEnv.addConstList_constants h₂ (T.name, ⟨D.uvars, T.type⟩)
      (List.mem_map.2 ⟨T, hT, rfl⟩)] at hc
    cases hc
    exact VInductDecl'.junkVal_hasType₁ C.wf C.le₁ hb hT
  refine { closed := ?_, dom := ?_, covers := ?_, val := hval }
  · intro c s hd
    obtain ⟨T, hT, rfl, hK, rfl⟩ := VInductDecl'.junkSubst_dom hd
    exact VEnv.IsDefEq.closedN C.ordered₁
      (hval hd (VEnv.addConstList_constants h₂ (T.name, ⟨D.uvars, T.type⟩)
        (List.mem_map.2 ⟨T, hT, rfl⟩))) trivial
  · intro c hd
    cases hs : D.junkSubst K b c with
    | none => exact absurd hs hd
    | some s => obtain ⟨T, -, rfl, hK, -⟩ := VInductDecl'.junkSubst_dom hs; exact hK
  · intro T hT hK
    rw [VInductDecl'.junkSubst_eq_some hnd hT hK]; exact nofun

/-- **THE BYPASS, WITH INHABITATION AT `e₁`.**  Strictly weaker premise than
`VIndRestore.argsTypedK_of_resultSortInhab`'s, same conclusion, still hole-free. -/
theorem VIndRestore.argsTypedK_of_resultSortInhab₁ {D : VInductDecl'} {R : VIndRestore}
    {K : List Name} {env e₂ e₁ : VEnv} {occ : Nat → VNestedOcc} {b : VIndType → VExpr}
    (C : RestrictStepCfg D R K env e₂ e₁ occ) (H₂ : D.ArgsTypedK K e₂ occ)
    (hb : D.ResultSortInhab e₁ b) :
    R.ValStrengthen D K e₂ e₁ ∧ D.ArgsTypedK K e₁ occ :=
  ⟨VIndRestore.valStrengthen_of_companionVals C H₂ (D.companionVals_junk₁ C hb),
   VIndRestore.argsTypedK_of_companionVals C H₂ (D.companionVals_junk₁ C hb)⟩

/-- …and the same from the environment condition at `e₁`. -/
theorem VIndRestore.argsTypedK_of_sortWitness₁ {D : VInductDecl'} {R : VIndRestore}
    {K : List Name} {env e₂ e₁ : VEnv} {occ : Nat → VNestedOcc}
    (C : RestrictStepCfg D R K env e₂ e₁ occ) (H₂ : D.ArgsTypedK K e₂ occ)
    (hw : e₁.SortWitness) (hlv : D.lvl.WF D.uvars) :
    R.ValStrengthen D K e₂ e₁ ∧ D.ArgsTypedK K e₁ occ :=
  let ⟨_, hb⟩ := VInductDecl'.resultSortInhab_of_sortWitness (D := D) hw hlv
  VIndRestore.argsTypedK_of_resultSortInhab₁ C H₂ hb

/-- The `env` form implies the `e₁` form, so §0's statement is a corollary of §2a's and the
ordering between the two conditions is recorded rather than assumed. -/
theorem VEnv.SortWitness.mono {env e₁ : VEnv} (hw : env.SortWitness) (hle : env ≤ e₁) :
    e₁.SortWitness := let ⟨_, hc⟩ := hw; ⟨_, hle.constants hc⟩

namespace InductiveDeclExamples

/-- **AND THE `e₁` FORM FAILS AT THE REAL WITNESS TOO.**  `e₁` is `env₁` plus `NTree`, whose
declared type is `Type u → Type u`; so refuting the condition at `env` (§1) does refute it at `e₁`,
and the brief's "at `e₁`/`e₂`" phrasing gets the same answer. -/
theorem listEnv₃_not_sortWitness {env₁ env₃ : VEnv}
    (h : VEnv.empty.addInduct' listDecl = some env₁)
    (h₃ : env₁.addConstList (ntreeAux.typeConstsC ntreeK) = some env₃) : ¬ env₃.SortWitness := by
  rintro ⟨c, hc⟩
  rcases VEnv.addConstList_constants_inv h₃ hc with hm | hm
  · have hns : ∀ p ∈ ntreeAux.typeConstsC ntreeK, p.2.typeIsSort = false := by decide
    have hb := hns _ hm
    rw [VConstant.typeIsSort_eq_true] at hb
    exact absurd hb (by simp)
  · exact listEnv_no_sort_const h hm

/-- …and at `e₂` (the `addIndTypes` staging), for the same reason: both `NTree` and the companion
member are declared at `Type u → Type u`. -/
theorem listEnv₂_not_sortWitness {env₁ env₂ : VEnv}
    (h : VEnv.empty.addInduct' listDecl = some env₁)
    (h₂ : env₁.addIndTypes ntreeAux = some env₂) : ¬ env₂.SortWitness := by
  rintro ⟨c, hc⟩
  rw [VEnv.addIndTypes] at h₂
  rcases VEnv.addConstList_constants_inv h₂ hc with hm | hm
  · have hns : ∀ p ∈ ntreeAux.typeConsts, p.2.typeIsSort = false := by decide
    have hb := hns _ hm
    rw [VConstant.typeIsSort_eq_true] at hb
    exact absurd hb (by simp)
  · exact listEnv_no_sort_const h hm

end InductiveDeclExamples

/-- **§1(c) AT ALL THREE ENVIRONMENTS.**  The condition is not a consequence of `RestrictStepCfg`
at `env`, at `e₂`, or at `e₁` — so no reading of `StrengthenFamily.lean` §8's residue makes it
automatic. -/
theorem not_sortWitness_of_restrictStepCfg₃ :
    (¬ ∀ (D : VInductDecl') (R : VIndRestore) (K : List Name) (env e₂ e₁ : VEnv)
        (occ : Nat → VNestedOcc), RestrictStepCfg D R K env e₂ e₁ occ → env.SortWitness) ∧
    (¬ ∀ (D : VInductDecl') (R : VIndRestore) (K : List Name) (env e₂ e₁ : VEnv)
        (occ : Nat → VNestedOcc), RestrictStepCfg D R K env e₂ e₁ occ → e₂.SortWitness) ∧
    (¬ ∀ (D : VInductDecl') (R : VIndRestore) (K : List Name) (env e₂ e₁ : VEnv)
        (occ : Nat → VNestedOcc), RestrictStepCfg D R K env e₂ e₁ occ → e₁.SortWitness) := by
  obtain ⟨env₁, env₂, -, env₃, -, h, h₂, -, h₃, -⟩ := InductiveDeclExamples.ntree_stage₂_exists
  have C := InductiveDeclExamples.ntreeAux_restrictStepCfg h h₂ h₃
  exact ⟨fun H => InductiveDeclExamples.listEnv_not_sortWitness h (H _ _ _ _ _ _ _ C),
    fun H => InductiveDeclExamples.listEnv₂_not_sortWitness h h₂ (H _ _ _ _ _ _ _ C),
    fun H => InductiveDeclExamples.listEnv₃_not_sortWitness h h₃ (H _ _ _ _ _ _ _ C)⟩

end Lean4Lean

namespace Lean4Lean

/-! ## §3 Vacuity, both ways

The brief asks for both directions, and both matter here.

* **Not trivially true.**  If the condition held at every environment for a cheap reason it would
  not be a condition and the bypass would be unconditional.  It does not: §1(b) refutes it at the
  tree's own nested witness, and `not_sortWitness_of_wf` refutes it from `VEnv.WF` alone.  So
  §0's `hw` is load-bearing.
* **Not trivially false.**  §2's arity-0 theorems exhibit it holding at a real configuration of the
  same nested block, with the whole bypass run there.
* **Not degenerate as a substitution.**  A `CompanionVals` whose `σ` were everywhere `none` would
  make `StrengthenFamily.lean` §2's transport the identity.  It is not, and the value it installs
  is neither the intended `ntreeVal` nor the successor clause's `ntreeJunk`, so the fourth clause
  really is the one firing. -/

/-- **(a) The condition does not follow from environment well-formedness.**  `VEnv.empty` is `WF`
and has no constants at all, so no cheap environment invariant delivers the condition. -/
theorem not_sortWitness_of_wf : ¬ ∀ env : VEnv, VEnv.WF env → env.SortWitness := by
  intro H
  obtain ⟨_, hc⟩ := H VEnv.empty ⟨[], .empty⟩
  exact absurd hc nofun

namespace InductiveDeclExamples

/-- **(c) The substitution's domain is not empty at the extended witness**, and the value is the
sort-witness axiom's λ-telescope. -/
theorem ntree_sortWitJunk_dom_val :
    ntreeAux.junkSubst ntreeK ntreeSortWitJunk `_nested.List_1
      = some (.lam (.sort (.succ (.param 0))) (.const `sortWit [.succ (.param 0)])) := by decide

/-- …and it is **not** the intended value `ntreeVal`, so §2's transport is not the sandwich of
`RestrictCompanion.lean` §3 in disguise. -/
theorem ntree_sortWitJunkVal_ne_tyVal :
    ntreeAux.junkVal ntreeSortWitJunk (ntreeAux.types.getD 1 default) ≠ ntreeVal := by decide

/-- …and it is not `StrengthenFamily.lean` §6's successor-clause value either: the fourth
discharge clause installs a genuinely different inhabitant. -/
theorem ntree_sortWitJunk_ne_ntreeJunk :
    ntreeSortWitJunk (ntreeAux.types.getD 1 default)
      ≠ ntreeJunk (ntreeAux.types.getD 1 default) := by decide

end InductiveDeclExamples

/-! ## §4 Which of the thirteen holes this routes through: **none**

Every declaration in this file is graded below.  `#print axioms` and `scripts/exists.lean` agree:
nothing here reaches `sorryAx`, so the bypass of `Theory/Typing/UniqueTyping.lean`'s strengthening
`sorry` stays a bypass — restating its side condition has not smuggled the hole back in through the
condition.  Nothing here uses `VEnv.HasArgs.of_mkApp` or any `PiInv`; the only transports are
`VEnv.IsDefEq.substC` (inherited from `StrengthenFamily.lean` §2) and `VEnv.IsDefEq.constDF`
(inherited from `WeakNForward.lean` §4.1).

## §5 The verdict, stated once

**The bypass needs exactly one satisfiable hypothesis, and it is an environment condition.**

* It is *not* implied by `RestrictStepCfg` (`not_sortWitness_of_restrictStepCfg`), and the
  counterexample is the project's own parameterised nested witness, not a manufactured
  environment: `VEnv.empty.addInduct' listDecl` declares no constant whose type is a sort at all
  (`listEnv_no_sort_const`).
* It *is* satisfiable at a real configuration of the same nested block
  (`ntreeAux_sortWitness_bypass`, arity 0), and holds in any environment declaring `PUnit.{u}` —
  which the standard prelude does, so in practice it is discharged by inspection of the
  environment rather than by a proof about the block.
* So `StrengthenFamily.lean` §8's residue does **not** close unconditionally.  What it closes to is
  `VEnv.SortWitness`: one existential over the environment's constant table, decidable at any
  concrete environment, with no judgement and no level side condition on the block beyond
  `D.lvl.WF D.uvars` — which `VInductDecl'.WF` already carries wherever the kernel accepted the
  block.

**What is NOT claimed.**  (i) That `VEnv.SortWitness` is *necessary* — it is sufficient, and §1's
counterexample refutes only its derivability from `RestrictStepCfg`, not the bypass at that
environment by some other route (at `ntreeAux` in particular the *successor* clause fires, so the
bypass does hold there; what fails is only this clause's premise).  (ii) That every environment
`Lean4Lean.addDecl` can reach declares such a constant — the counterexample environment is reached
by declaring `List` over the empty environment, which is a legitimate history, so the answer to
"can such an environment arise" is **yes**.  (iii) Anything about the flip,
`tryEtaStructCore.WF`, `isDefEqUnitLike.WF`, or the other twelve holes. -/

end Lean4Lean

#print axioms Lean4Lean.VEnv.SortWitness
#print axioms Lean4Lean.VConstant.typeIsSort
#print axioms Lean4Lean.VConstant.typeIsSort_eq_true
#print axioms Lean4Lean.InductiveDeclExamples.ntreeSortWitJunk
#print axioms Lean4Lean.VInductDecl'.junkVal_hasType₁
#print axioms Lean4Lean.VInductDecl'.companionVals_junk₁
#print axioms Lean4Lean.VIndRestore.argsTypedK_of_resultSortInhab₁
#print axioms Lean4Lean.VIndRestore.argsTypedK_of_sortWitness₁
#print axioms Lean4Lean.VEnv.SortWitness.mono
#print axioms Lean4Lean.InductiveDeclExamples.listEnv₂_not_sortWitness
#print axioms Lean4Lean.InductiveDeclExamples.listEnv₃_not_sortWitness
#print axioms Lean4Lean.not_sortWitness_of_restrictStepCfg₃
#print axioms Lean4Lean.VEnv.SortWitness.sortInhab
#print axioms Lean4Lean.VInductDecl'.resultSortInhab_of_sortWitness
#print axioms Lean4Lean.VIndRestore.argsTypedK_of_sortWitness
#print axioms Lean4Lean.VEnv.addInduct'_constants_inv
#print axioms Lean4Lean.InductiveDeclExamples.listDecl_allConsts_no_sort
#print axioms Lean4Lean.InductiveDeclExamples.listEnv_no_sort_const
#print axioms Lean4Lean.InductiveDeclExamples.listEnv_not_sortWitness
#print axioms Lean4Lean.not_sortWitness_of_restrictStepCfg
#print axioms Lean4Lean.VNestedOcc.OccursN.mono
#print axioms Lean4Lean.VEnv.ConstsClosedC.addConst_sort
#print axioms Lean4Lean.VInductDecl'.KFresh.addConst_sort
#print axioms Lean4Lean.InductiveDeclExamples.ntree_sortWit_fresh
#print axioms Lean4Lean.InductiveDeclExamples.ntree_sortWit_stage_exists
#print axioms Lean4Lean.InductiveDeclExamples.ntree_sortWit_const
#print axioms Lean4Lean.InductiveDeclExamples.ntree_sortWitness
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_built_sortWit
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_restrictStepCfg_sortWit
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_sortWitness_bypass
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_sortWit_valStrengthen_nonvacuous
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_argsTypedK_of_sortWitness
#print axioms Lean4Lean.not_sortWitness_of_wf
#print axioms Lean4Lean.InductiveDeclExamples.ntree_sortWitJunk_dom_val
#print axioms Lean4Lean.InductiveDeclExamples.ntree_sortWitJunkVal_ne_tyVal
#print axioms Lean4Lean.InductiveDeclExamples.ntree_sortWitJunk_ne_ntreeJunk
