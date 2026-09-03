import Lean4Lean.Theory.Inductive.CompanionResolve
import Lean4Lean.Theory.Inductive.NestedTele
import Lean4Lean.Theory.Typing.ConstSubstNested

/-!
# Is `VInductDecl'.WFC` available on the nested path?  No — and it is *false*, not merely weak

`docs/handoff-restrict.md` closes with an item it flagged as read rather than checked:

> `InductR.lean` §4's claim that `WFC` is unavailable on the nested path — if that reading is
> wrong, `WFC` is a third and much shorter route.

This file settles it.  The reading is **right**, and the situation is worse than "unavailable":
`VInductDecl'.WFC env D K` is **refutable** at the nested configuration, so an obligation that
carried it as a hypothesis would be *vacuously* discharged — the project's dominant defect, in
the one place the handoff left a door open.

What is new here versus what was already in the tree:

* `Verify/Environment/InductR.lean` §4 (:452, :465) argues the point in prose.
* `Theory/Inductive/NestedHead.lean`'s `ntreeAux_staging` proves the three *staging* `rfl`s —
  `typeConsts` has `_nested.List_1`, `typeConstsC ntreeK` does not, and `NTree.node`'s second
  field type mentions `.const _nested.List_1` — and its docstring then *asserts* "at that
  staging the clause is not merely weaker, it is unsatisfiable".
* Nobody had turned that assertion into a theorem.  §2 does, in general; §3 instantiates it at
  the `NTree`/`List` witness at the real staged environment; §4 states the vacuity consequence.

## The mechanism, in one line

`VIndCtor.WF` is stated over the environment in which the block's type constants are already
declared, and `VIndCtor.WF.isType` (`Theory/Inductive/Lemmas.lean`) turns it into
`e₁.IsType D.uvars [] (C.type D j)` — a **closed** typing.  A closed typing in `e₁` cannot
mention a constant `e₁` does not declare (`VEnv.IsDefEq.noCSubst'`).  But `C.type D j` ends in
`C.canonResult D j = D.tyApp j …`, whose head *is* `.const (D.types.getD j default).name`.  So
`WFC.ctors` at a member whose name `e₁` lacks demands a typing that provably does not exist.

Note what this argument does **not** use: no `HasArgs.of_mkApp`, no `PiInv`, no application
inversion at all — `noCSubst'` is a structural induction over the `IsDefEq` derivation, and the
context is `[]`, so its `hΓ` premise is `nofun`.
-/

namespace Lean4Lean

open Lean (Name)

/-! ## 1. One structural lemma

`Theory/Inductive/NestedTele.lean` has `NoCSubst.mkPi_tele` (peel a `mkPi`); the `mkApp`
counterpart is not there, and it is the other half of `C.type`. -/

namespace VExpr
variable {σ : CSubst}

/-- `NoCSubst` is inherited by the head of a spine. -/
theorem NoCSubst.mkApp_head {e : VExpr} :
    ∀ {as : List VExpr}, (e.mkApp as).NoCSubst σ → e.NoCSubst σ
  | [], h => h
  | _ :: as, h => by
    have := NoCSubst.mkApp_head (as := as) h
    exact this.1

end VExpr

/-! ## 2. The general obstruction

**Statement.**  If a member of the block has a constructor and its type constant is *not*
declared in the environment `WFC.ctors` is staged over, then `WFC` is false.

Nothing here is about nesting or about companions as such: it is the staging of `WFC.ctors`
against the head of `canonResult`.  §3 supplies the nested instance, and `WFC_nil_iff` +
`ntreeAux_WF'` supply the contrast at `K = []` (where `addIndTypesC` declares everything, so
`hnone` is unsatisfiable and this lemma says nothing). -/

/-- **The head of a constructor's stored type is the member's own type constant.**  Extracted
from `C.type`/`canonResult`/`tyApp` so that §2's proof is one rewrite. -/
theorem VIndCtor.type_mkPi_head (C : VIndCtor) (D : VInductDecl') (j : Nat) {σ : CSubst}
    (h : (C.type D j).NoCSubst σ) : σ (D.types.getD j default).name = none := by
  have h2 := (VExpr.NoCSubst.mkPi_tele h).2
  rw [VIndCtor.canonResult, VInductDecl'.tyApp] at h2
  exact VExpr.NoCSubst.mkApp_head h2

/-- **`VInductDecl'.WFC` is refutable when a member's type constant is missing from the
staged environment.**

`hnone` is the whole content: `WFC.ctors` is staged over `addIndTypesC D K`, which *omits* the
members named in `K`, and a member named in `K` whose name is not already in `env` is therefore
undeclared where its own constructors are checked. -/
theorem VInductDecl'.not_WFC_of_undeclared {env e₁ : VEnv} {D : VInductDecl'} {K : List Name}
    {j : Nat} {T : VIndType} {C : VIndCtor}
    (henv₁ : e₁.Ordered) (hst : env.addIndTypesC D K = some e₁)
    (hT : D.types[j]? = some T) (hC : C ∈ T.ctors)
    (hnone : e₁.constants T.name = none) : ¬ D.WFC env K := by
  intro h
  have hgetD : (D.types.getD j default).name = T.name := by
    rw [List.getD_eq_getElem?_getD, hT]; rfl
  have hfresh : (CSubst.one T.name (.sort .zero)).FreshIn e₁ := by
    intro c ci hc
    by_cases hce : c = T.name
    · subst hce; rw [hnone] at hc; exact absurd hc nofun
    · exact CSubst.one_of_ne hce
  obtain ⟨u, hu⟩ := (h.ctors e₁ hst j T hT C hC).isType henv₁
  have hno : (C.type D j).NoCSubst (CSubst.one T.name (.sort .zero)) :=
    (VEnv.IsDefEq.noCSubst' (henv₁.noCSubst hfresh) hfresh hu nofun).1
  have := C.type_mkPi_head D j hno
  rw [hgetD, CSubst.one_self] at this
  exact absurd this nofun

/-- **The companion-member form**, which is the one the nested path hits: a member listed in
`K` is dropped by `typeConstsC`, so if `env` does not already declare it — and on the nested
path `mkUniqueName` guarantees it does not — `WFC` is false. -/
theorem VInductDecl'.not_WFC_of_fresh_companion {env e₁ : VEnv} {D : VInductDecl'}
    {K : List Name} {j : Nat} {T : VIndType} {C : VIndCtor}
    (henv₁ : e₁.Ordered) (hst : env.addIndTypesC D K = some e₁)
    (hT : D.types[j]? = some T) (hC : C ∈ T.ctors)
    (hK : T.name ∈ K) (hfresh : env.constants T.name = none) : ¬ D.WFC env K := by
  refine not_WFC_of_undeclared henv₁ hst hT hC ?_
  rw [VEnv.addIndTypesC] at hst
  have hmem : T.name ∉ (D.typeConstsC K).map (·.1) := by
    simp only [VInductDecl'.typeConstsC, List.mem_map, List.mem_filterMap]
    rintro ⟨c, ⟨c', -, hc'⟩, hcn⟩
    split at hc'
    · exact absurd hc' nofun
    · rename_i hcK
      simp only [Option.some.injEq] at hc'
      subst hc'
      exact absurd (show c'.1 ∈ K by rw [hcn]; exact hK) hcK
  rw [VEnv.addConstList_constants_of_not_mem hst hmem]; exact hfresh

/-! ### 2a. The field form

`NestedHead.lean`'s `ntreeAux_staging` docstring blames a *different* occurrence: not the
companion member's own `canonResult` but `NTree.node`'s second **field** type, which is
`_nested.List_1 α`.  That is a second, independent obstruction — it lands on the member the
user actually wrote (`j = 0`, not in `K`) — and it needs the same one theorem, because
`C.type` binds the field telescope. -/

theorem VInductDecl'.not_WFC_of_field {env e₁ : VEnv} {D : VInductDecl'} {K : List Name}
    {σ : CSubst} {j : Nat} {T : VIndType} {C : VIndCtor} {i : Nat} {F : VIndField}
    (henv₁ : e₁.Ordered) (hσ : σ.FreshIn e₁) (hst : env.addIndTypesC D K = some e₁)
    (hT : D.types[j]? = some T) (hC : C ∈ T.ctors) (hF : C.fields[i]? = some F)
    (hmention : ¬ F.type.NoCSubst σ) : ¬ D.WFC env K := by
  intro h
  obtain ⟨u, hu⟩ := (h.ctors e₁ hst j T hT C hC).isType henv₁
  have hno : (C.type D j).NoCSubst σ :=
    (VEnv.IsDefEq.noCSubst' (henv₁.noCSubst hσ) hσ hu nofun).1
  exact hmention <| (VExpr.NoCSubst.mkPi_tele hno).1 _ <|
    List.mem_append_right _ (List.mem_map_of_mem (List.mem_of_getElem? hF))

/-! ### 2b. The obvious repair, and why it fails too

§4's prose locates the obstruction at *the companion member's* constructor type.  If that were
the whole story, the repair would be to weaken the clause to the members the user wrote — check
constructors at `addIndTypesC D K` only for `T.name ∉ K`, where the type constant *is*
declared.  `WFCOwn` below is that weakening, and §3b refutes it at the same witness: on the
nested path the user's own constructor mentions the *auxiliary* member's constant
(`NTree.node`'s second field is `_nested.List_1 α`), so restricting the quantifier does not
reach a satisfiable clause.

This closes the natural fourth route as well, and it is the correction to make to §4's reason:
the obstruction is not "a companion member's own constructor type"; it is "**any** constructor
type in the block that mentions a dropped constant", and on the nested path the user's members
are exactly the ones that do — that is what nesting *is*. -/

/-- `WFC.ctors` weakened to the members the user wrote.  Not a predicate anyone in the tree
uses; stated here only to be refuted (§3b). -/
def VInductDecl'.WFCOwnCtors (env : VEnv) (D : VInductDecl') (K : List Name) : Prop :=
  ∀ env₁, env.addIndTypesC D K = some env₁ →
    ∀ j (T : VIndType), D.types[j]? = some T → T.name ∉ K →
      ∀ (C : VIndCtor), C ∈ T.ctors → C.WF env₁ D j T

theorem VInductDecl'.not_WFCOwnCtors_of_field {env e₁ : VEnv} {D : VInductDecl'}
    {K : List Name} {σ : CSubst} {j : Nat} {T : VIndType} {C : VIndCtor} {i : Nat}
    {F : VIndField}
    (henv₁ : e₁.Ordered) (hσ : σ.FreshIn e₁) (hst : env.addIndTypesC D K = some e₁)
    (hT : D.types[j]? = some T) (hK : T.name ∉ K) (hC : C ∈ T.ctors)
    (hF : C.fields[i]? = some F) (hmention : ¬ F.type.NoCSubst σ) :
    ¬ D.WFCOwnCtors env K := by
  intro h
  obtain ⟨u, hu⟩ := (h e₁ hst j T hT hK C hC).isType henv₁
  have hno : (C.type D j).NoCSubst σ :=
    (VEnv.IsDefEq.noCSubst' (henv₁.noCSubst hσ) hσ hu nofun).1
  exact hmention <| (VExpr.NoCSubst.mkPi_tele hno).1 _ <|
    List.mem_append_right _ (List.mem_map_of_mem (List.mem_of_getElem? hF))

/-! ## 3. Instantiated at the `NTree`/`List` nested witness

Standing rule: *instantiate, don't admire.*  §2 alone would be another statement that compiles
and proves nothing; what makes it a refutation of §4's third route is that its hypothesis set is
**jointly inhabited at the block Lean's own kernel runs the nested elimination on**, at the
staged environment `AddInductStagesR`'s first stage actually produces. -/

namespace InductiveDeclExamples

section
variable {env₁ env₃ : VEnv}
variable (h : VEnv.empty.addInduct' listDecl = some env₁)
variable (h₃ : env₁.addConstList (ntreeAux.typeConstsC ntreeK) = some env₃)

include h h₃ in
theorem ntree_env₃_ordered : env₃.Ordered :=
  VEnv.addConstList_ordered (listEnv_ordered h)
    (VEnv.addInductR_typeConstsC_wf (ntreeAux_WF h)) h₃

include h h₃ in
/-- The auxiliary constant is absent from the environment `WFC.ctors` is staged over. -/
theorem ntree_nlist_absent₃ : env₃.constants `_nested.List_1 = none := by
  rw [VEnv.addConstList_constants_of_not_mem h₃ (by decide)]
  exact ntree_fresh' h _ (by decide)

include h h₃ in
theorem ntreeSubst_fresh₃ : ntreeSubst.FreshIn env₃ := by
  intro c ci hc
  by_cases hce : c = `_nested.List_1
  · subst hce; rw [ntree_nlist_absent₃ h h₃] at hc; exact absurd hc nofun
  · exact ntreeSubst_of_ne hce

/-- The two members, pinned, so that `T` is not a metavariable at the call sites below. -/
theorem ntree_types_zero : ntreeAux.types[0]? = some
    { name := ``NTree, type := .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0))),
      indices := [], ctors := [ntreeNode] } := rfl

theorem ntree_types_one : ntreeAux.types[1]? = some
    { name := `_nested.List_1,
      type := .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0))),
      indices := [], ctors := [nlistNil, nlistCons] } := rfl

include h h₃ in
/-- **`WFC` is FALSE at the nested witness — obstruction 1, the companion's own result type.**

`_nested.List_1.nil`'s stored type ends in `_nested.List_1 α`, and `addIndTypesC ntreeAux
ntreeK` does not declare `_nested.List_1`. -/
theorem ntreeAux_not_WFC : ¬ ntreeAux.WFC env₁ ntreeK :=
  VInductDecl'.not_WFC_of_fresh_companion (C := nlistNil) (ntree_env₃_ordered h h₃) h₃
    ntree_types_one (List.Mem.head _) (by decide) (ntree_fresh' h _ (by decide))

include h h₃ in
/-- **…and obstruction 2, the one `ntreeAux_staging`'s docstring names.**  `NTree.node`'s
second field type *is* `.const _nested.List_1 [.param 0]` applied to `.bvar 1`, and `NTree` is
a member the *user wrote* — `j = 0`, not in `ntreeK`.  So the re-staging breaks a clause about
the user's own constructor, not only about the auxiliary one; the documented reason is correct
as stated, and it is a strictly separate failure from `ntreeAux_not_WFC`'s. -/
theorem ntreeAux_not_WFC_node : ¬ ntreeAux.WFC env₁ ntreeK := by
  refine VInductDecl'.not_WFC_of_field (C := ntreeNode) (i := 1) (ntree_env₃_ordered h h₃)
    (ntreeSubst_fresh₃ h h₃) h₃ ntree_types_zero (List.Mem.head _) rfl ?_
  intro hn
  have hne : ntreeSubst `_nested.List_1 = none := hn.1
  rw [ntreeSubst, CSubst.one_self] at hne
  exact absurd hne nofun

include h h₃ in
/-- **3b. The restricted clause is false too.**  `NTree ∉ ntreeK` — this is the member the user
wrote — and `NTree.node`'s second field type still mentions the dropped `_nested.List_1`.  So no
re-staging of `WFC.ctors` over `addIndTypesC` is satisfiable at a nested block, however the
quantifier is restricted. -/
theorem ntreeAux_not_WFCOwnCtors : ¬ ntreeAux.WFCOwnCtors env₁ ntreeK := by
  refine VInductDecl'.not_WFCOwnCtors_of_field (C := ntreeNode) (i := 1)
    (ntree_env₃_ordered h h₃) (ntreeSubst_fresh₃ h h₃) h₃ ntree_types_zero (by decide)
    (List.Mem.head _) rfl ?_
  intro hn
  have hne : ntreeSubst `_nested.List_1 = none := hn.1
  rw [ntreeSubst, CSubst.one_self] at hne
  exact absurd hne nofun

end

/-- **The refutation with no hypotheses left**, via `ntreeAux_declared_exists`. -/
theorem ntreeAux_not_WFC' :
    ∃ env₁ : VEnv, VEnv.empty.addInduct' listDecl = some env₁ ∧ ¬ ntreeAux.WFC env₁ ntreeK := by
  obtain ⟨env₁, h⟩ : ∃ e, VEnv.empty.addInduct' listDecl = some e := ⟨_, rfl⟩
  obtain ⟨env₃, h₃⟩ := ntreeAux_declared_exists h
  exact ⟨env₁, h, ntreeAux_not_WFC h h₃⟩

/-! ## 4. The vacuity consequence — why this is worth a theorem

`WFC` is not "unavailable" in the sense of "true but unproved".  It is **false** at the nested
configuration, so any obligation carrying `D.WFC venv K` as a conjunct — the shape
`InductR.lean` §4 considered and rejected for `InductStepNested` — is *vacuously true* at the
witness.  It would have discharged the flip's residual, `VIndRestore.ValAt`, and everything
else, by `absurd`.  That is the failure mode `fooComp_WF` / `docs/vacuity-ledger.md` exist to
catch, and §4's prose reading was protecting against it. -/

theorem ntree_WFC_vacuates {env₁ env₃ : VEnv}
    (h : VEnv.empty.addInduct' listDecl = some env₁)
    (h₃ : env₁.addConstList (ntreeAux.typeConstsC ntreeK) = some env₃)
    (P : Prop) : ntreeAux.WFC env₁ ntreeK → P :=
  fun hw => absurd hw (ntreeAux_not_WFC h h₃)

/-! ## 5. Collapse test: the re-staging is the *only* thing that flips it

Standing rule: *a hypothesis can be inert*, and *check the hypothesis set is jointly
inhabited*.  §2's lemmas are vacuous at `K = []` (their `hK : T.name ∈ []` and their `hnone`
have no witness there), so their content lives entirely at `K ≠ []`.  The pair below is the
sharpest form of the answer: **the same `D`, at the same `env₁`, satisfies `WFC` at `K = []`
and refutes it at `K = ntreeK`.**  Nothing about the block changes; only the staging of the
`ctors` clause. -/

theorem ntreeAux_WFC_nil {env₁ : VEnv} : ntreeAux.WFC env₁ [] :=
  VInductDecl'.WFC_nil_iff.2 ntreeAux_WF'

theorem ntreeAux_WFC_flips {env₁ env₃ : VEnv}
    (h : VEnv.empty.addInduct' listDecl = some env₁)
    (h₃ : env₁.addConstList (ntreeAux.typeConstsC ntreeK) = some env₃) :
    ntreeAux.WFC env₁ [] ∧ ¬ ntreeAux.WFC env₁ ntreeK ∧ ntreeAux.WF env₁ :=
  ⟨ntreeAux_WFC_nil, ntreeAux_not_WFC h h₃, ntreeAux_WF'⟩

end InductiveDeclExamples

/-! ## 6. A second, independent witness — and `fooDecl_WFC`'s hypothesis is load-bearing

Standing rule: *a count is only as meaningful as the population it ranges over.*  §3 is one
block.  This section runs §2 on the *other* family in the tree — `CompanionResolve.lean`
Part 8's `fooDecl`/`fooCompDecl` pair — and the result is a complete characterisation of when
`WFC` can hold at a companion member.

Cross-check against what is already proved there, which came out exactly right:

* `fooComp_WFC : fooCompDecl.WFC env₁ [`Foo]` holds at **arbitrary** `env₁`, and §2 does not
  contradict it: `fooCompDecl`'s member has `ctors := []`, and `not_WFC_of_undeclared` needs
  `C ∈ T.ctors`.  ("Re-staging restores the clause's *domain*; it does not give it any
  *content* at `ctors = []`" — that docstring is exact.)
* `fooDecl_WFC : fooDecl.WFC env₁ [`Foo]` — whose member *does* have a constructor — is stated
  under `h : VEnv.empty.addInduct' fooDecl = some env₁`, i.e. under `Foo ∈ env₁`.  §6 proves
  that `h` is **load-bearing**: drop it and the statement is false, not merely unproved.

So the dividing line is exactly `env.constants T.name`: with a *fresh* companion name and a
non-empty constructor list, `WFC` is refutable.  That is the nested path's configuration by
construction (`mkUniqueName`), and it is `fooDecl_WFC`'s configuration only because `Foo` is
already declared. -/

namespace InductiveDeclExamples

theorem foo_types_zero : fooDecl.types[0]? = some
    { name := `Foo, type := .sort .zero, indices := [],
      ctors := [{ name := `Foo.mk, params := [],
                  fields := [{ type := .sort .zero, lvl := .succ .zero, recArg := none }],
                  args := [] }] } := rfl

/-- At a block all of whose members are companions, `addIndTypesC` adds nothing — so the
`ctors` premise is satisfied at the input environment itself, with no freshness side
condition.  This is what makes the refutation below unconditional in `env₁`. -/
theorem foo_addIndTypesC {env₁ : VEnv} : env₁.addIndTypesC fooDecl [`Foo] = some env₁ := by
  simp [VEnv.addIndTypesC, VInductDecl'.typeConstsC, VInductDecl'.typeConsts, fooDecl,
    VEnv.addConstList]

/-- **`fooDecl_WFC`'s `h` is load-bearing.**  Without `Foo` in the environment the re-staged
predicate is false, because `Foo.mk`'s stored type is `Foo → Foo`. -/
theorem fooDecl_not_WFC_of_fresh {env₁ : VEnv} (henv₁ : env₁.Ordered)
    (hfresh : env₁.constants `Foo = none) : ¬ fooDecl.WFC env₁ [`Foo] :=
  VInductDecl'.not_WFC_of_fresh_companion henv₁ foo_addIndTypesC foo_types_zero
    (List.Mem.head _) (by decide) hfresh

/-- **The flip, at the second witness, with no hypotheses at all**: the same block, at the same
(empty) environment, satisfies `WF` and refutes `WFC [`Foo]`.  `fooDecl_WF` is
`Theory/Inductive/DeclExamples.lean`'s first `WF` witness, so both halves are pre-existing
statements; only the conjunction is new. -/
theorem fooDecl_WF_and_not_WFC :
    fooDecl.WF VEnv.empty ∧ ¬ fooDecl.WFC VEnv.empty [`Foo] :=
  ⟨fooDecl_WF, fooDecl_not_WFC_of_fresh .empty rfl⟩

end InductiveDeclExamples

/-! ## 7. Axiom lines

Names read off this file's own `namespace` lines (`Lean4Lean`, `Lean4Lean.VExpr`,
`Lean4Lean.InductiveDeclExamples`), never composed from the path. -/

#print axioms Lean4Lean.VExpr.NoCSubst.mkApp_head
#print axioms Lean4Lean.VIndCtor.type_mkPi_head
#print axioms Lean4Lean.VInductDecl'.not_WFC_of_undeclared
#print axioms Lean4Lean.VInductDecl'.not_WFC_of_fresh_companion
#print axioms Lean4Lean.VInductDecl'.not_WFC_of_field
#print axioms Lean4Lean.VInductDecl'.not_WFCOwnCtors_of_field
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_not_WFCOwnCtors
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_not_WFC
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_not_WFC_node
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_not_WFC'
#print axioms Lean4Lean.InductiveDeclExamples.ntree_WFC_vacuates
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_WFC_nil
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_WFC_flips
#print axioms Lean4Lean.InductiveDeclExamples.foo_addIndTypesC
#print axioms Lean4Lean.InductiveDeclExamples.fooDecl_not_WFC_of_fresh
#print axioms Lean4Lean.InductiveDeclExamples.fooDecl_WF_and_not_WFC

end Lean4Lean
