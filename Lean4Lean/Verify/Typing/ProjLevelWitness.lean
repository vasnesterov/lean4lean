import Lean4Lean.Theory.Inductive.Lemmas
import Lean4Lean.Theory.Inductive.Structure

set_option linter.unusedSimpArgs false

/-!
# `TrProj.wf`'s open subgoal is FALSE, and here is the witness

`Verify/Typing/Lemmas.lean`'s `TrProj.wf` carries one `sorry`.  The comment at that `sorry`
reads "Closing this is one `Ctx.LiftN.one` strengthening step per unused field".  **That is
wrong.**  The goal at that position is a *level* equivalence,

    VLevel.inst us (C.fields.getD k default).lvl ≈ VLevel.inst us VLevel.zero

under `k < i`, `¬ C.FieldUsed D 0 k`, `D.isLE = false`, `env.IsStructure s D T C`, the F17
clause, and the typing side conditions.  Strengthening produces typing judgements; it cannot
produce a level equivalence.  And the subgoal does not merely lack a proof: it is **refuted**
by the very witness `TrProj.wf`'s own docstring names — `structure Bar : Prop where
(n : Nat) (h : True)`, here in its `VInductDecl'` form as `barDecl`.

`barRefutes` below satisfies *every* hypothesis in that goal state simultaneously and negates
the conclusion.  So the `sorry` is not a hole in an otherwise-sound argument: the route
through `projTerm_hasType`'s `hlv` premise cannot be completed at all, and `TrProj.wf` needs
the reformulation its docstring describes (the peel loop) rather than a missing lemma.

Note what is *not* claimed: `TrProj.wf` itself is not refuted.  Only the subgoal that the
current proof reduces it to.
-/

namespace Lean4Lean

open VExpr

/-! ## `barDecl` — `structure Bar : Prop where (n : Prop) (h : ∀ p : Prop, p)`

Two non-recursive fields, `Prop`-valued block, `isLE = false`.

* field 0 has `lvl = .succ .zero` (it is `Prop : Sort 1`) and is **unused** by the rest of
  the telescope, so F17 says nothing about it;
* field 1 has `lvl = .imax (.succ .zero) .zero ≈ .zero`, so F17's obligation at `k = i = 1`
  is discharged.

The docstring's `Bar` uses `Nat` for field 0; `Prop` is used here only because the empty
environment has no `Nat`.  Nothing about the refutation depends on the choice: all that is
needed is a field whose recorded level is not `≈ .zero`.

`isLE = false` is *forced*, not merely permitted: `VInductDecl'.WF.isLE` constrains `isLE`
only in the `true` direction, and `barDecl.LECond` is outright false — `lvl = .zero` is not
`IsNeverZero`, and at field 0 neither `.succ .zero ≈ .zero` nor `.bvar 1 ∈ C.args` (`args`
is empty).  `barDecl_not_LECond` below checks this. -/
def barField0 : VIndField where
  type := .sort .zero
  lvl := .succ .zero
  recArg := none

/-- `∀ (p : Prop), p`, in the context that already binds field 0.  `bvar 0` is the `∀`'s own
binder, so field 0 (which would be `bvar 1` here) does not occur. -/
def barField1 : VIndField where
  type := .forallE (.sort .zero) (.bvar 0)
  lvl := .imax (.succ .zero) .zero
  recArg := none

def barCtor : VIndCtor where
  name := `Bar.mk
  params := []
  fields := [barField0, barField1]
  args := []

def barType : VIndType where
  name := `Bar
  type := .sort .zero
  indices := []
  ctors := [barCtor]

def barDecl : VInductDecl' where
  uvars := 0
  params := []
  lvl := .zero
  types := [barType]
  isLE := false

/-! ## `barDecl` is well-formed -/

theorem barDecl_WF : barDecl.WF .empty where
  types_ne := by simp [barDecl]
  params := trivial
  types := by
    intro T hT
    simp [barDecl] at hT
    subst hT
    exact { indices := trivial
            isType := ⟨_, .sortDF trivial trivial (.refl _)⟩
            canon := ⟨_, .sortDF trivial trivial (.refl _)⟩ }
  ctors := by
    intro env₁ he j T hT C hC
    match j, hT with
    | 0, hT =>
      simp [barDecl] at hT
      subst hT
      simp [barType] at hC
      subst hC
      have hc : env₁.constants `Bar = some ⟨0, VExpr.sort .zero⟩ := by
        simp [VEnv.addIndTypes, VEnv.addConstList, VInductDecl'.typeConsts, barDecl, barType,
          VEnv.addConst, VEnv.empty] at he
        subst he; simp
      refine { params_len := rfl, params_eq := .zero, fields := ?_,
               args_len := rfl, args_fresh := by simp [barCtor], args_ty := .nil,
               result := .constDF hc nofun nofun rfl .nil }
      intro i F hF
      match i, hF with
      | 0, hF =>
        simp [barCtor] at hF
        subst hF
        exact { hasType := .sortDF trivial trivial (.refl _)
                level := fun ls => by simp [VLevel.eval, barDecl, Lean.Nat.imax]
                binders_indep := nofun
                pos := ⟨.sort .zero, by simp [VInductDecl'.NoBlock, VExpr.NoConsts],
                        _, .sortDF trivial trivial (.refl _)⟩ }
      | 1, hF =>
        simp [barCtor] at hF
        subst hF
        have hty : env₁.HasType barDecl.uvars
            ((List.map (fun x => x.type) (List.take 1 barCtor.fields)).reverse
              ++ barDecl.params.reverse)
            barField1.type (.sort barField1.lvl) := by
          show env₁.HasType 0 [barField0.type] _ _
          refine .forallEDF (.sortDF trivial trivial (.refl _)) ?_
          exact .bvar (.zero ..)
        exact { hasType := hty
                level := fun ls => by
                  simp [VLevel.eval, barDecl, Lean.Nat.imax]
                binders_indep := nofun
                pos := ⟨barField1.type,
                        by simp [VInductDecl'.NoBlock, VExpr.NoConsts, barField1],
                        _, hty⟩ }
  isLE := by simp [barDecl]

theorem barEnv_eq : ∃ e, VEnv.empty.addInduct' barDecl = some e := ⟨_, rfl⟩

noncomputable def barEnv : VEnv := barEnv_eq.choose

theorem barEnv_IsStructure : barEnv.IsStructure `Bar barDecl barType barCtor where
  types := rfl
  name := rfl
  ctors := rfl
  noRec := rfl
  decl := ⟨.empty, barEnv, barDecl_WF, barEnv_eq.choose_spec, VEnv.LE.rfl⟩

/-- `isLE = false` is forced, not merely permitted. -/
theorem barDecl_not_LECond : ¬ barDecl.LECond := by
  rintro (h | ⟨T, hT, (hc | ⟨C, hC, hf⟩)⟩)
  · exact absurd (h [] (by simp [VLevel.eval, barDecl])) (by simp [barDecl, VLevel.eval])
  · simp [barDecl] at hT; subst hT; simp [barType] at hc
  · simp [barDecl] at hT; subst hT; simp [barType] at hC; subst hC
    rcases hf 0 barField0 rfl with h | h
    · exact absurd (congrFun h []) (by simp [VLevel.eval, barField0])
    · simp [barCtor] at h

/-! ## The refutation -/

theorem barEnv_Bar_const : barEnv.constants `Bar = some ⟨0, .sort .zero⟩ :=
  VEnv.addInduct'_types (T := barType) barEnv_eq.choose_spec (by simp [barDecl])

theorem barEnv_Bar_hasType : barEnv.HasType 0 [] (.const `Bar []) (.sort .zero) :=
  .constDF barEnv_Bar_const nofun nofun rfl .nil

/-- Field 0 is unused by the rest of the constructor's telescope. -/
theorem bar_not_fieldUsed : ¬ barCtor.FieldUsed barDecl 0 0 := by
  intro h
  refine h ?_
  simp [barCtor, VIndCtor.canonResult, VInductDecl'.tyApp, VExpr.mkPi, VExpr.Skips',
    barField1, barDecl, VInductDecl'.np]

/-- **Every hypothesis of `TrProj.wf`'s open subgoal, satisfied at once, with the conclusion
false.**

The components are, in the order the goal state at `Verify/Typing/Lemmas.lean`'s `sorry`
lists them: `HS`, `hΓ`, `he`, `h3`, `h4`, `h5`, `h7`, `hpsA`, `hιsA`, `hi`, `hLE`, `h`
(the F17 clause), `hlt`, `hu`, and the negated goal. -/
theorem barRefutes :
    ∃ (env : VEnv) (U : Nat) (Γ : List VExpr) (s : Lean.Name) (D : VInductDecl')
      (T : VIndType) (C : VIndCtor) (us : List VLevel) (ps ιs : List VExpr)
      (e : VExpr) (i k : Nat),
      env.IsStructure s D T C ∧
      OnCtx Γ (env.IsType U) ∧
      env.HasType U Γ e ((VExpr.const s us).mkApp (ps ++ ιs)) ∧
      us.length = D.uvars ∧ ps.length = D.np ∧ ιs.length = T.indices.length ∧
      (∀ l ∈ us, VLevel.WF U l) ∧
      env.HasArgs U Γ (D.params.map (VExpr.instL us)) ps ∧
      env.HasArgs U Γ (VExpr.instAllTele (T.indices.map (VExpr.instL us)) ps) ιs ∧
      i < C.fields.length ∧
      D.isLE = false ∧
      (∀ k, k ≤ i → (k = i ∨ C.FieldUsed D 0 k) →
        VLevel.inst us (C.fields.getD k default).lvl ≈ VLevel.zero) ∧
      k < i ∧ ¬ C.FieldUsed D 0 k ∧
      ¬ (VLevel.inst us (C.fields.getD k default).lvl ≈ VLevel.inst us VLevel.zero) := by
  refine ⟨barEnv, 0, [.const `Bar []], `Bar, barDecl, barType, barCtor, [], [], [],
    .bvar 0, 1, 0, barEnv_IsStructure, ⟨trivial, _, barEnv_Bar_hasType⟩, ?_, rfl, rfl, rfl,
    nofun, .nil, .nil, by simp [barCtor], rfl, ?_, Nat.zero_lt_one, bar_not_fieldUsed, ?_⟩
  · exact .bvar (.zero ..)
  · rintro k hk (rfl | hu)
    · simp [barCtor, barField1, VLevel.inst, VLevel.equiv_def, VLevel.eval, Lean.Nat.imax]
    · match k, hk with
      | 0, _ => exact absurd hu bar_not_fieldUsed
      | 1, _ =>
        simp [barCtor, barField1, VLevel.inst, VLevel.equiv_def, VLevel.eval, Lean.Nat.imax]
  · intro h
    exact absurd (congrFun h []) (by simp [barCtor, barField0, VLevel.inst, VLevel.eval])

end Lean4Lean
