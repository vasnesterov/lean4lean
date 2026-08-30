import Lean4Lean.Verify.Typing.Lemmas

/-!
# `TrProj.wf` is not vacuous

`TrProj.wf` (`Verify/Typing/Lemmas.lean`) is now proved, by the swap route of
`Verify/Typing/ProjSkip.lean`.  A proof of a statement nobody can instantiate would be no
progress at all, and the configuration this lemma had to survive — a **small-eliminating**
structure with an **unused** earlier field whose recorded level is *not* `≈ .zero` — is exactly
the one that refutes the premise the old proof reduced to (`ProjLevelWitness.lean`'s
`barRefutes`).  So the witness is built here, at that same configuration.

## What is checked

* `barEnv_TrProj` — an actual `TrProj` derivation at `barDecl`, `i = 1`, over the unused
  field 0.  Every clause of the constructor is discharged, F17 included, and F17 is discharged
  in its **guarded** form: field 0 is *not* `≈ .zero`, so a blanket `∀ k ≤ i` clause would have
  had no witness here.
* `barEnv_TrProj_target` — the term the derivation produces, spelled out (`rfl`).  It is
  `Bar.rec (fun _ : Bar => ∀ p : Prop, p) (fun (n : Prop) (h : ∀ p : Prop, p) => h) e`, with no
  projection of field 0 anywhere in it.
* `barEnv_TrProj_wf` — `TrProj.wf` applied to that derivation.

## The one hypothesis that cannot be exhibited here

`TrProj.wf` also asks for `VEnv.WF barEnv`, and that is **not available in this tree** — not
because of anything about `barDecl`, but because `VInductDecl'` is not yet wired into
`VDecl.induct` (`Theory/Inductive/Decl.lean`'s "the primed name is temporary" note), so
`VEnv.WF'`, which is an induction over `VDecl`s, has no step that produces `barEnv`.  It is
therefore carried as a hypothesis below rather than discharged.  Everything else — including
the whole `IsStructure` derivation and the F17 clause — is discharged outright.
-/

namespace Lean4Lean

open VExpr

/-- The context: one binder of type `Bar`. -/
def barCtx : List VExpr := [.const `Bar []]

theorem barCtx_onCtx : OnCtx barCtx (barEnv.IsType 0) :=
  ⟨trivial, _, barEnv_Bar_hasType⟩

/-- **An actual `TrProj` derivation**, at the two-field witness, projecting the *used* field 1
over the *unused* field 0. -/
theorem barEnv_TrProj :
    TrProj barEnv 0 barCtx `Bar 1 (.bvar 0)
      (barDecl.projTerm barType barCtor [] [] [] 1 (.bvar 0)) := by
  refine .mk barEnv_IsStructure ?_ rfl rfl rfl (by simp [barCtor]) nofun .nil .nil (.inr ?_)
  · exact .bvar (.zero ..)
  · rintro k hk (rfl | hu)
    · simp [barCtor, barField1, VLevel.inst, VLevel.equiv_def, VLevel.eval, Lean.Nat.imax]
    · match k, hk with
      | 0, _ => exact absurd hu bar_not_fieldUsed
      | 1, _ =>
        simp [barCtor, barField1, VLevel.inst, VLevel.equiv_def, VLevel.eval, Lean.Nat.imax]

/-- **The term it produces**, spelled out — no occurrence of a projection of field 0. -/
theorem barEnv_TrProj_target :
    barDecl.projTerm barType barCtor [] [] [] 1 (.bvar 0)
      = .app (.app (.app (VExpr.const `Bar.rec [])
            ((VExpr.const `Bar []).lam ((VExpr.sort .zero).forallE (.bvar 0))))
          ((VExpr.sort .zero).lam (((VExpr.sort .zero).forallE (.bvar 0)).lam (.bvar 0))))
          (.bvar 0) := rfl

/-- **`TrProj.wf` fired at that derivation.**  `VEnv.WF barEnv` is a hypothesis for the reason
in this file's header; nothing else is assumed. -/
theorem barEnv_TrProj_wf (henv : VEnv.WF barEnv) :
    VExpr.WF barEnv 0 barCtx (barDecl.projTerm barType barCtor [] [] [] 1 (.bvar 0)) :=
  TrProj.wf henv barCtx_onCtx barEnv_TrProj ⟨_, .bvar (.zero ..)⟩

/-- …and field 0's recorded level really is not `≈ .zero`, so this witness is not one a blanket
F17 clause could have covered.  (`barRefutes` uses the same fact to refute the premise the old
proof of `TrProj.wf` reduced to.) -/
theorem barField0_lvl_ne_zero :
    ¬ (VLevel.inst [] (barCtor.fields.getD 0 default).lvl ≈ VLevel.inst [] VLevel.zero) := by
  intro h
  exact absurd (congrFun h []) (by simp [barCtor, barField0, VLevel.inst, VLevel.eval])

end Lean4Lean
