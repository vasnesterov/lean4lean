import Lean4Lean.Verify.Typing.ProjLevelWitness
import Lean4Lean.Theory.Inductive.Lemmas

/-!
# The syntactic core of `TrProj.wf`'s live route

`ProjLevelWitness.lean` refutes the subgoal the current proof of `TrProj.wf`
(`Verify/Typing/Lemmas.lean`) reduces to: `projTerm_hasType`'s `hlv` premise demands
`lvl_k.inst us ≈ .zero` at **every** `k ≤ i`, and at an unused field that is false.  This file
carries the fact that makes the *replacement* route work, and it is purely syntactic.

## The route, and why it is live

`VInductDecl'.projCore`'s only use of the earlier projections is inside its motive,
`instAll ftype (ps.map (·.liftN _) ++ earlier)`.  In `instAll e (as) k` the list element at
position `j` substitutes at de Bruijn index `as.length - 1 - j` (`instAll_cons`), so with
`as = ps ++ earlier`, `|ps| = np`, `|earlier| = i`, the entry `earlier[k]` substitutes at index
`i - 1 - k` — **exactly the index `VIndCtor.not_fieldUsed_skips` proves `ftype` skips** when
field `k` is unused.  So `projTerm … i e` does not mention the projection of an unused earlier
field *at all*: the term the current proof cannot type is not in the term it is typing.

`VIndCtor.not_fieldUsed_skips` is described in `Theory/Inductive/Structure.lean` as "stated and
unused"; this is the use.

That turns the open subgoal from a level equivalence (refuted) into: type the motive body from
the *compressed* spine, dropping the positions the field type skips.  The one judgement that
step needs is single-binder strengthening for a type,

    IsType (A :: Δ) (X.liftN 1)  ⟹  IsType Δ X

which is **already a lemma in this tree** — `VEnv.IsType.weakN_iff`
(`Theory/Typing/UniqueTyping.lean:221`), at `Ctx.LiftN.one`.  It is backed by
`IsDefEqU.weakN_iff`'s `sorry` at `UniqueTyping.lean:172`, i.e. by an *existing* hole owned by
another stream, not by a statement that has to be invented.  `TrProj.wf`'s docstring reaches
the same target and calls it "the rescoped target"; what that docstring got wrong is only the
*shape* of the current subgoal, and `ProjLevelWitness.lean` corrects that.

## What is here, and what is not

Here: the substitution lemma (`VExpr.instAll_congr_skips`), its `projCore` instance
(`VInductDecl'.projCore_congr_earlier`), and the `barDecl` demonstration — the two-field
witness of `ProjLevelWitness.lean`, where field 0 is unused and *not* `≈ .zero`, so this is the
exact configuration `barRefutes` uses.

Not here: the guarded re-proofs of `projArgs_hasArgs`, `projMotiveBody_hasType`,
`projMinor_hasType` and `projTerm_hasType`.  Those are the bulk of the work and they live in
`Theory/Inductive/StructureClosed.lean`, which this stream does not own; the index arithmetic
bridging `not_fieldUsed_skips`'s `i - 1 - k` to the *post-`ps`-substitution* skip is the one
remaining syntactic step, and it is bounded (substituting at indices `≥ i` cannot create an
occurrence below `i`).
-/

namespace Lean4Lean

open VExpr

/-- Substituting at an index the term does not use is independent of what is substituted. -/
theorem VExpr.inst_congr_skips {e : VExpr} {m : Nat} (h : e.Skips' 1 m) (a b : VExpr) :
    e.inst a m = e.inst b m := by
  obtain ⟨e', rfl⟩ := VExpr.skips_iff_exists.1 (VExpr.skips_iff.2 h)
  rw [VExpr.inst_liftN, VExpr.inst_liftN]

/-- **The lemma the route runs on.**  One position of an `instAll` spine is irrelevant as soon
as the term reached just before that position is substituted skips index `k + |post|`. -/
theorem VExpr.instAll_congr_skips {pre post : List VExpr} {e a b : VExpr} {k : Nat}
    (h : (VExpr.instAll e pre (k + post.length + 1)).Skips' 1 (k + post.length)) :
    VExpr.instAll e (pre ++ a :: post) k = VExpr.instAll e (pre ++ b :: post) k := by
  rw [VExpr.instAll_append, VExpr.instAll_append]
  simp only [List.length_cons, VExpr.instAll_cons]
  rw [show k + (post.length + 1) = k + post.length + 1 from by omega,
    VExpr.inst_congr_skips h a b]

/-- **`projCore` does not read the earlier projections it discards.**  Instantiated at the
position of an unused field, this says the projected term is *literally the same* whether or
not the ill-typed projection is supplied. -/
theorem VInductDecl'.projCore_congr_earlier (D : VInductDecl') (T : VIndType) (C : VIndCtor)
    (us : List VLevel) (ps is : List VExpr) (i : Nat) (e : VExpr)
    (pre post : List VExpr) (a b : VExpr)
    (h : (VExpr.instAll ((C.fields.getD i default).type.instL us)
            (ps.map (·.liftN (is.length+1)) ++ pre) (post.length + 1)).Skips' 1 post.length) :
    D.projCore T C us ps is i (pre ++ a :: post) e
      = D.projCore T C us ps is i (pre ++ b :: post) e := by
  simp only [VInductDecl'.projCore]
  rw [show ps.map (·.liftN (is.length+1)) ++ (pre ++ a :: post)
        = (ps.map (·.liftN (is.length+1)) ++ pre) ++ a :: post from by simp,
    show ps.map (·.liftN (is.length+1)) ++ (pre ++ b :: post)
        = (ps.map (·.liftN (is.length+1)) ++ pre) ++ b :: post from by simp,
    VExpr.instAll_congr_skips (k := 0) (by simpa using h)]

/-! ## The demonstration, at the two-field witness

`barDecl`'s field 0 is `Prop` — recorded level `.succ .zero`, *not* `≈ .zero` — and is unused by
field 1's type `∀ p : Prop, p`.  `barRefutes` (`ProjLevelWitness.lean`) uses exactly this to
falsify the current proof's subgoal.  Here the same configuration shows the subgoal is not
needed. -/

/-- **Field 0's projection is irrelevant to `.proj Bar 1`**, by `rfl`: the recursor application
`TrProj` produces is independent of what sits at the unused position. -/
theorem barDecl_projCore_indep (e x y : VExpr) :
    barDecl.projCore barType barCtor [] [] [] 1 [x] e
      = barDecl.projCore barType barCtor [] [] [] 1 [y] e := rfl

/-- …and `projTerm`, which supplies the *ill-typed* `projCore … 0` at that position, is equal to
the instance that supplies a trivially well-typed term instead. -/
theorem barDecl_projTerm_eq (e : VExpr) :
    barDecl.projTerm barType barCtor [] [] [] 1 e
      = barDecl.projCore barType barCtor [] [] [] 1 [.sort .zero] e := rfl

/-- **The whole term, spelled out.**  `Bar.rec (fun _ : Bar => ∀ p : Prop, p)
(fun (n : Prop) (h : ∀ p : Prop, p) => h) e` — there is no occurrence of a projection of
field 0 anywhere in it, which is why `TrProj.wf` is *true* at the witness that refutes its
current proof's subgoal. -/
theorem barDecl_projTerm_spelled (e : VExpr) :
    barDecl.projTerm barType barCtor [] [] [] 1 e
      = .app (.app (.app (VExpr.const `Bar.rec [])
            ((VExpr.const `Bar []).lam ((VExpr.sort .zero).forallE (.bvar 0))))
          ((VExpr.sort .zero).lam (((VExpr.sort .zero).forallE (.bvar 0)).lam (.bvar 0))))
          e := rfl

end Lean4Lean
