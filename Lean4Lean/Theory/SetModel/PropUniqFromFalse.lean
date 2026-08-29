import Lean4Lean.Theory.SetModel.PropReduce
import Lean4Lean.Theory.Consistency
import Lean4Lean.Theory.Typing.CycleConv

/-!
# `PropUniq` is free once the goal has handed you the proof of `False`

**`docs/backward-analysis.md` §6.2, written.**

`leanTTConsistent` is `∀ env, env.LeanWF → ¬ ∃ e, env.HasType 0 [] e falseProp`,
and `¬ P` *is* `P → False`, so its proof may `intro` the inhabitant of
`falseProp` **before** building any model.  From that point every proposition of
the environment is inhabited: `falseProp = ∀ p : Prop, p` applied to a
proposition `A` is a term of type `A`.

`PropUniq` — the statement `PropSplitAudit.propSplitOf` needs alongside
`PropTypeAgree` — is exactly `PropTypeAgree`'s **diagonal**, the case `A' = A`,
guarded by the existence of an inhabitant of `A`.  And the guard bites only at
propositions, which is precisely where `hfalse` supplies one.

```
PropTypeAgree : Γ ⊢ e : A → Γ ⊢ e : A' → Γ ⊢ A : sort u → Γ ⊢ A' : sort u' →
                (u.eval ls = 0 ↔ u'.eval ls = 0)
PropUniq      :                  Γ ⊢ A : sort u → Γ ⊢ A  : sort v  →
                (u.eval ls = 0 ↔ v.eval ls = 0)
```

Put `A' := A`, `u' := v`, and the two typing premises `Γ ⊢ e : A` become one
obligation: *find an inhabitant of `A`*.

## The two hypotheses this costs, and neither is a context condition

* **`hf : ∃ e, env.HasType 0 [] e falseProp`** — the theorem's own hypothesis,
  delivered by `Verify/Bridge.hasType_falseProp` (proved, sorry-free) before
  `leanTTConsistent` is invoked.  Assuming it while building the model is the
  classical shape of the argument, not circularity: the model's job is to
  contradict it.
* **`henv : env.Ordered`** — needed only to weaken the closed typing into the
  arbitrary context `Γ` that `PropUniq` quantifies over.

**RZ-3 is answered here, and favourably.**  `HasType.weak0`
(`Theory/Typing/Lemmas.lean`) weakens a typing at `[]` into an *arbitrary* `Γ`
with **no** hypothesis on `Γ` — no `OnCtx`, no `CtxClosed`.  Its `CtxClosed`
argument is discharged at the source context `[]`, which is trivially closed.
So `PropSplit`'s fields do **not** need to grow a context hypothesis, and the
model stream owes nothing here.

## The scope of the claim

Without `hf` this file claims nothing: the diagonal instantiation has no `e` to
instantiate at an *uninhabited* proposition.  If someone later proves
`PropTypeAgree → PropUniq` unconditionally, this conclusion is unchanged and
strictly weaker.

And the standing label still travels: `PropTypeAgree` itself is **open**, and
the model remains conditional on a `PropSplit` that nothing in the tree
constructs.  What this file does is narrow that parameter's residual syntactic
import from two statements to one.
-/

namespace Lean4Lean

namespace VEnv

variable {env : VEnv}

/-- A `0`-well-formed level that evaluates to `0` at *some* valuation is
`≈ .zero`: it has no parameters, so its value does not depend on the
valuation. -/
theorem VLevel.equiv_zero_of_wf_zero {u : VLevel} {ls : List ℕ}
    (hu : u.WF 0) (h : u.eval ls = 0) : u ≈ .zero :=
  Lean4Lean.VLevel.equiv_def.mpr fun _ ↦
    (VLevel.eval_eq_of_wf hu fun _ hi ↦ absurd hi (Nat.not_lt_zero _)).trans h

/-- **Every proposition of an inconsistent environment is inhabited.**

`falseProp = ∀ p : Prop, p`, so applying its inhabitant to `A` gives a term of
type `(.bvar 0).inst A = A`.  Stated at an arbitrary context, which is what
`PropUniq` quantifies over; the only price is `Ordered env`, for `weak0`. -/
theorem inhabited_of_hasType_falseProp (henv : env.Ordered)
    {e : VExpr} (he : env.HasType 0 [] e falseProp)
    {Γ : List VExpr} {A : VExpr} (hA : env.HasType 0 Γ A (.sort .zero)) :
    env.HasType 0 Γ (.app e A) A := by
  have he' : env.HasType 0 Γ e (.forallE (.sort .zero) (.bvar 0)) := he.weak0 henv
  show env.IsDefEq 0 Γ (.app e A) (.app e A) A
  simpa [VExpr.inst, VExpr.instVar] using IsDefEq.appDF he' hA

/-- The half of the biconditional that carries the content: an `A` with a
`Prop` sort and a second sort `v` has `v` a `Prop` sort too. -/
theorem propUniq_aux (henv : env.Ordered)
    (hf : ∃ e, env.HasType 0 [] e falseProp) (hT : env.PropTypeAgree 0)
    {Γ : List VExpr} {A : VExpr} {u v : VLevel} {ls : List ℕ}
    (hu : u.WF 0) (hv : v.WF 0)
    (hA : env.HasType 0 Γ A (.sort u)) (hA' : env.HasType 0 Γ A (.sort v))
    (h0 : u.eval ls = 0) : v.eval ls = 0 := by
  obtain ⟨e, he⟩ := hf
  -- `u ≈ .zero`, so `A` is a proposition on the nose
  have hz : u ≈ .zero := VLevel.equiv_zero_of_wf_zero hu h0
  have hsort : env.IsDefEq 0 Γ (.sort u) (.sort .zero) (.sort (.succ u)) :=
    IsDefEq.sortDF hu trivial hz
  have hA0 : env.HasType 0 Γ A (.sort .zero) := IsDefEq.defeqDF hsort hA
  -- the inhabitant, and then `PropTypeAgree`'s diagonal
  have happ : env.HasType 0 Γ (.app e A) A :=
    inhabited_of_hasType_falseProp henv he hA0
  exact (hT hu hv happ happ hA hA').mp h0

/-- **`PropTypeAgree` ⟹ `PropUniq`, under the goal's own hypothesis.**

This is `docs/backward-analysis.md` §6.2.  Combined with
`PropSplitAudit.propSplitOf`, the model's syntactic import collapses from
`PropUniq ∧ PropTypeAgree` to `PropTypeAgree` alone. -/
theorem PropUniq.of_propTypeAgree (henv : env.Ordered)
    (hf : ∃ e, env.HasType 0 [] e falseProp) (hT : env.PropTypeAgree 0) :
    env.PropUniq 0 := fun hu hv hA hA' ↦
  ⟨propUniq_aux henv hf hT hu hv hA hA', propUniq_aux henv hf hT hv hu hA' hA⟩

/-! ## The hypothesis pair is satisfiable, not merely stated

`propUniq_aux` runs on `env.Ordered` **together with** an inhabitant of
`falseProp` at the empty context.  A conjunction that no environment satisfies
would make everything above it vacuous, so exhibit one: `loopEnv2`
(`Theory/Typing/CycleConv.lean`) is `VEnv.WF` by two `.axiom` steps and declares
a constant of type `falseProp`.

It is of course **not** `LeanWF` — it is an axiom environment, so it is no
counterexample to consistency.  What it witnesses is exactly what is needed: the
two hypotheses are jointly satisfiable, so the derivation below is not a
statement about the empty class. -/
theorem ordered_and_inconsistent_satisfiable :
    loopEnv2.Ordered ∧ ∃ e, loopEnv2.HasType 0 [] e falseProp :=
  ⟨loopEnv2_wf.ordered, ⟨.const `f [], hasType_constFalse' loopEnv2_f⟩⟩

end VEnv

namespace SetModel

/-- **The assembled conclusion: one syntactic statement is enough.**

A `PropSplit` — the model's entire syntactic import — is constructible from
`PropTypeAgree` alone, given the environment's own inconsistency hypothesis.
`PropUniq` is discharged by `PropUniq.of_propTypeAgree`, and the reduction to
zero universe parameters is `PropUniq.of_zero` / `PropTypeAgree.of_zero`
(`SetModel/PropReduce.lean`), so this is available at **every** `nv`. -/
noncomputable def propSplitOfAgree (env : VEnv) (nv : ℕ) (henv : env.Ordered)
    (hf : ∃ e, env.HasType 0 [] e falseProp) (hT : env.PropTypeAgree 0) :
    PropSplit env nv :=
  propSplitOf env nv
    (VEnv.PropUniq.of_zero (VEnv.PropUniq.of_propTypeAgree henv hf hT) nv)
    (VEnv.PropTypeAgree.of_zero hT nv)

end SetModel

end Lean4Lean
