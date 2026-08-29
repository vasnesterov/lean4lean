import Lean4Lean.Theory.Typing.HeadReduction

/-!
# Stuck K-redexes, and what they cost `HeadReduction.lean`

`Theory/Typing/HeadReduction.lean`'s two exports that point *from* a conversion *into*
reduction -- `IsDefEq.reduce_sort` and `IsDefEq.reduce_forallE` -- are the shape the
Π-injectivity `trans` case wants (`Theory/Typing/Injectivity.lean:556`, "needs `e₂` to
reduce to a Π").  This file measures what those two statements *forbid*, without using
either of them, and therefore without inheriting their `sorryAx`.

## The finding

The pattern language of `Theory/Typing/Pattern.lean` puts a **constructor** at the major
premise of every ι/quotient rule:

    SimplePattern.iota r m c n |>.toPattern
      = .app (.varN (.const r) m) (.varN (.const c) n)      -- `Pattern.lean:293`

and `Pattern.Matches` is syntactic, so a redex whose major premise is a *variable* matches
nothing.  Hence `whnf_app_bvar` below: **`f x` is weak-head normal whenever `f` is and `f`
is not a `.lam`, for any `x` a bound variable** -- no `WHRed` rule fires, whatever the
`Params` instance registers.

That is exactly the K-redex `rec C ms is h` with `h` a variable of an inductive *predicate*
type.  Under proof irrelevance such an `h` is definitionally the constructor, so the redex
*is* definitionally equal to its ι-contractum, while being weak-head normal.

Two rules that both Carneiro's κ-reduction and the real Lean kernel have, and this tree's
`Pat` does not:

* Carneiro, *The Type Theory of Lean*, `unique.tex:103` (stated) / `:107` (explained) -- the rule named there `K⁺`:
  `P` SS inductive, `Γ ⊢ intro inv[p,h] : α  ⟹  Γ ⊢ rec_P C e p h ↝_κ e inv[p,h] v`,
  which fires at an **arbitrary** major premise `h`.  `unique.tex:66` says in as many words
  that without such a device "the standard formulation of the Church-Rosser theorem ... is
  not true ... because of proof irrelevance".
* `~/lean4/src/kernel/inductive.cpp:595` (`init_K_target`) and
  `~/lean4/src/kernel/inductive.h:90,135` -- K-like reduction, for a single-constructor
  inductive predicate whose constructor has no fields beyond the parameters.  This tree's
  *implementation* has it too (`Lean4Lean/Inductive/Reduce.lean`, `toCtorWhenK`); only
  `Theory/` does not.

## What is proved here

* `whnf_app_bvar` -- the stuck-redex lemma, unconditional in the `Params` instance.
* `ReduceSortStmt` / `ReduceForallEStmt` -- `IsDefEq.reduce_sort`'s and
  `IsDefEq.reduce_forallE`'s types, verbatim, packaged as `Prop`s so that they can be
  *hypotheses*.  `reduceSortStmt_holds` / `reduceForallEStmt_holds` prove each **by** the
  corresponding theorem, so these are not paraphrases (those two are `sorryAx`-tainted, by
  inheritance, and that is the point of stating them).
* `not_reduceSortStmt_of_stuck` / `not_reduceForallEStmt_of_stuck` -- **`sorry`-free**: a
  weak-head-normal application to a variable that is definitionally a sort (resp. a Π)
  refutes the corresponding statement outright.

So the refutation of both is reduced to a single remaining obligation, stated in one place:

> **(K)** exhibit a `Params` instance and a context `Γ` with `f` weak-head normal, not a
> `.lam`, and `Γ ⊢ f (.bvar i) ≡ .sort u : A` (or `≡ .forallE A B : V`).

`docs/handoff-headreduction.md` prices (K).  Nothing in this file assumes it.
-/

namespace Lean4Lean
namespace VEnv

open VExpr

variable [Params]
open Params

/-- **The stuck-redex lemma.**  No weak-head rule fires on `f x` when `f` is weak-head
normal and not a `.lam` and `x` is a bound variable:

* `WHRed.app` would need `f` to reduce;
* `WHRed.major` would need the *argument* to reduce, and a `.bvar` does not;
* `WHRed.beta` would need `f` to be a `.lam`;
* `WHRed.extra` would need a registered pattern to match `f x`, and by `Params.pat_simple`
  every registered pattern is `.const c` (which does not match an `.app`) or
  `.app _ (.varN (.const c) n)`, whose argument position demands a `.const`-headed
  application -- never a `.bvar`.

Nothing here depends on *which* rules the environment registers, so the lemma holds at every
`Params` instance, the ones carrying ι and quotient rules included. -/
theorem whnf_app_bvar {Γ : List VExpr} {f : VExpr} {i : Nat}
    (hf : WHNF Γ f) (hlam : ∀ A e, f ≠ .lam A e) : WHNF Γ (.app f (.bvar i)) := by
  intro e' H
  cases H with
  | app h1 => exact hf _ h1
  | major _ h2 => exact WHNF.bvar _ h2
  | beta => exact hlam _ _ rfl
  | extra h1 h2 _ =>
    obtain ⟨sp, rfl⟩ := pat_simple h1
    cases sp with
    | defn c => cases h2
    | iota r m c n =>
      cases h2 with
      | app _ ha =>
        cases n with
        | zero => cases ha
        | succ n => cases ha

/-- Corollary: the same term is stuck under the reflexive-transitive closure. -/
theorem whRedS_app_bvar_eq {Γ : List VExpr} {f e' : VExpr} {i : Nat}
    (hf : WHNF Γ f) (hlam : ∀ A e, f ≠ .lam A e)
    (H : WHRedS Γ (.app f (.bvar i)) e') : e' = .app f (.bvar i) :=
  ((whnf_app_bvar hf hlam).whRedS H).symm

/-! ## The two statements, verbatim

The two `Prop`s below are `IsDefEq.reduce_sort`'s and `IsDefEq.reduce_forallE`'s types with
**every binder made explicit** and nothing else changed.  Making them explicit is forced --
a `Prop`-valued `def` cannot be introduced by `fun` past an implicit binder -- and it is
harmless: `reduceSortStmt_holds` / `reduceForallEStmt_holds` below prove each **by** the
corresponding theorem, so these are the theorems' types and not paraphrases. -/

/-- `IsDefEq.reduce_sort`'s type, packaged so it can be a hypothesis. -/
def ReduceSortStmt : Prop :=
  ∀ (Γ : List VExpr) (e : VExpr) (u : VLevel) (A : VExpr),
    OnCtx Γ (Params.env.IsType Params.univs) →
    Params.env.IsDefEq Params.univs Γ e (.sort u) A →
    ∃ u', WHRedS Γ e (.sort u') ∧ u' ≈ u

/-- `IsDefEq.reduce_forallE`'s type, packaged so it can be a hypothesis. -/
def ReduceForallEStmt : Prop :=
  ∀ (Γ : List VExpr) (e A B V : VExpr),
    OnCtx Γ (Params.env.IsType Params.univs) →
    Params.env.IsDefEq Params.univs Γ e (.forallE A B) V →
    ∃ A' B', WHRedS Γ e (.forallE A' B')

/-- Anti-strawman: `ReduceSortStmt` is `IsDefEq.reduce_sort`'s type.
**`sorryAx`-tainted**, by inheritance -- deliberately. -/
theorem reduceSortStmt_holds : ReduceSortStmt :=
  fun _ _ _ _ hΓ H => IsDefEq.reduce_sort hΓ H

/-- Anti-strawman: `ReduceForallEStmt` is `IsDefEq.reduce_forallE`'s type.
**`sorryAx`-tainted**, by inheritance -- deliberately. -/
theorem reduceForallEStmt_holds : ReduceForallEStmt :=
  fun _ _ _ _ _ hΓ H => IsDefEq.reduce_forallE hΓ H

/-! ## What a stuck K-redex does to them -/

/-- **A stuck application that is definitionally a sort refutes `reduce_sort`.**
`sorry`-free: it uses `whnf_app_bvar` and `WHNF.whRedS`, neither of which touches
`ChurchRosser.lean`. -/
theorem not_reduceSortStmt_of_stuck {Γ : List VExpr} {f A : VExpr} {i : Nat} {u : VLevel}
    (hΓ : OnCtx Γ (Params.env.IsType Params.univs))
    (hf : WHNF Γ f) (hlam : ∀ A e, f ≠ .lam A e)
    (H : Params.env.IsDefEq Params.univs Γ (.app f (.bvar i)) (.sort u) A) :
    ¬ ReduceSortStmt := by
  intro hs
  obtain ⟨u', hred, -⟩ := hs _ _ _ _ hΓ H
  exact absurd (whRedS_app_bvar_eq hf hlam hred) nofun

/-- **A stuck application that is definitionally a Π refutes `reduce_forallE`.**
`sorry`-free, for the same reason. -/
theorem not_reduceForallEStmt_of_stuck {Γ : List VExpr} {f A B V : VExpr} {i : Nat}
    (hΓ : OnCtx Γ (Params.env.IsType Params.univs))
    (hf : WHNF Γ f) (hlam : ∀ A e, f ≠ .lam A e)
    (H : Params.env.IsDefEq Params.univs Γ (.app f (.bvar i)) (.forallE A B) V) :
    ¬ ReduceForallEStmt := by
  intro hs
  obtain ⟨A', B', hred⟩ := hs _ _ _ _ _ hΓ H
  exact absurd (whRedS_app_bvar_eq hf hlam hred) nofun

/-- The two packaged together: **no `Params` instance can host a stuck application that is
definitionally a sort**, if `IsDefEq.reduce_sort` is to hold there.  This is the exact
residual obligation `docs/handoff-headreduction.md` calls **(K)**. -/
theorem reduceSortStmt_forbids_stuck {Γ : List VExpr} {f A : VExpr} {i : Nat} {u : VLevel}
    (hs : ReduceSortStmt)
    (hΓ : OnCtx Γ (Params.env.IsType Params.univs))
    (hf : WHNF Γ f) (hlam : ∀ A e, f ≠ .lam A e) :
    ¬ Params.env.IsDefEq Params.univs Γ (.app f (.bvar i)) (.sort u) A :=
  fun H => not_reduceSortStmt_of_stuck hΓ hf hlam H hs

end VEnv
end Lean4Lean
