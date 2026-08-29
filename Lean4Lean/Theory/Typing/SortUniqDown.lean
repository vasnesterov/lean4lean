import Lean4Lean.Theory.Typing.SortUniq
import Lean4Lean.Theory.Typing.DeclRules
import Lean4Lean.Theory.Typing.CycleConv

/-!
# `SortUniq` decided: it is *below* nothing, and *above* `sort_inv`

`Theory/Typing/SortUniq.lean` states universe uniqueness as a hypothesis and derives
`sort_not_proof` from it; `Theory/Typing/SortUniqFacts.lean` gives an upper bound
(`SortUniq` follows from `IsDefEq.uniq` and `IsDefEqU.sort_inv`).  Both were read as saying
that `SortUniq` is a cheap keystone: close it and four of `Injectivity.lean`'s seven holes
lose their hard case, leaving normalisation (`sort_inv`'s `trans`) as a *separate*
obligation.

This file establishes the missing **lower** bound, and it goes the other way:

> `sort_inv_of_sortUniq` — **`SortUniq` implies `IsDefEqU.sort_inv` outright, `trans` case
> and all, with no normalisation argument anywhere.**  Machine-checked, `sorryAx`-free.

So the two statements the brief called "two primitives" are not independent: universe
uniqueness *contains* sort injectivity.  `SortUniq` is not a way around normalisation; it is
at least as strong as the statement normalisation was wanted for.

**Why the implication exists here and not in the reference.**  It is a consequence of this
tree's *type-indexed* conversion judgment.  `IsDefEqU Γ (.sort u) (.sort v)` unfolds to
`∃ A, IsDefEq Γ (.sort u) (.sort v) A`: a single `A` typing **both** endpoints.  That hands
the proof two typings of one term (`.sort v : A` and `.sort v : .sort (.succ v)`), which is
exactly `SortUniq`'s premise shape.  Carneiro's conversion judgment
(`~/lean-type-theory/axioms.tex:30-41`) is three-place and carries no type, so `sort_inv`
there is *not* a consequence of universe uniqueness.  `Injectivity.lean`'s docstring names
the type index as the port artifact that makes `uniq` a theorem rather than a rule; the same
artifact is what makes `sort_inv` a corollary of `SortUniq`.

## The statement as written is false

`VEnv.SortUniq` carries **no hypothesis on `env`**.  `sortUniq_badEnv` below refutes it:
one `.sort .zero ≡ .sort .zero : .sort 2` rule makes `.sort .zero` inhabit both `.sort 1`
and `.sort 2`, and `1 ≉ 2`.  Both level guards and `OnCtx [] _` hold; the guards analysed in
`SortUniq.lean`'s docstring are not the ones that were missing.

This is a missing-guard defect, not a refutation of the intended fact: `badEnv_not_wf`
machine-checks that the witness environment is not `VEnv.WF`, by the already-proved
`VEnv.WF.instL_lhs_ne_sort` ("no rule rewrites a sort").  The statement that has to be
targeted is therefore `∀ env, env.WF → env.SortUniq U`, which is what
`SortUniqFacts.WF.sortUniq` already states and what every consumer can supply.
-/

namespace Lean4Lean
namespace VEnv

variable {env : VEnv} {U : Nat} {Γ : List VExpr} {u v : VLevel}

/-! ## The lower bound: `SortUniq → sort_inv`

`sort_inv_of_sortUniq` moved to `Theory/Typing/SortUniq.lean` so that
`Theory/Typing/Injectivity.lean` — which cannot import this file (`CycleConv` imports
`Injectivity`) — can use it to prove `IsDefEqU.sort_inv`.  Statement unchanged. -/

/-- The `Ordered`-free packaging: `SortUniq` for a `VEnv.WF` environment gives `sort_inv`. -/
theorem sort_inv_of_sortUniq' (huniq : env.SortUniq U) (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U))
    (H : env.IsDefEqU U Γ (.sort u) (.sort v)) : u ≈ v :=
  sort_inv_of_sortUniq huniq henv.ordered hΓ H

/-! ## The statement as written is false -/

/-- `Sort 0 ≡ Sort 0 : Sort 2` — a rule that retypes a sort two levels up. -/
def badDefEq : VDefEq :=
  { uvars := 0, lhs := .sort .zero, rhs := .sort .zero,
    type := .sort (.succ (.succ .zero)) }

/-- The environment carrying exactly `badDefEq`. -/
def badEnv : VEnv where
  constants _ := none
  defeqs df := df = badDefEq

theorem badEnv_defeq : badEnv.defeqs badDefEq := rfl

/-- `.sort .zero : .sort 2` in `badEnv`, by the `extra` rule. -/
theorem badEnv_sort_two (U : Nat) :
    badEnv.HasType U [] (.sort .zero) (.sort (.succ (.succ .zero))) :=
  IsDefEq.extra (env := badEnv) (uvars := U) (Γ := []) (df := badDefEq) (ls := [])
    badEnv_defeq (by simp) rfl

/-- **`VEnv.SortUniq` as stated is false.**  It carries no hypothesis on `env`, and one
`.sort`-headed rule refutes it.  Every guard in the statement holds at this witness:
`OnCtx [] _` is trivial and both levels are `WF` at any `U` (they are closed). -/
theorem sortUniq_badEnv (U : Nat) : ¬ badEnv.SortUniq U := by
  intro h
  have := h (Γ := []) (e := .sort .zero) trivial (by trivial) (by trivial)
    (HasType.sort (U := U) (l := .zero) trivial) (badEnv_sort_two U)
  exact absurd (congrFun this []) (by simp [VLevel.eval])

/-- …and the witness is a *missing guard*, not a refutation of the intended fact:
`badEnv` is not a well-formed environment.  `VEnv.WF.instL_lhs_ne_sort` — "no rule rewrites
a sort", already proved in `Theory/Typing/DeclRules.lean` — excludes exactly this shape. -/
theorem badEnv_not_wf : ¬ badEnv.WF :=
  fun h => h.instL_lhs_ne_sort badEnv_defeq [] .zero rfl

/-! ## Non-vacuity: fired at `CycleConv.propLoopEnv`

`propLoopEnv` is a proved-`VEnv.WF` environment (`propLoopEnv_wf`) whose head reduction has
a two-cycle, so `propLoop_headStep_not_wf` machine-checks that **no normalisation argument
terminates there**.  `sort_inv_of_sortUniq` still fires: it is not a normalisation argument
in disguise. -/

theorem propLoop_sort_inv {U Γ u v} (huniq : propLoopEnv.SortUniq U)
    (hΓ : OnCtx Γ (propLoopEnv.IsType U))
    (H : propLoopEnv.IsDefEqU U Γ (.sort u) (.sort v)) : u ≈ v :=
  sort_inv_of_sortUniq huniq propLoopEnv_wf.ordered hΓ H

/-- The relation the lemma constrains is inhabited at this environment — the conclusion is
not vacuously about an empty premise. -/
theorem propLoop_sort_defeq_refl : propLoopEnv.IsDefEqU 0 [] (.sort .zero) (.sort .zero) :=
  ⟨_, IsDefEq.sortDF trivial trivial rfl⟩

/-- …and it is not total either: granted `SortUniq`, `Prop` and `Type` stay apart in an
environment with a δ-cycle. -/
theorem propLoop_zero_not_defeq_one (huniq : propLoopEnv.SortUniq 0) :
    ¬ propLoopEnv.IsDefEqU 0 [] (.sort .zero) (.sort (.succ .zero)) := fun H =>
  absurd (congrFun (propLoop_sort_inv (Γ := []) huniq trivial H) []) (by simp [VLevel.eval])

end VEnv
end Lean4Lean

namespace Lean4Lean
namespace VEnv

variable {env : VEnv} {U : Nat}

/-! ## The sandwich, as hypothesis-level implications

`Theory/Typing/SortUniqFacts.lean` derives `SortUniq` from `IsDefEq.uniq` and
`IsDefEqU.sort_inv`, but that derivation is `sorryAx`-tainted (both inputs are open), so it
cannot be used to compare *strengths*.  The two `Prop`s below package the same two inputs as
hypotheses, and the resulting implications are `sorryAx`-free.  Together with
`sort_inv_of_sortUniq` they pin `SortUniq` exactly:

    UniqTy ∧ SortInv  →  SortUniq  →  SortInv

i.e. **`SortUniq` and `SortInv` are the same statement modulo `UniqTy`**, and `UniqTy` is
`IsDefEq.uniq`, which the cone measurement in `docs/handoff-sortuniq.md` shows is proved once
`IsDefEqU.sort_inv` and `IsDefEqU.forallE_inv_stratified` are supplied. -/

/-- Unique typing, packaged as a hypothesis: the statement of `IsDefEq.uniq`. -/
def UniqTy (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {e A B : VExpr}, OnCtx Γ (env.IsType U) →
    env.HasType U Γ e A → env.HasType U Γ e B → env.IsDefEqU U Γ A B

/-- Sort injectivity, packaged as a hypothesis: the statement of `IsDefEqU.sort_inv`. -/
def SortInv (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {u v : VLevel}, OnCtx Γ (env.IsType U) →
    env.IsDefEqU U Γ (.sort u) (.sort v) → u ≈ v

/-- **Upper bound**: `SortUniq` follows from unique typing plus sort injectivity. -/
theorem sortUniq_of (huq : env.UniqTy U) (hsi : env.SortInv U) : env.SortUniq U :=
  fun hΓ _ _ h1 h2 => hsi hΓ (huq hΓ h1 h2)

/-- **Lower bound**: `SortUniq` gives sort injectivity back, on its own. -/
theorem sortInv_of_sortUniq (huniq : env.SortUniq U) (henv : Ordered env) : env.SortInv U :=
  fun hΓ H => sort_inv_of_sortUniq huniq henv hΓ H

end VEnv
end Lean4Lean
