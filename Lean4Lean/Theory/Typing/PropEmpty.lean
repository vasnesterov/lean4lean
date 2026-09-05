import Lean4Lean.Theory.Typing.PropAtWF

/-!
# `VEnv.PropAgreeOn (∅ : VEnv) 0`: the bottom of the family, attacked

`Theory/Typing/PropAtWF.lean` ends by naming `PropAgreeOn (∅ : VEnv) 0` as the single open
hypothesis at the bottom of both antitone chains (`PropAgreeOn.mono_env`,
`PropAgreeOn.mono_univs`) and the one a round should attack.  This is that round.

## Verdict

**Still open — neither proved nor refuted here.**  What is new is that the target has been made
*strictly smaller*, in the one coordinate nobody had tried: **its context.**

## §1 The context quantifier and the `OnCtx` guard are both removable

`propAgreeOn_iff_nil`: over any `Ordered` environment,

    PropAgreeOn env U  ↔  PropAgreeNil env U

where `PropAgreeNil` is `PropAgreeOn`'s instance at `Γ = []` — no context quantifier and no
`OnCtx` guard at all.  So the guard that has been threaded through this entire corner (and that
`SetModel/PropSplitAudit` added to `PropSplit`'s two fields on 2026-09-02, and that
`PropAgreeLift` restates twice) is **not part of the content of the target**: it is bookkeeping
that Π-abstraction discharges.

The mechanism is the one place where `PropAgreeOn`'s deliberately weak conclusion pays off.
Abstracting the outermost context entry sends the tuple

    (A₁::Γ,  e,  A,  A',  u,  u')   ↦   (Γ,  .lam A₁ e,  .forallE A₁ A,  .forallE A₁ A',
                                          .imax u₁ u,  .imax u₁ u')

by `IsDefEq.lamDF` and `IsDefEq.forallEDF` alone, and `imax_eval_zero_iff` says
`(.imax u₁ u).eval ls = 0 ↔ u.eval ls = 0` — **the propositionhood bit is invariant under
Π-abstraction**, because `Nat.imax` is `0` exactly when its second argument is.  A conclusion
of the form `u ≈ u'` (i.e. `SortUniq`'s) does *not* survive this transport: `.imax u₁ u ≈ .imax u₁ u'`
is strictly weaker than `u ≈ u'`.  So this reduction is available to `PropAgreeOn` and not to the
hypothesis it was introduced to replace, which is a fact about the two statements and not about
this file.

At `∅` the `Ordered` side condition is free (`PiInvVac.empty_ordered`), so
`propAgreeOn_empty_iff_nil` is an unconditional restatement of the round's target.

## §2 Anti-vacuity, in both directions, at `Γ = []`

A reduction to a smaller class is worthless if the smaller class is empty, and the check inverts
for the negatives.  Both are recorded:

* the reduced statement's **premises** still fire at `Γ = []` with the two types syntactically
  different — `SortInvIndep.propAgreeOn_premises_fire` is already stated there, so §1 loses no
  content (`propAgreeNil_premises_fire`);
* conversion at `∅` is **not** the identity, so §1 has not reduced the target to a triviality:
  `empty_conv_nontrivial` exhibits a `β`-step and `empty_proofIrrel_fires` exhibits a
  `proofIrrel` step between two *syntactically distinct* terms, both at `∅`, both hole-free.
  `empty_no_defeqs` kills `IsDefEq.extra` and the absence of constants kills `IsDefEq.constDF`;
  every other rule of `Theory/Typing/Basic.IsDefEq` is live at `∅`, and the two rules the open
  residual turns on (`appDF` with `beta`, and `proofIrrel`) are among the live ones.  **This is
  why `env = ∅` does not shrink the residual**: `∅`-ness deletes exactly the two rules that the
  `app` case never uses.

## §3 The limits, proved rather than asserted

`propAgreeNil_ls_irrelevant`: `PropAgreeOn ∅ 0`'s own conclusion is `ls`-free, because
`u.WF 0` forbids `.param` (`PropAgreeGuarded.eval_indep_of_wf_zero`).  At `U ≥ 1` the `∀ ls`
quantifier does genuine work — `param_eval_zero_not_indep` exhibits a level that is `WF 1`, is
`0` at `ls = [0]` and nonzero at `ls = [1]` — so the bottom of the `U`-chain says nothing
whatever about parametric universes.  Together with `PropAtWF.propAgreeOn_bottom` this is the
exact measure of how weak the round's target is: it is the `.param`-free, closed-context,
constant-free, rule-free corner of the family.

`PropAgreeNil.mono_env` and `PropAgreeNil.mono_univs`: the reduced statement is antitone in both
coordinates too, so §1 did not move the target in the lattice — `PropAgreeNil (∅ : VEnv) 0` is
still the bottom.  `propAgreeNil_empty_of_any` is the one-way direction, and
`forallEProofPair_empty_dies_of_nil` is the entry-kill it drives: a positive would settle the
`proofIrrel` route's entry **only at `∅`**, since `mono_env` runs from larger environments to
smaller ones and there is no converse in the tree.
-/

namespace Lean4Lean
namespace VEnv

variable {env : VEnv} {U : Nat}

/-! ## §0 The level arithmetic that makes §1 work -/

/-- **The propositionhood bit of an `imax` is its codomain's.**  `Nat.imax a b = 0 ↔ b = 0`:
if `b = 0` the `imax` is `0` by definition, and if `b ≠ 0` it is `max a b ≥ b > 0`.

This is the whole reason §1 goes through for `PropAgreeOn` and not for `SortUniq`. -/
theorem imax_eval_zero_iff (u v : VLevel) (ls : List Nat) :
    (VLevel.imax u v).eval ls = 0 ↔ v.eval ls = 0 := by
  simp only [VLevel.eval, Lean.Nat.imax, Nat.max_eq_max]
  split <;> omega

/-! ## §1 The closed-context form, and the equivalence -/

/-- **`PropAgreeOn` at the empty context**: no context quantifier, no `OnCtx` guard.  Compare
`SortInvIndep.PropAgreeOn`, from which this drops exactly `∀ Γ` and `OnCtx Γ (env.IsType U)`. -/
def PropAgreeNil (env : VEnv) (U : Nat) : Prop :=
  ∀ {e A A' : VExpr} {u u' : VLevel} {ls : List Nat},
    u.WF U → u'.WF U →
    env.HasType U [] e A → env.HasType U [] e A' →
    env.HasType U [] A (.sort u) → env.HasType U [] A' (.sort u') →
    (u.eval ls = 0 ↔ u'.eval ls = 0)

/-- The easy half: `Γ = []` is an instance, and `OnCtx [] _` is `True`. -/
theorem PropAgreeOn.nil (h : PropAgreeOn env U) : PropAgreeNil env U :=
  fun hu hu' he he' hA hA' => h (Γ := []) trivial hu hu' he he' hA hA'

/-- **The hard half: one Π-abstraction step.**  Given the whole tuple at `A₁::Γ`, `IsDefEq.lamDF`
and `IsDefEq.forallEDF` move it to `Γ` with both levels wrapped in `.imax u₁ ·`, and
`imax_eval_zero_iff` says the two propositionhood bits are unchanged.  `u₁` is obtained *once*
from the guard's own entry (`IsDefEq.sort_r` for its well-formedness), so the same `u₁` wraps
both sides. -/
theorem PropAgreeNil.propAgreeOn (henv : Ordered env) (h : PropAgreeNil env U) :
    PropAgreeOn env U := by
  suffices H : ∀ Γ : List VExpr, OnCtx Γ (env.IsType U) →
      ∀ {e A A' : VExpr} {u u' : VLevel} {ls : List Nat}, u.WF U → u'.WF U →
      env.HasType U Γ e A → env.HasType U Γ e A' →
      env.HasType U Γ A (.sort u) → env.HasType U Γ A' (.sort u') →
      (u.eval ls = 0 ↔ u'.eval ls = 0) by
    intro Γ e A A' u u' ls hΓ hu hu' he he' hA hA'
    exact H Γ hΓ hu hu' he he' hA hA'
  intro Γ
  induction Γ with
  | nil => intro _ e A A' u u' ls hu hu' he he' hA hA'; exact h hu hu' he he' hA hA'
  | cons A₁ Γ ih =>
    intro hΓ e A A' u u' ls hu hu' he he' hA hA'
    obtain ⟨hΓ', u₁, hA₁⟩ := hΓ
    have hu₁ : u₁.WF U := hA₁.sort_r henv hΓ'
    rw [← imax_eval_zero_iff u₁ u ls, ← imax_eval_zero_iff u₁ u' ls]
    exact ih hΓ' (u := .imax u₁ u) (u' := .imax u₁ u') ⟨hu₁, hu⟩ ⟨hu₁, hu'⟩
      (IsDefEq.lamDF hA₁ he) (IsDefEq.lamDF hA₁ he')
      (IsDefEq.forallEDF hA₁ hA) (IsDefEq.forallEDF hA₁ hA')

/-- **§1's result.**  Over any `Ordered` environment the two statements are the same statement:
the context quantifier and the `OnCtx` guard carry no content in `PropAgreeOn`. -/
theorem propAgreeOn_iff_nil (henv : Ordered env) : PropAgreeOn env U ↔ PropAgreeNil env U :=
  ⟨PropAgreeOn.nil, PropAgreeNil.propAgreeOn henv⟩

/-- **The round's target, restated with no context and no guard.**  `Ordered` is free at `∅`. -/
theorem propAgreeOn_empty_iff_nil :
    PropAgreeOn (∅ : VEnv) 0 ↔ PropAgreeNil (∅ : VEnv) 0 :=
  propAgreeOn_iff_nil empty_ordered

/-- The reduction composes with the antitone bound: **one** closed-context instance anywhere in
the class supplies the round's target. -/
theorem propAgreeOn_empty_of_nil_anywhere {env : VEnv} (henv : Ordered env)
    (h : PropAgreeNil env U) : PropAgreeOn (∅ : VEnv) 0 :=
  propAgreeOn_bottom (h.propAgreeOn henv)

/-- …and it composes with `PiInvVac`'s entry-kill: the `proofIrrel` route's entry at `∅` dies from
a closed-context statement about `∅` alone. -/
theorem forallEProofPair_empty_dies_of_nil (h : PropAgreeNil (∅ : VEnv) 0) :
    (¬ ForallEProofPair (∅ : VEnv) 0) ∧ (¬ SortZeroConvProp (∅ : VEnv) 0) :=
  forallEProofPair_empty_dies_of_weakest (propAgreeOn_empty_iff_nil.2 h)


/-! ## §1b The reduced statement sits in the same place in the lattice -/

/-- `PropAgreeNil` is **antitone** in the environment, exactly as `PropAgreeOn` is
(`PropAtWF.PropAgreeOn.mono_env`): the reduction of §1 does not move the statement in the
lattice, so `PropAgreeNil (∅ : VEnv) 0` is still the *bottom* and still the weakest thing to
attack. -/
theorem PropAgreeNil.mono_env {env env' : VEnv} (le : env ≤ env') (h : PropAgreeNil env' U) :
    PropAgreeNil env U := fun hu hu' he he' hA hA' =>
  h hu hu' (he.mono le) (he'.mono le) (hA.mono le) (hA'.mono le)

/-- …and antitone in the universe count. -/
theorem PropAgreeNil.mono_univs {U U' : Nat} (le : U ≤ U') (h : PropAgreeNil env U') :
    PropAgreeNil env U := fun hu hu' he he' hA hA' =>
  h (hu.mono le) (hu'.mono le) (he.mono_uvars le) (he'.mono_uvars le)
    (hA.mono_uvars le) (hA'.mono_uvars le)

/-- **The one-way direction, spelled out.**  Any `PropAgreeOn` instance anywhere in the class
delivers the round's target in its reduced form.  There is no converse in the tree, and §3 of the
module docstring says why one should not be expected. -/
theorem propAgreeNil_empty_of_any {env : VEnv} (h : PropAgreeOn env U) :
    PropAgreeNil (∅ : VEnv) 0 :=
  propAgreeOn_empty_iff_nil.1 (propAgreeOn_bottom h)

/-! ## §2 Anti-vacuity at `Γ = []`, and why `∅` does not shrink the residual -/

/-- **§1 loses no content: the reduced statement's premises still fire.**  All six slots of
`PropAgreeNil` are satisfied simultaneously, at *every* environment hence at `∅`, with the two
types **syntactically different** — this is `SortInvIndep.propAgreeOn_premises_fire`, whose
witness was already at `Γ = []`, repackaged in the reduced statement's own shape. -/
theorem propAgreeNil_premises_fire :
    (VExpr.sort (.succ .zero) : VExpr) ≠ .sort (.succ (.imax .zero .zero)) ∧
    (VLevel.succ .zero).WF 0 ∧ (VLevel.succ (.imax .zero .zero)).WF 0 ∧
    env.HasType 0 [] (.sort .zero) (.sort (.succ .zero)) ∧
    env.HasType 0 [] (.sort .zero) (.sort (.succ (.imax .zero .zero))) ∧
    env.HasType 0 [] (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) ∧
    env.HasType 0 [] (.sort (.succ (.imax .zero .zero)))
      (.sort (.succ (.succ (.imax .zero .zero)))) :=
  have ⟨_, hne, h1, h2, h3, h4⟩ := propAgreeOn_premises_fire (env := env)
  ⟨hne, trivial, ⟨trivial, trivial⟩, h1, h2, h3, h4⟩

/-- **Conversion at `∅` is not the identity: `β` fires**, between two syntactically distinct
closed terms, at `Γ = []`.  So §1 has not reduced the target to a statement about a trivial
relation, and `empty_no_defeqs` (which kills `IsDefEq.extra`) does not make `IsDefEq (∅ : VEnv) 0`
syntactic equality. -/
theorem empty_conv_nontrivial :
    (VExpr.app (.lam (.sort (.succ .zero)) (.bvar 0)) (.sort .zero) : VExpr) ≠ .sort .zero ∧
    (∅ : VEnv).IsDefEq 0 [] (.app (.lam (.sort (.succ .zero)) (.bvar 0)) (.sort .zero))
      (.sort .zero) (.sort (.succ .zero)) := by
  refine ⟨by simp, ?_⟩
  have hbv : (∅ : VEnv).HasType 0 [.sort (.succ .zero)] (.bvar 0) (.sort (.succ .zero)) := by
    have := IsDefEq.bvar (env := (∅ : VEnv)) (uvars := 0)
      (Γ := [.sort (.succ .zero)]) (A := (VExpr.sort (.succ .zero)).lift) .zero
    simpa [VExpr.lift, VExpr.liftN, VEnv.HasType] using this
  have := IsDefEq.beta (env := (∅ : VEnv)) (uvars := 0) (Γ := []) (A := .sort (.succ .zero))
    (B := .sort (.succ .zero)) (e := .bvar 0) (e' := .sort .zero) hbv
    (HasType.sort (show (VLevel.zero).WF 0 from trivial))
  simpa [VExpr.inst, VExpr.instVar] using this

/-- **`proofIrrel` fires at `∅` too**, under the `OnCtx` guard, between two syntactically distinct
terms — the context is `P : Prop, h : P, h' : P`, written innermost-last as
`[.bvar 1, .bvar 0, .sort .zero]`, and every entry is an `∅.IsType 0`.

This is the anti-vacuity check that matters for the refutation direction: the rule a refutation of
`PropAgreeOn (∅ : VEnv) 0` would have to run through is **live at `∅`**, and the guard does not
exclude its premise shape.  Together with `empty_conv_nontrivial` this is the machine-checked form
of "`∅`-ness deletes only `constDF` and `extra`, and the `app` case uses neither". -/
theorem empty_proofIrrel_fires :
    OnCtx [.bvar 1, .bvar 0, .sort .zero] ((∅ : VEnv).IsType 0) ∧
    (VExpr.bvar 0 : VExpr) ≠ .bvar 1 ∧
    (∅ : VEnv).IsDefEq 0 [.bvar 1, .bvar 0, .sort .zero] (.bvar 0) (.bvar 1) (.bvar 2) := by
  have hP : (∅ : VEnv).HasType 0 [.sort .zero] (.bvar 0) (.sort .zero) := by
    have := IsDefEq.bvar (env := (∅ : VEnv)) (uvars := 0) (Γ := [.sort .zero])
      (A := (VExpr.sort .zero).lift) .zero
    simpa [VExpr.lift, VExpr.liftN, VEnv.HasType] using this
  have hP' : (∅ : VEnv).HasType 0 [.bvar 0, .sort .zero] (.bvar 1) (.sort .zero) := by
    have := IsDefEq.bvar (env := (∅ : VEnv)) (uvars := 0) (Γ := [.bvar 0, .sort .zero])
      (A := ((VExpr.sort .zero).lift).lift) (.succ .zero)
    simpa [VExpr.lift, VExpr.liftN, VEnv.HasType] using this
  have hp2 : (∅ : VEnv).HasType 0 [.bvar 1, .bvar 0, .sort .zero] (.bvar 2) (.sort .zero) := by
    have := IsDefEq.bvar (env := (∅ : VEnv)) (uvars := 0)
      (Γ := [.bvar 1, .bvar 0, .sort .zero])
      (A := (((VExpr.sort .zero).lift).lift).lift) (.succ (.succ .zero))
    simpa [VExpr.lift, VExpr.liftN, VEnv.HasType] using this
  have h0 : (∅ : VEnv).HasType 0 [.bvar 1, .bvar 0, .sort .zero] (.bvar 0) (.bvar 2) := by
    have := IsDefEq.bvar (env := (∅ : VEnv)) (uvars := 0)
      (Γ := [.bvar 1, .bvar 0, .sort .zero]) (A := (VExpr.bvar 1).lift) .zero
    simpa [VExpr.lift, VExpr.liftN, VEnv.HasType] using this
  have h1 : (∅ : VEnv).HasType 0 [.bvar 1, .bvar 0, .sort .zero] (.bvar 1) (.bvar 2) := by
    have := IsDefEq.bvar (env := (∅ : VEnv)) (uvars := 0)
      (Γ := [.bvar 1, .bvar 0, .sort .zero]) (A := ((VExpr.bvar 0).lift).lift)
      (.succ .zero)
    simpa [VExpr.lift, VExpr.liftN, VEnv.HasType] using this
  exact ⟨⟨⟨⟨trivial, _, HasType.sort (show (VLevel.zero).WF 0 from trivial)⟩, _, hP⟩, _, hP'⟩,
    by simp, IsDefEq.proofIrrel hp2 h0 h1⟩

/-! ## §3 The limits of the target, proved -/

/-- **At `U = 0` the `∀ ls` quantifier of `PropAgreeOn` is dead**, because `u.WF 0` forbids
`.param` — `PropAgreeGuarded.eval_indep_of_wf_zero`.  Stated for the reduced statement. -/
theorem propAgreeNil_ls_irrelevant {u : VLevel} (hu : u.WF 0) (ls ls' : List Nat) :
    (u.eval ls = 0 ↔ u.eval ls' = 0) :=
  iff_of_eq (congrArg (· = 0) (VLevel.eval_indep_of_wf_zero hu ls ls'))

/-- **…and at `U ≥ 1` it is not dead**, so the bottom of the `U`-chain says nothing whatever about
parametric universes: `.param 0` is `WF 1`, evaluates to `0` at `ls = [0]` and to `1` at `ls = [1]`.
This is the exact measure of what `PropAgreeOn.mono_univs`' descent to `U = 0` throws away. -/
theorem param_eval_zero_not_indep :
    ∃ u : VLevel, u.WF 1 ∧ u.eval [0] = 0 ∧ u.eval [1] ≠ 0 :=
  ⟨.param 0, Nat.zero_lt_one, rfl, by simp [VLevel.eval]⟩

section Audit
#print axioms Lean4Lean.VEnv.imax_eval_zero_iff
#print axioms Lean4Lean.VEnv.PropAgreeOn.nil
#print axioms Lean4Lean.VEnv.PropAgreeNil.propAgreeOn
#print axioms Lean4Lean.VEnv.propAgreeOn_iff_nil
#print axioms Lean4Lean.VEnv.propAgreeOn_empty_iff_nil
#print axioms Lean4Lean.VEnv.propAgreeOn_empty_of_nil_anywhere
#print axioms Lean4Lean.VEnv.forallEProofPair_empty_dies_of_nil
#print axioms Lean4Lean.VEnv.PropAgreeNil.mono_env
#print axioms Lean4Lean.VEnv.PropAgreeNil.mono_univs
#print axioms Lean4Lean.VEnv.propAgreeNil_empty_of_any
#print axioms Lean4Lean.VEnv.propAgreeNil_premises_fire
#print axioms Lean4Lean.VEnv.empty_conv_nontrivial
#print axioms Lean4Lean.VEnv.empty_proofIrrel_fires
#print axioms Lean4Lean.VEnv.propAgreeNil_ls_irrelevant
#print axioms Lean4Lean.VEnv.param_eval_zero_not_indep
end Audit

end VEnv
end Lean4Lean
