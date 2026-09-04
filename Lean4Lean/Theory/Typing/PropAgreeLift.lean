import Lean4Lean.Theory.Typing.PropConv
import Lean4Lean.Theory.Typing.UniqueTypingN

/-!
# Lifting route B above `Injectivity`, and measuring what it is worth

`docs/audit-hole-producers.md` §2.3 names exactly one "genuinely under-explored move" for the
three remaining open `Theory/` holes: migrate
`SetModel/PropAgreeWall.propTypeAgreeOnCtx_of_stratifiedN` (route B — the `sorryAx`-free
producer of the `OnCtx`-guarded prop-agreement statement) up out of `Theory/SetModel`, so that
`Theory/Typing/Injectivity.lean` — where holes #5 `IsDefEqU.forallE_inv_stratified` and #8
`WF.rigidShapeUniqNS` live — could cite it.  `docs/handoff-propagreelift.md` runs that move and
this file is its Lean half.  **The verdict is negative, and the negative half is the content.**

## What was already true before this file

The migration had **already been performed**, in a *stronger* form:
`Theory/Typing/PropAgreeGuarded.propAgreeOn_of_stratifiedNOn` is route B with the `OnCtx` guard
pushed onto its two hypotheses, `sorryAx`-free, in `Theory/Typing`, complete with local copies
of the one `SetModel` name route B's proof uses (`VLevel.equivZero_iff_eval_zero'`).  The audit
missed it.  What that file did *not* do is place it where `Injectivity` can see it:
`PropAgreeGuarded` imports `SortInvIndep → InjOneFact → … → Injectivity`, so it is **downstream**
of both holes.

## §1 What this file adds on the positive side, and it is small

§1 re-proves route B from imports that are **incomparable** with `Injectivity`
(`PropConv`, `UniqueTypingN`, and their closures — measured: neither reaches `Injectivity`, and
`Injectivity` reaches neither).  So `Injectivity.lean` *could* cite `propAgreeUp_of_stratifiedN`
after a one-line import, which is the strongest form of the audit's suggestion.  The conclusion
`PropAgreeUp` is `SortInvIndep.PropAgreeOn` and `SetModel/PropSplitAudit.PropTypeAgreeOnCtx`
verbatim (checked `Iff.rfl` in a scratch file importing both — recorded in
`docs/handoff-propagreelift.md` §2 M8; it cannot be checked *here*, since importing either would
recreate the downstream position this file exists to avoid).

That is a *relocation*, and relocations are not results.  Hence §2.

## §2 Why the relocation buys nothing, sharpened

`SortInvIndep.propAgree_conclusion_not_sortUniq` establishes that prop-agreement's conclusion
cannot deliver `SortUniq`'s by exhibiting **one** level pair (`1`, `2`) that agrees on the
propositionhood bit and is not `≈`.  Its own docstring records the limit: it does not say the
deficit is large, only that it is nonzero.  §2 closes that gap in the direction that is
available without a witness environment, and the statements are new:

* `equiv_iff_eval_nil_up` — at `U = 0`, `u ≈ u'` **is** `u.eval [] = u'.eval []`, a natural
  number;
* `propBit_of_both_nonzero` — at `U = 0`, **any two** levels that are both non-`Prop` satisfy
  prop-agreement's conclusion, at every `ls`.  So the conclusion is not merely weaker than `≈`;
  it is a **single bit**, and it is constant on the whole non-`Prop` class;
* `propBit_iff_eval_nil_zero` — and that bit is exactly `u.eval [] = 0`;
* `propAgree_deficit_infinite` — an infinite family of pairwise non-`≈` levels, all `WF 0`, all
  agreeing on the bit at every `ls`;
* `propAgree_deficit_unbounded` — the two levels can be forced to differ by an arbitrary
  amount.

Read together: at `U = 0` (the only index at which route B works at all —
`equivZero_iff_eval_zero` needs `u.WF 0`, and the step is refuted at `nv ≥ 2` by
`SetModel/NotProofNoModel.propAgree_pointwise_not_from_equivZero`) prop-agreement determines a
level to within **one of two classes**, while `SortUniq` — which is hole #5, by
`PiLevelPin.piInvStratApp_iff_sortUniq` — determines it up to `≈`, i.e. pins a natural number.
The gap is `2` against `ℕ`, and no amount of relocation narrows it.

## §3 The limits of *this* file, stated

1. §2 refutes the move "instantiate prop-agreement and read `SortUniq` off its conclusion".  It
   does **not** refute `PropAgreeUp env 0 → env.SortUniq 0` as an implication: that needs an
   environment satisfying the first and not the second, and this file exhibits none.  The gap is
   inherited verbatim from `SortInvIndep.propAgree_conclusion_not_sortUniq`, whose docstring
   states it, and it is the one place in this corner where new content is still available.
2. §1 is citable-in-principle from `Injectivity`.  It is not *cited*: the import must be added to
   `Injectivity.lean`, which this stream does not own.  The exact edit is written out in
   `docs/handoff-propagreelift.md` §3.  It should not be applied, for the reason §2 gives.
3. Route B's two hypotheses remain open at every index above `0`
   (`PropUniqN.zero` / `PropTypeAgreeN.zero` are the only unconditional instances), so §1 is a
   conditional, not a producer — exactly as it was in `SetModel`.
-/

namespace Lean4Lean

namespace VLevel

/-- At `nv = 0` a well-formed level has no parameters, so its value is assignment-independent.

A third copy of `SetModel/PreludeOracle.eval_const_of_wf_zero`; the second is
`Theory/Typing/PropAgreeGuarded.eval_indep_of_wf_zero`, which is unavailable here because that
file sits downstream of `Injectivity` and importing it would defeat this file's whole purpose.
The duplication is deliberate and is the price of the upstream position. -/
theorem eval_indep_of_wf_zero_up : ∀ {u : VLevel}, u.WF 0 → ∀ ls ls', u.eval ls = u.eval ls'
  | .zero, _, _, _ => rfl
  | .succ l, h, ls, ls' => by
    simp only [VLevel.eval, eval_indep_of_wf_zero_up (u := l) h ls ls']
  | .max l₁ l₂, h, ls, ls' => by
    simp only [VLevel.eval, eval_indep_of_wf_zero_up (u := l₁) h.1 ls ls',
      eval_indep_of_wf_zero_up (u := l₂) h.2 ls ls']
  | .imax l₁ l₂, h, ls, ls' => by
    simp only [VLevel.eval, eval_indep_of_wf_zero_up (u := l₁) h.1 ls ls',
      eval_indep_of_wf_zero_up (u := l₂) h.2 ls ls']
  | .param i, h, _, _ => absurd h (by simp [VLevel.WF])

/-- Hence at `nv = 0` the `≈ .zero` shape and the pointwise shape agree.  Upstream copy of
`Theory/Typing/PropAgreeGuarded.equivZero_iff_eval_zero'`. -/
theorem equivZero_iff_eval_zero_up {u : VLevel} (hu : u.WF 0) (ls : List Nat) :
    u ≈ (.zero : VLevel) ↔ u.eval ls = 0 := by
  rw [VLevel.equiv_def]
  refine ⟨fun h => by simpa [VLevel.eval] using h ls, fun h ls' => ?_⟩
  simp only [VLevel.eval]
  rw [eval_indep_of_wf_zero_up hu ls' ls]; exact h

/-! ## §2 The size of the deficit -/

/-- **At `U = 0`, `≈` is equality of one natural number.**  This is the yardstick §2 measures
against: `SortUniq`'s conclusion is `u ≈ u'`, and at the only index route B works at, that is
exactly `u.eval [] = u'.eval []`. -/
theorem equiv_iff_eval_nil_up {u u' : VLevel} (hu : u.WF 0) (hu' : u'.WF 0) :
    u ≈ u' ↔ u.eval [] = u'.eval [] := by
  refine ⟨fun h => VLevel.equiv_def.1 h [], fun h => VLevel.equiv_def.2 fun ls => ?_⟩
  rw [eval_indep_of_wf_zero_up hu ls [], eval_indep_of_wf_zero_up hu' ls [], h]

/-- **The deficit, structurally: prop-agreement's conclusion is constant on the non-`Prop`
class.**  Any two `WF 0` levels that are both non-`Prop` satisfy it, at every `ls`, with no
relation between them whatsoever.  This is the sharp form of "it delivers only the
propositionhood bit" that `SortInvIndep.lean`'s docstring asserts in prose and checks on a
single pair. -/
theorem propBit_of_both_nonzero {u u' : VLevel} (hu : u.WF 0) (hu' : u'.WF 0)
    (h : u.eval [] ≠ 0) (h' : u'.eval [] ≠ 0) : ∀ ls, (u.eval ls = 0 ↔ u'.eval ls = 0) := by
  intro ls
  rw [eval_indep_of_wf_zero_up hu ls [], eval_indep_of_wf_zero_up hu' ls []]
  exact ⟨fun hz => absurd hz h, fun hz => absurd hz h'⟩

/-- …and dually on the `Prop` class, so prop-agreement's conclusion **is** agreement of the
single bit `eval [] = 0`.  Two classes, against `ℕ`-many for `≈`. -/
theorem propBit_iff_eval_nil_zero {u u' : VLevel} (hu : u.WF 0) (hu' : u'.WF 0) :
    (∀ ls, (u.eval ls = 0 ↔ u'.eval ls = 0)) ↔ (u.eval [] = 0 ↔ u'.eval [] = 0) := by
  refine ⟨fun h => h [], fun h ls => ?_⟩
  rw [eval_indep_of_wf_zero_up hu ls [], eval_indep_of_wf_zero_up hu' ls []]
  exact h

/-- The level `n+1`, as a `param`-free `VLevel`: `WF` at every `nv`, in particular at `0`. -/
def natLevel : Nat → VLevel
  | 0 => .zero
  | n + 1 => .succ (natLevel n)

theorem natLevel_wf {nv : Nat} : ∀ n, (natLevel n).WF nv
  | 0 => trivial
  | n + 1 => natLevel_wf n

theorem natLevel_eval : ∀ (n : Nat) (ls : List Nat), (natLevel n).eval ls = n
  | 0, _ => rfl
  | n + 1, ls => by simp only [natLevel, VLevel.eval, natLevel_eval n ls]

/-- **The deficit is infinite, not a single pair.**  An infinite family of `WF 0` levels,
pairwise non-`≈`, all agreeing on the propositionhood bit at every assignment.  So
prop-agreement's conclusion cannot be repaired by ruling out finitely many level pairs, which is
what `SortInvIndep.propAgree_conclusion_not_sortUniq` leaves open. -/
theorem propAgree_deficit_infinite :
    ∃ f : Nat → VLevel, (∀ i, (f i).WF 0) ∧
      (∀ i j ls, ((f i).eval ls = 0 ↔ (f j).eval ls = 0)) ∧
      (∀ i j, i ≠ j → ¬ f i ≈ f j) := by
  refine ⟨fun i => natLevel (i + 1), fun i => natLevel_wf _, fun i j ls => ?_, fun i j hij h => ?_⟩
  · simp [natLevel_eval]
  · refine hij ?_
    have h' := (equiv_iff_eval_nil_up (natLevel_wf _) (natLevel_wf _)).1 h
    simp only [natLevel_eval] at h'
    omega

/-- **…and unbounded in the level.**  For every `k` there are two levels agreeing on the
propositionhood bit whose `≈`-classes differ by `k`.  The information prop-agreement fails to
carry is therefore not bounded by any constant. -/
theorem propAgree_deficit_unbounded (k : Nat) :
    ∃ u u' : VLevel, u.WF 0 ∧ u'.WF 0 ∧ (∀ ls, (u.eval ls = 0 ↔ u'.eval ls = 0)) ∧
      u.eval [] = 1 ∧ u'.eval [] = k + 2 ∧ ¬ u ≈ u' := by
  refine ⟨natLevel 1, natLevel (k + 2), natLevel_wf _, natLevel_wf _, ?_,
    natLevel_eval 1 [], natLevel_eval (k + 2) [], fun h => ?_⟩
  · simp [natLevel_eval]
  · have h' := (equiv_iff_eval_nil_up (natLevel_wf _) (natLevel_wf _)).1 h
    simp only [natLevel_eval] at h'
    omega

end VLevel

namespace VEnv

variable {env : VEnv}

/-! ## §1 Route B, upstream of `Injectivity` -/

/-- **Prop-agreement, restated at a position `Injectivity` can import.**

Character-for-character `SortInvIndep.PropAgreeOn`, which is character-for-character
`SetModel/NotProofNoModel.PropTypeAgreeOnCtx`'s guarded form.  Restated rather than imported for
the reason `SortInvIndep.lean` gives for its own copy — a `Theory/Typing` file may not import
`Theory/SetModel` — plus the reason this file exists: `SortInvIndep` is downstream of
`Injectivity`, so importing *it* would put this statement below the holes it is aimed at. -/
def PropAgreeUp (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {e A A' : VExpr} {u u' : VLevel} {ls : List Nat},
    OnCtx Γ (env.IsType U) → u.WF U → u'.WF U →
    env.HasType U Γ e A → env.HasType U Γ e A' →
    env.HasType U Γ A (.sort u) → env.HasType U Γ A' (.sort u') →
    (u.eval ls = 0 ↔ u'.eval ls = 0)

/-- **Route B at the upstream layer.**  Same statement as
`SetModel/PropAgreeWall.propTypeAgreeOnCtx_of_stratifiedN` (arity 4), same proof, same
hypotheses; the only difference is position, and position was the audit's entire hypothesis.

`nv = 0` is load-bearing: `equivZero_iff_eval_zero_up` needs `u.WF 0`, and the step is refuted at
`nv ≥ 2`.  The `N+1` index is `Stratified.sortDF` concluding one index up while `Stratified.conv`
wants both premises at the same index; `HasTypeN.mono` pays for that with no hypothesis. -/
theorem propAgreeUp_of_stratifiedN (henv : Ordered env)
    (pta : ∀ n, env.PropTypeAgreeN 0 n) (pun : ∀ n, env.PropUniqN 0 n) :
    PropAgreeUp env 0 := by
  intro Γ e A A' u u' ls hΓ hu hu' he he' hA hA'
  rw [← VLevel.equivZero_iff_eval_zero_up hu ls, ← VLevel.equivZero_iff_eval_zero_up hu' ls]
  obtain ⟨n₁, sHe⟩ := he.stratifyN henv hΓ
  obtain ⟨n₂, sHe'⟩ := he'.stratifyN henv hΓ
  obtain ⟨n₃, sHA⟩ := hA.stratifyN henv hΓ
  obtain ⟨n₄, sHA'⟩ := hA'.stratifyN henv hΓ
  have hrefl : (VLevel.zero : VLevel) ≈ (VLevel.zero : VLevel) := VLevel.equiv_def.2 fun _ => rfl
  have He : env.HasTypeN 0 (max (max n₁ n₂) (max n₃ n₄) + 1) Γ e A :=
    sHe.mono (Nat.le_succ_of_le (Nat.le_trans (Nat.le_max_left n₁ n₂) (Nat.le_max_left _ _)))
  have He' : env.HasTypeN 0 (max (max n₁ n₂) (max n₃ n₄) + 1) Γ e A' :=
    sHe'.mono (Nat.le_succ_of_le (Nat.le_trans (Nat.le_max_right n₁ n₂) (Nat.le_max_left _ _)))
  have HA : env.HasTypeN 0 (max (max n₁ n₂) (max n₃ n₄) + 1) Γ A (.sort u) :=
    sHA.mono (Nat.le_succ_of_le (Nat.le_trans (Nat.le_max_left n₃ n₄) (Nat.le_max_right _ _)))
  have HA' : env.HasTypeN 0 (max (max n₁ n₂) (max n₃ n₄) + 1) Γ A' (.sort u') :=
    sHA'.mono (Nat.le_succ_of_le (Nat.le_trans (Nat.le_max_right n₃ n₄) (Nat.le_max_right _ _)))
  constructor
  · intro hz
    have hpA : env.HasTypeN 0 (max (max n₁ n₂) (max n₃ n₄) + 1) Γ A (.sort .zero) :=
      .conv (.sortDF hu trivial hz) HA
    exact (pun _ (pta _ He He' hpA) HA').1 hrefl
  · intro hz
    have hpA' : env.HasTypeN 0 (max (max n₁ n₂) (max n₃ n₄) + 1) Γ A' (.sort .zero) :=
      .conv (.sortDF hu' trivial hz) HA'
    exact (pun _ (pta _ He' He hpA') HA).1 hrefl

/-! ### Anti-vacuity for §1's hypotheses, replayed upstream

Both hypotheses hold at the base index at every environment with no side condition
(`PropTypeAgreeN.zero`, `PropUniqN.zero`), so §1 is not a statement about an empty class.  This
does **not** discharge §1: `stratifyN` produces the index from the caller's derivation and it is
not `0`.  The `∀ n` form is `PropConv.lean`'s and `PropShadow.lean`'s open target. -/

theorem propTypeAgreeN_zero_up : env.PropTypeAgreeN 0 0 := PropTypeAgreeN.zero

theorem propUniqN_zero_up : env.PropUniqN 0 0 := PropUniqN.zero

/-! ## §2 applied to §1: what `Injectivity` would get, and why it is not enough

`PropAgreeUp`'s conclusion is a biconditional about `eval … = 0`.  By
`VLevel.propBit_iff_eval_nil_zero` that is agreement of a single bit; by
`VLevel.equiv_iff_eval_nil_up` the conclusion `Injectivity` needs (`SortUniq`, hence hole #5 via
`PiLevelPin.piInvStratApp_iff_sortUniq`) is equality of a natural number; and by
`VLevel.propAgree_deficit_infinite` / `propAgree_deficit_unbounded` the shortfall is infinite and
unbounded.  The statement below is that composition, in the form a consumer would meet it: even
with §1 available *and* both of its hypotheses discharged, the levels of a term's two sort-typings
are not pinned. -/

/-- **The round's negative result.**  For any environment at all, `PropAgreeUp env 0`'s
conclusion — the strongest thing route B can deliver, at the only index it works at — is
satisfied by level pairs that are arbitrarily far apart in `≈`.  So no instantiation of §1 at any
subject or context yields `SortUniq`, and lifting route B above `Injectivity` does not shrink
hole #5 or hole #8.

The `_env` binder is deliberate and is why it is named with an underscore: the witnesses **do not
depend on the environment**, which is exactly why no choice of environment repairs the route.  A
counterexample environment would be the *other* result (§3 limit 1) and this is not it. -/
theorem propAgreeUp_conclusion_underdetermines (_env : VEnv) (k : Nat) :
    ∃ u u' : VLevel, u.WF 0 ∧ u'.WF 0 ∧
      (∀ ls : List Nat, (u.eval ls = 0 ↔ u'.eval ls = 0)) ∧ ¬ u ≈ u' ∧
      u'.eval [] = u.eval [] + (k + 1) :=
  let ⟨u, u', hu, hu', hbit, h1, h2, hne⟩ := VLevel.propAgree_deficit_unbounded k
  ⟨u, u', hu, hu', hbit, hne, by rw [h1, h2]; omega⟩

section Audit
#print axioms Lean4Lean.VLevel.eval_indep_of_wf_zero_up
#print axioms Lean4Lean.VLevel.equivZero_iff_eval_zero_up
#print axioms Lean4Lean.VLevel.equiv_iff_eval_nil_up
#print axioms Lean4Lean.VLevel.propBit_of_both_nonzero
#print axioms Lean4Lean.VLevel.propBit_iff_eval_nil_zero
#print axioms Lean4Lean.VLevel.natLevel
#print axioms Lean4Lean.VLevel.natLevel_wf
#print axioms Lean4Lean.VLevel.natLevel_eval
#print axioms Lean4Lean.VLevel.propAgree_deficit_infinite
#print axioms Lean4Lean.VLevel.propAgree_deficit_unbounded
#print axioms Lean4Lean.VEnv.PropAgreeUp
#print axioms Lean4Lean.VEnv.propAgreeUp_of_stratifiedN
#print axioms Lean4Lean.VEnv.propTypeAgreeN_zero_up
#print axioms Lean4Lean.VEnv.propUniqN_zero_up
#print axioms Lean4Lean.VEnv.propAgreeUp_conclusion_underdetermines
end Audit

end VEnv
end Lean4Lean
