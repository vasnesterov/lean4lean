import Lean4Lean.Theory.Typing.AppCase
import Lean4Lean.Theory.Typing.SortClauses
import Lean4Lean.Theory.Typing.PropAgreeGuarded

/-!
# `∀ n, AppUniqLvl` is FALSE at an `Ordered` environment

`docs/handoff-sortinv-route.md` §9.2 identifies `∀ n, AppUniqLvl` (= `∀ n, PropUniqN.AppCase`
= `∀ n, PropUniqN`) as the single remaining syntactic obligation of the hole-free route to
`PropAgreeOn`.  §11 item 1 says to attack it.

**It cannot be proved from `Ordered env`.**  This file gives a machine-checked counterexample.
-/
namespace Lean4Lean
namespace VEnv

/-! ## The environment -/

/-- A `VDefEq` identifying `Type 0 → Prop` with `Type 0 → Type 0`.  **Both sides are typed at
`.sort 2`**, because `.imax 2 1` and `.imax 2 2` are both `≈ 2` — the domain's universe
swallows the codomain's.  So the rule satisfies `VDefEq.WF ∅` while relating two Π-types whose
codomains disagree on propositionhood. -/
def piLvlRule : VDefEq :=
  ⟨0, .forallE (.sort (.succ .zero)) (.sort .zero),
      .forallE (.sort (.succ .zero)) (.sort (.succ .zero)),
      .sort (.succ (.succ .zero))⟩

def piLvlEnv : VEnv := VEnv.empty.addDefEq piLvlRule

theorem piLvlRule_wf : piLvlRule.WF ∅ := by
  constructor
  · have h : (∅ : VEnv).HasType 0 [] (.forallE (.sort (.succ .zero)) (.sort .zero))
        (.sort (.imax (.succ (.succ .zero)) (.succ .zero))) :=
      VEnv.IsDefEq.forallEDF (.sortDF trivial trivial rfl) (.sortDF trivial trivial rfl)
    exact .defeqDF (.sortDF (l := .imax (.succ (.succ .zero)) (.succ .zero))
      (l' := .succ (.succ .zero)) ⟨trivial, trivial⟩ trivial
      (by simp [VLevel.equiv_def, VLevel.eval, Lean.Nat.imax])) h
  · have h : (∅ : VEnv).HasType 0 []
        (.forallE (.sort (.succ .zero)) (.sort (.succ .zero)))
        (.sort (.imax (.succ (.succ .zero)) (.succ (.succ .zero)))) :=
      VEnv.IsDefEq.forallEDF (.sortDF trivial trivial rfl) (.sortDF trivial trivial rfl)
    exact .defeqDF (.sortDF (l := .imax (.succ (.succ .zero)) (.succ (.succ .zero)))
      (l' := .succ (.succ .zero)) ⟨trivial, trivial⟩ trivial
      (by simp [VLevel.equiv_def, VLevel.eval, Lean.Nat.imax])) h

theorem piLvlEnv_ordered : Ordered piLvlEnv := .defeq .empty piLvlRule_wf

theorem piLvlEnv_defeqs : piLvlEnv.defeqs piLvlRule := Or.inl rfl

/-- **`piLvlEnv` is not `VEnv.WF`.**  Every rule of a well-formed environment is a declaration
rule, and no declaration rule rewrites a Π-type (`IsDeclRule.lhs_ne_forallE`).  So this witness
says nothing about `VEnv.WF` environments — see §"What this does not refute". -/
theorem piLvlEnv_not_wf : ¬ piLvlEnv.WF :=
  fun h => (h.defeq_isDeclRule piLvlEnv_defeqs).lhs_ne_forallE _ _ rfl

/-! ## The witness -/

/-- The rule's left-hand side, `Type 0 → Prop`. -/
def piLvlL : VExpr := .forallE (.sort (.succ .zero)) (.sort .zero)

/-- The rule's right-hand side, `Type 0 → Type 0`. -/
def piLvlR : VExpr := .forallE (.sort (.succ .zero)) (.sort (.succ .zero))

/-- The rule, as an index-1 conversion.  `extra`'s only premises are membership and level
well-formedness, so this costs nothing. -/
theorem piLvlEnv_conv : piLvlEnv.IsDefEqN 0 1 [piLvlL] piLvlL piLvlR :=
  Stratified.extra (ls := []) piLvlEnv_defeqs nofun rfl

/-- The function: a variable of the left-hand type. -/
theorem piLvl_fn₀ : piLvlEnv.HasTypeN 0 1 [piLvlL] (.bvar 0) piLvlL :=
  Stratified.bvar (Γ := [piLvlL]) Lookup.zero

/-- …and the *same* variable at the right-hand type, by `conv` along the rule. -/
theorem piLvl_fn₁ : piLvlEnv.HasTypeN 0 1 [piLvlL] (.bvar 0) piLvlR :=
  .conv piLvlEnv_conv piLvl_fn₀

/-- The argument, `Prop`, typed at the common domain `Type 0`. -/
theorem piLvl_arg {Γ : List VExpr} :
    piLvlEnv.HasTypeN 0 1 Γ (.sort .zero) (.sort (.succ .zero)) :=
  Stratified.sort trivial

/-- **The premise bundle of the `app` case**, at the witness: one function with two Π-types and
one argument typed at both domains — `AppCase.lean`'s `AppData`, verbatim. -/
theorem piLvl_appData :
    AppData piLvlEnv 0 1 [piLvlL] (.bvar 0) (.sort .zero)
      (.sort (.succ .zero)) (.sort .zero)
      (.sort (.succ .zero)) (.sort (.succ .zero)) :=
  ⟨piLvl_fn₀, piLvl_arg, piLvl_fn₁, piLvl_arg⟩

/-! ## The refutations -/

/-- **`AppUniqLvl` is false at `piLvlEnv`, at `n = 1`.**  The two instantiated codomains are
*literally* `Prop` and `Type 0`; no conversion is needed on either side, so neither premise of
`AppUniqLvl` is met by accident.

This is the difference from `AppCaseRefute.witness` (`Theory/Typing/AppCase.lean` §4), whose
two types are a sort and a **stuck** term: that witness refutes `AppTypeUniq` and `UniqN` but
`witness_shapes` shows it is not a (sort, sort) pair, so it leaves `AppUniqLvl` alone. -/
theorem piLvlEnv_appUniqLvl_false : ¬ piLvlEnv.AppUniqLvl 0 1 := fun h =>
  absurd (congrFun ((h piLvl_appData .rfl .rfl).1 rfl) []) (by simp [VLevel.eval])

/-- …and the `∀ n` form with it, which is what §9.2's assembly asks for. -/
theorem piLvlEnv_appUniqLvl_all_false : ¬ ∀ n, piLvlEnv.AppUniqLvl 0 n :=
  fun h => piLvlEnv_appUniqLvl_false (h 1)

/-- **The tree's own statement of the case is false too**, via `AppUniqLvl.iff`. -/
theorem piLvlEnv_appCase_false : ¬ PropUniqN.AppCase piLvlEnv 0 1 :=
  fun h => piLvlEnv_appUniqLvl_false (AppUniqLvl.of_appCase h)

theorem piLvlEnv_appCase_all_false : ¬ ∀ n, PropUniqN.AppCase piLvlEnv 0 n :=
  fun h => piLvlEnv_appCase_false (h 1)

/-! ### …and the statement itself, spelled out without the `app`-case packaging

`.app (.bvar 0) Prop` has **two sort types** at index 1: `Prop` and `Type 0`. -/

theorem piLvl_witness₀ :
    piLvlEnv.HasTypeN 0 1 [piLvlL] (.app (.bvar 0) (.sort .zero)) (.sort .zero) :=
  Stratified.app piLvl_fn₀ piLvl_arg

theorem piLvl_witness₁ :
    piLvlEnv.HasTypeN 0 1 [piLvlL] (.app (.bvar 0) (.sort .zero))
      (.sort (.succ .zero)) :=
  Stratified.app piLvl_fn₁ piLvl_arg

/-- **`PropUniqN` is false at `piLvlEnv`, at `n = 1`** — one term, two sort types, one a
proposition and one not. -/
theorem piLvlEnv_propUniqN_false : ¬ piLvlEnv.PropUniqN 0 1 := fun h =>
  absurd (congrFun ((h piLvl_witness₀ piLvl_witness₁).1 rfl) []) (by simp [VLevel.eval])

theorem piLvlEnv_propUniqN_all_false : ¬ ∀ n, piLvlEnv.PropUniqN 0 n :=
  fun h => piLvlEnv_propUniqN_false (h 1)

/-- The witness in `∃` form, for quoting. -/
theorem piLvl_witness :
    ∃ (env : VEnv) (Γ : List VExpr) (A : VExpr) (u v : VLevel),
      Ordered env ∧ env.HasTypeN 0 1 Γ A (.sort u) ∧ env.HasTypeN 0 1 Γ A (.sort v) ∧
      u ≈ (.zero : VLevel) ∧ ¬ v ≈ (.zero : VLevel) :=
  ⟨piLvlEnv, [piLvlL], .app (.bvar 0) (.sort .zero), .zero, .succ .zero,
    piLvlEnv_ordered, piLvl_witness₀, piLvl_witness₁, rfl,
    fun h => absurd (congrFun h []) (by simp [VLevel.eval])⟩

/-! ## The guard does not help

`docs/handoff-sortinv-route.md` §9.3 weakens route B's hypotheses to the `OnCtx`-guarded
`PropUniqNOn` / `PropTypeAgreeNOn`, and §11 item 3 proposes pushing that guard into
`SetModel/PropAgreeWall.lean`.  **The witness context is guarded**, so the refutation survives
the weakening: the rule's left-hand side is a genuine type — it is typed at `.sort 2`, which is
`piLvlRule_wf`'s first component. -/

theorem piLvlL_isType : piLvlEnv.IsType 0 [] piLvlL :=
  ⟨_, piLvlRule_wf.1.mono VEnv.addDefEq_le⟩

theorem piLvlL_onCtx : OnCtx [piLvlL] (piLvlEnv.IsType 0) := ⟨trivial, piLvlL_isType⟩

/-- The same at the index: `piLvlL` is a type at index `k+1` too (the `sortDF` that collapses
`.imax 2 1` to `2` lives at `k+1`). -/
theorem piLvlL_isTypeN {k : Nat} {Γ : List VExpr} : piLvlEnv.IsTypeN 0 (k+1) Γ piLvlL :=
  ⟨.succ (.succ .zero), trivial,
    .conv (.sortDF (l := .imax (.succ (.succ .zero)) (.succ .zero)) ⟨trivial, trivial⟩ trivial
        (by simp [VLevel.equiv_def, VLevel.eval, Lean.Nat.imax]))
      (Stratified.forallE trivial trivial (Stratified.sort trivial) (Stratified.sort trivial))⟩

theorem piLvlL_onCtxN {k : Nat} : piLvlEnv.OnCtxN 0 (k+1) [piLvlL] :=
  ⟨trivial, piLvlL_isTypeN⟩

/-- **The `OnCtx`-guarded form of the target is false as well.** -/
theorem piLvlEnv_propUniqNOn_false : ¬ PropUniqNOn piLvlEnv 0 1 := fun h =>
  absurd (congrFun ((h piLvlL_onCtx piLvl_witness₀ piLvl_witness₁).1 rfl) [])
    (by simp [VLevel.eval])

theorem piLvlEnv_propUniqNOn_all_false : ¬ ∀ n, PropUniqNOn piLvlEnv 0 n :=
  fun h => piLvlEnv_propUniqNOn_false (h 1)

/-! ## What this closes

`PropAgreeGuarded.propAgreeOn_of_stratifiedN` and `propAgreeOn_of_stratifiedNOn` take
`Ordered env` and the two `∀ n` families.  `piLvlEnv` satisfies the first and refutes the
second, in both the plain and the guarded formulation.  So **route B's hypotheses are not
derivable from `Ordered env`**, guard or no guard, and §11 item 3's proposed edit to
`SetModel/PropAgreeWall.lean` does not change that. -/

theorem ordered_not_enough_for_propUniqN :
    ¬ ∀ (env : VEnv), Ordered env → ∀ n, env.PropUniqN 0 n :=
  fun h => piLvlEnv_propUniqN_false (h _ piLvlEnv_ordered 1)

theorem ordered_not_enough_for_appUniqLvl :
    ¬ ∀ (env : VEnv), Ordered env → ∀ n, env.AppUniqLvl 0 n :=
  fun h => piLvlEnv_appUniqLvl_false (h _ piLvlEnv_ordered 1)

theorem ordered_not_enough_for_propUniqNOn :
    ¬ ∀ (env : VEnv), Ordered env → ∀ n, PropUniqNOn env 0 n :=
  fun h => piLvlEnv_propUniqNOn_false (h _ piLvlEnv_ordered 1)

/-! ## The instance route B actually consumes — refuted too

`PropAgreeGuarded.propAgreeOn_of_stratifiedNOn` applies `pun` exactly twice, and in both places
one of the two universes is **literally `.zero`** (`(pun _ hΓ (pta …) HA').1 hrefl`).  So route B
consumes only the `u = .zero` instance of `PropUniqN`.  Both halves are recorded here: the
instance is *not* a weakening, and the refutation covers it anyway. -/

/-- The `u = .zero` instance: *propositionhood of a type is unambiguous.* -/
def PropUniqZeroN (env : VEnv) (U n : Nat) : Prop :=
  ∀ {Γ : List VExpr} {A : VExpr} {v : VLevel},
    env.HasTypeN U n Γ A (.sort .zero) → env.HasTypeN U n Γ A (.sort v) →
    v ≈ (.zero : VLevel)

theorem PropUniqN.propUniqZeroN (h : env.PropUniqN U n) : PropUniqZeroN env U n :=
  fun h₀ hv => (h h₀ hv).1 (VLevel.equiv_def.2 fun _ => rfl)

/-- **…and it is NOT weaker — graded as the collapse it is.**  At any index `k+1`, `sortDF`
turns `A : .sort u` with `u ≈ 0` into `A : .sort .zero`, so the zero instance recovers the whole
statement.  The one thing it needs that `PropUniqN` does not state is `u.WF U`, which every
consumer supplies (`SortInvIndep.PropAgreeOn` carries it as `hu`).  So naming this instance
records *where* route B's demand sits; it does **not** reduce it. -/
theorem PropUniqZeroN.propUniqN {k : Nat} (hwf : ∀ {Γ : List VExpr} {A : VExpr} {u : VLevel},
      env.HasTypeN U (k+1) Γ A (.sort u) → u.WF U)
    (h : PropUniqZeroN env U (k+1)) : env.PropUniqN U (k+1) := by
  intro Γ A u v hu hv
  constructor
  · intro hz
    exact h (.conv (.sortDF (hwf hu) trivial hz) hu) hv
  · intro hz
    exact h (.conv (.sortDF (hwf hv) trivial hz) hv) hu

/-- **The instance route B consumes is false at `piLvlEnv`.** -/
theorem piLvlEnv_propUniqZeroN_false : ¬ PropUniqZeroN piLvlEnv 0 1 := fun h =>
  absurd (congrFun (h piLvl_witness₀ piLvl_witness₁) []) (by simp [VLevel.eval])

theorem piLvlEnv_propUniqZeroN_all_false : ¬ ∀ n, PropUniqZeroN piLvlEnv 0 n :=
  fun h => piLvlEnv_propUniqZeroN_false (h 1)

/-! ## What this does **not** refute — stated because a refutation that hit the wrong target
would be worthless

1. **Not `VEnv.WF`.**  `piLvlEnv_not_wf`.  A well-formed environment's rules are declaration
   rules, and `IsDeclRule.lhs_ne_forallE` says none of them rewrites a Π-type.  So this witness
   leaves `∀ n, AppUniqLvl preludeEnv 0 n` completely open, and says only — but exactly — that
   a proof of it must consume the rule-shape restriction, i.e. `WF.defeq_isDeclRule` /
   `IsDeclRule.lhs_shape`, and cannot run on `Ordered env`.

2. **Not `PropTypeAgreeN`, and not by any rule of this shape.**  The witness's two types are
   `Prop` and `Type 0`; neither is a *proposition*, so `PropTypeAgreeN`'s hypothesis `IsPropN A`
   is never met at it.  More than that: the `imax` slack that makes this construction work is
   provably unavailable for `PropTypeAgreeN`.  A Π–Π rule at a common type `.sort t` forces
   `.imax c d₀ ≈ .imax c d₁` on the two codomain universes, and that already implies the two
   codomains agree on propositionhood — so no rule of this shape can separate a proposition
   from a non-proposition. -/
theorem imax_congr_agree_zero {c d₀ d₁ : VLevel} (h : VLevel.imax c d₀ ≈ VLevel.imax c d₁) :
    (d₀ ≈ (.zero : VLevel) ↔ d₁ ≈ (.zero : VLevel)) := by
  constructor
  · intro h₀
    exact VLevel.imax_eq_zero.1 (h.symm.trans (VLevel.imax_eq_zero.2 h₀))
  · intro h₁
    exact VLevel.imax_eq_zero.1 (h.trans (VLevel.imax_eq_zero.2 h₁))

/-- 3. **Not the two `∀ n` targets' *assembly*, which was already void for a different
reason.**  `PropAgreeGuarded.propTypeAgreeN_and_propUniqN_of` and
`propTypeAgreeN_and_propUniqN_iff` take `∀ n, RegPi`, and `RegPiSat.regPi_false` refutes
`RegPi` at **every** environment, every `U` and every `n`.  So those two are not "conditional on
`RegPi` being satisfiable" (as `docs/handoff-sortinv-route.md` §9.2 has it) — they are
**vacuous**, unconditionally.  `propUniqN_iff_appCase_all` is the one that survives, and it
survives here too: both of its sides are false at `piLvlEnv`. -/
theorem regPi_all_false {env : VEnv} {U : Nat} : ¬ ∀ n, env.RegPi U n :=
  fun h => regPi_false (h 0)

/-! ## Not established, and it is the first thing to check next

Whether `piLvlEnv` satisfies `SortDisjInvN` at index 1 — clause (1) `SortInvN` and clause (3)
`SortForallEDisjN`.  Neither is refuted by the rule (it relates two Π-types, so it respects both
shapes; contrast `SortClauses.sortPiEnv`, whose rule relates a sort to a Π and refutes clause
(3) outright).  If they do hold, the refutation strengthens to *`∀ n, AppUniqLvl` is not implied
by `Ordered env ∧ ∀ n, SortDisjInvN`*, i.e. the side conditions of §9.2's assembly do not rescue
it.  Proving them needs a `SubstCRefute.stuck`-style induction over index-1 conversions, whose
`beta` case is the general weak-head-confluence problem; **no claim is made either way here.** -/

section Audit
#print axioms Lean4Lean.VEnv.piLvlRule_wf
#print axioms Lean4Lean.VEnv.piLvlEnv_ordered
#print axioms Lean4Lean.VEnv.piLvlEnv_defeqs
#print axioms Lean4Lean.VEnv.piLvlEnv_not_wf
#print axioms Lean4Lean.VEnv.piLvlEnv_conv
#print axioms Lean4Lean.VEnv.piLvl_fn₀
#print axioms Lean4Lean.VEnv.piLvl_fn₁
#print axioms Lean4Lean.VEnv.piLvl_arg
#print axioms Lean4Lean.VEnv.piLvl_appData
#print axioms Lean4Lean.VEnv.piLvlEnv_appUniqLvl_false
#print axioms Lean4Lean.VEnv.piLvlEnv_appUniqLvl_all_false
#print axioms Lean4Lean.VEnv.piLvlEnv_appCase_false
#print axioms Lean4Lean.VEnv.piLvlEnv_appCase_all_false
#print axioms Lean4Lean.VEnv.piLvl_witness₀
#print axioms Lean4Lean.VEnv.piLvl_witness₁
#print axioms Lean4Lean.VEnv.piLvlEnv_propUniqN_false
#print axioms Lean4Lean.VEnv.piLvlEnv_propUniqN_all_false
#print axioms Lean4Lean.VEnv.piLvl_witness
#print axioms Lean4Lean.VEnv.piLvlL_isType
#print axioms Lean4Lean.VEnv.piLvlL_onCtx
#print axioms Lean4Lean.VEnv.piLvlL_isTypeN
#print axioms Lean4Lean.VEnv.piLvlL_onCtxN
#print axioms Lean4Lean.VEnv.piLvlEnv_propUniqNOn_false
#print axioms Lean4Lean.VEnv.piLvlEnv_propUniqNOn_all_false
#print axioms Lean4Lean.VEnv.ordered_not_enough_for_propUniqN
#print axioms Lean4Lean.VEnv.ordered_not_enough_for_appUniqLvl
#print axioms Lean4Lean.VEnv.ordered_not_enough_for_propUniqNOn
#print axioms Lean4Lean.VEnv.imax_congr_agree_zero
#print axioms Lean4Lean.VEnv.regPi_all_false
#print axioms Lean4Lean.VEnv.PropUniqN.propUniqZeroN
#print axioms Lean4Lean.VEnv.PropUniqZeroN.propUniqN
#print axioms Lean4Lean.VEnv.piLvlEnv_propUniqZeroN_false
#print axioms Lean4Lean.VEnv.piLvlEnv_propUniqZeroN_all_false
end Audit

end VEnv
end Lean4Lean
