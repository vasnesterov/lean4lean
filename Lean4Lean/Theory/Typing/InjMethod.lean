import Lean4Lean.Theory.Typing.UniqueTypingN
import Lean4Lean.Theory.Typing.PatternRules

/-!
# Clause (3) of definitional inversion needs `VEnv.WF`, and **one** rule is enough to break it

`Theory/Typing/UniqueTypingN.lean` and `Theory/Typing/DefInvRefute.lean` both record clauses (1)
and (3) of `VEnv.DefInv` — `SortInvN` and `SortForallEDisjN` — as **open, "neither proved nor
refuted"**, and they are the two clauses the surviving reductions to
`Theory/Typing/Injectivity.lean`'s open statements consume
(`IsDefEqU.sort_inv_of_sortInvN`, `IsDefEqU.sort_forallE_inv_of_sortForallEDisjN`).

`SortForallEDisjN` **is** `RigidSortPiDisj`, conjunct 3 of the 5 that
`RigidNodeCircle.rigidShapeUniqNS_iff_family` splits `Injectivity.WF.rigidShapeUniqNS` into, and
it is the one conjunct of the five for which `InjSortPiModel.lean` supplies a usable semantic
fact. So it is the live seam of that hole.

This file settles the *environment* axis for it, which no refutation in the tree had run: every
refutation in `DefInvRefute.lean` is over the **empty** environment, where clause (3) survives.

## What is proved

**`SortForallEDisjN` is not provable from `Ordered env` at any index `n ≥ 1`.**
`injEnv` carries a single definitional equation

    Prop  ≡  ∀ (_ : Prop), Prop        at   Sort 1

with **no constant anywhere in it**: `rogueDf.lhs` is `.sort .zero` on the nose. `Ordered.defeq`
asks only `df.WF env` — both sides typed at `df.type` in the empty context — and both sides are,
so `ordered_injEnv` holds. `Stratified.extra` then turns the rule into a `⊢₁` conversion between
a sort and a Π (`rogue_link`), which is exactly what clause (3) forbids.

## Why this is sharper than `Theory/Typing/InjPiRogue.lean`

That file's `roguePiEnv` needs **two** δ-rules on **one constant**, so the clause of `VEnv.WF` it
pins is `DefEqHeadsUnique` — *rule-count uniqueness* (`Theory/Typing/DeltaUnique.lean`). Its
summary is therefore that "a `VEnv.WF` environment cannot carry **two** δ-rules for one
constant", and that is one clause too weak. `injEnv` carries **one** rule and no constant, so the
clause it pins is `VEnv.RuleShape.delta` — *a δ-rule's left-hand side is `.const ci.name _`* —
which is logically prior to rule-count uniqueness and is what `not_wf_injEnv` uses.

**One rule is enough to break clause (3), if its head is not a constant.**

## What is NOT claimed

* **No hole is closed and no census number moves.** This is a negative result about a hypothesis,
  not a discharge. `Injectivity.WF.rigidShapeUniqNS` and `IsDefEqU.forallE_inv_stratified` both
  still carry their `sorry`.
* **The real holes are NOT refuted.** They take `VEnv.WF env`, and `not_wf_injEnv` shows `injEnv`
  is not `VEnv.WF`. The refutation stops exactly at that line, as it must.
* **Nothing here says clause (3) is false over a `VEnv.WF` environment.** It says any proof of it
  must consume `VEnv.RuleShape`, and that `Ordered` — the strength every reduction in
  `InjMidLocal.lean`, `InjChainLower.lean`, `InjPiInhab.lean` and `SortDisjPiLvl.lean` carries —
  cannot suffice.
-/

namespace Lean4Lean
namespace VEnv
namespace InjMethod

open VExpr

/-- `Prop`, i.e. `Sort 0`. -/
def vProp : VExpr := .sort .zero

/-- `∀ (_ : Prop), Prop`. -/
def vPiProp : VExpr := .forallE (.sort .zero) (.sort .zero)

/-- **The one rogue rule**, and the whole point of it is that `lhs` is *not* `const`-headed. -/
def rogueDf : VDefEq := ⟨0, vProp, vPiProp, .sort (.succ .zero)⟩

/-- The witness environment: `∅` plus `rogueDf`, and nothing else. No constants at all. -/
def injEnv : VEnv := (∅ : VEnv).addDefEq rogueDf

theorem injEnv_defeqs : injEnv.defeqs rogueDf := Or.inl rfl

/-! ## The environment is `Ordered` -/

theorem lhs_type : (∅ : VEnv).HasType 0 [] vProp (.sort (.succ .zero)) :=
  HasType.sort trivial

theorem imax_equiv : (VLevel.imax (.succ .zero) (.succ .zero)) ≈ (VLevel.succ .zero) := by
  funext ls; simp [VLevel.eval]; decide

theorem rhs_type : (∅ : VEnv).HasType 0 [] vPiProp (.sort (.succ .zero)) :=
  IsDefEq.defeq (IsDefEq.sortDF (l := .imax (.succ .zero) (.succ .zero)) (l' := .succ .zero)
      ⟨trivial, trivial⟩ trivial imax_equiv)
    (HasType.forallE (u := .succ .zero) (v := .succ .zero)
      (HasType.sort trivial) (HasType.sort trivial))

theorem rogueDf_wf : rogueDf.WF (∅ : VEnv) := ⟨lhs_type, rhs_type⟩

theorem ordered_injEnv : Ordered injEnv := .defeq .empty rogueDf_wf

/-! ## The rule is a `⊢₁` conversion between a sort and a Π -/

/-- **The link.**  `Stratified.extra` at `n = 0` produces a `⊢₁` conversion, which is the
smallest index at which any non-`rfl` conversion exists (`IsDefEqN.zero_iff`). -/
theorem rogue_link {Γ : List VExpr} : injEnv.IsDefEqN 0 1 Γ vProp vPiProp := by
  have h := Stratified.extra (env := injEnv) (U := 0) (n := 0) (Γ := Γ)
    (ls := []) (df := rogueDf) injEnv_defeqs (by simp) rfl
  simpa [rogueDf, vProp, vPiProp, VExpr.instL, VLevel.inst] using h

/-- The link at every index `≥ 1`, by monotonicity. -/
theorem rogue_link_mono {Γ : List VExpr} {n : Nat} (hn : 1 ≤ n) :
    injEnv.IsDefEqN 0 n Γ vProp vPiProp := IsDefEqN.mono hn rogue_link

/-! ## Clause (3) is false at `injEnv`, at every index `≥ 1` -/

/-- **The result.**  `SortForallEDisjN` — `unique.tex:34`, clause (3) of definitional inversion,
and `RigidSortPiDisj` — is **false** at an `Ordered` environment carrying one non-`const`-headed
rule, at every index at which it is not vacuous. -/
theorem not_sortForallEDisjN {n : Nat} (hn : 1 ≤ n) : ¬ injEnv.SortForallEDisjN 0 n :=
  fun h => h (Γ := []) (rogue_link_mono (Γ := []) hn)

/-- The `n = 1` instance, i.e. the smallest index at which clause (3) has any content. -/
theorem not_sortForallEDisjN_one : ¬ injEnv.SortForallEDisjN 0 1 :=
  not_sortForallEDisjN (Nat.le_refl 1)

/-- **`Ordered` does not prove clause (3).**  The headline: no theorem of the form
`Ordered env → env.SortForallEDisjN U n` exists for `n ≥ 1`. -/
theorem not_sortForallEDisjN_of_ordered :
    ¬ ∀ (env : VEnv) (U n : Nat), Ordered env → 1 ≤ n → env.SortForallEDisjN U n :=
  fun h => not_sortForallEDisjN_one (h injEnv 0 1 ordered_injEnv (Nat.le_refl 1))

/-- And `DefInv` itself, at every index `≥ 1`, since clause (3) is one of its three fields. -/
theorem not_defInv {n : Nat} (hn : 1 ≤ n) : ¬ injEnv.DefInv 0 n :=
  fun d => not_sortForallEDisjN hn d.sort_forallE

/-! ## …and the witness is **not** `VEnv.WF`, which is where the refutation must stop

`injEnv` has no constants at all, and `rogueDf.lhs` is `.sort .zero`, so no clause of
`VEnv.RuleShape` can hold of it: `delta` needs a `.const`-headed lhs, and `quot`/`iota` need
declared constants. `VEnv.WF.ruleShape` therefore refutes `VEnv.WF injEnv`. -/

theorem injEnv_constants (c : Lean.Name) : injEnv.constants c = none := rfl

/-- **No rule of a constant-free environment has a sort as its left-hand side.**  Stated over a
free `df` so that `cases` does not have to unify a projection with a literal. -/
theorem ruleShape_lhs_ne_sort {env : VEnv} (hc : ∀ c, env.constants c = none)
    {df : VDefEq} {l : VLevel} (h : env.RuleShape df) : df.lhs ≠ .sort l := by
  cases h <;> simp_all [VDefVal.toDefEq]

/-- **`injEnv` is not `VEnv.WF`.**  So `Injectivity.WF.rigidShapeUniqNS` and
`IsDefEqU.forallE_inv_stratified`, which both take `VEnv.WF env`, are **not** refuted by anything
in this file — and, by `DeltaUnique.WF.defEqHeadsUnique` and `WF.ruleShape`, cannot be. -/
theorem not_wf_injEnv : ¬ VEnv.WF injEnv := fun h =>
  ruleShape_lhs_ne_sort injEnv_constants (l := .zero) (h.ruleShape injEnv_defeqs) rfl

end InjMethod
end VEnv
end Lean4Lean
