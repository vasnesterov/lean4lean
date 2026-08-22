import Lean4Lean.Theory.SetModel.Cnst

/-!
# The interpretation of `Quot`

`Quot` is the only primitive of the prelude whose type mentions no other
constant (see `SetModel/PreludeSpec.lean`), so it is the only one that can be
interpreted before the inductive interpretation exists.

## The level split, and why it is not an artefact

`setQuotient_mem_U` is stated at `U κ (i+1)`, never at `U κ 0`, and **that
restriction is real**: the set-theoretic quotient of a proposition is not a
proposition.  A member of `U κ 0 = UProp = ℘{•}` is a subset of `{•}`; its
quotient by any relation is a set of equivalence *classes*, and the one class of
`{•}` is `{•}` itself, so the quotient is `{{•}}`, which is not a subset of
`{•}`.

Lean agrees, for its own reasons: `Quot r : Sort u` for `α : Sort u`, so at
`u = 0` the quotient is a `Prop`, and every inhabited `Prop` is `True`.  So the
interpretation must split on the level and give the proof-irrelevant answer in
the `Prop` case — `{•}` when the domain is inhabited, `∅` otherwise.

This is the **third** place in the model where a statement that reads uniformly
has needed a level-sensitive case split.  The other two were `forallE`'s
codomain (impredicative `mkForallProp` versus `mkForallType`, split on whether
the codomain is a `Prop`) and `Coherent`'s level bound (`U κ i` is only a real
universe below the chain length).  The pattern is worth naming: **a construction
that is uniform in ZFC is rarely uniform across `Sort 0` versus `Sort (u+1)`,
because `Prop` is proof-irrelevant and impredicative while the higher universes
are neither.**  Expect a fourth.
-/

namespace Lean4Lean.SetModel

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open scoped Classical

variable {V : Type*} [SetStructure V] [Nonempty V]

section
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The relation a `Quot` argument denotes, as a set of pairs.

`r` denotes a *curried internal function* `α → α → Prop`, so `(r ‘ x) ‘ y` is a
truth value and the relation it names is the set of pairs at which that value is
`{•}`.  Membership of `•` is the same test, and is the one that stays inside the
`ℒₛₑₜ`-definable fragment. -/
noncomputable def quotRel (α r : V) : V :=
  {p ∈ (α ×ˢ α : V) ; ∃ x ∈ α, ∃ y ∈ α, p = (⟨x, y⟩ₖ : V) ∧ (pt : V) ∈ (r ‘ x) ‘ y}

/-- **The denotation of `Quot α r` at universe index `i`.**

At `i = 0` the answer is proof-irrelevant: `Quot r` is a `Prop`, inhabited
exactly when `α` is.  Above that it is the honest set-theoretic quotient by the
*equivalence closure* of `r` — `Quot` does not require its relation to be an
equivalence, and `eqvClosure` is what `SetModel/Universe.lean` supplies for
exactly this reason. -/
noncomputable def quotVal (α r : V) : ℕ → V
  | 0 => if α = ∅ then (∅ : V) else ({pt} : V)
  | _ + 1 => setQuotient α (eqvClosure α (quotRel α r))

end

section
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {n : ℕ} {κ : ℕ → V} (hκ : IsInaccessibleChain n κ)

include hκ in
/-- **`Quot` stays in its universe.**  Both branches, and the `Prop` branch
needs nothing from the chain — which is the point of splitting. -/
theorem quotVal_mem_U {i : ℕ} (hi : i < n) {α r : V} (hα : α ∈ U κ i) :
    quotVal α r i ∈ U κ i := by
  match i with
  | 0 =>
    rw [quotVal, U_zero]
    split
    · exact mem_UProp_iff.2 (by simp)
    · exact true_mem_UProp
  | j + 1 =>
    rw [quotVal]
    exact setQuotient_mem_U hκ (Nat.lt_of_succ_lt hi) hα

end

end Lean4Lean.SetModel
