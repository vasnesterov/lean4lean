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

/-! ### Definability

Everything the model puts inside a `mkLam` has to be `ℒₛₑₜ`-definable **jointly
in all its arguments**, because the fibre map varies with the domain element.
That is a stronger demand than anything `SetModel/Universe.lean` needed:
`eqvStep_definable` is stated in the operator's last argument only, with the
carrier and relation fixed.

Plain `definability` does not reach any of these.  Two documented workarounds are
both needed, in combination:

* the `mem_ext_iff` route — restate `T = f a b` as a first-order membership
  formula and call `definability` on that (this is how `eqvStep_definable`
  itself is proved);
* passing `sep`'s definability argument explicitly rather than through its
  `autoParam`, since the `autoParam` runs `definability` without the local
  hypotheses that make it succeed.

Without the second, the `sep` inside `quotEqv` fails with
`aesop: internal error during proof reconstruction: goal N was not normalised`
— the same failure recorded as Foundation gap #1. -/

/-- The relation a `Quot` argument denotes, as a set of pairs.

`r` denotes a *curried internal function* `α → α → Prop`, so `(r ‘ x) ‘ y` is a
truth value and the relation it names is the set of pairs at which that value is
inhabited. -/
noncomputable def quotRel (α r : V) : V :=
  {p ∈ (α ×ˢ α : V) ; ∃ x ∈ α, ∃ y ∈ α, p = (⟨x, y⟩ₖ : V) ∧ (pt : V) ∈ (r ‘ x) ‘ y}

theorem quotRel_definable : ℒₛₑₜ-function₂[V] (fun α r ↦ quotRel α r) := by
  suffices ℒₛₑₜ-relation₃[V] (fun T α r ↦ T = quotRel α r) by exact this
  have e : ∀ T α r : V, T = quotRel α r ↔ ∀ p, p ∈ T ↔ p ∈ α ×ˢ α ∧
      (∃ x ∈ α, ∃ y ∈ α, p = (⟨x, y⟩ₖ : V) ∧ (pt : V) ∈ (r ‘ x) ‘ y) := by
    intro T α r; rw [mem_ext_iff]; simp [quotRel]
  simp only [e]
  definability

/-- One step of the equivalence-closure operator, definable **jointly** in the
carrier, the relation and the stage.  `Universe.lean`'s `eqvStep_definable`
fixes the first two. -/
theorem eqvStep_definable₃ : ℒₛₑₜ-function₃[V] (fun A R S ↦ eqvStep A R S) := by
  suffices ℒₛₑₜ-relation₄[V] (fun T A R S ↦ T = eqvStep A R S) by exact this
  have e : ∀ T A R S : V, T = eqvStep A R S ↔ ∀ p, p ∈ T ↔ p ∈ A ×ˢ A ∧
      ((∃ x ∈ A, p = ⟨x, x⟩ₖ) ∨ p ∈ R ∨
        (∃ x y : V, p = ⟨x, y⟩ₖ ∧ ⟨y, x⟩ₖ ∈ S) ∨
        (∃ x y z : V, p = ⟨x, z⟩ₖ ∧ ⟨x, y⟩ₖ ∈ S ∧ ⟨y, z⟩ₖ ∈ S)) := by
    intro T A R S; rw [mem_ext_iff]; simp [eqvStep]
  simp only [e]
  definability

theorem quotEqv_pred (A R : V) :
    ℒₛₑₜ-predicate[V] (fun p ↦ ∀ S ∈ (℘ (A ×ˢ A) : V), eqvStep A R S ⊆ S → p ∈ S) := by
  have := eqvStep_definable A R
  definability

/-- The equivalence closure, as the intersection of all closed subrelations —
a **Π₁ form**, deliberately.

`Universe.lean`'s `eqvClosure` is `lfp`, hence `⋂ˢ` of the prefixed points, and
`⋂ˢ`'s membership condition carries a nonemptiness clause; that existential is
what makes `definability` diverge.  Stating the same set by its universal
property removes the existential and the proof goes through.  The two agree —
`A ×ˢ A` is itself closed, so the family is nonempty — but nothing below needs
that, because `setQuotient_mem_U` holds for an arbitrary relation. -/
noncomputable def quotEqv (A R : V) : V :=
  sep (A ×ˢ A) (fun p ↦ ∀ S ∈ (℘ (A ×ˢ A) : V), eqvStep A R S ⊆ S → p ∈ S) (quotEqv_pred A R)

theorem quotEqv_definable : ℒₛₑₜ-function₂[V] (fun A R ↦ quotEqv A R) := by
  suffices ℒₛₑₜ-relation₃[V] (fun T A R ↦ T = quotEqv A R) by exact this
  have hs := @eqvStep_definable₃ V
  have e : ∀ T A R : V, T = quotEqv A R ↔ ∀ p, p ∈ T ↔ p ∈ A ×ˢ A ∧
      ∀ S ∈ (℘ (A ×ˢ A) : V), eqvStep A R S ⊆ S → p ∈ S := by
    intro T A R; rw [mem_ext_iff]; simp [quotEqv, mem_sep_iff]
  simp only [e]
  definability

/-- **The denotation of `Quot α r` at universe index `i`.**

At `i = 0` the answer is proof-irrelevant: `Quot r` is a `Prop`, inhabited
exactly when `α` is.  Above that it is the set-theoretic quotient by the
equivalence closure of `r` — `Quot` does not require its relation to be an
equivalence, which is why the closure appears at all. -/
noncomputable def quotVal (α r : V) (i : ℕ) : V :=
  if i = 0 then (if α = ∅ then (∅ : V) else ({pt} : V))
  else setQuotient α (quotEqv α (quotRel α r))

theorem setQuotient_definable₂ : ℒₛₑₜ-function₂[V] (fun A R ↦ setQuotient A R) := by
  suffices ℒₛₑₜ-relation₃[V] (fun T A R ↦ T = setQuotient A R) by exact this
  have e : ∀ T A R : V, T = setQuotient A R ↔ ∀ c, c ∈ T ↔
      ∃ x ∈ A, ∀ z, z ∈ c ↔ (z ∈ A ∧ (⟨x, z⟩ₖ : V) ∈ R) := by
    intro T A R
    rw [mem_ext_iff]
    simp only [mem_setQuotient_iff]
    refine forall_congr' fun c ↦ iff_congr Iff.rfl (exists_congr fun x ↦ and_congr_right fun _ ↦ ?_)
    rw [mem_ext_iff]
    simp [eqvClass]
  simp only [e]
  definability

/-- The `Prop` branch, as a first-order condition: the quotient of a proposition
is inhabited exactly when the proposition is. -/
theorem quotVal_zero_eq (α r : V) :
    quotVal α r 0 = {_z ∈ ({pt} : V) ; α ≠ ∅} := by
  rw [quotVal, if_pos rfl]
  refine subset_antisymm (fun z hz ↦ ?_) (fun z hz ↦ ?_)
  · split at hz
    · exact absurd hz (by simp)
    · exact mem_sep_iff.2 ⟨hz, ‹_›⟩
  · obtain ⟨hz, hne⟩ := mem_sep_iff.1 hz
    rw [if_neg hne]; exact hz

theorem quotVal_definable (i : ℕ) : ℒₛₑₜ-function₂[V] (fun α r ↦ quotVal α r i) := by
  by_cases h : i = 0
  · subst h
    suffices ℒₛₑₜ-relation₃[V] (fun T α r ↦ T = quotVal α r 0) by exact this
    have e : ∀ T α r : V, T = quotVal α r 0 ↔ ∀ z, z ∈ T ↔ (z ∈ ({pt} : V) ∧ α ≠ ∅) := by
      intro T α r; rw [quotVal_zero_eq, mem_ext_iff]; simp [mem_sep_iff]
    simp only [e]
    definability
  · simp only [quotVal, if_neg h]
    have h1 := @quotRel_definable V
    have h2 := @quotEqv_definable V
    have h3 := @setQuotient_definable₂ V
    definability

end

section
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {n : ℕ} {κ : ℕ → V} (hκ : IsInaccessibleChain n κ)

include hκ in
/-- **`Quot` stays in its universe.**  Both branches, and the `Prop` branch
needs nothing from the chain — which is the point of splitting. -/
theorem quotVal_mem_U {i : ℕ} (hi : i < n) {α r : V} (hα : α ∈ U κ i) :
    quotVal α r i ∈ U κ i := by
  rw [quotVal]
  split
  · rename_i h0
    subst h0
    rw [U_zero]
    split
    · exact mem_UProp_iff.2 (by simp)
    · exact true_mem_UProp
  · rename_i h0
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    exact setQuotient_mem_U hκ (Nat.lt_of_succ_lt hi) hα

end

end Lean4Lean.SetModel
