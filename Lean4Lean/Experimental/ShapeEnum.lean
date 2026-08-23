/-
# Bounded enumeration and proof-carrying search

## Why this file exists

Every counterexample on the shape-model route so far has been a HAND-BUILT WITNESS.  That
asymmetry shaped the whole route: a hand-built witness can only ever produce "here is a
counterexample", never "there is none".  So every question needing the NEGATIVE answer got
settled by inference instead -- and inference on that route failed three times in three turns
(see `ShapeLogRel.lean` banner sections 13-15).

This file is the tool that converts such a guess into a decision.

## The vacuity guard, and why it is structural rather than advisory

A search that silently examines NOTHING looks identical to a search that found nothing.  That
is the same failure class as a `sorryAx`-backed declaration reading like a proof, and this
project now has several instances of it.  So `none_in_range` DOES NOT let you state "nothing
in range satisfies `P`" on its own: it demands, in the same theorem, a list of `probes` that
are machine-checked to LIE IN the range.  A range that examines nothing cannot cover a
non-empty probe list, so the vacuous case cannot be stated.  Pass the known witnesses as
probes and the guard is meaningful; pass `[]` and you have proved nothing and the statement
says so.

## Deliberately NOT importing `ShapeLogRel`

`Lean4Lean.Experimental.ShapeLogRel` currently has 12 errors, so lake emits NO `.olean` for it
(only `.olean.hash` / `.trace`) and it CANNOT BE IMPORTED.  Everything here is therefore
generic over `α` and depends on nothing but core.  The `Shape`-specific pools are built at the
use site, where `Shape`, `hasType`, `join` and `ble` are in scope.  This also keeps the tool
green while its consumer is red.

## Trust boundary -- read before quoting a result

  * `witness?` / `#eval` SEARCH.  Fast, and NOT trusted: `#eval` runs compiled code.
    A hit is a lead, not a fact.
  * `witness_mem` CERTIFIES a hit: instantiate at the found element and discharge by `decide`
    (or `rfl`).  That is kernel-checked and is what may be quoted.
  * `none_in_range` CERTIFIES an exhaustive negative, by `decide`, and is therefore limited to
    ranges the kernel can actually chew through.  `native_decide` would scale it but adds
    `Lean.ofReduceBool` to the axiom set, which on this project is a trust hole rather than a
    convenience -- so it is not used here, and a range too big to `decide` must be REPORTED AS
    UNDECIDED rather than quoted as clear.
-/

namespace Lean4Lean.Enum

/-! ## Bounded enumeration combinators -/

/-- Every list of length exactly `k` drawn from `pool`. -/
def listsOfLen (pool : List α) : Nat → List (List α)
  | 0 => [[]]
  | k + 1 => (listsOfLen pool k).flatMap fun t => pool.map (· :: t)

/-- Every list of length at most `k` drawn from `pool`. -/
def listsUpTo (pool : List α) (k : Nat) : List (List α) :=
  (List.range (k + 1)).flatMap (listsOfLen pool)

/-- The full cartesian product. -/
def pairs (xs : List α) (ys : List β) : List (α × β) :=
  xs.flatMap fun a => ys.map fun b => (a, b)

theorem mem_pairs {xs : List α} {ys : List β} {a b} :
    (a, b) ∈ pairs xs ys ↔ a ∈ xs ∧ b ∈ ys := by
  simp [pairs]

/-- Size of a range, for reporting alongside a result.  A range's size is part of the claim:
"clear over 45" and "clear over 4" are different facts. -/
abbrev size (xs : List α) : Nat := xs.length

/-! ## The search driver -/

namespace Search

/-- Untrusted search.  `#eval` this; do not quote it.  Certify a hit with `witness_mem`. -/
def witness? (P : α → Bool) (xs : List α) : Option α := xs.find? P

/-- Certification for a hit: membership in the range, and that `P` really fires. -/
theorem witness_mem {P : α → Bool} {xs : List α} {a : α} (h : witness? P xs = some a) :
    a ∈ xs ∧ P a = true :=
  ⟨List.mem_of_find?_eq_some h, List.find?_eq_some_iff_append.1 h |>.1⟩

/-- `P` fires nowhere in the range. -/
def clear (P : α → Bool) (xs : List α) : Bool := xs.all fun x => !P x

/-- The range covers every probe.  This is the vacuity guard. -/
def covers [DecidableEq α] (xs probes : List α) : Bool :=
  probes.all fun p => decide (p ∈ xs)

/--
**Proof-carrying exhaustive negative.**

Reads: "`P` holds nowhere in `xs`, AND `xs` demonstrably contains every one of `probes`."

The second conjunct is not decoration.  Without it, `xs = []` proves the first conjunct
vacuously and the result is indistinguishable from a real exhaustive check.  Supply the known
witnesses as `probes`: then a vacuous range cannot satisfy `hcov`, and the theorem cannot be
stated at all.  Supply `probes = []` and the theorem is honest but says nothing.
-/
theorem none_in_range [DecidableEq α] {P : α → Bool} {xs probes : List α}
    (hclear : clear P xs = true) (hcov : covers xs probes = true) :
    (∀ x ∈ xs, P x = false) ∧ (∀ p ∈ probes, p ∈ xs) := by
  refine ⟨fun x hx => ?_, fun p hp => ?_⟩
  · have := List.all_eq_true.1 hclear x hx
    simpa using this
  · have := List.all_eq_true.1 hcov p hp
    simpa using this

/-- Convenience: the negative statement alone, once the guard has been discharged separately. -/
theorem not_mem_of_clear {P : α → Bool} {xs : List α} (hclear : clear P xs = true)
    {a : α} (ha : a ∈ xs) : P a = false := by
  have := List.all_eq_true.1 hclear a ha; simpa using this

end Search

/-! ## Self-test

A search tool that cannot rediscover a counterexample it is known to contain is not validated,
and its "clear" answers are worthless.  These run the driver against a toy predicate with a
known witness and a known-clear range, so that a regression in the combinators shows up here
rather than as a silently empty search. -/

section SelfTest

private def toyPool : List Nat := [0, 1, 2, 3, 4, 5]

/-- The driver FINDS a witness that is there. -/
example : Search.witness? (fun n => decide (n * n = 9)) toyPool = some 3 := by decide

/-- ... and certifying that hit is kernel-checked. -/
example : (3 : Nat) ∈ toyPool ∧ (decide (3 * 3 = 9)) = true := by decide

/-- The driver reports CLEAR when nothing matches -- together with a non-empty probe list,
so this is an exhaustive negative and not a vacuous one. -/
example : (∀ n ∈ toyPool, (decide (n * n = 7)) = false) ∧ (∀ p ∈ [0, 5], p ∈ toyPool) :=
  Search.none_in_range (by decide) (by decide)

/-- The vacuity guard bites: the empty range cannot cover a non-empty probe list. -/
example : Search.covers ([] : List Nat) [0] = false := by decide

/-- Enumeration sizes are as intended (a silent change here would shrink every later range). -/
example : (listsOfLen toyPool 2).length = 36 := by decide
example : (listsUpTo toyPool 1).length = 7 := by decide
example : (pairs toyPool toyPool).length = 36 := by decide

end SelfTest

end Lean4Lean.Enum
