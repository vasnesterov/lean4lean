import Foundation.FirstOrder.SetTheory.InaccessibleCardinal
import Lean4Lean.Theory.Consistency

/-!
# Main theorem: Lean TT is equiconsistent with ZFC + ω-many inaccessibles

This file states the main metatheoretic theorem of this development, following
M. Carneiro, *The Type Theory of Lean* (2019), Theorem 5.10 / Chapter 6:

> Lean's type theory is consistent if and only if
> `ZFC + {"there exist at least n inaccessible cardinals" | n ∈ ω}` is.

The two sides come from independent developments and share no syntax:

* `leanTTConsistent` (this repository, `Lean4Lean.Theory.Consistency`): no
  environment built from the standard prelude (`Eq`, `Iff`, `Nonempty`,
  `propext`, `Quot.sound`, `Classical.choice`, quotients) by axiom-free
  well-formed declaration steps types an inhabitant of `∀ p : Prop, p`.

* `Entailment.Consistent 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰` (Foundation): the first-order theory
  `ZFC` plus the sentence schema "there exist at least `n` inaccessible
  cardinals" (one sentence per meta-level `n : ℕ`) does not derive `⊥`.

The intended proof is fragment-wise, mirroring the fact that a single Lean
proof uses finitely many universes and a single first-order derivation uses
finitely many schema instances:

* (←, upper bound) from a model of `ZFC + n inaccessibles`, interpret
  Lean TT restricted to `n` universe levels in `V_{κ_n}`;
* (→, lower bound) inside Lean TT, construct for each `n` a model of
  `ZFC + n inaccessibles` (Foundation's `Universe.{0}` model of `𝗭𝗙𝗖` is the
  `n = 0` instance of exactly this construction).
-/

namespace Lean4Lean

open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-- **Equiconsistency of Lean's type theory with
`ZFC + {≥ n inaccessible cardinals | n ∈ ω}`** (Carneiro 2019).

The right-hand side is `leanTTConsistent`: every environment obtained from the
standard prelude by axiom-free well-formed declarations is consistent. The
left-hand side is consistency of the first-order set theory `𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰`. -/
theorem leanTT_equiconsistent_zfc_omega_inaccessibles :
    Entailment.Consistent 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰 ↔ leanTTConsistent := by
  sorry

end Lean4Lean
