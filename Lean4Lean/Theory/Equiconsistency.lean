import Foundation.FirstOrder.SetTheory.InaccessibleCardinal
import Lean4Lean.Theory.Consistency
import Lean4Lean.Theory.SetModel.UpperBound
import Lean4Lean.Theory.SetModel.PreludeOracle  -- 2026-09-02: InductOracleOK at the prelude's `.induct nonemptyIndDecl` step, at `preludeEnv`. Imported for the same reason as PreludeWitness below: `oracleStepOK_NE_at_preludeEnv` discharges one of the three `.induct` obligations inside `OracleInput`, and §11 of that file names the single hypothesis (`PropTypeAgree preludeEnv 0`) that keeps the parameter `L : PropSplit preludeEnv nv` from being known inhabited.
import Lean4Lean.Theory.SetModel.PropAgreeWall  -- 2026-09-02: the answer to "is `PropTypeAgree preludeEnv 0` the injectivity wall?". Imported so the reduction is load-bearing here: `preludeEnv_propTypeAgreeOnCtx` discharges the context-guarded half of `PropTypeAgreeInput`'s instance at the witness environment unconditionally, and `nonempty_propSplit_preludeEnv_of_ctxReplace` names the single residual (`CtxReplace preludeEnv 0`) that keeps `PropSplit preludeEnv 0` from being known inhabited.
import Lean4Lean.Theory.SetModel.PreludeWitness  -- 2026-09-02: preludeWF / exists_leanWF. Imported so the witness is LOAD-BEARING here, not merely proved: without it `leanTTConsistent` and all three of `upper_bound_of_inputs`'s inputs are statements about a possibly-empty class (`upper_bound_vacuous_of_no_leanWF`), and `not_forall_not_leanWF` is what refutes that collapse.

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

/-! ## Which half `kernel_sound` needs

`kernel_sound`'s conclusion is `Entailment.Inconsistent 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰`, reached from
a checker run that certifies `False`.  Composed through the refinement chain that
gives `¬ leanTTConsistent`, the only part of the equiconsistency it consumes is
the **upper bound** — the `←` direction, "a model of `ZFC + n inaccessibles`
interprets Lean TT".  The lower bound (`→`, building models of
`ZFC + n inaccessibles` inside Lean TT) is not on the path to `kernel_sound` at
all; it is what makes the statement above an `↔` rather than an implication.

Recording that as a lemma so the endgame does not re-derive it: the whole
`SetModel/` tower is aimed at the hypothesis of this theorem, not at the `↔`. -/

/-- **The half `kernel_sound` needs**, isolated: the upper bound alone suffices.
`Entailment.Inconsistent` is the negation of `Entailment.Consistent`, so
contraposing the upper bound gives exactly `kernel_sound`'s conclusion. -/
theorem inconsistent_of_upper_bound
    (h : Entailment.Consistent 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰 → leanTTConsistent)
    (hbad : ¬ leanTTConsistent) : Entailment.Inconsistent 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰 :=
  Entailment.not_consistent_iff_inconsistent.mp fun hc ↦ hbad (h hc)

/-- The upper bound is the `←` direction of the theorem above, so nothing is
lost by aiming the model at it. -/
theorem upper_bound_of_equiconsistent
    (h : Entailment.Consistent 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰 ↔ leanTTConsistent) :
    Entailment.Consistent 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰 → leanTTConsistent := h.mp

/-! ## The `←` half, as a theorem of its own

The `↔` above keeps its `sorry`: its `→` half is not this project's theorem, and its `←`
half is not unconditional either.  What *is* available is the `←` half from three named
inputs, which is what `SetModel/UpperBound.lean` assembles out of the whole `SetModel/`
tower — the thirteen-case soundness induction, the `VEnv.WF'` recursion for the constant
assignment, the inaccessible chain, and Foundation's completeness theorem.

Read `upper_bound_of_inputs` with §3–§5 of that file: the three inputs and the conclusion are
**simultaneously** free if `VEnv.LeanWF` is uninhabited, and the tree exhibits no inhabitant.
`SetModel.exists_leanWF_iff` pins the missing object as `SetModel.PreludeWF`. -/

/-- **The upper bound, from the three model-side inputs** — the half `kernel_sound` consumes.
Composing with `inconsistent_of_upper_bound` above turns a checker run certifying `False`
into `Entailment.Inconsistent 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰`.

The three inputs are, in the vocabulary of `SetModel/UpperBound.lean`:
`PropTypeAgreeInput` (unique typing, in the one form the interpretation needs),
`InstDescendInput` (the substitution-descent residual of `PropSplit.Stable`), and
`OracleInput` (the `.axiom`/`.quot`/`.induct` oracle obligations).  Everything else the
model needs is discharged. -/
theorem leanTTConsistent_of_consistent_zfcInacc
    (hTI : SetModel.PropTypeAgreeInput) (hII : SetModel.InstDescendInput)
    (hO : SetModel.OracleInput) :
    Entailment.Consistent 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰 → leanTTConsistent :=
  SetModel.upper_bound_of_inputs hTI hII hO

/-- …and the same composed all the way to `kernel_sound`'s conclusion, so that the endgame
reads off one statement rather than three. -/
theorem inconsistent_zfcInacc_of_inputs
    (hTI : SetModel.PropTypeAgreeInput) (hII : SetModel.InstDescendInput)
    (hO : SetModel.OracleInput) (hbad : ¬ leanTTConsistent) :
    Entailment.Inconsistent 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰 :=
  inconsistent_of_upper_bound (leanTTConsistent_of_consistent_zfcInacc hTI hII hO) hbad

end Lean4Lean
