import Lean4Lean.Theory.Typing.Strengthen
import Lean4Lean.Theory.Typing.CycleConv

/-!
# Non-vacuity witnesses for `Theory/Typing/Strengthen.lean`

Every statement `Strengthen.lean` names — `Strengthening`, `TypingStrengthening`,
`TransStrengthening`, `SortDescend`, `PiDescend` — is a `∀`-statement over contexts, and a
`∀`-statement is worth nothing if its hypotheses are never jointly satisfiable.  This file
replays each of them, and the two theorems of `Strengthen.lean` §9, **at an instance over
`CycleConv.propLoopEnv`** — a `VEnv.WF` environment (`propLoopEnv_wf`) with two constants and
two δ-rules — where

* the context being stripped is `[A]`, `A` being an actual *proposition of the environment*
  (`propLoop_isProp`), so the instance does not exist over `VEnv.empty`, which has no
  constants at all;
* the conversion fed to `TransStrengthening.strengthening` is the environment's δ-loop
  `A ≡ B`, **not** a reflexivity — it exists only because of the rules.

The witness deliberately strips a *proposition*: `IsDefEqU.strengthen_of_instN`
(`Strengthen.lean` §1) discharges strengthening whenever the stripped entry is inhabited
downstairs, so a witness whose stripped entry is a `Sort` that the empty context obviously
inhabits would be testing the easy half.

## Correction: the `_fires` implications are **tautologies**, and §3 is the evidence

The `_fires` theorems of §2 are all of the form `Statement → C`, and **every one of those `C`
is provable outright, sorry-free, without the hypothesis** — §4 below proves each of them
unconditionally, machine-checked.  So no `_fires` *statement* certifies anything about its
hypothesis: it could be re-proved tomorrow by a tactic that never mentions `HS`, and the
witness would be silently gone.  This is the same defect as the strengthening capstone that
was found to be a tautology earlier in this development, and it was present here from the
file's first commit.

The evidence is still real, but it lives in the *proof terms*, not the statements, so §3
lifts it to the statement level: `propLoopEnv_sortDescend_premises`,
`propLoopEnv_piDescend_premises` and `propLoopEnv_strengthening_premises` each assert exactly
the premise list of the corresponding statement, at exactly the instantiation §2 uses.  Those
are the theorems to quote for non-vacuity; the `_fires` ones are kept only because
`docs/handoff-weakn.md` §7 names them.

**Why no non-tautological implication exists here.**  A witness for a `∀`-statement can only
discharge premises the reader can check, and for all five statements the premises are typings
*upstairs*, in the larger context, while the conclusion is the corresponding fact
*downstairs*.  Over `propLoopEnv` every term whose upstairs typing can be exhibited is a
closed term whose downstairs typing is the same derivation, so the conclusion is always free.
Making it non-free needs a term typeable only with the stripped entry in scope — which is
precisely what strengthening says does not exist.  Premise-satisfiability, as in §3, is
therefore the strongest honest form.

Everything here is sorry-free **except** `propLoopEnv_piDescend_sortDescend_fires`, which is
`sorryAx`-tainted through `Strengthen.PiDescend.sortDescend` → `IsDefEqU.forallE_inv`
(`Theory/Typing/Injectivity.lean`).  It is also a tautology by §4, so it currently carries no
information at all.  The two consumers that take a hypothesis take it as a hypothesis, so
nothing below asserts `SortDescend` or `PiDescend`.
-/

namespace Lean4Lean
namespace VEnv

open VExpr

/-! ## 1. The witness data -/

/-- `Γ = []`, `Γ' = [A]`: one entry stripped, and it is the environment's proposition `A`. -/
theorem propLoopEnv_W : Ctx.LiftN 1 0 [] [VExpr.const `A []] := .one

theorem propLoopEnv_onCtx : OnCtx [VExpr.const `A []] (propLoopEnv.IsType 0) :=
  ⟨trivial, _, propLoop_isProp.1⟩

/-- `A` is a proposition in *every* context, in particular in the stripped one. -/
theorem propLoopEnv_hA {Γ : List VExpr} :
    propLoopEnv.HasType 0 Γ (.const `A []) (.sort .zero) :=
  hasType_constProp propLoopEnv_A

/-- The δ-loop `A ≡ B`, the conversion that makes this environment interesting. -/
theorem propLoopEnv_AB {Γ : List VExpr} :
    propLoopEnv.IsDefEq 0 Γ (.const `A []) (.const `B []) (.sort .zero) :=
  .extra (ls := []) propLoopEnv_defeqs_A nofun rfl

/-! ## 2. The statements, fired

**Read the module docstring before quoting any of these.**  Each is an implication whose
conclusion §4 proves outright; the premise discharge happens inside the proof term and is
invisible in the statement.  §3 is the statement-level version.
-/

/-- **`SortDescend` fires**: its five hypotheses hold at the witness. -/
theorem propLoopEnv_sortDescend_fires (HS : SortDescend propLoopEnv 0) :
    ∃ u, propLoopEnv.HasType 0 [] (.const `A []) (.sort u) :=
  HS (n := 1) (k := 0) propLoopEnv_W trivial propLoopEnv_onCtx propLoopEnv_hA ⟨_, propLoopEnv_hA⟩

/-- **`PiDescend` fires**: the function is the identity on `Prop`, the argument is the
environment's proposition `A`. -/
theorem propLoopEnv_piDescend_fires (HP : PiDescend propLoopEnv 0) :
    ∃ A₀ B₀, propLoopEnv.HasType 0 [] (.lam (.sort .zero) (.bvar 0)) (.forallE A₀ B₀) ∧
      propLoopEnv.HasType 0 [] (.const `A []) A₀ := by
  refine HP (n := 1) (k := 0) (A := .sort .zero) (B := (VExpr.sort .zero).lift)
    propLoopEnv_W trivial propLoopEnv_onCtx ?_ propLoopEnv_hA
    ⟨_, .lamDF (.sortDF trivial trivial rfl) (.bvar .zero)⟩ ⟨_, propLoopEnv_hA⟩
  show propLoopEnv.HasType 0 _ ((VExpr.lam (.sort .zero) (.bvar 0)).liftN 1 0) _
  rw [show (VExpr.lam (.sort .zero) (.bvar 0)).liftN 1 0 = .lam (.sort .zero) (.bvar 0) by
    simp [VExpr.liftN, liftVar]]
  exact .lamDF (.sortDF trivial trivial rfl) (.bvar .zero)

/-- **§9's `PiDescend.sortDescend` fires** at the same witness. -/
theorem propLoopEnv_piDescend_sortDescend_fires (HP : PiDescend propLoopEnv 0) :
    ∃ u, propLoopEnv.HasType 0 [] (.const `A []) (.sort u) :=
  PiDescend.sortDescend propLoopEnv_wf HP propLoopEnv_W trivial propLoopEnv_onCtx
    propLoopEnv_hA ⟨_, propLoopEnv_hA⟩

/-- **`TypingStrengthening` fires.** -/
theorem propLoopEnv_typingStrengthening_fires (HT : TypingStrengthening propLoopEnv 0) :
    VExpr.WF propLoopEnv 0 [] (.const `A []) :=
  HT (n := 1) (k := 0) propLoopEnv_W trivial propLoopEnv_onCtx propLoopEnv_hA

/-- **§9's `TransStrengthening.strengthening` fires**, at the environment's δ-loop — a
conversion which is not a reflexivity and which does not exist over `VEnv.empty`. -/
theorem propLoopEnv_trans_strengthening_fires (H : TransStrengthening propLoopEnv 0) :
    propLoopEnv.IsDefEqU 0 [] (.const `A []) (.const `B []) :=
  H.strengthening propLoopEnv_W trivial propLoopEnv_onCtx ⟨_, propLoopEnv_AB⟩

/-- **`Strengthening` fires**, at the same δ-loop. -/
theorem propLoopEnv_strengthening_fires (H : Strengthening propLoopEnv 0) :
    propLoopEnv.IsDefEqU 0 [] (.const `A []) (.const `B []) :=
  H propLoopEnv_W trivial propLoopEnv_onCtx ⟨_, propLoopEnv_AB⟩

/-! ## 3. The premises, as statements

The non-vacuity content of §2, hoisted out of the proof terms.  Each theorem below is
literally the premise list of the corresponding definition in `Strengthen.lean`, at the
instantiation `n = 1`, `k = 0`, `Γ = []`, `Γ' = [A]` that §2 uses — so it says "these
hypotheses are jointly satisfiable at a non-degenerate instance" as a *statement*, which is
what a non-vacuity check has to do.  None of them mentions the open statement, so none of
them can be a tautology about it.

The instance is non-degenerate in the two ways that matter: `n = 1`, so `Γ ≠ Γ'` and the
statement is not being read at its trivial `Ctx.LiftN 0` instance; and the stripped entry is
the environment's proposition `A`, for which no inhabitant over `[]` is known, so
`IsDefEqU.strengthen_of_instN` — the easy half — does not discharge it. -/

/-- The lifts at this instance are identities: `A`, `B` and the closed identity function are
closed, so `liftN 1 0` fixes them.  Recorded because §3's statements are otherwise unreadable
against `Strengthen.lean`'s `e.liftN n k` premises. -/
theorem propLoopEnv_liftA : (VExpr.const `A []).liftN 1 0 = .const `A [] := rfl

theorem propLoopEnv_liftB : (VExpr.const `B []).liftN 1 0 = .const `B [] := rfl

theorem propLoopEnv_liftId :
    (VExpr.lam (.sort .zero) (.bvar 0)).liftN 1 0 = .lam (.sort .zero) (.bvar 0) := by
  simp [VExpr.liftN, liftVar]

/-- **`SortDescend`'s five premises hold**, at `n = 1`, `k = 0`, `Γ = []`, `Γ' = [A]`,
`e = A`, `u = 0`. -/
theorem propLoopEnv_sortDescend_premises :
    Ctx.LiftN 1 0 [] [VExpr.const `A []] ∧
    OnCtx [] (propLoopEnv.IsType 0) ∧
    OnCtx [VExpr.const `A []] (propLoopEnv.IsType 0) ∧
    propLoopEnv.HasType 0 [VExpr.const `A []]
      ((VExpr.const `A []).liftN 1 0) (.sort .zero) ∧
    VExpr.WF propLoopEnv 0 [] (.const `A []) :=
  ⟨propLoopEnv_W, trivial, propLoopEnv_onCtx, propLoopEnv_hA, _, propLoopEnv_hA⟩

/-- **`PiDescend`'s seven premises hold**, at the same context pair, with `f` the closed
identity on `Prop` and `a` the environment's proposition `A`. -/
theorem propLoopEnv_piDescend_premises :
    Ctx.LiftN 1 0 [] [VExpr.const `A []] ∧
    OnCtx [] (propLoopEnv.IsType 0) ∧
    OnCtx [VExpr.const `A []] (propLoopEnv.IsType 0) ∧
    propLoopEnv.HasType 0 [VExpr.const `A []]
      ((VExpr.lam (.sort .zero) (.bvar 0)).liftN 1 0)
      (.forallE (.sort .zero) ((VExpr.sort .zero).lift)) ∧
    propLoopEnv.HasType 0 [VExpr.const `A []] ((VExpr.const `A []).liftN 1 0) (.sort .zero) ∧
    VExpr.WF propLoopEnv 0 [] (.lam (.sort .zero) (.bvar 0)) ∧
    VExpr.WF propLoopEnv 0 [] (.const `A []) := by
  refine ⟨propLoopEnv_W, trivial, propLoopEnv_onCtx, ?_, propLoopEnv_hA,
    ⟨_, .lamDF (.sortDF trivial trivial rfl) (.bvar .zero)⟩, _, propLoopEnv_hA⟩
  rw [propLoopEnv_liftId]
  exact .lamDF (.sortDF trivial trivial rfl) (.bvar .zero)

/-- **`Strengthening`'s four premises hold**, and the conversion supplied is the environment's
δ-loop `A ≡ B` — not a reflexivity, and not available over `VEnv.empty`.  This is also
`TransStrengthening`'s premise list after `TransStrengthening.strengthening` has split the
conversion, and `TypingStrengthening`'s after dropping the last conjunct in favour of
`propLoopEnv_sortDescend_premises`' fourth. -/
theorem propLoopEnv_strengthening_premises :
    Ctx.LiftN 1 0 [] [VExpr.const `A []] ∧
    OnCtx [] (propLoopEnv.IsType 0) ∧
    OnCtx [VExpr.const `A []] (propLoopEnv.IsType 0) ∧
    propLoopEnv.IsDefEqU 0 [VExpr.const `A []]
      ((VExpr.const `A []).liftN 1 0) ((VExpr.const `B []).liftN 1 0) :=
  ⟨propLoopEnv_W, trivial, propLoopEnv_onCtx, _, propLoopEnv_AB⟩

/-! ## 4. …and the `_fires` conclusions are free

Each theorem here is the conclusion of one of §2's implications, proved with **no hypothesis
at all**.  Together they are the machine-checked form of the docstring's correction: §2's
statements are tautologies, and a reader who takes `propLoopEnv_sortDescend_fires` as evidence
that `SortDescend`'s premises are satisfiable is reading the proof, not the theorem. -/

/-- Conclusion of `propLoopEnv_sortDescend_fires` and of
`propLoopEnv_piDescend_sortDescend_fires`, unconditionally. -/
theorem propLoopEnv_sortDescend_concl_free :
    ∃ u, propLoopEnv.HasType 0 [] (.const `A []) (.sort u) := ⟨_, propLoopEnv_hA⟩

/-- Conclusion of `propLoopEnv_piDescend_fires`, unconditionally. -/
theorem propLoopEnv_piDescend_concl_free :
    ∃ A₀ B₀, propLoopEnv.HasType 0 [] (.lam (.sort .zero) (.bvar 0)) (.forallE A₀ B₀) ∧
      propLoopEnv.HasType 0 [] (.const `A []) A₀ :=
  ⟨_, _, .lamDF (.sortDF trivial trivial rfl) (.bvar .zero), propLoopEnv_hA⟩

/-- Conclusion of `propLoopEnv_typingStrengthening_fires`, unconditionally. -/
theorem propLoopEnv_typingStrengthening_concl_free :
    VExpr.WF propLoopEnv 0 [] (.const `A []) := ⟨_, propLoopEnv_hA⟩

/-- Conclusion of `propLoopEnv_trans_strengthening_fires` and of
`propLoopEnv_strengthening_fires`, unconditionally. -/
theorem propLoopEnv_strengthening_concl_free :
    propLoopEnv.IsDefEqU 0 [] (.const `A []) (.const `B []) := ⟨_, propLoopEnv_AB⟩

end VEnv
end Lean4Lean
