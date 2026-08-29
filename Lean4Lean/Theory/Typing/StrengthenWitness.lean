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

Everything here is sorry-free; the two consumers that take a hypothesis take it as a
hypothesis, so nothing below asserts `SortDescend` or `PiDescend`.
-/

namespace Lean4Lean
namespace VEnv

open VExpr

/-! ## The witness data -/

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

/-! ## The statements, fired -/

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

end VEnv
end Lean4Lean
