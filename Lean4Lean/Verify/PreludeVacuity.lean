import Lean4Lean.Verify.Bridge
import Lean4Lean.Verify.TypeChecker.Reduce
import Lean4Lean.Verify.Soundness

/-!
# Where the `Bridge` chain is false, and the trap that is next to it

`docs/critical-path.md` reads stop condition 2 as "2 hypotheses + 8 holes + 1 refuted
statement".  This file pins down *which link* of `Verify/Bridge.lean` carries the falsity, and
records a way of "closing" `kernel_sound` that would produce a COMPLETE guard-2 report on a
worthless proof.  Everything here is proved; the one existence fact that a proof cannot supply
is isolated as a hypothesis and backed by an `#eval` check, in the style of
`Verify/Inductive/AddDeclWF.lean` §4.

## The measurement

`VEnvs.WF.no_inductInfo` (`Verify/InductFlip.lean`) says a `VEnvs` model forbids **any**
`.inductInfo` in the constant map, because it quantifies over `safety = .unsafe`, where
`TrEnv'.ignore` cannot fire.  That is what refutes `addDecl.WF`.

At `safety = .safe` the corresponding statement is *false* — `no_inductInfo_false_at_safe`
(`Verify/TypeChecker/Reduce.lean`) exhibits an **unsafe** inductive sitting in a `.safe`-level
map, admitted by `ignore`.  So one cannot conclude from `TrEnv .safe` alone that there is no
inductive.

`§1` closes that gap in the one direction that matters: `ignore` needs `¬ safety ≤ ci.safety`,
and at `safety = .safe` — the top of `DefinitionSafety` — that forces `ci.safety ≠ .safe`.  A
**safe** inductive therefore cannot be ignored either, and no other `TrEnv'` constructor emits
an `.inductInfo` while `AddInduct` is empty.  Hence `TrEnv .safe env venv` is unsatisfiable as
soon as `env` holds one safe inductive, with no `VEnv`-side guard required.

`§2` applies this to `stdPrelude`, whose head is `eqDecl`, an `.inductDecl` with
`isUnsafe := false`.  The consequences:

* `foldAddDecl_tr` (`Verify/Bridge.lean:172`) — "the accepted environment has a `.safe` model"
  — is a **false statement**, refuted at `ds = stdPrelude`.  This is the link the falsity of
  `addDecl.WF` actually reaches; it is upstream of everything else in the chain.
* `PreludeBridge stdPrelude` (H1) takes `TrEnv .safe env venv` as a *hypothesis*, so at the
  instances the main theorem uses it is **vacuously true**.  Discharging H1 as it stands buys
  the main theorem nothing.

## The trap

`Verify/Inductive/AddDeclWF.lean` §5.4 item 3 proposes, as part of landing the honest
postcondition, that `foldAddDecl_tr` "become a hypothesis alongside `PreludeBridge`".  §3 below
records why that must not be done in that form: the statement is refuted, so assuming it makes
`kernel_sound` derivable from a falsehood — `Verify/Guard.lean`'s guard 2 would print
"proof COMPLETE" with no `sorryAx` anywhere, and the theorem would mean nothing.  A hypothesis
is only honest if it is satisfiable; the repair has to weaken the *conclusion* of the chain
(to `AddDeclPost`, and a fold-level invariant that does not claim `TrEnv .safe`), not assume
the false form.

This file states no axiom and closes no hole.  It is a measurement.
-/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

/-! ## 1. A safe inductive is not compatible with `TrEnv .safe`

Unconditional, and — unlike `TrEnv.not_inductInfo` — with no `∃ ci', venv.constants name = …`
guard: at `safety = .safe` the guard is free, because `.safe` is the top of
`DefinitionSafety`. -/

theorem safe_le_safety_inductInfo {v : InductiveVal} (hu : v.isUnsafe = false) :
    DefinitionSafety.safe ≤ (ConstantInfo.inductInfo v).safety := by
  simp [ConstantInfo.safety, ConstantInfo.isUnsafe, ConstantInfo.isPartial, hu]

/-- **The measurement.**  `TrEnv .safe env venv` is unsatisfiable once `env` holds a *safe*
inductive.  `no_inductInfo_false_at_safe` shows the `isUnsafe = false` hypothesis cannot be
dropped: an unsafe inductive really can sit in a `.safe`-level map. -/
theorem TrEnv.not_safe_inductInfo {env : Environment} {venv : VEnv}
    (H : TrEnv .safe env venv) {name v} (h : env.find? name = some (.inductInfo v))
    (hu : v.isUnsafe = false) : False := by
  have h' : env.constants.find? name = some (.inductInfo v) := by
    rw [← H.map_wf.find?'_eq_find?]; exact h
  rcases TrEnv'.find?_shape H h' (safe_le_safety_inductInfo hu) with
    ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> cases h

/-! ## 2. `foldAddDecl_tr` is false, and H1 is vacuous at the instances that matter -/

/-- The environment the checker really produces from `stdPrelude` holds a safe inductive.
A proof cannot supply this: it is a fact about running the checker.  Check B below evaluates
it. -/
def PreludeHoldsSafeInduct : Prop :=
  ∃ (fuel : FuelConfig) (env : Kernel.Environment) (name : Name) (v : InductiveVal),
    foldAddDecl fuel stdPrelude = .ok env ∧
    env.find? name = some (.inductInfo v) ∧ v.isUnsafe = false

/-- **`foldAddDecl_tr`'s statement is false.**  Not "open": there is no environment model of
the prelude at `.safe` while `AddInduct` is empty. -/
theorem foldAddDecl_tr_false (hex : PreludeHoldsSafeInduct) :
    ¬ ∀ (fuel : FuelConfig) (ds : List Declaration) (env : Kernel.Environment),
        foldAddDecl fuel ds = .ok env → ∃ venv : VEnv, TrEnv .safe env venv ∧ venv.WF := by
  obtain ⟨fuel, env, name, v, hok, hfind, hu⟩ := hex
  intro H
  obtain ⟨venv, htr, -⟩ := H fuel stdPrelude env hok
  exact htr.not_safe_inductInfo hfind hu

/-- **H1 is vacuous where the main theorem uses it.**  `Bridge.PreludeBridge stdPrelude`
assumes `TrEnv .safe env venv`; at `ds = []` that hypothesis is unsatisfiable, so the
implication holds with nothing proved about `LeanWF`.

Stated at `ds = []` on purpose: extending it to every `ds` needs a monotonicity lemma for the
executable `addDecl` on constant maps (`find?` is preserved by a later successful step), which
does not exist in the tree.  The instance below is already enough to refute the reading of H1
as "the one remaining hypothesis that carries real content". -/
theorem preludeBridge_vacuous_at_nil (hex : PreludeHoldsSafeInduct)
    (P : VEnv → Prop) :
    ∃ (fuel : FuelConfig) (env : Kernel.Environment),
      foldAddDecl fuel (stdPrelude ++ []) = .ok env ∧
      ∀ venv : VEnv, TrEnv .safe env venv → P venv := by
  obtain ⟨fuel, env, name, v, hok, hfind, hu⟩ := hex
  exact ⟨fuel, env, by simpa using hok, fun _ htr => (htr.not_safe_inductInfo hfind hu).elim⟩

/-! ### Check B: the checker really produces a safe inductive from `stdPrelude`

An evaluation, not a proof — it is what backs `PreludeHoldsSafeInduct`. -/

open Lean.Elab.Command in
#eval show Lean.CoreM Unit from do
  match foldAddDecl {} stdPrelude with
  | .error _ => throwError "check B: the checker rejected stdPrelude"
  | .ok env =>
    let some (.inductInfo v) := env.find? ``Eq
      | throwError "check B: Eq is not an inductInfo in the prelude environment"
    unless v.isUnsafe = false do throwError "check B: Eq came out unsafe"
    Lean.logInfo s!"check B: stdPrelude leaves Eq an inductInfo, isUnsafe = {v.isUnsafe} \
      -- so TrEnv .safe has no model of it and foldAddDecl_tr is false"

/-! ## 3. The trap, stated as a theorem

If the false form is assumed, anything follows.  This is not a hypothetical: item 3 of
`Verify/Inductive/AddDeclWF.lean` §5.4 proposes assuming exactly this shape. -/

/-- **Assuming `foldAddDecl_tr` proves anything.**  Any `Q` at all — `kernel_sound`'s
conclusion included.  A guard-2 run over such a proof would report "proof COMPLETE". -/
theorem anything_of_foldAddDecl_tr_hypothesis (hex : PreludeHoldsSafeInduct)
    (hbad : ∀ (fuel : FuelConfig) (ds : List Declaration) (env : Kernel.Environment),
      foldAddDecl fuel ds = .ok env → ∃ venv : VEnv, TrEnv .safe env venv ∧ venv.WF)
    (Q : Prop) : Q :=
  absurd hbad (foldAddDecl_tr_false hex)

end Lean4Lean
