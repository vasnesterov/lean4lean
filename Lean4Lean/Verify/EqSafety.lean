import Lean4Lean.Verify.SafeFragment

/-!
# `Eq` must be safe for quotient initialization

`Verify/SafeFragment.lean` §3 records that `TrEnv safety env venv` with `env.quotInit = true`
forces `Eq` to be *visible at `safety`* (`TrEnv.eq_visible_of_quotInit`), hence at
`safety = .safe` forces `Eq` to be a **safe** declaration -- and that neither
`Lean4Lean.checkEqType` nor the C++ kernel's `check_eq_type` checked that.

`checkEqType` now checks it (`Lean4Lean/Quot.lean`; see `divergences.md`, `bugs-found.md`).
This file is the proof-side counterpart:

* §1 `TrEnv.eq_isUnsafe_false_of_quotInit` -- the model's demand, spelled as a fact about
  `InductiveVal.isUnsafe`.  This is the *necessity* direction: the check `checkEqType` now
  performs is not a convenience, it is exactly what the `.safe` model requires.
* §2 `checkEqType.WF_safe` -- the *sufficiency* direction, and the honest, **non-vacuous**
  postcondition of `checkEqType`: on success, `Eq` is an inductive declaration present in the
  kernel environment and its `ConstantInfo.safety` is `.safe`.  Contrast the current
  `checkEqType.WF` in `Verify/Environment.lean`, whose postcondition is `False`.
* §3 `checkEqType.WF_visible` -- the same fact in the shape `TrEnv.eq_visible_of_quotInit`
  consumes it: `Eq` is visible at *every* safety level.
* §4 `checkEqType.WF_quotReady` -- the full replacement for `checkEqType.WF`, i.e. what
  `addQuot.WF` actually needs (`VEnv.QuotReady` at every safety level), reduced to the one
  premise that is *not* available from the checker: that a safe inductive `Eq` of the checked
  shape translates to `eqConst`.  That premise is the `AddInduct`/`TrEnv'.induct` obligation
  (`Theory/Inductive/Decl.lean`); `AddInduct` has no constructors today, so it cannot be
  discharged here.  Everything else `addQuot.WF` needs is proved.

**What changed.** Before the checker change, §1 and §2 were *contradictory* for an
`unsafe inductive Eq`: §1 says the `.safe` model demands `isUnsafe = false`, and `checkEqType`
returned `.ok` anyway, so `∃ venv, TrEnv .safe env venv` after the `.quotDecl` step was
**false**, not merely unproved.  With the check in place the two agree, and §4 is a genuine
reduction of `addQuot.WF` to the inductive-translation obligation rather than a vacuity
argument.
-/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

/-! ## 1. Necessity: the `.safe` model demands a safe `Eq` -/

theorem ConstantInfo.safety_inductInfo (info : InductiveVal) :
    (ConstantInfo.inductInfo info).safety = if info.isUnsafe then .unsafe else .safe := by
  cases h : info.isUnsafe <;>
    simp [ConstantInfo.safety, ConstantInfo.isUnsafe, ConstantInfo.isPartial, h]

/-- **The model's demand, in the checker's vocabulary.**

If the `.safe` model exists for a quotient-initialized environment whose `Eq` is an inductive
declaration, then that declaration is *not* unsafe.  This is what `checkEqType` must enforce;
it is `TrEnv.eq_safe_of_quotInit` read through `ConstantInfo.safety_inductInfo`. -/
theorem TrEnv.eq_isUnsafe_false_of_quotInit {env : Environment} {venv : VEnv}
    {info : InductiveVal} (H : TrEnv .safe env venv) (hq : env.quotInit = true)
    (hfind : env.find? ``Eq = some (.inductInfo info)) : info.isUnsafe = false := by
  have h := H.eq_safe_of_quotInit hq hfind
  rw [ConstantInfo.safety_inductInfo] at h
  cases hu : info.isUnsafe with
  | false => rfl
  | true => rw [hu] at h; simp at h

/-! ## 2. Sufficiency: the honest, non-vacuous postcondition of `checkEqType` -/

/-- **The honest replacement for `checkEqType.WF`'s `False`.**

On success `checkEqType env` guarantees that `Eq` is an inductive declaration in `env` and that
it is `safe`.  No `VEnvs.WF` hypothesis, and nothing vacuous: this is read straight off the
executable checker. -/
theorem checkEqType.WF_safe {env : Environment} :
    (checkEqType env).WF fun _ =>
      ∃ info : InductiveVal, env.find? ``Eq = some (.inductInfo info) ∧
        info.isUnsafe = false ∧ (ConstantInfo.inductInfo info).safety = .safe := by
  intro _ h
  unfold checkEqType at h
  simp only [Environment.get] at h
  split at h <;> try contradiction
  rename_i ci hfind
  cases ci with
  | inductInfo info =>
    have hu : info.isUnsafe = false := by
      cases hu : info.isUnsafe with
      | false => rfl
      | true => simp [hu, ( · >>= · ), Except.bind, pure, Pure.pure, Except.pure] at h
    exact ⟨info, hfind, hu, by simp [ConstantInfo.safety_inductInfo, hu]⟩
  | _ => simp_all [( · >>= · ), Except.bind, pure, Pure.pure, Except.pure]

/-! ## 3. The shape `TrEnv.eq_visible_of_quotInit` consumes -/

/-- On success, `Eq` is visible at *every* safety level -- the premise
`TrEnv.eq_visible_of_quotInit` extracts from any model of a quotient-initialized environment,
now **established by the checker** rather than assumed. -/
theorem checkEqType.WF_visible {env : Environment} :
    (checkEqType env).WF fun _ =>
      ∀ ci, env.find? ``Eq = some ci → ∀ safety, safety ≤ ci.safety :=
  WF_safe.mono fun _ ⟨info, hfind, _, hsafe⟩ ci hci safety => by
    cases hci.symm.trans hfind; rw [hsafe]; exact DefinitionSafety.le_safe

/-! ## 4. What `addQuot.WF` needs, and the one premise still missing -/

/-- **The full replacement for `checkEqType.WF`**, modulo the inductive-translation obligation.

`addQuot.WF`'s non-initialized branch must build `TrEnv'.quot`, whose first premise is
`VEnv.QuotReady (ves.venv safety)`, i.e. `(ves.venv safety).constants ``Eq = some eqConst`.
This theorem delivers exactly that, from one hypothesis:

`htr` -- *a safe inductive `Eq` present in the kernel environment translates to `eqConst`*.

`htr` is the `AddInduct` / `TrEnv'.induct` obligation and nothing else: it is the statement
that the abstract environment's model of the `Eq` inductive block is the `eqConst` of
`Theory/Quot.lean`.  It is not provable today because `AddInduct` has no constructors, so
`TrEnv'` cannot place *any* inductive in a model (`TrEnv'.no_inductInfo`); it is precisely the
piece `Theory/Inductive/Decl.lean` is designed to supply.

Everything else `addQuot.WF` needs at this step is discharged here: presence of `Eq`, its
safety, and hence its visibility at every level. -/
theorem checkEqType.WF_quotReady {env : Environment} {ves : VEnvs}
    (htr : ∀ (safety : DefinitionSafety) (info : InductiveVal),
      env.find? ``Eq = some (.inductInfo info) → info.isUnsafe = false →
      (ves.venv safety).constants ``Eq = some eqConst) :
    (checkEqType env).WF fun _ => ∀ safety, (ves.venv safety).QuotReady :=
  WF_safe.mono fun _ ⟨info, hfind, hu, _⟩ safety => htr safety info hfind hu

end Lean4Lean
