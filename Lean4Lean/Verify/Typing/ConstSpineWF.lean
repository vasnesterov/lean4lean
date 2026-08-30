import Lean4Lean.Theory.Typing.PatWFIota
import Lean4Lean.Verify.Typing.Rigidity

/-!
# The constant-application family with `PatWF` discharged

`Verify/Typing/ConstSpine.lean` proves facts (A), (B) and (D) about constant applications at
an arbitrary `VEnv.WF` environment, **conditional on `VEnv.PatWF`** — at the time it was
written, `PatWF` was the one open field of `VEnv.Params`.

`VEnv.patWF` (`Theory/Typing/PatWFIota.lean`) has since closed all three of `Pat`'s
constructors at an arbitrary `VEnv.WF` environment, with `VEnv.PiInv` as the only extra
hypothesis, and `VEnv.piInv_axiom` (`Theory/Typing/Injectivity.lean`) supplies `PiInv` from
the **existing** census hole `IsDefEqU.forallE_inv`.  This file composes the two, so the
family becomes unconditional in the environment: `VEnv.WF` and nothing else.

This file exists rather than the composition being done in `Theory/`: `ConstSpine.lean` is
under `Verify/`, and a `Theory/` file may not import it.

## What the measurement says, and what it does **not**

**[measured]** — forward hole cone, transitive over type *and* value, `allowOpaque := true`:

    VEnv.const_app_inv_of_patWF   weakN_iff, forallE_inv_stratified, NormalEq.descend, forallE_inv
    VEnv.const_app_inv_of_wf      (the same four; `patWF` contributes only
                                   forallE_inv_stratified, `piInv_axiom` only forallE_inv)

So discharging `PatWF` **adds nothing to the cone**.  What it buys is that `PatWF` is no
longer a *carried hypothesis*: `TrProj.uniq`'s obligations (2) and (3) were blocked on
producing one, and now are not.

**The caveat, and it is not small.**  Every result here routes through
`VEnv.IsDefEq.church_rosser`, and `VEnv.not_crStatement_of_kstep`
(`Theory/Typing/KCanonical.lean`) refutes `church_rosser`'s *statement* at any `Params`
instance registering the ι-rule of a large-eliminating subsingleton — `Eq` being the standard
one.  `VEnv.paramsOfPiInv` at an arbitrary `VEnv.WF` environment is such an instance whenever
the environment declares `Eq`.  Three registers, kept apart:

* **[measured]** `not_crStatement_of_kstep`'s own hole cone is `forallE_inv_stratified`
  *alone* — it does **not** contain `NormalEq.descend`, so the refutation is not circular
  with the hole `church_rosser` is waiting on.
* **[read off source]** no `Params` instance discharging that refutation's hypotheses is
  built in this tree (`PatWFIota.lean`'s own note says a full ι witness is not constructed),
  so what exists is a *conditional* refutation, not a counterexample.
* **[analysis]** if such an instance is built, `NormalEq.descend` is false, and this whole
  family — (A), (B), (D), and `constRigid_of_weakNorm` with it — has to be re-derived by
  another route.  The statements below are not thereby refuted; their *proof* is.

Nothing here is `sorry`-free, and nothing here should be read as closing a census hole.
-/

namespace Lean4Lean
namespace VEnv

/-- **`VEnv.PatWF` at an arbitrary well-formed environment**, with Π-injectivity taken from
the existing census hole rather than carried. -/
theorem patWF_of_wf {env : VEnv} (henv : env.WF) (U : Nat) : env.PatWF U :=
  patWF henv (piInv_axiom henv)

/-- **(B) and (D) together**, at an arbitrary well-formed environment. -/
theorem constApp_inv_of_wf {env : VEnv} (henv : env.WF) (U : Nat)
    {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U)) {c c' : Lean.Name} {ls ls' : List VLevel}
    {as as' : List VExpr}
    (hc : env.RuleFreeHead c) (hc' : env.RuleFreeHead c')
    (hty : env.IsType U Γ ((VExpr.const c ls).mkApp as))
    (H : env.IsDefEqU U Γ ((VExpr.const c ls).mkApp as) ((VExpr.const c' ls').mkApp as')) :
    c = c' ∧ List.Forall₂ (· ≈ ·) ls ls' ∧ List.Forall₂ (env.IsDefEqU U Γ) as as' :=
  constApp_inv_of_patWF henv U (patWF_of_wf henv U) hΓ hc hc' hty H

/-- **(B)** `IsDefEqU.const_app_inv`, at an arbitrary well-formed environment. -/
theorem const_app_inv_of_wf {env : VEnv} (henv : env.WF) (U : Nat) :
    ConstAppInvStmt env U :=
  constAppInvStmt_of_patWF henv U (patWF_of_wf henv U)

/-- **(A)**, Π half, at an arbitrary well-formed environment. -/
theorem const_forallE_inv_of_wf {env : VEnv} (henv : env.WF) (U : Nat) :
    ConstForallEInvStmt env U :=
  constForallEInvStmt_of_patWF henv U (patWF_of_wf henv U)

/-- **(A)**, sort half, at an arbitrary well-formed environment. -/
theorem const_sort_inv_of_wf {env : VEnv} (henv : env.WF) (U : Nat) :
    ConstSortInvStmt env U :=
  constSortInvStmt_of_patWF henv U (patWF_of_wf henv U)

/-- **(D)** `VEnv.ConstNoConf`, at an arbitrary well-formed environment. -/
theorem constNoConf_of_wf {env : VEnv} (henv : env.WF) (U : Nat) : env.ConstNoConf U :=
  constNoConf_of_patWF henv U (patWF_of_wf henv U)

/-! ## Non-vacuity, re-fired with the hypothesis gone

`Verify/Typing/Rigidity.lean`'s `propLoopEnv2` witnesses fired (A) and (D) with `PatWF`
discharged *by hand*, from the δ fragment.  The point of the two below is different: they are
the same conclusions with **no** `PatWF` argument anywhere, at an environment whose `WF` is
proved from `VEnv.empty`.  If the family had become vacuous in the discharge, these would not
typecheck. -/

theorem propLoopEnv2_A_ne_B' :
    ¬ propLoopEnv2.IsDefEqU 0 [] (.const `A []) (.const `B []) := by
  intro h
  have := (constApp_inv_of_wf propLoopEnv2_wf 0 (Γ := []) trivial
    (c := `A) (c' := `B) (ls := []) (ls' := []) (as := []) (as' := [])
    propLoopEnv2_ruleFree propLoopEnv2_ruleFree
    ⟨_, hasType_constProp propLoopEnv2_A⟩ h).1
  exact absurd this (by decide)

theorem propLoopEnv2_A_ne_sort' {u : VLevel} :
    ¬ propLoopEnv2.IsDefEqU 0 [] (.const `A []) (.sort u) :=
  const_sort_inv_of_wf propLoopEnv2_wf 0 [] `A [] [] u trivial propLoopEnv2_ruleFree

end VEnv
end Lean4Lean
