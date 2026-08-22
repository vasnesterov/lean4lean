import Lean4Lean.Theory.Consistency

/-!
# `VDecl.unsafeDef` is impure — regression test

This file is the machine-checked justification for two design decisions, and it
must keep building: if either is ever undone, this file goes red.

1. `VDecl.isPure` (`Theory/Typing/Env.lean`) is `False` on `.unsafeDef`.
2. `TrEnv'.unsafeDef` (`Verify/Environment/Basic.lean`) carries a safety gate,
   so the `safe`-level model never takes the step (`TrEnv'.wf_noUnsafe`).

## What goes wrong without them

`VDecl.WF.unsafeDef` typechecks each member's *value* in `env'`, the environment
that already carries the block's own constants:

```
| unsafeDef :
  (∀ ci ∈ cis, ci.toVConstant.WF env) →
  env.addConsts cis = some env' →
  (∀ ci ∈ cis, ci.WF env') →          -- ← `env'`, not `env`
  VDecl.WF env (.unsafeDef cis) (env'.addDefEqs cis)
```

So a member may be defined to be *itself*, and `def f : (∀ p : Prop, p) := f`
passes. `selfRef_wf` below builds that step over any environment in which one
name is free; `selfRef_inconsistent` inhabits `falseProp` in the result. Nothing
about this is repairable inside the model: `ModelData.cnst f` would have to
satisfy `cnst f = ⟦f⟧`, which is every value at once, and the declared type has
none. It was a real defect while `isAxiomFree` (the predecessor of `isPure`)
admitted the step: `leanTTConsistent` was then *false*, with this witness.

## This is not an implementation divergence

Both kernels behave the same way, and correctly. Verified empirically against
`Lean4Lean.addDecl` and `Lean.Kernel.Environment.addDeclCore` on the same
environment, with identical error text in every case:

* A **safe** mutual block is rejected outright —
  `invalid mutual definition, declaration is not tagged as unsafe/partial` —
  by the C++ kernel (`src/kernel/environment.cpp`, `add_mutual`) and by
  `Lean4Lean.addMutual` alike. So a kernel `mutualDefnDecl` is *only* ever
  `partial`/`unsafe`, and gating `TrEnv'.unsafeDef` on the tag discards nothing.
* A **`partial` or `unsafe`** block is accepted by both, and
  `partial def bad : (∀ p : Prop, p) := bad` really does land in the environment
  as a constant of that type.
* A **safe** declaration mentioning such a constant is rejected by both, at
  `src/kernel/type_checker.cpp:109-117` and `Lean4Lean/TypeChecker.lean:125-131`
  respectively (`infer_constant`, guarded by `!infer_only`) — in the value, in
  the type, under a beta redex, under a `let`, under `mdata`, and in the
  constructor type of an inductive. The safe fragment is closed.

That is sound for Lean because `partial`/`unsafe` constants carry a
`DefinitionSafety` tag and the kernel refuses to use them while checking a safe
declaration. **The abstract theory models no such tag**: `VConstant` is
`⟨uvars, type⟩`, and `VDecl.WF` has no safety condition anywhere. Hence the
split: `.unsafeDef` stays in `VDecl` — the `partial`/`unsafe`-level models in
`Verify/` need it, because the kernel delta-unfolds a `partial` definition
(`ConstantInfo.deltaValue?` is `some` for every `defnInfo`, and `isDelta` has no
safety guard), so those models must carry a circular defining equation — but it
is excluded from the pure fragment that `leanTTConsistent` quantifies over, and
gated out of the `safe`-level model.
-/

namespace Lean4Lean

/-- `f : ∀ p : Prop, p`, whose value is `f` itself. -/
def selfRefCV : VConstVal := ⟨⟨0, falseProp⟩, `f⟩

/-- The same, as a definition whose value is the constant it defines. -/
def selfRefDV : VDefVal := ⟨selfRefCV, .const `f []⟩

theorem falseProp_isType (env : VEnv) : env.IsType 0 [] falseProp :=
  ⟨_, VEnv.IsDefEq.forallEDF (u := .succ .zero) (v := .zero)
    (.sortDF trivial trivial rfl) (.bvar .zero)⟩

theorem hasType_selfRef {env : VEnv} (h : env.constants `f = some ⟨0, falseProp⟩) :
    env.HasType 0 [] (.const `f []) falseProp :=
  VEnv.IsDefEq.constDF (ci := ⟨0, falseProp⟩) h nofun nofun rfl .nil

/-- **The step is well-formed** over any environment in which `f` is free. -/
theorem selfRef_wf {env env' : VEnv} (h : env.addConst `f ⟨0, falseProp⟩ = some env') :
    VDecl.WF env (.unsafeDef [selfRefDV]) (env'.addDefEqs [selfRefDV]) := by
  refine .unsafeDef (fun ci hci ↦ ?_) ?_ (fun ci hci ↦ ?_)
  · simp only [List.mem_singleton] at hci; subst hci; exact falseProp_isType _
  · show (VEnv.addConst env `f ⟨0, falseProp⟩).bind _ = _
    rw [h]; rfl
  · simp only [List.mem_singleton] at hci; subst hci
    refine hasType_selfRef ?_
    unfold VEnv.addConst at h
    split at h
    · exact absurd h nofun
    · cases h; simp

/-- **…and the environment it produces is inconsistent.** -/
theorem selfRef_inconsistent {env env' : VEnv}
    (h : env.addConst `f ⟨0, falseProp⟩ = some env') :
    ¬ (env'.addDefEqs [selfRefDV]).Consistent := by
  refine fun hcon ↦ hcon ⟨.const `f [], hasType_selfRef ?_⟩
  unfold VEnv.addConst at h
  split at h
  · exact absurd h nofun
  · cases h; simp [VEnv.addDefEqs, VEnv.addDefEq]

/-- **Decision 1, pinned.** The step is *not* pure, so `VEnv.LeanWF` — and hence
`leanTTConsistent` — never sees it. Were this `trivial` instead, the two theorems above
would refute `leanTTConsistent`. -/
theorem selfRef_not_isPure : ¬ (VDecl.unsafeDef [selfRefDV]).isPure := id

/-- The same for the weaker predicate the refinement layer supplies. -/
theorem selfRef_not_noUnsafe : ¬ (VDecl.unsafeDef [selfRefDV]).noUnsafe := id

/-- Every *other* `VDecl` former is pure, so the exclusion is exactly one constructor wide. -/
example (ci : VConstVal) (cd : VDefVal) (D : VInductDecl') :
    (VDecl.def cd).isPure ∧ (VDecl.opaque cd).isPure ∧ (VDecl.example cd).isPure ∧
      (VDecl.quot).isPure ∧ (VDecl.induct D).isPure ∧ ¬ (VDecl.axiom ci).isPure :=
  ⟨trivial, trivial, trivial, trivial, trivial, id⟩

end Lean4Lean
