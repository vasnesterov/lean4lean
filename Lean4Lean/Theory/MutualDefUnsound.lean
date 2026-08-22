import Lean4Lean.Theory.Consistency

/-!
# `VDecl.mutualDef` refutes `leanTTConsistent`

This file exhibits a machine-checked counterexample: an axiom-free `VDecl.WF`
step, applicable over *any* environment in which one name is free, whose result
types an inhabitant of `falseProp = ∀ p : Prop, p`.

## What goes wrong

`VDecl.WF.mutualDef` typechecks each member's *value* in `env'`, the environment
that already carries the block's own constants:

```
| mutualDef :
  (∀ ci ∈ cis, ci.toVConstant.WF env) →
  env.addConsts cis = some env' →
  (∀ ci ∈ cis, ci.WF env') →          -- ← `env'`, not `env`
  VDecl.WF env (.mutualDef cis) (env'.addDefEqs cis)
```

So a member may be defined to be *itself*, and `def f : (∀ p : Prop, p) := f`
passes. Nothing about this is repairable inside the model: `ModelData.cnst f`
would have to satisfy `cnst f = ⟦f⟧`, which is every value at once, and the
declared type has none.

## This is not an implementation divergence

Both kernels behave the same way, and correctly:

* A **safe** mutual block is rejected outright —
  `invalid mutual definition, declaration is not tagged as unsafe/partial` —
  by the C++ kernel (`src/kernel/environment.cpp`, `add_mutual`) and by
  `Lean4Lean.addMutual` alike.
* A **`partial` or `unsafe`** block is accepted by both, and
  `partial def bad : False := bad` really does land in the environment as a
  constant of type `False`.

That is sound for Lean because `partial`/`unsafe` constants carry a
`DefinitionSafety` tag and the kernel refuses to use them while checking a safe
declaration. **The abstract theory models no such tag**: `VConstant` is
`⟨uvars, type⟩`, and `VDecl.WF` has no safety condition anywhere. So the
declaration steps that `Theory/Consistency.lean` lists as the "pure" fragment —
which include `mutualDef` — do not in fact form a consistent theory.

## The fix is a specification decision, not a proof

Two shapes, both outside this file's remit:

1. **Drop `mutualDef` from `VDecl`**, and have the translation keep
   `partial`/`unsafe` declarations out of the `VEnv` entirely. This is the
   semantically honest option: those constants are not part of the trusted
   logic, so they have no business in the theory the model interprets.
   `TrEnv'.mutualDef` is already only reachable with `safety := .unsafe`
   (`Verify/Environment/Extension.lean`), so nothing safe would be lost.
2. **Give `VConstant` a safety flag**, propagate it through `VDecl.WF`, and
   state consistency for the safe fragment. Strictly more faithful, and strictly
   more work everywhere.

Until one of them lands, `ModelData.Coherent` is not provable for an environment
containing a `mutualDef` step — and neither is `leanTTConsistent`.
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
    VDecl.WF env (.mutualDef [selfRefDV]) (env'.addDefEqs [selfRefDV]) := by
  refine .mutualDef (fun ci hci ↦ ?_) ?_ (fun ci hci ↦ ?_)
  · simp only [List.mem_singleton] at hci; subst hci; exact falseProp_isType _
  · show (VEnv.addConst env `f ⟨0, falseProp⟩).bind _ = _
    rw [h]; rfl
  · simp only [List.mem_singleton] at hci; subst hci
    refine hasType_selfRef ?_
    unfold VEnv.addConst at h
    split at h
    · exact absurd h nofun
    · cases h; simp

/-- …and it is axiom-free, so nothing excludes it from `VEnv.LeanWF`. -/
theorem selfRef_axiomFree : (VDecl.mutualDef [selfRefDV]).isAxiomFree := trivial

/-- **…and the environment it produces is inconsistent.** -/
theorem selfRef_inconsistent {env env' : VEnv}
    (h : env.addConst `f ⟨0, falseProp⟩ = some env') :
    ¬ (env'.addDefEqs [selfRefDV]).Consistent := by
  refine fun hcon ↦ hcon ⟨.const `f [], hasType_selfRef ?_⟩
  unfold VEnv.addConst at h
  split at h
  · exact absurd h nofun
  · cases h; simp [VEnv.addDefEqs, VEnv.addDefEq]

end Lean4Lean
