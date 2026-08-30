import Lean4Lean.Verify.Environment.Basic
import Lean4Lean.Theory.Inductive.StructureEta

/-!
# The `IsStructure` bridge, and why `AddInduct` as currently designed cannot supply it

`docs/handoff-eta.md` §5 isolated the single step that blocks `tryEtaStructCore.WF`:

> supply `c.venv.IsStructure I D T C` from `c.env.isNonRecStructure I = true`.

This file names that step (`StructureBridge`) and reports a **machine-checked finding about
it**: the bridge does not follow from `AddInduct`'s *intended* definition either.  It is not
merely blocked on `AddInduct` being empty.

## The finding

`AddInductStages` (`Verify/Environment/Basic.lean`) — and `AddInductStagesR`
(`Verify/Environment/InductR.lean`), the nested-aware replacement — relate the constant map to
the abstract block through `AddIndConsts` at the shape predicates

```
fun ci => ∃ v, ci = .inductInfo v      fun ci => ∃ v, ci = .ctorInfo v      … .recInfo …
```

and through `TrConstant`, which is
`safety ≤ ci.safety ∧ ci.levelParams.length = ci'.uvars ∧ TrExprS env … ci.type ci'.type`.

**Nothing there mentions `InductiveVal.isRec`, `.ctors`, `.numIndices` or `.numParams`, or
`ConstructorVal.numFields`, `.numParams` or `.induct`** — and those six fields are exactly
what `Environment.isNonRecStructure` and the two eta checks read.  So the abstract environment
does not determine, and is not determined by, the answer `isNonRecStructure` gives.

`addInductStages_bookkeeping_free` below proves this at `R10.Wit.decl`, the tree's existing
`AddInductStages` witness: *the same* block, *the same* starting map and environment, and
*the same* resulting `VEnv`, with the map's `InductiveVal` carrying whatever `isRec`,
`ctors` and `numIndices` one likes.  `isNonRecStructure_not_determined` reads off the
consequence: one run makes `isNonRecStructure` say `true`, another makes it say `false`, and
the abstract side is identical in both.

This is the information-flow defect the standing method note describes — *a statement carrying
less information than its conclusion needs* — caught on the relation rather than on a theorem.

## What must change

`AddIndConsts`'s shape predicate for the type stage has to record the bookkeeping.
`IndShape`/`CtorShape` below are the strengthenings, written out so that the eventual edit to
`AddInductStages` is a substitution rather than a redesign.  Neither is used by anything yet:
they are the *statement* of what the flip owes structure eta, and the flip is a coordinated
change across files this stream does not own.

With `IndShape` in place the bridge is a lookup: `isNonRecStructure I = true` gives
`v.numIndices = 0`, `v.ctors = [c]` and `v.isRec = false`; `IndShape` transports those to
`T.indices = []`, `T.ctors.length = 1` and `C.recFields = []`, which with `D.types = [T]`
(from the type stage having a single entry for `I`) is every field of `VEnv.IsStructure`
except `decl`, and `decl` is `AddInductStages.to_addInduct` plus `TrEnv'.induct`'s `D.WF`
premise.

## Scope

`StructureBridge` is stated but **not proved**, and it is not proved *vacuously* either: the
vacuous route (`TrEnv.not_inductInfo`) needs the name to be one the `VEnv` already holds,
which `isNonRecStructure` alone does not give.  Nothing in this file is a `sorry`; the bridge
is a definition, and the theorems about it are the negative results above.
-/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

/-- **The bridge**, exactly as `docs/handoff-eta.md` §5 names it: the kernel environment's
verdict that `I` is a non-recursive structure, transported to the abstract environment.

The extra conjuncts beyond `IsStructure` are the two the eta rule needs and `IsStructure`
does not carry: no indices (`isNonRecStructure` tests `numIndices = 0`) and a field count
agreeing with the `ConstructorVal` the checker reads its loop bound from. -/
def StructureBridge (safety : DefinitionSafety) (env : Environment) (venv : VEnv) : Prop :=
  TrEnv safety env venv →
  ∀ I : Name, env.isNonRecStructure I = true →
    ∃ D T C, venv.IsStructure I D T C ∧ T.indices = [] ∧
      ∀ ci : ConstructorVal, env.find? C.name = some (.ctorInfo ci) →
        ci.numFields = C.fields.length ∧ ci.numParams = D.np

/-- The strengthened shape predicate the **type** stage of `AddInduct` must use, if the bridge
is ever to be provable.  Compare the current one, `fun ci => ∃ v, ci = .inductInfo v`. -/
def IndShape (D : VInductDecl') (T : VIndType) (ci : ConstantInfo) : Prop :=
  ∃ v : InductiveVal, ci = .inductInfo v ∧
    v.numParams = D.np ∧ v.numIndices = T.indices.length ∧
    v.ctors = T.ctors.map (·.name) ∧ v.all = D.types.map (·.name) ∧
    (v.isRec = false → ∀ C ∈ T.ctors, C.recFields = [])

/-- The strengthened shape predicate for the **constructor** stage. -/
def CtorShape (D : VInductDecl') (T : VIndType) (C : VIndCtor) (ci : ConstantInfo) : Prop :=
  ∃ v : ConstructorVal, ci = .ctorInfo v ∧
    v.induct = T.name ∧ v.numParams = D.np ∧ v.numFields = C.fields.length

namespace R10.Wit

/-- `R10.Wit.uInd` with the three fields `isNonRecStructure` reads left free.  Every field
`TrConstant` and `AddIndConsts` constrain — `name`, `levelParams`, `type`, `isUnsafe` — is
fixed; the rest is a parameter. -/
def uIndWith (numIndices : Nat) (ctors : List Name) (isRec : Bool) : InductiveVal where
  name := `R10.Wit.U; levelParams := []; type := .sort (.succ .zero)
  numParams := 0; numIndices := numIndices; all := [`R10.Wit.U]; ctors := ctors
  numNested := 0; isRec := isRec; isUnsafe := false; isReflexive := false

/-- `uInd` is the instance with the structure bookkeeping. -/
theorem uIndWith_eq : uIndWith 0 [`R10.Wit.U.unit] false = uInd := rfl

/-- **`AddInductStages` at `decl`, with the type constant's bookkeeping a free parameter.**

This is `addInductStages_wit`'s proof with `uInd` replaced by `uIndWith ni cs ir`.  That the
replacement goes through unchanged *is* the finding: the three obligations the type stage
imposes on its `ConstantInfo` are `ci.name = n` (`rfl`), the shape (`⟨_, rfl⟩`) and
`TrConstant` (`⟨by decide, rfl, .sort rfl⟩`), and none of them looks at `numIndices`, `ctors`
or `isRec`. -/
theorem addInductStages_with {m : ConstMap} (hwf : m.WF) (hfr : ∀ n, m.find? n = none)
    (ni : Nat) (cs : List Name) (ir : Bool) :
    ∃ m' env', AddInductStages m VEnv.empty decl m' env' ∧
      m'.find? `R10.Wit.U = some (.inductInfo (uIndWith ni cs ir)) ∧
      VEnv.empty.addInduct' decl = some env' := by
  obtain ⟨e1, he1⟩ := VEnv.addConst_eq_none (env := VEnv.empty) (name := `R10.Wit.U)
    (ci := ⟨0, .sort (.succ .zero)⟩) rfl
  have c1 := VEnv.addConst_constants_eq he1
  have hU1 : e1.constants `R10.Wit.U = some ⟨0, .sort (.succ .zero)⟩ := by rw [c1]; simp
  obtain ⟨e2, he2⟩ := VEnv.addConst_eq_none (env := e1) (name := `R10.Wit.U.unit)
    (ci := ⟨0, .const `R10.Wit.U []⟩) (by rw [c1]; simp [VEnv.empty])
  have c2 := VEnv.addConst_constants_eq he2
  have hU2 : e2.constants `R10.Wit.U = some ⟨0, .sort (.succ .zero)⟩ := by
    rw [c2]; simp [hU1]
  have hu2 : e2.constants `R10.Wit.U.unit = some ⟨0, .const `R10.Wit.U []⟩ := by rw [c2]; simp
  obtain ⟨e3, he3⟩ := VEnv.addConst_eq_none (env := e2) (name := `R10.Wit.U.rec)
    (ci := ⟨0, decl.recType 0⟩) (by rw [c2, c1]; simp [VEnv.empty])
  have w1 := hwf.insert `R10.Wit.U (.inductInfo (uIndWith ni cs ir)) (hfr _)
  have f2 : (m.insert `R10.Wit.U (.inductInfo (uIndWith ni cs ir))).find? `R10.Wit.U.unit
      = none := by rw [hwf.find?_insert]; simp [hfr]
  have w2 := w1.insert `R10.Wit.U.unit (.ctorInfo uCtor) f2
  have s1 : AddIndConsts (fun ci => ∃ v, ci = .inductInfo v) decl.typeConsts
      m VEnv.empty (m.insert `R10.Wit.U (.inductInfo (uIndWith ni cs ir))) e1 :=
    .cons (ci := .inductInfo (uIndWith ni cs ir)) rfl ⟨_, rfl⟩
      ⟨DefinitionSafety.le_safe, rfl, .sort rfl⟩
      (hfr _) he1 .nil
  have s2 : AddIndConsts (fun ci => ∃ v, ci = .ctorInfo v) decl.ctorConsts
      (m.insert `R10.Wit.U (.inductInfo (uIndWith ni cs ir))) e1
      ((m.insert `R10.Wit.U (.inductInfo (uIndWith ni cs ir))).insert `R10.Wit.U.unit
        (.ctorInfo uCtor)) e2 :=
    .cons (ci := .ctorInfo uCtor) rfl ⟨_, rfl⟩ ⟨by decide, rfl, .const hU1 rfl rfl⟩ f2 he2 .nil
  have s3 : AddIndConsts (fun ci => ∃ v, ci = .recInfo v) decl.recConsts
      ((m.insert `R10.Wit.U (.inductInfo (uIndWith ni cs ir))).insert `R10.Wit.U.unit
        (.ctorInfo uCtor)) e2
      ((((m.insert `R10.Wit.U (.inductInfo (uIndWith ni cs ir))).insert `R10.Wit.U.unit
        (.ctorInfo uCtor))).insert `R10.Wit.U.rec (.recInfo uRec)) e3 :=
    .cons (ci := .recInfo uRec) rfl ⟨_, rfl⟩ ⟨by decide, rfl, tr_recType hU2 hu2⟩
      (by rw [w1.find?_insert, hwf.find?_insert]; simp [hfr, Lean.mkRecName]) he3 .nil
  have H : AddInductStages m VEnv.empty decl _ (e3.addIndRules decl) :=
    ⟨_, _, _, _, e3, s1, s2, s3, rfl⟩
  refine ⟨_, _, H, ?_, H.to_addInduct⟩
  rw [w2.find?_insert, w1.find?_insert]; simp [hwf.find?_insert]

/-- **The `InductiveVal` bookkeeping is free.**  Two `AddInductStages` runs of the *same*
block from the *same* map and environment, landing on the *same* `VEnv`, whose type constants
differ in every field `isNonRecStructure` inspects. -/
theorem addInductStages_bookkeeping_free {m : ConstMap} (hwf : m.WF)
    (hfr : ∀ n, m.find? n = none)
    (ni₁ ni₂ : Nat) (cs₁ cs₂ : List Name) (ir₁ ir₂ : Bool) :
    ∃ m₁ m₂ env', AddInductStages m VEnv.empty decl m₁ env' ∧
      AddInductStages m VEnv.empty decl m₂ env' ∧
      m₁.find? `R10.Wit.U = some (.inductInfo (uIndWith ni₁ cs₁ ir₁)) ∧
      m₂.find? `R10.Wit.U = some (.inductInfo (uIndWith ni₂ cs₂ ir₂)) := by
  obtain ⟨m₁, env₁, H₁, hf₁, ha₁⟩ := addInductStages_with hwf hfr ni₁ cs₁ ir₁
  obtain ⟨m₂, env₂, H₂, hf₂, ha₂⟩ := addInductStages_with hwf hfr ni₂ cs₂ ir₂
  cases ha₁.symm.trans ha₂
  exact ⟨m₁, m₂, env₁, H₁, H₂, hf₁, hf₂⟩

/-- **`isNonRecStructure`'s verdict is not a function of the abstract environment.**  Same
block, same abstract result; the map says "non-recursive structure" in one run and "recursive"
in the other.

Hence no lemma of the form `isNonRecStructure I = true → (something about venv)` can be proved
from `AddInductStages`/`AddInductStagesR` as they stand — including `StructureBridge`. -/
theorem isNonRecStructure_not_determined {m : ConstMap} (hwf : m.WF)
    (hfr : ∀ n, m.find? n = none) :
    ∃ m₁ m₂ env' v₁ v₂,
      AddInductStages m VEnv.empty decl m₁ env' ∧
      AddInductStages m VEnv.empty decl m₂ env' ∧
      m₁.find? `R10.Wit.U = some (.inductInfo v₁) ∧
      m₂.find? `R10.Wit.U = some (.inductInfo v₂) ∧
      (v₁.isRec = false ∧ v₁.ctors = [`R10.Wit.U.unit] ∧ v₁.numIndices = 0) ∧
      v₂.isRec = true := by
  obtain ⟨m₁, m₂, env', H₁, H₂, hf₁, hf₂⟩ :=
    addInductStages_bookkeeping_free hwf hfr 0 0 [`R10.Wit.U.unit] [`R10.Wit.U.unit] false true
  exact ⟨m₁, m₂, env', _, _, H₁, H₂, hf₁, hf₂, ⟨rfl, rfl, rfl⟩, rfl⟩

end R10.Wit

end Lean4Lean
