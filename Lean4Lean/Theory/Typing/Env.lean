import Lean4Lean.Theory.Typing.Basic
import Lean4Lean.Theory.VDecl
import Lean4Lean.Theory.Quot
import Lean4Lean.Theory.Inductive.Restore

namespace Lean4Lean

def VDefVal.WF (env : VEnv) (ci : VDefVal) : Prop := env.HasType ci.uvars [] ci.value ci.type

/-- Add a block of constants, without their defining equations. -/
def VEnv.addConsts (env : VEnv) (cis : List VDefVal) : Option VEnv :=
  cis.foldlM (fun env ci => env.addConst ci.name ci.toVConstant) env

/-- Add the defining equations of a block, after all of its constants. -/
def VEnv.addDefEqs (env : VEnv) (cis : List VDefVal) : VEnv :=
  cis.foldl (fun env ci => env.addDefEq ci.toDefEq) env

inductive VDecl.WF : VEnv → VDecl → VEnv → Prop where
  | axiom :
    ci.WF env →
    env.addConst ci.name ci.toVConstant = some env' →
    VDecl.WF env (.axiom ci) env'
  | def :
    ci.WF env →
    env.addConst ci.name ci.toVConstant = some env' →
    VDecl.WF env (.def ci) (env'.addDefEq ci.toDefEq)
  /-- A `partial`/`unsafe` mutual block. The values are checked in `env'`, which already
  carries the block's own constants, so this rule is *circular by design*: it is the only
  `VDecl.WF` rule that can make a well-formed environment inconsistent. See `VDecl` and
  `Theory/MutualDefUnsound.lean`; `VDecl.isPure` excludes it. -/
  | unsafeDef :
    (∀ ci ∈ cis, ci.toVConstant.WF env) →
    env.addConsts cis = some env' →
    (∀ ci ∈ cis, ci.WF env') →
    VDecl.WF env (.unsafeDef cis) (env'.addDefEqs cis)
  | opaque :
    ci.WF env →
    env.addConst ci.name ci.toVConstant = some env' →
    VDecl.WF env (.opaque ci) env'
  | example :
    ci.WF env →
    VDecl.WF env (.example ci) env
  | quot :
    env.QuotReady →
    env.addQuot = some env' →
    VDecl.WF env .quot env'
  | induct :
    decl.WF env →
    env.addInduct' decl = some env' →
    VDecl.WF env (.induct decl) env'

/-! ### The nested `.induct` step, and what is left before it can be a rule

`Environment.addInductive`'s **nested** path does not run `addInduct'` on any `VInductDecl'`.
It elaborates an *auxiliary* block with one extra member per nested occurrence, declares those
members' **recursors** under renamed names (`I.rec_1`, `I.rec_2`, …), and declares neither
their type constants nor their constructors — so the constant list it adds is
`D.allConstsCR R K`, not `D.allConsts`, and the `induct` rule above is *refutable* for such a
block (`tBlock_not_addInductStages`, `Verify/Environment/InductR.lean`).

The step is `VEnv.AddNestedStep` (`Theory/Inductive/Restore.lean`), and **it is nameable here**
— which it was not before: `VEnv.addInductR` and `VIndRestore.Faithful` lived downstream of
this file, and `Faithful` additionally carried the declaration history `ds : List VDecl`,
which `VDecl.WF env d env'` has not got.  Both are fixed: the definitions moved upstream, and
`Faithful.ctors_complete` now asks for `VInductDecl'.Declared`, the same fact over the
environment alone, which a history discharges (`VEnv.WF'.declared`).  The `example` below is
the machine-checked statement that the name elaborates at this position in the import graph.

The rule it would add is exactly

```lean
  | inductNested {D : VInductDecl'} {K : List Lean.Name} {R : VIndRestore} :
    VEnv.AddNestedStep env D K R env' →
    VDecl.WF env (.induct D) env'
```

and it is **not added**, for two measured reasons.

1. **`VEnv.WF.ordered` (`Theory/Typing/EnvLemmas.lean`) would have no proof.**  Its `induct`
   arm is `addInduct_WF`, i.e. `addInduct'_ordered_final`; the nested arm needs
   `addInductR_ordered`, and that is not bookkeeping — `Ordered` records that every declared
   constant's type was `IsType` at its staging environment, so it demands that the
   **restored** constructor and recursor types are well typed and the restored ι-rules well
   formed.  For a user constructor whose field was rewritten from `_nested.List_1 α` back to
   `List (Tree α)` that is the substantive nested-soundness theorem, not a corollary of
   `D.WF env`.  `VEnv.addInductR_ordered'` (`Theory/Inductive/NestedOrdered.lean`) factors it
   into exactly the three obligations that remain.
2. **Adding a constructor to `VDecl.WF` breaks four proofs in two files this stream does not
   own** — `Theory/Typing/DeltaUnique.lean` (`WF'.defEqHeads`, `WF'.keys`, `WF'.iotaTypes`)
   and `Theory/Typing/PatternRules.lean` (`WF'.ruleShape`) — plus five in
   `Theory/Inductive/Nested.lean` and one each here-adjacent in `EnvLemmas.lean` and
   `DeclRules.lean`, which are owned.  Measured by adding a clone constructor and building:
   that is the *complete* list; nothing in `Verify/` case-splits on `VDecl.WF`.
-/

/-- **The nested step is nameable at this position in the import graph.**  Machine-checked
prerequisite for the `inductNested` rule above; see the section docstring. -/
example (env env' : VEnv) (D : VInductDecl') (K : List Lean.Name) (R : VIndRestore) : Prop :=
  VEnv.AddNestedStep env D K R env'

/-- A declaration step other than `.axiom` and `.unsafeDef`: the *pure* fragment.
All other steps are conservative, in that `VDecl.WF` requires them to typecheck
*in the environment before the step*, so (by the intended metatheory) they cannot
introduce inconsistency over the standard prelude. `Theory/Consistency.lean`
states consistency for exactly this fragment.

Both exclusions are load-bearing. `.axiom` is obvious. `.unsafeDef` models a
`partial`/`unsafe` mutual block, whose values are checked in the environment that
already carries the block's own constants; `Theory/MutualDefUnsound.lean`
exhibits a well-formed `.unsafeDef` step producing an inhabitant of `falseProp`,
so any fragment containing it is *provably* inconsistent. -/
def VDecl.isPure : VDecl → Prop
  | .axiom _ => False
  | .unsafeDef _ => False
  | _ => True

instance : ∀ d : VDecl, Decidable d.isPure
  | .axiom _ | .unsafeDef _ => .isFalse id
  | .def _ | .opaque _ | .example _ | .quot | .induct _ => .isTrue trivial

/-- The weaker half of `VDecl.isPure`: not a `partial`/`unsafe` block. `.axiom` steps
are still permitted, so this is what the *refinement layer* can supply on its own
(`TrEnv'.wf_noUnsafe`); ruling out further axioms is separate bookkeeping about the
kernel-level declaration list. -/
def VDecl.noUnsafe : VDecl → Prop
  | .unsafeDef _ => False
  | _ => True

theorem VDecl.isPure.noUnsafe : ∀ {d : VDecl}, d.isPure → d.noUnsafe
  | .def _, _ | .opaque _, _ | .example _, _ | .quot, _ | .induct _, _ => trivial

inductive VEnv.WF' : List VDecl → VEnv → Prop where
  | empty : VEnv.WF' [] .empty
  | decl {env} : VDecl.WF env d env' → env.WF' ds → env'.WF' (d::ds)

def VEnv.WF (env : VEnv) : Prop := ∃ ds, VEnv.WF' ds env
