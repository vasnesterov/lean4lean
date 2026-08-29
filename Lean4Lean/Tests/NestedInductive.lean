import Lean4Lean.Environment
import Lean4Lean.Theory.Inductive.NestedPositivity

/-!
Regression tests for the nested-inductive parameter check added for
leanprover/lean4#14577.

When a nested occurrence `I Ds is` is eliminated, the parametric arguments `Ds` are dropped
from the generated auxiliary type, so they escape the ordinary type checking of the
declaration. The kernel checks them separately at the end; so must we.

Both declarations are built by hand rather than elaborated, so that the environment does
not already contain them and only the kernel path is exercised.
-/

namespace Lean4Lean.Tests.NestedInductive

open Lean

/-- `inductive Tree0 (α : Type) | node : Array (Tree0 α) → Tree0 α` -/
def treeDecl : Declaration :=
  let tree := fun a => mkApp (mkConst `Tree0 []) a
  .inductDecl [] 1
    [{ name := `Tree0
       type := .forallE `α (.sort 1) (.sort 1) .default
       ctors := [{
         name := `Tree0.node
         type := .forallE `α (.sort 1)
           (.forallE `es (mkApp (mkConst ``Array [.zero]) (tree (.bvar 0)))
             (tree (.bvar 1)) .default) .default }] }]
    false

/-- As above, but the dropped parametric argument `Tree0 Bool.true` is ill typed. -/
def badDecl : Declaration :=
  .inductDecl [] 1
    [{ name := `Bad0
       type := .forallE `α (.sort 1) (.sort 1) .default
       ctors := [{
         name := `Bad0.node
         type := .forallE `α (.sort 1)
           (.forallE `es
             (mkApp (mkConst ``Array [.zero])
               (mkApp (mkConst `Bad0 []) (mkConst ``Bool.true)))
             (mkApp (mkConst `Bad0 []) (.bvar 1)) .default) .default }] }]
    false

run_meta do
  let kenv := (← getEnv).toKernelEnv

  -- A well-formed nested inductive must be accepted. Storing `aux2nested` abstracted over
  -- the parameters while checking it against a context of free variables regressed this
  -- into "type checker does not support loose bound variables" (#17).
  match Lean4Lean.addDecl kenv treeDecl with
  | .ok _ => pure ()
  | .error e =>
    throwError "nested inductive was rejected: {← (e.toMessageData {}).toString}"

  -- ... and an ill-typed dropped parameter must still be caught.
  match Lean4Lean.addDecl kenv badDecl with
  | .ok _ => throwError "nested inductive with an ill-typed parameter was accepted"
  | .error _ => pure ()

/-! ## The nested-positivity rejection witness

Moved here from `Theory/Inductive/NestedPositivity.lean`, which owns the abstract half.
`Theory/` is the abstract specification the implementation is refined against, so it does not
import the implementation; running the checker belongs on this side of that line.

`docs/handoff-nested-build.md` §3 has the analysis.  This is the *rejection* control that the
handoff recorded as missing: a nested declaration that must be refused for positivity, refused
by this development's own entry point, with the message naming a `_nested…` constant. -/

/-! ## Part 3: the executable rejection

Both declarations are built by hand, so the elaborator never sees them and only the kernel
path — `ElimNestedInductive.run` followed by `AddInductive.run`'s `checkPositivity` — is
exercised.  `Lean4Lean.addDecl` is this development's own entry point. -/

open Lean in
/-- `inductive BadNest | mk : Neg BadNest → BadNest`, with `Neg` the negation carrier
from `Theory/Inductive/NestedPositivity.lean` (fully qualified: bare `Neg` is core's class) -/
def badNestDecl : Declaration :=
  .inductDecl [] 0
    [{ name := `BadNest
       type := .sort 1
       ctors := [{
         name := `BadNest.mk
         type := .forallE `n (mkApp (mkConst ``Lean4Lean.InductiveDeclExamples.Neg []) (mkConst `BadNest []))
           (mkConst `BadNest []) .default }] }]
    false

open Lean in
/-- `inductive OkNest | mk : Wrap OkNest → OkNest` -/
def okNestDecl : Declaration :=
  .inductDecl [] 0
    [{ name := `OkNest
       type := .sort 1
       ctors := [{
         name := `OkNest.mk
         type := .forallE `n (mkApp (mkConst ``Lean4Lean.InductiveDeclExamples.Wrap []) (mkConst `OkNest []))
           (mkConst `OkNest []) .default }] }]
    false

open Lean in
run_meta do
  let kenv := (← getEnv).toKernelEnv
  -- the accept control: a strictly positive nesting must go through
  match Lean4Lean.addDecl kenv okNestDecl with
  | .ok _ => pure ()
  | .error e =>
    throwError "strictly positive nested inductive was rejected: \
      {← (e.toMessageData {}).toString}"
  -- **the rejection witness**
  match Lean4Lean.addDecl kenv badNestDecl with
  | .ok _ =>
    throwError "non-positive nested inductive was ACCEPTED"
  | .error e =>
    let msg ← (e.toMessageData {}).toString
    -- and the rejection is the *auxiliary block's ordinary* positivity check: the message
    -- names the auxiliary constructor, not `BadNest.mk`
    unless (msg.splitOn "non positive occurrence").length == 2 do
      throwError "rejected, but not for positivity: {msg}"
    unless (msg.splitOn "_nested").length == 2 do
      throwError "rejected for positivity, but not at the auxiliary constructor: {msg}"

end Lean4Lean.Tests.NestedInductive
