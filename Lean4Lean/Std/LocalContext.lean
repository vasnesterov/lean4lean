import Lean.LocalContext
import Std.Data.HashMap.Lemmas
import Lean4Lean.Std.Basic

/-!
# A pure local context

`Lean.LocalContext` stores its declarations in a `PersistentHashMap` and a `PersistentArray`,
both of whose traversal/insertion helpers are `partial` upstream, hence `opaque`: nothing at
all can be proved about them, which is why `Lean4Lean/Verify/Axioms.lean` had to *assume*
`PersistentArray.WF.toList'_push`, `PersistentHashMap.WF.toList'_insert`,
`PersistentHashMap.WF.find?_eq` and `PersistentHashMap.findAux_isSome`.

This module replaces the container with `Std.HashMap` + `Array`, both of which have a complete
verified API upstream. The API mirrors `Lean.LocalContext` exactly for the operations the
kernel uses (`mkLocalDecl`, `mkLetDecl`, `find?`, `findFVar?`, `get!`, `contains`,
`mkBinding`/`mkLambda`/`mkForall`); `mkBinding` is a verbatim copy of the upstream body, which
only ever consults `findFVar?`.

The `auxDeclToFullName` field is dropped: the kernel never writes it, and it is the only
reason `Lean.Name.quickCmp` (an `@[extern]` function) is structurally reachable from the
checker at all.
-/

namespace Lean
instance : LawfulBEq FVarId where
  eq_of_beq {a b} h := by cases a; cases b; exact congrArg _ (eq_of_beq (α := Name) h)
  rfl {a} := by cases a; exact beq_self_eq_true (α := Name) _
end Lean

namespace Lean4Lean
open Lean

/-- A local context: a finite map from `FVarId` to `LocalDecl`, together with the declarations
in insertion order.  Mirrors `Lean.LocalContext` minus `auxDeclToFullName`, with verified
containers. -/
structure LocalContext where
  fvarIdToDecl : Std.HashMap FVarId LocalDecl := {}
  decls        : Array (Option LocalDecl)     := #[]
  deriving Inhabited

namespace LocalContext

def empty : LocalContext := {}

def isEmpty (lctx : LocalContext) : Bool := lctx.fvarIdToDecl.isEmpty

def mkLocalDecl (lctx : LocalContext) (fvarId : FVarId) (userName : Name) (type : Expr)
    (bi : BinderInfo := BinderInfo.default) (kind : LocalDeclKind := .default) : LocalContext :=
  match lctx with
  | { fvarIdToDecl := map, decls := decls } =>
    let idx  := decls.size
    let decl := LocalDecl.cdecl idx fvarId userName type bi kind
    { fvarIdToDecl := map.insert fvarId decl, decls := decls.push decl }

def mkLetDecl (lctx : LocalContext) (fvarId : FVarId) (userName : Name) (type : Expr)
    (value : Expr) (nondep := false) (kind : LocalDeclKind := default) : LocalContext :=
  match lctx with
  | { fvarIdToDecl := map, decls := decls } =>
    let idx  := decls.size
    let decl := LocalDecl.ldecl idx fvarId userName type value nondep kind
    { fvarIdToDecl := map.insert fvarId decl, decls := decls.push decl }

def find? (lctx : LocalContext) (fvarId : FVarId) : Option LocalDecl :=
  lctx.fvarIdToDecl[fvarId]?

def findFVar? (lctx : LocalContext) (e : Expr) : Option LocalDecl :=
  lctx.find? e.fvarId!

def get! (lctx : LocalContext) (fvarId : FVarId) : LocalDecl :=
  match lctx.find? fvarId with
  | some d => d
  | none   => panic! "unknown free variable"

def getFVar! (lctx : LocalContext) (e : Expr) : LocalDecl := lctx.get! e.fvarId!

def contains (lctx : LocalContext) (fvarId : FVarId) : Bool :=
  lctx.fvarIdToDecl.contains fvarId

def containsFVar (lctx : LocalContext) (e : Expr) : Bool := lctx.contains e.fvarId!

/-- Verbatim copy of `Lean.LocalContext.mkBinding`; it consults the context only through
`findFVar?`. -/
@[inline] def mkBinding (isLambda : Bool) (lctx : LocalContext) (xs : Array Expr) (b : Expr)
    (usedLetOnly : Bool := true) (generalizeNondepLet := false) : Expr :=
  let b := b.abstract xs
  xs.size.foldRev (init := b) fun i _ b =>
    let x := xs[i]
    let handleCDecl (n : Name) (ty : Expr) (bi : BinderInfo) : Expr :=
      let ty := ty.abstractRange i xs;
      if isLambda then
        Lean.mkLambda n bi ty b
      else
        Lean.mkForall n bi ty b
    match lctx.findFVar? x with
    | some (.cdecl _ _ n ty bi _)  =>
      handleCDecl n ty bi
    | some (.ldecl _ _ n ty val nondep _) =>
      if nondep && generalizeNondepLet then
        handleCDecl n ty .default
      else if !usedLetOnly || b.hasLooseBVar 0 then
        let ty  := ty.abstractRange i xs
        let val := val.abstractRange i xs
        mkLet n ty val b nondep
      else
        b.lowerLooseBVars 1 1
    | none => panic! "unknown free variable"

def mkLambda (lctx : LocalContext) (xs : Array Expr) (b : Expr) (usedLetOnly : Bool := true)
    (generalizeNondepLet := false) : Expr :=
  mkBinding true lctx xs b usedLetOnly generalizeNondepLet

def mkForall (lctx : LocalContext) (xs : Array Expr) (b : Expr) (usedLetOnly : Bool := true)
    (generalizeNondepLet := false) : Expr :=
  mkBinding false lctx xs b usedLetOnly generalizeNondepLet

/-- Convert to `Lean.LocalContext`, for the error-message payloads of `Lean.Kernel.Exception`
(whose constructors take the upstream type).  Only ever called on a failure path, so the
refinement proofs — which constrain only successful runs — never see it. -/
def toLean (lctx : LocalContext) : Lean.LocalContext :=
  lctx.decls.foldl (init := {}) fun l d => match d with
    | some d => l.addDecl d
    | none => l

/-- Convert from `Lean.LocalContext`; used only by the `TermElabM` lift, which is a development
convenience and is not reachable from `Lean4Lean.addDecl`. -/
def ofLean (lctx : Lean.LocalContext) : LocalContext := Id.run do
  let mut r : LocalContext := {}
  for d in lctx do
    r := { fvarIdToDecl := r.fvarIdToDecl.insert d.fvarId d, decls := r.decls.push (some d) }
  return r

end LocalContext

class MonadLCtx (m : Type → Type) where
  getLCtx : m LocalContext

/-- Not `export`ed: an alias would be ambiguous with `Lean.getLCtx` wherever `open Lean` is in
scope, whereas a real declaration in the `Lean4Lean` namespace takes priority over it. -/
@[inline] def getLCtx {m : Type → Type} [MonadLCtx m] : m LocalContext := MonadLCtx.getLCtx

instance [MonadLift m n] [MonadLCtx m] : MonadLCtx n where
  getLCtx := liftM (MonadLCtx.getLCtx : m _)

end Lean4Lean
