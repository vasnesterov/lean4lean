import Batteries.Data.List.Basic
import Lean4Lean.Environment.Basic
import Lean4Lean.TypeChecker

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

open private Lean.Kernel.Environment.add from Lean.Environment

/--
`anySubterm p e` is `true` iff some subterm of `e` satisfies `p`. "Subterm" here means `e`
itself together with, recursively, the immediate children of every node — so for an
application `f a b` the nodes `f a b`, `f a`, `f`, `a` and `b` are all tested.

This is a total, structurally recursive stand-in for `(e.find? p).isSome`.
`Lean.Expr.find?` is `Lean.Expr.findImpl?`, an `opaque` `@[extern "lean_find_expr"]`
constant with *no* Lean-side body, so nothing about its result can be established without
adding an interface axiom. Every use of it in this file consumes the result only through
`.isSome`, i.e. asks a purely existential question, and for that question the C traversal's
order, its short-circuiting and its pointer-identity cache are all invisible: `for_each_fn<true>`
(`~/lean4/src/kernel/for_each_fn.cpp`) visits exactly the node set enumerated above, and the
predicates used here are pure. So this walk returns the same `Bool` while depending on
nothing outside Lean. The C++ kernel's `has_ind_occ` asks the same existential question.

The traversal is delegated to `Lean.Expr.replaceNoCacheT` (`Lean4Lean/Expr.lean`), which is
exactly this structural walk: it applies its callback to a node, and descends into the node's
immediate children — the six recursive `Expr` constructors, an application's `f` and `a`
included — precisely when the callback declines. Reusing it rather than writing a fresh
recursion is deliberate: every recursive definition, structural or not, gets an
`f._unsafe_rec` companion for code generation, and `Verify/Guard.lean`'s check 3 counts those,
so a new walk would enlarge the frozen implementation-gap list. `replaceNoCacheT` is already
in the checker's cone and on that list, and unlike `findImpl?` it is ordinary total Lean whose
body can be unfolded in a proof.

The callback never rewrites anything: it returns `some s` only to prune (on a hit, and once a
hit has been recorded), and the returned expression is the input, so no rebuilding happens.
Like the C traversal minus its pointer cache, this is `O(tree size)` rather than `O(dag size)`.
-/
def anySubterm (p : Expr → Bool) (e : Expr) : Bool :=
  (Lean.Expr.replaceNoCacheT (m := StateM Bool) visit e |>.run false).2
where
  /-- `none` = descend into the children, `some s` = stop here (the answer is already `true`). -/
  visit (s : Expr) : StateM Bool (Option Expr) := do
    if ← get then return some s
    if p s then
      set true
      return some s
    return none

/--
One step of type-annotation stripping: `optParam α d ↦ α`, `autoParam α t ↦ α`,
`outParam α ↦ α`, `semiOutParam α ↦ α`, and anything else unchanged.

Matched on the application shape rather than through `Expr.appFn!`/`appArg!` so that it is
total with no `panic!` branch, and so that the over- and under-applied cases fall through to
`e` exactly as `Expr.isAppOfArity` makes them do in `isOptParam`/`isOutParam`.
-/
@[inline] def stripAnnotation : Expr → Expr
  | e@(.app (.app (.const n _) α) _) => if n == ``optParam || n == ``autoParam then α else e
  | e@(.app (.const n _) α) => if n == ``outParam || n == ``semiOutParam then α else e
  | e => e

/-- Whether `stripAnnotation` would do anything — the cheap guard that keeps the common case
(98% of constructor binder domains carry no annotation) to a single shallow match. -/
@[inline] def isAnnotation : Expr → Bool
  | .app (.app (.const n _) _) _ => n == ``optParam || n == ``autoParam
  | .app (.const n _) _ => n == ``outParam || n == ``semiOutParam
  | _ => false

/--
`Lean.Name.appendAfter` and `Lean.Name.appendIndexAfter`, without the opaque.

Both upstream functions build the new component with `String.Internal.append`
(`Init/Data/String/Bootstrap.lean`), which is `@[extern "lean_string_append"]` **`opaque`, with
no Lean body at all** -- exactly the shape of `Lean.Expr.findImpl?` and
`Lean.Expr.consumeTypeAnnotations` before `anySubterm` and `consumeAnnotations` replaced them,
and, like them, invisible to `Verify/Guard.lean`'s check 3, which filters to constants defined in
`Lean4Lean.*` modules. Nothing whatever can be said about the string it returns.

`String.append` (`Init/Data/String/Defs.lean`) is the same C function -- both carry
`@[extern "lean_string_append"]` -- but it is a `def` whose Lean body *is* its specification:

    def String.append (s : String) (t : @& String) : String where
      toByteArray := s.toByteArray ++ t.toByteArray
      isValidUTF8 := s.isValidUTF8.append t.isValidUTF8

So these two definitions are the upstream ones verbatim with `String.Internal.append` replaced
by `++`. They are checked against the upstream originals over a whole `Lean` environment by
`Lean4Lean/Tests/KernelHardening.lean` (2,066,550 name/suffix pairs, no disagreement), and the
structural check in the same file requires that no `Lean4Lean.*` constant reachable from
`addDecl` names the upstream pair any more.

**No new recursive definition.** Both are non-recursive: `Lean.Name.modifyBase` and
`toString` are upstream, so neither acquires an `f._unsafe_rec` companion and check 3's frozen
implementation-gap list is unchanged. That is the same constraint `anySubterm` and
`consumeAnnotations` were designed around.

**Not called `Name.appendAfter`.** Dot notation on a `Name` would resolve back to the upstream
function, silently undoing the replacement, so these are plain `Lean4Lean` functions used in
prefix position.
-/
def appendAfter' (n : Name) (suffix : String) : Name :=
  n.modifyBase fun
    | .str p s => .str p (s ++ suffix)
    | n        => .str n suffix

@[inherit_doc appendAfter']
def appendIndexAfter' (n : Name) (idx : Nat) : Name :=
  n.modifyBase fun
    | .str p s => .str p (s ++ "_" ++ toString idx)
    | n        => .str n ("_" ++ toString idx)

namespace AddInductive
open TypeChecker

structure RecInfo where
  motive : Expr
  minors : Array Expr
  indices : Array Expr
  major : Expr
  deriving Inhabited

structure InductiveStats where
  lctx : LocalContext := {}
  levels : List Level
  resultLevel : Level
  nindices : Array Nat := #[]
  indConsts : Array Expr
  params : Array Expr
  isNotZero : Bool
  deriving Inhabited

structure Context where
  env : Environment
  lctx : LocalContext := {}
  lparams : List Name
  ngen : NameGenerator := { namePrefix := `_ind_fresh }
  safety : DefinitionSafety
  allowPrimitive : Bool
  fuel : FuelConfig := {}

abbrev M := ReaderT Context <| Except Exception

/--
`Lean.Expr.consumeTypeAnnotations`, without the opaque.

Both kernels record the annotation-stripped domain as a binder's local-context type -- the C++
kernel at `src/kernel/inductive.cpp:222,227`, lean4lean at the thirteen `withLocalDecl` sites
below -- so the call cannot simply be dropped; that would be a real divergence.

But `Lean.Expr.consumeTypeAnnotations` is `partial`, hence an `opaque` **with no Lean body at
all**, like `Lean.Expr.findImpl?` before `anySubterm` replaced it. Nothing can be proved about
its result, and it is invisible to `Verify/Guard.lean`'s check 3, which filters to constants
defined in `Lean4Lean.*` modules. It reached eleven distinct binder-introducing loops here --
`checkInductiveTypes`, `checkConstructors`, `checkPositivity`, `isRecArg`, `isLargeEliminator`
and all six of `mkRecInfos` -- so every abstract local context the inductive adder builds was
resting on it. `Verify/Inductive/Add.lean`'s `M.WF.elim_loop` carries the resulting hypothesis
`hcta`, which is false on ~2% of the constructors of a real environment.

**No new recursive definition.** `stripAnnotation` and `isAnnotation` are non-recursive and the
iteration is `Nat.repeat`, which is upstream; a fresh structural recursion here would acquire an
`_unsafe_rec` companion and enlarge check 3's frozen list, which is the same constraint that
made `anySubterm` delegate to `Expr.replaceNoCacheT` rather than walk on its own.

**Exhaustion rejects rather than returning a half-stripped term.** `stripAnnotation` is the
identity at its fixpoint, so `Nat.repeat` past the fixpoint is harmless; what the bound rules
out is annotation nesting deeper than `inductiveFuel`. Returning a partially stripped type
would put a merely *definitionally* correct type in the local context and silently change what
later `isDefEq` calls see; throwing is sound unconditionally and keeps the property the rest of
this file relies on, that more fuel only ever enlarges the accepted set.

Cost: the guard makes the common path one shallow match, the same test the C function makes
first. Only an actually-annotated domain enters the loop.
-/
def consumeAnnotations (e : Expr) : M Expr := fun c =>
  if isAnnotation e then
    if isAnnotation (Nat.repeat stripAnnotation c.fuel.inductiveFuel e) then
      .error .deepRecursion
    else .ok (Nat.repeat stripAnnotation c.fuel.inductiveFuel e)
  else .ok e

instance : MonadLocalNameGenerator M where
  withFreshId f c := f c.ngen.curr { c with ngen := c.ngen.next }

instance (priority := low) : MonadLift TypeChecker.M M where
  monadLift x c := x.run c.env c.safety c.lctx c.lparams (fuel := c.fuel)

instance (priority := low+1) : MonadWithReaderOf LocalContext M where
  withReader f x := withReader (fun c => { c with lctx := f c.lctx }) x

instance : MonadLCtx M where
  getLCtx := return (← read).lctx

@[inline] def withEnv (env : Environment) (x : M α) : M α :=
  withReader (fun c => { c with env }) x

def getType (fvar : Expr) : M Expr :=
  return ((← getLCtx).get! fvar.fvarId!).type

def checkInductiveTypes
    (nparams : Nat) (indTypes : Array InductiveType)
    (k : InductiveStats → M α) : M α := do
  let rec loopInd dIdx stats : M α := do
    if _h : dIdx < indTypes.size then
      let indType := indTypes[dIdx]
      let env := (← read).env
      let type := indType.type
      env.checkNoMVarNoFVar indType.name type
      _ ← checkType type
      let rec loop stats type i nindices fuel k : M α := match fuel with
      | 0 => throw .deepRecursion
      | fuel+1 => do
        if let .forallE name dom body bi := type then
          if i < nparams then
            if stats.indConsts.isEmpty then
              let dom' ← consumeAnnotations dom
              withLocalDecl name bi dom' fun param => do
                let stats := { stats with params := stats.params.push param }
                let type := body.instantiate1 param
                loop stats (← whnf type) (i + 1) nindices fuel k
            else
              let param := stats.params[i]!
              unless ← isDefEq dom (← getType param) do
                throw <| .other "parameters of all inductive datatypes must match"
              let type := body.instantiate1 param
              loop stats (← whnf type) (i + 1) nindices fuel k
          else
            let dom' ← consumeAnnotations dom
            withLocalDecl name bi dom' fun arg => do
              let type := body.instantiate1 arg
              loop stats (← whnf type) i (nindices + 1) fuel k
        else
          if i != nparams then
            throw <| .other "number of parameters mismatch in inductive datatype declaration"
          k type stats nindices
      let fuel := (← readThe Context).fuel.inductiveFuel
      loop stats (← whnf type) 0 0 fuel fun type stats nindices => show M α from do
      let type ← ensureSort type
      let mut stats := stats
      let resultLevel := type.sortLevel!
      if stats.indConsts.isEmpty then
        let lctx := (← read).lctx
        stats := { stats with lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
      else if !resultLevel.isEquiv stats.resultLevel then
        throw <| .other "mutually inductive types must live in the same universe"
      stats := { stats with
        nindices := stats.nindices.push nindices
        indConsts := stats.indConsts.push (.const indType.name stats.levels) }
      loopInd (dIdx + 1) stats
    else
      k <|
        assert! stats.levels.length == (← read).lparams.length
        assert! stats.nindices.size == indTypes.size
        assert! stats.indConsts.size == indTypes.size
        assert! stats.params.size == nparams
        stats
  termination_by indTypes.size - dIdx
  loopInd 0 { (default : InductiveStats) with levels := (← read).lparams.map .param }

def hasIndOcc (indConsts : Array Expr) (t : Expr) : Bool :=
  anySubterm (fun
    | .const e _ => indConsts.any fun I => I.constName! == e
    | _ => false) t

/-- Return true if declaration is recursive -/
def isRec (indTypes : Array InductiveType) (indConsts : Array Expr) : Bool :=
  let rec loop
    | .forallE _ dom body _ => hasIndOcc indConsts dom || loop body
    | _ => false
  indTypes.any fun indType => indType.ctors.any fun ctor => loop ctor.type

/-- Return true if the given declaration is reflexive.

Remark: We say an inductive type `T` is reflexive if it
contains at least one constructor that takes as an argument a
function returning `T'` where `T'` is another inductive datatype (possibly equal to `T`)
in the same mutual declaration. -/
def isReflexive (indTypes : Array InductiveType) (indConsts : Array Expr) : Bool :=
  let rec loop
    | .forallE _ dom body _ => dom.isForall && hasIndOcc indConsts dom || loop body
    | _ => false
  indTypes.any fun indType => indType.ctors.any fun ctor => loop ctor.type

def declareInductiveTypes (stats : InductiveStats) (numParams : Nat)
    (indTypes : Array InductiveType) (numNested : Nat) (isUnsafe : Bool) : M Environment :=
  fun c =>
  let all := indTypes.map (·.name) |>.toList
  let infos := indTypes.zipWith (bs := stats.nindices) fun indType numIndices =>
    { indType with
      numParams, numIndices, all, numNested, isUnsafe
      levelParams := c.lparams
      ctors := indType.ctors.map (·.name)
      isRec := isRec indTypes stats.indConsts
      isReflexive := isReflexive indTypes stats.indConsts }
  infos.foldlM (init := c.env) fun env info => do
    env.checkName info.name c.allowPrimitive
    return env.add (.inductInfo info)

def isValidIndAppIdx (stats : InductiveStats) (t : Expr) (i : Nat) : Bool :=
  t.withApp fun I args => Id.run do
  unless I == stats.indConsts[i]! && args.size == stats.params.size + stats.nindices[i]! do
    return false
  for i in [:stats.params.size] do
    if stats.params[i]! != args[i]! then return false
  for i in [stats.params.size:args.size] do
    if hasIndOcc stats.indConsts args[i]! then return false
  true

def isValidIndApp? (stats : InductiveStats) (t : Expr) : Option Nat := do
  for i in [:stats.indConsts.size] do
    if isValidIndAppIdx stats t i then
      return i
  none

def isRecArg (stats : InductiveStats) (t : Expr) : M (Option Nat) := do
  loop t (← readThe Context).fuel.inductiveFuel
where
  loop t
  | 0 => throw .deepRecursion
  | fuel+1 => do
    let t ← whnf t
    let .forallE name dom body bi := t | return isValidIndApp? stats t
    let dom' ← consumeAnnotations dom
    withLocalDecl name bi dom' fun arg => do
    loop (body.instantiate1 arg) fuel

def checkPositivity (stats : InductiveStats) (t : Expr) (ctor : Name) (idx : Nat) :
    M Unit := do loop t (← readThe Context).fuel.inductiveFuel where
  loop t
  | 0 => throw .deepRecursion
  | fuel+1 => do
    let t ← whnf t
    if !hasIndOcc stats.indConsts t then return
    if let .forallE name dom body bi := t then
      if hasIndOcc stats.indConsts dom then
        throw <| .other s!"arg #{idx + 1} of '{ctor}' \
          has a non positive occurrence of the datatypes being declared"
      let dom' ← consumeAnnotations dom
      withLocalDecl name bi dom' fun arg => do
      loop (body.instantiate1 arg) fuel
    else if let none := isValidIndApp? stats t then
      throw <| .other s!"arg #{idx + 1} of '{ctor}' \
        has a non valid occurrence of the datatypes being declared"

def checkConstructors (indTypes : Array InductiveType)
    (stats : InductiveStats) (isUnsafe : Bool) : M Unit := do
  let env ← getEnv
  for h : idx in [:indTypes.size] do
    let indType := indTypes[idx]
    -- `List Name` rather than `NameSet`: a `NameSet` is an `RBTree` ordered by
    -- `Lean.Name.quickCmp`, whose *executed* path is `@[implemented_by quickCmpImpl]` and thence
    -- the body-less opaque `quickCmpImpl.unsafe_impl_2` (a pointer-equality fast path).  Unlike
    -- a hash lookup, a tree lookup is not re-confirmed by an equality test, so a comparison that
    -- wrongly reported `eq` would silently accept a duplicate constructor.  `List.contains` runs
    -- `Name.beq`, whose Lean body *is* its specification.  Quadratic in the constructor count;
    -- see `divergences.md`.
    let mut foundCtors : List Name := []
    for ctor in indType.ctors do
      let n := ctor.name
      if foundCtors.contains n then
        throw <| .other s!"duplicate constructor name '{n}'"
      foundCtors := n :: foundCtors
      let t := ctor.type
      env.checkNoMVarNoFVar n t
      _ ← checkType t
      let rec loop t i
      | 0 => throw .deepRecursion
      | fuel+1 => do
        if let .forallE name dom body bi := t then
          if let some param := stats.params[i]? then
            unless ← isDefEq dom (← getType param) do
              throw <| .other
                s!"arg #{i + 1} of '{n}' does not match inductive datatype parameters"
            loop (body.instantiate1 param) (i + 1) fuel
          else
            let s ← ensureType dom
            unless stats.resultLevel.isAlwaysZero || stats.resultLevel.geq' s.sortLevel! do
              throw <| .other s!"universe level of type_of(arg #{i + 1}) of '{n}' \
                is too big for the corresponding inductive datatype"
            if !isUnsafe then
              checkPositivity stats dom n i
            let dom' ← consumeAnnotations dom
            withLocalDecl name bi dom' fun arg => do
              loop (body.instantiate1 arg) (i + 1) fuel
        else if !isValidIndAppIdx stats t idx then
          throw <| .other s!"invalid return type for '{n}'"
      loop t 0 (← readThe Context).fuel.inductiveFuel

def declareConstructors (stats : InductiveStats)
    (indTypes : Array InductiveType) (isUnsafe : Bool) : M Environment :=
  fun c => indTypes.foldlM (init := c.env) fun env indType => do
    let (_, env) ← indType.ctors.foldlM (init := (0, env)) fun (cidx, env) ctor => do
      let type := ctor.type
      let rec arity i
        | .forallE _ _ body _ => arity (i+1) body
        | _ => i
      let arity := arity 0 type
      env.checkName ctor.name c.allowPrimitive
      pure (cidx + 1, env.add <| .ctorInfo {
        type, cidx, isUnsafe
        levelParams := c.lparams
        name := ctor.name
        induct := indType.name
        numParams := stats.params.size
        numFields := assert! arity ≥ stats.params.size; arity - stats.params.size
      })
    pure env

/-- Return true if recursor can map into any universe -/
def isLargeEliminator (stats : InductiveStats) (indTypes : Array InductiveType) : M Bool := do
  if stats.isNotZero then return true
  let #[indType] := indTypes | return false
  match indType.ctors with
  | [] => return true
  | [ctor] =>
    let rec loop type i toCheck
    | 0 => throw .deepRecursion
    | fuel+1 => do
      if let .forallE name dom body bi := type then
        let dom' ← consumeAnnotations dom
        withLocalDecl name bi dom' fun arg => do
          let mut toCheck := toCheck
          if i ≥ stats.params.size then
            if !(← ensureType dom).sortLevel!.isAlwaysZero then
              toCheck := toCheck.push arg
          loop (body.instantiate1 arg) (i + 1) toCheck fuel
      else
        return toCheck.all type.getAppArgs.contains
    loop ctor.type 0 #[] (← readThe Context).fuel.inductiveFuel
  | _ => return false

/-- The recursor's elimination universe: `.zero` for a small eliminator, otherwise the first
of `u`, `u_1`, `u_2`, … that is not already a level parameter of the declaration.

The search is *bounded* rather than left `partial`, so that the function has a body and
equation lemmas and can be reasoned about at all. The bound costs nothing: the candidates
`u`, `u_1`, `u_2`, … are pairwise distinct, so among any `lparams.length + 1` of them at
least one is absent from `lparams`, and the `0` case is unreachable. Freshness is exactly
what `docs/design-inductive.md` F10 rests on — `getRecLevelParams elimLevel lparams` must be
`u :: lparams` with `u ∉ lparams`. -/
def getElimLevel (stats : InductiveStats) (indTypes : Array InductiveType) :
    M Level := do
  unless ← isLargeEliminator stats indTypes do return .zero
  let {lparams, ..} ← read
  return .param (loop lparams `u 1 (lparams.length + 1))
where
  /-- The first of `u`, `u_i`, `u_(i+1)`, … that is not in `lps`. -/
  loop (lps : List Name) (u : Name) (i : Nat) : Nat → Name
    | 0 => u
    | fuel + 1 =>
      if lps.contains u then loop lps (appendIndexAfter' `u i) (i + 1) fuel else u

def isKTarget (stats : InductiveStats) (indTypes : Array InductiveType) : M Bool := do
  let #[indType] := indTypes | return false
  unless stats.resultLevel.isAlwaysZero do return false
  let [ctor] := indType.ctors | return false
  let rec loop i
    | .forallE _ _ body _ => i < stats.params.size && loop (i + 1) body
    | _ => true
  return loop 0 ctor.type

@[inline] def getIIndices (stats : InductiveStats) (t : Expr) : Nat × Array Expr :=
  ((isValidIndApp? stats t).get!, t.getAppArgs[stats.params.size:])

-- FIXME: The function below has been exploded into nested loops as standalone functions
-- because I couldn't get them all to compile together as `let rec`s.
namespace mkRecInfos

def loopArgs1 (stats : InductiveStats) (type : Expr) (i : Nat) (indices : Array Expr)
    (fuel : Nat) (k : Array Expr → M α) : M α := match fuel with
  | 0 => throw .deepRecursion
  | fuel+1 => do
    if let .forallE name dom body bi := type then
      if i < stats.params.size then
        loopArgs1 stats (← whnf <| body.instantiate1 stats.params[i]!) (i + 1) indices fuel k
      else
        let dom' ← consumeAnnotations dom
        withLocalDecl name bi dom' fun arg => do
        loopArgs1 stats (← whnf <| body.instantiate1 arg) i (indices.push arg) fuel k
    else
      k indices

variable (stats : InductiveStats) (indTypes : Array InductiveType) (elimLevel : Level) in
def loopInd1 (dIdx : Nat) (recInfos : Array RecInfo) (k : Array RecInfo → M α) : M α := do
  if _h : dIdx < indTypes.size then
    let ctx ← readThe Context
    loopArgs1 stats (← whnf indTypes[dIdx].type) 0 #[] ctx.fuel.inductiveFuel fun indices => do
    let tTy := mkAppN (mkAppN stats.indConsts[dIdx]! stats.params) indices
    let tTy' ← consumeAnnotations tTy
    withLocalDecl `t .default tTy' fun major => do
    let lctx ← getLCtx
    let motiveTy := lctx.mkForall indices <| lctx.mkForall #[major] <| .sort elimLevel
    let name := if indTypes.size > 1 then appendIndexAfter' `motive (dIdx+1) else `motive
    let motiveTy' ← consumeAnnotations motiveTy
    withLocalDecl name .default motiveTy' fun motive => do
    loopInd1 (dIdx + 1) (recInfos.push { motive, minors := #[], indices, major }) k
  else
    k recInfos
termination_by indTypes.size - dIdx

variable (stats : InductiveStats) in
def loopCtorArgs (t : Expr) (k : Expr → Array Expr → Array Expr → M α) : M α := do
  loop t 0 #[] #[] (← readThe Context).fuel.inductiveFuel
where
  loop t i bu u
  | 0 => throw .deepRecursion
  | fuel+1 => do
    if let .forallE name dom body bi := t then
      if let some param := stats.params[i]? then
        loop (body.instantiate1 param) (i + 1) bu u fuel
      else
        let dom' ← consumeAnnotations dom
        withLocalDecl name bi dom' fun arg => do
        let bu := bu.push arg
        let u := if (← isRecArg stats dom).isSome then u.push arg else u
        loop (body.instantiate1 arg) (i + 1) bu u fuel
    else k t bu u

def loopUArgs (ui : Expr) (k : Expr → Array Expr → M α) : M α := do
  loop (← whnf (← inferType ui)) #[] (← readThe Context).fuel.inductiveFuel
where
  loop uiTy xs
  | 0 => throw .deepRecursion
  | fuel+1 => do
    if let .forallE name dom body bi := uiTy then
      let dom' ← consumeAnnotations dom
      withLocalDecl name bi dom' fun arg => do
      loop (← whnf <| body.instantiate1 arg) (xs.push arg) fuel
    else
      k uiTy xs

variable (stats : InductiveStats) (u : Array Expr) (recInfos : Array RecInfo) in
def loopU (i : Nat) (v : Array Expr) (k : Array Expr → M α) : M α := do
  if _h : i < u.size then
    let ui := u[i]
    let viTy ← loopUArgs ui fun uiTy xs => do
      let (itIdx, itIndices) := getIIndices stats uiTy
      return (← getLCtx).mkForall xs <|
        .app (mkAppN recInfos[itIdx]!.motive itIndices) (mkAppN ui xs)
    let vName := appendAfter' ((← getLCtx).get! ui.fvarId!).userName "_ih"
    let viTy' ← consumeAnnotations viTy
    withLocalDecl vName .default viTy' fun vi => do
    loopU (i + 1) (v.push vi) k
  else
    k v
termination_by u.size - i

variable (stats : InductiveStats) (indTypeName : Name) (dIdx : Nat) in
def loopCtors (recInfos : Array RecInfo)
    (ctors : List Constructor) (k : Array RecInfo → M α) : M α := match ctors with
  | ctor::ctors =>
    loopCtorArgs stats ctor.type fun t bu u => do
    let (itIdx, itIndices) := getIIndices stats t
    let introApp := mkAppN (mkAppN (.const ctor.name stats.levels) stats.params) bu
    let motiveApp := Expr.app (mkAppN recInfos[itIdx]!.motive itIndices) introApp
    loopU stats u recInfos 0 #[] fun v => do
    let lctx ← getLCtx
    let minorTy := lctx.mkForall bu <| lctx.mkForall v motiveApp
    let minorName := ctor.name.replacePrefix indTypeName .anonymous
    let minorTy' ← consumeAnnotations minorTy
    withLocalDecl minorName .default minorTy' fun minor => do
    let recInfos := recInfos.modify dIdx fun s => { s with minors := s.minors.push minor }
    loopCtors recInfos ctors k
  | [] => k recInfos

variable (stats : InductiveStats) (indTypes : Array InductiveType) in
def loopInd2 (dIdx : Nat) (recInfos : Array RecInfo) (k : Array RecInfo → M α) : M α := do
  if _h : dIdx < indTypes.size then
    let indType := indTypes[dIdx]
    let indTypeName := indType.name
    loopCtors stats indTypeName dIdx recInfos indType.ctors fun recInfos =>
    loopInd2 (dIdx + 1) recInfos k
  else
    k recInfos
termination_by indTypes.size - dIdx

end mkRecInfos

def mkRecInfos (stats : InductiveStats) (indTypes : Array InductiveType)
    (elimLevel : Level) (k : Array RecInfo → M α) : M α :=
  mkRecInfos.loopInd1 stats indTypes elimLevel 0 #[] fun recInfos =>
  mkRecInfos.loopInd2 stats indTypes 0 recInfos k

def getRecLevels (elimLevel : Level) (levels : List Level) : List Level :=
  if elimLevel.isParam then elimLevel :: levels else levels

def getRecLevelParams (elimLevel : Level) (lparams : List Name) : List Name :=
  if let .param u := elimLevel then u :: lparams else lparams

def mkRecRules (indTypes : Array InductiveType) (elimLevel : Level) (stats : InductiveStats)
    (dIdx : Nat) (motives : Array Expr) (minors : Array Expr) :
    StateT Nat M (List RecursorRule) := do
  let d := indTypes[dIdx]!
  let lvls := getRecLevels elimLevel stats.levels
  let mut rules := #[]
  for ctor in d.ctors do
    let rule ← fun minorIdx => mkRecInfos.loopCtorArgs stats ctor.type fun _ bu u =>
      let rec loopU i (v : Array Expr) k := do
        if _h : i < u.size then
          let ui := u[i]
          let val ← mkRecInfos.loopUArgs ui fun uiTy xs => do
            let (itIdx, itIndices) := getIIndices stats uiTy
            let val := .const (mkRecName indTypes[itIdx]!.name) lvls
            let val := mkAppN (mkAppN (mkAppN (mkAppN val stats.params) motives) minors) itIndices
            return (← getLCtx).mkLambda xs <| val.app (mkAppN ui xs)
          loopU (i + 1) (v.push val) k
        else
          k v
      termination_by u.size - i
      loopU 0 #[] fun v => do
      let lctx ← getLCtx
      let rule := {
        ctor := ctor.name
        nfields := bu.size
        rhs := lctx.mkLambda stats.params <| lctx.mkLambda motives <|
          lctx.mkLambda minors <| lctx.mkLambda bu <|
          mkAppN (mkAppN minors[minorIdx]! bu) v
      }
      return (rule, minorIdx + 1)
    rules := rules.push rule
  return rules.toList

def run (nparams : Nat) (types : List InductiveType) (numNested : Nat) : M Environment := do
  let isUnsafe := (← read).safety != .safe
  let indTypes := types.toArray
  let {lparams, ..} ← read
  Environment.checkDuplicatedUnivParams lparams
  checkInductiveTypes nparams indTypes fun stats => do
  withEnv (← declareInductiveTypes stats nparams indTypes numNested isUnsafe) do
  checkConstructors indTypes stats isUnsafe
  withEnv (← declareConstructors stats indTypes isUnsafe) do
  let elimLevel ← getElimLevel stats indTypes
  let k ← isKTarget stats indTypes
  mkRecInfos stats indTypes elimLevel fun recInfos => do
  let motives := recInfos.map (·.motive)
  let minors := recInfos.flatMap (·.minors)
  let numMinors := minors.size
  let numMotives := motives.size
  let all := indTypes.map (·.name) |>.toList
  let lctx ← getLCtx
  let isUnsafe := (← read).safety != .safe
  StateT.run' (s := 0) do
  let mut env ← getEnv
  let {allowPrimitive, ..} ← read
  for h : dIdx in [:indTypes.size] do
    let indType := indTypes[dIdx]
    let info := recInfos[dIdx]!
    let ty :=
      lctx.mkForall stats.params <|
      lctx.mkForall motives <|
      lctx.mkForall minors <|
      lctx.mkForall info.indices <|
      lctx.mkForall #[info.major] <|
      .app (mkAppN info.motive info.indices) info.major
    let rules ← mkRecRules indTypes elimLevel stats dIdx motives minors
    let name := mkRecName indType.name
    env.checkName name allowPrimitive
    env := env.add <| .recInfo {
      levelParams := getRecLevelParams elimLevel lparams
      type := ty.inferImplicit 1000 false -- note: flag has reversed polarity from C++
      numParams := stats.params.size
      numIndices := stats.nindices[dIdx]!
      name, all, numMotives, numMinors, rules, k, isUnsafe
    }
  pure env

end AddInductive

namespace ElimNestedInductive

structure Result where
  ngen : NameGenerator
  nparams : Nat
  lctx : LocalContext
  params : Array Expr -- the fvars declared in `lctx`
  /-- Exprs are open over `params`, like the C++ `m_aux2nested`.  An association list rather
  than a `NameMap`, so that lookup runs `Name.beq` instead of `Name.quickCmp`, whose executed
  path is a body-less opaque; the keys are `mkUniqueName`'s output and so are distinct, and
  `List.lookup` returns the first match, which is the most recently pushed — the same
  last-write-wins semantics `NameMap.insert` has. -/
  aux2nested : List (Name × Expr)
  types : List InductiveType

instance [MonadStateOf NameGenerator m] : MonadNameGenerator m where
  getNGen := get
  setNGen := set

namespace Result

def getNestedIfAuxCtor (r : Result) (env' : Environment) (c : Name) : Option (Expr × Name) := do
  let .ctorInfo { induct, .. } ← env'.find? c | none
  return (← r.aux2nested.lookup induct, induct)

def restoreCtorName (r : Result) (env' : Environment) (c : Name) : Name := Id.run do
  let (e, name) := (r.getNestedIfAuxCtor env' c).get!
  let .const I _ := e.getAppFn | unreachable!
  c.replacePrefix name I

def restoreNested (r : Result) (env' : Environment) (e : Expr)
    (auxRec : List (Name × Name) := []) : Expr :=
  Id.run <| StateT.run' (s := { namePrefix := `_nested_fresh : NameGenerator }) do
  let pi := e.isForall
  let mut e := e
  let mut As := #[]
  let mut lctx : LocalContext := {}
  for _ in [:r.nparams] do
    match e with
    | .forallE name dom body bi | .lam name dom body bi =>
      let id := ⟨← mkFreshId⟩
      lctx := lctx.mkLocalDecl id name dom bi
      let arg := .fvar id
      e := body.instantiate1 arg
      As := As.push arg
    | _ => unreachable!
  -- `Expr.replaceNoCache`, not `Expr.replace`: the latter is `@[implemented_by]` an unsafe
  -- pointer-keyed cache.  See `divergences.md` § "nested-inductive replacement is uncached".
  e := e.replaceNoCache fun t => do
    if let .const c ls := t then
      if let some recName := auxRec.lookup c then
        return .const recName ls
    let .const c _ := t.getAppFn | none
    if let some nested := r.aux2nested.lookup c then
      let args := t.getAppArgs
      assert! args.size ≥ r.nparams
      return mkAppRange ((nested.abstract r.params).instantiateRev As) r.nparams args.size args
    let (nested, auxI_name) ← r.getNestedIfAuxCtor env' c
    let args := t.getAppArgs
    assert! args.size ≥ r.nparams
    let nested' := (nested.abstract r.params).instantiateRev As
    nested'.withApp fun I I_args => do
    let .const I_c I_ls := I | unreachable!
    let c' := .const (c.replacePrefix auxI_name I_c) I_ls
    return mkAppRange (mkAppN c' I_args) r.nparams args.size args
  return if pi then lctx.mkForall As e else lctx.mkLambda As e

end Result

structure State where
  ngen : NameGenerator := { namePrefix := `_nested_fresh }
  nestedAux : Array (Expr × Name) := {}
  lvls : List Level
  newTypes : Array InductiveType
  nextIdx : Nat := 1
  /-- Search bound for `mkUniqueName`, seeded by `run` from `FuelConfig.inductiveFuel`. -/
  fuel : Nat := 0
  deriving Inhabited

abbrev M := ReaderT Environment <| StateT State <| Except Exception

instance : MonadNameGenerator M where
  getNGen := return (← get).ngen
  setNGen ngen := modify fun s => { s with ngen }

/-- A name of the form `n_i` that the environment does not already use.

Bounded rather than `partial`, so that the function has a body and equation lemmas and can be
reasoned about at all. The bound is `FuelConfig.inductiveFuel`, the same counter every other
structural loop in this file uses, and exhaustion is a *rejection* (`.deepRecursion`) rather
than a silently colliding name — which keeps the property `Verify/Soundness.lean` relies on,
that more fuel only ever enlarges the accepted set. `nextIdx` still advances across calls, so
successive searches do not retry names this one rejected.

A count of the environment's constants would be the tight bound, but neither `SMap` nor
`PersistentHashMap` stores a size, so computing it would be `O(|env|)` per call. -/
def mkUniqueName (n : Name) : M Name := fun env s => loop env n s s.nextIdx s.fuel
where
  loop (env : Environment) (n : Name) (s : State) (i : Nat) :
      Nat → Except Exception (Name × State)
    | 0 => throw <| .other "deep recursion: ElimNestedInductive.mkUniqueName"
    | fuel + 1 =>
      let r := appendIndexAfter' n i
      if env.contains r then loop env n s (i + 1) fuel
      else pure (r, { s with nextIdx := i + 1 })

def illFormed : Exception :=
  .other "invalid nested inductive datatype, ill-formed declaration"

def replaceParams (params : Array Expr) (e : Expr) (As : Array Expr) : M Expr := do
  assert! As.size == params.size
  return (e.abstract As).instantiateRev params

/-- IF `e` is of the form `I Ds is` where
  1) `I` is a nested inductive datatype (i.e., a previously declared inductive datatype),
  2) the parametric arguments `Ds` do not contain loose bound variables, and do contain inductive datatypes in `m_new_types`
THEN return the `inductive_val` in the `constant_info` associated with `I`.
Otherwise, return none. -/
def isNestedInductiveApp? (e : Expr) : M (Option InductiveVal) := do
  if !e.isApp then return none
  let .const fn _ := e.getAppFn | return none
  let env ← read
  let some (.inductInfo ci) := env.find? fn | return none
  let args := e.getAppArgs
  if ci.numParams > args.size then return none
  let mut isNested := false
  let mut looseBVars := false
  for i in [0:ci.numParams] do
    if args[i]!.hasLooseBVars then
      looseBVars := true
    let newTypes := (← get).newTypes
    if anySubterm (fun
      | .const t _ => newTypes.any fun ty => t == ty.name
      | _ => false) args[i]!
    then
      isNested := true
  if !isNested then return none
  if looseBVars then
    throw <| .other s!"invalid nested inductive datatype '{fn}', \
      nested inductive datatypes parameters cannot contain local variables."
  return some ci

def instantiateForallParams (e : Expr) (hi : Nat) (params : Array Expr) :
    Except Exception Expr := do
  let mut e := e
  for _ in [:hi] do
    let .forallE _ _ body _ := e | throw illFormed
    e := body
  return e.instantiateRevRange 0 hi params

/-- If `e` is a nested occurrence `I Ds is`, return `Iaux As is` -/
def replaceIfNested (lctx : LocalContext) (params : Array Expr) (As : Array Expr) (e : Expr) :
    M (Option Expr) := do
  let some I_val ← isNestedInductiveApp? e | return none
  e.withApp fun fn args => do
  let .const I_name I_lvls := fn | unreachable!
  let I_nparams := I_val.numParams
  assert! I_nparams ≤ args.size
  let IAs := mkAppRange fn 0 I_nparams args -- `I As`
  let Iparams ← replaceParams params IAs As
  let st ← get
  if let some auxI_name := st.nestedAux.findSome? fun (e, n) =>
    if e == Iparams then some n else none
  then
    return mkAppRange (mkAppN (.const auxI_name st.lvls) As) I_nparams args.size args
  let mut result := none
  let env ← read
  for J_name in I_val.all do
    let .inductInfo J_info ← env.get J_name | unreachable!
    let J := .const J_name I_lvls
    let JAs := mkAppRange J 0 I_nparams args
    let auxJ_name ← mkUniqueName (`_nested ++ J_name)
    let auxJ_type := J_info.type.instantiateLevelParamsNoCache J_info.levelParams I_lvls
    let auxJ_type := lctx.mkForall As <| ← instantiateForallParams auxJ_type I_nparams args
    let JAs' ← replaceParams params JAs As
    modify fun st => { st with nestedAux := st.nestedAux.push (JAs', auxJ_name) }
    if J_name == I_name then
      result := some <|
        mkAppRange (mkAppN (.const auxJ_name (← get).lvls) As) I_nparams args.size args
    let auxJ_ctors ← J_info.ctors.mapM fun J_ctor_name => do
      let J_ctor_info ← env.get J_ctor_name
      -- auxJ_cnstr_type still has references to `J`, this will be fixed later when we process it.
      let auxJ_ctor_name := J_ctor_name.replacePrefix J_name auxJ_name
      let auxJ_ctor_type :=
        J_ctor_info.type.instantiateLevelParamsNoCache J_ctor_info.levelParams I_lvls
      let auxJ_ctor_type ← instantiateForallParams auxJ_ctor_type I_nparams args
      return { name := auxJ_ctor_name, type := lctx.mkForall As auxJ_ctor_type }
    let newType := { name := auxJ_name, type := auxJ_type, ctors := auxJ_ctors }
    modify fun st => { st with newTypes := st.newTypes.push newType }
  assert! result.isSome
  return result

def replaceAllNested (lctx : LocalContext) (params : Array Expr) (As : Array Expr) (e : Expr) :
    M Expr := e.replaceNoCacheT (replaceIfNested lctx params As)

def withParams (type : Expr) (nparams : Nat)
    (k : LocalContext → Expr → Array Expr → M α) : M α := loop {} type #[] nparams where
  loop lctx type params
  | 0 => k lctx type params
  | i+1 => do
    let .forallE name dom body bi := type
      | throw <| .other "invalid inductive datatype declaration, incorrect number of parameters"
    let id := ⟨← mkFreshId⟩
    let lctx := lctx.mkLocalDecl id name dom bi
    let arg := .fvar id
    loop lctx (body.instantiate1 arg) (params.push arg) i

def run (fuel nparams : Nat) (types : List InductiveType) : M Result := do
  let I :: _ := types
    | throw <| .other s!"invalid empty (mutual) inductive datatype declaration, \
        it must contain at least one inductive type."
  modify fun s => { s with fuel }
  withParams I.type nparams fun lctx _ params => do
  let rec loop i
  | 0 => throw <| .other "deep recursion: ElimNestedInductive.run.loop"
  | fuel+1 => do
    let s ← get
    if _h : i < s.newTypes.size then
      let indType := s.newTypes[i]
      let ctors ← indType.ctors.mapM fun ctor => do
        withParams ctor.type nparams fun lctx ctorType As => do
        assert! As.size == nparams
        return { ctor with type := lctx.mkForall As (← replaceAllNested lctx params As ctorType) }
      modify fun s => { s with newTypes := s.newTypes.set! i { indType with ctors } }
      loop (i+1) fuel
    else
      let aux2nested := s.nestedAux.foldl (fun m (e, n) => (n, e) :: m) []
      return { s with nparams := params.size, lctx, params, aux2nested, types := s.newTypes.toList }
  loop 0 fuel
end ElimNestedInductive

def mkAuxRecNameMap (env' : Environment) (types : List InductiveType) :
    List Name × List (Name × Name) := Id.run do
  let mainType :: _ := types | unreachable!
  let ntypes := types.length
  let mainName := mainType.name
  let some (.inductInfo mainInfo) := env'.find? mainName | unreachable!
  let allNames := mainInfo.all
  assert! allNames.length > ntypes
  let mut oldRecNames := #[]
  let mut recMap : List (Name × Name) := []
  let mut nextIdx := 1
  for indName in allNames.drop ntypes do
    let oldRecName := mkRecName indName
    let newRecName := appendIndexAfter' (mkRecName mainName) nextIdx
    nextIdx := nextIdx + 1
    recMap := (oldRecName, newRecName) :: recMap
    oldRecNames := oldRecNames.push oldRecName
  return (oldRecNames.toList, recMap)

/--
`noLooseBVars d e` is `true` when every `Expr.bvar` in `e` is bound within `e` itself, given
that `e` sits under `d` enclosing binders.

A pure structural recursion, deliberately *not* routed through `Expr.looseBVarRange`: that is a
cached 20-bit header field, so reading it would put `Lean.Expr.mkData_eq`'s side condition in the
way of every consequence. This function needs no axiom at all.
-/
def noLooseBVars (d : Nat) : Expr → Bool
  | .bvar i => i < d
  | .app f a => noLooseBVars d f && noLooseBVars d a
  | .lam _ t b _ => noLooseBVars d t && noLooseBVars (d + 1) b
  | .forallE _ t b _ => noLooseBVars d t && noLooseBVars (d + 1) b
  | .letE _ t v b _ => noLooseBVars d t && noLooseBVars d v && noLooseBVars (d + 1) b
  | .mdata _ e => noLooseBVars d e
  | .proj _ _ e => noLooseBVars d e
  | .fvar .. | .mvar .. | .sort .. | .const .. | .lit .. => true

/--
Reject a declaration whose type carries a **loose** bound variable.

**This is a divergence from the C++ kernel, in the restrictive direction — see
`divergences.md`.** C++ accepts such a declaration and *silently reinterprets it*:
`elim_nested_inductive_fn` round-trips every constructor type through `get_params` and
`lctx.mk_pi`, and `abstract` rewrites only `fvar`/`mvar` nodes, so a loose bvar whose index is
small enough gets **captured** by a parameter binder and the stored constructor type is not the
one written. `Lean4Lean/Verify/Inductive/RunIdentity.lean` exhibits the witness and proves that
the specification — that the resulting environment realises a translation of the *submitted*
declaration — is **false** without this check.

Rejecting is the cheaper of the two repairs: the alternative is a closedness *premise*, which
`Lean4Lean/Verify/ClosednessPropagation.lean` measures as reaching `kernel_sound`'s frozen
statement and therefore narrowing it. A top-level `Expr` with a loose bvar is not a term of the
type theory and no elaborator emits one, so nothing legitimate is refused.
-/
def checkNoLooseBVars (n : Name) (e : Expr) : Except Exception Unit := do
  unless noLooseBVars 0 e do
    throw <| .other s!"invalid declaration '{n}', it contains a loose bound variable"

/-!
### The uniform-occurrence pre-pass

`~/lean4/src/kernel/inductive.cpp`'s `check_uniform_ind_occs`, which
`environment::add_inductive` runs immediately before nested elimination — exactly where this
guard loop sits — and which lean4lean lacked, so it **accepted a declaration C++ rejects**
(`nested-nonuniform-param` in the Kernel Arena, graded `either`).

Upstream's own comment says why the check exists: *later phases inspect the constructor types
modulo `whnf`, which can erase an occurrence*. So the soundness-relevant half of the
whnf-versus-syntax gap is closed **syntactically**, before any reduction happens.

Two things this transcription gets right and a naive reading does not.

* **The visitor prunes.** C++ walks with `for_each_offset_fn` and returns `false` on success. Read
  without that, "every occurrence applied to at most `nparams` arguments must be applied to
  exactly `nparams`" is *unsatisfiable* whenever `nparams ≥ 1` — `I p₀ … p_{n-1}` contains
  `I p₀ … p_{n-2}` — and would reject `List`. See `uio_naive_too_strong` in
  `Verify/Inductive/UniformOccMeasure.lean`.
* **An over-applied occurrence imposes nothing itself**; the demand falls on its `nparams`-prefix,
  which is visited as a subterm. C++'s comment: *"so that occurrences in the indices are checked
  too"*.

The predicate coincides with `VInductDecl'.uniformOcc?`, the trigger of the abstract restoration
operator (`Theory/Inductive/Restore.lean`) — proved, on the nodes C++ checks, as
`uio_uniformOcc_iff`. `Verify/Inductive/UniformOccMeasure.lean` holds the specification `uioOk`,
the exactness pair (`uioOk_iff` and `uio_ok_of_occ`, the latter ruling out a
reject-everything check), and the scans: **0 of 7013** submitted constructors and **0 of 7215**
post-elimination.
-/

/-- Argument count of an application spine. -/
def spineNArgs : Expr → Nat
  | .app f _ => spineNArgs f + 1
  | _ => 0

/-- Head of an application spine. -/
def spineHead : Expr → Expr
  | .app f _ => spineHead f
  | e => e

/-- C++'s `is_bvar(args[i], offset - 1 - i)`, written `j + 1 + i == d` so no truncated
subtraction is involved; it entails `i < d`, which subsumes C++'s separate `offset >= nparams`
conjunct. -/
def isParamArg (d i : Nat) : Expr → Bool
  | .bvar j => j + 1 + i == d
  | _ => false

/-- Every argument of the spine is the parameter bvar its position demands. -/
def spineParamArgs (d : Nat) : Expr → Bool
  | .app f a => spineParamArgs d f && isParamArg d (spineNArgs f) a
  | _ => true

/-- `us` is the block's own level list, i.e. `lps.map Level.param`.

Deliberately **not** `us == lps.map .param`: `Lean.Level.beq` is `@[extern] opaque`, so that
comparison is usable only through the frozen axiom `Lean.Level.instLawfulBEqLevel`. Matching
`.param` and comparing `Name`s keeps this check — and its exactness lemma — free of every frozen
axiom, the same trade `noLooseBVars` makes against `Expr.mkData_eq`. -/
def ownLevels : List Name → List Level → Bool
  | [], [] => true
  | p :: ps, .param q :: us => p == q && ownLevels ps us
  | _, _ => false

/-- `noNonUniformOcc names lps np d e` is `true` when every occurrence in `e` of a member of the
block being declared is applied to exactly `np` arguments, at the block's own levels, with those
arguments the parameter bound variables — `d` being the binder depth (C++'s `offset`) at which
`e` sits. -/
def noNonUniformOcc (names : List Name) (lps : List Name) (np : Nat) : Nat → Expr → Bool
  | _, .bvar _ | _, .fvar _ | _, .mvar _ | _, .sort _ | _, .lit _ => true
  | _, .const c us => !names.contains c || (np == 0 && ownLevels lps us)
  | d, .mdata _ e => noNonUniformOcc names lps np d e
  | d, .proj _ _ e => noNonUniformOcc names lps np d e
  | d, .lam _ t b _ => noNonUniformOcc names lps np d t && noNonUniformOcc names lps np (d + 1) b
  | d, .forallE _ t b _ =>
    noNonUniformOcc names lps np d t && noNonUniformOcc names lps np (d + 1) b
  | d, .letE _ t v b _ =>
    noNonUniformOcc names lps np d t && noNonUniformOcc names lps np d v
      && noNonUniformOcc names lps np (d + 1) b
  | d, .app f a =>
    match spineHead (.app f a) with
    | .const c us =>
      if names.contains c && !decide (np < spineNArgs (.app f a)) then
        spineNArgs (.app f a) == np && spineParamArgs d (.app f a) && ownLevels lps us
      else noNonUniformOcc names lps np d f && noNonUniformOcc names lps np d a
    | _ => noNonUniformOcc names lps np d f && noNonUniformOcc names lps np d a

/-- Reject a constructor type in which a member of the block being declared occurs
non-uniformly. See the section comment above; C++ names the offending datatype where this names
the constructor, which is a wording difference only — the Kernel Arena grades accept/reject, not
`stderr`. -/
def checkUniformIndOccs (names : List Name) (lps : List Name) (np : Nat) (n : Name) (e : Expr) :
    Except Exception Unit := do
  unless noNonUniformOcc names lps np 0 e do
    throw <| .other s!"invalid occurrence of a datatype being declared in '{n}': it must be \
      applied to the parameters and universe levels of the mutual declaration"

def checkNoNestedAux (n : Name) (e : Expr) : Except Exception Unit := do
  if anySubterm (fun
      | .const c _ => (`_nested).isPrefixOf c
      | .proj s _ _ => (`_nested).isPrefixOf s
      | _ => false) e then
    throw <| .other s!"invalid declaration '{n}', it uses the reserved prefix '_nested'"

/--
Reject a declaration whose **own name** carries the reserved `_nested` prefix.

**This is a divergence from the C++ kernel, in the restrictive direction -- see
`divergences.md`.** Neither kernel checks this today: `checkNoNestedAux` above, and C++'s
`check_no_nested_aux` (`src/kernel/inductive.cpp`), scan a declaration's *type* for
`_nested`-prefixed constants, and in both the name argument is used only in the error message.
`Lean.isReservedName` does not catch it either -- it is a registry, and nothing in the Lean 4
tree registers `_nested`. So `inductive _nested.Foo` is accepted by both kernels today.

Why it matters. The nested-inductive pass rewrites a block, replacing each nested occurrence with
an auxiliary member it *invents*, checks the rewritten block, then restores the original names.
The `_nested` prefix is how the restoration tells invented names from declared ones. Because the
prefix is not an invariant of the environment, it cannot be used as a name barrier.

**Updated 2026-09-03, and the second half of this paragraph is now false.**  The two restoration
facts `RestoreData.ownName`/`ownCtor` (`Verify/Inductive/NestedRestore.lean`) are **no longer
hypotheses**: acceptance by `Environment.addInductive` implies the gate condition
(`addInductive_WF_noNestedDeclNames`, `Verify/Inductive/RestoreFaithful.lean`), which discharges
both, and `RestoreData.auxRec` follows from the gate alone.  The first half stands: the prefix is
**STALE, corrected 2026-09-04 -- PR #46 (`7e39484`) falsified every sentence of what this paragraph
used to say.**  It read: *"the prefix is still not an environment-wide invariant, because this check
guards only the inductive branch -- `axiom _nested.zzz` and `def _nested.ddd` are still accepted,
machine-checked by a `#eval` in `RestoreFaithful.lean` that fails the build if that changes.  Extending
it to every declaration is one line and a wider divergence from C++; it is costed in
`docs/decision-nested-prefix-all-decls.md` and awaiting a human decision."*

All of it is now false.  The human decision was taken (approved on PR #46), the one line is in
`checkConstantVal` (`Lean4Lean/Environment.lean`), so **prefixed axioms and definitions are REJECTED**
-- and the `#eval` this paragraph cites **fired on the merge and now asserts the opposite**, having been
written as a tripwire for exactly this change.  The prefix **is** an environment-wide invariant:
`Verify/Inductive/NoNestedAll.lean` establishes `VEnv.NoNestedN` across every `addDecl` branch
(`VEnv.NoNestedN.of_addDecl`), and `noNestedEnv_not_preserved_unchecked` shows it fails with
`check := false`, so the check is load-bearing.  Two residuals remain, both named there:
`MutualNamesGate` (the header loop, unproved not false) and `InductiveMapGate` (the map side of the
inductive step).  The divergence itself is recorded in `divergences.md`.

No exploit is claimed, and two mitigations may close every path: `mkUniqueName` skips names the
environment already holds, and the renamed recursors end in `rec_k`, never `rec`. There is a
machine-checked case (`Verify/Inductive/NestedOccData.lean`) where a user name collides with an
invented one and **both kernels reject it identically**, via the duplicate-constant check. What is
certain is narrower: nothing in the implementation establishes what the proof needs.
**Superseded**: as of PR #45 it does, for the inductive branch -- see the update above.
-/
def checkNoNestedAuxName (n : Name) : Except Exception Unit := do
  if (`_nested).isPrefixOf n then
    throw <| .other
      s!"invalid declaration '{n}', its name uses the reserved prefix '_nested'"

def Environment.addInductive (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe allowPrimitive : Bool) (fuel : FuelConfig := {}) :
    Except Exception Environment := do
  for indType in types do
    env.checkNoMVarNoFVar indType.name indType.type
    -- C++ applies the reserved-prefix test to the member's OWN type as well as to each
    -- constructor's (`inductive.cpp`, `environment::add_inductive`, the two
    -- `check_no_nested_aux` calls).  This line was missing, so lean4lean accepted at the gate a
    -- member whose own type mentions a `_nested` constant, where C++ rejects it -- verified by
    -- a self-checking `#eval` in `Verify/Inductive/NestedOccData.lean`.
    checkNoNestedAux indType.name indType.type
    -- The declaration's OWN name, which neither kernel checks.  A divergence in the
    -- restrictive direction; see `checkNoNestedAuxName` and `divergences.md`.
    checkNoNestedAuxName indType.name
    checkNoLooseBVars indType.name indType.type
    for ctor in indType.ctors do
      env.checkNoMVarNoFVar ctor.name ctor.type
      checkNoNestedAux ctor.name ctor.type
      checkNoNestedAuxName ctor.name
      checkNoLooseBVars ctor.name ctor.type
      checkUniformIndOccs (types.map (·.name)) lparams nparams ctor.name ctor.type
  let res ← ElimNestedInductive.run fuel.inductiveFuel nparams types env
    |>.run' { lvls := lparams.map .param, newTypes := types.toArray }
  -- `nestedAux`'s names are `mkUniqueName`'s output, hence pairwise distinct, so the list's
  -- length is the number of distinct keys a `NameMap` would have held.
  let numNested := res.aux2nested.length
  let safety := if isUnsafe then .unsafe else .safe
  let env' ← AddInductive.run nparams res.types numNested
    { env, allowPrimitive, lparams, fuel, safety }
  if numNested = 0 then return env'
  let allIndNames := types.map (·.name)
  let (recNames', recNameMap') := mkAuxRecNameMap env' types
  (·.2) <$> StateT.run (s := env) do
  let processRec recName := do
    let newRecName := (recNameMap'.lookup recName).getD recName
    let some (.recInfo recInfo) := env'.find? recName | unreachable!
    let newRecType := res.restoreNested env' recInfo.type recNameMap'
    let newRules ← recInfo.rules.mapM fun rule => do
      let newRhs := res.restoreNested env' rule.rhs recNameMap'
      let newCtorName := if newRecName == recName then rule.ctor else
        res.restoreCtorName env' rule.ctor
      return { rule with ctor := newCtorName, rhs := newRhs }
    (← MonadState.get).checkName newRecName allowPrimitive
    modify (·.add <| .recInfo { recInfo with
      name := newRecName, type := newRecType, all := allIndNames, rules := newRules })
  for indType in types do
    let some (.inductInfo ind) := env'.find? indType.name | unreachable!
    (← get).checkName ind.name allowPrimitive
    modify (·.add <| .inductInfo { ind with all := allIndNames })
    for ctorName in ind.ctors do
      let some (.ctorInfo ctor) := env'.find? ctorName | unreachable!
      let newType := res.restoreNested env' ctor.type
      (← get).checkName ctor.name allowPrimitive
      modify (·.add <| .ctorInfo { ctor with type := newType })
    processRec (mkRecName indType.name)
  recNames'.forM processRec
  -- Type check the nested applications `I Ds` that were replaced by auxiliary types: the
  -- parametric arguments `Ds` do not appear in the auxiliary declaration, so they would
  -- otherwise escape checking (lean4#14576/#14577).  Checked against the *final* environment,
  -- so no auxiliary declaration is in scope.  Mirrors `src/kernel/inductive.cpp:1317-1324`.
  TypeChecker.M.run (← get) (safety := safety) (lctx := res.lctx)
      (lparams := lparams) (fuel := fuel) do
    res.aux2nested.forM fun (_, e) => do _ ← TypeChecker.checkType e
  -- Re-check everything `restoreNested` rewrote: the constructor types, and the recursor types
  -- and computation rules.  Those terms are rewritten *after* the auxiliary block was checked
  -- and are not otherwise checked in the final environment; the inductive types themselves are
  -- added unchanged and need no check.  Upstream expects the preceding checks to make this
  -- redundant and keeps it anyway, to stop a mistake in the restoration from reaching the
  -- environment -- `src/kernel/inductive.cpp:1325-1346`, which lean4lean was missing.
  let final ← get
  let mut recNames : Array Name := #[]
  for indType in types do
    let r := mkRecName indType.name
    recNames := recNames.push ((recNameMap'.lookup r).getD r)
  for recName in recNames' do
    recNames := recNames.push ((recNameMap'.lookup recName).getD recName)
  TypeChecker.M.run final (safety := safety) (lctx := {}) (lparams := lparams) (fuel := fuel) do
    for indType in types do
      let some (.inductInfo ind) := final.find? indType.name | unreachable!
      for ctorName in ind.ctors do
        let some (.ctorInfo ctor) := final.find? ctorName | unreachable!
        _ ← TypeChecker.checkType ctor.type
  for recName in recNames do
    let some (.recInfo recInfo) := final.find? recName | unreachable!
    TypeChecker.M.run final (safety := safety) (lctx := {}) (lparams := recInfo.levelParams)
        (fuel := fuel) do
      _ ← TypeChecker.checkType recInfo.type
      for rule in recInfo.rules do
        _ ← TypeChecker.checkType rule.rhs
