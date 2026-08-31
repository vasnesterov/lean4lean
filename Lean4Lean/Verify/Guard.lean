import Lean4Lean.Verify.Soundness
import Lean4Lean.Verify.Axioms

/-!
# Build-time guard checks for the soundness goal

This file mechanically enforces the guardrails stated in `CLAUDE.md`. It is
**frozen**: editing it — in particular extending either frozen list below —
requires human sign-off. The checks run during elaboration and fail the build
on violation; they are tests, not proofs, and nothing imports this file.

1. **Axiom freeze**: `Lean4Lean/Verify/Axioms.lean` declares exactly the **24**
   axioms of `frozenAxioms` below (32 at commit `20e2d14`). Every frozen axiom of
   this project is declared in that one file, which is what lets this check see
   all of them: it enumerates axioms by *defining module*.
2. **Axiom whitelist**: the axioms of `kernel_sound` are contained in
   {`propext`, `Classical.choice`, `Quot.sound`} ∪ those **24**
   (∪ {`sorryAx`} while the proof is in progress). The build fails the moment
   any other axiom enters the proof cone. The check reports whether `sorryAx`
   is still present; the goal is met only when it reports COMPLETE.
3. **No verified/executed divergence**: among the constants defined in this
   repo and reachable from the checker entry point `Lean4Lean.addDecl`
   (following `@[implemented_by]` targets and `partial` unsafe companions,
   i.e. the code that actually executes), the ones that are `partial`,
   `@[extern]`, or `@[implemented_by]` are contained in the frozen list
   below — the state at the time this guard was written. Removing entries
   (de-partialing the checker) is progress; adding any is forbidden without
   sign-off, because a new such attribute lets the compiled checker diverge
   from the function `kernel_sound` talks about.
-/

namespace Lean4Lean.Guard
open Lean

/-- The 24 axioms declared by `Lean4Lean/Verify/Axioms.lean` — check 1's
reference set, and exactly the axioms that file may declare. The three standard
axioms are *not* here; see `axiomWhitelist`.

Re-pinned from the 32 of commit `20e2d14`, with sign-off, as two bugs were
fixed: `Lean.Level.mkLevelIMaxCore_eq` was **removed** (its model carried a
disjunct upstream does not have, so the axiom proved `False`; it is now a
`rfl` theorem), and `Lean.PersistentArray.toList'_push` was **renamed** to
`Lean.PersistentArray.WF.toList'_push` when it acquired the well-formedness
hypothesis it was missing.

Re-pinned again from 31 to 29: `Std.TreeMap.all_eq_all_toList` and
`Std.TreeMap.any_eq_any_toList` are now proved from the upstream `DTreeMap`
lemmas (see `docs/axiom-audit.md` §8), so they were **removed** from this list.

Re-pinned again from 29 to 28: `Lean.Expr.liftLooseBVars_eq` was **deleted**. It
was false — `lean_expr_lift_loose_bvars` returns `e` unchanged when `s` or `d`
fails `lean_is_scalar`, while the model shifts — and an axiom-cone scan over
every `Lean4Lean.*` declaration found it had **0** dependents, so deleting it
was strictly better than adding a side condition. See `docs/axiom-audit.md`
§11.2.

Re-pinned again from 28 to 27: `Lean.Expr.looseBVarRange_eq` became a
**theorem**. It was derivable all along from `Expr.mkData_eq` and
`Expr.mkAppData_eq` under the `BVarBounded` side condition it already carried,
so the statement is unchanged and no consumer had to move. See
`docs/axiom-audit.md` §13.

Re-pinned from 29 to 25: the four `PersistentArray`/`PersistentHashMap`
container axioms were removed, together with the `WF.toList'_length` theorem that
was their only consumer. They are gone because nothing reaches them any more, not
because they were proved: `Lean4Lean.LocalContext` and the `SMap` stage-1
environment map replaced the persistent containers with `Std.HashMap`/`Array`,
whose lemmas are theorems. This was **class (B)** in `docs/axiom-audit.md` §14.4
-- the only axioms with no model at all, since no model of the HAMT or of the
persistent-array trie exists -- so it removes the whole residual consistency risk
rather than shrinking it. Verified before re-pinning: all five names unreachable
from `Lean4Lean.addDecl`'s 7853-declaration cone, arena 185/6/0 unchanged.
Human-approved (2026-08-29).

Re-pinned from 27 to 29 — **the first expansion; every prior re-pin was a
reduction.** `Lean4Lean.ptrEqExpr_eq` and `Lean4Lean.ptrEqConstantInfo_eq` were
moved here from `Lean4Lean/PtrEq.lean`, where they had been declared next to the
opaques they constrain.

**This records no new assumption.** Both axioms had been asserted and used since
long before this guard existed: an axiom-cone scan put them in the cone of
`Bridge.not_leanTTConsistent_of_kernel_proves_false` and the rest of the Bridge
chain, with **49** and **47** dependents. Because check 1 enumerates axioms by
*defining module*, an axiom declared outside `Verify/Axioms.lean` was invisible
to it — and check 2 would have failed the moment `kernel_sound`'s proof
completed. The count moved up because the guard's *view* was widened to the
axioms already in force, not because anything new was assumed. Moving the
declarations is what makes one list suffice for both checks.

Both have the form `ptrEq a b = true → a = b`: an implication constraining only
the `true` branch, hence structurally immune to the equational
value-on-the-wrong-branch defect behind both historical `False`-proofs, and
satisfiable by the exhibited model `fun _ _ => false`. Neither can be deleted
(they are used) nor discharged (`ptrEqExpr` is `opaque` by design). See
`docs/axiom-audit.md` §14.

Re-pinned from 25 to 24: `Lean.Expr.replace_eq` was **deleted**. It asserted
`Lean.Expr.replace = Expr.replaceNoCache`, and upstream `Expr.replace` is
`replaceImpl`: `opaque` with `@[extern "lean_replace_expr"]` and no Lean body, so
the axiom could never become a theorem. It is gone because the checker no longer
reaches it. Six level-parameter sites now call core's own pure
`Lean.Expr.instantiateLevelParamsNoCache` instead of the cached
`instantiateLevelParams`/`instantiateTypeLevelParams`, and an 8444-constant walk of
`Lean4Lean.addDecl`'s cone reports `Expr.replaceImpl`, `Expr.replace`,
`Expr.instantiateLevelParams`, `Expr.instantiateLevelParamsCore` and
`ConstantInfo.instantiateTypeLevelParams` all absent. See `divergences.md`
§ "level-parameter instantiation is uncached".

Note for anyone re-treading this: the axiom was `@[simp]`, so a by-name search
wrongly reported it unused once before — it was silently bridging `replace` to
`replaceNoCache` inside `instantiateLevelParamsCore_eq`. **An `@[simp]` axiom's
reachability is a build result, never a grep result.**

Shrinking this list is progress; adding to it requires sign-off. -/
def frozenAxioms : List Name := [
  `Lean.Expr.abstractRange_eq,
  `Lean.Expr.abstract_eq,
  `Lean.Expr.equal_eq,
  `Lean.Expr.eqv_eq,
  `Lean.Expr.hasLooseBVar_eq,
  `Lean.Expr.instantiate1_eq,
  `Lean.Expr.instantiateRange_eq,
  `Lean.Expr.instantiateRevRange_eq,
  `Lean.Expr.instantiateRev_eq,
  `Lean.Expr.instantiate_eq,
  `Lean.Expr.lowerLooseBVars_eq,
  `Lean.Expr.mkAppData_eq,
  `Lean.Expr.mkData_eq,
  `Lean.Level.hasMVar_eq,
  `Lean.Level.hasParam_eq,
  `Lean.Level.instLawfulBEqLevel,
  `Lean.Level.isExplicitSubsumedAux_eq,
  `Lean.Level.mkData_eq,
  `Lean.Level.mkMaxAux_eq,
  `Lean.Level.normalize_eq,
  `Lean.Level.skipExplicit_eq,
  `Lean.Syntax.structEq_eq,
  `Lean4Lean.ptrEqExpr_eq,
  `Lean4Lean.ptrEqConstantInfo_eq]

/-- Check 2's reference set: the three standard axioms, plus every axiom this
project asserts. -/
def axiomWhitelist : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound] ++ frozenAxioms

/-- Constants defined in this repo, reachable from `Lean4Lean.addDecl`, that
are `partial`, `@[extern]`, or `@[implemented_by]` — frozen at the state of
the implementation when this guard was written. Entries may be removed as the
checker is made total; none may be added without human sign-off. -/
def implGapWhitelist : List Name := [
  `Lean.Expr.cheapBetaReduce.loop,                        -- partial
  `Lean.Expr.replaceM,                                    -- implemented_by
  `Lean.Expr.replaceNoCacheT,                             -- partial
  `Lean.Kernel.Environment.checkDuplicatedUnivParams,     -- partial
  `Lean.Level.Normalize.VarNode.addVar,                   -- partial
  `Lean.Level.Normalize.normalizeAux,                     -- partial
  `Lean.Level.Normalize.orderedInsert,                    -- partial
  `Lean.Level.Normalize.subset,                           -- partial
  `Lean.Level.Normalize.subsumeVars,                      -- partial
  `Lean.Level.forEach,                                    -- partial
  `Lean4Lean.AddInductive.checkConstructors.loop,         -- partial
  `Lean4Lean.AddInductive.checkInductiveTypes.loopInd,    -- partial
  `Lean4Lean.AddInductive.checkInductiveTypes.loopInd.loop, -- partial
  `Lean4Lean.AddInductive.checkPositivity.loop,           -- partial
  `Lean4Lean.AddInductive.declareConstructors.arity,      -- partial
  `Lean4Lean.AddInductive.getElimLevel.loop,              -- partial
  `Lean4Lean.AddInductive.isKTarget.loop,                 -- partial
  `Lean4Lean.AddInductive.isLargeEliminator.loop,         -- partial
  `Lean4Lean.AddInductive.isRec.loop,                     -- partial
  `Lean4Lean.AddInductive.isRecArg.loop,                  -- partial
  `Lean4Lean.AddInductive.isReflexive.loop,               -- partial
  `Lean4Lean.AddInductive.mkRecInfos.loopArgs1,           -- partial
  `Lean4Lean.AddInductive.mkRecInfos.loopCtorArgs.loop,   -- partial
  `Lean4Lean.AddInductive.mkRecInfos.loopCtors,           -- partial
  `Lean4Lean.AddInductive.mkRecInfos.loopInd1,            -- partial
  `Lean4Lean.AddInductive.mkRecInfos.loopInd2,            -- partial
  `Lean4Lean.AddInductive.mkRecInfos.loopU,               -- partial
  `Lean4Lean.AddInductive.mkRecInfos.loopUArgs.loop,      -- partial
  `Lean4Lean.AddInductive.mkRecRules.loopU,               -- partial
  `Lean4Lean.ElimNestedInductive.mkUniqueName.loop,       -- partial
  `Lean4Lean.ElimNestedInductive.run.loop,                -- partial
  `Lean4Lean.ElimNestedInductive.withParams.loop,         -- partial
  `Lean4Lean.Environment.forallTelescope.loop,            -- partial
  `Lean4Lean.Environment.lambdaTelescope.loop,            -- partial
  `Lean4Lean.EquivManager.isEquiv,                        -- partial
  `Lean4Lean.TypeChecker.Inner.inferApp.loop,             -- partial
  `Lean4Lean.TypeChecker.Inner.inferForall.loop,          -- partial
  `Lean4Lean.TypeChecker.Inner.inferLambda.loop,          -- partial
  `Lean4Lean.TypeChecker.Inner.inferLet.loop,             -- partial
  `Lean4Lean.TypeChecker.Inner.inferType',                -- partial
  `Lean4Lean.TypeChecker.Inner.isDefEqApp.loop,           -- partial
  `Lean4Lean.TypeChecker.Inner.isDefEqArgs,               -- partial
  `Lean4Lean.TypeChecker.Inner.isDefEqForall,             -- partial
  `Lean4Lean.TypeChecker.Inner.isDefEqLambda,             -- partial
  `Lean4Lean.TypeChecker.Inner.lazyDeltaProjReduction.loop, -- partial
  `Lean4Lean.TypeChecker.Inner.lazyDeltaReduction.loop,   -- partial
  `Lean4Lean.TypeChecker.Inner.whnf',                     -- partial
  `Lean4Lean.TypeChecker.Inner.whnf'.loop,                -- partial
  `Lean4Lean.TypeChecker.Inner.whnfCore',                 -- partial
  `Lean4Lean.TypeChecker.Inner.whnfCore'.loop,            -- partial
  `Lean4Lean.TypeChecker.Methods.withFuel,                -- partial
  `Lean4Lean.ptrEqConstantInfo.unsafe_impl_2,             -- implemented_by
  `Lean4Lean.ptrEqExpr.unsafe_impl_2,                     -- implemented_by
  `List.all2]                                             -- partial

/- Check 1: the frozen axiom file declares exactly the 24 whitelisted axioms. -/
#eval show CoreM Unit from do
  let env ← getEnv
  let some modIdx := env.getModuleIdx? `Lean4Lean.Verify.Axioms
    | throwError "guard: module Lean4Lean.Verify.Axioms not found"
  let mut declared : NameSet := {}
  for (n, ci) in env.constants.toList do
    if let .axiomInfo _ := ci then
      if env.getModuleIdxFor? n = some modIdx then
        declared := declared.insert n
  -- `frozenAxioms`, not `axiomWhitelist`: this check is about what
  -- `Verify/Axioms.lean` declares, and must not demand the three standard
  -- axioms be declared there.
  let frozen : NameSet := frozenAxioms.foldl (·.insert ·) {}
  for n in declared.toList do
    unless frozen.contains n do
      throwError "guard VIOLATION: Axioms.lean declares {n}, \
        which is not in the frozen 24-axiom whitelist. \
        Changing that file requires human sign-off."
  for n in frozen.toList do
    unless declared.contains n do
      throwError "guard VIOLATION: frozen axiom {n} is no longer declared by \
        Axioms.lean. Changing that file requires human sign-off."
  IO.println s!"guard 1: Axioms.lean declares exactly the 24 frozen axioms ✓"

/- Check 2: the axioms of `kernel_sound` are within the whitelist. -/
#eval show CoreM Unit from do
  let axioms ← collectAxioms ``kernel_sound
  let allowed : NameSet := axiomWhitelist.foldl (·.insert ·) {}
  let mut sorries := false
  for n in axioms do
    if n == ``sorryAx then
      sorries := true
    else unless allowed.contains n do
      throwError "guard VIOLATION: kernel_sound uses axiom {n}, which is \
        outside the whitelist (propext, Classical.choice, Quot.sound, and the \
        24 frozen axioms of Axioms.lean). Adding an axiom requires human \
        sign-off."
  if sorries then
    IO.println "guard 2: kernel_sound axioms within whitelist ✓ \
      (proof INCOMPLETE: sorryAx present)"
  else
    IO.println "guard 2: kernel_sound axioms within whitelist ✓ — \
      proof COMPLETE, no sorry"

/- Check 3: no new `partial`/`@[extern]`/`@[implemented_by]` constants defined
in this repo are reachable from the checker entry point. -/
#eval show CoreM Unit from do
  let env ← getEnv
  let mut visited : NameSet := {}
  let mut stack : List Name := [``Lean4Lean.addDecl]
  while h : stack ≠ [] do
    let n := stack.head h
    stack := stack.tail
    if visited.contains n then continue
    visited := visited.insert n
    if let some ci := env.find? n then
      for u in ci.getUsedConstantsAsSet.toList do
        unless visited.contains u do stack := u :: stack
      -- follow the code that actually executes
      if let some impl := Compiler.getImplementedBy? env n then
        unless visited.contains impl do stack := impl :: stack
      let uRec := Name.str n "_unsafe_rec"
      if env.contains uRec then
        unless visited.contains uRec do stack := uRec :: stack
  let allowed : NameSet := implGapWhitelist.foldl (·.insert ·) {}
  let mut count := 0
  for n in visited.toList do
    let some modIdx := env.getModuleIdxFor? n | continue
    let modName := env.header.moduleNames.getD modIdx.toNat .anonymous
    unless (`Lean4Lean).isPrefixOf modName do continue
    let mut kinds : List String := []
    if (Compiler.getImplementedBy? env n).isSome then kinds := "implemented_by" :: kinds
    if (getExternAttrData? env n).isSome then kinds := "extern" :: kinds
    -- A `_unsafe_rec` companion alone does NOT mean `partial`: the equation compiler emits
    -- one for *every* computable recursive definition, structural and well-founded included.
    -- What distinguishes a genuine `partial def` is that it elaborates to an `opaque`.
    if env.contains (.str n "_unsafe_rec") then
      match env.find? n with
      | some (.opaqueInfo _) => kinds := "partial" :: kinds
      | _ => pure ()   -- ordinary recursive def: `_unsafe_rec` is codegen, not `partial`
    unless kinds.isEmpty do
      count := count + 1
      let ks := ", ".intercalate kinds
      unless allowed.contains n do
        throwError "guard VIOLATION: {n} ({ks}, defined in \
          {modName}) is reachable from Lean4Lean.addDecl but not in the frozen \
          implementation-gap whitelist. New partial/extern/implemented_by in \
          the checker's cone lets the compiled checker diverge from the \
          verified function; it requires human sign-off."
  IO.println s!"guard 3: checker cone implementation gaps within frozen list \
    ({count}/{implGapWhitelist.length} remaining) ✓"

end Lean4Lean.Guard
