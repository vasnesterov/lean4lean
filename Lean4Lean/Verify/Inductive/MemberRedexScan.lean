import Lean4Lean.Verify.Inductive.CanonGapMeasure
import Lean4Lean.Theory.Inductive.MemberRedex

/-!
# Row 117e, executed: the ground truth `vconst` cannot see, and the repair's coverage

**This file changes no implementation and weakens no statement.**  It is the executed half of
`Theory/Inductive/MemberRedex.lean`, and it exists because that file's usual ground-truth anchor
is broken in this corner: `vconst(type_of% ·)` **β-reduces**, so a `vconst` equation cannot
witness what the kernel stores for a redex-containing type.  §1 reads the stored `Expr` instead.

**Standing note (ledger row 116h): this file imports `Experimental/ConeJoin.lean` — for the same
reason `CanonGapMeasure.lean` does, the duplicate-name check — so it must NEVER be listed in
`ConeJoin.lean`.  `Theory/Inductive/MemberRedex.lean` is the file that goes there.**

* §1 — the stored `MRedex.MRWit.MJ.rec_1`, self-guarding: the `node` minor premise's field domain
  **is** the β-redex `(fun x => MJ) k`, and it **does** carry an induction hypothesis.  Both halves
  matter: the first is what makes `VNestedOcc.field`'s stored type faithful, the second is what
  makes its `recArg = none` unfaithful.
* §2 — the coverage measurement, **guarded** (four `throwError`s, added 2026-09-02: the figures
  used to be `logInfo`-only, i.e. a report rather than a statement -- ledger row 118f's mistake).  For every safe block in the running environment that has a
  nested-shaped field, `ElimNestedInductive.run` is applied and every auxiliary constructor field
  is classified by three predicates: the **syntactic** one the recogniser uses today, the
  **head-β** one `VNestedOcc.field` adds, and the **whnf** one the implementation itself uses
  (`AddInductive.isRecArg`'s loop, transcribed).  What the repair must cover is
  `whnf ∧ ¬syntactic`; what it would still miss is `whnf ∧ ¬syntactic ∧ ¬headβ`.
-/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

namespace MRScanGT

/-! ## 1. The stored companion recursor -/

/-- Strip `n` leading `forallE`s. -/
def mrsDrop : Nat → Expr → Expr
  | 0, e => e
  | n+1, .forallE _ _ b _ => mrsDrop n b
  | _+1, e => e

/-- The `i`-th leading binder domain. -/
def mrsDom : Nat → Expr → Option Expr
  | 0, .forallE _ d _ _ => some d
  | n+1, .forallE _ _ b _ => mrsDom n b
  | _, _ => none

def mrsPis : Expr → Nat
  | .forallE _ _ b _ => mrsPis b + 1
  | _ => 0

#eval show Lean.CoreM Unit from do
  let env ← getEnv
  let some ci := env.find? ``MRedex.MRWit.MJ.rec_1
    | throwError "mr/gt: MJ.rec_1 absent -- then the witness block is not the nested one \
        Theory/Inductive/MemberRedex.lean claims and its ground-truth rows are void"
  -- binders: motive_1, motive_2, obj-minor, node-minor, major
  let some nodeMinor := mrsDom 3 ci.type
    | throwError "mr/gt: MJ.rec_1 has fewer than 4 leading binders: {ci.type}"
  unless mrsPis nodeMinor == 3 do
    throwError "mr/gt: the node minor premise has {mrsPis nodeMinor} binders, not 3 -- \
      Theory/Inductive/MemberRedex.lean's mr_minor_arity_ground is measuring something else: \
      {nodeMinor}"
  let some fieldDom := mrsDom 1 nodeMinor
    | throwError "mr/gt: no field binder in the node minor premise"
  unless fieldDom.isApp && !fieldDom.getAppFn.isConst do
    throwError "mr/gt: the stored field domain is {fieldDom}, not an `.app`-headed redex -- \
      then `instantiateForallParams` now beta-reduces and the whole round is void"
  unless fieldDom.headBeta.getAppFn.constName? == some ``MRedex.MRWit.MJ do
    throwError "mr/gt: the field domain's head-beta is {fieldDom.headBeta}, not the block \
      member MJ"
  let some ih := mrsDom 2 nodeMinor
    | throwError "mr/gt: the node minor premise has no third binder -- then Lean does NOT give \
        the redex field an induction hypothesis and route B of row 117e is wrong"
  -- and `vconst`'s reading of the same position, for the caveat
  logInfo m!"mr/gt: STORED MJ.rec_1 node minor premise = {nodeMinor}\n\
    mr/gt:   field domain (stored)   = {fieldDom}   -- an `.app`-headed β-redex ✓\n\
    mr/gt:   field domain (head-β)   = {fieldDom.headBeta}   -- the block member MJ ✓\n\
    mr/gt:   induction hypothesis    = {ih}   -- Lean DOES treat the redex field as recursive ✓\n\
    mr/gt: so the built companion member's `recArg = none` computes a 2-binder minor premise \
    where the kernel stores a 3-binder one, and `vconst(type_of% @MJ.rec_1)` cannot see it \
    because it β-reduces the domain."

end MRScanGT

/-! ## 2. Coverage: does head-β suffice on the population that matters? -/

namespace MRScanCov
open CGMGuard CGMScan CGMScan3

/-- Syntactic pi-stripping. -/
partial def mrcStripSyn : Expr → Expr
  | .forallE _ _ b _ => mrcStripSyn b
  | .mdata _ e => mrcStripSyn e
  | e => e

/-- The essential content of `VIndRestore.recogAt`: after stripping the *syntactic* leading pis,
is the spine head one of the block's own type constants? -/
def mrcSyn (names : List Name) (e : Expr) : Bool :=
  match (mrcStripSyn e).getAppFn with
  | .const c _ => names.contains c
  | _ => false

/-- The same after one **head-β** contraction — what `VNestedOcc.field` adds. -/
def mrcBeta (names : List Name) (e : Expr) : Bool := mrcSyn names e.headBeta

/-- `AddInductive.isRecArg`'s own loop (`Lean4Lean/Inductive/Add.lean`): `whnf` at every step.

**The loose-bvar guard is load-bearing and the `try`/`catch` below could not do its job without
it.**  `Meta.whnf` on an expression with a loose bvar does not throw — it **panics**, and a Lean
`panic!` prints to stderr and returns the `Inhabited` default, so `catch` never fires and `whnf`
hands back an arbitrary expression.  Before this guard the scan panicked **nine times** per run
(`PANIC at Lean.Meta.whnfEasyCases … loose bvar in expression`), which was visible only as
stderr noise: all four `throwError` guards below still passed, because none of them can detect
that a `whnf` result was fabricated.  So every coverage figure this scan has ever reported was
computed partly from default values.  Skipping `whnf` where the term is not closed in the local
context is the conservative choice: it can only make `mrcWhnf` return `false` where it used to
return garbage, so a *defect* can disappear but none can be invented. -/
partial def mrcWhnf (names : List Name) (t : Expr) : MetaM Bool := do
  let t ← if t.hasLooseBVars then pure t else try Meta.whnf t catch _ => pure t
  match t with
  | .forallE n d b bi =>
    Meta.withLocalDecl n bi d fun x => mrcWhnf names (b.instantiate1 x)
  | _ => return match t.getAppFn with
    | .const c _ => names.contains c
    | _ => false

#eval show Lean.MetaM Unit from do
  let lenv ← getEnv
  let kenv := lenv.toKernelEnv
  let nidx : Name → Nat := fun n => match lenv.find? n with
    | some (.inductInfo w) => w.numIndices | _ => 0
  let mut tried := 0
  let mut fields := 0
  let mut defect := 0          -- whnf ∧ ¬syn : what `field` gets wrong today
  let mut covered := 0         -- whnf ∧ ¬syn ∧ headβ : what the repair fixes
  let mut residual := 0        -- whnf ∧ ¬syn ∧ ¬headβ : what the repair still misses
  let mut defectBlocks : List Name := []
  let mut residualBlocks : List Name := []
  for (n, ci) in lenv.constants.toList do
    let .inductInfo v := ci | continue
    unless v.all.head? == some n do continue
    if v.isUnsafe then continue
    let mut hasNested := false
    let mut types : List InductiveType := []
    for m in v.all do
      let some (.inductInfo w) := lenv.find? m | continue
      let mut cs : List Constructor := []
      for c in w.ctors do
        let some cci := lenv.find? c | continue
        cs := cs ++ [{ name := c, type := cci.type }]
        let (_, nn, _) := cgmWalkCtor lenv v.all (v.levelParams.map Level.param) v.numParams
          nidx 0 0 cci.type
        if nn > 0 then hasNested := true
      types := types ++ [{ name := m, type := w.type, ctors := cs }]
    unless hasNested do continue
    tried := tried + 1
    let lvls := v.levelParams.map Level.param
    match (ElimNestedInductive.run 10000 v.numParams types kenv).run'
        { lvls, newTypes := types.toArray } with
    | Except.error _ => continue
    | Except.ok res =>
      let anames := res.types.map (·.name)
      let mut blockDefect := false
      let mut blockResidual := false
      for t in res.types do
        for c in t.ctors do
          -- Walk the constructor's pi spine; binders past `numParams` are fields.
          --
          -- **The binders MUST be instantiated as we descend, and the previous version did not
          -- do it.**  It recursed into `body` with loose bvars intact, so every domain at depth
          -- `k` carried up to `k` loose bvars; `mrcWhnf` then called `Meta.whnf` on them, which
          -- does not throw but **panics** and returns the `Inhabited` default.  Nine panics per
          -- run, invisible to all four guards below, and every coverage figure this scan has
          -- reported was computed partly from fabricated `whnf` results.  The three verdicts are
          -- therefore computed here, *inside* the enclosing `withLocalDecl`s, where each domain
          -- is closed; only `Bool`s leave the scope, so no free variable escapes it.
          let rec walk (i : Nat) : Expr → MetaM (List (Bool × Bool × Bool))
            | .forallE n dom body bi => do
              let here : List (Bool × Bool × Bool) ←
                if i < v.numParams then pure [] else do
                  let syn := mrcSyn anames dom
                  let hb := mrcBeta anames dom
                  let wh ← mrcWhnf anames dom
                  pure [(syn, hb, wh)]
              let rest ← Meta.withLocalDecl n bi dom fun x => walk (i + 1) (body.instantiate1 x)
              return here ++ rest
            | _ => return []
          for (syn, hb, wh) in ← walk 0 c.type do
            fields := fields + 1
            if wh && !syn then
              defect := defect + 1
              blockDefect := true
              if hb then covered := covered + 1
              else
                residual := residual + 1
                blockResidual := true
      if blockDefect then defectBlocks := n :: defectBlocks
      if blockResidual then residualBlocks := n :: residualBlocks
  logInfo s!"mr/cov: {tried} safe blocks with a nested-shaped field, {fields} auxiliary \
    constructor fields after ElimNestedInductive.run.\n\
    mr/cov:   DEFECT (impl says recursive, today's recogniser says no): {defect} field(s) in \
    {defectBlocks.eraseDups.length} block(s) {defectBlocks.eraseDups.take 20}\n\
    mr/cov:   COVERED by one head-β step (VNestedOcc.field): {covered}\n\
    mr/cov:   RESIDUAL after the repair: {residual} in \
    {residualBlocks.eraseDups.length} block(s) {residualBlocks.eraseDups.take 20}"
  -- **Guards, not reports.**  Ledger row 118f: a `logInfo`-only `#eval` is not a measurement,
  -- and until 2026-09-02 the "3/3 coverage, residual 0" figure was `logInfo`-only -- it traced to
  -- notes rather than to anything that could fail.  These four `throwError`s are what make it a
  -- machine-checked statement of this file.  Three of them are the claim; the first two are its
  -- anti-vacuity dual, because a scan that walked nothing, or found nothing to fix, would satisfy
  -- the other two trivially (row 118d: without it, a reject-everything check passes).
  if tried = 0 || fields = 0 then
    throwError "mr/cov: the scan walked {tried} block(s) and {fields} field(s) -- an empty \
      population, so every coverage figure below it is vacuous.  Either ElimNestedInductive.run \
      is failing everywhere or cgmWalkCtor's nested test is broken."
  if defect = 0 then
    throwError "mr/cov: DEFECT is 0 across {tried} block(s) and {fields} field(s) -- then the \
      repair (VNestedOcc.field's head-β branch) fixes nothing on this population and the \
      `3 of 3 covered` claim is vacuous.  Either the whnf transcription (mrcWhnf) or the \
      syntactic one (mrcSyn) is wrong."
  unless defect = covered do
    throwError "mr/cov: {covered} of {defect} defect(s) covered by one head-β step -- the \
      `3 of 3` claim in Theory/Inductive/MemberRedex.lean and ledger row 119c is FALSE on the \
      current environment."
  unless residual = 0 do
    throwError "mr/cov: {residual} field(s) in {residualBlocks.eraseDups.length} block(s) \
      {residualBlocks.eraseDups.take 20} would STILL be misclassified after the head-β repair \
      -- the repair must be strengthened to `isRecArg`'s full loop (whnf at every pi-stripping \
      step), and VNestedOcc.field as written is not enough."
  logInfo "mr/cov: GUARDED -- population non-empty, at least one defect, every defect covered by \
    one head-β step, residual 0.  So the repair is adequate on the population that matters.  It \
    is still narrower than `isRecArg` in principle -- a redex under a binder, or one that needs \
    δ, would need `isRecArg`'s full loop -- and that residue is named, not measured away."

end MRScanCov
end Lean4Lean
