import Lean4Lean.Experimental.ConeJoin

/-!
# Measurement: the syntactic/definitional gap at `VInductDecl'.Canonical` (ledger row 113)

**This file changes no implementation and weakens no statement.**  It is the measurement round
for ledger row 113: `AddInductiveRunRealisesClosed` (`Verify/Inductive/RunIdentity.lean` §4) is
conditionally refuted by a block whose recursive field's *stored* type is a β-redex, and the two
candidate repairs — a syntactic guard, or weakening `VInductDecl'.Canonical` to a definitional
condition — are priced here.

Every name is prefixed `cgm`/`CGM` (ledger row 113f: inside the `ConeJoin` closure any short
name collides, and a silent resolution produces a confidently wrong measurement).
-/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

namespace CGMRedexWit

/-! ## 1. The witness

`inductive cgmT : Type where | mk : ((fun x : Type => cgmT) Prop) → cgmT`

`np = 0`, one member, one constructor, one field.  The field's stored type is a β-redex whose
`whnf` is `cgmT`, so `AddInductive.isRecArg` classifies it as **recursive** while the stored type
is `.app`-headed. -/

/-- `(fun x : Type => cgmT) Prop` — the field's stored type. -/
def cgmRedex : Expr :=
  .app (.lam `x (.sort (.succ .zero)) (.const `cgmT []) .default) (.sort .zero)

def cgmCtor : Constructor :=
  { name := `cgmT.mk, type := .forallE `a cgmRedex (.const `cgmT []) .default }

def cgmBlock : InductiveType :=
  { name := `cgmT, type := .sort (.succ .zero), ctors := [cgmCtor] }

/-- The block is closed and fvar-free, so **ruling 109's guard does not exclude it**: the two
repairs priced here are genuinely a new question, not a re-run of rows 108–112. -/
theorem cgm_blockClosed : BlockClosed [cgmBlock] := by
  intro t ht; rw [List.mem_singleton] at ht; subst ht; decide

theorem cgm_blockClosedMembers : BlockClosedMembers [cgmBlock] := by
  intro t ht; rw [List.mem_singleton] at ht; subst ht; decide

theorem cgm_noLooseBVars_ctor : noLooseBVars 0 cgmCtor.type = true := by decide

/-! ## 2. The witness is accepted, and the stored field type is the redex verbatim

Self-guarding: this `#eval` throws if any of the four checkers starts rejecting the block, which
is exactly what the guard priced in §4 would do. -/

#eval show Lean.CoreM Unit from do
  let kenv := Kernel.Environment.empty `main
  -- ruling 109's guard accepts it: nothing here is about loose bvars
  match checkNoLooseBVars cgmCtor.name cgmCtor.type with
  | Except.error _ => throwError "cgm/accept: checkNoLooseBVars rejects the redex block -- \
      then row 113's witness is already excluded and the whole measurement is void"
  | Except.ok _ => pure ()
  -- `AddInductive.run` on the input block, which is what `AddInductiveRunRealisesClosed` states
  match AddInductive.run 0 [cgmBlock] 0
      { env := kenv, allowPrimitive := false, lparams := [], safety := .safe, fuel := {} } with
  | Except.error e => throwError "cgm/accept: AddInductive.run REJECTS the redex block \
      ({e.toMessageData {}}) -- AddInductiveRunRealisesClosed is vacuous at it and row 113's \
      conditional refutation must be withdrawn"
  | Except.ok env' =>
    let some ci := env'.find? cgmCtor.name
      | throwError "cgm/accept: AddInductive.run accepted but stored no constructor"
    unless ci.type == cgmCtor.type do
      throwError "cgm/accept: the STORED constructor type is {repr ci.type}, not the submitted \
        {repr cgmCtor.type} -- the field's stored type is not the redex and TrIndDecl.trCtors \
        does not force it"
  -- and the two outer entry points
  match Environment.addInductive kenv [] 0 [cgmBlock] false false with
  | Except.error e => throwError "cgm/accept: Environment.addInductive REJECTS the redex block \
      ({e.toMessageData {}}) -- row 113's witness is unreachable"
  | Except.ok _ => pure ()
  match Lean4Lean.addDecl kenv (.inductDecl [] 0 [cgmBlock] false) with
  | Except.error e => throwError "cgm/accept: Lean4Lean.addDecl REJECTS the redex block \
      ({e.toMessageData {}})"
  | Except.ok _ => pure ()
  logInfo "cgm/accept: AddInductive.run, Environment.addInductive and Lean4Lean.addDecl all \
    ACCEPT the β-redex recursive field from the empty environment, and the stored constructor \
    type is the submitted one verbatim ✓"

end CGMRedexWit

/-! ## 3. The candidate guard, stated and **not installed**

The guard is `AddInductive.checkPositivity` with its leading `whnf` deleted.  Like
`Lean4Lean.noLooseBVars` it is written as a **pure structural recursion** rather than through
anything cached or opaque, so it reaches **no axiom at all**; and like it, the depth parameter
replaces `withLocalDecl`, so the check is a fact about the *stored* `Expr` rather than about an
fvar context.

`cgmOcc` is `AddInductive.hasIndOcc` asked on a `List Name` instead of an `Array Expr` of
`.const`s; `hasIndOcc_eq` (`Verify/Inductive/Add.lean`) is the existing bridge between the two,
and `anySub` is the existing pure reading of `Lean4Lean.anySubterm`. -/

namespace CGMGuard

/-- The block-occurrence predicate. -/
def cgmP (names : List Name) : Expr → Bool
  | .const c _ => names.contains c
  | _ => false

/-- `e` mentions one of the block's own type constants. -/
def cgmOcc (names : List Name) (e : Expr) : Bool := anySub (cgmP names) e

/-- The syntactic reading of `AddInductive.isValidIndApp?`: the head is the `j`-th member of the
block at the block's own levels, applied to exactly `np + nindices j` arguments whose first `np`
are the parameter bvars `#(d-1) … #(d-np)` and whose remaining ones are block-free.  This is
`VInductDecl'.tyApp`'s syntactic image: `bvars k np = [#(k+np-1), …, #k]` with `k = d - np`. -/
def cgmValidIndApp (names : List Name) (lvls : List Level) (np : Nat) (nidx : Name → Nat)
    (d : Nat) (t : Expr) : Bool :=
  t.withApp fun f args =>
    match f with
    | .const I us =>
        names.contains I && us == lvls && args.size == np + nidx I && decide (np ≤ d) &&
        args.toList.take np == (List.range np).map (fun k => Expr.bvar (d - 1 - k)) &&
        (args.toList.drop np).all fun a => !cgmOcc names a
    | _ => false

/-- **The guard.**  `AddInductive.checkPositivity`'s recursion with `t ← whnf t` deleted and
`withLocalDecl` replaced by a depth counter. -/
def cgmSynPos (names : List Name) (lvls : List Level) (np : Nat) (nidx : Name → Nat) :
    Nat → Expr → Bool
  | d, .mdata _ e => cgmSynPos names lvls np nidx d e
  | d, .forallE _ dom body _ =>
      !cgmOcc names dom && cgmSynPos names lvls np nidx (d + 1) body
  | d, t => !cgmOcc names t || cgmValidIndApp names lvls np nidx d t

/-! ### The intended condition, in closed form

`cgmBinderDoms` and `cgmStripHead` are the syntactic pi-spine decomposition — the `Expr`-side
counterpart of `VIndCtor.skeleton` (`Theory/Inductive/Decl.lean`), which inverts `VIndCtor.type`
on the nose. -/

def cgmBinderDoms : Expr → List Expr
  | .mdata _ e => cgmBinderDoms e
  | .forallE _ dom b _ => dom :: cgmBinderDoms b
  | _ => []

def cgmStripHead : Expr → Expr
  | .mdata _ e => cgmStripHead e
  | .forallE _ _ b _ => cgmStripHead b
  | e => e

def cgmStripD (d : Nat) : Expr → Nat
  | .mdata _ e => cgmStripD d e
  | .forallE _ _ b _ => cgmStripD (d + 1) b
  | _ => d

theorem cgmOcc_mdata (names : List Name) (m : MData) (e : Expr) :
    cgmOcc names (.mdata m e) = cgmOcc names e := by
  rw [cgmOcc, cgmOcc, anySub_eq]; simp [cgmP]

theorem cgmOcc_forallE (names : List Name) (n : Name) (d b : Expr) (bi : BinderInfo) :
    cgmOcc names (.forallE n d b bi) = (cgmOcc names d || cgmOcc names b) := by
  rw [cgmOcc, cgmOcc, cgmOcc, anySub_eq]; simp [cgmP]

/-- **The guard decides exactly the intended condition** — the analogue of `noLooseBVars_iff`
(`Verify/Inductive/RunIdentity.lean`), and the reason it is needed is the same: a check that
decided *more* than intended would refuse legitimate declarations while satisfying every
instrument in this repo.

Read right to left: the field's stored type either mentions no block constant at all, or its
**syntactic** pi-spine has block-free binders and ends in the block's own type constant applied
to the parameter bvars and to block-free indices.  That right-hand disjunct is
`VIndCtor.Canonical`'s equation `F.type = r.canonType D i` transported to `Expr`, with
`r.binders = cgmBinderDoms F.type` and `r.args = (cgmStripHead F.type).getAppArgs.drop np`. -/
theorem cgm_synPos_iff (names : List Name) (lvls : List Level) (np : Nat) (nidx : Name → Nat) :
    ∀ (d : Nat) (t : Expr), cgmSynPos names lvls np nidx d t = true ↔
      (cgmOcc names t = false ∨
        ((cgmBinderDoms t).all (fun B => !cgmOcc names B) = true ∧
          cgmValidIndApp names lvls np nidx (cgmStripD d t) (cgmStripHead t) = true)) := by
  intro d t
  induction t generalizing d with
  | mdata m e ih => rw [cgmSynPos, cgmOcc_mdata, cgmBinderDoms, cgmStripHead, cgmStripD]; exact ih d
  | forallE n dom body bi _ ihb =>
    rw [cgmSynPos, cgmOcc_forallE, cgmBinderDoms, cgmStripHead, cgmStripD, List.all_cons]
    rw [Bool.and_eq_true, ihb (d + 1)]
    constructor
    · rintro ⟨hd, hb | ⟨h1, h2⟩⟩
      · exact .inl (by simp [Bool.not_eq_true'] at hd; simp [hd, hb])
      · exact .inr ⟨by simp_all, h2⟩
    · rintro (h | ⟨h1, h2⟩)
      · simp only [Bool.or_eq_false_iff] at h
        exact ⟨by simp [h.1], .inl h.2⟩
      · simp only [Bool.and_eq_true] at h1
        exact ⟨h1.1, .inr ⟨h1.2, h2⟩⟩
  | _ =>
    simp only [cgmSynPos, cgmBinderDoms, cgmStripHead, cgmStripD, List.all_nil, true_and,
      Bool.or_eq_true, Bool.not_eq_true']

end CGMGuard

/-! ## 4. What the guard would cost: the running environment, scanned

For every inductive block in the running environment (Lean core + `Std` + `Mathlib` + this
project, i.e. the same population `Verify/ClosednessPropagation.lean`'s loose-bvar scan reports as
4158 inductives / 6744 constructors), every constructor field is classified by `cgmSynPos`.

Three buckets, and the third is the only one the guard would newly reject:

* **ok** — the field is syntactically block-free, or syntactically `∀ ξ, I p π` canonical;
* **nested** — the field's syntactic spine ends in a *foreign* inductive applied to parameters
  that mention the block (`List (Tree α)`).  These are the nested occurrences.  The guard belongs
  **after** `ElimNestedInductive.run`, where such a field has become `_nested.List_1 α …` and is
  canonical, so this bucket is not a cost — but it is reported separately rather than folded into
  "ok", because on the *stored* (restored) types it is a `cgmSynPos` failure, and a guard placed
  in the pre-`run` loop *would* reject all of it;
* **violation** — anything else: a redex-headed recursive field (row 113's witness), a field whose
  pi-spine needs `whnf` to be seen, a `letE`, a block occurrence under a projection.

`nidx` is read out of the environment rather than recomputed. -/

namespace CGMScan
open CGMGuard

/-- Classify one field type; `2` = violation, `1` = nested-shaped, `0` = ok. -/
def cgmClass (env : Lean.Environment) (names : List Name) (lvls : List Level) (np : Nat)
    (nidx : Name → Nat) (d : Nat) (t : Expr) : Nat :=
  if cgmSynPos names lvls np nidx d t then 0
  else
    (cgmStripHead t).withApp fun f args =>
      match f with
      | .const C _ =>
        if names.contains C then 2
        else match env.find? C with
          | some (.inductInfo w) =>
            if (args.toList.take w.numParams).any (fun a => cgmOcc names a) then 1 else 2
          | _ => 2
      | _ => 2

/-- Walk a constructor's syntactic pi-spine.  The first `np` binders are the parameters; each
later binder's domain is a field, classified at the binder depth it sits at.  Returns
`(nfields, nested-shaped, violations)`. -/
def cgmWalkCtor (env : Lean.Environment) (names : List Name) (lvls : List Level) (np : Nat)
    (nidx : Name → Nat) : Nat → Nat → Expr → Nat × Nat × Nat
  | d, i, .forallE _ dom body _ =>
    let (nf, a, b) := cgmWalkCtor env names lvls np nidx (d + 1) (i + 1) body
    if i < np then (nf, a, b)
    else match cgmClass env names lvls np nidx d dom with
      | 0 => (nf + 1, a, b)
      | 1 => (nf + 1, a + 1, b)
      | _ => (nf + 1, a, b + 1)
  | _, _, _ => (0, 0, 0)

#eval show Lean.CoreM Unit from do
  let env ← getEnv
  let nidx : Name → Nat := fun n => match env.find? n with
    | some (.inductInfo w) => w.numIndices
    | _ => 0
  let mut blocks := 0
  let mut ctors := 0
  let mut fields := 0
  let mut nested := 0
  let mut viol := 0
  let mut nestedBlocks : List Name := []
  let mut violCtors : List Name := []
  let mut violNestedBlocks : List Name := []
  for (n, ci) in env.constants.toList do
    let .inductInfo v := ci | continue
    unless v.all.head? == some n do continue   -- one visit per mutual block
    blocks := blocks + 1
    let names := v.all
    let lvls := v.levelParams.map Level.param
    let np := v.numParams
    let mut blockNested := false
    let mut blockViol := false
    for m in v.all do
      let some (.inductInfo w) := env.find? m | continue
      for c in w.ctors do
        let some cci := env.find? c | continue
        ctors := ctors + 1
        let (nf, nn, nv) := cgmWalkCtor env names lvls np nidx 0 0 cci.type
        fields := fields + nf
        nested := nested + nn
        viol := viol + nv
        if nn > 0 then blockNested := true
        if nv > 0 then
          blockViol := true
          violCtors := c :: violCtors
    if blockNested then nestedBlocks := n :: nestedBlocks
    if blockViol then violNestedBlocks := (if v.isNested then n else n ++ `NOTNESTED) :: violNestedBlocks
  logInfo s!"cgm/scan: {blocks} inductive blocks, {ctors} constructors, {fields} constructor \
    fields in the running environment.  nested-shaped fields: {nested} (in \
    {nestedBlocks.length} blocks); VIOLATIONS: {viol} in {violCtors.eraseDups.length} \
    constructors, {violNestedBlocks.eraseDups.length} blocks.  \
    Violating blocks (`.NOTNESTED` suffix = isNested is false): \
    {violNestedBlocks.eraseDups.take 60}"

end CGMScan

/-! ### 4.1 The one violation, examined

The scan finds exactly **one** violating field in the whole running environment.  This `#eval`
prints it, and re-checks it after `ElimNestedInductive.run` — which is where the guard belongs. -/

namespace CGMScan1
open CGMGuard CGMScan

#eval show Lean.CoreM Unit from do
  let env ← getEnv
  let nidx : Name → Nat := fun n => match env.find? n with
    | some (.inductInfo w) => w.numIndices
    | _ => 0
  for (n, ci) in env.constants.toList do
    let .inductInfo v := ci | continue
    unless v.all.head? == some n do continue
    let names := v.all
    let lvls := v.levelParams.map Level.param
    let np := v.numParams
    let mut bad := false
    for m in v.all do
      let some (.inductInfo w) := env.find? m | continue
      for c in w.ctors do
        let some cci := env.find? c | continue
        let (_, _, nv) := cgmWalkCtor env names lvls np nidx 0 0 cci.type
        if nv > 0 then bad := true
    unless bad do continue
    logInfo m!"cgm/scan1: block {n} (all = {names}, np = {np}, isNested = {v.isNested}), \
      member type {v.type}"
    for m in v.all do
      let some (.inductInfo w) := env.find? m | continue
      for c in w.ctors do
        let some cci := env.find? c | continue
        let (_, _, nv) := cgmWalkCtor env names lvls np nidx 0 0 cci.type
        if nv > 0 then logInfo m!"cgm/scan1:   violating ctor {c} : {cci.type}"

end CGMScan1

/-! ### 4.2 The one violation is `unsafe`, and `TrIndDecl` excludes unsafe blocks

`AddInductive.checkPositivity` runs only under `if !isUnsafe` (`Lean4Lean/Inductive/Add.lean`), and
`TrIndDecl.safe` requires `isUnsafe = false`, so an unsafe block is outside the specification's
domain altogether.  The guard would be placed under the same `if !isUnsafe`, so it does not touch
it either.  This `#eval` is the *safe*-only count. -/

namespace CGMScan2
open CGMGuard CGMScan

#eval show Lean.CoreM Unit from do
  let env ← getEnv
  let nidx : Name → Nat := fun n => match env.find? n with
    | some (.inductInfo w) => w.numIndices
    | _ => 0
  let mut blocks := 0
  let mut ctors := 0
  let mut fields := 0
  let mut nested := 0
  let mut viol := 0
  let mut unsafeViol := 0
  let mut violCtors : List Name := []
  for (n, ci) in env.constants.toList do
    let .inductInfo v := ci | continue
    unless v.all.head? == some n do continue
    if v.isUnsafe then
      -- count separately: positivity is skipped for these and `TrIndDecl.safe` excludes them
      for m in v.all do
        let some (.inductInfo w) := env.find? m | continue
        for c in w.ctors do
          let some cci := env.find? c | continue
          let (_, _, nv) := cgmWalkCtor env v.all (v.levelParams.map Level.param) v.numParams
            nidx 0 0 cci.type
          unsafeViol := unsafeViol + nv
      continue
    blocks := blocks + 1
    for m in v.all do
      let some (.inductInfo w) := env.find? m | continue
      for c in w.ctors do
        let some cci := env.find? c | continue
        ctors := ctors + 1
        let (nf, nn, nv) := cgmWalkCtor env v.all (v.levelParams.map Level.param) v.numParams
          nidx 0 0 cci.type
        fields := fields + nf
        nested := nested + nn
        viol := viol + nv
        if nv > 0 then violCtors := c :: violCtors
  if viol = 0 then
    logInfo s!"cgm/safe: {blocks} SAFE inductive blocks, {ctors} constructors, {fields} fields; \
      {nested} nested-shaped fields; ZERO violations.  The only violation in the environment is \
      in an `unsafe` block ({unsafeViol} field(s)), where positivity is skipped and which \
      `TrIndDecl.safe` excludes ✓"
  else
    throwError "cgm/safe: {viol} violation(s) in SAFE blocks: {violCtors.eraseDups.take 40} -- \
      the guard would reject a safe declaration this toolchain produced"

end CGMScan2

/-! ### 4.3 The nested bucket disappears after `ElimNestedInductive.run`

This is what decides the guard's **placement**.  A nested occurrence `List (Tree α)` is not
syntactically `∀ ξ, I p π`, so a guard in `Environment.addInductive`'s *pre-*`run` loop — where
`checkNoLooseBVars` sits — would reject every nested block.  After `ElimNestedInductive.run` the
same field is `_nested.List_1 α …`, which is canonical.

Every safe block in the environment that has a nested-shaped field is reconstructed from the
environment, put through `ElimNestedInductive.run`, and re-checked against the **auxiliary**
block's names and index counts. -/

namespace CGMScan3
open CGMGuard CGMScan

/-- Number of leading pis, which for a member of `res.types` is `np + nindices`. -/
def cgmNPis : Expr → Nat
  | .forallE _ _ b _ => cgmNPis b + 1
  | .mdata _ e => cgmNPis e
  | _ => 0

#eval show Lean.CoreM Unit from do
  let lenv ← getEnv
  let kenv := lenv.toKernelEnv
  let nidx : Name → Nat := fun n => match lenv.find? n with
    | some (.inductInfo w) => w.numIndices
    | _ => 0
  let mut tried := 0
  let mut runFailed : List Name := []
  let mut stillBad : List Name := []
  let mut auxOk := 0
  for (n, ci) in lenv.constants.toList do
    let .inductInfo v := ci | continue
    unless v.all.head? == some n do continue
    if v.isUnsafe then continue
    -- does the block have a nested-shaped field on its stored (restored) types?
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
    | Except.error _ => runFailed := n :: runFailed
    | Except.ok res =>
      let anames := res.types.map (·.name)
      let anidx : Name → Nat := fun m =>
        match res.types.find? (·.name == m) with
        | some t => cgmNPis t.type - min (cgmNPis t.type) v.numParams
        | none => nidx m
      let mut bad := 0
      for t in res.types do
        for c in t.ctors do
          let (_, nn, nv) := cgmWalkCtor lenv anames lvls v.numParams anidx 0 0 c.type
          bad := bad + nn + nv
      if bad = 0 then auxOk := auxOk + 1 else stillBad := n :: stillBad
  if runFailed.isEmpty && stillBad.isEmpty then
    logInfo s!"cgm/nested: {tried} safe blocks with a nested-shaped field; \
      ElimNestedInductive.run succeeded on all of them and ALL {auxOk} auxiliary blocks are \
      syntactically canonical -- so the guard is free at nested blocks provided it runs AFTER \
      elimination, and would reject all {tried} of them if it ran before ✓"
  else
    logInfo s!"cgm/nested: {tried} tried; run failed on {runFailed.length} \
      ({runFailed.take 20}); still non-canonical after elimination: {stillBad.length} \
      ({stillBad.take 20}); clean: {auxOk}"

end CGMScan3

/-! ### 4.4 The two blocks that are still non-canonical after elimination -/

namespace CGMScan4
open CGMGuard CGMScan CGMScan3

#eval show Lean.CoreM Unit from do
  let lenv ← getEnv
  let kenv := lenv.toKernelEnv
  let nidx : Name → Nat := fun n => match lenv.find? n with
    | some (.inductInfo w) => w.numIndices | _ => 0
  for n in [``Lean.Json, ``Lean.PrefixTreeNode] do
    let some (.inductInfo v) := lenv.find? n | continue
    let mut types : List InductiveType := []
    for m in v.all do
      let some (.inductInfo w) := lenv.find? m | continue
      let mut cs : List Constructor := []
      for c in w.ctors do
        let some cci := lenv.find? c | continue
        cs := cs ++ [{ name := c, type := cci.type }]
      types := types ++ [{ name := m, type := w.type, ctors := cs }]
    let lvls := v.levelParams.map Level.param
    match (ElimNestedInductive.run 10000 v.numParams types kenv).run'
        { lvls, newTypes := types.toArray } with
    | Except.error e => logInfo m!"cgm/two: {n}: run failed {e.toMessageData {}}"
    | Except.ok res =>
      let anames := res.types.map (·.name)
      let anidx : Name → Nat := fun m =>
        match res.types.find? (·.name == m) with
        | some t => cgmNPis t.type - min (cgmNPis t.type) v.numParams
        | none => nidx m
      logInfo m!"cgm/two: {n} np={v.numParams} aux members = {anames}"
      for t in res.types do
        logInfo m!"cgm/two:   member {t.name} : {t.type}  (nidx {anidx t.name})"
        for c in t.ctors do
          let (_, nn, nv) := cgmWalkCtor lenv anames lvls v.numParams anidx 0 0 c.type
          if nn + nv > 0 then
            logInfo m!"cgm/two:   BAD ctor {c.name} (nested {nn}, viol {nv}) : {c.type}"

end CGMScan4

/-! ## 5. **The redex-headed recursive field is manufactured by the kernel itself**

This is the round's decisive measurement, and it changes the pricing of both repairs.

`ElimNestedInductive.run` builds an auxiliary constructor's type by
`instantiateForallParams`, i.e. `Expr.instantiateRevRange` — a substitution that does **not**
β-reduce (C++'s `instantiate_pi_params` / `instantiate_rev` in `kernel/instantiate.cpp` is the
same plain `replace`).  So when a block nests through an inductive with a **dependent**
parameter `β : ι → Sort v`, and the nested instance supplies `β := fun _ => I`, every field of
the nested type whose stored type is `β k` becomes the β-redex `(fun _ => I) k` — a **recursive
field of the auxiliary block whose stored type is `.app`-headed**, which is exactly row 113's
witness shape.

`Lean.Json` and `Lean.PrefixTreeNode` are real instances: both nest through
`Std.DTreeMap.Internal.Impl (α) (β : α → Type v)`, whose `inner` constructor has a field `β k`.
§4.3's scan finds them and no others in the running environment.

`cgmDep`/`cgmJ` below is the same pattern from the **empty** environment, so the whole path is
executable and nothing is read out of a pre-built environment. -/

namespace CGMNestWit
open CGMGuard

/-- `inductive cgmDep (β : Prop → Type) : Type where | mk : (u : Prop) → β u → cgmDep β` -/
def cgmDepBlock : InductiveType :=
  { name := `cgmDep
    type := .forallE `β (.forallE `_a (.sort .zero) (.sort (.succ .zero)) .default)
      (.sort (.succ .zero)) .default
    ctors := [{ name := `cgmDep.mk
                type := .forallE `β (.forallE `_a (.sort .zero) (.sort (.succ .zero)) .default)
                  (.forallE `u (.sort .zero)
                    (.forallE `_f (.app (.bvar 1) (.bvar 0))
                      (.app (.const `cgmDep []) (.bvar 2)) .default) .default) .default }] }

/-- `inductive cgmJ : Type where | wrap : cgmDep (fun _ : Prop => cgmJ) → cgmJ` — a perfectly
ordinary nested inductive.  Its own field type is a saturated application of a foreign inductive
constant: **nothing the user writes is a redex**. -/
def cgmJBlock : InductiveType :=
  { name := `cgmJ
    type := .sort (.succ .zero)
    ctors := [{ name := `cgmJ.wrap
                type := .forallE `_w
                  (.app (.const `cgmDep [])
                    (.lam `x (.sort .zero) (.const `cgmJ []) .default))
                  (.const `cgmJ []) .default }] }

#eval show Lean.CoreM Unit from do
  let kenv := Kernel.Environment.empty `main
  -- 1. both blocks are accepted, from the empty environment, by lean4lean end to end
  let env1 ← match Environment.addInductive kenv [] 1 [cgmDepBlock] false false with
    | Except.error e => throwError "cgm/nestwit: cgmDep rejected ({e.toMessageData {}})"
    | Except.ok e => pure e
  let env2 ← match Environment.addInductive env1 [] 0 [cgmJBlock] false false with
    | Except.error e => throwError "cgm/nestwit: cgmJ REJECTED ({e.toMessageData {}}) -- \
        then the nested pattern is not accepted and this measurement is void"
    | Except.ok e => pure e
  unless (env2.find? `cgmJ.wrap).isSome do
    throwError "cgm/nestwit: cgmJ accepted but cgmJ.wrap not stored"
  -- 2. and `ElimNestedInductive.run` manufactures the redex-headed recursive field
  let .ok res := (ElimNestedInductive.run 10000 0 [cgmJBlock] env1).run'
      { lvls := [], newTypes := #[cgmJBlock] }
    | throwError "cgm/nestwit: ElimNestedInductive.run rejected cgmJ"
  let anames := res.types.map (·.name)
  let mut found := false
  for t in res.types do
    for c in t.ctors do
      -- look for a field whose stored type is `.app`-headed and whose head-beta is a block member
      let rec fields : Expr → List Expr
        | .forallE _ dom body _ => dom :: fields body
        | _ => []
      for dom in fields c.type do
        if dom.isApp && !dom.getAppFn.isConst then
          let hb := dom.headBeta
          if anames.contains (hb.getAppFn.constName?.getD Name.anonymous) then
            found := true
            logInfo m!"cgm/nestwit: aux ctor {c.name} has field {dom} -- stored `.app`-headed, \
              head-beta {hb}, a member of the auxiliary block {anames}"
  unless found do
    throwError "cgm/nestwit: no redex-headed recursive field in \
      {res.types.map fun t => t.ctors.map (·.type)} -- either `instantiateRevRange` now \
      β-reduces or the nesting no longer fires; §5's whole account must be rechecked"
  -- 3. the candidate guard of §3 rejects it, i.e. would reject `cgmJ` -- and `Lean.Json`
  let nidxA : Name → Nat := fun _ => 0
  let mut rejected := false
  for t in res.types do
    for c in t.ctors do
      let rec fields2 (d : Nat) : Expr → List (Nat × Expr)
        | .forallE _ dom body _ => (d, dom) :: fields2 (d + 1) body
        | _ => []
      for (d, dom) in fields2 0 c.type do
        unless cgmSynPos anames [] 0 nidxA d dom do rejected := true
  unless rejected do
    throwError "cgm/nestwit: the §3 guard ACCEPTS the auxiliary block -- then §5's conclusion \
      that the guard rejects Lean.Json is wrong"
  logInfo "cgm/nestwit: cgmDep and cgmJ are both accepted from the EMPTY environment; \
    ElimNestedInductive.run manufactures a recursive field whose stored type is a β-redex; and \
    the §3 syntactic guard REJECTS the auxiliary block.  So the guard would reject Lean.Json and \
    Lean.PrefixTreeNode, and row 113's witness shape is produced by the kernel itself rather \
    than only by a hand-written block ✓"

end CGMNestWit

/-! ## 6. The mechanism, as a theorem rather than as prose

Row 113 argues: `TrIndDecl.trCtors` forces the field's `F.type` to be the redex; `D.Canonical`
then excludes `F.recArg = some r`; so `VIndField.WF.pos`'s `none` branch has to supply a
block-free `A` definitionally equal to it, which is false but needs Church–Rosser strength.

The middle two steps are proved below, at the `VIndField.WF` level where `Canonical` and `pos`
actually meet — so the conditional refutation is a theorem with **one** named escape, rather than
an argument.  The `rrc_canonType_ne_app` the ledger cites is not in the tree (it lived in a
deleted scratch file); `cgm_canonType_ne_redex` is its replacement, and it is **stronger**: it
needs neither `D.np = 0` nor `r.args = []`, because the obstruction is the *spine head*
(`.const`, always) rather than the arity. -/

namespace CGMAbstract

/-- The spine head of an application. -/
def cgmSpineFn : VExpr → VExpr
  | .app f _ => cgmSpineFn f
  | e => e

theorem cgm_spineFn_mkApp : ∀ (l : List VExpr) (f : VExpr),
    cgmSpineFn (VExpr.mkApp f l) = cgmSpineFn f
  | [], _ => rfl
  | a :: as, f => cgm_spineFn_mkApp as (.app f a)

/-- The `VExpr` the witness's stored field type translates to:
`(fun x : Type => cgmT) Prop`. -/
def cgmRedexV : VExpr :=
  .app (.lam (.sort (.succ .zero)) (.const `cgmT [])) (.sort .zero)

/-- **A canonical recursive-field type is never the redex** — at *any* `D.np` and *any*
`r.args`, because `VIndRecArg.canonType` is either `.forallE`-headed (nonempty `ξ`) or a
`.const`-headed application spine, and the redex is neither. -/
theorem cgm_canonType_ne_redex (D : VInductDecl') (r : VIndRecArg) (i : Nat) :
    r.canonType D i ≠ cgmRedexV := by
  cases hb : r.binders with
  | cons A As => rw [VIndRecArg.canonType, hb, VExpr.mkPi]; exact fun h => by cases h
  | nil =>
    rw [VIndRecArg.canonType, hb, VExpr.mkPi, VIndRecArg.canonResult, VInductDecl'.tyApp]
    intro h
    have := cgm_spineFn_mkApp (VExpr.bvars (r.binders.length + i) D.np ++ r.args)
      (.const (D.types.getD r.idx default).name D.ownLvls)
    rw [h] at this
    simp [cgmSpineFn, cgmRedexV] at this

/-- **The only escape.**  A block-free `VExpr` definitionally equal, *as a type*, to the stored
redex.  Since the redex reduces to the freshly declared block constant, this says a block-free
term is convertible with a constant that has no rules and no definition — which the tree wants
false, and refuting it is Church–Rosser strength. -/
def CGMEscape (env : VEnv) (D : VInductDecl') (Γ : List VExpr) : Prop :=
  ∃ A, D.NoBlock A ∧ env.IsDefEqType D.uvars Γ cgmRedexV A

/-- **Row 113's mechanism, machine-checked.**  Given only that the field's stored type *is* the
redex (which `TrIndDecl.trCtors` forces, `VIndCtor.type` being the stored type on the nose and
`TrExprS` having no defeq slack) and that the constructor is `VIndCtor.Canonical` at that field,
`VIndField.WF` forces `CGMEscape`.  So the residue is false unless `CGMEscape` holds. -/
theorem cgm_wf_forces_escape {env : VEnv} {D : VInductDecl'} {pre : List VIndField}
    {Γ : List VExpr} {i : Nat} {F : VIndField}
    (hcanon : ∀ r, F.recArg = some r → F.type = r.canonType D i)
    (hred : F.type = cgmRedexV) (h : VIndField.WF env D pre Γ i F) :
    CGMEscape env D Γ := by
  have hnone : F.recArg = none := by
    match hr : F.recArg with
    | none => rfl
    | some r => exact absurd ((hcanon r hr).symm.trans hred) (cgm_canonType_ne_redex D r i)
  have := h.pos
  rw [hnone] at this
  obtain ⟨A, hA, hdef⟩ := this
  exact ⟨A, hA, hred ▸ hdef⟩

/-- Instrument 7's dual for §6: `CGMEscape` is not something the guard-free statement gets for
free — but neither is it refuted here.  What *is* proved is that it is the **sole** residue. -/
theorem cgm_escape_is_sole {env : VEnv} {D : VInductDecl'} {pre : List VIndField}
    {Γ : List VExpr} {i : Nat} {F : VIndField}
    (hcanon : ∀ r, F.recArg = some r → F.type = r.canonType D i)
    (hred : F.type = cgmRedexV) (hesc : ¬ CGMEscape env D Γ) :
    ¬ VIndField.WF env D pre Γ i F :=
  fun h => hesc (cgm_wf_forces_escape hcanon hred h)

/-- **`VIndCtor.Canonical` is false at any constructor with a redex-headed recursive field.**
§4.3/§5 exhibit one in the *auxiliary* block `ElimNestedInductive.run` builds for `Lean.Json`,
so this fires at a real Lean-library declaration and not only at §1's hand-written block.

The dichotomy this leaves is worth stating, because the second horn is currently invisible:
either `D` records the field as recursive — and then `Canonical` is false, by this theorem — or it
records `recArg = none` — and then §6's `CGMEscape` is owed *and* the recursor shape is wrong,
because the checker's `isRecArg` does emit an induction hypothesis for that field while a `D` with
`recArg = none` does not.  Nothing sees the second horn today only because
`AddInductStages`' recursor fold has no `RecShape` (ledger row 113c). -/
theorem cgm_not_canonical {D : VInductDecl'} {C : VIndCtor} {i : Nat} {F : VIndField}
    {r : VIndRecArg} (hF : C.fields[i]? = some F) (hr : F.recArg = some r)
    (hred : F.type = cgmRedexV) : ¬ C.Canonical D :=
  fun h => cgm_canonType_ne_redex D r i ((h i F r hF hr).symm.trans hred)

end CGMAbstract

#print axioms Lean4Lean.CGMGuard.cgm_synPos_iff
#print axioms Lean4Lean.CGMAbstract.cgm_canonType_ne_redex
#print axioms Lean4Lean.CGMAbstract.cgm_wf_forces_escape
#print axioms Lean4Lean.CGMAbstract.cgm_escape_is_sole
#print axioms Lean4Lean.CGMAbstract.cgm_not_canonical
#print axioms Lean4Lean.CGMRedexWit.cgm_blockClosed

end Lean4Lean
