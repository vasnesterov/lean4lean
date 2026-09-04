# handoff-surfacemap

Owned files this round: `Lean4Lean/Verify/Inductive/SurfaceMap.lean` (new), this doc.
Read-only otherwise. Concurrent streams own `Verify/Inductive/FragmentWiden.lean`
and `Theory/Typing/SEReduce.lean`.

## Priors (written BEFORE the first measurement)

Target handed down: a map
`Lean4Lean.ElimNestedInductive.Result.types -> Lean4Lean.VInductDecl'`
satisfying `D.nameSkelV = surfNameSkel rtypes`.

P1. I expect `surfNameSkel` to be a *names-only* skeleton (list of names,
    or list of (name, list-of-ctor-names)). If so the equation is decidable by
    `rfl`/`simp` on a concrete example and provable by `List.map` congruence in
    general. CONFIDENCE: high on shape, medium on it being literally `List Name`.
P2. I expect the absence claim (no `List InductiveType -> VInductDecl'` etc.)
    to hold, because the handed-down reason is structural: the `TrExpr`-style
    relation's app constructor carries typing premises, so no purely syntactic
    total function into the translated world can exist. CONFIDENCE: high.
P3. I therefore expect the map to be *partial* (`Option`-valued), mirroring
    `Lean4Lean.ctorTr?`, and to thread a `ConstLookup`. The name skeleton half
    should nonetheless be *total-in-the-success-case* and independent of the
    typing output — i.e. `nameSkelV` should be computable from the surface names
    alone, so the skeleton equation holds even though the type half is `Option`.
    CONFIDENCE: medium-high. RISK: if `nameSkelV` mentions translated types,
    the equation is entangled with the typing output and (b) gets much harder.
P4. Three fields to discharge: `trType`, `trCtors`, `trCtorsLen`. Prior: the
    existing `Lean4Lean.trCtorsLen_of_skelPrefix` (arity 3) does `trCtorsLen`
    + `ctorName_own` + name half of `trType`; my map must supply its `List`
    equation. CONFIDENCE: medium — I have not yet read its statement.
P5. Arity-0 witness at `Lean4Lean.InductiveDeclExamples.ntreeAux`: I expect
    `ntreeAux` to be the *auxiliary* (un-nested) inductive produced by
    `ElimNestedInductive` on `ntree`, hence exactly the interesting input.
    CONFIDENCE: medium.
P6. Import closure: I expect to need only the module defining `ctorTr?`/
    `VInductDecl'`/`surfNameSkel` plus the examples module. RISK: examples
    module may itself import the hand-built-instance modules, defeating
    structural exclusion. CONFIDENCE: low — must measure.
P7. Round-close: census 13 / NOT BUILT 0 is the current state; I expect my file
    to add 0 sorries. CONFIDENCE: high (I intend no sorries).

## Measurements (appended as made)

### M1 (P1 confirmed, exactly). `surfNameSkel` / `nameSkelV` are names-only.
`Lean4Lean/Verify/Inductive/CtorsLenGeneral.lean:154,159`:
```
def surfNameSkel (l : List InductiveType) : List (Name × List Name) :=
  l.map fun t => (t.name, t.ctors.map (·.name))
def VInductDecl'.nameSkelV (D : VInductDecl') : List (Name × List Name) :=
  D.types.map fun T => (T.name, T.ctors.map (·.name))
```
So the skeleton equation reads NOTHING but `VIndType.name` and `VIndCtor.name`.
CONSEQUENCE (P3 confirmed and sharpened): the skeleton half is *independent of the
typing output*. A map may be `Option`-valued for the content and the skeleton
equation still holds unconditionally on success, by `List.mapM` length+pointwise.

### M2. `SkelPrefix` = `∃ tail, D.nameSkelV = surfNameSkel types ++ tail`
(`CtorsLenGeneral.lean:166`). My target's `= surfNameSkel rtypes` is the
`tail = []` case, which is strictly stronger, so it implies `SkelPrefix` and
therefore all three of §2's consequences.

### M3. Fields' precise asks (measured, not assumed).
- `trType`: `Lean4Lean.trIndType_of_ctorTr` (`Verify/Inductive/FlipWiring.lean:144`)
  wants `t.name = T.name` and `ctorTr? Γc Us t.type [] = some (T.type, t')`.
  So `VIndType.type := (ctorTr? ...).1` is EXACTLY what the producer wants. Easy.
- `trCtors`: `trCtors_of_ctorTr` (`TrIndDeclNProducer.lean:85`) wants
  `ctorTr? Γc Us c.type [] = some (C.typeR D R j, t')` — the *derived* `VIndCtor.typeR`,
  not a stored field. RISK, now the central one: the ctor side is an INVERSION
  (decompose a `VExpr` pi-telescope into `params`/`fields`/`args`), not a copy.
- `trCtorsLen`: via `trCtorsLen_of_skelPrefix`, names only.

### M4 (P2 CONFIRMED). Absence re-verified with `shape.lean`, three head pairs.
Population 454 built modules each time.
- `HEADS="Lean.InductiveType Lean4Lean.VInductDecl'"` -> 202 hits, 50 of them
  structure fields. Every non-field hit is `Prop`-valued (`TrCtorsLen`,
  `SkelPrefix`, `CtorNamesAgree`, `TrIndDecl`, `SpineHargsN`, `RestoreData`, the
  refutations, auto-generated `rec`/`recOn`/`casesOn`/`match_*`).
- `HEADS="Lean.InductiveType Lean4Lean.VIndType"` -> same, all `Prop` or auto-gen.
- `HEADS="Lean.Constructor Lean4Lean.VIndCtor"` -> same.
CONCLUSION: **no data-producing function from the surface to the abstract records
exists anywhere in the tree.** Absence stands, now against the compiled
environment and not by grep.
(Also note the first run: `HEADS="InductiveType VInductDecl'"` printed
`HEAD NOT A CONSTANT` and 0 hits -- unqualified heads are not evidence.)

### M5 (P6 REFUTED, and this reshaped the design). Import closures, measured.
- `Lean4Lean.Verify.Inductive.CtorsLenGeneral` closure = **147** modules;
  `NestedRestoreWit`, `AddDeclWF`, `ValAtParam`, `NestedRunInvariant` all OUT.
- `Lean4Lean.Verify.Inductive.FlipWiring` closure = **198**; it pulls in
  `NestedRestoreWit`, `AddDeclWF`, `ValAtParam`, `NestedRunInvariant`,
  `NestedRestore`, `Verify.TypeChecker.*` -- because `TrExprSGeneral` sits on
  `ExprConstructionScope`, which imports `ValAtParam`.
So `ctorTr?` is **not reachable under structural exclusion**: any file that can
cite `ctorTr?` also sees four hand-built-instance modules.
DESIGN CONSEQUENCE: the map takes the translation as an **oracle parameter**
`tr : Expr -> Option VExpr` and the typing as per-node `TrExprS` *inputs*.
Then the file imports exactly ONE module (`CtorsLenGeneral`, 147) and the
`ctorTr?` instantiation happens one module downstream, where
`trExprS_of_ctorTr` is citable. Verified with `can-cite.py` below.

### M6 (a miss in my priors, caught by the elaborator not by me).
I wrote the two decompositions and their round-trip lemmas as new §1. The build
said `Lean4Lean.VExpr.peelPis has already been declared`. All four already exist
and are citable at my position (`scripts/can-cite.py`, consumer
`Lean4Lean.Verify.Inductive.CtorsLenGeneral`, closure 147):
- `Lean4Lean.VExpr.peelPis`  -- `Lean4Lean.Theory.Typing.PatternDecode`  YES
- `Lean4Lean.VExpr.spine`    -- `Lean4Lean.Theory.Typing.PatternDecode`  YES
- `Lean4Lean.VExpr.mkApp_spine` -- `Lean4Lean.Theory.Typing.PatternDecode` YES
- `Lean4Lean.VExpr.mkPi_peelPis` -- `Lean4Lean.Theory.Typing.PatWFIota`   YES
§1 deleted; the map uses the tree's. RULE FOR NEXT ROUND: run `shape.lean` on the
*helper* shapes too, not only on the headline shape. I ran it on
`InductiveType x VInductDecl'` and never on `VExpr x VExpr`.

### M7. §1-§3 GREEN. The skeleton equation is proved and needs no typing:
`Lean4Lean.nameSkelV_surfInductDecl?` : `surfInductDecl? tr uvars ps lvl isLE rtypes = some D
-> D.nameSkelV = surfNameSkel rtypes`, and `Lean4Lean.skelPrefix_surfInductDecl?`
gives `SkelPrefix rtypes D` with `tail = []`.

### M8. THE MAP EXISTS. §4 (reassembly) and §5 (the three fields) GREEN.
`Lean4Lean.surfInductDecl? (tr : Expr -> Option VExpr) (uvars : Nat) (ps : List VExpr)
(lvl : VLevel) (isLE : Bool) (rtypes : List InductiveType) : Option VInductDecl'`
(arity 6, cone 730, no hole, cone reaches sorryAx: false).
A constructor's abstract record is read off its *translated* type:
`peelPis` -> first `np` binders are `C.params`, the rest are `C.fields`
(`recArg := none`, `lvl := D.lvl`), and the target's spine, after the `bvars`
naming the parameters, is `C.args`. Three decidable guards. The map COMPUTES.

`Lean4Lean.typeR_surfIndCtor?` (arity 15, cone 1748): `C.typeR D D.idRestore j = ct`
-- the produced record reassembles, at the identity restoration, to the very
expression the oracle returned. That is exactly the input
`Lean4Lean.trIndCtorR_iff_of_ctorTr` asks a `VIndCtor` for.

### M9. Which fields the skeleton equation discharges, measured through existing lemmas.
- `TrCtorsLen` : `Lean4Lean.trCtorsLen_surfInductDecl?` (cone 1069) =
  `trCtorsLen_of_skelPrefix` o `skelPrefix_surfInductDecl?`. NOT re-proved.
- `CtorNameOwn` : `Lean4Lean.ctorNameOwn_surfInductDecl?` = `ctorNameOwn_of_skelPrefix`. Free.
- `trType`'s name half : `Lean4Lean.name_eq_of_skelPrefix`, applied. Free.
- `trType` (both halves) : `Lean4Lean.trType_surfInductDecl?` (cone 1017), needs
  `OracleSound tr env Us`.
- `trCtors` : `Lean4Lean.trCtors_surfInductDecl?` (cone 1914), staged over
  `env.addIndTypesC D K = some env₁` exactly as the field is, needs
  `OracleSound tr env₁ Us` per staged environment.
So ONE `List` equation gives three fields free and the other two need only the
oracle. `length` (`D.types.length = rtypes.length`) is `length_surfInductDecl?`.

### M10 (a boundary, measured with `can-cite.py`, and it is Claim B not Claim A).
`OracleSound tr env Us := forall e e', tr e = some e' -> TrExprS env Us [] e e'`
is `Lean4Lean.trExprS_of_ctorTr`'s conclusion **verbatim** (checked at
`Verify/Inductive/TrExprSGeneral.lean:224`), so
`tr := fun e => (ctorTr? Gc Us e []).map (.1)` discharges it from a `ConstLookup`.
BUT `can-cite.py` says, both directions:
- consumer `Lean4Lean.Verify.Inductive.SurfaceMap` (closure 148):
  `Lean4Lean.ctorTr?` NO, `Lean4Lean.trExprS_of_ctorTr` NO,
  `Lean4Lean.trIndCtorR_iff_of_ctorTr` NO -- would have to gain `TrExprSGeneral`.
- consumer `Lean4Lean.Verify.Inductive.TrIndDeclNProducer` (closure 207):
  `Lean4Lean.nameSkelV_surfInductDecl?` NO, `Lean4Lean.typeR_surfIndCtor?` NO,
  `Lean4Lean.OracleSound` NO -- would have to gain `SurfaceMap`.
Both NO, symmetrically => **no cycle**: a NEW module importing both closes it in
one lemma. I do not own such a module, so the composition is NOT done this round.
This is the one place where I did not "discharge through the existing lemma":
`trIndType_of_ctorTr` / `trCtors_of_ctorTr` are uncitable at my position, so §5
discharges `trType`/`trCtors` through `TrIndType`/`TrIndCtorR`'s own definitions
with `OracleSound` as the input. The content is the same; the wiring is one import.

### M11. Structural exclusions, measured (not hand-listed).
`SurfaceMap` imports exactly ONE module; closure **148** (= `CtorsLenGeneral`'s 147 + itself).
**32 modules in the tree mention `TrIndDeclN` / `TrIndCtorR` / `TrIndType`.
My closure contains 3 of them** (`Verify.Environment.Induct`,
`Verify.Environment.InductR`, `Verify.Inductive.CtorsLenGeneral`) -- all three
unavoidable, all three disclosed. **28 excluded**, including every hand-built-instance
holder: `NestedRestoreWit`, `AddDeclWF`, `StagesFiring`, `CtorPointwise`,
`TrIndDeclNProducer` (the ntreeAux hand-built trType/trCtors -- §6's own block),
`TrExprSGeneral`, `FlipWiring`, `FragmentWiden`, `FlipConstruct`, `TrTypeProducer`,
`TrSpineProducer`, `TrIndDeclNCtorOwn`, `ValAtParam`, `NestedRunInvariant`,
`NestedRestore`, `RestoreFaithful`, `RunIdentity`, `SpineClause`, ...
Also disclosed and not droppable: `Theory.Inductive.NestedHead` (declares `ntreeAux`,
`NTree`), `Theory.Typing.PatternDecode` + `Theory.Typing.PatWFIota` (§1's
decompositions).

### M12. THE ARITY-0 WITNESS.
`Lean4Lean.InductiveDeclExamples.ntreeAux_surfaceMap_witness` -- arity **0**, cone
**2063**, own value is a hole: **false**; cone reaches sorryAx: **false**;
watched declarations in cone: **none of 6**.
Reached through the map. The single block-specific input is
`Lean4Lean.InductiveDeclExamples.ntreeRTypes_maps` (arity 0, cone 814):
```
surfInductDecl? (vtr? [`u]) 1 [.sort (.succ (.param 0))] (.succ (.param 0)) true
  ntreeRTypes = some (eraseRecArgs ntreeAux)   -- by rfl
```
i.e. **the map reproduces `ntreeAux` on the nose up to `recArg`**: every member
name, stored type and `indices`, and every constructor's `name`, `params`, `fields`
(types AND universes) and `args` agree with `NestedHead.lean`'s hand-written block.
The witness then carries, at `ntreeAux` ITSELF (not at the erasure):
`nameSkelV = surfNameSkel ntreeRTypes`, `SkelPrefix`, `TrCtorsLen`, `CtorNameOwn`,
the name half, `trType` and `trCtors` -- the last two quantified over an arbitrary
`env`/`Us`/`K` and an arbitrary sound oracle, so no typing is assumed at a fixed
environment. Plus the four anti-`nfnAux` non-degeneracy facts and anti-vacuity at
`j = 0` and `j = 1`.
NEGATIVE CONTROLS (both in the bundle):
1. `ntreeAux_not_nameSkelV_dbl` : duplicate the surface constructor and the skeleton
   equation FAILS -- so §3 is not slack.
2. `ntreeRTypesRenamed_fails` : rename the auxiliary member without renaming the
   occurrences of it inside the constructor types and **the map returns `none`** --
   `surfIndCtor?`'s target-head guard fires. A map that merely copied names would
   have succeeded. (This is a control on the MAP, not on the premise.)
GAP, machine-checked in the bundle rather than asserted: `ntreeNode.recFields.length = 1`
while the map's constructor has `0`. `recArg` is the one datum the map does not
recover, and no field of `TrIndDeclN` can see it.

### M13. Round-close numbers.
- whole-tree `lake build`: **Build completed successfully (1643 jobs)**.
- `scripts/sorry-census-all.lean --run`: on disk 484, population 460,
  **BUILT 460; NOT BUILT 0**; **HOLES 13** (pass A 13, pass B 0). Unchanged by this round.
- guard 1: 24 frozen axioms OK. guard 2: within whitelist OK (proof INCOMPLETE,
  sorryAx present -- unchanged). guard 3: 2/2 implementation gaps OK.
- in-repo `automatically included section variable` warnings: **0**
  (the one in the build log is `Foundation/FirstOrder/SetTheory/Z.lean`, external).
- `python3 scripts/layer-check.py`: **exit 0**, hard rule ok (66 modules), soft
  report unchanged (4 Theory files with direct Verify imports, none mine).
- `SurfaceMap.lean`: 0 sorries, 0 warnings, 36 `#print axioms` lines, every one
  `[propext, (Classical.choice,) Quot.sound]` or none -- **no `sorryAx` anywhere**.

## Claim A / Claim B

**CLAIM A (closed before this round, and this round does not touch it).**
All twelve fields of `Lean4Lean.TrIndDeclN` have general producers. Commit 2118e0e.
Nothing here weakens or re-opens it. This round is entirely about Claim B.

**CLAIM B (the assembled theorem's hypotheses jointly dischargeable).**
Moved this round:
- B1 CLOSED: *a map from `ElimNestedInductive.Result.types` to a `VInductDecl'` with
  `D.nameSkelV = surfNameSkel rtypes`.* `Lean4Lean.surfInductDecl?` +
  `Lean4Lean.nameSkelV_surfInductDecl?`. The equation, not a prefix with unknown tail.
- B2 CLOSED: *the reassembly.* `Lean4Lean.typeR_surfIndCtor?` --
  `C.typeR D D.idRestore j = ct`.
- B3 CLOSED: `trCtorsLen`, `ctorName_own`, `trType`'s name half at the map's output,
  through `CtorsLenGeneral` §2 and not re-proved.
- B4 CLOSED modulo one import: `trType`, `trCtors` at the map's output, from
  `OracleSound` alone.
Still open, and none of it is Claim A:
- B5 **the composition with `ctorTr?`**: one lemma
  `ConstLookup Gc env -> OracleSound (fun e => (ctorTr? Gc Us e []).map (.1)) env Us`,
  in a NEW module importing both `SurfaceMap` and `TrExprSGeneral`. Measured to be
  cycle-free (M10). I do not own such a module.
- B6 **the restoration**: §4/§5 are at `D.idRestore`, which is right for the
  post-elimination list. Relating the USER's block to the same `D` needs the real
  restoration (`ntreeRestore` at `ntreeAux`) -- `TrIndCtorR`'s `R.ctorName` and
  `R.tyName`/`tyLvls`/`tyArgs` are then not the identity. Untouched here.
  The NAME side of the composition IS done: `skelPrefix_of_surfInductDecl?_run`
  chains with `runSkelExtends` by `rfl` (`surfNameSkel` is `nameSkel`'s body verbatim).
- B7 **`recArg`**: the map sets it to `none`. Invisible to all twelve fields
  (`VIndField.typeR_id`), load-bearing for `VInductDecl'.WF`. `isRecArg`'s job.
- B8 `D.params` / `D.lvl` / `D.isLE` are *inputs* to the map because `TrIndDeclN`
  does not pin them; `VInductDecl'.WF` does. Not a gap in the relation, a gap in WF.
- B9 the other seven fields (`safe`, `uvars`, `np`, `companions`, `trSpine`,
  `recName_own`, `recName_aux`) are Claim A's and were not re-examined here.
