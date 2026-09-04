# handoff-layering — cutting the `Verify/` → deepest-`SetModel/` import inversion

Round opened 2026-09-04. Scope: surgical refactor with a verification bar.

Owned files: `Lean4Lean/Theory/Typing/StructEtaPrice.lean`,
`Lean4Lean/Theory/SetModel/RecTypePeel.lean`, new files under
`Lean4Lean/Theory/SetModel/` or `Lean4Lean/Theory/Inductive/`, and this file.
`Verify/` is untouched; `Verify/{Soundness,Axioms,Guard}.lean` frozen.

## 0. Priors, written before the first measurement

Recorded now so that the measurements can contradict them.

1. **The move is probably possible.** The brief says `RecTypePeel.lean` imports
   `StructEtaPrice.lean` *solely* for `Lean4Lean.SetModel.eq_singleton_of_recProp`, and that
   declaration is namespaced `SetModel` — a `SetModel`-namespace lemma living in
   `Theory/Typing/` is prima facie a lemma that was parked in the wrong file for import
   convenience, not one that needs the eta/`Verify` machinery. Prior: 70% movable.
2. **The likely obstruction, if any, is not `Verify/` proper but the *purpose* of
   StructEtaPrice.** That file exists to *price* a fourteenth `IsDefEq` constructor by
   measuring against `Verify/TypeChecker/EtaUnitRefute.lean`. If `eq_singleton_of_recProp` was
   proved *using* the private copy of the relation declared in StructEtaPrice, or using an
   `EtaUnitRefute` counterexample environment (`MutField.unitEnv`), the move fails. Prior:
   25% that some `Verify/`-rooted constant is in the transitive term dependency set.
3. **The lowest destination is probably `Theory/SetModel/UnitOracleLarge.lean`'s level or
   below**, since StructEtaPrice already imports `Theory.SetModel.UnitOracleLarge`; anything
   `eq_singleton_of_recProp` needs from the `SetModel` side is most likely available there. I
   expect to create a *new* file under `Theory/SetModel/` rather than editing
   `UnitOracleLarge.lean` (not owned).
4. **The cone number will change even on a successful move.** Cone 5826 is measured against
   whatever the module's import closure is; moving the declaration into a smaller closure
   should *shrink* or leave the cone equal, never grow it. Axiom set must be identical, and
   `sorryAx`-free / `none of 6` watched must hold. Prior: axioms identical, cone ≤ 5826.
5. **The other three inversions are likely the same shape and equally cuttable**, but only
   `StructEtaPrice` reaches the deepest layer, so they are lower priority.
   `CommutationLemmas.lean` (0 importers) is likely *deletable-or-movable at zero cost* and is
   the cheap test case. `EtaGuardLand.lean` and `NoConfRepair.lean` import `Verify.Typing.*`
   guard/inv lemmas that are plausibly *genuinely* `Verify`-level, in which case the fix there
   is not a move but keeping them out of `SetModel`'s cone — which they already are.
6. **Risk I most expect to bite:** `lake build` of the whole tree is slow, and a
   dependency-set measurement done by grep will be wrong. Everything below is computed from
   the built `.olean` population / `#print axioms` / a term-level constant walk, not grepped.

## 1. Measurements (appended as made)

### M1 — the inversion census, recomputed (2026-09-04)

`grep -rln 'import Lean4Lean.Verify' Lean4Lean/Theory/` returns **five** files, but one is a
false positive: `Lean4Lean/Theory/Typing/PatAppParams.lean:81` is a *comment*
(`-- needs \`import Lean4Lean.Verify.QuotConsts\`, so it cannot live in \`Theory/\``) — a note
explaining why a lemma was *not* put there. Anchoring the pattern to line start
(`grep -n '^import Lean4Lean.Verify'`) gives the brief's **four**. Confirmed.

| inverted file | `Verify.*` imports | direct importers |
|---|---|---|
| `Theory/Typing/EtaGuardLand.lean` | `Verify.Typing.NoConfGuard` | `Theory/Typing/ConstAppInvSIProof.lean`, `Theory/Typing/ConfluenceRebuildPrice.lean` |
| `Theory/Typing/StructEtaPrice.lean` | `Verify.TypeChecker.EtaUnitRefute` | `Theory/Typing/ConfluenceRebuildPrice.lean`, `Theory/Typing/NoConfRepair.lean`, `Theory/Typing/SEReerectionScope.lean`, **`Theory/SetModel/RecTypePeel.lean`** |
| `Theory/Typing/CommutationLemmas.lean` | `Verify.TypeChecker.EtaStructG`, `Verify.Typing.ProjGenLift`, `Verify.Typing.ProjGenInst`, `Verify.Typing.ProjClosedG` | none |
| `Theory/Typing/NoConfRepair.lean` | `Verify.Typing.ProjSpineInv` | `Theory/Typing/EtaGuardLand.lean` |

### M2 — the dependency set of `Lean4Lean.SetModel.eq_singleton_of_recProp`

Computed, not grepped: a term-level constant walk (type + value, transitively) over the
environment obtained by `importModules [Lean4Lean.Theory.Typing.StructEtaPrice]`, with each
cone member attributed to its defining module via `Environment.getModuleIdxFor?`.

- cone **5826** constants over **219** defining modules, 0 unattributed
- **`Lean4Lean.Verify.*` constants in the cone: 0**
- `sorryAx` in cone: **false**
- axioms in cone (3): `Quot.sound`, `Classical.choice`, `propext`

Only **five** `Lean4Lean` modules appear in the cone at all (the other 214 are Lean core,
Std, Mathlib and Foundation):

| defining module | constants in cone |
|---|---|
| `Lean4Lean.Theory.SetModel.Universe` | `Lean4Lean.SetModel.UProp`, `Lean4Lean.SetModel.pt`, `Lean4Lean.SetModel.mem_UProp_iff` |
| `Lean4Lean.Theory.SetModel.Interp` | `Lean4Lean.SetModel.mkLam`, `Lean4Lean.SetModel.mkLam._proof_1`, `Lean4Lean.SetModel.mem_mkLam_iff` |
| `Lean4Lean.Theory.SetModel.InterpSound` | `Lean4Lean.SetModel.mkLam_value`, `Lean4Lean.SetModel.mkLam_mem_function` |
| `Lean4Lean.Theory.SetModel.Rank` | `Lean4Lean.SetModel.value_eq_of_kpair_mem` |
| `Lean4Lean.Theory.Typing.StructEtaPrice` | `Lean4Lean.SetModel.charBody`, `Lean4Lean.SetModel.charBody._proof_1`, `Lean4Lean.SetModel.charBody_definable`, `Lean4Lean.SetModel.constDom_definable`, `Lean4Lean.SetModel.charFam`, `Lean4Lean.SetModel.charFam_value`, `Lean4Lean.SetModel.charFam_mem_pow`, `Lean4Lean.SetModel.eq_singleton_of_recProp` |

**Verdict: the move is possible.** Prior 1 (70% movable) confirmed; prior 2 (25% chance of a
`Verify/`-rooted obstruction) refuted by measurement — the obstruction is zero. The
declaration never touched `EtaUnitRefute`, `MutField.unitEnv`, or the private `IsDefEqSE`
relation; it was parked in `StructEtaPrice.lean` for narrative adjacency (§8 of that file's
argument) and nothing else.

The six helpers to move with it are exactly the seven-minus-one `StructEtaPrice` rows above.
`Lean4Lean.SetModel.mkForallType_const_eq_pow` and `Lean4Lean.SetModel.recProp_at_singleton`
are in the same `§8` section but are **not** in the cone; a tree-wide usage scan
(`grep -rn` over `Lean4Lean/`, excluding `StructEtaPrice.lean` itself) finds **zero** external
users of either, and zero external users of any of the six helpers. The only external
reference to anything in the section is `Theory/SetModel/RecTypePeel.lean:429`
(`refine eq_singleton_of_recProp hmk (fun m hm hpt x hx ↦ ?_)`).

### M3 — destination: the lowest module that carries the four dependencies

Textual import-closure computation over `Lean4Lean/**.lean`:

- `Lean4Lean.Theory.SetModel.InterpSound` — closure 21 modules, **Verify.\* entries: 0**, and
  it already carries all four of `SetModel.Universe`, `SetModel.Interp`,
  `SetModel.InterpSound`, `SetModel.Rank`.
- `Lean4Lean.Theory.SetModel.SoundInduction` — closure 23, Verify.\*: 0, also carries all four
  (it imports `InterpSound`), and is already `RecTypePeel.lean`'s first import.

So a **single** `import Lean4Lean.Theory.SetModel.InterpSound` suffices for the moved block:
that is the lowest point in the chain that has everything, and it reaches no `Verify/`.

### M4 — `RecTypePeel.lean`'s import closure, BEFORE

- `Lean4Lean.Theory.SetModel.RecTypePeel`: closure **154** `Lean4Lean` modules,
  **`Verify.*` entries: 46**.
- `Lean4Lean.Theory.Typing.StructEtaPrice`: closure **150**, **`Verify.*` entries: 46** — the
  identical 46. So `StructEtaPrice` is the whole story: RecTypePeel's other three imports
  (`SetModel.SoundInduction`, `Theory.Inductive.Decl`, `Theory.Inductive.NestedHead`) must
  contribute none, verified next.

### M5 — `RecTypePeel.lean` uses no `Verify.*` constant at all

Union cone over all **91** declarations defined in
`Lean4Lean.Theory.SetModel.RecTypePeel`: 8347 constants,
**`Verify.*` constants used transitively: 0**, `sorryAx` in the union cone: false (the module
does contain `sorry`-carrying declarations, e.g. `SetModel.UnitAudit.unitDeclLE_recPiTele`, but
they were already there — see the census line at round close).

So the whole 46-module `Verify/` sub-closure was dead weight arriving through one import edge.

Also measured: `Theory/Inductive.Decl` (closure 9) and `Theory/Inductive/NestedHead` (closure
37) contribute **0** `Verify.*` each, and `SetModel/SoundInduction` (closure 23) likewise — so
`StructEtaPrice` was the *only* route, as M4 predicted.

Cross-check that RecTypePeel needs nothing else from `StructEtaPrice`: `IsDefEqSE` occurs 0
times in the file, `HasArgsSE` 0 times. Of the 77 declarations `StructEtaPrice` defines, the
only one `RecTypePeel` references is `SetModel.eq_singleton_of_recProp`, at line 429
(`refine eq_singleton_of_recProp hmk (fun m hm hpt x hx ↦ ?_)`).

*(A first pass at this check matched by last name component and produced 23 spurious hits —
`IsDefEqSE.cons`, `.nil`, `.rec`, `.eta`, `.symm`, `.trans`, `.bvar`, `.below` etc. all match
the bare words `cons`, `nil`, `rec`, `eta`, … which appear all over the file. Recorded because
it is exactly the kind of measurement error that would have licensed a wrong conclusion.)*

### M6 — the move, and the thing the measurement missed

New file **`Lean4Lean/Theory/SetModel/RecPropSingleton.lean`**, one import
(`Lean4Lean.Theory.SetModel.InterpSound`), carrying verbatim:
`Lean4Lean.SetModel.charBody`, `Lean4Lean.SetModel.charBody_definable`,
`Lean4Lean.SetModel.constDom_definable`, `Lean4Lean.SetModel.charFam`,
`Lean4Lean.SetModel.charFam_value`, `Lean4Lean.SetModel.charFam_mem_pow`,
`Lean4Lean.SetModel.eq_singleton_of_recProp`, plus
`Lean4Lean.SetModel.recProp_at_singleton` (the non-vacuity bound for
`eq_singleton_of_recProp`'s hypothesis; it depends only on Foundation's `mem_singleton_iff`, so
it adds nothing to the destination's dependency set, and its docstring is about the moved
theorem). `Lean4Lean.SetModel.mkForallType_const_eq_pow` stayed in `StructEtaPrice.lean`: it is
not in the cone, and has zero users tree-wide.

**What M2/M5 did not catch, and the build did.** Deleting
`import Lean4Lean.Theory.Typing.StructEtaPrice` also removed
`Lean4Lean.Theory.SetModel.UnitOracleLarge` from `RecTypePeel.lean`'s closure —
`StructEtaPrice.lean`'s *other* import. `RecTypePeel.lean` mentions `UnitAudit` 7 times, and
one of those is `#print axioms Lean4Lean.SetModel.UnitAudit.isPropL_recB1_iff'`, which failed
with `Unknown constant`. A **constant-cone** measurement cannot see this: `#print axioms` is a
command, not a declaration, so the name is in no cone. Fixed by importing
`Lean4Lean.Theory.SetModel.UnitOracleLarge` directly — closure 54, `Verify.*` entries **0**.

Lesson for the next round of this kind: cutting an import edge removes the *whole* transitive
contribution of the removed module, not just the constant you moved, and command-level
references (`#print axioms`, `#check`, `example`, attribute mentions) are invisible to a cone
walk. Build, don't just measure.

### M7 — AFTER: the verification bar

**Import closure of `Lean4Lean.Theory.SetModel.RecTypePeel`, recomputed** (transitive textual
`import` walk over `Lean4Lean/**.lean`, not inspection):

| | before | after |
|---|---|---|
| `Lean4Lean` modules in closure | 154 | **59** |
| `Lean4Lean.Verify.*` modules in closure | **46** | **0** |

The `Verify.*` list is empty — the walk prints `Verify.* entries: 0 []`. The 22 `SetModel`
modules that remain are all `Theory/SetModel/`.

**Cone and axioms of `Lean4Lean.SetModel.eq_singleton_of_recProp`:**

| | before | after |
|---|---|---|
| module | `Lean4Lean.Theory.Typing.StructEtaPrice` | `Lean4Lean.Theory.SetModel.RecPropSingleton` |
| arity | 8 | 8 |
| cone | 5826 | **5826** |
| own value is a hole | false | false |
| cone reaches `sorryAx` | false | **false** |
| watched declarations in cone | **none of 6** | **none of 6** |
| axioms | `propext`, `Classical.choice`, `Quot.sound` | **identical** |

`exists.lean` lines, after (population 449 built modules, watching 6):

```
FOUND       Lean4Lean.SetModel.eq_singleton_of_recProp
            module Lean4Lean.Theory.SetModel.RecPropSingleton, arity 8, cone 5826
            own value is a hole: false; cone reaches sorryAx: false
            watched declarations in cone: none of 6
```

and before (population 447):

```
FOUND       Lean4Lean.SetModel.eq_singleton_of_recProp
            module Lean4Lean.Theory.Typing.StructEtaPrice, arity 8, cone 5826
            own value is a hole: false; cone reaches sorryAx: false
            watched declarations in cone: none of 6
```

The per-module attribution of the cone is also unchanged apart from the seven constants that
changed module: `Universe` 3, `Interp` 3, `InterpSound` 2, `Rank` 1, and 8 in the new module
where there were 8 in `StructEtaPrice`. Prior 4 (cone ≤ 5826, axioms identical) confirmed —
exactly equal, which is what a verbatim move should give.

### M8 — the other three inversions: measured, and the same treatment does NOT work

For each, the union cone over *all* declarations the module defines, counting constants whose
defining module is under `Lean4Lean.Verify`:

| module | own decls | union cone | `Verify.*` constants **actually used** |
|---|---|---|---|
| `Theory/Typing/EtaGuardLand.lean` | 31 | 7728 | **111** |
| `Theory/Typing/CommutationLemmas.lean` | 19 | 3123 | **96** |
| `Theory/Typing/NoConfRepair.lean` | 70 | 8015 | **109** |
| `Theory/SetModel/RecTypePeel.lean` (the one just fixed) | 91 | 8347 | **0** |

So `RecTypePeel.lean` was the *only* one of the four where the `Verify/` edge was dead weight.
The other three genuinely consume `Verify/`-defined objects; a "move the lemma down" fix does
not exist for them, and pretending otherwise would just relocate the inversion.

**But the inversion is still real, and it is in the other direction.** What they consume is not
type-checker code; it is `Theory`-level mathematics that happens to be *defined* under
`Verify/`. Measured, per Verify module, "constants used from *other* `Verify` modules":

| `Verify/` module | own decls | cone | constants from other `Verify` modules | imports |
|---|---|---|---|---|
| `Verify/Typing/ProjGen.lean` | 118 | 3795 | **0** | only `Theory.Inductive.StructureClosed` |
| `Verify/Typing/ConstSpine.lean` | 104 | 7614 | **0** | only four `Theory.Typing.*` |
| `Verify/Typing/ProjClosedG.lean` | 42 | 2323 | 2 (both `ProjGen`) | only `Verify.Typing.ProjGen` |
| `Verify/Typing/ProjGenLift.lean` | 30 | 3012 | 45 (`ProjGen` + `ProjClosedG` only) | only `Verify.Typing.ProjClosedG` |
| `Verify/Typing/ProjGenInst.lean` | 48 | 2067 | 51 (same three only) | only `Verify.Typing.ProjGenLift` |
| `Verify/TypeChecker/EtaStructG.lean` | 92 | 12705 | **976 across 23 modules** | — |
| `Verify/TypeChecker/EtaUnitRefute.lean` | 35 | 7629 | 98 across 8 | — |
| `Verify/Typing/NoConfGuard.lean` | 53 | 7725 | 57 across 3 | — |
| `Verify/Typing/ProjSpineInv.lean` | 22 | 7789 | 153 across 6 | — |

**Recommendation, in priority order. Do not do any of it in this round.**

1. **`CommutationLemmas.lean` (0 importers): fixable, and the fix is a *five-module* move, not a
   lemma move.** Its 96 `Verify.*` constants come from exactly the chain
   `ProjGen → ProjClosedG → ProjGenLift → ProjGenInst` plus a handful of `MutField.*` from
   `EtaStructG`. The first four form a **closed cluster**: their only import outside the cluster
   is `Theory.Inductive.StructureClosed`, and they use **no** constant from any other `Verify`
   module. That cluster is `Theory/Inductive/` content misfiled under `Verify/Typing/`
   (`projTermG`, `projArgsG`, `padMinor*`, `padMotive*`, `realMinor`, `ClosedTele.*` — generic
   projection/eta *syntax*, nothing about the checker). Moving all four down to
   `Theory/Inductive/` would remove the largest single source of inversion pressure in the tree,
   and would also delete `StructEtaPrice.lean` §3's stated cost ("the constructor cannot be
   written where `IsDefEq` lives … needs `projTermG` (`Verify/Typing/ProjGen.lean`)"). Cost:
   4 + 3 + 3 + 3 = 13 direct importers to repoint, all under `Verify/`, none frozen. This is
   worth doing and is the natural next round.
   *Caveat:* `CommutationLemmas.lean`'s residual `MutField.*` dependency on `EtaStructG` would
   remain, so this fixes most of the file, not all of it. Check whether those `MutField.*` uses
   are in the lemmas or only in example firings before committing.
2. **`EtaGuardLand.lean` and `NoConfRepair.lean`: leave them.** Both route through
   `MutField.unitEnv` / `MutField.declEnv` (`EtaStructG`, `EtaUnitRefute`) and through
   `VEnv.ncPropEnv` (`NoConfGuard`), and those modules are *not* misfiled: `EtaStructG` alone
   pulls 976 constants from 23 other `Verify` modules including `Verify.Expr`,
   `Verify.LocalContext`, `Verify.TypeChecker.Basic` and `Verify.EquivManager`. The
   counterexample environments are built with checker-side machinery, so they belong in
   `Verify/`. The correct treatment for these two files is the opposite one: **make sure they
   never acquire a `Theory/SetModel/` importer**, since that is the only way the inversion turns
   into a cycle risk. Today neither reaches `SetModel/` (`EtaGuardLand` ← `ConstAppInvSIProof`,
   `ConfluenceRebuildPrice`; `NoConfRepair` ← `EtaGuardLand`), and all of those are
   `Theory/Typing/` or orphans. A cheap guard — a scripted check that no
   `Lean4Lean/Theory/SetModel/*.lean` closure contains a `Verify.*` module — would make this
   invariant machine-enforced rather than remembered. That is the single highest-value follow-up
   and it is much cheaper than any of the moves.
3. **`StructEtaPrice.lean` itself keeps its `Verify/` import, correctly.** After this round it
   has 3 importers, all under `Theory/Typing/`. Its `EtaUnitRefute` import is the *content* of
   the file (§5 refutes deriving `StructEtaG` from `VEnv.WF` using `MutField.unitEnv`), so it is
   not an accident and should not be cut.
4. **`Verify/Typing/ConstSpine.lean` is the sleeper.** 104 declarations, cone 7614, **zero**
   constants from any other `Verify` module, and it imports only four `Theory.Typing.*` modules.
   It is pure `Theory` content — `VEnv.IsDefEq.constApp_inv` and the `ParRed`/`NormalEq` spine
   inversions, the very lemmas `StructEtaPrice.lean` §6 proves are *false* for the extended
   relation. It has only 2 direct importers. Moving it to `Theory/Typing/ConstSpine.lean` is
   cheaper than the `ProjGen` cluster and removes a large chunk of `EtaGuardLand`'s and
   `NoConfRepair`'s 111/109. Worth doing before (1).

### M9 — round close

Whole-tree `lake build`: **exit 0, "Build completed successfully (1635 jobs)"**, 0 errors in the
full log.

*(The brief's baseline was 1633 jobs. The +2 is not all mine: `git status` shows two other
streams active on the same worktree this round —
`Lean4Lean/Theory/SetModel/TeleWFBridge.lean` and `Lean4Lean/Verify/Inductive/FlipWiring.lean`
are new, and `Lean4Lean/Verify/Inductive/TrIndDeclNProducer.lean` is modified, none of them
mine. This also explains `exists.lean`'s population moving 447 → 449 while I added one file.
Absolute job/population counts are not attributable to a single stream when the tree is shared;
the closure, cone and axiom numbers above are, because they are per-declaration.)*

`scripts/sorry-census-all.lean --run`:

```
on disk: 476; in default-target population: 452; Experimental (out of population): 24
BUILT: 452; in population but NOT BUILT: 0
HOLES over the WHOLE built population, unioned across both passes: 13
```

**census 13, NOT BUILT 0.** The 13 are the standing ones (`TrProj.weak'_inv`,
`TypeChecker.Inner.inferProj.WF`, `isDefEqUnitLike.WF`, `tryEtaStructCore.WF`,
`IsDefEqU.forallE_inv_stratified`, `IsDefEqU.weakN_iff`, `NormalEq.descend`,
`WF.rigidShapeUniqNS`, `VIndRecArg.exists_indep`, `addDecl.WF`, `kernel_complete`,
`kernel_sound`, `leanTT_equiconsistent_zfc_omega_inaccessibles`) — none added, none removed.

Three guards, from the build log:

```
guard 1: Axioms.lean declares exactly the 24 frozen axioms ✓
guard 2: kernel_sound axioms within whitelist ✓ (proof INCOMPLETE: sorryAx present)
guard 3: checker cone implementation gaps within frozen list (2/2 remaining) ✓
```

In-repo section-variable warnings: **0**. The build log has exactly one
`automatically included section variable(s) unused` line and it is
`Foundation/FirstOrder/SetTheory/Z.lean:35` — a dependency, not this repo
(`grep 'section variable' | grep -c 'Lean4Lean/'` = 0). The new module emits no warnings of any
kind; a forced rebuild of it produced only its three `#print axioms` info lines.

Files changed by this round: `Lean4Lean/Theory/SetModel/RecPropSingleton.lean` (new),
`Lean4Lean/Theory/SetModel/RecTypePeel.lean`, `Lean4Lean/Theory/Typing/StructEtaPrice.lean`,
`docs/handoff-layering.md` (new). Nothing under `Lean4Lean/Verify/` was touched. No git
state-changing commands were run.

### Scorecard against the priors

| prior | outcome |
|---|---|
| 1. 70% movable | **correct** — movable, and the obstruction was zero rather than small |
| 2. 25% a `Verify/`-rooted constant is in the dependency set | **refuted** — 0 of 5826 |
| 3. destination at `UnitOracleLarge`'s level or below; new file not an edit to an unowned one | **correct**, and lower than guessed: `InterpSound` (closure 22) suffices |
| 4. cone ≤ 5826, axioms identical | **correct**, exactly equal on both |
| 5. other three are the same shape and equally cuttable | **wrong, and this is the round's second finding** — all three genuinely use `Verify.*` constants (111 / 96 / 109). `RecTypePeel` was the only dead edge. The half of the prior that survived is that `CommutationLemmas` is the cheapest test case, though the fix there is a five-module move, not a lemma move |
| 6. a grepped dependency set would be wrong | **correct, and it bit twice** — once on the last-name-component match (M5) and once by being blind to `#print axioms` (M6) |
