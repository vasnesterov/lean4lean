# handoff: migrating the `ProjGen` cluster out of `Verify/` into `Theory/Inductive/`

Round scope: a measured migration with a hard verification bar. Not a design round.
Written BEFORE the first measurement, then appended to as each measurement lands
(eighteen crashes in prior rounds; batching loses everything).

## Priors, recorded before measuring

1. **The brief's claim is a prior round's report, not my measurement.** The claim is that
   `ProjGen -> ProjClosedG -> ProjGenLift -> ProjGenInst` is a closed cluster whose only
   outside import is `Lean4Lean.Theory.Inductive.StructureClosed`, using no constant from
   any other `Verify/` module. The orchestrator's own calibration note says attributions have
   been wrong nine times. So: **verify, do not trust.**
2. **Expected structure of the check.** Closedness under *imports* is decidable without
   elaboration: Lean cannot reference a constant from a module it does not import. If
   `closure(Theory.Inductive.StructureClosed)` contains no `Lean4Lean.Verify.*` module, and
   each of the four imports only its predecessor (plus `StructureClosed` at the head), then
   the four literally cannot cite any `Verify/` constant, and closedness is a theorem about
   the import graph rather than a survey of uses. I expect this to be the shape of the answer.
   The risk case: a *second* import line further down one of the four files (the census script
   documents that this tree puts `/-! -/` blocks between imports, so a naive head-20 read
   can miss one).
3. **Expected failure mode if it is not closed.** `ProjGenInst`/`ProjGenLift` are the ones I
   would bet on: they are the "commutation" files, and commutation lemmas in this tree have a
   habit of being stated against checker-side `TrProj`. If any of the four cites a `Verify/`
   constant, the move is unsafe and I stop and report.
4. **Prior on axiom sets.** A pure file move should not change any axiom set. If one changes,
   the likely cause is not the move but an `autoImplicit` hole or a name resolved differently
   under the new module path (a namespace shadowing effect). That is a finding, not something
   to absorb.
5. **Prior on cone sizes.** Cone sizes may move by a constant or two: the four files' import
   closures change (they lose nothing, since their closure is already `StructureClosed`'s), but
   `CommutationLemmas` drops `Verify/TypeChecker/EtaStructG` only if it turns out unused --
   the brief says drop the "now-unnecessary" Verify imports, and `EtaStructG` is a *fourth*
   Verify import not in the cluster, so it probably stays. Expect `CommutationLemmas` cone
   sizes to be unchanged.
6. **Prior on the census.** 13 and NOT BUILT 0 is the target. A move that leaves a stale
   `.olean` behind under the old path could make an orphan/NOT BUILT number move; I will
   check for stale oleans explicitly after the move.

## Measurements (appended in order)

### M1 — baseline build (before any edit)
`lake build` from a clean tree state: **EXIT 0, 1644 jobs, "Build completed successfully"**.
Other streams are live: `git status` at round start showed `M Lean4Lean/Verify/Inductive/SurfaceMap.lean`,
`M docs/handoff-surfacemap.md`, untracked `Lean4Lean/Theory/Typing/CRSEScope.lean`,
`docs/handoff-claimb.md`, `docs/handoff-crse.md`. (This is already different from the git status
in my briefing snapshot, which listed `Theory/SetModel/CnstRecursion.lean` etc. — streams moved.)

### M2 — import lines, read from the whole file, not the head
`grep -n '^\s*import'` over all five files. Each of the four has **exactly one** import line, and
`CommutationLemmas` has exactly four. No hidden second import after a `/-! -/` block.

    ProjGen        <- Lean4Lean.Theory.Inductive.StructureClosed        (1 import)
    ProjClosedG    <- Lean4Lean.Verify.Typing.ProjGen                  (1)
    ProjGenLift    <- Lean4Lean.Verify.Typing.ProjClosedG              (1)
    ProjGenInst    <- Lean4Lean.Verify.Typing.ProjGenLift              (1)
    CommutationLemmas <- Verify.TypeChecker.EtaStructG, Verify.Typing.{ProjGenLift, ProjGenInst, ProjClosedG}

### M3 — CLOSEDNESS, part 1: the import graph (a proof, not a survey)
`closure(Lean4Lean.Theory.Inductive.StructureClosed)` = **21 modules, containing ZERO
`Lean4Lean.Verify.*`**. Its only non-`Lean4Lean.Theory` members are `Lean`, five `Batteries.*`,
`Lean4Lean.Std.Basic`, `Lean4Lean.Std.VariableBang`.
Therefore the four modules' closures are exactly `closure(StructureClosed) + {the four}`
(checked: `closure(ProjGenInst) == closure(StructureClosed) | {four}` is **True**, 25 modules).
**Lean cannot reference a constant from a module it does not import**, so no declaration in the
four can cite any `Verify/` constant outside the cluster. This is decisive on its own.

### M4 — CLOSEDNESS, part 2: the cone walk (independent confirmation)
A Lean script (`/tmp/migaudit.lean`) imports `ProjGenInst` + `CommutationLemmas`, enumerates every
declaration defined in each of the five modules, walks its full transitive constant cone, and maps
each constant back to its defining module. `Verify/` modules touched by each module's whole cone:

    ProjGen             1  -> {ProjGen}
    ProjClosedG         2  -> {ProjClosedG, ProjGen}
    ProjGenLift         3  -> {ProjGenLift, ProjClosedG, ProjGen}
    ProjGenInst         4  -> {ProjGenInst, ProjGenLift, ProjClosedG, ProjGen}
    CommutationLemmas   5  -> the four PLUS Lean4Lean.Verify.TypeChecker.EtaStructG

**VERDICT: the cluster IS closed.** The brief's report is confirmed by two independent methods.

**A correction to the brief, though:** it says to "drop the now-unnecessary `Verify/` imports from
`CommutationLemmas.lean`" — plural, implying all of them. The cone walk shows `CommutationLemmas`
genuinely *uses* constants from `Verify.TypeChecker.EtaStructG`, which is NOT in the cluster and
does NOT move. So `CommutationLemmas` goes from 4 direct `Verify/` imports to **1**, not to 0, and
it stays on the soft-report list. Dropping the `EtaStructG` import would break it.

### M5 — population/declaration counts (the before-table's shape)
    ProjGen             78 public decls, 40 internal
    ProjClosedG         21 public,       21 internal
    ProjGenLift         19 public,       11 internal
    ProjGenInst         27 public,       21 internal
    CommutationLemmas   17 public,        2 internal
    total public: 162
Full per-declaration cone/hole/watched/axiom lines are in `/tmp/before.txt`; the before/after
comparison below is a mechanical diff of that file against `/tmp/after.txt`.

### M6 — importers, measured
14 `import` lines across **12 files** name one of the four modules (the brief said "13
importers"; the exact figures are 12 files / 14 import lines, plus **one non-import module
reference**: `scripts/hole-cone.lean:218` names ``​`Lean4Lean.Verify.Typing.ProjGen`` inside an
`importModules` call — that is the 13th site, and a grep for `import` alone misses it).
Four of the twelve are the cluster members themselves. **None is frozen.**

    Lean4Lean/Theory/Typing/CommutationLemmas.lean          (3 lines)   [owned]
    Lean4Lean/Theory/Inductive/{ProjClosedG,ProjGenLift,ProjGenInst}.lean  (1 each) [owned, moved]
    Lean4Lean/Verify/TypeChecker/EtaStructG.lean            (1)   [import line only]
    Lean4Lean/Verify/TypeChecker/UnitEta.lean               (1)   [import line only]
    Lean4Lean/Verify/Typing/ProjClosedGWitness.lean         (1)   [import line only]
    Lean4Lean/Verify/Typing/ProjGenBeta.lean                (1)   [import line only]
    Lean4Lean/Verify/Typing/ProjGenInstWitness.lean         (1)   [import line only]
    Lean4Lean/Verify/Typing/ProjGenLiftWitness.lean         (1)   [import line only]
    Lean4Lean/Verify/Typing/ProjGenWitness.lean             (1)   [import line only]
    scripts/hole-cone.lean                                  (1 import + 1 importModules)

### M7 — the migration performed
Plain `mv` (not `git mv` — no state-changing git this round), then a regex confined to
`^\s*import\s+` lines. Stale build artifacts for the four OLD module paths were deleted from
`.lake/build/{lib/lean,ir}/Lean4Lean/Verify/Typing/` (20 files: `.olean`, `.ilean`, `.trace`,
`.c`, `.setup.json` and their `.hash` siblings).
**This deletion is not housekeeping.** `sorry-census-all.lean` and `exists.lean` take their
population from the *filesystem walk of `.lean` files*, so a stale `.olean` with no `.lean` is
invisible to them — but `importModules {module := Lean4Lean.Verify.Typing.ProjGen}` would still
have **succeeded from the stale olean**, silently measuring a pre-migration snapshot. That is a
new instrument blindness in the same family as the ten already on the ledger, and the reason to
delete rather than leave.
Baseline `lake build`: 1644 jobs. Post-migration `lake build`: **EXIT 0, 1644 jobs**, zero errors.

### M8 — THE VERIFICATION BAR: before/after over all 162 declarations
Same script, run against the old paths (`/tmp/before.txt`) and the new (`/tmp/after.txt`),
diffed after normalising only the `===== MODULE …` header text.

**The complete diff of a 522-line audit is the five `CONE-MODULE-UNIVERSE`/`VERIFY-TOUCHED`
blocks — i.e. exactly the intended effect, and nothing else.**

    axiom sets            IDENTICAL across all 162 declarations (byte-diff empty)
    ownHole / sorryAx     IDENTICAL (0 holes before, 0 after)
    WATCHED IN CONE       IDENTICAL: 0 of 162 declarations, before and after
    cone sizes            IDENTICAL for every declaration -- not "within a constant or two":
                          sum of cone sizes 215469 before, 215469 after
    cone-module-universe  86 / 61 / 77 / 47 / 81 -- unchanged sizes, only the
                          Verify-attribution changed

My prior 5 said cone sizes might shift by a constant or two. **They did not shift at all**, and
the reason is worth writing down: the cone is over constants *actually cited*, and this migration
added and removed no import from anyone's closure — it renamed four nodes of the import graph.
A cone size shift would therefore have been a *symptom*, not the expected noise I budgeted for.

Verify-attribution, before -> after:

    ProjGen             1 -> 0
    ProjClosedG         2 -> 0
    ProjGenLift         3 -> 0
    ProjGenInst         4 -> 0
    CommutationLemmas   5 -> 1   (Lean4Lean.Verify.TypeChecker.EtaStructG, which does not move)

Axiom sets observed over the 162 (unchanged before/after):
`[Quot.sound, propext]` x64, `[propext]` x48, `[Classical.choice, Quot.sound, propext]` x33, `[]` x17.

### M9 — warnings: pre-existing, carried over unchanged, NOT introduced
Baseline log: 9 warnings in `Verify/Typing/ProjGen.lean` (7 "This simp argument is unused",
2 `variable!`-linter "Variable name … is not explicitly referenced") and 1 in `ProjClosedG.lean`.
Post-migration log: the identical 10 warnings at the identical line:col, now under the new paths.
So the migration introduced zero warnings. They are still ten warnings in files I own, which the
round-close bar counts, so they are addressed as a separate, clearly-marked pass below.

### M10 — `exists.lean` on the headline declarations (both lines, as required)
Population 458 built modules; watching 6 declarations. **The `*** WATCHED IN CONE ***` line did
not fire for any declaration**; every one reports the negative form, which is the other line:

    watched declarations in cone: none of 6

and all eleven report `own value is a hole: false; cone reaches sorryAx: false`.

    VEnv.IsStructureG                  Theory.Inductive.Structure       arity 6  cone 7   [NO PROOF TERM]
    VInductDecl'.projCoreG             Theory.Inductive.ProjGen         arity 10 cone 686
    VInductDecl'.ProjClosedG           Theory.Inductive.ProjClosedG     arity 1  cone 2   [NO PROOF TERM]
    VInductDecl'.projTermG_lift'       Theory.Inductive.ProjGenLift     arity 16 cone 3009
    VInductDecl'.projTermG_instN       Theory.Inductive.ProjGenInst     arity 17 cone 2030
    VInductDecl'.projTermG_instL       Theory.Inductive.ProjGenInst     arity 10 cone 879
    VInductDecl'.etaExpansionG_weakN   Theory.Typing.CommutationLemmas  arity 14 cone 3018
    VInductDecl'.etaExpansionG_instL   Theory.Typing.CommutationLemmas  arity 8  cone 884
    VInductDecl'.etaExpansion_weakN    Theory.Typing.CommutationLemmas  arity 11 cone 2788
    VInductDecl'.projAllG_lift'        Theory.Typing.CommutationLemmas  arity 13 cone 3011
    MutField.decl_projClosedG          Theory.Typing.CommutationLemmas  arity 0  cone 665

**An independent cross-check I did not plan for.** `docs/handoff-commutation.md:68` recorded, in an
earlier round and under the old path, `projTermG_lift'` as "arity 16, cone 3009, hole false,
sorryAx false". `exists.lean` post-migration reports **arity 16, cone 3009, hole false, sorryAx
false**. A figure written down by a different round before the move is reproduced exactly after it.
(Note `IsStructureG` lives in `Theory/Inductive/Structure.lean`, not in the cluster — it had
already been moved down in an earlier round, which `Structure.lean:565` records.)

### M11 — the remaining layer inversions, with the constant counts that justify each
`python3 scripts/layer-check.py` -> **EXIT 0**. HARD RULE: 66 `Theory/SetModel/` modules checked,
none reaches `Verify/`. SOFT REPORT: four `Theory/` files, each with **1** direct `Verify/` import.
Cited-constant counts measured by cone walk (`/tmp/inversion.lean`), not by inspection:

    Theory.Typing.EtaGuardLand    <- Verify.Typing.NoConfGuard      : 29 decls cite 111 Verify constants
        across 9 Verify modules (ConstSpine 54, EtaStructG 15, ProjLevelWitness 14,
        EtaUnitRefute 11, NoConfGuard 10, ConstSpineWF 4, Rigidity 1, ProjSpineInv 1, EtaResidual 1)
    Theory.Typing.NoConfRepair    <- Verify.Typing.ProjSpineInv     : 68 decls cite  95 Verify constants
        (ConstSpine 39, EtaUnitRefute 23, EtaStructG 22, Rigidity 6, ConstSpineWF 3, EtaResidual 2)
    Theory.Typing.StructEtaPrice  <- Verify.TypeChecker.EtaUnitRefute: 65 decls cite 52 Verify constants
        (EtaUnitRefute 23, EtaStructG 22, Rigidity 5, EtaResidual 2)
    Theory.Typing.CommutationLemmas <- Verify.TypeChecker.EtaStructG: 17 decls cite   8 Verify constants
        (EtaStructG 8)

**Legitimacy, case by case, by the script's own rule** ("a small constant-count is the suspicious
case; a large one usually means the file is genuinely about checker-built objects"):

* `EtaGuardLand` (111) and `NoConfRepair` (95) — **legitimate.** Both are dense in
  `Verify.Typing.ConstSpine` (54 and 39 constants), the checker's constant-spine machinery. A file
  that cites 39–54 constants of one checker module is *about* the checker, not parked above it.
* `StructEtaPrice` (52) — **legitimate**, but weaker: it is a *pricing* document, and 45 of its 52
  are `EtaUnitRefute` + `EtaStructG`, i.e. refutation witnesses. It is about what the checker's
  η-machinery costs, so it needs those witnesses; it is not a parked proof.
* `CommutationLemmas` (8) — **NOT legitimate, and this is the honest reading of what this round
  did.** See M12.

### M12 — FINDING: the migration converted CommutationLemmas' inversion, it did not remove it
Measured (`/tmp/cmlbefore.lean`): CommutationLemmas' 17 declarations cite 3123 constants in total.
88 of those are defined in the four modules that moved (ProjGenLift 27, ProjClosedG 25, ProjGen 21,
ProjGenInst 15), and 8 in `Verify/TypeChecker/EtaStructG.lean`.

    BEFORE: 96 constants cited under Verify/, across 5 modules, 4 direct imports
    AFTER:   8 constants cited under Verify/, across 1 module,  1 direct import

**96 is the bottom of the "96–111 constants" band that `layer-check.py`'s own docstring cites as
the evidence that its listed inversions are legitimate.** So before this round CommutationLemmas
was, by that criterion, a legitimate inversion. It now cites 8, which by the same criterion is
"what a parked declaration looks like". The migration did not resolve the inversion; **it converted
a large, justified one into a small, suspicious one** — which is progress, because a small one is
cheap to finish, but it is not the same as done, and the brief's phrasing ("would fix most of
CommutationLemmas's layering inversion") is accurate only in that arithmetic sense.

### M13 — the next move is already measured, and it is small
The 8 residual constants are 7 distinct declarations (one is `etaExpansionG.eq_1`, an auto-generated
equation of `etaExpansionG`):

    MutField.aTy, MutField.bTy, MutField.aCtor, MutField.bCtor, MutField.decl,
    VInductDecl'.projAllG, VInductDecl'.etaExpansionG

Cone walk over all seven (`/tmp/resid.lean`): **703 constants total, of which exactly 7 are defined
under `Verify/` — precisely themselves.** So this seven-declaration set is **closed** in the same
sense the four-module cluster was. Moving them out of `Verify/TypeChecker/EtaStructG.lean` into
`Theory/` would take CommutationLemmas to **0** direct `Verify/` imports and remove it from the soft
report entirely.
NOT DONE THIS ROUND, deliberately: `EtaStructG.lean` is not a file I own, and this is a
declaration-level split (extract 7 declarations into a new `Theory/Inductive/` module), not an
import-line edit. `closure(EtaStructG)` is 143 modules with 31 `Verify/` modules inside, so the
*file* cannot move; only these 7 declarations can. That is a self-contained next round.

### M14 — round-close numbers
    lake build                    EXIT 0, 1644 jobs, "Build completed successfully", 0 errors
                                  (baseline was also 1644 jobs)
    census (--run)                on disk 485; in-population 461; BUILT 461; NOT BUILT 0
                                  HOLES over the whole built population: 13   <- unchanged, target hit
                                  pass A 458 / pass B 3; ORPHAN modules 53
    guard 1  Axioms.lean declares exactly the 24 frozen axioms                        ok
    guard 2  kernel_sound axioms within whitelist (proof INCOMPLETE: sorryAx present) ok
    guard 3  checker cone implementation gaps within frozen list (2/2 remaining)      ok
             -- all three byte-identical to the baseline log's guard lines
    layer-check.py                EXIT 0; hard rule clean over 66 SetModel modules

### M15 — the ten pre-existing warnings, fixed as a separate pass
Fixed **statement-preservingly**, never by removing a hypothesis:
* 7x `linter.unusedSimpArgs` — the argument dropped from the `simp`/`simp only` list.
  `ProjGen.lean:278` (`List.getElem?_map`, `List.getElem?_range` — both flagged, both dropped),
  `:288` (same pair), `:426` (`if_pos rfl`), `:535` (`Nat.add_zero`);
  `ProjClosedG.lean:142` (`Nat.add_comm`).
* 3x `linter.unusedVariables` — binder **renamed** to a `_`-prefix, NOT removed:
  `ProjGen.lean:256` `padMotive`'s `(D : VInductDecl')` -> `(_D : …)`;
  `:1084` and `:1156` `(hrec : C'.recFields = [])` -> `(_hrec : …)`.
  Removing `hrec` would *strengthen* two theorem statements and change what downstream depends on
  — exactly the silent regression this round's bar exists to catch — so it was not done.
  Checked first that nothing calls these by named argument: `grep 'hrec :='` finds only an unrelated
  local `have` in `Verify/PrimitiveWF.lean:1383`, and every `padMotive` caller uses dot notation
  (`D.padMotive …`), which resolves on the argument's *type*, not its name. Renaming is therefore
  API-preserving, and the statements stay alpha-equivalent.

**Re-audited after the warning pass.** `diff /tmp/after.txt /tmp/final.txt` is **empty**: the ten
fixes changed nothing at all — not one cone size, axiom set, hole flag or watched flag among the
162. And against the original pre-migration baseline, the only remaining differences in the whole
audit are still the intended `VERIFY-TOUCHED` attribution lines. Sum of cone sizes: 215469
at baseline, 215469 now.

### M16 — round-close, final numbers (all re-run after the warning pass)
    lake build            EXIT 0, 1644 jobs, "Build completed successfully"
                          0 errors; 0 warnings from any file I own
    census (--run)        on disk 485; in-population 461; BUILT 461; NOT BUILT 0
                          HOLES: 13  (pass A 13, pass B 0); pass A 458 / pass B 3; ORPHANS 53
                          -> census 13 and NOT BUILT 0: on target, moved in neither direction
    guard 1               Axioms.lean declares exactly the 24 frozen axioms            ok
    guard 2               kernel_sound axioms within whitelist                          ok
                          (proof INCOMPLETE: sorryAx present -- unchanged from baseline)
    guard 3               checker cone implementation gaps within frozen list (2/2)     ok
    layer-check.py        EXIT 0; hard rule clean over 66 SetModel modules;
                          soft report: 4 Theory/ files, 1 direct Verify import each
The 13 holes are the same 13 as before (`TrProj.weak'_inv`, `inferProj.WF`, `isDefEqUnitLike.WF`,
`tryEtaStructCore.WF`, `IsDefEqU.forallE_inv_stratified`, `IsDefEqU.weakN_iff`, `NormalEq.descend`,
`WF.rigidShapeUniqNS`, `VIndRecArg.exists_indep`, `addDecl.WF`, `kernel_complete`, `kernel_sound`,
`leanTT_equiconsistent_zfc_omega_inaccessibles`) — none in a file this round touched.

### M17 — a stale figure in a script I do not own (report only, no edit)
`scripts/layer-check.py`'s docstring says "**Three** such files are legitimate — they … use
**96–111** constants from `Verify/` each". Measured today there are **four** such files, with cited
counts **111, 95, 52 and 8**. The 96 in that band is almost certainly CommutationLemmas' own
pre-migration count (measured today as exactly 96), so the docstring was written when
CommutationLemmas was one of the three. It is now stale in both the count of files and the range.
I did not edit it — not a file I own. Suggested correction for whoever does own it: "Two files
(`EtaGuardLand` 111, `NoConfRepair` 95) are dense in `Verify.Typing.ConstSpine` and legitimate;
`StructEtaPrice` (52) is a pricing document and legitimate; `CommutationLemmas` (8) is the
suspicious case and has a measured 7-declaration fix (see `docs/handoff-projmigrate.md` M13)."

### M18 — documentation drift left behind, in files I do not own (report only)
Six prose references to the four modules' OLD paths survive in files outside my ownership, and one
of them is now a false statement rather than a stale path:
* `Lean4Lean/Theory/Inductive/StructureEta.lean:87` — "`VEnv.IsStructureG` was declared in
  `Verify/Typing/ProjGen.lean` and nothing under `Theory/` …". **The second clause is now wrong**
  (and its first clause was already historical: `IsStructureG` lives in
  `Theory/Inductive/Structure.lean` today, per `Structure.lean:565`).
* `Lean4Lean/Theory/Inductive/Structure.lean:492`, `:565`; `Theory/Inductive/IotaGen.lean:10, :69`;
  `Theory/Typing/StructEtaPrice.lean:61, :115`; `Verify/TypeChecker/EtaStructG.lean:25`;
  `Verify/TypeChecker/FiringWitness.lean:57`; `Verify/Typing/ProjGenWitness.lean:14` — all say
  `Verify/Typing/ProjGen*.lean`; the files are now under `Theory/Inductive/`.
I updated only the two such references inside `CommutationLemmas.lean` (a file I own):
lines 22 and 147, now `Theory/Inductive/ProjGenLift.lean:289` and `Theory/Inductive/ProjGenInst.lean:414`.

### M19 — re-poll: three other-stream commits landed mid-round
`git log` advanced from `651bb08` to `6319956` while this round ran (`9be4ca8`, `6bd173f`,
`6319956`), and the in-flight files I saw at M1 (`Verify/Inductive/SurfaceMap.lean`,
`Theory/Typing/CRSEScope.lean`, `docs/handoff-{surfacemap,claimb,crse}.md`) are now committed;
two new untracked handoffs appeared (`docs/handoff-claimb2.md`, `docs/handoff-indepresidual.md`).
So the green in M16 was measured against a tree that has since moved. **Re-ran `lake build`
after their commits landed: EXIT 0, 1644 jobs, 0 errors, 0 warnings from files I own, all three
guards ✓.** No file of mine was clobbered and nothing of theirs broke on my move.

### Files touched this round (complete)
Moved (`mv`, contents unchanged except as noted):
    Lean4Lean/Verify/Typing/ProjGen.lean      -> Lean4Lean/Theory/Inductive/ProjGen.lean
    Lean4Lean/Verify/Typing/ProjClosedG.lean  -> Lean4Lean/Theory/Inductive/ProjClosedG.lean
    Lean4Lean/Verify/Typing/ProjGenLift.lean  -> Lean4Lean/Theory/Inductive/ProjGenLift.lean
    Lean4Lean/Verify/Typing/ProjGenInst.lean  -> Lean4Lean/Theory/Inductive/ProjGenInst.lean
Edited beyond the import line (files I own):
    Lean4Lean/Theory/Inductive/ProjGen.lean       import line + 9 warning fixes
    Lean4Lean/Theory/Inductive/ProjClosedG.lean   import line + 1 warning fix
    Lean4Lean/Theory/Inductive/ProjGenLift.lean   import line only
    Lean4Lean/Theory/Inductive/ProjGenInst.lean   import line only
    Lean4Lean/Theory/Typing/CommutationLemmas.lean  3 import lines + 2 prose path refs
Edited: IMPORT LINE ONLY (files I do not own; they fail to compile solely because of the move):
    Lean4Lean/Verify/TypeChecker/EtaStructG.lean
    Lean4Lean/Verify/TypeChecker/UnitEta.lean
    Lean4Lean/Verify/Typing/ProjClosedGWitness.lean
    Lean4Lean/Verify/Typing/ProjGenBeta.lean
    Lean4Lean/Verify/Typing/ProjGenInstWitness.lean
    Lean4Lean/Verify/Typing/ProjGenLiftWitness.lean
    Lean4Lean/Verify/Typing/ProjGenWitness.lean
Edited, and flagged because it is outside the enumerated ownership list:
    scripts/hole-cone.lean  -- its `import` line AND the module name inside its `importModules`
    call at :218. It is not a compiled module, so `lake build` would have stayed green with it
    broken; it would simply have failed at run time. Two module-path tokens, no logic touched.
New: docs/handoff-projmigrate.md (this file).
Deleted: 20 stale build artifacts under .lake/build/{lib/lean,ir}/Lean4Lean/Verify/Typing/ for the
four OLD module paths (see M7 for why this is load-bearing, not tidying).
NOT touched: Verify/Soundness.lean, Verify/Axioms.lean, Verify/Guard.lean (frozen),
docs/vacuity-ledger.md, scripts/layer-check.py, and every other stream's file.
No state-changing git ran at any point (plain `mv`, not `git mv`).
