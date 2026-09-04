# handoff-commutation.md

Stream: commutation lemmas — five lemmas reported **missing** by a pricing round:
`projTerm_weakN`, `projTermG_weakN`, `etaExpansion_weakN`, `etaExpansionG_weakN`,
`etaExpansionG_instL`.

Ownership: `Lean4Lean/Theory/Typing/CommutationLemmas.lean` (new) and this file. Everything
else read-only.

## PRIORS (written before the first instrument call)

Recorded so they can be scored against measurement, per process rule.

1. **At least one of the five already exists.** The brief says a `shape.lean` scan has caught
   five already-done assignments this session. `weakN`/`liftN` commutation for a term-former is
   the single most routine lemma in this tree, and `projTerm` is old machinery. I put
   ~70% on at least one of the five being present, ~35% on at least three.
2. **The `G` variants are the more likely to be absent.** A `G`-suffixed former (I expect a
   "generalised"/telescoped variant) is newer than its plain counterpart, so its commutation
   lemmas are the likelier gap. So I predict plain-before-G: if exactly some exist, they are
   `projTerm_weakN` / `etaExpansion_weakN`.
3. **Naming will not match.** The brief's names are the *pricing round's* names, not
   necessarily the tree's. This repo's convention for weakening commutation is `liftN`/`weakN`
   with names like `X.liftN_comm`, `X.weakN_eq`, or an inline `simp` lemma. So I expect the
   `exists.lean` verdict to be NOT FOUND on all five *as named* while `shape.lean` finds
   content under other names. **The verdict that matters is `shape.lean`'s, not
   `exists.lean`'s.**
4. **`etaExpansionG_instL` is the odd one out.** Four are `weakN`; one is `instL`. Level
   instantiation commutes with term formers only if the former does not itself mention a
   universe level in a position `instL` touches. Eta-expansion builds a `.lam` whose domain
   type is a term, so I expect this one to be *ordinary* too, but it is the one I would bet on
   being non-ordinary if any is. Prior on "one of the five is not an ordinary structural
   induction": ~30%, and conditional on that, ~55% it is this one.
5. **The ~40-site estimate is probably too high.** The brief itself flags that a lemma can be
   vacuous because the former never appears in the relevant position. `projTerm` in particular
   I expect appears in few congruence sites. Prior: the true consuming-site count for the
   `projTerm` pair is under 10 direct.
6. **Direct ≪ transitive.** Per `users.lean`'s own docstring the repo has conflated these
   repeatedly. I expect direct counts in the single digits and transitive in the hundreds for
   anything in the confluence layer.

## MEASUREMENTS (appended one line per instrument call, as made)

- M1 `grep` for definitions of the four term-formers. Definitions: `Lean4Lean.VInductDecl'.projTerm`
  (`Theory/Inductive/Structure.lean:104`), `projTermG` (`Verify/Typing/ProjGen.lean:388`),
  `etaExpansionG` (`Verify/TypeChecker/EtaStructG.lean:113`). Grep also shows
  `projTerm_instL` (Structure.lean:148), `projTerm_lift'` (Structure.lean:357),
  `projTermG_lift'` (ProjGenLift.lean:289), `projTermG_instL` (ProjGenInst.lean:414),
  `projTerm_instN` (Structure.lean:442), `projTermG_instN` (ProjGenInst.lean:269).
  **Prior 3 already looks confirmed: the tree's suffix is `_lift'`, not `_weakN`.** 577 total
  mentions across 50 files.
- M2 `lake build` at HEAD `a1dbfd1`: **green, 1630 jobs**, before any edit of mine. Population for
  the structural instruments is therefore the full default target.
- M3 `grep` for `weakN` as a *definition*: **there is no `VExpr.weakN`**. `weakN` in this tree is
  a *judgement*-level lemma suffix (`VEnv.HasType.weakN`, `IsDefEqU.weakN_iff`,
  `VEnv.HasArgs.weakN`, …). The *syntactic* weakening of a `VExpr` is `VExpr.liftN`
  (`Theory/VExpr.lean:38`), generalised by `VExpr.lift' : VExpr → Lift → VExpr`
  (`Theory/VExpr.lean:670`). So the brief's `_weakN` names must be read as the tree's `_lift'`
  family. Also: the brief's namespace `Lean4Lean.VExpr.projTerm` does not exist — the real name
  is `Lean4Lean.VInductDecl'.projTerm`.
- M4 `exists.lean` (population **444 built modules**, watching 6). Verdict on the five brief
  names, all in `Lean4Lean.VInductDecl'`: `projTerm_weakN` **NOT FOUND**, `projTermG_weakN`
  **NOT FOUND**, `etaExpansion_weakN` **NOT FOUND**, `etaExpansionG_weakN` **NOT FOUND**,
  `etaExpansionG_instL` **NOT FOUND**. As *names*, the pricing round was right.
  Same call, the `_lift'`-convention candidates: `Lean4Lean.VInductDecl'.projTerm_lift'`
  FOUND (module `Lean4Lean.Theory.Inductive.Structure`, arity 13, cone 2692, hole false, sorryAx
  false, watched none of 6); `Lean4Lean.VInductDecl'.projTermG_lift'` FOUND (module
  `Lean4Lean.Verify.Typing.ProjGenLift`, arity 16, cone 3009, hole false, sorryAx false, watched
  none of 6). Also FOUND: `etaExpansion_instL` (cone 774), `projAll_instL` (771),
  `projTerm_instL` (765), `projTermG_instL` (879), `projTerm_instN` (1717),
  `projTermG_instN` (2030) — all hole-free, sorryAx-free, watched none of 6.
  NOT FOUND: `projAll_lift'`, `projAllG_lift'`.
- M5 `shape.lean`, five conclusion-shape queries, population 444 each, heads all resolved
  (so the 0-hit lines are real evidence):
  * `HEADS="Lean4Lean.VInductDecl'.projTerm Lean4Lean.VExpr.lift'"` -> **2 hits**, 0 fields:
    `Lean4Lean.prjEnv_trProj_lifted` (arity 0, `Verify/Typing/ProjExistClose`) and
    `Lean4Lean.VInductDecl'.projTerm_lift'` (arity 13, `Theory/Inductive/Structure`).
    => **`projTerm_weakN` ALREADY EXISTS.**
  * `HEADS="Lean4Lean.VInductDecl'.projTermG Lean4Lean.VExpr.lift'"` -> **2 hits**, 0 fields:
    `Lean4Lean.Rich.projTermG_lift'_fires` (arity 0, `Verify/Typing/ProjGenLiftWitness`) and
    `Lean4Lean.VInductDecl'.projTermG_lift'` (arity 16, `Verify/Typing/ProjGenLift`).
    => **`projTermG_weakN` ALREADY EXISTS, and it is already fired.**
  * `HEADS="Lean4Lean.VInductDecl'.etaExpansion Lean4Lean.VExpr.lift'"` -> **0 hits. NOTHING.**
  * `HEADS="Lean4Lean.VInductDecl'.etaExpansionG Lean4Lean.VExpr.lift'"` -> **0 hits. NOTHING.**
  * `HEADS="Lean4Lean.VInductDecl'.etaExpansionG Lean4Lean.VExpr.instL"` -> 13 hits, 0 fields,
    but **not one is a commutation lemma**: 11 are auto-generated recursors/`match`es of
    `VEnv.IsDefEqSE`/`VEnv.HasArgsSE` (`Theory/Typing/StructEtaPrice`,
    `Theory/Typing/ConfluenceRebuildPrice`), plus `VEnv.IsDefEqSE.structEta` (the constructor
    itself) and `VEnv.StructEtaG.congrProj_at_projAllG` (`Verify/TypeChecker/EtaStructG`).
    => **`etaExpansionG_instL` ABSENT.**
- M6 `shape.lean`, four confirming/helper queries, population 444, heads resolved:
  * `etaExpansion` + `Lean4Lean.VExpr.liftN` -> **0 hits**. So the absence of
    `etaExpansion_weakN` is not a `lift'`-vs-`liftN` spelling artefact.
  * `etaExpansionG` + `VExpr.liftN` -> **0 hits**. Same for the G variant.
  * `projAllG` + `VExpr.instL` -> 3 hits, all `VEnv.StructEtaG.{congrSpine,
    congrProj_at_projAllG, congrProj}` in `Verify/TypeChecker/EtaStructG` — congruence
    *consumers*, not commutation. So the `projAllG`/`instL` helper is absent too.
  * `projAllG` + `VExpr.lift'` -> **0 hits**.

## VERDICTS ON THE FIVE (measured, not grepped)

| brief name | verdict | the tree's name |
|---|---|---|
| `projTerm_weakN` | **ALREADY PRESENT** | `Lean4Lean.VInductDecl'.projTerm_lift'` |
| `projTermG_weakN` | **ALREADY PRESENT** | `Lean4Lean.VInductDecl'.projTermG_lift'` |
| `etaExpansion_weakN` | genuinely ABSENT | — |
| `etaExpansionG_weakN` | genuinely ABSENT | — |
| `etaExpansionG_instL` | genuinely ABSENT | — |

`StructEtaPrice.lean:53` claims all five are absent "(`scripts/exists.lean`, this round)". That
call was a **name** search against `_weakN`; the tree spells syntactic weakening `_lift'`, so two
of the five were false negatives. Prior 1 scored: correct (two already present). Prior 2 scored:
**correct** — the two present are exactly the `projTerm` pair, but I predicted plain-before-G and
in fact *both* plain and G are present for `projTerm` and *both* absent for `etaExpansion`; the
split is by term-former, not by G-ness. Prior 3 scored: correct, and it is the whole explanation.
- M7 First `lake build Lean4Lean.Theory.Typing.CommutationLemmas` of the new file:
  **155/155, green on the first attempt**, no error and no warning attributable to my file (the
  warnings replayed are pre-existing, in `PatWFIota`, `Verify/Typing/Lemmas`,
  `Verify/TypeChecker/IsDefEq`, `Verify/Typing/ProjClosedG`). Proved: `projAll_lift'`,
  `etaExpansion_lift'`, `etaExpansion_liftN`, `etaExpansion_weakN`, `projAllG_lift'`,
  `etaExpansionG_lift'`, `etaExpansionG_liftN`, `etaExpansionG_weakN`, `projAllG_instL`,
  `etaExpansionG_instL`. Prior 4 scored: **wrong in its direction** — `etaExpansionG_instL` is
  the *most* ordinary of the three (unconditional), and the non-ordinary asymmetry is on the
  `liftN` side instead: `projAll(G)` fixes `is := []`, and `projTerm(G)_lift'` carries
  `his : is.length = T.indices.length`, so the weakening lemmas need `T.indices = []` while the
  `instL` lemma needs nothing. That hypothesis is free at every `StructEta`/`StructEtaG` site.
- M8 §4 firings added; four iterations to green (`recFields` needed unfolding for the
  `ProjClosedG.recArgs` clause; `liftN`/`liftVar` and `instL`/`VLevel.inst` needed to be in the
  `simpa` set; the non-vacuity inequality needed `List.range bazCtor.fields.length = [0,1]`
  supplied by `rfl` before `mkApp` would reduce). Final
  `lake build Lean4Lean.Theory.Typing.CommutationLemmas`: **155/155 green**.
  `lean_diagnostic_messages` on the file: **zero items** — no error, no warning, no
  section-variable warning.
- M9 `exists.lean` on the ten new declarations (population 445): all **FOUND** in
  `Lean4Lean.Theory.Typing.CommutationLemmas`, every one **own value is a hole: false; cone
  reaches sorryAx: false; watched declarations in cone: none of 6**. Cones:
  `projAll_lift'` 2781, `etaExpansion_lift'` 2785, `etaExpansion_liftN` 2787,
  `etaExpansion_weakN` 2788, `projAllG_lift'` 3011, `etaExpansionG_lift'` 3015,
  `etaExpansionG_liftN` 3017, `etaExpansionG_weakN` 3018, `projAllG_instL` 881,
  `etaExpansionG_instL` 884. Support/firings: `bazDecl_projClosed` 218,
  `MutField.decl_projClosedG` 665, `etaExpansion_liftN_fires` 2803,
  `etaExpansion_liftN_fires_nontrivial` 2808, `etaExpansionG_liftN_fires` 3032,
  `etaExpansionG_instL_fires` 896 — same three clean lines each.
- M10 `users.lean` on the term-formers (population 445, 26602 non-internal decls).
  DIRECT / TRANSITIVE: `projTerm` **87 / 480**; `projTermG` **75 / 174**;
  `etaExpansion` **20 / 23**; `etaExpansionG` **57 / 92**; `projAll` **19 / 32**;
  `projAllG` **22 / 104**; `projTerm_lift'` **2 / 180**; `projTermG_lift'` **3 / 10**;
  and **`etaExpansion_instL` 0 / 0** — the existing narrow `instL` commutation lemma has
  *no* users at all, direct or transitive. That is the sharpest available comment on the
  ~40-site figure: it is a forecast about a constructor that does not exist yet, not a count
  of live demand.
- M11 `exists.lean` on the would-be consuming congruence sites (population 447). FOUND:
  `Lean4Lean.VEnv.IsDefEq.weakN` (`Theory/Typing/Lemmas`), `VEnv.IsDefEqStrong.weakN`
  (`Theory/Typing/Strong`), `VEnv.NormalEq.weakN` (`Theory/Typing/ChurchRosser`),
  `VEnv.ParRed.weakN` (`Theory/Typing/ChurchRosser`), `VEnv.ParRedK.weakN`
  (`Theory/Typing/KEta`), `VEnv.IsDefEq.instL` (`Theory/Typing/Lemmas`),
  `VEnv.IsDefEqStrong.instL` (`Theory/Typing/Strong`), `VEnv.NormalEq.instL_congr`
  (`Theory/Typing/ChurchRosser`). **NOT FOUND**: `VEnv.ParRed.instL`, `VEnv.ParRedK.instL`,
  `VEnv.IsDefEqE.weakN`, `VEnv.IsDefEqE.instL`, `VEnv.IsDefEqRaw.weakN`,
  `VEnv.IsDefEqRaw.instL`. So the consuming set is **5 weakN + 3 instL = 8 induction sites**,
  not ~40: `IsDefEqE` and `IsDefEqRaw` have no such lemma at all, and `ParRed`/`ParRedK` have
  no `instL`.
- M12 `users.lean` on those 8 (population 447, 26691 non-internal decls). DIRECT / TRANSITIVE:
  `IsDefEq.weakN` **30 / 2464**; `IsDefEqStrong.weakN` **10 / 1578**;
  `NormalEq.weakN` **7 / 305**; `ParRed.weakN` **3 / 293**; `ParRedK.weakN` **4 / 12**;
  `IsDefEq.instL` **14 / 2209**; `IsDefEqStrong.instL` **5 / 1550**;
  `NormalEq.instL_congr` **2 / 278**.
- M13 Round-close whole-tree `lake build`: **FAILS, and not in anything I own.** The only errors
  are in `Lean4Lean/Theory/SetModel/RecTypePeel.lean`, an **untracked file another stream is
  editing right now** (`git status` shows it `??` alongside `docs/handoff-recpeel.md`; its mtime
  was 26 s old at first check, and the error moved from `:362`/`:363` to `:379` between two
  consecutive builds). **Nothing imports it** (the `import Lean4Lean.Verify.Typing.RecTypePeel`
  lines in `ProjSpineInv.lean` and `Experimental/ConeJoin.lean` name a *different*, tracked,
  working module). My own module and its full import closure build green (M8). Not my file, not
  mine to fix — reporting, not touching.
- M14 `scripts/sorry-census-all.lean`: **HOLES over the whole built population, unioned across
  both passes: 13** (pass A 446 modules, pass B — the `Replay` reverse closure — 3).
  **BUILT 449; NOT BUILT 1**, and the sole NOT BUILT module is
  `Lean4Lean.Theory.SetModel.RecTypePeel` — the other stream's in-flight file from M13. So
  census is **13 / NOT BUILT 1**, and the 1 is not mine.
- M15 `lake build Lean4Lean.Verify.Guard`, three guards, all passing:
  * `guard 1: Axioms.lean declares exactly the 24 frozen axioms ✓`
  * `guard 2: kernel_sound axioms within whitelist ✓ (proof INCOMPLETE: sorryAx present)`
  * `guard 3: checker cone implementation gaps within frozen list (2/2 remaining) ✓`
- M16 The other stream's `RecTypePeel.lean` went green on the next poll. Re-run round-close:
  * whole-tree `lake build`: **Build completed successfully (1633 jobs)**, zero error lines.
  * `scripts/sorry-census-all.lean`: **BUILT 450; NOT BUILT 0**;
    **HOLES 13** (pass A 447 modules found 13, pass B 3 modules found 0).
  * three guards: as M15, all ✓.
  * in-repo section-variable warnings: **0** (grep for `section variable` over the full build log,
    restricted to `Lean4Lean/` paths).
  * `lean_diagnostic_messages` on `Theory/Typing/CommutationLemmas.lean`: zero items.

## SCORECARD ON PRIORS

1. "At least one of the five already exists" — **correct**, two did.
2. "The `G` variants are the likelier gap; plain-before-G" — **half right, for the wrong reason.**
   The split is by *term-former*, not by G-ness: both `projTerm` weakening lemmas were present
   (plain *and* G), both `etaExpansion` ones absent (plain *and* G). My stated mechanism
   ("a G former is newer than its plain counterpart") does not explain the data.
3. "Naming will not match; the verdict that matters is `shape.lean`'s" — **correct, and it is the
   entire explanation** for the pricing round's two false negatives.
4. "`etaExpansionG_instL` is the one likeliest to be non-ordinary" — **wrong, and inverted.** It is
   the *only* one of the three that is unconditional. The asymmetry is on the weakening side.
5. "The ~40-site estimate is probably too high" — **correct**, and by more than I expected. The
   consuming set for these five is 8 induction sites (M11), and the ~40 covers eight lemma
   families of which these five serve two.
6. "Direct ≪ transitive" — **correct** (M12: `IsDefEq.weakN` 30 direct / 2464 transitive, an 82x
   ratio; `IsDefEqStrong.instL` 5 / 1550, 310x).
