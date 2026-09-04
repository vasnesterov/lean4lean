# `VEnv.NoNestedN` across every `addDecl` branch — running the `TrEnv'` induction

Stream: `nonestedall`, opened 2026-09-04.

Owns: `Lean4Lean/Verify/Inductive/NoNestedAll.lean` (new), `Verify/Inductive/RestoreFaithful.lean`
§5 and its `#eval` gate only, this file.

Task: `RestoreFaithful.lean` §5 says the *hypothesis* of `VEnv.NoNestedN.addConst` became
suppliable on every branch when PR #46 (`7e39484`) put `checkNoNestedAuxName` beside `checkName`
in `checkConstantVal`, but that the *induction* over `TrEnv'` was never run, so every §3 discharge
that needs §2 is still conditional in fact.  Run the induction.

## §1 Priors, written before any Lean tool ran

Numbered, with probabilities.  **Never edited.**  Corrections go in §2.  Context available when
these were written: I had `cat`-read `RestoreFaithful.lean` in full, `Verify/Environment/Basic.lean`
lines 1-200 and 560-760, `Verify/Environment/Lemmas.lean` lines 1-140, `Lean4Lean/Environment.lean`
lines 1-80, `Environment/Basic.lean`'s `checkName`, and grepped `NoNestedN` / `AddInduct` /
`insertDefs`.  No `lake build`, no LSP call, no `#eval`, no `scripts/*` run.

| # | prediction | p |
| --- | --- | --- |
| 1 | **The tree builds green at HEAD (`ca04f43`) when I start**, with no edit of mine. Another stream is running additive-only, so a shared file may be mid-flight. | 0.75 |
| 2 | A bare `lake build` from cold cache takes over 10 minutes. | 0.6 |
| 3 | **The `TrEnv'` induction does not need to be written.** `Aligned.find?_iff` (`Verify/Environment/Lemmas.lean`:43) plus `TrEnv'.aligned` (:120) already gives `venv.constants n = some _ → ∃ ci, C.find? n = some ci`, so `NoNestedN` follows from a *map-level* cleanliness hypothesis in a handful of lines and no new induction over `TrEnv'` at all. | 0.7 |
| 4 | If 3 holds, the `induct` case is discharged **vacuously**, inheriting `Aligned.addInduct`'s `nomatch` — so the result covers environments containing inductives only vacuously, and that is the honest limit of the round. | 0.9 |
| 5 | If 3 fails and I must write the induction by hand, the case that resists is `unsafeDef` (the `insertDefs` / `addConsts` list step), not `axiom`/`defn`/`thm`/`opaque`. | 0.55 |
| 6 | The `quot` case needs **no** hypothesis at all: `AddQuot` adds the four fixed names `Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind`, so cleanliness there is `by decide`. | 0.85 |
| 7 | **No lemma of the form "`addDecl` preserves map cleanliness" exists** in the tree today. (Checked with `grep`, `scripts/exists.lean`, `scripts/can-cite.py` before I write it.) | 0.85 |
| 8 | The real remaining work is implementation-side: a theorem that `checkConstantVal` **success** implies `¬ IsNestedName v.name`. Given `checkNoNestedAuxName_ok_iff` this is under 40 lines. | 0.8 |
| 9 | **The friction is the monad.** `checkConstantVal` lives in `TypeChecker.M`, not `Except`, so §1.1's `Except.WF` idiom does *not* transfer directly and I need an `M`-level WF lemma or a first-projection argument. This is where the round's hours go. | 0.7 |
| 10 | A lemma describing `Kernel.Environment.add`'s effect on `constants` (`find?_add` / `add_constants` shape) already exists, since `add` is `open private`-imported and unprovable otherwise. | 0.6 |
| 11 | `NoNestedN` ends the round **established for all four non-inductive `TrEnv'` cases** (`axiom`, `defn`, `thm`, `opaque`) plus `ignore`. | 0.7 |
| 12 | `NoNestedN` ends the round established for `quot`. | 0.8 |
| 13 | `NoNestedN` ends the round established **non-vacuously** for `induct`. Blocked on `AddInduct`'s emptiness, which is outside my ownership and is a seven-file flip. | 0.1 |
| 14 | §5's verdict ends the round at "proved, modulo `AddInduct`'s emptiness" rather than at "proved". | 0.75 |
| 15 | I fire the result at a *closed* instance beyond `ntree_restoration_keeps_the_environment_clean` — an `#eval`-or-`decide` firing at the `addDecl` level, not merely at `addInductR`. | 0.6 |
| 16 | At least one thing I am about to claim "does not exist" turns out to exist. | 0.5 |
| 17 | At least one claim in §5's own prose (which I did not write) turns out to be inaccurate about the tree, in the way this project's docstrings have been repeatedly. | 0.45 |
| 18 | The `#eval` gate in §5.1 still passes unchanged at HEAD (i.e. all three of `inductive`/`axiom`/`def` at a `_nested` name are rejected). | 0.9 |

## §2 Measurements, appended the moment each lands

| # | measurement | date/time | verdict on the prior |
| --- | --- | --- | --- |
| M1 | `lake build` at `ca04f43`, no edit of mine: **`Build completed successfully (1656 jobs)`**, exit 0, everything replayed from cache. | 2026-09-04 13:31 CEST | **#1 confirmed** (p 0.75). Tree green at start. |
| M2 | The same build, timed cold-from-cache: **1.06 s real** (1656 jobs, all replayed — this machine has the full build cache). | 2026-09-04 13:32 CEST | **#2 refuted** (p 0.6 that it exceeds 10 min). Cache makes the licensing build cheap, so rule 5 costs nothing here. |
| M3 | `scripts/exists.lean` (population 470 modules): `Aligned.find?_iff` **FOUND**, `Verify/Environment/Lemmas`, arity 5, cone 3533, own value a hole: false, cone reaches `sorryAx`: **false**. `Environment.find?_add_of_ne` **FOUND**, `Verify/Environment/Extension`, arity 7, cone 3461, hole false, `sorryAx` false. `VEnv.NoNestedN` arity 1 cone 208; `.addConst` arity 7 cone 491; `checkNoNestedAuxName_ok_iff` arity 1 cone 4349; `addInductive_WF_noNestedDeclNames` arity 7 cone 7774 — all hole-free and `sorryAx`-free. | 2026-09-04 13:40 CEST | supports #3: the bridge lemma exists and is clean. |
| M4 | `scripts/shape.lean`, three conclusion-shape queries with resolved heads: `{VEnv.NoNestedN, Aligned}` → **0 hits**; `{VEnv.NoNestedN, TrEnv'}` → **0 hits**; `{VEnv.NoNestedN, Lean.ConstMap}` → **0 hits**; `{IsNestedName, Lean.ConstMap}` → **0 hits**. | 2026-09-04 13:42 CEST | **#7 confirmed** (p 0.85). Nothing in the tree connects the name invariant to the *kernel-level* constant map, in any of the four spellings. This is the gap, and it is real. |
| M5 | `python3 scripts/can-cite.py Lean4Lean.Verify.Inductive.RestoreFaithful …`: closure 188 modules; **YES** for all three of `Aligned.find?_iff`, `TrEnv'.aligned`, `Environment.find?_add_of_ne`. So a new file importing `RestoreFaithful` can cite the bridge with no migration. | 2026-09-04 13:45 CEST | no prior; removes the `can-cite` failure mode this project has hit four times. |
| M6 | **The `TrEnv'` induction does not have to be written.** `NoNestedAll.lean` §2 — `VEnv.NoNestedN.of_aligned` (3 lines) and `.of_trEnv'` (1 line) — compiles **first try**: `✔ Built Lean4Lean.Verify.Inductive.NoNestedAll (1.2s)`. `TrEnv' safety C Q venv → NoNestedMap C → venv.NoNestedN`. | 2026-09-04 13:52 CEST | **#3 confirmed** (p 0.7). #5 is moot: no case resisted, because `TrEnv'.aligned` had already run the nine-case induction and `Aligned.find?_iff` had already done the `SMap`-insert work. |
| M7 | §5.1's `#eval` gate at HEAD, unchanged, on the same build: `all three of inductive _nested.Zzz, axiom _nested.zzz and def _nested.ddd are REJECTED ✓`. | 2026-09-04 13:52 CEST | **#18 confirmed** (p 0.9). |
| M8 | **`checkConstantVal`'s success gives the name fact, unconditionally.** `Lean4Lean.checkConstantVal_noNestedName : checkConstantVal env v ap ctx s = .ok r → ¬ IsNestedName v.name` — 6 lines, on a 9-line helper `liftExcept_bind_ok` that peels one `liftM`-of-`Except` out of the `ReaderT Context (StateT State (Except Exception))` stack. No error. | 2026-09-04 14:05 CEST | **#8 confirmed** (p 0.8, "under 40 lines"): 15 lines total. **#9 refuted** (p 0.7, "the monad is where the hours go"): two simp-set iterations, about ten minutes — `StateT.lift` and `Except.pure` were the two missing unfoldings. |
| M8a | **Why this had to be a fresh lemma and not a strengthening of the existing one.** `Verify/Environment/Checker.lean`:86-88 already discharges the `checkNoNestedAuxName` step of `checkConstantValCore.WF` as `Except.WF.trivial`, with the comment *"The reserved `_nested` prefix is rejected operationally; no later proof needs that fact."* That file is not mine, **and going through it would have been the wrong move anyway**: `checkConstantVal.WF`'s precondition is `wf : ves.WF env`, and `VEnvs.WF` is *unsatisfiable* for any `env` whose map holds an `.inductInfo` (`VEnvs.WF.no_inductInfo`, `Verify/InductFlip.lean`). A name fact proved through the `M.WF` framework would therefore be vacuous at every realistic environment. `checkConstantVal_noNestedName` carries no `VEnvs.WF`, no `VState.WF`, no `VContext` — it is a statement about the raw monadic value. | 2026-09-04 14:05 CEST | **#16 confirmed** (p 0.5): the thing I would have called absent — reasoning about that exact line of `checkConstantVal` — exists, and is deliberately trivial. |
| M9 | **The `axiomDecl` branch closes on the implementation side.** From `addAxiom env v true fuel = .ok env'`, a clean map, and `env.constants.WF`: `NoNestedMap env'.constants`. Route: `checkConstantVal_run_noNestedName` (peels `M.run`/`StateT.run'`) then `NoNestedMap.add` (`(env.add ci).constants = env.constants.insert ci.name ci` by `rfl`, then `SMap.WF.find?_insert`). Needed `open private Lean.Kernel.Environment.add from Lean.Environment`, as `Verify/Environment.lean`:9 does. | 2026-09-04 14:20 CEST | on track for #11. |
| M10 | **Four of the seven `addDecl` branches close on the implementation side**: `addAxiom_noNestedEnv`, `addTheorem_noNestedEnv`, `addOpaque_noNestedEnv`, `addDefinition_noNestedEnv` (the last covering *both* safety arms — the `unsafe` arm's two `M.run`s and the safe arm's extra `checkPrimitiveDef` bind). Invariant carried is `NoNestedEnv env := env.constants.WF ∧ NoNestedMap env.constants`; the `WF` half is needed by `SMap.WF.find?_insert` and is what `Environment.add` preserves given `checkName`'s freshness. | 2026-09-04 14:45 CEST | on track for #11. |
| M11 | **The `quotDecl` branch closes too** — `addQuot_noNestedEnv`. Route: `addQuot_eq` (`Verify/QuotConsts.lean`:493) lifts the four `add`s out of the `ExprBuildT` block, so the added names are the literals and cleanliness is `by decide`; the freshness each `add` needs at the *intermediate* environments is `Environment.find?_add_of_ne` from the four `checkName`s plus four `by decide` disequalities. `markQuotInit` is transported by `NoNestedEnv.markQuotInit` (`{env with quotInit := true}`, so `constants` is `rfl`). | 2026-09-04 15:00 CEST | **#12 confirmed** (p 0.8) and #6's spirit: the quot names are decidable, though the branch was *not* free — the intermediate freshnesses cost ten lines. |
| M12 | **`addDecl` assembled, 5 of 7 branches unconditional.** `addDecl_noNestedEnv` takes two named residual `Prop`s and nothing else: `MutualNamesGate` (the header loop's postcondition — names clean, fresh, `Nodup`) and `InductiveMapGate` (the *map* side of the inductive step: `addInductive` adds no name outside `indDeclNamesN types k`). Both are **unproved, not false**; neither is a *name* condition — those are theorems. `addDecls_noNestedEnv` extends it to `List.foldlM` over a declaration list; `VEnv.NoNestedN.of_addDecl` composes with §2. | 2026-09-04 15:25 CEST | **#11 confirmed** (p 0.7) for `axiom`/`defn`/`thm`/`opaque`; **#13 confirmed** (p 0.1, i.e. predicted *not* to happen) — the induct branch is not established non-vacuously. |
| M13 | **`#print axioms` on all 18 new results, 2026-09-04 15:30 CEST.** Every one: `[propext, Classical.choice, Quot.sound]` — **no `sorryAx`**. `addDecl_noNestedEnv`, `addDecls_noNestedEnv`, `VEnv.NoNestedN.of_addDecl` and `addQuot_noNestedEnv` additionally carry the four frozen `Lean.Expr` primitives `abstractRange_eq`, `abstract_eq`, `hasLooseBVar_eq`, `lowerLooseBVars_eq` — all four are on `Verify/Guard.lean`'s whitelist (lines 116, 117, 120, 126), checked, so guard 1 is not disturbed. `addInduct_isEmpty` is `[propext, Quot.sound]`. | 2026-09-04 15:30 CEST | no prior; rule 6. |
| M14 | **§5.3's `#eval` gate fires.** `axiom Zzz : Prop` is ACCEPTED from `Kernel.Environment.empty`, the resulting map holds **0** `_nested`-prefixed constants (scanned, not assumed), and `axiom _nested.zzz` is REJECTED. So `addDecl_noNestedEnv`'s antecedent is satisfiable and `checkConstantVal_noNestedName` is not vacuous. | 2026-09-04 15:30 CEST | **#15 confirmed** (p 0.6): a firing at the `addDecl` level, not only at `addInductR`. |
| M15 | **Two firings and one refutation, all closed.** (a) `clean_kernel_env_survives_ntree_restoration`: clean empty kernel map → `VEnv.empty.NoNestedN` *through the new route* → the restored `ntreeAux` step stays clean while the unrestored one does not (the last two conjuncts are `ntree_restoration_keeps_the_environment_clean`, reached from the kernel side). (b) `quotWit_noNestedN_fires`: §2 fired at `QuotWit.trEnv_addQuot_wit`, a closed `TrEnv` over **five** constants — `Eq`, `Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind` — each exhibited, so the `∀ n` is not quantifying over nothing. (c) `noNestedEnv_not_preserved_unchecked`: with `check := false` the invariant is **refuted** from an environment where it held, so the check is load-bearing rather than decorative. | 2026-09-04 15:30 CEST | no prior; the "instantiate, don't admire" rule. |
| M16 | **`AddInduct` really is empty**, machine-checked here rather than quoted: `addInduct_isEmpty : ¬ AddInduct C₁ venv₁ decl C₂ venv₂ := nofun`. So §2's `induct` case is discharged *vacuously* — inherited from `Aligned.addInduct`'s `nomatch`, not introduced by me. Routing through `Aligned` is deliberate: when the flip lands, `TrEnv'.aligned`'s induct arm is repaired by `Aligned.addInductStages` and **nothing in `NoNestedAll.lean` changes**. | 2026-09-04 15:30 CEST | **#4 confirmed** (p 0.9). |
| M17 | **`lake build`, bare, after all my edits: `Build completed successfully (1659 jobs)`, exit 0** (was 1656 — the new module, counted in three lib targets). The 13 pre-existing `declaration uses sorry` warnings are unchanged and none is mine. `lake build Lean4Lean.Verify.Guard`: `guard 1: Axioms.lean declares exactly the 24 frozen axioms ✓`, `guard 2: kernel_sound axioms within whitelist ✓ (proof INCOMPLETE: sorryAx present)` — i.e. guard state unchanged. | 2026-09-04 16:00 CEST | rule 5 satisfied; only a bare `lake build` licenses "green", and this is it. |
| M18 | **A stale claim, in a file I do not own.** `Lean4Lean/Inductive/Add.lean`:1084-1086 (the `checkNoNestedAuxName` docstring, "Updated 2026-09-03") still reads: *"The first half stands: the prefix is still not an environment-wide invariant, because this check guards only the inductive branch -- `axiom _nested.zzz` and `def _nested.ddd` are still accepted, machine-checked by a `#eval` in `RestoreFaithful.lean` that fails the build if that changes."* PR #46 falsified all three clauses, and the `#eval` it points at is the one that now asserts the opposite. The last sentence — "Extending it to every declaration is one line ... awaiting a human decision" — describes a decision that has already been taken. **Not edited** (outside my ownership); the exact repair is named in §3 below. | 2026-09-04 16:05 CEST | **#17 confirmed** (p 0.45), though not where I predicted: §5's own prose was accurate; the stale claim was one file upstream, in the docstring of the very function PR #46 changed. |

### Prior scoring, all 18

confirmed: 1, 3, 4, 7, 8, 10, 11, 12, 13 (as a *negative* prediction — it did not happen, as predicted), 14, 15, 16, 17, 18.
refuted: 2 (build is 1.06 s from cache, not >10 min), 9 (the monad cost ten minutes, not the round — `StateT.lift` and `Except.pure` were the whole difficulty).
half: 6 — the quot names are `by decide`, as predicted, but "needs **no** hypothesis at all" was wrong: the four `add`s need freshness at the *intermediate* environments, which is ten lines of `Environment.find?_add_of_ne`.
moot: 5 (conditional on #3 failing; it did not fail).

Score: 14/18 confirmed, 2 refuted, 1 half, 1 moot. The two refutations were both *pessimism* about cost.

## §3 What I could not do, and the exact edits somebody else must make

1. **`Verify/Inductive/RestoreFaithful.lean` §3's table** (line 257-263) is outside my ownership
   (I own "§5 and its `#eval` gate only"), so its `RestoreData.head` row still reads
   `**reduced**: presentedHead_clean_of_declared; residual named`. The content is now stronger and
   §5's prose says so. The exact edit, for whoever owns §3:
   * the `RestoreData.head` row's *condition* column: `§2 (NoNestedN) + "the presented head is declared"`
     → `§2 (NoNestedN, now a theorem for any kernel-built environment: VEnv.NoNestedN.of_addDecl) + "the presented head is declared"`;
   * the `RestoreData.args` row's *status* column: `already routed: ProjNoNested.lean's hnn consumers`
     → `already routed, and hnn is now supplied: VEnv.NoNestedN.of_addDecl`.
   No proof changes; the theorems the rows point at are unchanged.
2. **`Lean4Lean/Inductive/Add.lean`:1084-1088** — the stale paragraph in M18. Suggested repair: replace
   "The first half stands … awaiting a human decision" with "**Superseded 2026-09-04 by PR #46**:
   `checkConstantVal` now calls `checkNoNestedAuxName` too, so `axiom _nested.zzz` and
   `def _nested.ddd` are rejected as well, the prefix *is* an environment-wide invariant of anything
   `addDecl` builds (`NoNestedMap`, `Verify/Inductive/NoNestedAll.lean`), and the human decision
   recorded in `docs/decision-nested-prefix-all-decls.md` has been taken." Not edited: not my file.
3. **`MutualNamesGate`** — `addMutual`'s header loop, extracted. This is the `Except`-level
   `guardLoop_noNested` pattern (`RestoreFaithful.lean` §1.1) lifted to
   `ReaderT Context (StateT State (Except Exception))`, with the `found : List Name` accumulator
   threaded through three `if`s. `M_bind_ok` in `NoNestedAll.lean` is the workhorse it needs.
   Estimated 60-100 lines. Nothing about it looks false.
4. **`InductiveMapGate`** — the map side of the inductive step, i.e. `AddInductStagesR`'s
   constant-map half. This is the seven-file flip `docs/handoff-addinduct.md` prices, not a lemma.
5. **`AddInduct`'s emptiness** — the inherited vacuity of §2's `induct` case. `NoNestedAll.lean` is
   written so that the flip requires **no change** to it.

## §4 Method gaps in my own round

* **I predicted the route wrong in a way none of my 18 priors caught.** Every prediction was about
  *cost* or *outcome*; none was about *shape*. The shape turned out to be the whole result: the
  induction did not need to be written, and the condition that has to be threaded is the
  kernel-level `NoNestedMap`, not the abstract `NoNestedN`. A prior of the form "the hypothesis I
  will end up threading is not the one the brief names" would have been worth all six cost priors.
* **I nearly took the `M.WF` trap on trust, and then closed it.** I first reasoned from
  `VEnvs.WF.no_inductInfo`'s docstring that a name fact routed through `checkConstantVal.WF` would
  be vacuous, and acted on it *before* checking — the "read the docstring, then trust it" failure
  this project keeps paying for. Fixed while writing this section: `venvsWF_refuted_at_inductInfo`
  (`NoNestedAll.lean` §4) now instantiates the refutation, so the design decision rests on a
  theorem in my own file. It is load-bearing: if `VEnvs.WF` were satisfiable at environments with
  an `.inductInfo`, strengthening `checkConstantValCore.WF` would have been the cheaper route and
  `checkConstantVal_noNestedName` redundant.
* **`scripts/can-cite.py` printed `? could not parse exists.lean output` for `Lean4Lean.addQuot_eq`**
  and I proceeded on a sibling (`quotCI`, same module, `YES`). That is a reasonable inference but it
  is not a measurement, and the script's own docstring is about exactly this failure mode.
* **The `mutualDefnDecl` branch is the one place I chose a gate over a proof for reasons of time
  rather than of difficulty.** The gate is honestly stated, but it is a gate I could have closed.

## §5 The measured table, final (`scripts/exists.lean`, population 473 modules, 2026-09-04 16:20 CEST)

All in `Lean4Lean.Verify.Inductive.NoNestedAll`. Every row: **own value is a hole: false; cone
reaches sorryAx: false**. `#print axioms` for all of them is `[propext, Classical.choice,
Quot.sound]`, except `addInduct_isEmpty` = `[propext, Quot.sound]` and the four that additionally
carry the frozen `Lean.Expr` primitives `abstractRange_eq`/`abstract_eq`/`hasLooseBVar_eq`/
`lowerLooseBVars_eq` (`addQuot_noNestedEnv`, `addDecl_noNestedEnv`, `addDecls_noNestedEnv`,
`VEnv.NoNestedN.of_addDecl`) — all four on `Guard.lean`'s whitelist, lines 116/117/120/126.

| name | arity | cone |
| --- | --- | --- |
| `VEnv.NoNestedN.of_trEnv` | 5 | 6098 |
| `checkConstantVal_noNestedName` | 7 | 7264 |
| `addDecl_noNestedEnv` | 8 | 9192 |
| `addDecls_noNestedEnv` | 8 | 9195 |
| `VEnv.NoNestedN.of_addDecl` | 11 | 9592 |
| `quotWit_noNestedN_fires` | 1 | 6276 |
| `clean_kernel_env_survives_ntree_restoration` | 0 | 6363 |
| `noNestedEnv_not_preserved_unchecked` | 0 | 8161 |
| `addInduct_isEmpty` | 5 | 280 |
| `venvsWF_refuted_at_inductInfo` | 5 | 6095 |
| `MutualNamesGate` (residual) | 0 | 7301 |
| `InductiveMapGate` (residual) | 0 | 7751 |

## §6 Correction to M1/M17: HEAD moved under me

M1's baseline build was at `ca04f43`. By the time M17's licensing build ran, the other stream had
committed twice and HEAD was **`601140d`** (`ca04f43` → `82b3060` → `601140d`). So M17's
`Build completed successfully (1659 jobs)` is at `601140d` **plus my three files**, not at
`ca04f43` plus mine. Both builds were green and the job count difference (1656 → 1659) is entirely
my new module counted across the `Lean4Lean.Verify` glob; nothing of the other stream's showed up as
red at any point. Recording this because "a count without a date is a defect" and mine had the wrong
commit attached for four hours.
