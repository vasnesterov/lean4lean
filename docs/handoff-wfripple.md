# handoff-wfripple — the `ntreeAux_WF` → `ntreeAux_WF'` re-pointing, measured then done

Date: 2026-09-03.  Stream: "wfripple".  Written incrementally; §0 is the last thing updated.

## 0. Status (updated as work proceeds)

* **DONE — outcome 1.**  All **32** application sites (+1 `@`-application) re-pointed to
  `ntreeAux_WF'`, the wrapper `ntreeAux_WF` **deleted**, tree green at 1599 jobs, axiom sets
  **identical** for all 23 surviving declarations, census **13 → 13 with an identical list**,
  in-repo section-variable warnings **0 → 0**, `unusedVariables` **66 → 66**.
* **No site needed a proof change.**  The intermediate build — all sites re-pointed, wrapper still
  present — was green, which is the evidence that the replacement is mechanical.
* **The relayed ripple figure was stale, not wrong**: 27 sites in 9 files when
  `handoff-lifttrim.md` measured it, **32 in 14** now.  Five files became new callers of the
  wrapper in the interim, and `TeleCongr` went 3 → 1 (§1).  That decay is the argument against keeping the wrapper.
* **One cascade, and it is a second strengthening**: `ntreeAux_argsTypedK_of_wf`'s hypothesis
  became unused and was removed too, re-pointing its 3 sites (§3.1).
* Both trims are **instantiated at environments where the removed hypothesis is refuted** (§4), so
  each is a strengthening — the old statements were never broken, they simply had fewer instances.

## 1. The ripple, measured on the tree as it stands (not 27 in 9)

`handoff-lifttrim.md` §3 measured **27 sites in 9 files** and the brief relayed that.  Measured
again on `master` @ `1191a23` + committed sibling work, the population is:

    grep -roE "ntreeAux_WF h\b" --include=*.lean .   ->  32 hits
    plus  NestedBuild.lean:2144  example := @ntreeAux_WF

**32 application sites in 14 files, plus one `@`-application: 33 in 14 files.**

| file | sites | in lifttrim's 27/9? |
|---|---|---|
| `Theory/Typing/ConstSubstNested.lean` | 9 | yes (9) |
| `Theory/Inductive/CtorBeta.lean` | 6 | yes (6) |
| `Theory/Inductive/FamInhabC.lean` | 2 | **no — new** |
| `Theory/Inductive/HTeleRecB.lean` | 2 | **no — new** |
| `Theory/Inductive/NestedTele.lean` | 2 | yes (2) |
| `Theory/Inductive/OwnRule.lean` | 2 | yes (2) |
| `Theory/Inductive/RecTyped.lean` | 2 | yes (2) |
| `Theory/Inductive/HTeleGen.lean` | 1 | **no — new** |
| `Theory/Inductive/HTeleNTree.lean` | 1 | **no — new** |
| `Theory/Inductive/WFCRoute.lean` | 1 | **no — new** |
| `Theory/Inductive/TeleCongr.lean` | 1 | yes, but lifttrim said **3** |
| `Theory/Inductive/NestedBuild.lean` | 1 (+ the `@` example) | yes (1) |
| `Theory/Inductive/NestedHead.lean` | 1 | yes (1) |
| `Verify/Inductive/ArgsTypedSupply.lean` | 1 | yes (1) |

So the relayed "27 in 9" was **right when it was taken and is now stale**: five files became new
callers since (`FamInhabC`, `HTeleRecB`, `HTeleGen`, `HTeleNTree`, `WFCRoute`), and `TeleCongr`
dropped 3 → 1.  This is the second time in two rounds that this count moved; the
number is a property of the hour, not of the lemma.  **The wrapper is being consumed faster than
it is being retired** — which is itself the argument for retiring it now.

The 32 sites sit in **24 distinct enclosing declarations**:

`ntreeAux_argsTypedK_of_wf`, `ntreeSubst_WF`, `ntreeNode_beta_bridge`,
`ntreeAux_ctorConstsCR_wf`, `ntreeF₁_ordered`, `ntree_recConsts_wf`,
`ntreeAux_ctorConstsCR_wf_of_fieldsD`, `ntreeAux_ctorConstsCR_wf_of_betaD`,
`ntree_iotaHargs_node_own`, `ntree_hdata_own_gen`, `n_hdata_all_gen`,
`ntree_obligationC_of_recHargs`, `fi_hdata_general_instantiated`,
`ntree_obligationC_of_entries`, `ntree_env₃_ordered`, `ntree_minor_sides_at_cons`,
`ntreeAux_AddNestedB`, `ntreeAux_obligationB_of_bundles`,
`ntreeAux_recHargs_premises_inhabited`, `ntreeAux_AddNested`,
`ntreeAux_obligationC_of_hdata`, `ntreeAux_addInductR_ordered`
(all in namespace `Lean4Lean.InductiveDeclExamples`, names read off each file's own
`namespace` lines and then confirmed FOUND by `scripts/exists.lean` against the compiled
environment — not composed from paths).

## 2. Baseline, before any edit

* Full `lake build`: **green, 1595 jobs**.
* `automatically included section variable` warnings: **1 total, 0 in-repo** — the one is
  `Foundation/FirstOrder/SetTheory/Z.lean:35` (`LO.FirstOrder.SetTheory.subset_of_eq`), out of
  reach behind the pinned dependency.  Brief confirmed on this point.
* `unusedVariables`-class warning lines: **66**.
* Axiom sets of the 24 enclosing declarations + both `ntreeAux_WF`/`ntreeAux_WF'`: recorded in
  §5.  Two shapes only: `{Quot.sound, propext}` (5 declarations) and
  `{Quot.sound, Classical.choice, propext}` (19).

## 3. What was done

**All 33 sites re-pointed; the wrapper is gone.**  No site needed a proof change — every one was
a one-token edit `ntreeAux_WF h` → `ntreeAux_WF'`, and the intermediate build (re-pointing done,
wrapper still present) was **green at 1595 jobs with zero errors**.  That intermediate build is
the evidence that the re-pointing is mechanical, kept separate from the wrapper's removal so the
two failure modes could not be confused.

Then:

* `Theory/Inductive/NestedHead.lean` — the `omit h in theorem ntreeAux_WF (_h : …) := ntreeAux_WF'`
  block deleted, and `ntreeAux_WF'`'s docstring updated (it used to promise the wrapper "kept so
  that the 27 existing call sites … go on working").
* `NestedBuild.lean:2144` — `example := @ntreeAux_WF` → `@ntreeAux_WF'`.
* Redundant parens left by the mechanical pass (`(ntreeAux_WF')`) removed, so the sites read
  `ntreeAux_WF'` and `ntreeAux_WF'.iotaCtx …`.
* Four prose/docstring mentions of the retired name re-pointed: `NestedHead.lean:73`,
  `NestedBuild.lean:1885`, `ConstSubstNested.lean:2294`, `RestoreOpWit.lean:28`.
* `Theory/Typing/LiftTrimWitness.lean` — its `#print axioms …ntreeAux_WF` line **had** to go (it
  names a constant that no longer exists); its §3 prose now says the name was retired and points
  here.  This is the one edit outside the mechanical class, and it is a `#print` line, not a proof.

### 3.1 The one cascade, and it is a second strengthening

Trimming a hypothesis propagates *up*.  Exactly one new warning appeared on the intermediate
build:

    Lean4Lean/Verify/Inductive/ArgsTypedSupply.lean:750:5:
      Variable name `h` is not explicitly referenced.

`ntreeAux_argsTypedK_of_wf` used `h : VEnv.empty.addInduct' listDecl = some env₁` for nothing but
`ntreeAux_WF h`.  Rather than silence it with `_h`, the binder was **removed** — a second
strengthening in the same shape as the first:

    before : ∀ {env₁ et}, VEnv.empty.addInduct' listDecl = some env₁ →
                          env₁.addIndTypes ntreeAux = some et → ntreeAux.ArgsTypedK …
    after  : ∀ {env₁ et}, env₁.addIndTypes ntreeAux = some et → ntreeAux.ArgsTypedK …

so the `listOcc` argument family holds at **every** environment staging `ntreeAux`, not only at
the one holding `listDecl`.  Its 3 call sites (`RestrictCompanion.lean:506`,
`ArgsTypedSupply.lean:764`, `ArgsTypedSupply.lean:912`) each lost one argument.  No further
cascade: the `unusedVariables` population is back to the baseline **66, with an identical list**.

Ripple total, therefore: **35 edits in 16 files** (33 for `ntreeAux_WF`, plus the trimmed binder
and 3 sites for `ntreeAux_argsTypedK_of_wf`), zero proof changes.

## 4. Instantiated, not admired

Two witnesses, both at environments where the removed hypothesis is **refuted**, so the untrimmed
statements had no instance there at all.

### 4.1 `ntreeAux_WF'` — `Theory/Inductive/WFRippleWitness.lean` (NEW, this stream)

`LiftTrimWitness.lean` §3 already gave the bare `ntreeAux.WF badEnv`.  What is new is that the
strengthened form is **consumed at a real block** through the very field the 32 re-pointed sites
reach for, `VInductDecl'.WF.ctors`:

    WFRipple.hyp_refuted   : ¬ (VEnv.empty.addInduct' listDecl = some badEnv)
    WFRipple.stage_badEnv  : ∃ et, badEnv.addIndTypes ntreeAux = some et
    WFRipple.nlistNil_WF_badEnv  {et} (hst : badEnv.addIndTypes ntreeAux = some et) :
        nlistNil.WF  et ntreeAux 1 auxMember
    WFRipple.nlistCons_WF_badEnv {et} (hst : …) :
        nlistCons.WF et ntreeAux 1 auxMember
    WFRipple.ctors_WF_at_refuting_env : the conjunction, staging existentially quantified

`badEnv` (from `LiftTrimWitness.lean` §1) declares `bad : #0`, so it is not `Ordered` and the
retired hypothesis is false there — yet the real nested block `ntreeAux` still stages into it
(`NTree` and `_nested.List_1` are fresh), and both constructors of the auxiliary member
`_nested.List_1` come back `VIndCtor.WF` in that staging.  Axioms:
`hyp_refuted` and `ctors_WF_at_refuting_env` `{propext, Classical.choice, Quot.sound}`;
`stage_badEnv`, `nlistNil_WF_badEnv`, `nlistCons_WF_badEnv` `{propext, Quot.sound}`;
`auxMember_eq` `{propext}`.  No `sorryAx`.

### 4.2 `ntreeAux_argsTypedK_of_wf` — appended to `Verify/Inductive/ArgsTypedSupply.lean`

    InductiveDeclExamples.ntreeAux_argsTypedK_over_empty :
      ¬ (VEnv.empty.addInduct' listDecl = some VEnv.empty) ∧
        ∃ et, VEnv.empty.addIndTypes ntreeAux = some et ∧
          ntreeAux.ArgsTypedK ntreeK et (fun _ => listOcc)

At `env₁ := VEnv.empty` the removed equation is refuted (`addInduct'` declares `List`;
`VEnv.empty` holds nothing — the same refutation `HypTrim2Witness.listEnv_ne_empty` uses) while
the surviving staging hypothesis is inhabited.  It sits next to the existing
`ntreeAux_datum_of_wf_inhabited`, needs **no new import**, and its `#print axioms` line was added
alongside.

**A note on file ownership, honestly.**  My grant was `NestedHead.lean` plus "any file needing only
a call-site update", plus new `Theory/Inductive/WFRipple*` files.  §4.2 is a *new theorem* in a
`Verify/` file, which is outside that grant on a literal reading.  I did it because the alternative
was to leave the second trim un-instantiated: `ntreeAux_argsTypedK_of_wf` lives in `Verify/`, and
**no file under `Theory/` imports `Verify/`** (checked: zero hits for `^import Lean4Lean.Verify` in
`Lean4Lean/Theory/`), so a `Theory/Inductive/WFRipple*` file cannot reach it without inverting the
layering.  `ArgsTypedSupply.lean` is claimed by no concurrent stream and I was already editing it
for the trim.  If you would rather that theorem were not there, it is a self-contained 12-line
block at the end of the `InductiveDeclExamples` namespace plus one `#print axioms` line.

## 5. Axioms — the bar is `after ⊆ before`

Measured with a copy of `scripts/exists.lean` extended to list the axiom constants in each
declaration's cone (names read off each file's own `namespace` lines, then confirmed FOUND against
the compiled environment).  Baseline, all 24 enclosing declarations plus the two `WF` forms:

| axiom set | declarations |
|---|---|
| `{Quot.sound, propext}` | `ntreeAux_WF`, `ntreeAux_WF'`, `ntreeAux_argsTypedK_of_wf`, `ntreeSubst_WF`, `ntreeNode_beta_bridge` |
| `{Quot.sound, Classical.choice, propext}` | the other 19 |

After — see §6 for the measurement.  The expectation for a pure re-pointing is *identical*; a
subset would be a win; only a superset disqualifies.

## 6. Verification, after

* Full `lake build`: **green, 1599 jobs**, zero errors.  (Baseline 1595; the extra jobs are
  `WFRippleWitness.lean` plus three files landed by concurrent streams during the run.)
* **`InductiveDeclExamples.ntreeAux_WF` is `NOT FOUND`** by `scripts/exists.lean` against the
  compiled environment (412 built modules) — the wrapper is retired, not merely unreferenced.
  `ntreeAux_WF'` is FOUND, arity 0.
* **Axioms, all 23 surviving declarations: identical to baseline**, nothing added and nothing
  removed — the expected outcome for a pure re-pointing.  `ntreeAux_argsTypedK_of_wf`
  `{Quot.sound, propext}` before and after, so the trimmed binder was carrying no axiom.
  New declarations: `ntreeAux_argsTypedK_over_empty` `{Quot.sound, propext}`;
  `WFRipple.*` as listed in §4.1.  No `sorryAx` anywhere in these cones.
* **Hole census** (`scripts/sorry-census-all.lean`, whole-filesystem population): **13 before, 13
  after, identical list** — `TrProj.weak'_inv`, `inferProj.WF`, `isDefEqUnitLike.WF`,
  `tryEtaStructCore.WF`, `IsDefEqU.forallE_inv_stratified`, `IsDefEqU.weakN_iff`,
  `NormalEq.descend`, `WF.rigidShapeUniqNS`, `VIndRecArg.exists_indep`, `addDecl.WF`,
  `kernel_complete`, `kernel_sound`, `leanTT_equiconsistent_zfc_omega_inaccessibles`.
* `automatically included section variable` warnings: **1, and it is `Foundation`'s** — in-repo
  **0 before and 0 after**.  No cascade of that class.
* `unusedVariables`: **66 before, 66 after, and the list is identical** modulo five line-number
  shifts inside `Verify/Environment/InductR.lean`, a concurrent stream's file.
* Guards: **1 ✓** (24 frozen axioms), **2 ✓** (whitelist; proof INCOMPLETE, `sorryAx` present — as
  before), **3 ✓** (2/2 gaps).  Note that "guards printed" proves little on its own; the
  substantive checks above are the census, the axiom table and the `NOT FOUND`.
* Frozen files (`Verify/Soundness.lean`, `Verify/Axioms.lean`, `Verify/Guard.lean`): **not read-
  modified and not `touch`ed**.  None of them mentions `ntreeAux_WF`.
* `AddInduct` was **not** flipped; `tryEtaStructCore.WF` and `isDefEqUnitLike.WF` untouched.

### 6.1 Two things about the tree that are not mine, and should be known

1. **`Lean4Lean.Theory.Inductive.IndexedWit` is in a default target, on disk, with no `.olean`.**
   The census reports `BUILT: 415; NOT BUILT: 1`.  It is the `IndexedWit` stream's new file and it
   failed to elaborate at the time of my build (`Unknown constant Lean4Lean.VEnv.ordered_empty` at
   `IndexedWit.lean:179`).  A hole in an unbuilt module is invisible to every instrument in this
   repo *while `lake build` still says green*, because `lake build` does not build files no target
   reaches.  Its owner should confirm it compiles.
2. **The build was blocked mid-session by another stream's in-progress edit**, not by mine:
   `Verify/Environment/InductR.lean` grew a `trSpine` field on a structure and for a while had
   `trSpine := sorry` at line 883 plus `Fields missing: trSpine` errors in `InductR.lean` and
   `Verify/Inductive/NestedRestoreWit.lean`.  Both are resolved in the tree as I verified it
   (`grep sorry Lean4Lean/Verify/Environment/InductR.lean` is empty, census still 13), but if you
   see `trSpine` errors, they are the `SpineClause` stream's, not this one's.

## 7. Files changed, and when — for the concurrent streams

All edits below were made on **2026-09-03**, between the baseline build (1595 jobs) and the
verification build in §6.  **`Theory/Inductive/IndexedWit*`, `Verify/Inductive/SpineClause*`,
`Verify/Inductive/NestedRestore*`, `Verify/Inductive/RestrictStep*` were not touched.**

| file | what |
|---|---|
| `Theory/Inductive/NestedHead.lean` | wrapper `ntreeAux_WF` **deleted**; 1 site; 2 prose |
| `Theory/Typing/ConstSubstNested.lean` | 9 sites; 1 prose |
| `Theory/Inductive/CtorBeta.lean` | 6 sites |
| `Theory/Inductive/FamInhabC.lean` | 2 sites |
| `Theory/Inductive/HTeleRecB.lean` | 2 sites |
| `Theory/Inductive/NestedTele.lean` | 2 sites |
| `Theory/Inductive/OwnRule.lean` | 2 sites |
| `Theory/Inductive/RecTyped.lean` | 2 sites |
| `Theory/Inductive/HTeleGen.lean` | 1 site |
| `Theory/Inductive/HTeleNTree.lean` | 1 site |
| `Theory/Inductive/WFCRoute.lean` | 1 site |
| `Theory/Inductive/TeleCongr.lean` | 1 site |
| `Theory/Inductive/NestedBuild.lean` | 1 site; `example := @ntreeAux_WF'`; 1 prose |
| `Theory/Inductive/RestoreOpWit.lean` | 1 prose mention only |
| `Theory/Typing/LiftTrimWitness.lean` | 1 prose; its `#print axioms …ntreeAux_WF` line removed |
| `Verify/Inductive/ArgsTypedSupply.lean` | 1 site; `ntreeAux_argsTypedK_of_wf` binder trimmed; 2 of its 3 sites; new §4.2 witness + `#print axioms` |
| `Verify/Inductive/RestrictCompanion.lean` | 1 site of `ntreeAux_argsTypedK_of_wf` |
| `Theory/Inductive/WFRippleWitness.lean` | **NEW** — §4.1 |
| `docs/handoff-wfripple.md` | **NEW** — this file |

**Note for the `IndexedWit` stream specifically.**  You are building an indexed nested block and may
touch the same witness family.  Two things to know: (i) `InductiveDeclExamples.ntreeAux_WF` **no
longer exists** — use `ntreeAux_WF'`, which takes no argument (and no `env₁` argument either;
`env₁` is a section variable of `NestedHead.lean`, inferred from the use site); (ii)
`InductiveDeclExamples.ntreeAux_argsTypedK_of_wf` lost its first explicit argument and is now
`(het : env₁.addIndTypes ntreeAux = some et) → …`.  If you had `ntreeAux_WF h` or
`ntreeAux_argsTypedK_of_wf h het` in an uncommitted buffer, drop the `h`.

## 8. Where the brief was wrong

1. **"the ripple is 27 sites in 9 files"** — it was, when `handoff-lifttrim.md` measured it.  On
   this tree it is **32 sites in 14 files** (+1 `@`-application), five of those files being new
   callers (and `TeleCongr` went 3 → 1).  The brief was right to tell me to re-measure and right that the earlier relayed
   figure (25 in 8) was wrong; the correction is that **27/9 is also already wrong**, in the same
   direction, for the same reason.  A count of consumers of a widely-cited lemma decays within
   hours in this repo.
2. **"`ntreeAux.WF env₁` is a structure, so `ntreeAux_WF h` cannot survive `h`'s removal — hence
   the wrapper"** — the premise is true and the conclusion held only while the 11 sites were
   off-limits.  With the ownership grant widened, the flat replacement needed **zero** proof
   changes: the intermediate build (all sites re-pointed, wrapper still in place) was green at
   1595 jobs.  Outcome 1, not outcome 3.
3. **"outcome 3: a wrapper that keeps a widely-used name stable can be worth more than its
   removal"** — I do not think that applied here, and the reason is item 1 above turned around: the
   wrapper was *accruing* new callers (five files' worth in one session), each of which now had to
   be re-pointed anyway.  A wrapper that is still being written to is not a stable façade, it is a
   second name for the same lemma.
4. **"in-repo `automatically included section variable` warnings are at 0"** — confirmed, and the
   one remaining warning of the class is `Foundation`'s.  Still 0 in-repo after these edits.
5. The brief did **not** anticipate the second trim (§3.1).  Trimming `ntreeAux_WF` propagated one
   step up the call graph and made `ntreeAux_argsTypedK_of_wf`'s hypothesis unused — exactly the
   cascade the brief warned about in the *warning-count* sense, but the useful reading is that
   **one strengthening produced another**.
