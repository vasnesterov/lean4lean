# handoff — `SEReduce`: weakening the 14→13 collapse side condition, and reducing `ConstAppInvSISE` to an `↔`

Stream owns exactly `Lean4Lean/Theory/Typing/SEReduce.lean` (new) and this file.
Everything else read-only. Four concurrent streams own `Theory/SetModel/InterpMkPi.lean`,
`Verify/Inductive/AddInductMapScope.lean`, `CtorsLenGeneral.lean`, `FragmentWiden.lean`;
a red build in any of those is their work in flight, not mine.

Process rule for this stream (from seventeen crashes): **priors first, then one appended line per
instrument call, appended as the call is made.** No batching. My predecessor on this exact task
crashed at "let me record measurements and write the file", with the work done and unrecorded.

## §0 PRIORS (written before the first measurement of this round)

Falsifiable guesses, so the measurements can contradict them and be seen to.

- **Q0 — predecessor's cone/arity figures reproduce.** Its M1 gives
  `Lean4Lean.VEnv.ConstAppInvSISE` arity 2 / cone 634, `Lean4Lean.ConstAppInvSISEFromWF` arity 0 /
  cone 638, `VEnv.StructInhabSE` arity 4 / cone 83, `structEta_lhs_structInhabSE` arity 15 / cone 87,
  `NotStructInhabSEOfIsTypeStmt` arity 0 / cone 97, `guard_rejects_an_axiom` arity 7 / cone 382,
  `VEnv.structInhabOnlyNoConf_false` arity 0 / cone 3815. The brief adds
  `VEnv.IsDefEqSE.toIsDefEq_of_no_defeqs` arity 8 / cone 1308 and
  `VEnv.WF.isStructureG_ruleFreeHead` arity 8 / cone 4094. Prior: **all reproduce exactly** —
  cones have been exact all session. Confidence 0.9.

- **Q1 — shape of the weakened side condition (a).** The existing condition is "no defeqs" in the
  environment, i.e. a global statement that no `.defeq` constant exists. Prior: the right weakening
  is **not** about defeqs at all but about the *firing premise of `structEta`*: the collapse needs
  only that no term in play can be the `structEta` head, i.e. that there is no `S`/`us`/`ps` with
  `VEnv.IsStructureG` at which `StructInhabSE` holds. So my condition should be a **`Prop` over the
  environment quantifying over structure heads**, of the form "for every `S us ps`, ¬(eta-eligible
  at `S us ps`)", and "no defeqs" should imply it. Prior: the implication `no defeqs → my condition`
  is provable, so `toIsDefEq_of_no_defeqs` becomes a **corollary** of my generalisation, which is the
  test that the weakening is real. Confidence 0.6. Falsifier: `structEta`'s premises mention the
  ambient environment only through `IsDefEqSE` recursively, in which case the condition cannot be
  stated environment-locally and must be carried as a hypothesis on the derivation instead.

- **Q2 — is the weakened collapse provable this round?** The collapse is an induction over the 14
  constructors where 13 map across by IH and `structEta` is excluded by the side condition. Prior:
  **yes, provable, and hole-free relative to the imports**, because `toIsDefEq_of_no_defeqs` already
  does exactly this induction and I am only replacing the discharge of the `structEta` case. The
  risk is not the eta case but the `trans`/`proofIrrel` cases if the existing proof used
  "no defeqs" a *second* time, for something other than eta. Confidence 0.65 hole-free; 0.85 that
  it compiles with at most one carried hypothesis.

- **Q3 — the `↔` premise (b), and its classification.** Prior: the smallest sufficient premise for
  `ConstAppInvSISE` is **SE-Church–Rosser**, i.e. the existence of `church_rosserSE` (predecessor
  verified its absence, and `descendSE_uniq_sortUniq_not_all` /
  `not_parRedStatementSE_of_propMajor` refute the two standard routes to it). Prior: this is
  **ordinary open work, not one of the 13 census holes** — the census holes are `sorry`-carrying
  declarations, and `church_rosserSE` does not exist at all, so it cannot be a census entry.
  Confidence 0.7. Falsifier: one of the 13 holes *is* an SE-confluence statement under another name,
  in which case (b)'s premise is a hole and I must say which.

- **Q4 — the `↔` is achievable even though the forward direction is not.** Prior: an `↔` against a
  premise `P` is cheap exactly when `P` is chosen as "the hypothesis the induction needs", so the
  reverse direction is a projection. Prior: I can state `ConstAppInvSISE ↔ P` with `P` the SE-collapse
  side condition *plus* the 13-ctor `constApp_inv`, and both directions are short. Confidence 0.55
  that a genuine `↔` (not a restatement) lands; 0.8 that at minimum the `→` reduction lands.

- **Q5 — vacuity at both shapes (c).** Prior: my side condition is **satisfied at
  `Lean4Lean.MutField.unitEnv`** (zero-field structure — but note the brief says the failure was
  shown *not* to be zero-field-only, so unitEnv satisfying it is not enough) and **also satisfied at
  `Lean4Lean.MutField.bigEnv`** (positive-field plus axiom inhabitants), because `bigEnv`'s axiom
  inhabitants are not structure applications. Prior: satisfiable at both, and *restrictive* in that
  it fails at whatever environment `structEta` actually fires in. Confidence 0.55 at `bigEnv`;
  0.75 at `unitEnv`. Falsifier for restrictiveness: the condition holds vacuously everywhere,
  which would mean I stated it about the wrong quantifier and the collapse is unconditionally true —
  which would contradict `structInhabOnlyNoConf_false`, so that is a real check.

- **Q6 — the two hard constraints (d).** Prior: I will reproduce `guard_rejects_an_axiom` (cone 382)
  and `VEnv.structInhabOnlyNoConf_false` (cone 3815) and **not** weaken either; my condition
  quantifies over `IsStructureG` witnesses and `¬ IsProof`, never over head *names*, so
  `guard_rejects_an_axiom` does not bite. Confidence 0.9.

- **Q7 — taint.** Prior: my collapse is **hole-free** (it only inducts over `IsDefEqSE`), but
  anything I state as the `↔`'s premise that mentions the 13-ctor `constApp_inv` inherits that
  side's four holes plus the two watched `VEnv.IsDefEq.uniq` / `uniqU`. So I expect **two cleanliness
  classes in my own file**, and I will label each name rather than the file. Confidence 0.85.

- **Q8 — duplicate `IsDefEqUSE` / `IsDefEqSEU` (e).** Prior: still both present, both arity 5 /
  cone 7; I use whichever my target is stated with (`IsDefEqUSE`, per predecessor M9) and flag the
  other without touching either file. Confidence 0.95.

- **Q9 — layer and round-close (f).** Prior: my file is `Theory/`-only, no `Verify/` import needed,
  so `layer-check.py` exits 0 and no section-variable warnings arise. Census stays **13 / NOT BUILT 0**
  since I add no `sorry`. Confidence 0.8 on census unchanged; 0.85 on layer-check.

## §1 MEASUREMENTS (append-only, one line per instrument call, appended as the call is made)

- M1 `exists.lean` × 11 names, population **453 built modules** (predecessor saw 450; three modules
  added by concurrent streams since), watching 6 declarations. **Q0 CONFIRMED exactly, all nine
  figures, no exceptions** — every arity and every cone matches the brief and the predecessor's M1:
  - `Lean4Lean.VEnv.ConstAppInvSISE` — `Lean4Lean.Theory.Typing.ConstAppInvSIProof`, arity **2**,
    cone **634**, own value a hole: false, cone reaches sorryAx: **false**, **watched in cone: none of 6**.
  - `Lean4Lean.ConstAppInvSISEFromWF` — same module, arity **0**, cone **638**, hole false,
    sorryAx **false**, watched **none of 6**.
  - `Lean4Lean.VEnv.StructInhabSE` — same module, arity **4**, cone **83**, sorryAx false, watched none of 6.
  - `Lean4Lean.VEnv.structEta_lhs_structInhabSE` — same module, arity **15**, cone **87**, sorryAx false,
    watched none of 6.
  - `Lean4Lean.NotStructInhabSEOfIsTypeStmt` — same module, arity **0**, cone **97**, sorryAx false,
    watched none of 6.
  - `Lean4Lean.guard_rejects_an_axiom` — `Lean4Lean.Theory.Typing.NoConfRepair`, arity **7**,
    cone **382**, sorryAx false, watched none of 6. (constraint (d) first half reproduced)
  - `Lean4Lean.VEnv.structInhabOnlyNoConf_false` — `Lean4Lean.Theory.Typing.EtaGuardLand`, arity **0**,
    cone **3815**, sorryAx false, watched none of 6. (constraint (d) second half reproduced)
  - `Lean4Lean.VEnv.IsDefEqSE.toIsDefEq_of_no_defeqs` — `Lean4Lean.Theory.Typing.ConfluenceRebuildPrice`,
    arity **8**, cone **1308**, sorryAx false, watched none of 6. (brief's figure exact)
  - `Lean4Lean.VEnv.WF.isStructureG_ruleFreeHead` — `Lean4Lean.Theory.Typing.EtaGuardLand`, arity **8**,
    cone **4094**, sorryAx false, watched none of 6. (brief's figure exact)
  - **Q8 CONFIRMED**: `Lean4Lean.VEnv.IsDefEqUSE` (`ConstAppInvSIProof`) and
    `Lean4Lean.VEnv.IsDefEqSEU` (`ConfluenceRebuildPrice`) both arity **5**, cone **7** — same
    definition, two names, two files. I use `IsDefEqUSE`; flagging the other, touching neither.
  Note: all nine are `sorryAx`-clean **as statements**, which for the SE-side ones is because nothing
  proves them yet, not because they are established.

- M2 read `Theory/Typing/ConfluenceRebuildPrice.lean:294-346` (existing collapse) and
  `Theory/Typing/StructEtaPrice.lean:160-225` (the 14 constructors). **Q2's stated risk is REAL and
  is the whole weakening**: `toIsDefEq_of_no_defeqs` consumes `hd` in **two** places, not one —
  `| .extra h1 _ _ => absurd h1 (hd _)` and `| .structEta hS .. => absurd hS (…not_of_no_defeqs hd)`.
  Only the second is necessary: `IsDefEqSE`'s constructor list is `IsDefEq`'s thirteen *including*
  `extra`, so the `extra` case should map across as `.extra h1 h2 h3` and needs no side condition at
  all. The existing lemma kills `extra` gratuitously. **So "no defeqs" is doing two jobs and only one
  of them — excluding `structEta` — is load-bearing.** That is exactly the weakening (a) asks for.
- M3 note: `StructEtaSite.not_of_no_defeqs` (ConfluenceRebuildPrice:287) routes
  no-defeqs → `¬ IsStructureG` via `IsStructureG.not_of_no_defeqs`, so a condition phrased as
  `∀ S D j T C, ¬ env.IsStructureG S D j T C` is **implied by** no-defeqs — the corollary test in Q1.
- M4 read `Theory/Typing/Basic.lean:53-56`. `IsDefEq.extra`'s signature is **character-identical** to
  `IsDefEqSE.extra` (`env.defeqs df → (∀ l ∈ ls, l.WF uvars) → ls.length = df.uvars → …`).
  **M2's finding confirmed at the source**: the `extra` case of the collapse can be `.extra h1 h2 h3`
  and the `hd` there is pure waste. Sole *necessary* use of `hd` is the `structEta` case.
- M5 read `Theory/Inductive/Structure.lean:578` — `VEnv.IsStructureG` is a `structure` (env S D j T C).
  Q1 note: `structEta`'s premises split into **environment-local** (`IsStructureG`, `T.indices = []`,
  `C.recFields = []`, `us.length`/`levelWF`, the `small` level clause) and **derivation-local**
  (`ps`/`Γ`/`e`: `np`, `HasArgsSE`, `typed`). The weakest *env-local* condition that still kills the
  rule is the negation of the local block — that is what I will define, since a condition mentioning
  `Γ`/`e` would not be a statement about the environment at all. **Q1 refined, not falsified**: the
  condition IS statable environment-locally, but only if the `us`-dependent `small` clause is
  universally quantified over `us`.
- M6 read `Theory/Typing/ConstAppInvSIProof.lean:158-215`. `VEnv.ConstAppInvSISE` premise list is
  `OnCtx`, `RuleFreeHead c`, `RuleFreeHead c'`, `¬ IsProof`, `¬ StructInhabSE`, `IsDefEqUSE`.
  Also present and directly relevant to (b): `VEnv.ConstAppInvNoSISE` (guard deleted) and the file's
  own §3.3 note that **`ConstAppInvNoSISE` is REFUTED** while its 13-ctor twin
  `ConstAppInvNoSIFromWF` is a theorem — that is constraint (d)'s "¬ IsProof cannot be dropped"
  neighbour, and it means the `↔` in (b) must keep the `¬ StructInhabSE` guard.
  Template for (b) is in the same file: `constAppInvSIFromWF_iff_unguarded` (line ~151) is an `↔`
  whose docstring explicitly disclaims information content — I must not produce that shape again.
- M7 grep for the vacuity witnesses. **`MutField.bigEnv` is `Theory/Typing/NoConfRepair.lean:384`
  (Theory-level, importable by me) but `MutField.unitEnv` is
  `Verify/TypeChecker/EtaUnitRefute.lean:25` — a `Verify/` module.** Q9 AT RISK: importing it into a
  `Theory/` file is a layer inversion. Checking `layer-check.py` next; if it forbids the import I do
  the zero-field shape from a Theory-level zero-field structure instead and say so.
- M8 read `scripts/layer-check.py`. HARD rule (exit 1) is only `Theory/SetModel/ ↛ Verify/*`; a
  `Theory/` file importing `Verify/` is a **SOFT report, exit 0**, and the docstring says a *small*
  constant count is the suspicious signature. So a `Verify/` import from my file would not fail the
  gate but would earn me a soft row with a tiny count — exactly the "parked declaration" smell.
  **Decision: no `Verify/` import.** Q9 preserved by avoiding the import, not by luck.
- M9 read `Theory/Typing/NoConfRepair.lean:370-440` and `EtaGuardLand.lean:350-400`. **This is the
  vacuity material, already at Theory level, and it is better than Q5 hoped:**
  - `Lean4Lean.MutField.bigEnv_IsStructureG_A` — `IsStructureG` at the **zero-field** member (block 0).
  - `Lean4Lean.MutField.bigEnv_IsStructureG_B` — `IsStructureG` at the **one-field** member (block 1),
    with `MutField.bCtor_has_a_field` as the field count, so "positive field" is not a paraphrase.
  - `Lean4Lean.MutField.bigEnv_wf` — `bigEnv` is well formed (4 decl steps, 1 `.induct` + 3 `.axiom`).
  - `Lean4Lean.MutField.bigEnv_structEtaSE_bar` — the **fourteenth constructor actually firing** at the
    one-field member. So restrictiveness at positive-field shape is witnessable *positively*.
  - `VEnv.ncPropEnv` with `IsStructureG.not_of_no_defeqs (fun _ h => h)` (NoConfRepair §5.1 `example`)
    is a Theory-level no-defeqs environment — a satisfiability witness for my condition.
  **So both shapes are reachable without touching `Verify/`, and `MutField.unitEnv` is available at
  Theory level too** (NoConfRepair uses `unitEnv_addConst_foo2`, `unitEnv_A_isType`, …), which
  amends M7: the `Verify/` `def unitEnv` is a *second* copy, not the only one. Verifying next.
- M10 `head -20 | grep import` on NoConfRepair: it imports `Lean4Lean.Verify.Typing.ProjSpineInv`
  **directly**, so NoConfRepair is *already* one of the soft-reported Theory files, and
  `MutField.unitEnv`/`unitEnv_eq` really do live in `Verify/TypeChecker/EtaUnitRefute.lean:21,25`
  and reach Theory only through that edge. **M9's amendment retracted: there is exactly one
  `MutField.unitEnv` and it is `Verify/`-side.** But `layer-check.py` reports only *direct* Verify
  imports, so importing `NoConfRepair` (Theory) gives me `MutField.unitEnv`, `MutField.bigEnv` and
  the `IsStructureG` witnesses **without putting my own file on the soft report**. Q9 holds by this
  route. Both structure shapes therefore remain reachable.
- M11 import graph read: `ConstAppInvSIProof → EtaGuardLand → NoConfRepair → StructEtaPrice`, and
  `ConfluenceRebuildPrice → {StructEtaPrice, ParRedPropRefute, EtaGuardLand}`. So importing exactly
  `Lean4Lean.Theory.Typing.ConstAppInvSIProof` + `Lean4Lean.Theory.Typing.ConfluenceRebuildPrice`
  (both `Theory/`) gives me `IsDefEqSE`, `StructEtaSite`, `StructInhabSE`, `ConstAppInvSISE`,
  `toIsDefEq_of_no_defeqs`, `IsStructureG.not_of_no_defeqs`, `MutField.unitEnv`, `MutField.bigEnv`
  and the `bigEnv_IsStructureG_A/B` witnesses. **Two direct imports, both Theory/: no soft row.**
- M12 read `NoConfRepair.lean:95-103` and `:292-300`. **The two statements differ in exactly two
  places.** `StructInhabAt env Ty e := ∃ S D j T C us ps, IsStructureG S D j T C ∧ T.indices = [] ∧
  C.recFields = [] ∧ Ty e ((const S us).mkApp ps)` — `Ty` occurs **positively and only once**, so
  `StructInhabAt` is monotone in `Ty` for free. And `ConstAppInvSI` vs `ConstAppInvSISE` differ only
  by `StructInhab`↦`StructInhabSE` and `IsDefEqU`↦`IsDefEqUSE`. **So under my side condition the two
  statements are literally inter-derivable, which is the `↔` of (b)** — with the eta-eligible case as
  the entire residue. This is the plan: no new confluence, no new uniqueness.
- M13 `lake build Lean4Lean.Theory.Typing.SEReduce` — **GREEN on the first attempt**, 1321/1321 jobs,
  2.0s for my module. §1–§6 all compiled as written; no tactic search was needed anywhere and the
  `structEta` case is `(hne hS hidx hrec hlen hwf hsmall).elim`, i.e. it consumes exactly the five
  environment-local premises and discards the four derivation-local ones, as M5 predicted.
  **Q2 CONFIRMED and its stated risk realised and repaired**: `.extra h1 h2 h3` maps across with no
  side condition, so the new collapse's *only* use of the hypothesis is the eta case. Declarations
  landed: `VEnv.NoEtaEligible`, `VEnv.IsDefEqSE.toIsDefEq_of_noEta`,
  `VEnv.HasArgsSE.toHasArgs_of_noEta`, `VEnv.noEtaEligible_of_no_defeqs`,
  `VEnv.IsDefEqSE.toIsDefEq_of_no_defeqs'`, `VEnv.isDefEqSE_iff_of_noEta`,
  `VEnv.isDefEqUSE_iff_of_noEta`, `VEnv.StructInhabAt.mono'`, `VEnv.StructInhab.toSE`,
  `VEnv.not_structInhab_of_not_structInhabSE`, `VEnv.structInhabSE_iff_of_noEta`,
  `VEnv.constAppInvSISE_iff_of_noEta`, `VEnv.constAppInvSISE_of_noEta`,
  `ConstAppInvSISEFromWFEtaOnly`, `constAppInvSISEFromWF_iff_etaOnly`.
- M14 build log incidentally reveals **two satisfiability witnesses already in the tree** that Q5 did
  not anticipate: `Lean4Lean.refEnv_no_structEtaSite` and `Lean4Lean.ncPropEnv_no_structEtaSite`
  (`ConfluenceRebuildPrice.lean:760,761`), plus `Lean4Lean.VEnv.exists_defeq_of_structEtaSite` (759).
  The last is the strictness lever I was missing: it says a `StructEtaSite` *forces* a defeq, i.e.
  the implication in §3 is the only direction that holds. Using these for §7 rather than rebuilding.
- M15 grep for the vacuity witnesses gives me the **exact premise tuples**, so §7 is assembly, not
  search. `NoConfRepair.lean:468-492` fires `structEta` three times at `bigEnv`:
  `bigEnv_structEtaSE_foo` and `_foo2` use `bigEnv_IsStructureG_A rfl rfl rfl nofun rfl .nil
  bigEnv_foo_hasType (.inr (by simp [aCtor]))` (**zero-field**, block 0), and
  `bigEnv_structEtaSE_bar` uses `bigEnv_IsStructureG_B rfl rfl rfl nofun rfl .nil bigEnv_bar_hasType
  (.inr bCtor_field_prop)` (**one-field**, block 1). The first five arguments of each are precisely
  `NoEtaEligible`'s five, so `¬ bigEnv.NoEtaEligible 0` is one application at each shape.
  Satisfiability side: `refEnv_no_defeqs` and `VEnv.ncPropEnv`'s `fun _ h => h` are the two
  no-defeqs environments already used at `ConfluenceRebuildPrice.lean:675-681`.
- M16 read `StructEtaPrice.lean:300-330`. The `unitEnv`/`declEnv` tuples too:
  `structEtaSE_foo` = `unitEnv_IsStructureG_0 rfl rfl rfl nofun rfl .nil unitEnv_foo_hasType
  (.inr (by simp [aCtor]))` (**unitEnv, zero-field**) and `structEtaSE_B` =
  `declEnv_IsStructureG rfl rfl rfl nofun rfl .nil (.bvar (.zero ..)) (.inr bCtor_field_prop)`
  (**declEnv, positive-field**, and `declEnv_le_unitEnv` lifts it to `unitEnv` by `IsStructureG.mono`).
  So I can refute `NoEtaEligible` at **both environments at both shapes** — four refutations, not two.
  Satisfiability: `refEnv_no_defeqs` and `VEnv.ncPropEnv` (`wf_ncPropEnv` makes the latter a
  *well-formed* environment, which is what "real environment" has to mean here).
- M17 `lake build` after appending §7 — **4 errors**, all in §7.2, all the same cause: `nofun` for
  `∀ l ∈ us, l.WF U` cannot elaborate while `us` is still a metavariable, because `rfl :
  us.length = D.uvars` does not determine `us = []`. ("Missing cases" ×4 plus two application type
  mismatches.) Not a mathematical problem — the existing firings pass `(us := [])` explicitly and I
  had dropped it when reusing their premise tuples.
- M18 fixed by adding `(us := [])` to all four applications. `lake build
  Lean4Lean.Theory.Typing.SEReduce` — **GREEN**, 1321/1321, 2.1s. **Q5 CONFIRMED and beaten**:
  vacuity is established at **four corners**, not the two the brief asked for —
  `MutField.unitEnv_not_noEtaEligible_zeroField`, `MutField.unitEnv_not_noEtaEligible_posField`,
  `MutField.bigEnv_not_noEtaEligible_zeroField`, `MutField.bigEnv_not_noEtaEligible_posField` —
  and satisfiability at two: `VEnv.ncPropEnv_noEtaEligible` (at a **`VEnv.WF`** environment, by
  `wf_ncPropEnv`) and `refEnv_noEtaEligible`.
- M19 `lake env lean` on my file after §7 — **exit 0, zero output**: no errors, and in particular
  **zero section-variable warnings** (round-close item (f)).
- M20 grep chain found the strictness lever I judged missing at M14: `VEnv.addInduct'_types`
  (`Theory/Inductive/Lemmas.lean:548`, Theory-level) plus `IsStructureG.decl` forces
  `env.constants T.name = some ⟨D.uvars, T.type⟩`. Template is `Lean4Lean.VEnv.empty_structEtaG`
  (`Verify/TypeChecker/EtaStructG.lean:339`). So **an environment with no constants satisfies
  `NoEtaEligible` however many defeqs it carries** — a second sufficient condition, independent of §3.
- M21 wrote §8 and built — 4 errors: `Option.noConfusion` universe-mismatched on `h : none = some …`
  (fixed with `simp at h`), and `Inhabited VDefEq` does not exist ×3, so the separation theorem takes
  `df` as a parameter rather than using `default`. **`lake env lean` after the fix: exit 0, silent.**
  **Q1's confidence-0.6 corollary test PASSED and the strictness is now machine-checked, not asserted:**
  `Lean4Lean.noEtaEligible_strictly_weaker_than_no_defeqs` — §3's implication holds *and* its converse
  fails at `VEnv.empty.addDefEq df`, via `VEnv.noEtaEligible_of_no_constants`,
  `addDefEq_empty_noEtaEligible`, `addDefEq_empty_has_defeq`.
- M22 whole-tree `lake build` — **GREEN, 1640 jobs, zero errors.** No concurrent stream's file was
  red at this poll, so nothing to attribute to work in flight.
- M23 `lake env lean --run scripts/sorry-census-all.lean` (**with `--run`**, per the process rule):
  **BUILT: 457; in population but NOT BUILT: 0; HOLES unioned over the whole built population: 13.**
  Census target hit exactly — **13 and NOT BUILT 0**. My module appears in the population list and
  contributes no hole. (Population 457 vs M1's 453: my module plus three from concurrent streams.)
- M24 `python3 scripts/layer-check.py` — **exit 0**. HARD rule ok (65 SetModel modules, none reaches
  `Verify/`). SOFT report lists four Theory files (`CommutationLemmas` 4, `EtaGuardLand` 1,
  `NoConfRepair` 1, `StructEtaPrice` 1) — **`Lean4Lean.Theory.Typing.SEReduce` is NOT among them.**
  **Q9 CONFIRMED**: two Theory-only direct imports, no new soft row, no new drift.
- M25 `lake build Lean4Lean.Verify.Guard` — **all three guards ✓**:
  guard 1 "Axioms.lean declares exactly the 24 frozen axioms ✓";
  guard 2 "kernel_sound axioms within whitelist ✓ (proof INCOMPLETE: sorryAx present)" — the guard
  passes; the INCOMPLETE is the project's standing stop-condition state, unchanged by me;
  guard 3 "checker cone implementation gaps within frozen list (2/2 remaining) ✓".
  The only section-variable warning in the log is `Foundation/FirstOrder/SetTheory/Z.lean:35` —
  **Foundation, not in-repo**. Confirming zero in-repo ones next.
- M26 `lake build 2>&1 | grep -cE 'Lean4Lean/.*automatically included section variable'` = **0**.
  **Zero in-repo section-variable warnings**; the only one in the log is Foundation's `Z.lean:35`.
- M27 `exists.lean` × 17 names, population **454 built modules** (census at M23 said BUILT 457;
  the two walks were minutes apart with four streams committing, so I record both figures and
  attribute the gap to nothing). **Every new declaration is hole-free, `sorryAx`-free, and reaches
  none of the 6 watched declarations** — `WATCHED IN CONE: none of 6` on all sixteen:
  - `Lean4Lean.VEnv.NoEtaEligible` — `Lean4Lean.Theory.Typing.SEReduce`, arity **2**, cone **618**.
  - `Lean4Lean.VEnv.IsDefEqSE.toIsDefEq_of_noEta` — arity **8**, cone **791**.
  - `Lean4Lean.VEnv.noEtaEligible_of_no_defeqs` — arity **3**, cone **1216**.
  - `Lean4Lean.VEnv.noEtaEligible_of_no_constants` — arity **3**, cone **1151**.
  - `Lean4Lean.VEnv.structInhabSE_iff_of_noEta` — arity **5**, cone **801**.
  - `Lean4Lean.VEnv.constAppInvSISE_iff_of_noEta` — arity **3**, cone **831**.
  - `Lean4Lean.VEnv.constAppInvSISE_of_noEta` — arity **4**, cone **832**.
  - `Lean4Lean.ConstAppInvSISEFromWFEtaOnly` — arity **0**, cone **657**.
  - `Lean4Lean.constAppInvSISEFromWF_iff_etaOnly` — arity **1**, cone **882**.
  - `Lean4Lean.noEtaEligible_strictly_weaker_than_no_defeqs` — arity **1**, cone **1241**.
  - `Lean4Lean.VEnv.ncPropEnv_noEtaEligible` — arity **1**, cone **1222**.
  - `Lean4Lean.MutField.unitEnv_not_noEtaEligible_zeroField` — arity **0**, cone **4147**.
  - `Lean4Lean.MutField.unitEnv_not_noEtaEligible_posField` — arity **0**, cone **3863**.
  - `Lean4Lean.MutField.bigEnv_not_noEtaEligible_zeroField` — arity **0**, cone **4165**.
  - `Lean4Lean.MutField.bigEnv_not_noEtaEligible_posField` — arity **0**, cone **3876**.
  Baseline reproduced unchanged: `Lean4Lean.VEnv.IsDefEqSE.toIsDefEq_of_no_defeqs` arity 8 cone 1308.
  **`Lean4Lean.church_rosserSE` — NOT FOUND**, so Q3's classification stands: the residue cannot be
  a census hole, because the census counts `sorry`-carrying declarations and this has no declaration.
  **Q7 PARTLY FALSIFIED, in my favour**: I predicted two cleanliness classes in my own file, but
  `constAppInvSISE_of_noEta` and `constAppInvSISEFromWF_iff_etaOnly` come out `sorryAx`-**false**,
  because both carry the thirteen-constructor statement as a *hypothesis* rather than discharging it.
  So the whole file is currently one class: clean. Adding the discharged form next, so the taint is
  measured rather than predicted.
- M28 added §9, the **discharged** `↔`, and measured it. `lake env lean` exit 0;
  `lake build Lean4Lean.Theory.Typing.SEReduce` green, 1321/1321.
  - `Lean4Lean.constAppInvSISEFromWF_iff_etaOnly'` — `Lean4Lean.Theory.Typing.SEReduce`, arity **0**,
    cone **7580**, own value a hole: false, **cone reaches sorryAx: true**,
    holes in cone: `[Lean4Lean.VEnv.IsDefEqU.weakN_iff,
    Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified, Lean4Lean.VEnv.WF.rigidShapeUniqNS,
    Lean4Lean.VEnv.NormalEq.descend]`,
    **WATCHED IN CONE: [Lean4Lean.VEnv.IsDefEq.uniq, Lean4Lean.VEnv.IsDefEq.uniqU]**.
  - `Lean4Lean.constAppInvSIFromWF` — arity **0**, cone **7494**, sorryAx **true**, the **same four
    holes** and the **same two watched**.
  **Q7 now settled exactly, and the file really does have two cleanliness classes**: the discharged
  form inherits `constAppInvSIFromWF`'s taint *and nothing more* — identical hole list, identical
  watched list, cone 7580 vs 7494 (+86, my own material). Everything else in the file is clean.
  This is why §6 and §9 are separate declarations: one declaration would have hidden the boundary.
- M29 round-close re-run after §9. **Whole-tree `lake build` RED — but not in a file I own.**
  8 errors, all in `Lean4Lean/Theory/SetModel/OracleObligations.lean` (255,256,261,264,265,266,
  274,275): `Unknown identifier 'L'` ×6, one `invalid '▸' notation`, one `unsolved goals`. That is a
  `Theory/SetModel/` file; my stream owns only `Theory/Typing/SEReduce.lean` and this handoff.
  Census consequently reports **BUILT: 457; NOT BUILT: 1** (that one module) with **HOLES: 13**;
  `layer-check.py` exit **0**; in-repo section-variable warnings **0**.
  Per the process rule this is a concurrent stream's work in flight. **Re-polling.**
- M30 `git status --short`: **`Lean4Lean/Theory/SetModel/OracleObligations.lean` is UNTRACKED (`??`)**,
  alongside a brand-new `docs/handoff-oracleobligations.md`. So it is a file another stream created
  during my round, not a regression I caused — attribution is certain here rather than inferred, which
  matters given the calibration note that attributions have been wrong eight times this session.
  Also visible: `docs/handoff-checkerroute.md` and `docs/handoff-surfacemap.md` are new too, so
  **more than the four streams the brief named are live**, and `git log` has advanced three commits
  (`c762312`, `bff3c7c`, `2118e0e`) since my round began. My own file and this handoff are the only
  untracked entries attributable to me. **Re-polling the build.**
- M31 **re-poll: whole-tree `lake build` GREEN, 1641 jobs, zero errors.** The other stream fixed
  `OracleObligations.lean` between my two polls, exactly as the process rule anticipated. M29's red
  is theirs and is now gone; nothing of mine changed between the two polls.
- M32 **ROUND-CLOSE, all six items, after the green re-poll:**
  - whole-tree `lake build`: **GREEN, 1641 jobs**;
  - `lake env lean --run scripts/sorry-census-all.lean`: **BUILT 458; NOT BUILT 0; HOLES 13** ✓;
  - three guards: **guard 1 ✓** (24 frozen axioms), **guard 2 ✓** (whitelist; "proof INCOMPLETE:
    sorryAx present" is the standing state, unchanged by me), **guard 3 ✓** (2/2 remaining);
  - in-repo section-variable warnings: **0**;
  - `python3 scripts/layer-check.py`: **exit 0**, 66 SetModel modules checked, and
    `Lean4Lean.Theory.Typing.SEReduce` absent from the soft report;
  - nothing outside `Lean4Lean/Theory/Typing/SEReduce.lean` and `docs/handoff-sereduce.md` touched.

## §2 PRIORS SCORED

### My own priors
- **Q0 cone/arity figures reproduce — CONFIRMED, all nine, exactly** (M1). Cones exact again;
  the calibration note holds for the tenth consecutive round.
- **Q1 shape of the condition — CONFIRMED, refined** (M5, M13, M21). Statable environment-locally,
  with the `us`-dependent `small` clause universally quantified, as the falsifier clause anticipated.
  The corollary test I gave 0.6 to **passed**, and better: strictness is machine-checked (M21).
- **Q2 provable this round — CONFIRMED, and its named risk was the whole deliverable** (M2, M4, M13).
  I guessed "the risk is the `trans`/`proofIrrel` cases if the old proof used no-defeqs twice"; it
  used it twice, but for **`extra`**, not for `trans`. Half-right: right that there was a second use,
  wrong about which constructor. Hole-free, no carried hypothesis. 0.65 → landed.
- **Q3 residue is open work, not a census hole — CONFIRMED** (M27). `church_rosserSE` NOT FOUND, so
  it has no declaration and cannot be one of the 13.
- **Q4 the `↔` is achievable — CONFIRMED and exceeded**. I gave 0.55 to a genuine `↔` and 0.8 to a
  `→` only. Got a genuine `↔` in two forms, one clean and one discharged (M27, M28).
- **Q5 vacuity at both shapes — CONFIRMED and exceeded** (M18). Predicted satisfiable at unitEnv/
  bigEnv; **wrong about what the question was** — the condition necessarily *fails* at both (they have
  eta-eligible structures), and that failure is the restrictiveness half. Satisfiability is at
  `ncPropEnv`/`refEnv`. Four refutation corners, not two.
- **Q6 hard constraints — CONFIRMED** (M1, §7.3). Both cones reproduced (382, 3815); neither weakened;
  no head name anywhere in `NoEtaEligible`.
- **Q7 two cleanliness classes — PARTLY FALSIFIED then vindicated** (M27, M28). The conditional forms
  are clean, so at M27 the file was one class; §9's discharged form restored the second class, with
  the taint measured as *identical* to `constAppInvSIFromWF`'s.
- **Q8 duplicate still present — CONFIRMED** (M1). Both arity 5, cone 7. Bridged in §7.4, neither deleted.
- **Q9 layer / census — CONFIRMED** (M24, M32). No `Verify/` import; exit 0; census 13 unchanged.

### My predecessor's priors (it left them unscored)
- **P0 both names exist, brief conflated a `def` with a closed `Prop`** — its own M1 confirmed this
  and I reconfirmed both figures (634 and 638) at M1. **Scored: CONFIRMED, 0.8 well calibrated.**
- **P1 `ConstAppInvSISE` true but not provable by transport; 0.3 to closing it hole-free** —
  **CONFIRMED on both halves.** Its M8 established outright proof is out of reach, and my round shows
  the transport works *exactly* where eta cannot fire and nowhere else. Its 0.3 was correctly low.
- **P2 the transport failure is a missing *development*, not a missing lemma (0.75)** —
  **CONFIRMED and sharpened.** Its M5 confirmed at the proof text; my §5 localises it further: the
  missing development is needed *only* at eta-eligible environments, which its prior did not predict.
- **P3 satisfaction of the SE guard at an environment that HAS a structure (0.6)** —
  **FALSIFIED as stated, and the correction matters.** At an environment with an eta-eligible
  structure the guard is *not* satisfiable in the sense it hoped: my four §7.2 refutations show the
  condition fails there by construction. What is satisfiable there is the *pointwise* guard
  `¬ StructInhabSE` at particular terms, which is a different statement from the environment-level one.
- **P4 both cones reproduce, no weakening attempted (0.95)** — **CONFIRMED** (M1).
- **P5 taint inherited via `constApp_inv` (0.9)** — **CONFIRMED exactly** (M28): same four holes,
  same two watched, and nothing added.
- **P6 no `Verify/` import needed (0.85)** — **CONFIRMED for my file too** (M24), though only because
  I routed the `MutField` witnesses through Theory-level `NoConfRepair` rather than through
  `Verify/TypeChecker/EtaUnitRefute.lean` where `unitEnv` actually lives (M7, M10).

## §3 WHAT IS LEFT, FOR A SUCCESSOR

`Lean4Lean.ConstAppInvSISEFromWFEtaOnly` (arity 0, cone 657) is the whole residue, and
`Lean4Lean.constAppInvSISEFromWF_iff_etaOnly'` (arity 0, cone 7580) says it is *equivalent* to the
full obligation. **Classification: ordinary open work, not a census hole** — `church_rosserSE` is
NOT FOUND, and the census counts `sorry`-carrying declarations.

Three things a successor must not do, each with the measurement that forbids it:
1. **Do not re-erect `ParRedStatement` over `IsDefEqSE`.** `Lean4Lean.descendSE_uniq_sortUniq_not_all`
   and `Lean4Lean.VEnv.not_parRedStatementSE_of_propMajor` refute both standard routes.
2. **Do not guard on head names.** `Lean4Lean.guard_rejects_an_axiom` (cone 382).
3. **Do not drop `¬ IsProof`.** `Lean4Lean.VEnv.structInhabOnlyNoConf_false` (cone 3815), and
   `VEnv.ConstAppInvNoSISE` is separately refuted in `ConstAppInvSIProof.lean` §3.3.

Two things that are now cheap and were not before:
- Any existing proof that needs `IsDefEqSE ⊆ IsDefEq` no longer needs a defeq-free environment, only
  `VEnv.NoEtaEligible` — or merely `VEnv.noEtaEligible_of_no_constants`, which is independent of it.
- `VEnv.structInhabSE_iff_of_noEta` and `VEnv.isDefEqUSE_iff_of_noEta` let any `ConstAppInvSI`-shaped
  statement be moved between the two relations in one rewrite wherever eta cannot fire.

One piece of housekeeping I could not do: `VEnv.IsDefEqUSE` and `VEnv.IsDefEqSEU` are the same
definition in two files (both arity 5, cone 7). `VEnv.isDefEqUSE_iff_isDefEqSEU` bridges them.
Deleting one needs an owner of `ConstAppInvSIProof.lean` or `ConfluenceRebuildPrice.lean`.
Likewise `VEnv.IsDefEqSE.toIsDefEq_of_no_defeqs` in `ConfluenceRebuildPrice.lean` is now strictly
subsumed by `VEnv.IsDefEqSE.toIsDefEq_of_noEta` (my §3 re-derives it as
`toIsDefEq_of_no_defeqs'`); its owner may want to replace the body with the corollary.
**No frozen file needs any edit for any of this.**
