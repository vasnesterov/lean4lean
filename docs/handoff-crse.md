# handoff-crse — scoping the eta front's last reduction target (Church-Rosser over the SE relation)

Round opened 2026-09-04T04:23:36Z. Owner files: `docs/handoff-crse.md` (this),
`Lean4Lean/Theory/Typing/CRSEScope.lean` (only if a claim needs Lean).

## PRIORS (written before the first measurement — do not edit, append corrections below)

Relayed to me by the orchestrator, to be verified not trusted:

- P1. `Lean4Lean.VEnv.constAppInvSISE_iff_of_noEta` exists, arity 3, cone 831, hole-free.
- P2. `Lean4Lean.VEnv.NoEtaEligible` exists, cone 618, side condition weaker than defeq-freeness.
- P3. `Lean4Lean.constAppInvSISEFromWF_iff_etaOnly'` exists, arity 0, cone 7580, tainted with
      exactly 4 holes + 2 watched statements.
- P4. `Lean4Lean.VEnv.IsDefEq.church_rosserSE` is NOT FOUND (no declaration at all).
- P5. `Lean4Lean.VEnv.NormalEqSE` and `Lean4Lean.VEnv.ParRedSE` are DEFINED in
      `Theory/Typing/ConfluenceRebuildPrice.lean`, over a 14-constructor relation,
      with 2 new structure-eta rules and 1 new parallel-reduction rule; both report
      `[NO PROOF TERM]` (definitions exist, theorems do not).
- P6. Two central statements stay REFUTED when transported:
      `Lean4Lean.descendSE_uniq_sortUniq_not_all` (arity 0, cone 6800) and
      `Lean4Lean.VEnv.not_parRedStatementSE_of_propMajor` (arity 22, cone 674).
- P7. The set model validates structure eta and validation is *forced*; confluence needs
      nothing from `Theory/SetModel/` (zero model modules in the relevant closure).

My own priors before measuring:

- Q1. I expect the 13-constructor Church-Rosser development (if it exists at all) to be the
      thing being "ported". If it too is only definitions and no theorems, then "port" is the
      wrong word for every step and the honest gap is *the whole confluence proof*, not a port.
      This is the single most likely way the orchestrator's framing is wrong.
- Q2. `[NO PROOF TERM]` on both SE relations plus `church_rosserSE` NOT FOUND means the
      measured gap is probably "everything", and the interesting content of this round is
      (b) — whether the refutations kill the formulation.
- Q3. A refutation of `not_parRedStatementSE_of_propMajor` with arity 22 smells like a
      refutation *under 22 hypotheses*, i.e. a conditional refutation whose hypotheses may
      themselves be unsatisfiable. `[NO PROOF TERM]` and cone-only measurement cannot tell
      satisfiable from vacuous. I must check the vacuity question explicitly and NOT report
      "refuted" without saying whether the refutation's hypotheses are inhabited.
- Q4. Prior from the round brief: cone figures are reliable, attributions/prose are not.
      So I will re-derive every name and every location, and quote `exists.lean` verbatim.

## MEASUREMENTS (appended as made)

### M1 (2026-09-04T04:24:11Z) — `exists.lean` on the eight prior names

`population: 455 built modules`, `watching 6 declarations for cone membership`.

| name | verdict |
|---|---|
| `Lean4Lean.VEnv.constAppInvSISE_iff_of_noEta` | FOUND, `Theory.Typing.SEReduce`, **arity 3, cone 831**, hole false, sorryAx false, watched none of 6 |
| `Lean4Lean.VEnv.NoEtaEligible` | FOUND, `Theory.Typing.SEReduce`, **arity 2** (brief gave no arity), cone 618, clean |
| `Lean4Lean.constAppInvSISEFromWF_iff_etaOnly` (unprimed) | FOUND, `Theory.Typing.SEReduce`, **arity 1, cone 882**, hole false, sorryAx false, **watched none of 6** |
| `Lean4Lean.VEnv.IsDefEq.church_rosserSE` | **NOT FOUND** |
| `Lean4Lean.VEnv.NormalEqSE` | FOUND, `ConfluenceRebuildPrice`, arity 4, **cone 4** `[NO PROOF TERM]` |
| `Lean4Lean.VEnv.ParRedSE` | FOUND, `ConfluenceRebuildPrice`, arity 4, **cone 4** `[NO PROOF TERM]` |
| `Lean4Lean.descendSE_uniq_sortUniq_not_all` | FOUND, `ConfluenceRebuildPrice`, arity 0, cone 6800, clean, watched none of 6 |
| `Lean4Lean.VEnv.not_parRedStatementSE_of_propMajor` | FOUND, `ConfluenceRebuildPrice`, arity 22, cone 674, clean, watched none of 6 |

**P4 confirmed** (church_rosserSE absent). **P5 confirmed** (defs only, `[NO PROOF TERM]`).
**P1 confirmed exactly.** **P6 both names confirmed present with the stated arities/cones.**
**P3 is WRONG as relayed**: the brief said arity 0, cone 7580, "tainted with exactly the four
holes and two watched statements". The unprimed name is arity 1, cone 882, `sorryAx false`,
`watched none of 6`. Either the primed name is a different declaration or the brief's numbers
are from another decl. Checking the primed name next — do not use the brief's 7580 figure.

### M2 (2026-09-04T04:24:35Z) — the primed name, and the 13-constructor counterparts

- `Lean4Lean.constAppInvSISEFromWF_iff_etaOnly'` FOUND, `Theory.Typing.SEReduce`, arity 0,
  **cone 7580**, hole false, **cone reaches sorryAx: true**,
  `holes in cone: [Lean4Lean.VEnv.IsDefEqU.weakN_iff, Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified, Lean4Lean.VEnv.WF.rigidShapeUniqNS, Lean4Lean.VEnv.NormalEq.descend]`
  `*** WATCHED IN CONE: [Lean4Lean.VEnv.IsDefEq.uniq, Lean4Lean.VEnv.IsDefEq.uniqU] ***`
  → **P3 is exactly right for the primed name**; the unprimed name is a different, cheaper decl.
- `Lean4Lean.VEnv.constAppInvSISEFromWF_iff_etaOnly` (namespaced) **NOT FOUND** — the primed one
  is top-level `Lean4Lean.`, not `Lean4Lean.VEnv.`. Name discipline matters here.

**THE FINDING THAT REFRAMES THE ROUND.** The 13-constructor target that everything is
supposedly "ported from" exists but is *itself not proved*:

- `Lean4Lean.VEnv.IsDefEq.church_rosser` FOUND, `Theory.Typing.ChurchRosser`, arity 7,
  cone 4383, **cone reaches sorryAx: true**, holes in cone **exactly the same four**
  `[IsDefEqU.weakN_iff, IsDefEqU.forallE_inv_stratified, WF.rigidShapeUniqNS, NormalEq.descend]`
  and **WATCHED IN CONE the same two** `[IsDefEq.uniq, IsDefEq.uniqU]`.
- `Lean4Lean.VEnv.NormalEq` and `Lean4Lean.VEnv.ParRed`: FOUND, `ChurchRosser`, arity 4,
  cone 4, `[NO PROOF TERM]` — i.e. the 13-constructor relations are *also* just definitions,
  exactly like their SE twins. So `[NO PROOF TERM]` on `NormalEqSE`/`ParRedSE` is **not**
  evidence of a gap: it is what an inductive predicate always prints. **Prior Q2 was
  half-wrong and the brief's use of that flag as a gap signal is a misreading.**

**`Lean4Lean.VEnv.NormalEq.descend` is a HOLE at 13 constructors.** And the refuted SE statement
`descendSE_uniq_sortUniq_not_all` is about *descend*. So the SE refutation is not a new
obstruction introduced by eta — it is the *same* unproved step, now with a proof that one
route to it is false. This is the crux of (b) and I must not report it as an eta-specific problem
until I have read both statements.

### M3 (2026-09-04T04:26Z) — `ConfluenceRebuildPrice.lean` read in full (769 lines, 8 sections)

The file is a *pricing* file and its own docstring already answers most of (a)/(b). Verbatim:

> Two central statements of `Theory/Typing/ChurchRosser.lean` are false as written
> (`NormalEq.descend`, `NormalEq.parRed`). … **Answer: two jobs.**
> The repair the two false statements need is an extension of the *reduction* relation
> (a proof-replacement / `K⁺` step); the eta job is an extension of the *conversion* relation.
> Those are moves in opposite directions.

Structure, confirmed by reading:
- §1 `CRSchema` + `crSchema_eq_parRedStatement : … = @ParRedStatement _ := rfl` (anti-strawman)
  + `crSchema_congr` / `not_crSchema_of_inert`.
- §2 `DescentLamP` / `DescentOutP` / `DescendStatementP`, each `rfl`/`Iff`-checked equal to the
  real one. **The layer is polymorphic in exactly three ingredients**: a conversion, a
  multi-step reduction, a typing judgment. That count is `rfl`-checked, not asserted.
- §3 `StructEtaSite` (10 fields) + `StructEtaSite.not_of_no_defeqs`;
  `IsDefEqSE.toIsDefEq_of_no_defeqs` (mutual with `HasArgsSE.toHasArgs_of_no_defeqs`),
  `isDefEqSE_iff_of_no_defeqs`, `isDefEqSEU_iff_of_no_defeqs`.
- §4 `NormalEqSE` (11 constructors: 9 ported + `structEtaL` + `structEtaR`),
  `ParRedSE` (9 constructors: 8 ported + `structEta`), `ParRedSES := ReflTransGen`,
  and `normalEqSE_iff_of_no_defeqs` / `parRedSE_iff_of_no_defeqs` / `parRedSES_iff_of_no_defeqs`
  — **pointwise EQUAL, not merely conservative**, at a defeq-free env.
- §5.1 `descendStatementSE_iff_of_no_defeqs`, then `descendSE_uniq_sortUniq_not_all`
  (transported by *inertness*). §5.2 `not_parRedStatementSE_of_propMajor` (transported by
  *porting the argument* — needs no hypothesis on `env.defeqs` at all).
- §6 disjointness of the two jobs' witnesses; §7 vacuity checks; §8 a 32-line inline
  `#print axioms` sweep.

**Correction to the brief's constructor count.** The brief says "the 14-constructor relation".
`IsDefEqSE` does have 14 (13 + `structEta`), but `NormalEqSE` has **11** and `ParRedSE` has
**9**. The confluence layer's relations are not 14-constructor. Counts matter for step (a).

**The corrected shape is already named in the file**, not something this round must invent:
"The repair `descend` needs is on the *reduction* side (`Theory/Typing/ParRedMissing.lean`'s
proof-replacement step, or `KEta.lean`'s `ParRedK`)". Next: verify those exist and whether
`parRed` has already been restated over `ParRedK` (a recent commit message claims it has).

### M4 (2026-09-04T04:28Z) — (c) the model check: **P7 is HALF WRONG, and the wrong half matters**

Import closures computed from the source `import` lines (same method as `can-cite.py`):

| module | closure size | SetModel modules in closure |
|---|---|---|
| `Lean4Lean.Theory.Typing.ChurchRosser` | 48 | **0** |
| `Lean4Lean.Theory.Typing.KEta` | 64 | **0** |
| `Lean4Lean.Theory.Typing.ParRedMissing` | 71 | **0** |
| `Lean4Lean.Theory.Typing.ConfluenceRebuildPrice` | 230 | **20** |
| `Lean4Lean.Theory.Typing.SEReduce` | 232 | **20** |

The 20: `Cardinal, Cnst, CnstRecursion, Consts, FalseProp, Inaccessible, IndCard, IndStage,
InductOracleAudit, InductOracleWitness, Inductive, Interp, InterpSound, InterpSubst,
PropSplitAudit, Rank, SoundInduction, UnitOracleLarge, UnitOracleWitness, Universe`.

So: "confluence needs nothing from `Theory/SetModel/`" is **true of `ChurchRosser` itself**
(0 of 48) and **false of the modules where `NormalEqSE`/`ParRedSE` actually live** (20 of 230).
Consequence for (d): a Church-Rosser-over-SE theorem written at `ConfluenceRebuildPrice` or
later inherits the entire set model in its closure — a layering fact, not a mathematical one,
but it is the difference between a 48-module and a 230-module context and `layer-check.py`
cares. **Anyone told "no model dependency" and placing the proof next to the SE relations will
be surprised.** Whether the *mathematics* needs the model is a separate question, below.

### M5 (2026-09-04T04:33Z) — (a) induction/case-analysis site census, by walking PROOF TERMS

Method: load the population, for every `Lean4Lean.*` constant read
`ci.value?.getUsedConstantsAsSet`, test membership of `NormalEq.rec` / `ParRed.rec` /
`CParRed.rec` (pass 1) and of the three `.casesOn` (pass 2, excluding pass-1 hits).
Auto-generated companions (`rec/recOn/brecOn/casesOn/below/binductionOn/ndrec/noConfusion*/
ibelow/induct/eq_def`) excluded; `match_N` helpers folded into their parent. The brief is right
that grep finds nothing: every site is `induction H with | …`, so only the proof term shows it.

**Pass 1 — inducts on a layer relation (`.rec`): 26 declarations.**

| module | n | declarations |
|---|---|---|
| `Theory.Typing.ChurchRosser` | **15** | `ParRed.weakN, ParRed.defeqDFC, NormalEq.weakN_inv_DFC, NormalEq.parRed, NormalEq.defeq, CParRed.toParRed, NormalEq.defeqDFC, NormalEq.instN, ParRed.defeq, NormalEq.instN₂, NormalEq.symm, ParRed.instN, ParRed.weakN_inv, NormalEq.weakN, ParRed.triangle` |
| `Verify.Typing.ConstSpine` | 5 | `NormalEq.constApp_whnf, ParRed.constApp_inv, NormalEq.constApp_forallE, NormalEq.constApp_inv, NormalEq.constApp_sort` |
| `Theory.Typing.ConfluenceRebuildPrice` | 2 | `normalEqSE_iff_of_no_defeqs, parRedSE_iff_of_no_defeqs` (**already ported**) |
| `Theory.Typing.NormalEqStrengthen` | 1 | `NormalEq.weakN_inv_DFC'` |
| `Theory.Typing.KSite7Rows` | 1 | `parRedKStatement_of_rows` |
| `Theory.Typing.KEta` | 1 | `ParRed.toK` |
| `Theory.Typing.HeadReduction` | 1 | `StRed.triangle` |

**Pass 2 — case-analyses only (`.casesOn`, no `.rec`): 20 declarations.**

| module | n | declarations |
|---|---|---|
| `Theory.Typing.DescendRefute` | 7 | `refParRed_G2, refParRed_bvar, refParRed_F3, refParRed_constBvar, refParRed_const, refParRed_G3, refParRed_id` |
| `Theory.Typing.KCanonical` | 3 | `not_crStatement_of_kstep, parRedS_lam_inv, not_parRedStatement_of_hK` |
| `Theory.Typing.ChurchRosser` | **3** | `NormalEq.descend` (**the hole**), `ParRedExt.parRed_beta`, `NormalEq.trans` |
| `Theory.Typing.KSite7` | 2 | `NormalEq.trans_domEq, DomEq.trans_normalEq` |
| `Theory.Typing.HeadReduction` | 2 | `IsDefEq.reduce_sort, IsDefEq.reduce_forallE` |
| `Verify.Typing.ConstSpine` | 2 | `ParRed.sort_inv, ParRed.forallE_inv` |
| `Theory.Typing.KDescend` | 1 | `NormalEq.descendV` |

**Totals: 46 sites population-wide; 18 inside `ChurchRosser` itself (15 + 3).**
2 already ported. So the port surface is **44**, of which **18** are the confluence layer proper
and **26** are downstream consumers and refutation witnesses.

### M6 (2026-09-04T04:33:56Z) — `exists.lean` on the layer + the K route. **A CORRECTED STATEMENT ALREADY EXISTS AND IS PROVED.**

`population: 457 built modules` (up 2 from M1 — another stream landed modules mid-round).

| name | module | arity | cone | own hole | holes in cone |
|---|---|---|---|---|---|
| `Lean4Lean.VEnv.NormalEq.descend` | ChurchRosser | 12 | 3874 | **true** | `[IsDefEqU.forallE_inv_stratified, WF.rigidShapeUniqNS, NormalEq.descend]` |
| `Lean4Lean.VEnv.NormalEq.parRed` | ChurchRosser | 8 | 4135 | false | `[weakN_iff, forallE_inv_stratified, rigidShapeUniqNS, **NormalEq.descend**]` |
| `Lean4Lean.VEnv.ParRed.triangle` | ChurchRosser | 10 | 4084 | false | `[weakN_iff, forallE_inv_stratified, rigidShapeUniqNS]` — **no `descend`** |
| `Lean4Lean.VEnv.ParRedS.church_rosser` | ChurchRosser | 10 | 4366 | false | `[…, **NormalEq.descend**]` |
| `Lean4Lean.VEnv.NormalEq.descendV` | **KDescend** | 13 | 3876 | false | `[forallE_inv_stratified, rigidShapeUniqNS]` — **no `descend`** |
| `Lean4Lean.VEnv.parRedKStatement_of_rows` | **KSite7Rows** | 3 | 4298 | false | `[weakN_iff, forallE_inv_stratified, rigidShapeUniqNS]` — **no `descend`** |
| `Lean4Lean.VEnv.ParRedK` | KEta | 4 | 4 | — | `[NO PROOF TERM]` (a definition, like every inductive) |
| `Lean4Lean.VEnv.EtaK` | KEta | 4 | 4 | — | `[NO PROOF TERM]` |
| `Lean4Lean.VEnv.parRedKStatement` | — | — | — | — | **NOT FOUND** (name is not that) |

All of the above carry `*** WATCHED IN CONE: [Lean4Lean.VEnv.IsDefEq.uniq, Lean4Lean.VEnv.IsDefEq.uniqU] ***`.

**This changes the (b) verdict.** The two "refuted central statements" already have corrected
replacements at 13 constructors, and both are *proved*, both free of the `descend` hole:
- `NormalEq.descendV` (`Theory/Typing/KDescend.lean`) — the descent over the V/VK route.
- `parRedKStatement_of_rows` (`Theory/Typing/KSite7Rows.lean`) — the confluence statement
  restated over `ParRedK`, reduced to "rows".
And `ParRed.triangle` — the measure-based diamond that §3 of `ParRedMissing.lean` warns is the
real blocker — **does not go through `descend`** either. So the residual holes on the whole
route are the three unrelated ones (`IsDefEqU.weakN_iff`, `IsDefEqU.forallE_inv_stratified`,
`WF.rigidShapeUniqNS`) plus the two watched statements, *not* the confluence defect.
**Nothing has been rewired**: `ParRedS.church_rosser` and `NormalEq.parRed` still route through
the `NormalEq.descend` hole. The corrected statements exist beside the old ones, unconsumed.

### M7 (2026-09-04T04:38Z) — **(b) ANSWERED, and the answer is "the formulation must change; the corrected shape is joinability, and it is already named"**

Two files carry it.

**`Lean4Lean/Theory/Typing/StructEtaPrice.lean` §1 and §6.**
- §1's induction-site census (measured 2026-09-03 17:01–17:25 UTC, population 421, by walking
  proof terms — the same method as my M5): `IsDefEq` **22**, `IsDefEqStrong` **31**,
  `NormalEq` **31**, `ParRed` **26**, `ParRedK` **23**, `IsDefEqE` **3**, `IsDefEqRaw` **0**,
  `ParRedS` 0 (a closure `def`). **Total 136.** My M5 figure of 46 is a *subset*: I counted only
  the three confluence-layer relations and I netted out the compiler companions the same way,
  but §1 counts `.recOn/.brecOn/.below.*/.ndrec/.induct` as well and includes `IsDefEq`,
  `IsDefEqStrong`, `ParRedK`, `IsDefEqE`. Both figures are real; **136 is the number to quote
  for "what the fourteenth constructor costs", 46 for "what the confluence layer costs"**, and
  57 (`NormalEq` 31 + `ParRed` 26) for the two relations a CR port actually inducts on.
- §6 `Lean4Lean.eta_and_constNoConf_incompatible` FOUND, `StructEtaPrice`, arity 3, cone 5237,
  hole false, `holes in cone: [Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified]`,
  `watched declarations in cone: none of 6`. **Route-independent**: *no* relation can satisfy
  structure eta at `MutField.unitEnv` and const-head no-confusion together. So
  `Lean4Lean.VEnv.IsDefEq.constApp_inv` (`Verify/Typing/ConstSpine`, arity 14, cone 4446,
  holes `[weakN_iff, forallE_inv_stratified, rigidShapeUniqNS, NormalEq.descend]`, watched 2)
  is **false** for the extended relation, not merely unproved — and §6 records this is a fact
  about *Lean*: `structure A where` / `axiom foo : A` / `example : foo = A.mk := rfl` typechecks.

**`Lean4Lean/Verify/QuotAppParams.lean` (667 lines) — the decisive file, and the brief does not
mention it.** It builds `quotParams`, the canonical `.app`-pattern `Params` instance over a real
`VEnv.WF` environment (the quotient rule), and proves four things:

1. `quotParams_not_patMajorCanonical` — M3 is FALSE there.
2. `quotParams_not_kDiamond` — **`KDiamond` is FALSE there.** `KDiamond` is the hypothesis the
   whole K-route confluence reduction bottoms out in (`kDiamond_of_patMajorCanonical`,
   `KEtaDiamond.etaKDiamondAt_of_kDiamond`).
3. `quotParams_kDiamond_joinable` — **and the rule table is not at fault**: the two reducts are
   **joinable in one β-step**. Verbatim: *"So the defect is `KDiamond`'s demand that the two
   reducts be `NormalEq` on the nose; the joinability shape `KEta.lean`'s `EtaKDiamond` already
   uses survives this witness. **The repair is a restatement, not a new rule-table field.**"*
4. `quotParams_not_parRedStatement`, `quotParams_not_crStatement` — `NormalEq.parRed`'s and
   `IsDefEq.church_rosser`'s statements are **refuted at a reachable instance**.

**The vacuity question (my prior Q3) is settled and the answer is the good one.**
`ParRedMissing.lean` §4.1 says the `propMajor` refutations "are refuted at instances that **do
not exist in this tree yet** (grade of ledger row 33, not row 32)". `QuotAppParams.lean` builds
exactly such an instance and says so: *"Ledger row 33's grade for these refutations therefore
moves from 'refuted only at an instance that does not exist' to 'refuted at an instance
conditional on the injectivity corner'. It is **not** an unconditional refutation, and must not
be quoted as one."* The condition is exactly two holes: `IsDefEqU.forallE_inv_stratified` and
`WF.rigidShapeUniqNS` (Π-injectivity and unique typing — both things the project is *proving*,
not doubting). So: **the refutations are non-vacuous modulo the injectivity corner.**

### M8 (2026-09-04T04:42Z) — **the (b) verdict in full: the formulation must change, the corrected shape ALREADY EXISTS, and it lands ON Church-Rosser rather than reducing it**

`Lean4Lean/Theory/Typing/KDiamondJoin.lean` (619 lines) has already done the restatement this
round was asked to design. Exact shapes, read from source:

```
def KDiamond    : Prop := ∀ {Γ e e₁ e₂}, OnCtx Γ (IsType env univs) →
                            KStep Γ e e₁ → KStep Γ e e₂ → Γ ⊢ e₁ ≡ₚ e₂          -- NormalEq on the nose
def Joins (Γ e₁ e₂) : Prop := ∃ e₃ e₄, ParRedKS Γ e₁ e₃ ∧ ParRedKS Γ e₂ e₄ ∧ Γ ⊢ e₃ ≡ₚ e₄
def KDiamondJ   : Prop := KDiamond with `Joins` for `NormalEq`
def EtaKDiamond : Prop := … EtaK Γ e e₁ → EtaK Γ e e₂ → Joins Γ e₁ e₂            -- already joinability
```
`etaKDiamond_eq_joins` and `etaKDiamondAt_eq_joins` are `rfl` — the reuse is literal.

Answering the three sub-questions of (b) for the corrected statement `KDiamondJ`:

1. **Is it true?** *Not refuted, and not proved.* §8 is explicit: "Not that `KDiamondJ` is
   **true** at `quotParams`. What is proved is that the witness which refutes `KDiamond` there
   does *not* refute it" — `joins_beta_arg` / `joins_beta_arg_id` discharge the β-in-a-matched-
   argument configuration at **every** `Params` instance, in one `ParRedK` step.
2. **Does it suffice?** *Yes for the η-layer.* `etaKDDiamondAt_of_kDiamondJ` is **both** repairs
   at once and "with them the η-layer needs `KDiamondJ` and nothing else", `[propext, Quot.sound]`.
   `kDiamondJ_of_patMajorCanonicalJ` shows the reduction from M3 survives, same axiom set.
3. **Is it provable?** **This is where the route dies, and it is a circularity, not a difficulty.**
   `KDiamondJ` is *sandwiched between two Church-Rosser statements*:
   - **above**: `kDiamondJ_of_crK` — `KDiamondJ` follows from Church-Rosser over `ParRedK`. So
     `KDiamondJ` is an *instance* of CR, where `KDiamond` was strictly stronger than one.
   - **below**: `quotPat_argJoin_of_kDiamondJ` (**hole-free**, `[propext, Quot.sound]`) — at any
     instance registering `quotPat`, `KDiamondJ` implies that for **arbitrary definitionally
     equal** `x, x'` the applications `g x` and `g x'` are joinable. Verbatim: *"That is
     **Church-Rosser at an application**, not a property of the rule table."*

   The file's own conclusion: *"the localisation `PatMajorCanonical → KDiamond` was supposed to
   deliver is **gone** — `KDiamondJ` is sandwiched between two Church-Rosser statements.
   `KDescend.KDiamond`'s own docstring already warned that 'the whole content of `KDiamond` is
   the upgrade from `≡` to `≡ₚ`, which is exactly what confluence is being built to deliver';
   the joinability form does not escape that, it lands *on* it."*

   And the anti-strawman that the weakening is not free: `joins_normal_iff` (**hole-free**) — if
   both sides are `ParRedK`-normal then `Joins ↔ NormalEq`. So on normal forms the restatement
   *is* the original; the slack is exactly the pairs where one side steps.

**VERDICT.** The refutations are not telling us to fix two lemmas. They are telling us that the
project's strategy for confluence — *reduce Church-Rosser to a canonicity property of the rule
table (M3 / `KDiamond`)* — **cannot work at any strength of that property**, because the
corrected (joinability) form of the property is itself an instance of Church-Rosser at an
application. Restating further cannot help: `joins_normal_iff` pins the only available slack,
and weakening past it collapses back to `NormalEq`. A Church-Rosser proof for this system must
come from something that is **not** a rule-table property — a measure/termination argument, or a
model-theoretic normalisation — and no such thing is in the tree.

Corollary for the eta front specifically: `church_rosserSE` is *not* gated on eta work at all.
It is gated on the same missing ingredient as `church_rosser`, which is `ParRed.triangle` over
`ParRedK` (KDiamondJoin §6: consumer `ParRed.triangle` — **"none — it does not exist yet, at
either strength. Not claimed as satisfied"**). Porting `NormalEqSE`/`ParRedSE` upward buys
nothing until that exists.

### M9 (2026-09-04T04:55Z) — the one claim that needed Lean: **the new `ParRedSE` rule is an expansion that re-fires on its own output**

Built `Lean4Lean/Theory/Typing/CRSEScope.lean` (7 declarations, all `sorryAx`-free).

First, a read that no instrument reports and that reframes §7 of `ConfluenceRebuildPrice`:
`VEnv.StructEtaSite`, `NormalEqSE.structEtaL`, `NormalEqSE.structEtaR` and `ParRedSE.structEta`
occur in **`ConfluenceRebuildPrice.lean` alone** (grep over the whole tree), and **every**
occurrence is a definition or a refutation (`absurd hs (StructEtaSite.not_of_no_defeqs …)`).
`ConfluenceRebuildPrice` §7's vacuity check exhibits a β step and an old-`NormalEq` pair at
`refEnv` — an environment where its own §6 proves the three new rules are dead. **So the three
new rules have never been fired anywhere, and §7 does not cover them.**

What CRSEScope proves:
- `Lean4Lean.VEnv.StructEtaSite.iterate` `[propext, Quot.sound]` — the site is closed under its
  own expansion, needing **only** that the expansion is typed at the same type. A `structure`
  update: the nine other fields never mention `e`. Hence `ParRedSE.structEta` is an *expansion
  that re-applies to its own result*: `e ≫ η e ≫ η (η e) ≫ …`.
- `Lean4Lean.VEnv.not_parRedSE_rigid_of_structEtaSite` `[propext, Quot.sound]` — therefore
  `VEnv.parRedSES_rigid`'s hypothesis `∀ o, ParRedSE Γ e o → o = e` is **false** at any site
  whose expansion differs from its subject. That hypothesis is exactly what
  `not_parRedStatementSE_of_propMajor` consumes, and `ParRed`-normality is what `ParRed.triangle`,
  `CParRed.exists` and `KDiamondJoin.joins_normal_iff` are built on.
- `Lean4Lean.VEnv.etaExpansionG_idem_of_no_fields` `[propext]` — **and the regress is
  positive-fields-only.** At zero fields `VInductDecl'.etaExpansionG` does not mention `e` at all
  (`etaExpansionG_of_no_fields`: it is `(.const C.name us).mkApp ps`), so it is a *constant* map,
  its own fixed point after one step.
- `etaIterG` `[propext]`, `EtaStagesTyped` / `StructEtaSite.at_stage` / `parRedSES_etaIter`
  `[propext, Quot.sound]` — the unbounded `ParRedSES` chain, with "every stage is typed" carried
  as an explicit hypothesis because **no witness of `StructEtaSite` exists anywhere in the tree**
  to discharge it against. Stated, not assumed inline, so a future witness can be pointed at it.

**This lines the reduction side up with the model side exactly.** The model validates *zero-field*
surjective pairing and validates it as forced; zero fields is precisely where §3 says the
reduction rule is a fixed point and no orientation question arises. Positive fields is where both
the model validation and the rule's orientation are open.

**What this does and does not refute.** It does not refute `ParRedSE` — an expansion relation can
still be confluent, and `NormalEqSE` is symmetric so the conversion side is indifferent to
orientation. It refutes the **method**: every confluence argument in this tree is stated in terms
of `ParRed`-normal forms, and `ParRedSE` has none at a positive-field structure. So
`ParRedSE.structEta` must be **oriented as a contraction** (`η e ≫ e`) before any of that
machinery ports, and then `NormalEqSE.structEtaL`/`structEtaR` are what must be re-derived.

### M10 (2026-09-04T04:47Z) — (d) THE ORDERED PATH, with independence marked

Marks: **[R]** restatement, **[N]** new-case, **[P]** port of an existing 13-constructor proof.

The headline reordering: **`church_rosserSE` is not an eta target.** Its blocker is shared with
`church_rosser` and is not touched by anything on the eta front. The eta front's own product is
*already delivered* — `constAppInvSISE_iff_of_noEta` (cone 831, hole-free) guarded by
`NoEtaEligible` (cone 618) is the right shape, given that `eta_and_constNoConf_incompatible`
makes `constApp_inv` (187 users) **false**, route-independently, for any relation with structure
eta. There is nothing further for eta to prove until step 2 lands.

| # | step | mark | gated on | notes |
|---|---|---|---|---|
| **0** | **Re-orient `ParRedSE.structEta` as a contraction** — `… → ParRedSE Γ (η e) e`, not `… → ParRedSE Γ e (η e)` | **[R]** | **nothing** | CRSEScope §1–§2. Cheap: `ConfluenceRebuildPrice`'s §4 inertness cases die by `absurd hs` and are unaffected by the flip. Then `NormalEqSE.structEtaL/R` are derived from the contraction, not parallel to it |
| **1** | **Fire the three new rules once, anywhere** | **[R]** | **nothing** | No `StructEtaSite` witness exists in the tree; the rules have never fired. `StructEtaPrice` §5 already fires `IsDefEqSE.structEta` at `MutField.unitEnv` (zero-field) and `MutField.declEnv` (positive-field) — reuse those. Until this lands, §7's vacuity check covers only the *old* rules |
| **2** | **A Church-Rosser argument that is not a rule-table property** | **[R]** | **nothing** | **The real blocker, and it blocks `church_rosser` and `church_rosserSE` equally.** `KDiamondJoin` §3: `KDiamondJ` is sandwiched between `kDiamondJ_of_crK` (above) and `quotPat_argJoin_of_kDiamondJ` (below, hole-free) — it *is* CR at an application. `joins_normal_iff` (hole-free) pins the only slack, so no further weakening exists. `ParRed.triangle` over `ParRedK` does not exist "at either strength" (`KDiamondJoin` §6). Needs a measure/termination or model-theoretic normalisation argument; **nothing of that kind is in the tree** |
| **3** | **Positive-field model validation of structure eta** | **[R]** | **nothing** | `SetModel.eq_singleton_of_recProp` (cone 5826, `sorryAx`-free) + `RecTypePeel` §8 `eq_singleton_of_mem_interp_mkPi3` validate **zero-field** surjective pairing, forced. Positive fields: nothing. `StructEtaPrice` §7 closing note prices the telescoped form at "one file". CRSEScope §3 says positive fields is *exactly* where the orientation question lives, so 0 and 3 inform each other but neither gates the other |
| 4 | Port the 18 confluence-layer sites to `NormalEqSE`/`ParRedSE` | **[P]** | 2 | 15 `.rec` + 3 `.casesOn` in `ChurchRosser` (M5). Pointless before 2: the thing being ported is `NormalEq.descend` (a hole) and `NormalEq.parRed` (refuted at `quotParams`) |
| 5 | The `structEta` / `structEtaL` / `structEtaR` cases in those 18 | **[N]** | 0, 1, 4 | With the contraction orientation these are the *new* cases; with the current expansion orientation they are unprovable at any positive-field structure |
| 6 | Port the 26 downstream consumer sites | **[P]** | 4 | `Verify.Typing.ConstSpine` 7, `DescendRefute` 7, `KCanonical` 3, `KSite7` 2, `HeadReduction` 3, `KDescend` 1, `NormalEqStrengthen` 1, `KSite7Rows` 1, `KEta` 1 (M5) |
| — | **Do NOT revisit the closed-`VDefEq` route.** | — | — | `SEReerectionScope.lean` refutes it in both orientations: `Params.not_defeqs_etaDfZ` (orientation 1), `Params.not_pat_ctorSpine` (orientation 2, collides with `pat_uniq`), `SimplePattern.eq_defn_of_toPattern_varN` (not even expressible at positive arity). `StructEtaPrice` §7's "0 induction cases against 136" is priced against an uninhabitable `Params` |

**Independent, spawnable now, in parallel: 0, 1, 2, 3.** Steps 4–6 are strictly downstream of 2
and should not be spawned. Step 5 is downstream of 0, 1 and 4.

**Two-sided honesty about step 2.** It is not a hard lemma; it is a missing *kind* of argument.
`KDescend.KDiamond`'s own docstring already said "the whole content of `KDiamond` is the upgrade
from `≡` to `≡ₚ`, which is exactly what confluence is being built to deliver. Assuming it inside
the confluence proof is therefore circular unless it is supplied from outside, i.e. by a
canonicity fact about the rule table." `KDiamondJoin` §3 then closes off the rule table as a
source. So the tree has, between those two files, machine-checked that its own strategy for
confluence has no source. That is the finding of this round, and it is not an eta finding.

### ROUND-CLOSE (2026-09-04T04:47Z)

| check | result |
|---|---|
| whole-tree `lake build` | **`Build completed successfully (1644 jobs)`, exit 0** |
| `scripts/sorry-census-all.lean --run` | `on disk: 485; in default-target population: 461; Experimental: 24`; `BUILT: 461; in population but NOT BUILT: 0`; **`HOLES … : 13`** (pass A 13, pass B 0) |
| guard 1 | `Axioms.lean declares exactly the 24 frozen axioms ✓` |
| guard 2 | `kernel_sound axioms within whitelist ✓ (proof INCOMPLETE: sorryAx present)` |
| guard 3 | `checker cone implementation gaps within frozen list (2/2 remaining) ✓` |
| in-repo section-variable warnings | **zero** (`grep '^warning: Lean4Lean/.*automatically included section variable'` empty; the only such warning in the build is Foundation's `SetTheory/Z.lean:35`) |
| `scripts/layer-check.py` | **exit 0**; `HARD RULE: no Theory/SetModel/ module may reach Lean4Lean.Verify.* — ok, 66 module(s) checked` |
| `exists.lean` on all 7 new declarations | all FOUND in `Lean4Lean.Theory.Typing.CRSEScope`, `own value is a hole: false`, `cone reaches sorryAx: false`, `watched declarations in cone: none of 6` |
| inline `#print axioms` (§5 of CRSEScope) | 7/7 clean: `[propext]` ×2, `[propext, Quot.sound]` ×5 |

Frozen files untouched. Files written this round: `docs/handoff-crse.md`,
`Lean4Lean/Theory/Typing/CRSEScope.lean`. Nothing else.

### Corrections to the brief, collected

1. **P3** was quoted against the unprimed name. `constAppInvSISEFromWF_iff_etaOnly` is arity 1,
   cone 882, clean; the primed `constAppInvSISEFromWF_iff_etaOnly'` is the arity-0/cone-7580/
   four-holes/two-watched one. Both exist; they are different declarations.
2. **P2**: `NoEtaEligible` arity is **2**.
3. **P5's use of `[NO PROOF TERM]` as a gap signal is a misreading.** `NormalEq` and `ParRed`
   print it too (cone 4 each) — it is what every inductive predicate prints. It says nothing about
   `NormalEqSE`/`ParRedSE` that it does not also say about the originals.
4. **"the 14-constructor relation"**: `IsDefEqSE` has 14, but `NormalEqSE` has **11** and
   `ParRedSE` has **9**.
5. **P7 is half wrong.** `ChurchRosser`'s closure has 0 of 48 SetModel modules; but
   `ConfluenceRebuildPrice`'s has **20 of 230** and `SEReduce`'s **20 of 232**, and
   `StructEtaPrice` (where `IsDefEqSE` lives) **20 of 186**. Anyone told "no model dependency" and
   placing a proof next to the SE relations will be surprised. The model validation itself is real,
   forced and clean — but **zero-field only**.
6. **"the eta front's single remaining reduction target"** is the framing this round overturns.
   `church_rosserSE`'s blocker is `church_rosser`'s blocker, is not eta-specific, and is a
   circularity in the project's confluence strategy rather than a proof obligation.
7. The brief does not mention `Lean4Lean/Verify/QuotAppParams.lean` or
   `Lean4Lean/Theory/Typing/KDiamondJoin.lean`. They are the two files that decide (b).
