# Handoff (round 2): a general nested producer for `Lean4Lean.TrIndDeclN`

Owner files this round: `Lean4Lean/Verify/Inductive/TrIndDeclNProducer.lean` (new),
`docs/handoff-trinddeclnproducer2.md` (this file).
Round opened: 2026-09-03T23:32Z UTC.

Predecessor: `docs/handoff-trinddeclnproducer.md` — a round that crashed before taking any
measurement, leaving only priors P1-P8. Scoring those is task 0 of this round.

## §1 — My own priors, recorded BEFORE any measurement

Written before opening a single Lean file or running a single script this round. The only
inputs so far are CLAUDE.md, the brief, and the predecessor's §1. Nothing below is measured.

### 1.1 On the predecessor's eight predictions

I am asked to score P1-P8, and especially P3 ("at least one brief figure is wrong", 70%) and
P7 ("ownership attribution correct", 60%). My priors on how the scoring will come out:

- P3 I expect to **resolve TRUE**. The brief this round hands me two figures
  (`trIndDeclN_of_succLevel` arity 20 cone 3348; `trIndDeclN_of_head_indexFree` arity 20 cone
  3380) and self-reports fifteen errors this session. Two independent arity-20 claims for two
  differently-shaped theorems is itself mildly suspicious — a level route and an index-free
  route should not normally have identical arity. I put ~75% on at least one number being off.
  Note a subtlety I must not fudge: P3 as written scores against the *predecessor's* brief,
  which quoted four figures (3345/3348/3378/3380 with arities 21/20/15/20). I will score it
  against those, and separately report this round's two.
- P7 I expect to **resolve PARTIALLY or FALSE**, ~55% on "not correct for all four". The brief
  itself flags `csubstTy_freshIn` as possibly already proving the `FreshIn` fact, which if true
  means `FreshIn` is *not* open `RestoreData` business — that alone would falsify P7's "correct
  for all four open fields" if P7 is read as also asserting they are open.
- P1 (structure with 5-9 fields): I expect TRUE, ~70%. Lean4Lean's `Tr*` relations are
  typically structures; 5-9 is a wide band.
- P2 (exactly 4 open): I expect FALSE, ~60%. Rounds that predict "exactly the number the brief
  named" usually find either one already closed or one unnamed extra.
- P4 (`trSpine` genuinely general): TRUE, ~80%. Two named routes with cones is strong evidence.
- P5 (`ntreeAux` index-free): genuinely uncertain, 55%.
- P6 (witness needs concrete `trIndDeclN_wit`): I expect TRUE, ~70% — and this is the honest
  risk in part (d). The brief demands "general theorems rather than block-specific lemmas".
- P8 (census 13 / NOT BUILT 0): TRUE, ~90%.

### 1.2 My priors on the field checklist (part (a))

Unread. I expect `TrIndDeclN` to be a structure. My band: **6-10 fields**, slightly wider and
higher than the predecessor's 5-9, because a *nested* translation relation typically carries
both the non-nested content and nesting-specific coherence. I expect the classification to
split roughly: 2-4 already general (shape/arity/level-count bookkeeping plus `trSpine`),
2-3 general modulo a named lemma, and 3-5 open.

Specific guesses:
- A field relating `numParams`/`numTypes`/`uvars` — already general, arithmetic.
- Type-translation and constructor-translation fields — general modulo named lemmas.
- `trSpine` — already general via the two named routes.
- `Built`, `FreshIn`, `tyLvls`-WF, `Faithful` — the four the brief calls open. I predict at
  least one of these four is **already discharged in general** (most likely `FreshIn`, given
  the brief's own pointer to `csubstTy_freshIn`; second most likely `tyLvls`-WF as syntactic).

### 1.3 My priors on the assembly (part (b))

I predict the assembled producer lands at arity **18-28** and a cone within **±500 of 3400**.
I do not expect assembly to be the hard part. I expect the real cost to be (d).

### 1.4 My priors on vacuity (part (d))

`ntreeAux` at `Theory/Inductive/NestedHead.lean:624`, `uvars = 1`,
`params = [.sort (.succ (.param 0))]`. A single sort-valued parameter and one universe variable.

- I put 55% on it being index-free (P5 territory).
- I put 70% on needing to borrow at least one component from `NestedWit.trIndDeclN_wit`, and
  I commit now to labelling that honestly as "satisfiable, but that component came from the
  concrete witness" rather than claiming the general route.
- Degeneracy guard: I will assert `uvars = 1` and `params.length = 1` (specifically
  `params = [.sort (.succ (.param 0))]`) inside the witness statement so it cannot silently
  collapse to `nfnAux` (`uvars = 0`, `params = []`).
- Biggest vacuity worry: if the producer's hypotheses include both a level condition and an
  index-free condition, they might be jointly satisfiable only trivially. I will check that
  my witness's hypothesis instances are not each proved by `absurd`/`False.elim`-shaped
  reasoning, and I will report the `exists.lean` WATCHED IN CONE line for the witness itself.

### 1.5 Predictions I commit to, so a later round can score me

| # | Prediction | Confidence |
|---|---|---|
| Q1 | `TrIndDeclN` is a structure with 6-10 fields | 70% |
| Q2 | At least one of the brief's four "open" fields is already general | 65% |
| Q3 | At least one of this round's two brief figures (arity 20/cone 3348, arity 20/cone 3380) is wrong | 75% |
| Q4 | `csubstTy_freshIn` really does give `FreshIn` from type-staging success alone | 55% |
| Q5 | The assembled producer's arity is in 18-28 | 60% |
| Q6 | The arity-0 witness is achievable without `NestedWit.trIndDeclN_wit` | 30% |
| Q7 | Census stays 13 / NOT BUILT 0 | 90% |
| Q8 | There is at least one `TrIndDeclN` field the brief never mentions | 60% |

§2 onward is written after measurement.

---

## §2 — Measurements

All measured at commit `df1f380` (round opened at `753bc78`), population **440 built modules**
for `exists.lean` / `shape.lean`, **443** for `sorry-census-all.lean`.

### 2.0 Scorecard for the predecessor's P1-P8

| # | Prediction | Conf. | Verdict | What I measured |
|---|---|---|---|---|
| P1 | `TrIndDeclN` is a structure with 5-9 fields | 70% | **FALSE** | It is a structure, but with **12** fields (`InductR.lean:276-352`). |
| P2 | Exactly 4 fields are open | 55% | **FALSE** | **3** are open (`trType`, `trCtorsLen`, `trCtors`). And the four it named are not fields of `TrIndDeclN` at all — see P7. |
| P3 | At least one brief-supplied arity or cone number is wrong | 70% | **FALSE** | All four re-measured **exactly**: `VIndRestore.trSpine_of_resultSortInhab` 21/3345, `trIndDeclN_of_succLevel` 20/3348, `VIndRestore.spineHargsN_of_head_indexFree` 15/3378, `trIndDeclN_of_head_indexFree` 20/3380. This round's two figures also exact. |
| P4 | `trSpine` genuinely general, both routes real, neither a hole | 80% | **TRUE** | Both found, both `own value is a hole: false; cone reaches sorryAx: false`, and both fire at `ntreeAux`. One correction of *kind* below. |
| P5 | `ntreeAux` satisfies the head-member (`indexFree`) route | 60% | **TRUE** | `(ntreeAux.types.getD 0 default).indices = []` by `decide`; it is the route my §3 witness uses. |
| P6 | The arity-0 witness needs concrete `trIndDeclN_wit` for ≥1 open field | 65% | **FALSE** | Cone of `ntreeAux_trIndDeclN` (5958): `NestedWit.trIndDeclN_wit` **false**, `trIndDeclN_wit'` **false**, `TrIndDecl.toN` **false**. |
| P7 | Ownership attribution correct for all four open fields | 60% | **FALSE** | Wrong in kind for all four and wrong in fact for `Faithful`. Detail in §2.3. |
| P8 | Census stays 13 / NOT BUILT 0 | 85% | **TRUE** | `BUILT: 443; NOT BUILT: 0`; `HOLES … unioned across both passes: 13`. |

**Score: 3 of 8 (P4, P5, P8).** The two the brief most wanted both came out FALSE — and in the
direction *favourable to the brief* for P3: the predecessor bet against the brief's arithmetic
and lost. Every one of the four quoted numbers was right. My own Q3 made the same bet and lost
the same way; the lesson is that this brief's *numbers* have been reliable while its
*attributions* have not, and the two should be doubted separately.

### 2.1 (a) THE FIELD CHECKLIST — `Lean4Lean.TrIndDeclN`, 12 fields

Measured **2026-09-03T23:43:29Z**, at `Lean4Lean/Verify/Environment/InductR.lean:276-352`.
Classification is against *general* discharge, i.e. no block-specific lemma.

| # | field | class | discharged by |
|---|---|---|---|
| 1 | `safe : isUnsafe = false` | **block data** | an input of the construction site, not an obligation |
| 2 | `uvars : Us.length = D.uvars` | **block data** | ditto |
| 3 | `np : nparams = D.np` | **block data** | ditto |
| 4 | `length : D.types.length = types.length + numNested` | **block data** | ditto (`r.types.length = types.length + numNested` is a `Result` fact, not a `RestoreData` field) |
| 5 | `companions` | **already general** | `ElimNestedInductive.Result.RestoreData.companions` — a *field* of `RestoreData`, so free wherever you have one |
| 6 | `trType` | **OPEN** | nothing in the tree concludes `TrIndType` except `TrIndDecl.trType` / `TrIndDeclN.trType` (the two structure fields) and the four `rec`/`casesOn`/`recOn`/`mk` — measured with `shape.lean HEADS="TrIndType"`, 10 hits, all of them projections or recursors |
| 7 | `trCtorsLen` | **OPEN** | see §2.4 for the named lemma that would close it |
| 8 | `trCtors` | **OPEN** | nothing concludes `TrIndCtorR` except `TrIndDeclN.trCtors` and `TrIndDeclN.{rec,recOn,casesOn,mk}` — `shape.lean HEADS="TrIndCtorR"`, 5 hits |
| 9 | `trSpine` | **already general, two routes** | `VIndRestore.spineHargsN_of_succLevel` (level) and `VIndRestore.spineHargsN_of_head_indexFree` (index-free, 15/3378) |
| 10 | `ctorName_own` | **general modulo a named lemma — NOW CLOSED, this round** | `trCtors` composed with `VIndRestore.OwnId.ctorName`; proved in `trIndDeclN_of_ownId`'s body. Costs the staging premise `∃ env₁, env.addIndTypesC D K = some env₁`, the same one `TrIndDecl.toN` already pays |
| 11 | `recName_own` | **general modulo a named lemma — NOW CLOSED, this round** | `VIndRestore.OwnId.recName` composed with `trType`'s *name* half; proved in `trIndDeclN_of_ownId`'s body |
| 12 | `recName_aux` | **already general at `mkRestore`** | `ElimNestedInductive.Result.RestoreData.mkRestore_recName_aux` (arity 11, cone 1901) |

**So: 4 block data, 5 already general, 3 open.** Fields 10 and 11 moved from "general modulo a
named lemma" to "closed" this round; the named lemmas turned out to be `OwnId`'s own projections,
already in the tree.

**A correction of kind to the brief, and it matters for how the checklist reads.**
`trIndDeclN_of_succLevel` and `trIndDeclN_of_head_indexFree` are **not producers of
`TrIndDeclN`**, despite their names and despite being the two things the brief pointed me at.
Each takes

    hrest : R.SpineHargsN D K env types → TrIndDeclN env Us nparams types iu numNested D K R

as a hypothesis — that is, "every field but `trSpine`, already in hand" — and supplies only the
one field. Their own docstrings say so (`TrSpineProducer.lean` §2b: "the hypothesis is *exactly*
'every field but `trSpine`'"). The genuinely general spine producers are the two
`VIndRestore.spineHargsN_of_*` lemmas. Nothing in the tree *concluded* a nested `TrIndDeclN`
before this round: `TrIndDecl.toN` does it only at `numNested = 0`, and the two `NestedWit`
witnesses are concrete at the degenerate block.

### 2.2 (b) THE ASSEMBLED PRODUCER

`Lean4Lean/Verify/Inductive/TrIndDeclNProducer.lean`, 187 lines, **zero diagnostics** (not just
zero errors — the LSP returns an empty item list, so no warnings either).

| name | arity | cone | hole | sorryAx | watched-in-cone |
|---|---|---|---|---|---|
| `Lean4Lean.trIndDeclN_of_ownId` | 21 | 1154 | false | false | none of 6 |
| `Lean4Lean.trIndDeclN_of_restoreData` | 21 | 2151 | false | false | none of 6 |
| `Lean4Lean.InductiveDeclExamples.ntreeAux_trIndDeclN` | **0** | 5958 | false | false | none of 6 |
| `Lean4Lean.InductiveDeclExamples.nfnAux_is_degenerate` | 0 | 48 | false | false | none of 6 |

`trIndDeclN_of_ownId`'s hypotheses, in the three groups the brief asked for:

* **block data** — `hsafe`, `huv`, `hnp`, `hlen`;
* **general, supplied by an existing theorem at the site** — `hown : R.OwnId D K`, `hcomp`,
  `hrax`, `hspine : R.SpineHargsN D K env types`, plus the staging existence
  `hst : ∃ env₁, env.addIndTypesC D K = some env₁`;
* **THE OPEN FIELDS, and exactly these three** — `hty` (`trType`), `hclen` (`trCtorsLen`),
  `hctors` (`trCtors`).

`trIndDeclN_of_restoreData` is the same theorem at `r.mkRestore`, where `hown`, `hcomp` and
`hrax` all disappear into `RestoreData` (`mkRestore_ownId` 7/1219, `RestoreData.companions`,
`mkRestore_recName_aux` 11/1901). At `mkRestore` the producer's only non-data hypotheses are
`hst`, `hspine`, and the three open fields.

`OwnId` rather than `mkRestore` is the interface of §1 deliberately: it is available both at the
computed restoration and at a hand-written one (`ntreeRestore_ownId`), which is the only reason
§3's witness can exist at `ntreeRestore`.

### 2.3 (c) OWNERSHIP ATTRIBUTION — VERIFIED, AND LARGELY WRONG

The brief's claim: "`Built`/`FreshIn`/`tyLvls`-WF are reportedly `RestoreData` business,
`Faithful` is `RestoreFaithful.lean`'s."

**Wrong in kind, for all four.** None of `Built`, `FreshIn`, `tyLvls`-WF or `Faithful` is a
field of `TrIndDeclN`. They live on the *other* side of the nested story — `VInductDecl'.Built`
is its own 9-field structure (`Theory/Inductive/NestedBuild.lean:765`), `FreshIn` is
`CSubst.FreshIn` (`Theory/Typing/ConstSubst.lean:327`), `Faithful` is `VIndRestore.Faithful`
(`Theory/Inductive/Restore.lean:804`). So a round that had gone looking for them among
`TrIndDeclN`'s fields would have found nothing and could easily have concluded the fields were
missing. Field-by-field:

* **`FreshIn` — the brief's own pointer was RIGHT, and the work IS already done.**
  `Lean4Lean.VIndRestore.csubstTy_freshIn` (`Theory/Inductive/TeleMove2.lean:96`), **arity 6,
  cone 1093, hole false, sorryAx false, none of 6 watched** — `(R.csubstTy D K).FreshIn env`
  from `env.addIndTypes D = some E₁` alone. One caveat the brief did not state: this is
  `csubstTy`, whose domain is only the companion *type* names. The full `csubst` version
  (`VIndRestore.csubst_freshIn`, `Theory/Inductive/NestedRules.lean` §9) needs all three staging
  successes, and `(R.csubstTy D K).FreshIn env₃` is outright **false** whenever `K` names a
  member of `D`, because `env₃` declares precisely the names it substitutes. So "FreshIn from
  type-staging success alone" is true of the `csubstTy` half and only at the pre-block
  environment.
* **`Faithful` — NOT `RestoreFaithful.lean`'s.** `RestoreFaithful.lean` mentions the string
  `Faithful` three times and **concludes `VIndRestore.Faithful` nowhere**;
  `shape.lean HEADS="VIndRestore.Faithful"` finds 35 constants, spread over 16 modules, and
  `Verify/Inductive/RestoreFaithful` is **not one of them**. The general producer is
  `Lean4Lean.VInductDecl'.Built.toFaithful` (`Theory/Inductive/NestedBuild.lean:1166`,
  **arity 6, cone 2340**, hole false, sorryAx false, none of 6). So `Faithful` is *`Built`'s*
  business, not `RestoreFaithful.lean`'s. What `RestoreFaithful.lean` actually owns is the
  acceptance gate, and it discharges two `RestoreData` fields from it:
  `Lean4Lean.ElimNestedInductive.Result.ownName_of_gate` (**arity 14, cone 5796**) and
  `ownCtor_of_gate` (**arity 16, cone 5796**), both clean on both lines.
* **`Built`** — partly `RestoreData`'s: `NestedRestoreWit.lean` §6 states four of `Built`'s nine
  clauses are discharged by `RestoreData`. It is a structure in its own right, not a field.
* **`tyLvls`-WF** — not `RestoreData`'s at all. `Built.tyLvls` is a field of `Built`; the
  well-formedness form `∀ l ∈ R.tyLvls j, l.WF D.uvars` is carried as an explicit hypothesis in
  `RestrictCompanion.lean` (3 sites) and `ValRestGeneral.lean` (3 sites), and the only instance
  in the tree is block-specific: `Lean4Lean.InductiveDeclExamples.ntreeAux_tyLvls_wf`
  (`Verify/Inductive/ValAtParam.lean:90`, **arity 6, cone 755**, clean on both lines).

Net: **one of four attributions correct** (`FreshIn`, with a caveat), one wrong on the module
(`Faithful`), one wrong on the owner (`tyLvls`-WF), one half-right (`Built`); and all four
misplaced as "fields of `TrIndDeclN`".

### 2.4 (a-continued) What would close the three open fields

`trCtorsLen` and the pointwise half of the constructor story share a single cause:
`RestoreData.ctor` is *existential* —

    ctor : … → ∀ C ∈ T.ctors, ∃ c ∈ t.ctors, c.name = C.name

— so it gives neither a length equation nor an index-wise correspondence. A **pointwise**
strengthening, `∀ q C, T.ctors[q]? = some C → ∃ c, t.ctors[q]? = some c ∧ c.name = C.name`, plus
the converse length bound, would discharge `trCtorsLen` outright and is the single named lemma
that field is waiting on. `trType` and `trCtors` are irreducibly `TrExprS` obligations: they are
where the surface `Lean.Expr` meets the abstract term language, and no name-level structure can
supply them. The pattern that does supply them at a concrete block is `FlipConstruct.lean`'s
`trS_tac` bridges, which is exactly what §3 uses.

### 2.5 (d) THE ARITY-0 WITNESS — vacuity discharged

`Lean4Lean.InductiveDeclExamples.ntreeAux_trIndDeclN`, **arity 0**, cone 5958, hole false,
sorryAx false, **none of 6 watched declarations in cone**:

    ∃ env₁ : VEnv, VEnv.empty.addInduct' listDecl = some env₁ ∧
      ntreeAux.uvars = 1 ∧ ntreeAux.params = [.sort (.succ (.param 0))] ∧
      TrIndDeclN env₁ [`u] 1 [ntreeIndType] false 1 ntreeAux ntreeK ntreeRestore

so every hypothesis of `trIndDeclN_of_ownId` is **jointly satisfiable at the parameterised
nested block**, and the producer is not vacuous.

**Degeneracy guard, machine-checked rather than asserted.** The two numeric conjuncts are inside
the statement, and `nfnAux_is_degenerate : nfnAux.uvars = 0 ∧ nfnAux.params = []` (arity 0, cone
48) is next to it, so a witness that drifted to `nfnAux` would fail them.

**Route audit — general theorems only.** Cone membership of `ntreeAux_trIndDeclN`, measured
directly over the compiled environment:

| probe | in cone |
|---|---|
| `Lean4Lean.NestedWit.trIndDeclN_wit` | **false** |
| `Lean4Lean.NestedWit.trIndDeclN_wit'` | **false** |
| `Lean4Lean.TrIndDecl.toN` | **false** |
| `Lean4Lean.trIndDeclN_of_ownId` | true |
| `Lean4Lean.VIndRestore.spineHargsN_of_head_indexFree` | true |
| `Lean4Lean.InductiveDeclExamples.tr_ntreeNodeType` | true |
| `Lean4Lean.InductiveDeclExamples.ntreeRestore_ownId` | true |
| `Lean4Lean.InductiveDeclExamples.ntreeAux_spineHargsN` | false (the concrete-spine route is unused) |
| `Lean4Lean.InductiveDeclExamples.ntreeAux_datum_at_stage₁` | false |

So P6 is refuted by measurement, not by assertion: the witness borrows nothing from the concrete
`nfnAux` witness. What it *does* use is block **data** — `ntreeRestore_ownId`,
`ntreeAux_companions`, `ntreeAux_restrictStepCfg`, `ntreeAux_argsTypedK_of_wf`,
`list_const₃`/`ntree_const₃`, and `FlipConstruct.lean`'s two `TrExprS` bridges — which is what
"configuration data, general route" means and is the same discipline `TrSpineProducer.lean` §3
follows.

**Where the open fields came from at the witness, since this is the interesting part.**
`trType` is `⟨rfl, tr_ntreeType⟩` and `tr_ntreeType` takes **no hypotheses at all**; `trCtors`
is `⟨rfl, tr_ntreeNodeType (list_const₃ h h₃) (ntree_const₃ h₃)⟩`; `trCtorsLen` is `rfl`. So the
three open fields are open *in general*, not at this block — which is the strongest form the
non-vacuity claim can take.

### 2.6 Scorecard for my own Q1-Q8

| # | Prediction | Conf. | Verdict |
|---|---|---|---|
| Q1 | structure with 6-10 fields | 70% | **FALSE** (12) |
| Q2 | ≥1 of the four "open" already general | 65% | **TRUE** (`FreshIn`, via `csubstTy_freshIn`) |
| Q3 | ≥1 of this round's two figures wrong | 75% | **FALSE** (both exact) |
| Q4 | `csubstTy_freshIn` gives `FreshIn` from type-staging alone | 55% | **TRUE**, with the `csubstTy`-only caveat |
| Q5 | producer arity in 18-28 | 60% | **TRUE** (21) |
| Q6 | witness achievable without `trIndDeclN_wit` | 30% | **TRUE** — my worst-calibrated call, and the round's best result |
| Q7 | census 13 / NOT BUILT 0 | 90% | **TRUE** |
| Q8 | ≥1 `TrIndDeclN` field the brief never mentions | 60% | **TRUE** (the brief named none of the 12; `ctorName_own`, `recName_own`, `recName_aux`, `companions`, `trCtorsLen` all unmentioned) |

**6 of 8.** Q6 at 30% is the one to learn from: I priced "the witness needs the concrete
witness" at 70% on the predecessor's reasoning, and the truth was that `FlipConstruct.lean` had
already built the two `TrExprS` bridges the witness needs. Both the predecessor and I mispriced
in the same direction — assuming a gap where a hours-old file had already closed it — which is
the failure mode `shape.lean`'s docstring was written about, and neither of us ran `shape.lean`
on `TrIndType` before predicting.

### 2.7 (e) Round-close numbers

* whole-tree `lake build`: **Build completed successfully (1626 jobs)**, green.
* `scripts/sorry-census-all.lean`: **BUILT: 443; in population but NOT BUILT: 0**;
  **HOLES over the whole built population, unioned across both passes: 13**.
* guard 1: `Axioms.lean declares exactly the 24 frozen axioms ✓`
* guard 2: `kernel_sound axioms within whitelist ✓ (proof INCOMPLETE: sorryAx present)`
* guard 3: `checker cone implementation gaps within frozen list (2/2 remaining) ✓`
* in-repo section-variable warnings: **0**. The only "automatically included section variable(s)
  unused" warning in the whole build is `Foundation/FirstOrder/SetTheory/Z.lean:35`, in the
  pinned dependency, not this repo.
* axiom bar `after ⊆ before`: every new declaration reports `cone reaches sorryAx: false` and
  `watched declarations in cone: none of 6`; guard 1's count is unchanged at 24.
* frozen files untouched: `git status` shows no modification to `Verify/Soundness.lean`,
  `Verify/Axioms.lean`, `Verify/Guard.lean`. I own and changed exactly
  `Verify/Inductive/TrIndDeclNProducer.lean` (new) and this file (new).
