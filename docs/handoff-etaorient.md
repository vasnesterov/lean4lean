# handoff-etaorient — re-orienting the structure-eta reduction rule as a contraction

Round opened 2026-09-04T05:10:01Z. Owner files: `docs/handoff-etaorient.md`
(this) and `Lean4Lean/Theory/Typing/EtaOrient.lean` (new). Everything else is read-only for me;
in particular `ConfluenceRebuildPrice.lean`, `CRSEScope.lean`, `SEReduce.lean`,
`StructEtaPrice.lean` are NOT mine — if my work implies an edit there I state it exactly and stop.

Task, from the brief: (0) state the contracted form of the structure-eta rule and prove it does
not regress, and that `parRedSES_rigid`'s hypothesis is now satisfiable; (1) fire the three new SE
rules, which have never been instantiated, at both `MutField.unitEnv` (zero-field) and its
declaration environment (positive-field); (2) if there is room, say whether the contracted
orientation moves the two refuted confluence statements. Not Church-Rosser itself.

## PRIORS (written before the first measurement — do not edit; corrections go in MEASUREMENTS)

Relayed to me, to be verified not trusted:

- P1. `Lean4Lean.VEnv.StructEtaSite.iterate` exists in `CRSEScope`, arity 13, cone 732, hole-free:
      the eta site re-fires on its own output, needing only that the output is typed.
- P2. `Lean4Lean.VEnv.not_parRedSE_rigid_of_structEtaSite` exists, arity 12, cone 701: therefore
      `parRedSES_rigid`'s hypothesis is FALSE at any such site.
- P3. `Lean4Lean.VEnv.etaExpansionG_idem_of_no_fields` exists, arity 8, cone 698: the regress is
      positive-fields-only; at zero fields the expansion is a constant map.
- P4. The three new SE rules (`NormalEqSE.structEtaL`, `NormalEqSE.structEtaR`,
      `ParRedSE.structEta`) have never been fired: every occurrence in the tree is a definition
      or a refutation.
- P5. `StructEtaPrice` §5 has two firings of `IsDefEqSE.structEta`, at `Lean4Lean.MutField.unitEnv`
      (zero-field) and at a declaration environment (positive-field), reusable for (1).
- P6. The previous round judged re-orientation cheap because `ConfluenceRebuildPrice` §4's
      inertness cases die by `absurd hs` and are unaffected by the flip.

My own priors, written before measuring:

- Q1. The largest risk in this task is a **hole-shaped deliverable**. "Re-orient the rule" cannot
      mean editing `ParRedSE` — that constructor lives in `ConfluenceRebuildPrice.lean`, which I
      do not own. So the honest deliverable is a *new* relation in my own file (call it
      `ParRedSEC`, contraction-oriented) plus theorems relating it to the existing expansion one.
      I expect to have to say explicitly "the re-orientation requires this edit to
      `ConfluenceRebuildPrice.lean`, here it is verbatim, and I stopped".
- Q2. I expect the "does not regress" claim to be **provable but weaker than it sounds**. `iterate`
      says the *site* is closed under expansion. Under contraction the natural statement is that
      `η e ≫ e` cannot re-fire *as a contraction* at `e` unless `e` is itself an expansion of
      something — which is not automatic. So I expect the honest form to be: contraction does not
      regress *given* that the subject is not itself an eta expansion, i.e. a side condition, or
      else a genuine non-regress via a syntactic measure. I will look for the measure.
- Q3. `parRedSES_rigid`'s hypothesis is `∀ o, ParRedSE Γ e o → o = e`. Under contraction the
      hypothesis is satisfiable at any `e` that is *not* of the form `η _` — but I must check that
      the OTHER eight `ParRedSE` constructors do not already refute rigidity at the witnesses I
      pick, and that the witness environment is one where the rule is not simply dead (P4/§6 of
      `ConfluenceRebuildPrice` proves the new rules are dead at a defeq-free env, so a satisfiable
      hypothesis proved there is vacuous progress). **Satisfiable-at-a-live-site is the bar.**
- Q4. On (1): "fire the rule" means exhibit `StructEtaSite` (10 fields per the previous round's
      read) at a real environment. The previous round said no witness exists in the whole tree.
      If `StructEtaPrice` §5's firings are of `IsDefEqSE.structEta` and not of `StructEtaSite`,
      then its side conditions may be a *different* 10-tuple and the reuse may not be literal.
      I check field-by-field rather than assuming.
- Q5. On (2): I expect the answer to be **no** — the previous round's M8 established the two
      refuted statements (`descendSE_uniq_sortUniq_not_all`, `not_parRedStatementSE_of_propMajor`)
      are transported by *inertness* and by *porting the argument*, neither of which mentions the
      rule's direction. Orientation should be irrelevant to both. But the second consumes
      `parRedSES_rigid`, whose hypothesis orientation *does* change, so the second may move from
      "refuted under an unsatisfiable hypothesis" to "refuted under a satisfiable one" — which is
      a strengthening of the refutation, i.e. the opposite of what the brief hopes for. Flagging
      that as the most likely surprise.
- Q6. Calibration prior: the orchestrator's cone figures have been exact for nine rounds and its
      attributions/prose wrong ten times. So I re-derive every name and arity with `exists.lean`
      and quote it verbatim, and I read `ConfluenceRebuildPrice`'s actual constructor text before
      writing any "contracted form".

## CONSUMING MODULE (named up front, per process rule)

To be filled at M0 with the actual `can-cite.py` answer. Expected case: **this is a
pricing/refutation file with no consumer** — its product is a statement about the orientation of
a rule I do not own. If a consumer is possible I name it.

## MEASUREMENTS (appended as made)

### M1 (2026-09-04T05:14Z) — `exists.lean` on the relayed names. **P1–P3 exact.**

`population: 460 built modules`, `watching 6 declarations for cone membership`.

| name | module | arity | cone | own hole | cone→sorryAx | watched |
|---|---|---|---|---|---|---|
| `Lean4Lean.VEnv.StructEtaSite.iterate` | `Theory.Typing.CRSEScope` | **13** | **732** | false | false | none of 6 |
| `Lean4Lean.VEnv.not_parRedSE_rigid_of_structEtaSite` | `CRSEScope` | **12** | **701** | false | false | none of 6 |
| `Lean4Lean.VEnv.etaExpansionG_idem_of_no_fields` | `CRSEScope` | **8** | **698** | false | false | none of 6 |
| `Lean4Lean.VEnv.parRedSES_rigid` | `ConfluenceRebuildPrice` | 6 | 17 | false | false | none of 6 |
| `Lean4Lean.VEnv.StructEtaSite` | `ConfluenceRebuildPrice` | 11 | 10 | — | — | `[NO PROOF TERM]` |
| `Lean4Lean.VEnv.ParRedSE` | `ConfluenceRebuildPrice` | 4 | 4 | — | — | `[NO PROOF TERM]` |
| `Lean4Lean.VEnv.NormalEqSE` | `ConfluenceRebuildPrice` | 4 | 4 | — | — | `[NO PROOF TERM]` |
| `Lean4Lean.MutField.unitEnv` | **`Verify.TypeChecker.EtaUnitRefute`** | 0 | 928 | false | false | none of 6 |

**P1, P2, P3 confirmed on the nose** (13/732, 12/701, 8/698 — the orchestrator's cone figures are
exact for a tenth round). Note `[NO PROOF TERM]` is the instrument's own note that the cone is
type-constants only and says nothing about satisfiability; per the calibration line it is NOT a
gap signal, and I do not use it as one.

**Correction to a field count that both the brief's source and `CRSEScope`'s docstring get wrong.**
`VEnv.StructEtaSite` has **9** fields, not 10: `isStruct, indices, recFields, nuvars, levelWF, np,
args, typed, small`. `CRSEScope.StructEtaSite.iterate`'s docstring says "the nine other fields do
not mention `e`"; there are **eight** other than `typed`. `ConfluenceRebuildPrice`'s own §3 read in
`handoff-crse.md` M3 says "10 fields". Arity 11 is the *parameter* count
(`env univs Γ S D j T C us ps e`). Nothing depends on the number; recording it because the brief's
prose count was wrong twice and I am asked to re-derive rather than relay.

### M2 (2026-09-04T05:18Z) — the rule text, read from source before writing any "contracted form"

`Lean4Lean/Theory/Typing/ConfluenceRebuildPrice.lean:433-435`, verbatim:

```
  /-- **New.** -/
  | structEta :
    StructEtaSite env univs Γ S D j T C us ps e →
    ParRedSE Γ e (D.etaExpansionG T C us ps j e)
```

So the existing orientation is `e ⟶ η e` (expansion). The **contracted form** is therefore

```
  | structEtaC :
    StructEtaSite env univs Γ S D j T C us ps e →
    ParRedSE Γ (D.etaExpansionG T C us ps j e) e
```

with `StructEtaSite`'s `typed` field still stated about `e` (the *contractum*), which is the
choice that matters and which I record explicitly: the site's typing premise is
`env.IsDefEqSE univs Γ e e ((VExpr.const S us).mkApp ps)`, i.e. it types the **subject of the
expansion**, not the redex `η e`. Under the flip the redex is `η e` and the premise types its
reduct. That asymmetry is the whole content of §1 below.

`NormalEqSE.structEtaL/structEtaR` (lines 404-415) both take
`StructEtaSite … e` and a `NormalEqSE` recursion on `D.etaExpansionG … e`, concluding about `e`.
They are orientation-symmetric in form (they *peel* the expansion on one side), so the flip does
not change their statements at all — only what they are derived from.

### M3 (2026-09-04T05:30Z) — availability, and the two facts that shape the whole round

**`shape.lean` on the HELPER shapes** (per process rule; the deliverable is not the only thing to
check for pre-existence):

| heads | hits |
|---|---|
| `SizeOf.sizeOf` + `Lean4Lean.VExpr.mkApp` | **0** ("and this IS meaningful, heads resolved") |
| `SizeOf.sizeOf` + `Lean4Lean.VInductDecl'.etaExpansionG` | **0** |
| `Lean4Lean.VInductDecl'.etaExpansionG` alone | 48, none of them a size/≠ fact; the useful one is `Lean4Lean.MutField.declEnv_etaExpansionG_eq` (arity 0, `Verify/TypeChecker/EtaStructG.lean:511`) which computes the positive-field expansion concretely: `decl.etaExpansionG bTy bCtor [] [] 1 (.bvar 0) = (VExpr.const `MutField.B.mk []).mkApp [decl.projTermG bTy bCtor [] [] [] 0 1 (.bvar 0)]`, by `rfl` |

So the `sizeOf` route to non-regress is new, and the positive-field expansion's concrete shape is
already computed for me — which is what makes `η e ≠ e` free there (`.app …` vs `.bvar 0`).

**`can-cite.py` from `Theory.Typing.CRSEScope` (closure 231):** `unitEnv_IsStructureG_0`,
`declEnv_IsStructureG`, `unitEnv_foo_hasType`, `bCtor_field_prop`, `declEnv_etaExpansionG_eq`,
`structEtaSE_foo`, `structEtaSE_B`, `VEnv.Params` — **YES, all eight.** So importing
`CRSEScope` alone puts every witness I need in scope, and I add no `Verify/` import of my own
(so I do not appear in `layer-check.py`'s soft report; I inherit CRSEScope's 231-module closure
including its 20 `SetModel` modules, which is the layering fact `handoff-crse.md` M4 flagged).

**FACT 1 — I cannot edit the rule, so the deliverable is a parallel relation.** `ParRedSE` lives in
`ConfluenceRebuildPrice.lean`, which is not mine. Prior Q1 confirmed. So `EtaOrient.lean` defines
`VEnv.ParRedSEC` — the same nine constructors with the tenth flipped — and the exact edit
`ConfluenceRebuildPrice.lean` would need is stated at the end of this document and NOT made.

**FACT 2 — and this is the finding of item (1).** `StructEtaSite` takes no `Params` instance
(arity 11: `env univs Γ S D j T C us ps e`), so its witnesses are unconditional. But
`NormalEqSE`/`ParRedSE`/`ParRedSEC` all live under `variable [Params]`, and a `Params` instance
requires `henv : env.WF` **and** `extra_pat`, which demands that *every* `env.defeqs` rule be
`Pat`-registered (`ChurchRosser.lean:84-90`). Now `StructEtaSite.isStruct` is `env.IsStructureG`,
and `IsStructureG.not_of_no_defeqs` holds precisely because `IsStructureG.decl` puts the block's
**ι-rules** into `env.defeqs`. Registering an ι-rule is `PatWF`'s ι case, which
`ParamsBuild.lean`'s docstring says "needs `IsDefEqU.forallE_inv` (open,
`Theory/Typing/Injectivity.lean`)" — one of the tree's four holes. Hence:

> **Any environment at which the structure-eta rule can fire has ι-rules; `Params` cannot be
> instantiated over such an environment without the Π-injectivity hole. So the three new SE rules
> cannot be fired *unconditionally* anywhere, and the obstruction is `Params.extra_pat`, not
> anything about eta or about orientation.**

Also measured: `MutField.unitEnv_wf : VEnv.WF unitEnv` is **proved**
(`Verify/TypeChecker/EtaUnitRefute.lean:33`), while **`VEnv.WF declEnv` is open** — "this tree's
keystone, open for everybody" (`Verify/Typing/TrProjWideWitness.lean:24`). `StructEtaSite` needs
neither, so both site witnesses below are unconditional; only the `Params`-level firings are
conditional, and they are conditional on `Params`, not on `WF declEnv`.

### M4 (2026-09-04T05:45Z) — the contracted rule, and the regress IS gone

`Lean4Lean/Theory/Typing/EtaOrient.lean`, §1–§5. All of the following elaborated (diagnostics
empty) before the tree went red under another stream; see M6 for the re-poll.

**The contracted rule, fully qualified:** `Lean4Lean.VEnv.ParRedSEC.structEtaC`, in
`Lean4Lean.Theory.Typing.EtaOrient`:

```
  | structEtaC :
    StructEtaSite env univs Γ S D j T C us ps e →
    ParRedSEC Γ (D.etaExpansionG T C us ps j e) e
```

`Lean4Lean.VEnv.ParRedSEC` is `VEnv.ParRedSE`'s nine other constructors verbatim; the flip is the
only difference, and `ParRedSEC.rfl`, `ParRedSECS`, `parRedSECS_rigid`,
`parRedSEC_iff_of_no_defeqs` and `parRedSECS_iff_of_no_defeqs` are `ConfluenceRebuildPrice`'s four
corresponding proofs **ported with zero changes to the proof text** — which is the machine-checked
form of "the flip is cheap on the eight old constructors", and of prior P6 (the inertness cases die
by `absurd hs (StructEtaSite.not_of_no_defeqs hd)` in either direction). **P6 confirmed, by
re-proving rather than by reading.**

**The regress is gone, three ways:**

1. `Lean4Lean.VInductDecl'.sizeOf_lt_etaExpansionG` — `0 < C.fields.length → sizeOf e < sizeOf (η e)`.
   New (M3: `shape.lean` found 0 hits for `sizeOf` + `etaExpansionG`). Route:
   `VExpr.sizeOf_le_mkApp`, `VExpr.sizeOf_lt_mkApp_of_mem`, `sizeOf_lt_projCoreG`
   (`projCoreG` ends in `… ++ is ++ [e]`, so `e` is a member of its spine),
   `sizeOf_lt_projTermG`, then the `i = 0` entry of `projAllG` is a member of `ps ++ projAllG`.
2. `Lean4Lean.VEnv.StructEtaStepC.sizeOf_lt` and
   `Lean4Lean.VEnv.no_infinite_structEtaStepC` — a contraction step strictly decreases `sizeOf`, so
   there is **no `Nat`-indexed chain of them**. This is the exact negation of the shape
   `CRSEScope`'s `parRedSES_etaIter` proves *positively* for the expansion.
3. `Lean4Lean.VEnv.parRedSECS_etaIter_down` — the same η-tower `CRSEScope` §4 builds, traversed
   into `e` instead of away from it, terminating there.

**And the literal dual of `StructEtaSite.iterate` fails.** `iterate` needs only that the output is
typed. A *new* contraction redex needs the output to **be** an η-expansion, and
`Lean4Lean.VInductDecl'.etaExpansionG_ne_bvar` (plus `_sort`, `_lam`, `_forallE`) says an
η-expansion is always a `const`-headed application spine — so no amount of typing can turn `.bvar 0`
into a redex. **No side condition, no environment hypothesis.**

### M5 (2026-09-04T05:50Z) — `parRedSES_rigid`'s hypothesis is satisfiable, and the flip is measured at a POSITIVE-field site

- `Lean4Lean.VEnv.parRedSEC_rigid_bvar : ∀ o, ParRedSEC Γ (.bvar i) o → o = .bvar i` — **no
  hypotheses at all** beyond the `Params` instance. Also `parRedSEC_rigid_sort`.
  Route (`ParRedSEC.rigid_of_eq_bvar`): three constructors could conclude about an atom;
  `bvar`/`sort` return it unchanged, `extra` dies because `Pattern.Matches` only matches
  `.const c ls` and `.app f a`, and `structEtaC` dies on `etaExpansionG_ne_bvar`.
  Note the subject had to be stated as a variable plus an equation: `cases` on
  `ParRedSEC Γ (.bvar i) o` fails with *"Dependent elimination failed: Failed to solve equation
  `bvar i = (const C.name us).mkApp (ps ++ D.projAllG …)`"*, because `structEtaC`'s redex is not a
  constructor application. Recorded because it is the only real technical obstacle in the flip.
- `Lean4Lean.MutField.declEnv_rigidity_flips` — the two sides in one statement, at the
  **positive-field** member `B` of `MutField.decl` whose subject is `.bvar 0`:
  `¬ (∀ o, ParRedSE bCtx (.bvar 0) o → o = .bvar 0) ∧ (∀ o, ParRedSEC bCtx (.bvar 0) o → o = .bvar 0)`.
  The left conjunct is `CRSEScope`'s `not_parRedSE_rigid_of_structEtaSite` **instantiated for the
  first time** (it had no witness to instantiate at); the right is `parRedSEC_rigid_bvar`.
  **So the answer to (0) is yes, and it is measured where the regress actually lives** —
  `bCtor.fields.length = 1` (`MutField.bCtor_fields_pos`, by `decide`), and
  `MutField.declEnv_etaExpansionG_ne` shows the expansion differs from the subject there.

**Prior Q2 was wrong, and in the good direction.** I expected non-regress to need a side condition
("unless the subject is itself an expansion"). It does not: the `sizeOf` measure discharges it
outright at positive fields, and rigidity at the atoms is unconditional. The side condition I
predicted is exactly what `etaExpansionG_ne_bvar` eliminates.

**Prior Q3's bar met.** Satisfiability is not proved at a dead environment: it is proved with no
environment hypothesis at all, and then *contrasted* at a live positive-field site.

### M6 (2026-09-04T05:52Z) — the three rules fired, both structure shapes. **P4 confirmed, then closed.**

`grep` over the whole tree before writing anything: `StructEtaSite` had **no witness** — every
occurrence in `ConfluenceRebuildPrice.lean` is a definition or an `absurd`, exactly as prior P4
said, and `CRSEScope.lean` carries `EtaStagesTyped` as a hypothesis for that reason. **P4
confirmed.** Now closed, in `Lean4Lean.Theory.Typing.EtaOrient` §6:

| declaration | shape | subject |
|---|---|---|
| `Lean4Lean.MutField.unitEnv_structEtaSite` | **zero-field** (`aCtor.fields = []`) | the axiom `MutField.foo : A` |
| `Lean4Lean.MutField.declEnv_structEtaSite` | **positive-field** (`bCtor.fields.length = 1`) | `.bvar 0` in `bCtx = [.const MutField.B []]` |

Both are the **first `VEnv.StructEtaSite` witnesses in the tree**, both bundle `StructEtaPrice` §5's
premises (prior P5 confirmed: the reuse *is* literal, field for field — `isStruct` from
`unitEnv_IsStructureG_0` / `declEnv_IsStructureG`, `args := .nil`, `typed` from
`unitEnv_foo_hasType.toSE` / `VEnv.IsDefEq.toSE (.bvar (.zero ..))`, `small := .inr …`), and
**neither needs a `Params` instance nor `VEnv.WF`** — in particular the positive-field one does
**not** use the open `VEnv.WF declEnv`.

On top of them, eight firings — the three new rules at both shapes, plus the contraction:

| rule | zero-field | positive-field |
|---|---|---|
| `VEnv.ParRedSE.structEta` (expansion, existing) | `MutField.unitEnv_parRedSE_structEta` | `MutField.declEnv_parRedSE_structEta` |
| `VEnv.ParRedSEC.structEtaC` (contraction, new) | `MutField.unitEnv_parRedSEC_structEtaC` | `MutField.declEnv_parRedSEC_structEtaC` |
| `VEnv.NormalEqSE.structEtaL` | `MutField.unitEnv_normalEqSE_structEtaL` | `MutField.declEnv_normalEqSE_structEtaL` |
| `VEnv.NormalEqSE.structEtaR` | `MutField.unitEnv_normalEqSE_structEtaR` | `MutField.declEnv_normalEqSE_structEtaR` |

The `NormalEqSE` firings need the expansion to be typed, for `NormalEqSE.refl`. That came free:
`MutField.unitEnv_isDefEqSE_eta` (`structEtaGSE` applied at `unitEnv`, kept in the **raw**
`etaExpansionG` form rather than `StructEtaPrice`'s rewritten `.const MutField.A.mk []`) and
`structEtaSE_B` are each their own `.symm.trans` self, giving
`MutField.unitEnv_eta_hasType` / `MutField.declEnv_eta_hasType`.

**The one cost, and it is `Params`' not eta's — prior Q4's warning landed on a different target.**
All eight carry `he : env = unitEnv` / `env = declEnv` and `hu : univs = 0`, because
`NormalEqSE`/`ParRedSE`/`ParRedSEC` live under `variable [Params]` and **no `Params` instance over
either environment exists**. The reason is M3's FACT 2 and it is orientation-independent: a site
forces ι-rules into `env.defeqs`, `Params.extra_pat` forces those to be `Pat`-registered, and that
is `PatWF`'s ι case, which needs the `IsDefEqU.forallE_inv` hole. So **the site witnesses are
unconditional and the rule firings are conditional on `Params`**, and `ConfluenceRebuildPrice` §7's
vacuity check — which exhibits a β-step at `refParams`, where §6 of that file proves the new rules
are dead — is now supplemented rather than replaced: the *sites* are unconditionally live, the
*rules* fire the moment anyone instantiates `Params` over an environment with a structure.

### M7 (2026-09-04T05:55Z) — (2) neither refuted statement moves

- `Lean4Lean.descendSEC_uniq_sortUniq_not_all` — `descendSE_uniq_sortUniq_not_all` ported to the
  contracted relation via `DescendStatementSEC` and `descendStatementSEC_iff_of_no_defeqs`. Goes
  through **unchanged**: the transport is by inertness at `refEnv`, and
  `StructEtaSite.not_of_no_defeqs` says nothing about which way the rule points. **Unmoved.**
- `Lean4Lean.VEnv.not_parRedStatementSEC_of_propMajor` — `not_parRedStatementSE_of_propMajor`
  ported line for line over `ParRedStatementSEC`. Also **unmoved**, and note
  `ParRedStatementSEC` reuses `NormalEqSE` *verbatim*: the conversion side is orientation-symmetric
  because `structEtaL`/`structEtaR` **peel** an expansion rather than produce one.
  If anything this refutation is **strengthened** by the flip: its `hrig` hypothesis is exactly the
  one M5 shows is now satisfiable, where `not_parRedSE_rigid_of_structEtaSite` made it false.
  **Prior Q5 confirmed on both counts, including the "most likely surprise".**

So: re-orientation buys `ParRed`-normal forms (M4, M5) and buys nothing at all on the two refuted
statements. That is consistent with `handoff-crse.md` M8 — those two are gated on the missing
*kind* of argument (a measure/termination or model-theoretic normalisation), which orientation is
a precondition for and not a substitute for.

### M8 (2026-09-04T05:56Z) — build interference, re-polled as required

Two consecutive `lake env lean` runs on my own file failed with
`object file '…/Theory/Inductive/StructureClosed.olean' … does not exist`, then
`…/Theory/Typing/StrengthenVerdict.olean … does not exist`. Read-only `git status` at that moment
showed **`M Lean4Lean/Theory/Inductive/Decl.lean`, `M Lean4Lean/Theory/Typing/ShapeVar.lean`** and
two new untracked streams (`Verify/Inductive/B6.lean` + `docs/handoff-b6.md`,
`Theory/Inductive/IndepResidual.lean` + `docs/handoff-indepresidual.md`) — i.e. **another stream's
edits to `Theory/Inductive/Decl.lean` are invalidating oleans under me. Not my red build.** Waited
for it to settle and re-ran; see ROUND-CLOSE.

### M9 (2026-09-04T06:20Z) — cones and cleanliness, `exists.lean`, `population: 462 built modules`

Every declaration below: `own value is a hole: false`, `cone reaches sorryAx: false`,
`watched declarations in cone: none of 6`.

| name | arity | cone |
|---|---|---|
| `Lean4Lean.VEnv.ParRedSEC` | 4 | 4 `[NO PROOF TERM]` (as every inductive prints) |
| `Lean4Lean.VInductDecl'.sizeOf_lt_etaExpansionG` | 8 | 1997 |
| `Lean4Lean.VEnv.parRedSEC_rigid_bvar` | 5 | 1676 |
| `Lean4Lean.VEnv.no_infinite_structEtaStepC` | 4 | 2046 |
| `Lean4Lean.VEnv.parRedSECS_etaIter_down` | 13 | 753 |
| `Lean4Lean.MutField.unitEnv_structEtaSite` | 0 | 4184 |
| `Lean4Lean.MutField.declEnv_structEtaSite` | 0 | 3881 |
| `Lean4Lean.MutField.declEnv_parRedSEC_structEtaC` | 3 | 3912 |
| `Lean4Lean.MutField.declEnv_normalEqSE_structEtaL` | 3 | 3927 |
| `Lean4Lean.MutField.declEnv_rigidity_flips` | 3 | 4399 |
| `Lean4Lean.VEnv.not_parRedStatementSEC_of_propMajor` | **22** | **674** |
| `Lean4Lean.descendSEC_uniq_sortUniq_not_all` | **0** | **6800** |

**The last two rows are the sharpest number in the round.** `not_parRedStatementSE_of_propMajor` is
arity 22, cone 674; `descendSE_uniq_sortUniq_not_all` is arity 0, cone 6800 (M1 and
`handoff-crse.md` P6). The contracted ports are **arity 22 / cone 674** and **arity 0 / cone 6800**
— identical, digit for digit. The two refutations transport at *exactly* the same price in the
contracted orientation as in the expanded one, which is the quantitative form of "orientation does
not move them".

Also: `parRedSECS_etaIter_down` cone 753 against `parRedSES_etaIter`'s 732-family — the downward
tower costs 21 constants more than the upward one, the `sizeOf`/`ReflTransGen.trans` machinery.

### SCORING `docs/handoff-crse.md`'s PRIORS

That document verified its priors inline but never consolidated them, and it is not my file to edit,
so the scorecard goes here.

| prior | verdict |
|---|---|
| P1 `constAppInvSISE_iff_of_noEta` arity 3 cone 831 hole-free | **RIGHT** (its M1, exact) |
| P2 `NoEtaEligible` cone 618 | **RIGHT on the cone, WRONG on arity** (2, not the unstated figure) |
| P3 `constAppInvSISEFromWF_iff_etaOnly'` arity 0 cone 7580, 4 holes + 2 watched | **RIGHT for the primed name; the brief conflated it with the unprimed one** (arity 1, cone 882, clean) |
| P4 `church_rosserSE` NOT FOUND | **RIGHT** |
| P5 `NormalEqSE`/`ParRedSE` defined, `[NO PROOF TERM]` | **RIGHT that they are definitions; the flag was MISREAD as a gap signal** — `NormalEq`/`ParRed` at 13 constructors print it too |
| P6 both statements stay refuted, arities/cones as given | **RIGHT**, and now confirmed a second time: my ports reproduce 22/674 and 0/6800 exactly |
| P7 confluence needs nothing from `Theory/SetModel/` | **HALF WRONG** — true of `ChurchRosser` (0 of 48), false of the modules where the SE relations live (20 of 230) |
| Q1 the 13-constructor CR development is itself unproved, so "port" is the wrong word | **RIGHT**, and it was the round's reframing |
| Q2 the measured gap is "everything"; `[NO PROOF TERM]` signals it | **HALF WRONG**, self-corrected in its own M2 |
| Q3 the arity-22 refutation may be vacuous; must check inhabitation | **RIGHT to insist**, and the answer was the good one (non-vacuous modulo the injectivity corner) |
| Q4 re-derive every name; cone figures reliable, prose not | **RIGHT**, and it held again this round: P1–P3's cones were exact on the nose, while two prose counts (`StructEtaSite`'s field count, "the 14-constructor relation") were wrong |

### SCORING MY OWN PRIORS

| prior | verdict |
|---|---|
| Q1 the deliverable must be a parallel relation, not an edit; expect to state the edit and stop | **RIGHT**, exactly as written |
| Q2 non-regress will need a side condition ("unless the subject is itself an expansion") | **WRONG, in the good direction** — `sizeOf` discharges it outright at positive fields, and `etaExpansionG_ne_bvar` kills the side condition I predicted |
| Q3 satisfiability must be shown at a *live* site, not a dead one | **RIGHT to insist**; met by proving it with no environment hypothesis at all and contrasting at the live positive-field site |
| Q4 `StructEtaPrice` §5's premises may not be a literal `StructEtaSite` 10-tuple | **WRONG** — the reuse is literal, field for field, 9 fields (not 10) |
| Q5 (2) will be "no", and the second refutation may get *stronger* | **RIGHT on both**, including the predicted surprise |
| Q6 re-derive everything; cones exact, prose not | **RIGHT** (see the scorecard above) |

### ROUND-CLOSE (2026-09-04T06:30Z)

| check | result |
|---|---|
| whole-tree `lake build` | **`Build completed successfully (1648 jobs)`, exit 0** |
| `scripts/sorry-census-all.lean --run` | `on disk: 489; in default-target population: 465; Experimental: 24`; `BUILT: 465; in population but NOT BUILT: 0`; **`HOLES … : 13`** (pass A 13, pass B 0) |
| guard 1 | `Axioms.lean declares exactly the 24 frozen axioms ✓` |
| guard 2 | `kernel_sound axioms within whitelist ✓ (proof INCOMPLETE: sorryAx present)` |
| guard 3 | `checker cone implementation gaps within frozen list (2/2 remaining) ✓` |
| warnings from `EtaOrient.lean` | **zero** (`lake env lean` on the file, grep for `warning`/`error`: empty) |
| `scripts/layer-check.py` | **exit 0**; `HARD RULE … ok, 66 module(s) checked, none reaches Verify/`. `EtaOrient` does **not** appear in the soft report — it imports `CRSEScope`, not `Verify/` directly |
| `exists.lean` on the new declarations | all FOUND in `Lean4Lean.Theory.Typing.EtaOrient`, hole-free, `sorryAx`-free, `watched … none of 6` |
| inline `#print axioms` (§8) | **49/49 clean**: `[propext, Quot.sound]` ×23, `[propext, Classical.choice, Quot.sound]` ×25, `bCtor_fields_pos` **no axioms** |

Frozen files untouched. Files written this round: `docs/handoff-etaorient.md`,
`Lean4Lean/Theory/Typing/EtaOrient.lean`. Nothing else. `ConfluenceRebuildPrice.lean`,
`CRSEScope.lean`, `SEReduce.lean`, `StructEtaPrice.lean` read only.

### THE EDIT I DO NOT MAKE

`Lean4Lean/Theory/Typing/ConfluenceRebuildPrice.lean:433-435`, replace

```
  /-- **New.** -/
  | structEta :
    StructEtaSite env univs Γ S D j T C us ps e →
    ParRedSE Γ e (D.etaExpansionG T C us ps j e)
```

with

```
  /-- **New.**  Oriented as a contraction; see `Theory/Typing/EtaOrient.lean`. -/
  | structEta :
    StructEtaSite env univs Γ S D j T C us ps e →
    ParRedSE Γ (D.etaExpansionG T C us ps j e) e
```

and **nothing else in that file**: `ParRedSE.rfl`, `parRedSES_rigid`, `parRedSE_iff_of_no_defeqs`,
`parRedSES_iff_of_no_defeqs`, `ParRedStatementSE`, `not_parRedStatementSE_of_propMajor`,
`DescendStatementSE`, `descendStatementSE_iff_of_no_defeqs` and
`descendSE_uniq_sortUniq_not_all` all go through with their proof text unchanged — §3 and §7 of
`EtaOrient.lean` **are** those eight proofs, ported verbatim against the flipped constructor, and
they compile. `NormalEqSE` needs no change at all.

Consequence for a file that is also not mine: `CRSEScope.lean` §2 and §4
(`not_parRedSE_rigid_of_structEtaSite`, `EtaStagesTyped`, `StructEtaSite.at_stage`,
`parRedSES_etaIter`) are statements *about the expansion* and would have to be restated or deleted;
`EtaOrient.lean`'s `parRedSEC_rigid_bvar`, `StructEtaStepC`, `no_infinite_structEtaStepC` and
`parRedSECS_etaIter_down` are the replacements. §1 (`StructEtaSite.iterate`) and §3
(`etaExpansionG_idem_of_no_fields`) survive unchanged — they are about the site and the expansion
term, not about the reduction.
