# handoff: `ParamsStruct` — a `VEnv.Params` instance at a structure environment

Owner stream: `Lean4Lean/Theory/Typing/ParamsStruct.lean` + this file.  Nothing else edited.

## §1 PRIORS  (written before running any Lean tooling; NEVER edited afterwards)

### What I will verify rather than trust

The brief makes four load-bearing claims.  I trust none of them and will measure each:

1. **`Lean4Lean.VEnv.patWF_of_wf` exists at `Verify/Typing/ConstSpineWF.lean:57`, proves
   `env.PatWF U` from `env.WF` alone at an arbitrary environment, and carries only the
   `piInv` census hole.**  I will check the name with `scripts/exists.lean`, the statement
   with `scripts/shape.lean`, the hole cone with `scripts/hole-cone.lean` (or `exists.lean`'s
   axiom set), and citability with `scripts/can-cite.py`.
   *Prediction:* the name and location are right (I have already seen the source text at that
   line while grepping, before writing this).  I predict the hole cone is **larger than
   `forallE_inv` alone** — the file's own header table says `patWF` contributes
   `forallE_inv_stratified` and `piInv_axiom` contributes `forallE_inv`, so I expect **at
   least two** holes, not one.  So I predict the brief's "acceptance of the `piInv` census
   hole" is an *understatement* of the price by one hole.

2. **`VEnv.WF Lean4Lean.MutField.declEnv` is the missing piece / is the round's target.**
   *Prediction: this is already proved in the tree and the brief is wrong that it is open.*
   While locating the definitions by grep (before any Lean), I read
   `Lean4Lean/Verify/TypeChecker/EtaUnitRefute.lean:9`:
   `theorem declEnv_wf : VEnv.WF declEnv := ⟨[.induct decl], .decl (.induct decl_WF
   declEnv_eq.choose_spec) .empty⟩`, and `:33` `unitEnv_wf` likewise.  So I predict the
   answer to task 2 is **"provable outright, and already proved"**, that it is **not** blocked
   by the `AddInduct` flip (because `VEnv.empty.addInduct' decl = some e` holds by `rfl` —
   `declEnv_eq` is literally `⟨_, rfl⟩`, so no flip is needed at the empty environment), and
   that the whole of task 2 collapses to a citability question rather than a proof question.
   This will be the third consecutive round corrected on an absence claim if it holds.

3. **`paramsOfWF` (`Theory/Typing/ParamsBuild.lean:52`) needs only `env.WF`, `U`, and
   `PatWF env U`.**  *Prediction: true as read; it is `@[instance_reducible]`.*  So the
   instance is a two-line composition `paramsOfWF declEnv_wf U (patWF_of_wf declEnv_wf U)`
   and the entire round is a **layering** problem, not a mathematics problem.

4. **The eight `EtaOrient` firings needed a concrete-environment pin because no `Params`
   instance over a structure environment exists.**  *Prediction: the diagnosis is wrong.*
   If (2) and (3) hold, an instance exists; the pin was needed because `EtaOrient.lean` did
   not import the module holding `declEnv_wf`, or because the *witnesses* it fires are
   themselves about the concrete environment (`declEnv_IsStructureG` names `MutField.B`), in
   which case the pin can come off the `Params` argument but **not** off the witness — a
   general-environment restatement would need a general structure site, which is a different
   deliverable.  I predict this second horn: **the `Params` pin comes off, the witness pin
   does not.**

### Where I expect this to go hole-shaped or vacuous

- **Vacuity is the real risk, and it is not where the brief thinks.**  `EtaUnitRefute.lean`
  proves `MutField.unitEnv_not_structEtaG : ¬ unitEnv.StructEtaG` and
  `unitEnv_not_unitEta`.  So at `unitEnv` the structure-eta rule is **false**.  Any SE rule
  (`NormalEqSE`, `ParRedSE`, `ParRedSEC`) whose definition *assumes* structure eta will
  therefore be vacuous or refuted at `unitEnv`.  I predict: I will be able to build the
  `Params` instance, and firing an *SE* rule at it will hit the fact that the SE hypothesis
  is refutable there.  That is the honest headline risk: **the instance exists but the SE
  firing may be firing at an environment where the rule it is about is false.**  I will check
  which of the eight firings are SE-hypothesis-carrying.
- `Verify/Typing/ConstSpineWF.lean`'s own header records that
  `VEnv.not_crStatement_of_kstep` refutes `church_rosser`'s *statement* at any `Params`
  instance registering the ι-rule of a large-eliminating subsingleton.  `MutField.decl` has
  `isLE := false` and two ι-rules.  I predict this refutation does **not** apply at
  `declEnv`/`unitEnv` (no `Eq`, `isLE = false`), but I will check its hypotheses rather than
  assume, because if it does apply the instance is a *counterexample* rather than a witness.
- Layering: my file is under `Theory/`, so no direct `import Lean4Lean.Verify.*`.  I predict
  I must route through `Theory/Typing/StructEtaPrice.lean` or `CRSEScope.lean` to inherit
  `Verify`, and I predict `can-cite.py` will say `declEnv_wf` is **not** in their closure
  (it is in `Verify/TypeChecker/`, a late module), in which case the strongest thing I can
  build in a file I own is **conditional on `VEnv.WF env` at a general `env`** plus a
  *statement* of what the unconditional instance would be and exactly which import line the
  orchestrator must add.  I flag now that this is the likely shape of the deliverable.

### Predicted verdicts, one line each

- Instance at a positive-field structure environment: **exists**, price = 2 holes
  (`forallE_inv`, `forallE_inv_stratified`) + `VEnv.WF`, which is discharged.
- `VEnv.WF declEnv`: **already proved**, not flip-blocked.
- `VEnv.WF unitEnv`: **already proved**, not flip-blocked.
- Pin removal: partial — `Params` pin off, witness pin stays.
- Consumer: probably none yet; the honest answer is likely "no consumer, because the
  concrete-pin firings already typecheck and nothing asks for a general-`Params` form".

## §2 MEASUREMENTS (appended as made; §1 stands uncorrected above)

### M1 — `scripts/exists.lean`, twelve names, one run

| name | module | arity | cone | sorryAx? | holes |
|---|---|---|---|---|---|
| `Lean4Lean.VEnv.patWF_of_wf` | `Verify.Typing.ConstSpineWF` | 3 | 4062 | **yes** | `IsDefEqU.forallE_inv_stratified`, `VEnv.WF.rigidShapeUniqNS` |
| `Lean4Lean.MutField.declEnv_wf` | `Verify.TypeChecker.EtaUnitRefute` | 0 | 3840 | **no** | none |
| `Lean4Lean.MutField.unitEnv_wf` | `Verify.TypeChecker.EtaUnitRefute` | 0 | 3876 | **no** | none |
| `Lean4Lean.VEnv.paramsOfWF` | `Theory.Typing.ParamsBuild` | 4 | 6391 | **no** | none |
| `Lean4Lean.VEnv.PatWF` | `Theory.Typing.ParamsBuild` | 2 | 648 | no | none |
| `Lean4Lean.VEnv.patWF` | `Theory.Typing.PatWFIota` | 4 | 3929 | yes | `forallE_inv_stratified` |
| `Lean4Lean.VEnv.piInv_axiom` | `Theory.Typing.Injectivity` | 3 | 3576 | yes | `forallE_inv_stratified`, `WF.rigidShapeUniqNS` |
| `Lean4Lean.MutField.declEnv` | `Verify.TypeChecker.EtaStructG` | 0 | 923 | no | none |
| `Lean4Lean.MutField.unitEnv` | `Verify.TypeChecker.EtaUnitRefute` | 0 | 928 | no | none |
| `Lean4Lean.VEnv.Params` | `Theory.Typing.ChurchRosser` | 0 | 1 | no | (class; type-constants only) |
| `Lean4Lean.VEnv.not_crStatement_of_kstep` | `Theory.Typing.KCanonical` | 18 | 3579 | yes | `forallE_inv_stratified` |
| `Lean4Lean.MutField.decl_WF` | `Verify.TypeChecker.EtaStructG` | 0 | 3768 | **no** | none |

**Verdict on the brief's correction: the first half holds, the second half is understated,
and task 2 is already done in the tree.**

* `patWF_of_wf` **does** exist, at exactly the cited file/line, arity 3, and does prove
  `env.PatWF U` from `env.WF` alone at an arbitrary environment.  The previous round's
  "no `Params` instance over an environment with a structure exists" is therefore
  **refuted**, as the brief said.
* But the price is **two** holes, not one: `IsDefEqU.forallE_inv_stratified` **and**
  `VEnv.WF.rigidShapeUniqNS`.  The brief's phrase "acceptance of the `piInv` census hole"
  names one hole; the measured cone of `piInv_axiom` itself is *both* of those, and
  `IsDefEqU.forallE_inv` does **not** appear in either cone — so the `ConstSpineWF.lean`
  header table (which lists `forallE_inv` and `NormalEq.descend` and `weakN_iff`) is
  **stale**: those three have since been discharged and replaced by
  `rigidShapeUniqNS`.  §1's prediction 1 was right on direction (understated by one hole)
  and wrong on the identity of the holes.
* `patWF_of_wf` additionally drags **`VEnv.IsDefEq.uniq` and `IsDefEq.uniqU`** into its cone,
  which `exists.lean` flags as watched-by-policy.  This is not a hole but it is a cost the
  brief did not mention at all, and it is inherited by anything built on `patWF_of_wf`.
* **§1 prediction 2 confirmed, and it is the round's main result: `VEnv.WF declEnv` and
  `VEnv.WF unitEnv` are already theorems in the tree, and both are `sorry`-FREE** —
  `MutField.declEnv_wf` and `MutField.unitEnv_wf`, `Verify/TypeChecker/EtaUnitRefute.lean:9`
  and `:33`.  `MutField.decl_WF` (`Verify/TypeChecker/EtaStructG.lean:398`) is also
  `sorry`-free, cone 3768.  So the brief's framing ("(a) is your target", "`VEnv.WF` of that
  environment … is the missing piece") is wrong: it was never missing.
* **Not blocked by the `AddInduct` flip.**  `declEnv_eq : ∃ e, VEnv.empty.addInduct' decl =
  some e := ⟨_, rfl⟩` — the block is added to the *empty* environment, where `addInduct'`
  evaluates, so `some e` is `rfl` and no flip is needed.  The flip is about `addInduct` at a
  general environment; nothing here calls it.  So of the brief's two possibilities, **the
  first holds outright**, and the sorry-freeness of `declEnv_wf` is the proof.

### M2 — layering and citability (`can-cite.py`, `layer-check.py`)

* `Lean4Lean.Theory.Typing.ParamsStruct` imports **one** module,
  `Lean4Lean.Theory.Typing.EtaOrient`, and no `Verify` module directly.  Closure: 233 modules.
* `can-cite.py` on my module: **YES** for all five of `VEnv.patWF_of_wf`,
  `MutField.declEnv_wf`, `MutField.unitEnv_wf`, `VEnv.paramsOfPiInv`, `VEnv.piInv_axiom`.
* **`can-cite.py` on `EtaOrient.lean` itself: YES for `MutField.declEnv_wf` and YES for
  `VEnv.paramsOfPiInv`.**  So the previous round wrote "`VEnv.WF declEnv` is open for
  everybody" and "no `Params` instance satisfying them exists today" with both objects inside
  its own 232-module import closure.  This is the third consecutive round corrected on an
  absence claim, and the second in which the material was already citable at the claim site.
* `layer-check.py`: HARD RULE still ok (66 `Theory/SetModel/` modules, none reaches `Verify`).
  In the second SOFT REPORT `ParamsStruct` appears with **46 Verify modules, entering via
  `EtaOrient`** — i.e. the *same* 46 as `EtaOrient`, no new entry point, no new direct import.
  The count of Theory modules downstream of Verify goes 10 → 11; the count with *direct*
  Verify imports stays at 4.  No gratuitous drift added.

### M3 — hole identities: the repo's own prose is stale, in both directions

`exists.lean`, seven more names:

| name | own value a hole? | holes in cone |
|---|---|---|
| `VEnv.IsDefEqU.forallE_inv` | **no** | `forallE_inv_stratified`, `WF.rigidShapeUniqNS` |
| `VEnv.IsDefEqU.forallE_inv_stratified` | **yes** | itself |
| `VEnv.WF.rigidShapeUniqNS` | **yes** | itself |
| `VEnv.NormalEq.descend` | yes | itself + the two above |
| `MutField.unitEnv_not_structEtaG` | no | `weakN_iff`, `forallE_inv_stratified`, `rigidShapeUniqNS`, `NormalEq.descend` |
| `VEnv.paramsOfIotaFree` | no | `forallE_inv_stratified` |
| `MutField.declEnv_structEtaSite` | no | **none** |

Two corrections that matter:

1. **`IsDefEqU.forallE_inv` is not a hole.**  `EtaOrient.lean`'s prose, `ParamsBuild.lean`'s
   header and this round's brief all say the ι case of `PatWF` "needs the
   `IsDefEqU.forallE_inv` hole".  It is a *theorem*, proved from two others.  The real holes
   underneath are `IsDefEqU.forallE_inv_stratified` and `VEnv.WF.rigidShapeUniqNS`.  Naming
   the wrong hole is how "tainted" got read as "open".
2. **`ConstSpineWF.lean`'s own header table is stale**: it lists `weakN_iff`,
   `forallE_inv_stratified`, `NormalEq.descend`, `forallE_inv` as `patWF_of_wf`'s cone; the
   measured cone today is `forallE_inv_stratified`, `rigidShapeUniqNS` only.  (No edit made —
   not my file.  Recorded here for whoever owns it.)

### M4 — `scripts/shape.lean`, `HEADS="Lean4Lean.VEnv.Params Lean4Lean.MutField.declEnv"`

Seven constants in the population conclude something mentioning both, zero of them structure
fields.  Six are `EtaOrient.lean`'s pinned firings, all arity 3 (the two pin hypotheses plus
the instance).  The seventh, arity 0, is this round's `MutField.declParams_pin_satisfiable`.
So **before this file there was no unconditional statement relating `Params` to `declEnv`** —
which is the sense in which the previous round's claim was directionally right, and
`declParams` is the first `Params` instance at a structure environment in the tree.

## §3 WHAT WAS BUILT — `Lean4Lean/Theory/Typing/ParamsStruct.lean`

Builds clean: `lake build Lean4Lean.Theory.Typing.ParamsStruct` → 1322 jobs, **zero errors and
zero warnings from this file**.  Picked up automatically by the `Lean4Lean.Theory.*` glob.

### §1 of the file — the SE rules at an *arbitrary* well-formed environment (the pin off)

| name | arity | statement |
|---|---|---|
| `Lean4Lean.VEnv.paramsOfWFAx` | 3 | `env.WF → (U : Nat) → Params`, `= paramsOfPiInv henv U (piInv_axiom henv)`; `@[instance_reducible] noncomputable` |
| `VEnv.paramsOfWFAx_env` / `_univs` | 3 | `.env = env`, `.univs = U`, both `rfl` |
| `VEnv.parRedSE_structEta_of_wf` | 13 | a `StructEtaSite` at any `env.WF` fires `ParRedSE.structEta` at `paramsOfWFAx henv U` |
| `VEnv.parRedSEC_structEtaC_of_wf` | 13 | ditto for the **contraction** `ParRedSEC.structEtaC` |
| `VEnv.normalEqSE_structEtaL_of_wf` | 14 | ditto for `NormalEqSE.structEtaL` |
| `VEnv.normalEqSE_structEtaR_of_wf` | 14 | ditto for `NormalEqSE.structEtaR` |
| `VEnv.structEtaStepC_of_wf` | 14 | a positive-field site gives `StructEtaStepC` (hence `EtaOrient` §5's `sizeOf` decrease) |

Cone: 6930, holes `forallE_inv_stratified` + `rigidShapeUniqNS`, watched `IsDefEq.uniq`,
`IsDefEq.uniqU`.  **Adds nothing to `piInv_axiom`'s cone.**

### §2–§4 of the file — the concrete instances, and the eight firings unpinned

* `Lean4Lean.MutField.declParams : VEnv.Params` — `@[instance_reducible] noncomputable`,
  `= paramsOfWFAx declEnv_wf 0`.  **A `Params` instance whose environment contains a two-type
  mutual inductive block whose projected member `B` has one field.**  Cone 6931, same two holes.
* `MutField.unitParams` — the same over `unitEnv`.
* `declParams_env : declParams.env = declEnv := rfl`, `declParams_univs := rfl` (and the
  `unitParams` pair).  These are what make the pin come off by `rfl`.
* `declParams_pin_satisfiable : ∃ I : VEnv.Params, I.env = declEnv ∧ I.univs = 0` — the
  "instantiate, don't admire" witness for all eight of `EtaOrient` §6's theorems.
  `unitParams_pin_satisfiable` likewise.
* **All eight firings restated unconditionally** (`'`-suffixed):
  `unitEnv_parRedSE_structEta'`, `declEnv_parRedSE_structEta'`,
  `unitEnv_parRedSEC_structEtaC'`, `declEnv_parRedSEC_structEtaC'`,
  `unitEnv_normalEqSE_structEtaL'`, `unitEnv_normalEqSE_structEtaR'`,
  `declEnv_normalEqSE_structEtaL'`, `declEnv_normalEqSE_structEtaR'`, plus
  `declEnv_rigidity_flips'`.  Each is `@<original> <instance> rfl rfl`.
* Round-trip: `declEnv_parRedSEC_from_general`, `unitEnv_parRedSE_from_general`,
  `declEnv_structEtaStepC_from_general` re-derive three of them from §1's general lemmas, so
  §1 really is a generalisation and not a parallel statement.

### §5 of the file — the limits

* `declEnv_defeqs_iotaRule`, `declEnv_not_iotaFree`, `unitEnv_defeqs_iotaRule`,
  `unitEnv_not_iotaFree` — **`sorry`-free** (cone 1144).  The hole-free routes to `PatWF`
  (`patWF_of_iotaFree`, `patWF_of_deltaFragment`/`paramsOfDelta`) are genuinely unavailable at
  a structure environment, because adding an inductive block *is* adding ι-rules.  So the two
  `piInv` holes in `declParams` are load-bearing, not a lazy choice of route.
* `unitParams_fires_but_rule_false` — the SE contraction fires at `unitParams` **and**
  `¬ unitParams.env.StructEtaG`.  The instance removes the pin, not the gap.
* `exists_wf_structEtaSite_pos` — **`sorry`-FREE** (cone 3892, axioms
  `[propext, Classical.choice, Quot.sound]`): there really is a well-formed environment
  carrying a positive-field structure-eta site, so §1's four lemmas are not vacuous.

## §4 ANSWERS TO THE BRIEF, ONE LINE EACH

1. **Does a `Params` instance at a positive-field structure environment exist?**  Yes.
   `Lean4Lean.MutField.declParams`.  Price: `VEnv.WF declEnv` (already proved, `sorry`-free)
   plus the two census holes `IsDefEqU.forallE_inv_stratified` and `VEnv.WF.rigidShapeUniqNS`.
2. **Verification of the brief's correction.**  First half holds exactly: `patWF_of_wf` exists
   at `Verify/Typing/ConstSpineWF.lean:57`, arity 3, proves `PatWF` from `WF` alone at an
   arbitrary environment, and was citable from `EtaOrient.lean`.  Second half understated:
   it carries **two** holes, not "the `piInv` census hole", and `IsDefEqU.forallE_inv` — the
   hole everyone names — is not a hole at all.  It also drags `IsDefEq.uniq`/`uniqU` into the
   cone, which nothing had mentioned.
3. **`VEnv.WF` verdict.**  Both `declEnv` and `unitEnv`: **provable outright, and already
   proved, `sorry`-free**, at `Verify/TypeChecker/EtaUnitRefute.lean:9` and `:33`.  **Not**
   blocked by the `AddInduct` flip: the block is added to `VEnv.empty`, `declEnv_eq` is
   `⟨_, rfl⟩`, and no `Verify/Inductive/` content is touched or needed.  The brief's premise
   that "(a) is your target" was false before this round started.
4. **Strongest instance built, and its hypotheses' satisfiability.**  Unconditional:
   `declParams`/`unitParams` take no hypotheses at all.  The general one, `paramsOfWFAx`,
   takes `env.WF` and a `Nat`; `env.WF` is satisfiable at a structure environment by
   `declEnv_wf`, and the *joint* condition "`WF` + a positive-field eta site" is satisfiable
   and `sorry`-free by `exists_wf_structEtaSite_pos`.  Nothing here is vacuous.
5. **Firing.**  All eight of `EtaOrient` §6's firings restated with the pin off, plus three
   re-derived from the general lemma.  The `Params` pin comes off completely; §1's lemmas show
   even the *site* pin comes off, so §1 prediction 4 was **too pessimistic** — I predicted the
   witness pin would stay, and it does not, because `StructEtaSite` is a hypothesis rather
   than a fixed object.  What stays pinned is only the *non-vacuity* claim, which by its
   nature needs a witness.
6. **Consumer.**  None, and structurally none can exist yet: `ParamsStruct` sits below the
   whole 46-module `Verify` cluster that `EtaOrient` drags in, so every candidate consumer
   (`StructEtaPrice`, `EtaResidual`, `ConfluenceRebuildPrice`) is *upstream* of it —
   `can-cite.py Lean4Lean.Theory.Typing.StructEtaPrice Lean4Lean.MutField.declParams` says NO
   and names the import it would need.  The honest statement of value is negative-result
   removal: the eight `EtaOrient` firings stop being conditionals of unknown satisfiability.

## §5 GAPS IN MY OWN METHOD — including the ones a small change would break

1. **§1's four lemmas have essentially zero mathematical content.**  Each is a bare
   constructor application; the whole result rides on `(paramsOfWFAx henv U).env` reducing to
   `env` and `.univs` to `U` **by `rfl`**.  That is true only because `paramsOfPiInv` →
   `paramsOfWF` is a plain `def` returning a structure literal with `env := env`.  **If anyone
   ever routes `paramsOfWF` through `Classical.choice`, a `Quot`, or a `where`-clause that is
   not a literal, `paramsOfWFAx_env` stops being `rfl` and every `@`-instantiation in §3 and
   §4 of the file breaks at once.**  This is the single fragile joint in the deliverable, and
   it is one edit wide.
2. **The two holes could be false, and then the instance is wrong, not merely tainted.**
   `declParams` is built through `piInv_axiom`, whose cone is `forallE_inv_stratified` and
   `rigidShapeUniqNS`.  If either is refuted, `declParams` is not a `Params` instance at all
   and every `'`-suffixed theorem in §3 evaporates — the *conditional* versions in
   `EtaOrient.lean` survive, which is exactly why they were written that way.  I have made
   the conditionals unconditional at the cost of importing that risk; that is a real trade,
   not a free win.
3. **My own "limit" theorem is more tainted than the thing it limits.**
   `unitParams_fires_but_rule_false`'s second conjunct is `unitEnv_not_structEtaG`, whose cone
   carries **four** holes including `NormalEq.descend` — and `NormalEq.descend` is the hole the
   whole confluence layer is waiting on, and is itself refutable in one of the scenarios
   `ConstSpineWF.lean` records.  So "the rule is false where the instance fires" is a claim I
   am reporting at lower confidence than the instance itself.
4. **Unmeasured, and I flag it rather than guess: is `declParams` a
   `not_crStatement_of_kstep` instance?**  `ConstSpineWF.lean` records that `church_rosser`'s
   *statement* is refuted at any `Params` instance registering the ι-rule of a
   large-eliminating subsingleton.  `MutField.decl` has `isLE = false` and two ι-rules, and
   `MutField.A` is a one-constructor no-field type in `Type`, so on the face of it the
   subsingleton branch is unavailable — but I did **not** discharge
   `not_crStatement_of_kstep`'s eighteen hypotheses at `declParams`, and I have not proved it
   cannot be discharged.  If it can, `declParams` is a machine-checked counterexample
   generator, not an unblocker, and that is the more valuable reading of this round.  **This
   is the obvious next round.**
5. **`shape.lean` was run for one head pair only** (`Params` × `declEnv`).  I did not run a
   conclusion-shape sweep for "`Params` at *any* concrete environment", so I can say
   `declParams` is the first at a *structure* environment but not that it is the first
   concrete `Params` in the tree — `ParamsWitness.lean`'s `propLoopEnv` instance and
   `Verify/QuotAppParams.lean:124`'s `quotVEnv` instance both predate it, by the δ-fragment
   and `paramsOfPiInv` routes respectively.  The novelty claim is scoped to "structure
   environment", and the `quotVEnv` precedent means the *technique* is not even new — only
   its application here, which makes the previous round's absence claim harder to excuse, not
   easier.
6. **I did not test the SE rules' interaction with `Params.extra_pat` at these environments
   beyond what the instance forces.**  `extra_pat` is discharged by `Pat.extra henv` inside
   `paramsOfWF`, so it typechecks; I did not independently check that `decl`'s two ι-rules
   really land in `Pat declEnv` in the shape `PatWFIota`'s ι case expects.  The typechecker's
   acceptance of `paramsOfWFAx declEnv_wf 0` is my only evidence, and it is good evidence, but
   it is not a separate measurement.

## §6 EDITS TO FILES I DO NOT OWN — stated verbatim, **not applied**

Three prose corrections, all in files owned by other rounds.  None is a frozen file; none is
applied here.

**(E1) `Lean4Lean/Theory/Typing/EtaOrient.lean`, docstring, the paragraph beginning "**The
`Params` firings are conditional, and not because of eta.**"**  Two sentences are false as
measured:

* "`VEnv.WF declEnv` is open for everybody and is *not* used." (line ~47) — `VEnv.WF declEnv`
  is `MutField.declEnv_wf`, proved and `sorry`-free in `EtaOrient`'s own import closure.
  Replace with: "`VEnv.WF declEnv` is `MutField.declEnv_wf` and is *not* used here."
* "So the §6 firings carry `env = unitEnv` / `env = declEnv` hypotheses, and **no `Params`
  instance satisfying them exists today**." (line ~66) — replace with: "So the §6 firings
  carry `env = unitEnv` / `env = declEnv` hypotheses; `Theory/Typing/ParamsStruct.lean`
  discharges them with `MutField.declParams` / `unitParams`, at the price of the two census
  holes in `VEnv.piInv_axiom`."

Also line ~65, "which `Theory/Typing/ParamsBuild.lean` says needs `IsDefEqU.forallE_inv` — one
of the tree's four holes": `IsDefEqU.forallE_inv` is a theorem, not a hole; the holes are
`IsDefEqU.forallE_inv_stratified` and `VEnv.WF.rigidShapeUniqNS`.

**(E2) `Lean4Lean/Verify/Typing/ConstSpineWF.lean`, the `[measured]` table in the header.**  It
records `patWF_of_wf`'s cone as `weakN_iff, forallE_inv_stratified, NormalEq.descend,
forallE_inv`.  Measured 2026-09-04: `IsDefEqU.forallE_inv_stratified,
VEnv.WF.rigidShapeUniqNS` — and the watched names `IsDefEq.uniq`, `IsDefEq.uniqU` are in the
cone and go unmentioned.

**(E3) `Lean4Lean/Theory/Typing/ParamsBuild.lean`, header.**  "the ι and quotient cases are
what need `IsDefEqU.forallE_inv` (`Theory/Typing/Injectivity.lean`, open)" — `forallE_inv` is
not open, and `Theory/Typing/PatWFIota.lean`'s `patWF` has since closed the ι case at an
arbitrary `VEnv.WF` environment from `PiInv`.  The sentence is the direct source of the
previous round's wrong conclusion and is worth fixing first.
