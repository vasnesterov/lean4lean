# handoff-claimb2 — B5 (write the module), B7 (settle recArg), B6 (say what remains)

Owned files: `Lean4Lean/Verify/Inductive/ClaimB.lean` (new), `docs/handoff-claimb2.md` (this).
Round start: HEAD = 6319956 (predecessor's docs commit landed). `git status` shows two OTHER
streams in flight — a Proj/Typing migration (`Lean4Lean/Verify/Typing/Proj*` deleted,
`Lean4Lean/Theory/Inductive/Proj*` added, `docs/handoff-projmigrate.md`) and an
independence/residual stream (`docs/handoff-indepresidual.md`, `CommutationLemmas.lean`,
`EtaStructG.lean`, `UnitEta.lean`, `scripts/hole-cone.lean`). Neither file is mine.

## Priors (written BEFORE any measurement this round)

### Scoring my predecessor's priors (from `docs/handoff-claimb.md`)
- P1 (new module must import both families; nothing imports it yet) — **CORRECT**, and its M9
  went further and named a cycle-free consumer. Score 1.0.
- P2 (`OracleSound` dischargeable from the producers with no new induction) — **UNSETTLED**;
  that is exactly my B5. It crashed before writing the term. I inherit this as my own prior.
- P3 (B6 confidence 0.25) — its M10 then showed B6 is *blocked* on B7, which is stronger and
  more useful than the prior. Score the prior 0.4 (right that it would not close), the M10
  finding 1.0.
- P4 (`recArg` derivable from the translated ctor type, no surface data — confidence 0.55) —
  looks **CORRECT** and its M8/M11 nearly closed it. Score 0.9 pending my own measurement.
- P5 (intended the CHECKER route) — **WRONG**, and it refuted itself in M7. Score 0.0 for the
  prior, 1.0 for the self-refutation. This is the single most valuable line in the handoff:
  the orchestrator's "you may choose either supplier" was false.
- P6 (Claim A untouched) — I inherit; will re-verify.

### My own priors
- Q1. B5 shape: `OracleSound` is a *hypothesis* in 5 consumers and has no producer. Prior: it
  is dischargeable at `ctorTr?` by a term of the form `fun .. => ⟨trExprS_of_ctorTr .., ..⟩`
  with NO induction, because the `*_of_ctorTr` lemmas are exactly the pointwise facts.
  Confidence 0.65. Residual risk: `OracleSound` may demand a *totality* clause
  ("`tr` succeeds on every well-typed surface expr") which `ctorTr?` cannot give without a
  completeness lemma for the fragment. Confidence that such a clause exists: 0.35.
- Q2. B5 target: the brief says prefer the supplier-neutral `CtorStoresTr` (cone 853) over
  `OracleSound`. Prior: `ctorStoresTr_rigid` (cone 3783) is the introduction rule and
  `ctorStoresTr_iff` the elimination, so I should discharge `CtorStoresTr` first and get
  `OracleSound`'s `trCtors` arm as a corollary. Confidence that `CtorStoresTr` is the better
  primary target: 0.7. Confidence I can discharge BOTH: 0.5.
- Q3. B7 tension (`Decl.lean` L963-967 "unrecoverable from the declaration" vs `recog` reading
  it off a field type). Prior: the two are **consistent** and the distinguishing word is
  "declaration" = the SURFACE `Lean.InductiveType` list, vs `recog`'s input which is a
  `VIndRestore` + an already-translated `VExpr` field type. `recog` needs the restoration `R`
  (the member names/levels/args), which the surface declaration does not carry as data —
  it is *reconstructed* by the checker's own naming discipline. So: "unrecoverable from the
  surface declaration alone" AND "recoverable from (restoration, translated field type)" are
  both true and not in tension. Confidence 0.7. Competing prior: the L1044 table attribution
  to `checkPositivity`/`isRecArg` is simply STALE prose written before `recog` existed, and the
  honest answer is "the table row should now say `recog`". Confidence 0.3. These are not
  exclusive — both can hold. I will measure `recog`'s actual input type and `VIndRestore`'s
  provenance rather than argue.
- Q4. B7 closure: prior that `recog` alone closes B7 = 0.45. What I expect it still needs: a
  lemma in the OTHER direction — `recog` is proven *sound* (`recog_sound`: if it says `some r`
  then `r.canonTypeR D R i = S`) but B7 needs *completeness*: if the field genuinely IS
  recursive then `recog` returns `some`. Prior that no such completeness lemma exists yet: 0.6.
  If so, B7 closes as "recovery function exists and is sound; completeness is the residual".
- Q5. B6: prior that I can only STATE what remains, not prove it, and that the statement is
  "populate `recArg` in the surface map via `recog`, then the restoration stops being a no-op".
  Confidence B6 closes this round: 0.1.
- Q6. Claim A (twelve `TrIndDeclN` field producers) untouched at close: I will not open any
  Claim A file for writing. Verify by `git status` at close.
- Q7. Round-close: prior that census is 13 / NOT BUILT 0 and my file adds nothing to either,
  and that the ~66 "not explicitly referenced" warnings stay at ~66 with 0 from my file.
  Confidence 0.85 (the two live streams may move the warning count; that is drift).

## Measurements (appended as made)

### M1. `OracleSound` has NO totality clause — Q1's residual risk is dead
`Lean4Lean.OracleSound tr env Us := ∀ (e : Expr) (e' : VExpr), tr e = some e' → TrExprS env Us [] e e'`
(`Verify/Inductive/SurfaceMap.lean:352`). Pure soundness, no "succeeds on every well-typed input".
So Q1's 0.35 branch (a totality clause blocking `ctorTr?`) is **refuted by reading the type**:
the producer is a 4-line `Option.map` destructuring, no completeness lemma needed. Q1 confidence
raised to 0.95 before writing.

### M2. The exact producers, read in full
- `Lean4Lean.trExprS_of_ctorTr` (`TrExprSGeneral.lean:224`):
  `ConstLookup Γc env → ctorTr? Γc Us e [] = some (e', t') → TrExprS env Us [] e e'`.
  This is *precisely* `OracleSound`'s body at `tr := fun e => (ctorTr? Γc Us e []).map (·.1)`.
- `Lean4Lean.trIndType_of_ctorTr` (`FlipWiring.lean:143`) and `Lean4Lean.trType_of_ctorTr`
  (`FlipWiring.lean:161`) — the `trType` arm.
- `Lean4Lean.trCtors_of_ctorTr` (`TrExprSGeneral.lean:288`) and
  `Lean4Lean.trIndCtorR_of_ctorTr` (`TrExprSGeneral.lean:264`) — the `trCtors` arm.
- `Lean4Lean.ConstLookup Γc env := ∀ c ci, Γc c = some ci → env.constants c = some ci` — a leaf
  lookup table, no `HasType`, no `VEnv.WF`. And `Lean4Lean.constLookup_none` (`FlipWiring.lean:138`)
  discharges it for the empty table at EVERY environment: so the `trType` arm at a sort-telescope
  member is free of environment hypotheses entirely.

### M3. The neutral primitive's body, and why it is the better B5 target (confirms Q2)
`Lean4Lean.CtorStoresTr env Us rtypes D R` (`SurfaceMap.lean:407`) asks per constructor for
`c.name = R.ctorName C.name ∧ ∃ ct, TrExprS env Us [] c.type ct ∧ C.typeR D R j = ct`.
`Lean4Lean.ctorStoresTr_surfInductDecl?` (`SurfaceMap.lean:456`) already derives it *from*
`OracleSound`, and `Lean4Lean.trCtors_of_ctorStoresTr` (`SurfaceMap.lean:431`) derives the field
from it. So the chain is `ctorTr? → OracleSound → CtorStoresTr → trCtors`, and discharging the
FIRST arrow makes all three fire. Q2 confirmed: `CtorStoresTr` is downstream of `OracleSound`
here, so the one producer I owe is `OracleSound`, and `CtorStoresTr` comes both ways —
via the map (`ctorStoresTr_surfInductDecl?`) and directly from `ctorTr?` (my own, supplier-side).

### M4. Baseline: whole-tree `lake build` **exit 0**, 1644 jobs, at HEAD 6319956 + two streams' WIP.

### M5. **B7's tension is resolved, and the reconciling word is `whnf` — NOT "declaration vs restoration"** (my Q3 prior is wrong in its mechanism)
The already-in-repo witness is `Lean4Lean.ROWit` (`Theory/Inductive/RestoreOpWit.lean`), the
block that refuted `VInductDecl'.Canonical` (ledger ruling 116d):
```
inductive roT : Type where | mk : ((fun x : Type => roT) Prop) → roT
```
- `ROWit.roField.type = ROWit.roRedex = .app (.lam (.sort 1) (.const `roT [])) (.sort 0)` — a
  **β-redex stored verbatim**; the file records that `AddInductive.run`,
  `Environment.addInductive` and `Lean4Lean.addDecl` all **accept** this block (executed,
  `cgm/accept`).
- `ROWit.roField.recArg = some ROWit.roRec`, because `AddInductive.isRecArg` classifies the
  field recursive **by looking at `whnf`**.
- `Lean4Lean.VIndRestore.recogAt` is a **purely syntactic** matcher: it takes `b.spineFn` and
  demands `= .const (R.tyName k) (R.tyLvls k)`. At `roRedex` the spine head is a `.lam`, so
  `recog` returns **`none`** while the true `recArg` is `some roRec`.
So `recog` is **sound but provably incomplete**, and the incompleteness is not a gap in the
lemma — it is forced: `VIndField.WF.pos`'s `some` branch ties `F.type` to `r.canonType D i` by
`IsDefEqType` (defeq) only, and `isRecArg` reduces where `recog` cannot.
**Verdict: `Decl.lean` L963-967 ("`VIndField.recArg` unrecoverable from the declaration") and
L1044 (attributed to the checker's `checkPositivity`/`isRecArg`) are CONSISTENT with `recog`, and
both are correct.** `recog`'s docstring's "nothing about `D` enters" is about `D`, not about
`whnf`; it never claimed completeness, and `recog_sound` is the only direction it proves.
My Q3 was right that the two claims are consistent (0.7 branch) but **wrong about why**: the
distinguishing axis is not the surface declaration vs the restoration, it is **syntax vs `whnf`**.
Q4 (0.6 that completeness is the missing direction) is **CORRECT**, and stronger than I priced:
completeness is not merely absent, it is **false**, at a block the kernel accepts.

### M6. **NINTH ALREADY-DONE CATCH, and it is the big one: the `whnf` gap is already repaired and MEASURED**
Found by grepping `recogAt` outside `NestedBuild.lean` (a HELPER-shape query — the deliverable-shaped
"does a recArg reader exist" query had already returned `recog` and stopped).
`Lean4Lean/Theory/Inductive/MemberRedex.lean` §1 already has the **general** form of the negative
half I was about to prove concretely:
- `Lean4Lean.MRedex.recogAt_none_of_lamHead` / `Lean4Lean.MRedex.recog_none_of_lamHead`:
  `(splitPis S.piArity S).2.spineFn = .lam A b → R.recog nm i S = none`.
  My `ROWit` witness is an *instance* of this, not a new fact.
And the repair **has landed**: `Lean4Lean.VNestedOcc.field` (`NestedBuild.lean:367`) is a
**two-stage** reader —
```
match R.recog H.nm i S with
| some r => ...            -- stage 1: syntactic
| none => match R.recog H.nm i (VExpr.betaHead S) with
          | some r => ...  -- stage 2: one head-β step, then syntactic
          | none => ...    -- recArg := none
```
with `field_eq_fieldO_of_some` / `_of_none` proving it conservative on both sides.
And `Verify/Inductive/MemberRedexScan.lean` §2 **measured the coverage on the running
environment**: **47** safe blocks with a nested-shaped field, **790** auxiliary constructor fields,
**3** misclassified by stage 1 (`Lean.Json`, `Lean.PrefixTreeNode`, `MRedex.MRWit.MJ`),
**3 of 3** fixed by stage 2, **0** residual. The named residue that stage 2 still cannot reach:
a redex **under a binder** (`∀ y, (fun x => I) y`) or one needing **δ** — those need `isRecArg`'s
full whnf loop.
**This rewrites B7's answer.** It is not "recog is incomplete, full stop"; it is:
single-stage syntactic recovery is incomplete (provably, at `roDecl`); the two-stage
`recog ∘ betaHead` reader closes it on 790/790 measured fields; the residue is named and is
exactly the `whnf` loop. `Decl.lean` L963-967 and L1044 remain **correct as statements about a
single-stage read**, and the sharp version is "recoverable up to the `whnf` gap".

### M7. **B5 is DONE and B7 is CLOSED** — `Lean4Lean/Verify/Inductive/ClaimB.lean`, 20 declarations
`lean_diagnostic_messages`: **0 errors, 0 warnings**, 20 `#print axioms` lines, every one inside
the whitelist (`propext`, `Quot.sound`, `Classical.choice`), **no `sorryAx` anywhere**.
Imports: `Verify.Inductive.SurfaceMap` + `Verify.Inductive.FlipWiring` +
`Theory.Inductive.RestoreOpWit` + `Theory.Inductive.MemberRedex`. Closure = **203**
(union of the four = 202, plus itself). `TrIndDeclNProducer` (207) still does **not** contain
`ClaimB`, and `ClaimB` does not contain `TrIndDeclNProducer` — so the consumer import stays
cycle-free after the two extra Theory imports (each cost exactly 1 new module: RestoreOpWit 51,
MemberRedex 54, both almost entirely inside the existing closure).

B5 deliverables (all `Lean4Lean.`-qualified):
- `ctorOracle` — `fun e => (ctorTr? Γc Us e []).map (·.1)`, the pure function `OracleSound` wants.
- `oracleSound_of_ctorTr` — **`OracleSound`'s first producer.** 3-line proof.
- `oracleSound_none` — at the empty table, sound at *every* environment.
- `oracleSound_staged_of_ctorTr` — the staged form the `trCtors` arm asks for.
- `trType_surfInductDecl?_ctorTr`, `ctorStoresTr_surfInductDecl?_ctorTr`,
  `trCtors_surfInductDecl?_ctorTr` — the three oracle-dependent arms of the map with the
  `OracleSound` hypothesis **gone**, replaced by a `ConstLookup`.
- `surfInductDecl?_arms_ctorTr` — all three at once, from one `ConstLookup` + one staged family.
- `ctorStoresTr_of_ctorTr` — the **supplier-neutral primitive at an arbitrary `R`**, not routed
  through the map, so it is already usable at the real restoration (this is what B6 part 3 needs).
- `ctorStoresTr_of_ctorTr_rigid` — the witness is pinned, via `isUnique_of_ctorTr`.

B7 deliverables:
- `recog_roCanon` (`rfl`), `recog_roRedex_none` (`rfl`), `recog_roRedex_none'` (from
  `MRedex.recog_none_of_lamHead`, showing the witness is an instance), `recog_incomplete`.
- `VInductDecl'.recArgOf` — the **two-stage reader in the declaration setting**,
  `(recog S).orElse fun _ => recog (betaHead S)`.
- `recArgOf_sound` — sound *with the head-β step visible in the conclusion*: the answer restores
  either to `S` or to `betaHead S`. Deliberately a disjunction and not a defeq: the reader is NOT
  sound up to arbitrary conversion.
- `recArgOf_idx_lt`, `recArgOf_eq_recog_of_some` (conservativity), `recArgOf_eq_recArg`.
- `recArgOf_roRedex : ROWit.roDecl.recArgOf 0 ROWit.roField.type = ROWit.roField.recArg` — by
  **`rfl`**. The headline: at the block where the single-stage reader is wrong and the kernel
  stores a β-redex, the two-stage reader returns the stored `recArg` on the nose.

### M8. Round-close numbers (all measured after the file landed)
- whole-tree `lake build`: **exit 0**, **1645 jobs** (baseline was 1644; +1 = `ClaimB`).
- `scripts/sorry-census-all.lean --run`: **BUILT 462; NOT BUILT 0**; **HOLES 13**. Target met.
  `ClaimB` appears in the orphan list (nothing imports it yet — expected; the consumer import is
  `TrIndDeclNProducer`'s to make, and it is cycle-free).
- Guard 1: "Axioms.lean declares exactly the 24 frozen axioms ✓".
  Guard 2: "kernel_sound axioms within whitelist ✓ (proof INCOMPLETE: sorryAx present)".
  Guard 3: "checker cone implementation gaps within frozen list (2/2 remaining) ✓".
- `scripts/layer-check.py`: **exit 0**, "66 module(s) checked, none reaches Verify/"; soft report
  4 `Theory/` files with 1 direct `Verify/` import each — pre-existing, none mine.
- Warnings: **0 from `ClaimB.lean`.** In-repo "not explicitly referenced" total is **63 across 23
  files**, not the brief's ~66 across 24 — **drift, downward**, caused by another stream's
  `a554def` (the ProjGen migration into `Theory/`), which landed mid-round. Not my gate.
- **Claim A confirmed untouched**: `git diff --stat HEAD -- Lean4Lean/Verify/Inductive/` is
  **empty**, and `git status --porcelain` shows only `?? Lean4Lean/Verify/Inductive/ClaimB.lean`
  and `?? docs/handoff-claimb2.md` as mine.
- Frozen files (`Verify/Soundness.lean`, `Verify/Axioms.lean`, `Verify/Guard.lean`) not opened for
  writing, and no frozen edit is requested by this round.

### M9. Prior scoring, closed
- Q1 (0.65 → 0.95 after M1): **CORRECT**. The producer is 3 lines; the totality clause I feared
  does not exist.
- Q2 (0.7 that `CtorStoresTr` is the better target; 0.5 that both are dischargeable): **CORRECT and
  both discharged** — but the geometry was the other way round from what I assumed. `CtorStoresTr`
  is *downstream* of `OracleSound` in `SurfaceMap.lean`, so the single producer I owed was
  `OracleSound`, and `CtorStoresTr` then came **twice**: through the map, and directly from the
  supplier at arbitrary `R` (`ctorStoresTr_of_ctorTr`), which is the version B6 needs.
- Q3 (0.7 consistent, mechanism = "declaration vs restoration"): **half right**. Consistent, yes.
  Mechanism, **no** — it is **syntax vs `whnf`**. Scored 0.4.
- Q4 (0.6 that completeness is the missing direction): **CORRECT and understated**. Completeness
  of the single-stage reader is not missing, it is **false at a block the kernel accepts**; and the
  two-stage repair that fixes it was already in the tree and already measured (M6). Scored 0.9.
- Q5 (0.1 that B6 closes): **CORRECT, B6 did not close.** What it needs is now stated to the
  level of "restructure `surfIndCtor?` into two passes", with the one new lemma named.
- Q6 Claim A untouched: **held**.
- Q7 (0.85 census 13 / NOT BUILT 0, ~66 warnings): census **exactly right**; warning count drifted
  to 63 for a reason I can attribute (another stream's commit). Scored 0.9.
- **My own autoImplicit near-miss, logged as required.** The first draft of
  `trCtors_surfInductDecl?_ctorTr` wrote `TrIndCtorR env₁ Us D R j c C` with `R` **never bound** —
  exactly the hole-by-`autoImplicit` failure the process rules warn about. I caught it by reading
  my own draft against `SurfaceMap.lean:481`, before elaborating, and the fix is `D.idRestore`.
  The rule earned its keep again: had it elaborated, only a per-declaration axioms line would have
  shown it.

### M10. Cones and cleanliness of every deliverable (`scripts/exists.lean`, population 459)
| declaration | arity | cone | own hole | sorryAx in cone | watched in cone |
|---|---|---|---|---|---|
| `Lean4Lean.VInductDecl'.recArgOf` | 3 | **848** | false | **false** | **none of 6** |
| `Lean4Lean.recArgOf_roRedex` | 0 | **864** | false | **false** | **none of 6** |
| `Lean4Lean.recog_incomplete` | 0 | **864** | false | **false** | **none of 6** |
| `Lean4Lean.recArgOf_sound` | 5 | **941** | false | **false** | **none of 6** |
| `Lean4Lean.oracleSound_of_ctorTr` | 4 | **1151** | false | **false** | **none of 6** |
| `Lean4Lean.ctorStoresTr_of_ctorTr` | 8 | **1225** | false | **false** | **none of 6** |
| `Lean4Lean.trCtors_surfInductDecl?_ctorTr` | 24 | **2131** | false | **false** | **none of 6** |
| `Lean4Lean.surfInductDecl?_arms_ctorTr` | 13 | **2138** | false | **false** | **none of 6** |
Every deliverable is **0-hole and 0-watched**. `oracleSound_of_ctorTr`'s 1151 is `ctorTr?`'s 912
plus the soundness induction, i.e. the fragment route's price paid exactly as predicted; the checker
route would have been 18795 with 8 holes and both `IsDefEq.uniq`/`uniqU` (predecessor's M6).
B7's side is the cheapest thing here: the two-stage reader costs **848**, under half the map's arms.
