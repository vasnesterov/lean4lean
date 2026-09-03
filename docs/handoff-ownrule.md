# Handoff: the own-member producer of `IotaHargs` — blocker (C) now covers a whole block

**Written 2026-09-03**, on top of `bcc29da`.
My file: `Lean4Lean/Theory/Inductive/OwnRule.lean` (new, mine, 702 lines, 78 jobs, exit 0).
Nothing else was edited. **The flip was not made** and is not mine to make.
`Verify/Soundness.lean`, `Verify/Axioms.lean`, `Verify/Guard.lean`: not read for editing, not
written, not `touch`ed (`git status --short` on the three is empty).

## 0. Grading discipline

Every `#print axioms` line is **hole-freeness and nothing else** (`docs/vacuity-ledger.md` §0).
Content claims are stated separately, with the witness named. A reduction is graded as a
reduction, and where a residual remains I name it.

## 1. Result — outcome 1, at one block; outcome 1-minus at the other

`VIndRestore.iotaHargs_of_own` (§3, arity 12, `[propext, Classical.choice, Quot.sound]`) produces
`R.IotaHargs D σ e j C` at `T.name ∉ K` from

* the restoration's standing interface (`hown`, `hat`, `hfr`, `hσ`),
* the environment inputs `VEnv.iotaRulesRS_wf_of_hargsD` **already carries** (`hσD : σ.WFD env e
  D.recUvars`, `hI : D.IotaCtx env`), so at the call site they cost nothing,
* the rule's coordinates (`hT`, `hK`, `hC`, `hCall`, `hj`),
* and **`htele`. That is the entire residual.**

No `hargs` bundle, no `hres`, no `hpi`/`hsort` shape identity, no `hidx` datum, no bound on
`D.np`, no `e.Ordered`, no `hcl`. Compare `IotaHargsGen` §4 (`iotaHargs_of_heads`, arity 38,
eleven hypotheses `docs/handoff-iotahargs.md` §5d grades *"inhabitation unknown"*).

`lean_minimal_hypotheses` on `iotaHargs_of_own`: **all 12 explicit hypotheses load-bearing**; same
for `hdata_of_companions` (all 8). No dead premise — the class of defect the brief warned about.

Consequences, measured:

| | before | after |
|---|---|---|
| `MP`'s 2 ι-rules with a general producer | 1 | **2** |
| `NTree`'s 3 ι-rules with a general producer | 2 | **3** |
| `hdata` at `MP` from general producers only | no | **yes** (`mp_hdata_own_gen`) |
| (C) at `MP` with no hand ι-witness | no | **yes** (`mp_iotaRulesRS_wf_own_gen`, arity 0) |
| `hdata` at `NTree` from general producers only | no | **still no** — see §5 |

## 2. Why it is cheap: at the own member both conversions of `IotaHargs` are typings

`IotaHargs` is `htele ∧ ∃ A₀ v, hfunM ∧ hconv ∧ hmaj`. At `T.name ∉ K`:

* `hmaj`'s two sides are the **same term**. `VIndRestore.substC_ctorAppR` on the right and §1's new
  `substC_ctorApp'_eq_ctorAppR_own` on the left both land on
  `D.ctorAppR R j C (nf + (nm+nmin)) (bvars 0 nf)`. So `hmaj` degenerates from a conversion to the
  **major premise's typing**.
* Choosing `A₀` to be that typing's type — `(D.tyApp' j (nm+nmin+nf) args').substC σ` — makes
  `hconv` degenerate to `IsType` of it, since `HasType e U Γ x A` *is* `IsDefEq e U Γ x x A`.

Both typings are D-series facts moved across `σ` by `CSubst.WFD`. So the own member costs
`htele` and nothing else.

**The central measurement for this was already in the tree and nobody had connected it.**
`InductiveDeclExamples.rMaj_node_eq` (`Theory/Typing/ConstSubstNested.lean:3028`, `decide`) and
`MRedex.MPWit.mpMaj_obj_eq` (`Theory/Inductive/ParamRedex.lean:2044`, `decide`) *are* the identity
above, at the two parameterised blocks; `rMaj_nil_ne` / `rMaj_cons_ne` / `mpMaj_node_ne` are its
failure at the companions. `docs/handoff-iotahargs.md` §1 cited `rMaj_node_eq` only as *"a `rfl`
discount applies to one of route 1's nine"*. The discount is the whole own-member rule.

I re-elaborated all four statements in my file before deleting them as duplicates. (`mpMaj_obj_eq`
already has a second copy in the tree, `mpMaj_obj_eq'` at `ParamRedex.lean:2711`; a third was not
worth adding.)

## 3. What the file contains

### §1 The own-member head equations, without `D.params = []`

`VIndRestore.substC_tyApp'_eq_tyAppR'` (`NestedRules.lean:415`) already proves
`(D.tyApp' j k args).substC σ = D.tyAppR' R j k (args.map (substC · σ))` — but under
`hp : D.params = []` and `hcl0 : ∀ i, ∀ a ∈ R.tyArgs i, a.ClosedN 0`. Its proof is a
`by_cases hK : T.name ∈ K`, and **both hypotheses are used only in the `∈ K` branch**: `hp` to
strip `tyVal`'s `mkLams D.params`, `hcl0` to kill the `liftN` in `tyAppH`. The `∉ K` branch is
four rewrites off `hat.tyNone` and `hown.tyAppR'_eq`.

This is the class of finding the brief pointed at (`substC_tyAppR`'s five unused hypotheses): a
hypothesis carried past the branch that needs it, invisible in source because the section's
`include` suppresses `linter.unusedSectionVars`. Here the two discarded hypotheses are
**refuted** at the parameterised witnesses (`ntree_params_ne_nil` and `mp_params_ne_nil`, mine;
`InductiveDeclExamples.ntree_not_tyArgs_closed0`, pre-existing), so splitting the branch out is
what makes the own member reachable at `D.np > 0` **at all** — not a tidying.

`VIndRestore.substC_tyApp'_eq_tyAppR'_own`, `VIndRestore.substC_ctorApp'_eq_ctorAppR_own`, both
`[propext, Quot.sound]`.

### §2 The three D-series inputs at the ι-rule's context

`VInductDecl'.iotaLhs_hasType` (`Lemmas.lean` §E5) builds exactly what §3 needs — as internal
`have`s, exported nowhere. §2 states them:

* `VInductDecl'.iotaMajor_hasType` — the major premise typed at the canonical result. Its content
  is `ctorApp'_hasType` specialised to `Δ := minors.reverse ++ motives.reverse`; a specialisation,
  not a new fact, and I say so rather than claiming absence.
* `VInductDecl'.iotaMajorType_hasType` — `VIndCtor.WF.result` under `atRec`, weakened. This one
  had no counterpart in the tree.
* `VInductDecl'.iotaIdx_hasArgs` — the index spine, in the **motive's** telescope shape
  (`liftTele (k+1) (liftTele j …) 0`), which is what `iotaHargs_hfunM` consumes;
  `iotaLhs_hasType` states the same fact with the two lifts already fused.
* plus two plumbing lemmas, `atRecCtx_fields_params` and `iotaCtx_liftN` (the `Ctx.LiftN` from the
  constructor's own context into the ι-rule's).

So **`hidx` is not a residual at the own member either** — `docs/handoff-iotahargs.md` §6's row
"`hidx` — data (D-series)" is right about where it comes from, and §2 does the coming.

### §3 The producer. §4/§4a Instantiation. §5 Whole-block `hdata`.

`VIndRestore.hdata_of_companions` (§5.1, arity 8) is the whole-block statement: **after the
per-rule `htele`s, the residual of `hdata` is `IotaHargs` at the companion rules only.**

### §6/§6a Measurements. §7 Axiom audit (27 lines, all hole-free).

## 4. Anti-vacuity: hypothesis sets jointly inhabited, stated apart from hole-freeness

* `InductiveDeclExamples.ntree_iotaHargs_node_own` — §3 at `ntreeAux`'s own rule (`j = 0`,
  `C = NTree.node`), all 12 arguments supplied at once, `htele` from §J's `rIotaTele_node`.
* `InductiveDeclExamples.ntree_iotaHargs_node_own_inhabited` — **arity 0**: the seven staging
  environments discharged from `ntree_stage₃_exists`, so nothing is assumed.
* `MRedex.MPWit.mp_iotaHargs_obj_own` — the same at the **non-canonical** parameterised redex
  block's own rule (`j = 0`, `C = mpObj`), `htele` from §17's `mpIotaTele_obj`.
* `MRedex.MPWit.mp_hdata_own_gen` / `mp_iotaRulesRS_wf_own_gen` (**arity 0**) — `hdata` and then
  obligation (C) at `MP` with **no hand ι-witness anywhere**: own rule §3, companion rule
  `IotaHargsGen` §4 via `IotaWit.lean`'s `mp_iotaHargs_node_gen`.
* `InductiveDeclExamples.ntree_hdata_own_gen` / `ntree_iotaRulesRS_wf_own_gen` (**arity 0**) — the
  same at `ntreeAux`, but the two *companion* rules are still `rIotaRest_nil` / `rIotaRest_cons`.

### 4a. The shape check at the own index — not inheriting `IotaHargsGen` §7's bound

The brief is right that §7's `ntree_A0_node_eq` sat at `j = 0`, where §4 cannot apply, so §7
bounded 2 rules and not 3. The own-index check belongs to §3 and is here:

* `mp_own_A0_eq` (`decide`) — §3's `A₀` at `MP`'s own rule is `mpIotaHargs_obj`'s
  `.app mpNt (.bvar 5)`, chosen independently by the hand proof. **New**: `mp_A0_node` covered
  `j = 1` only, so there was no `j = 0` `A₀` check at this block.
* `ntree_own_A0_eq` (`decide`) — the same at `ntreeAux`. **Not new content**: it is
  `ntree_own_tyhead_fixed` composed with `ntree_A0_node_eq`, at the same `k = 7` and the same empty
  spine. Stated because §3's `A₀` is the *unrestored* head substituted, not `tyAppR'`.

### 4b. …and `hK` is not removable, refuted rather than argued

The brief told me to check whether an obstruction's hypotheses are actually used before believing
it. For `substC_tyApp'_comp` / `substC_ctorApp'_comp` (`NestedRules.lean:1758/1770`) the answer is
stronger than "used": **their conclusions are false at the own member**, machine-checked —

* `InductiveDeclExamples.ntree_own_tyApp'_comp_false`, `ntree_own_ctorApp'_comp_false`,
* `MRedex.MPWit.mp_own_tyApp'_comp_false`, all `decide`.

Their right-hand sides are saturated `D.np`-fold redexes; at the own member `substC` never fires,
so the left-hand side is the bare head. No hypothesis-trimming turns `IotaHargsGen` §4 into a
producer for the own rule, and the sibling was genuinely required.

### 4c. …and the own rule is not free for other reasons

* `ntree_own_ctors_ne_nil`, `mp_own_ctors_ne_nil` — the own member **has** constructors, so §5.1 is
  a strict weakening of `hdata` (1 of 3 rules at `ntreeAux`, 1 of 2 at `mpAux`) and not a
  restatement. At a block whose own member had no constructors §5.1 would be vacuous.
* `ntree_own_htele_nontrivial` / `mp_own_htele_nontrivial` (aliases of the existing
  `rIotaCtx_node_ne` / `mpIotaCtx_obj_ne`, no new proof) — the own rule's ι-context **does** move
  under restoration, which is why §3 still takes `htele`. The own member's constructors have fields
  mentioning the companion types; that is why `ntree_iota_components_ne` reports all nine
  components moving.

## 5. Where (C) stands now, honestly

`hdata` at a whole block = per-rule `htele` + `IotaHargs` at the **companion** rules.

* At `MRedex.MPWit.mpAux mpAuxNodeB`: complete through general producers (§5a).
* At `ntreeAux`: the own rule is done; the two companion rules would need `IotaHargsGen` §4
  instantiated there, and **§4 has never been instantiated at `ntreeAux`** —
  `docs/handoff-iotahargs.md` §8 item 2 is exactly that job and it is still open. So at the
  canonical block `hdata` does **not** yet follow from the two general producers alone.
* In general, `docs/handoff-iotahargs.md` §6's residual table is **over-stated for any block whose
  own member has constructors**: the two `hargs` bundles, `hres`, `hpiT`/`hpiC`/`hsortT` and `hidx`
  are needed **only at the rules of companion members**. `htele` is needed at every rule, and its
  two harder thirds are still the concurrent (B) stream's `motiveEntry_defeq_of_hargs` /
  `minorEntry_defeq_of_hargs`.

**(C) is not closed and I did not make the flip.** The census is still 13.

## 6. Where the brief and the previous handoffs are wrong

1. **"the type head does not move, so a producer off `OwnId.tyAppR'_eq` should be available"** —
   right about availability, wrong about the mechanism. `OwnId.tyAppR'_eq` alone gives the *type*
   head; what makes the producer cheap is `OwnId.ctorAppR_eq` making `hmaj` an identity, after
   which `A₀` can be chosen so `hconv` collapses too. The type head's collapse is used only to
   identify `A₀` with the hand proofs' (§4a), not in the proof.
2. **"cheap" was flagged as a guess about effort.** Measured: cheaper than the guess. The residual
   is not "a typing or two" but exactly one hypothesis, `htele`, and 12 of 12 hypotheses are
   load-bearing.
3. **`docs/handoff-iotahargs.md` §2's environment scan does not reproduce.** My scan over the
   compiled environment — **356** built modules, every `.lean` under `Lean4Lean/Theory` and
   `Lean4Lean/Verify` that has an `.olean`, listed explicitly — reports for
   `VIndRestore.IotaHargs`: **19 mentioning, 15 in the conclusion, 4 hypothesis-only**. Subtracting
   my 6 gives **9 in the conclusion before this file**, of which **exactly one**
   (`iotaHargs_of_heads`) was a general producer. §2 of that handoff claims "before my file: 8
   declarations mention it, four with it in the conclusion" and "after my file: 9 [total]". Those
   numbers cannot both be right after `IotaWit.lean` added three more; the likely cause is a
   narrower import list in their scan, which is the population blindness the ABSENCE rule is about.
   I state my population; theirs is not recoverable from the document.
4. **`mp_iotaHargs_node_inhabited` is not `[propext, Quot.sound]`.** It is
   `[propext, Classical.choice, Quot.sound]` (measured). `Classical.choice` enters through
   `VInductDecl'.ctorApp'_hasType`, which already carries it, so everything downstream of the
   D-series major-premise typing does — including my §3. `mp_own_not_mem_K`,
   `ntree_own_not_mem_K`, `mp_own_tyhead_fixed`, `ntree_own_tyhead_fixed` **are**
   `[propext, Quot.sound]` as relayed.
5. **`IotaHargsGen` §4's "not by itself a producer of `hdata` for a block" is right but
   under-stated**: it is not merely that `hK` fails at the own member; the `_comp` lemmas'
   conclusions are *false* there (§4b). "Not proved" and "false" are different rows in the ledger.
6. **`mpMaj_obj_eq` is duplicated in the tree** (`mpMaj_obj_eq'`, `ParamRedex.lean:2711`, proved a
   second way). Not mine to fix; recording it.

## 7. Verification record

* `lake build Lean4Lean.Theory.Inductive.OwnRule`: **78 jobs, exit 0**.
* All 27 `#print axioms` lines in §7/§7a: hole-free. `[propext, Quot.sound]` for the syntactic and
  `decide` results, plus `Classical.choice` for everything downstream of
  `VInductDecl'.ctorApp'_hasType` (pre-existing, not introduced here). `ntree_params_ne_nil` and
  `mp_params_ne_nil` depend on no axioms at all.
* Declaration names read off the file's own `namespace` lines, never composed from the path.
* `lake env lean --run scripts/sorry-census-all.lean`: **HOLES 13**. `BUILT: 397`;
  `in population but NOT BUILT: 1` — `Lean4Lean.Theory.Typing.ShapeIndepStep`, a concurrent
  stream's brand-new file, foreign and untouched.
* `scripts/dup-names.lean`: *"no duplicate Lean4Lean declarations across the joined cone"*.
* Layering: `grep -rln "^import Lean4Lean.Verify" Lean4Lean/Theory/` is empty.
* My file is an orphan module (imported by nothing), as a new leaf should be.
* Frozen files: untouched (`git status --short` on the three is empty).

### 7a. Foreign build failure seen and not fixed, per instruction

At session start the whole nested cone was **unbuildable**: `Theory/Inductive/NestedHead.lean` had
`omit h in` added to `ntree_const_staged` / `nlist_const_staged` while
`Theory/Typing/ConstSubstNested.lean:2177/2222` still passed `h`, so `ConstSubstNested` failed to
elaborate and every module above it with it. This is the HypTrim stream mid-edit; it resolved
itself ~2 minutes later when they updated the callers. I touched neither file. Worth recording
because the failure looked exactly like a broken import of my own and the error *kind* — an
application type mismatch on a section variable — is what identified it as foreign.

### 7b. Measured vs read off

**Measured by me this session:** every axiom line and arity above; `lean_minimal_hypotheses` on
`iotaHargs_of_own` and `hdata_of_companions`; every `decide` in §6/§6a; the environment scan of §6
item 3 (356 built modules, import list generated from the filesystem and filtered to those with an
`.olean`); the three structural scans that establish §1's and §4b's absence claims — conclusions
mentioning `tyAppR'`+`substC`: **14**, of which mine is **1**; `ctorAppR`+`substC`: **12**, mine
**1**; `tyBody`+`mkLams`+`substC`: **4**, mine **2**, and `ctorBody`+`mkLams`+`substC`: **2**, mine
**1** — so §1's two equations and §4b's three refutations have no prior counterpart; the census,
dup-names and layering checks.

**Measured by grep over the source, not over the environment:** that `VIndRestore.SubstAt.tyNone`
and `.ctorNone` have **exactly one consumer each** (`NestedRules.lean:435` and `:457`), both inside
the `hp`-gated lemma — which is what says §1's `∉ K` half had no other user. A projection's uses
are not visible to a type-level scan, so this one is a grep and I grade it as one.

**Read off source, not independently re-run:** that `hcl0` is refuted at `ntreeAux`
(`ntree_not_tyArgs_closed0` — I read the name and statement, did not re-elaborate);
`docs/handoff-iotahargs.md` §8 item 2 still being open (read from the document plus the absence of
any `ntreeAux` instance of `iotaHargs_of_heads` in my §6 scan output, which is evidence but not the
same as trying it).

## 8. Pick up first

1. **`IotaHargsGen` §4 at `ntreeAux`'s two companion rules** — the one thing between here and
   `hdata` at the canonical block from general producers alone. `docs/handoff-iotahargs.md` §8
   item 2's advice stands (`nlistNil` first: `nf = 0`, so `AsT = AsC = []`), and its named
   load-bearing hypothesis is `hbodyC`, the restored `List.nil (NTree #0)`'s typing.
2. **`htele` in general**, now the *only* residual at own rules and one of three at companion
   rules: `iotaCtx_teleDefEq` + the (B) stream's `motiveEntry_defeq_of_hargs` /
   `minorEntry_defeq_of_hargs` + `teleDefEq_fld_iota_of_fields`. Cross-stream; `RecTyped.lean` is
   not mine.
3. **Split `substC_tyApp'_eq_tyAppR'` / `substC_ctorApp'_eq_ctorAppR` at their branch** — §1 is the
   `∉ K` half, and the `∈ K` half is the only part that needs `hp`/`hcl0`. Someone who owns
   `NestedRules.lean` could restate the originals as the two halves plus a `by_cases`, deleting two
   hypotheses from the own-member route wherever else it appears. I did not, because that file is
   not mine.
4. **Do not** close `tryEtaStructCore.WF` / `isDefEqUnitLike.WF` (ledger row 197), and **do not**
   make the flip: (C) is still open at the canonical block and the census is still 13.
