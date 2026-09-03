# Handoff: blocker (C) re-examined at a second parameterised witness

**Written 2026-09-03**, on top of `6a62f13`.  My file:
`Lean4Lean/Theory/Inductive/IotaWit.lean` (new, mine, 24 declarations, 77 jobs, exit 0).
Nothing else in `Lean4Lean/` was edited.  **The flip was not made** and is not mine to make — see
§7.

## 0. Grading discipline

Every `#print axioms` line in §6 of my file is **hole-freeness and nothing else**
(`docs/vacuity-ledger.md` §0).  Content claims are stated separately, with the witness named, and
degeneracy is disclosed separately from inhabitation.  Names in `#print axioms` were read off the
file's own `namespace` lines.

## 1. The headline: §4 of `IotaHargsGen` IS jointly satisfiable at `mpAuxB` — and it has a
   restriction nobody had recorded

Answering the three questions I was set, in order.

**1. Is §4's hypothesis set jointly satisfiable at `mpAuxB_hdata`'s block?  YES, at the companion
ι-rule — and NO at the other one, for a reason that is not about difficulty.**

* `MRedex.MPWit.mp_iotaHargs_node_gen` (arity 6: four constant lookups + `henv` + the section's
  `F`) applies `VIndRestore.iotaHargs_of_heads` at `mpAux mpAuxNodeB`, `j = 1`, `C = mpAuxNodeB`,
  supplying **all 38 arguments simultaneously**.  Its conclusion is `mpIotaHargs_node`'s, so §4's
  general route reproduces the hand proof at a second, structurally different block.
* `mp_iotaHargs_node_inhabited` is the same thing at **arity 0** (`mp_stage₃_exists` discharges the
  five parameters), i.e. the joint-inhabitation certificate `ntreeAux_recHargs_premises_inhabited`
  is the model for.
* `mp_hdata_gen` (arity 10) is `mpAuxB_hdata` with the companion rule routed through §4, and
  `mp_iotaRulesRS_wf_gen` (**arity 0**) is obligation (C) at this block carried through it.

**So all eleven of `docs/handoff-iotahargs.md` §5d's never-checked hypotheses now hold at once at a
real block**: `hOnp`, `hbvT`, `hbvC`, `hbodyT`, `hbodyC`, `hAsT`, `hAsC`, `hpiT`, `hpiC`, `hsortT`,
`htele`.  §5d's grade "hole-free, shape-checked, inhabitation unknown" can be upgraded to
**"inhabited, at the companion rule of two structurally different parameterised blocks"**.

### 1a. …but §4 cannot reach the block's own member, and that is a *new* obstruction

`iotaHargs_of_heads` inherits `hK : T.name ∈ K` from `substC_tyApp'_defeq_tyAppR'_comp` and
`substC_ctorApp'_defeq_ctorAppR_comp` (`NestedRules.lean:1783/1803`), where it is load-bearing:
`hat.tySome j T hT hK` is what makes `substC` fire on the head constant (`substC_tyApp'_comp`,
`:1758`).  At the member the step **declares**, `σ` is `none` at that name — so `hK` is **false**,
not merely unproved.  Measured:

| measurement | verdict |
| --- | --- |
| `mp_own_not_mem_K` | `MP ∉ mpK` (`decide`) |
| `ntree_own_not_mem_K` | `NTree ∉ ntreeK` (`decide`) |
| `mp_companion_mem_K` / `ntree_companion_mem_K` | the companions *are* in `K`, so `hK` is not vacuous either way |
| `mp_csubst_own_none` | `σ (MP) = none` (`rfl`) — so no reformulation keeping `substC_tyApp'_comp` can reach `j = 0` |

**Consequence: §4 covers 1 of `MP`'s 2 ι-rules and 2 of `NTree`'s 3.**  It is therefore *not* by
itself a producer of `hdata` for a whole block; `mp_hdata_gen` has to fall back on
`mpIotaHargs_obj` at `q = 0`.  `docs/handoff-iotahargs.md` §4 calls §4 "`R.IotaHargs D σ e j C` in
general" and §2 calls it "the first with `IotaHargs` in the conclusion and no witness in its
statement" — both true, but the *general* reading over-claims by one rule per block, and this was
not recorded anywhere.

**And this matters for one of the checks that round already did.**  `IotaHargsGen` §7's
`ntree_A0_node_eq` is stated at `j = 0` — the `NTree.node` rule — where `hK` is false.  So that
particular shape check is at a `j` where §4 **cannot be applied at all**.  The other two
(`ntree_A0_nil_eq`, `ntree_A0_cons_eq`) are at `j = 1` and are fine.  That is one of the three
A₀ agreement checks landing outside §4's domain; it does not invalidate anything proved, but it
means §7 bounded 2 rules, not 3.

### 1b. The restriction is cheap, measured

Where `hK` fails the substitution is the identity on the head and `tyAppR'` collapses to `tyApp'`
(row 143d's head face, `VIndRestore.OwnId.tyAppR'_eq`).  So §4's `hconv` slot at the uncovered
rules degenerates to a **typing**, not a conversion:

* `mp_own_tyhead_fixed` (`decide`): `(tyApp' 0 6 []).substC σ = tyAppR' R 0 6 []` at `MP`;
* `ntree_own_tyhead_fixed` (`decide`): the same at `NTree`, at the ι-rule's own `k = 7`;
* and `mpMaj_obj_eq` / `rMaj_node_eq` (pre-existing, quoted) already say the *constructor* head is
  an identity at the own member.

So the honest statement of §1a is: **§4 needs a sibling for the own-member rules, and the sibling
is cheap** — an `OwnId`-based producer whose two conversions are `IsDefEq.rfl` up to a sort
derivation.  It is not in the tree; I did not write it (it belongs in `IotaHargsGen.lean`, which
I do not own).

## 2. Where I was told something wrong — the highest-value output

**The claim that yesterday's (C) round did not have `mpAuxB_hdata` is false, and the diagnosis
attached to it is false too.**  I was told:

> `ParamRedex.lean:2397`'s `mpAuxB_hdata` (arity 9) is an `IotaHargs` at a parameterised block …
> `docs/handoff-flipprice.md` §5b records (C) as having **no** parameterised `IotaHargs` witness;
> that is wrong. … The reason nobody had them: the structural scan the round relied on **did not
> import `ParamRedex.lean`**.

Checked against the round's own write-up:

* `docs/handoff-iotahargs.md` **§1** names `MRedex.MPWit.mpIotaHargs_obj` / `_node` and
  `mpAuxB_hdata` explicitly, calls them "the second one … the harder shape (a stored redex)", and
  uses them as its **headline correction** to its own brief: *"there are **two** parameterised
  witnesses with `IotaHargs` discharged, and the second one is the harder shape."*
* `docs/handoff-iotahargs.md` **§2** reports its scan finding **four** declarations with
  `IotaHargs` in the conclusion, and `mpAuxB_hdata` is one of the four it lists by name.  Its scan
  therefore *did* see `ParamRedex`.  It was a separate instrument (`/tmp/iotascan.lean`), not
  `Verify/Inductive/FlipPriceScan.lean`.
* `docs/handoff-iotahargs.md` **§5b** already measured the degeneracy at `MPWit.mpAux`, by name.

So the round I was asked to extend was **not** missing this witness; it had it, cited it, and had
already measured its degeneracy.  What *is* wrong is `docs/handoff-flipprice.md` §5b — an earlier,
different stream's doc — which says *"I have no witness for it at `np > 0`"*.  That sentence is
false, and `FlipPriceScan.lean`'s new header comment correctly flags it.  **The population defect
in `FlipPriceScan.lean` was real; the inference that it explains the (C) round's state is not.**

Consequence for how the task was framed: "a witness its own round did not have" was not the
situation.  The thing the round genuinely did not have — and this file supplies — is a **joint
instance of §4's 38 hypotheses at any witness at all** (its §5d says so in as many words).  That
was worth doing and it is what §1 above reports.

## 3. The degeneracy does NOT lift

Question 2 of my brief: *is the `instAll` window non-empty at `mpAuxB`?*  **No.**

* `mp_types_unindexed` (`decide`): `T.indices = []` at **both** members of `mpAux mpAuxNodeB`.
* `mp_ctorsAll_args_nil` (`decide`): `C.args = []` at **both** constructors.

So `IotaHargsGen` §2's `instAll` window is empty here exactly as at `ntreeAux`, and the round's
central limitation stands.  This is not new information — §5b of that handoff measured the
`indices` half at `MPWit.mpAux` already; the `C.args` half at `mpAux`'s two constructors is new,
and it confirms rather than lifts.  The only place the window is non-empty remains
`MRedex.TQWit.tqAux tqAuxNodeB` (`IndexedNested.lean`), which `IotaHargsGen` §6 already covers.

**Which of §3's twelve slots are at the empty window, and which are not** — stated separately
because the whole point of the exercise is not to let a degenerate coordinate pass as content:

| slot | at `mpAuxB`, `j = 1` | degenerate? |
| --- | --- | --- |
| `htele` | `mpIotaTele_node`; the ι-context **moves** (`mp_htele_nontrivial` = `mpIotaCtx_node_ne`) | no |
| `hOnp` | `onCtx_params_append` over `mpOnCtxIotaNode` — a 7-entry context, one entry a stored β-redex | no |
| `hbvT`, `hbvC` | `hasArgs_params_bvars_ctx` at `mpIotaGamma_split`; a real `np = 1` lookup at `bvars 6 1` | no |
| `hbodyT` | `mp_tyBody_hasType` (already in `ParamRedex.lean` §5.1) | no |
| `hbodyC` | `mpBetaN`'s right-hand typing at `k = 0` — the restored `MDep.node` head | no |
| `hpiC` | `mp_hpiC`; the `instAll` **moves** (`mp_hpiC_moves`) | no |
| `hAsC` | two `Lookup`s, the second at a **β-redex** domain (`mp_hAsC_second_is_redex`) | no |
| `hres` | `mp_hres`; index moves by `nf = 2` (`mp_hres_moves`) | no |
| `hidx` | `HasArgs.nil` — `T.indices = []` | **YES** |
| `hAsT` | `HasArgs.nil` — `C.args = []` | **YES** |
| `hpiT`, `hsortT` | `rfl` on a sort, because `AsT = []` | **YES** |

Nine of twelve carry content here; three sit at the empty window.  Compare `IotaHargsGen` §5, where
only `hfunM` was instantiated and `hidx` was the *only* slot: this is a strictly larger bound.

**Not degenerate in the other direction either**: §4's canonical `A₀` at this rule is `mpVc 6`
(`mp_A0_node`, `decide`), which is the `A₀` `mpIotaHargs_node` chose independently (read off
`ParamRedex.lean:2085`), and `v = .succ .zero` in both.  So §4's invented slots line up with the
witness at the second block too.

## 4. What remains of (C)

Question 3.  §4 being satisfiable at `mpAuxB` changes the residual list of
`docs/handoff-iotahargs.md` §6 as follows.

* **`hOnp`, `hbvT`, `hbvC`, `hpiT`, `hsortT`, `hres`, `hAsC`, `hpiC`** — no longer "available but
  never instantiated".  Every one of them was produced here from machinery already in the tree
  (`hasArgs_params_bvars_ctx`, `onCtx_params_append`, `mpBetaF`, `mpBetaN`, plus `decide` on closed
  data).  In particular **`hres` did not need the new lemma §8 item 1 of that handoff predicted**:
  at `C.args = []` it is `instAll (mpVc 8) (bvars 0 2) = mpVc 6`, one `decide`.  That prediction
  was explicitly flagged as a guess about difficulty; it is **untested still**, because the hard
  half of it (the `C.args` two-region rewrite) is exactly the half the empty window hides.  **Do
  not read this file as having closed §8 item 1.**
* **`hbodyT`, `hbodyC` — still the irreducible core.**  Here they came from `mp_tyBody_hasType`
  and `mpBetaN`, both hand-built at this witness from the two constant lookups.  Nothing general
  was found; `instAt_indep_of_tyArgs`' lower bound stands.
* **`htele` — unchanged.**  At this witness it is `mpIotaTele_node`, a hand proof.  In general it
  is still `iotaCtx_teleDefEq` + the (B) stream's two entry defeqs + `teleDefEq_fld_iota_of_fields`.
* **NEW: the own-member rules.**  §1a above.  (C) in general now needs *two* producers, and only
  one exists.

So the residual of (C) at `np > 0` after today: **`hargs` twice (`hbodyT`/`hbodyC`), `htele`,
`hidx`, and a second producer for the `j ∉ K` rules** — the last being new and cheap.  Everything
else has an instantiation at two parameterised blocks.

## 5. Verification record

* `lake build Lean4Lean.Theory.Inductive.IotaWit`: **77 jobs, exit 0**.  All **24**
  `#print axioms` lines: `[propext, Quot.sound]`, except `mp_ctorsAll_own_rule`,
  `mp_types_unindexed`, `mp_ctorsAll_args_nil` (no axioms), `mp_hAsC_second_is_redex`
  (`[propext]`), and `mp_iotaHargs_node_inhabited` / `mp_iotaRulesRS_wf_gen`
  (`[propext, Classical.choice, Quot.sound]`, inherited from `mp_stage₃_exists`).
* `lean_minimal_hypotheses` on `mp_iotaHargs_node_gen`: `henv` **load-bearing**.  The four constant
  lookups are section `variable`s (skipped by that tool) but all four are used — no
  "automatically included section variable(s) unused" warning was emitted for any declaration of
  mine.
* Environment scan (`/tmp/iotawitscan.lean`, importing `Verify.Soundness` + the nested cone
  **including `ParamRedex` and `IndexedNested`** — the import list is the thing that failed last
  time, so it is stated): declarations mentioning `VIndRestore.IotaHargs` went **8 → 10**, and
  those with it *in the conclusion* **6 → 8** (`mp_iotaHargs_node_gen` arity 6,
  `mp_iotaHargs_node_inhabited` arity **0**, `mp_hdata_gen` arity 10, plus the four pre-existing
  witnesses and `iotaHargs_of_heads`).  `mp_iotaHargs_node_inhabited` is the **first arity-0
  declaration in the tree with `IotaHargs` in its conclusion**.
* Layering: `grep -rln "^import Lean4Lean.Verify" Lean4Lean/Theory/` is **empty**.
* Frozen files (`Verify/Soundness.lean`, `Verify/Axioms.lean`, `Verify/Guard.lean`): not read for
  editing, not written, not `touch`ed.
* `tryEtaStructCore.WF` / `isDefEqUnitLike.WF` (ledger row 197): untouched, deliberately.
* My module is an orphan leaf (imported by nothing) and adds **no** holes.

### 5a. Foreign build state seen and not fixed

The first census run **failed** (`EXIT 1`) with
`object file … Theory/Inductive/NestedTele.olean … does not exist`, and reported four
`NOT BUILT` modules: `HargsShared`, `HypTrimWitness`, `NestedTele`, `TeleCongr`.  All four are
concurrent streams' (`git status`: `NestedTele.lean` and `RestoreBridge.lean` modified,
`HargsShared.lean` / `HypTrimWitness.lean` / `TeleCongr.lean` untracked).  `NestedTele.olean` was
transiently absent mid-rebuild and came back; the census was re-run.  **My module imports
`NestedTele` transitively (via `IotaHargsGen`), so if their edit breaks it my module stops
building — through no change of mine.**  See §5b for the re-run.

### 5b. Census re-run

`lake env lean --run scripts/sorry-census-all.lean`, exit 0:

* **HOLES over the whole built population: 13** (pass A 13, pass B 0) — the expected figure,
  unchanged by this file.  The thirteen are `TrProj.weak'_inv`, `inferProj.WF`,
  `isDefEqUnitLike.WF`, `tryEtaStructCore.WF`, `IsDefEqU.forallE_inv_stratified`,
  `IsDefEqU.weakN_iff`, `NormalEq.descend`, `WF.rigidShapeUniqNS`, `VIndRecArg.exists_indep`,
  `addDecl.WF`, `kernel_complete`, `kernel_sound`,
  `leanTT_equiconsistent_zfc_omega_inaccessibles`.
* `on disk: 416; in default-target population: 392; BUILT: 390; in population but **NOT BUILT: 2**`.
* The two `NOT BUILT` modules are **`Lean4Lean.Theory.Inductive.HypTrimWitness`** and
  **`Lean4Lean.Theory.Inductive.TeleCongr`** — both concurrent streams', both untracked, neither
  mine and neither touched.  `IotaWit` is in the built population (it appears in the pass-A module
  list).
* `scripts/dup-names.lean`: *"no duplicate Lean4Lean declarations across the joined cone"*.

### 5c. Measured vs read off

**Measured by me this session:** every `decide`/`rfl` in my file; the joint application of
`iotaHargs_of_heads` at `mpAuxB`/`j = 1` (it either elaborates or it does not, and it does); the
`hK` falsity at both blocks and `σ (MP) = none`; the own-member head identities at both blocks; the
`indices`/`args` degeneracy at `mpAux`; `lean_minimal_hypotheses` on `mp_iotaHargs_node_gen`; the
8 → 10 / 6 → 8 environment scan with the import list checked; the census, the layering check, the
duplicate-name check; that `docs/handoff-iotahargs.md` §1/§2/§5b already name `mpAuxB_hdata` and
already measured `MPWit.mpAux`'s degeneracy (§2 above).

**Read off source, not independently re-derived:** that `mpIotaHargs_node` chose `A₀ = mpVc 6` and
`v = .succ .zero` (I read `ParamRedex.lean:2085`; my `mp_A0_node` proves §4's `A₀` equals `mpVc 6`,
which is the machine half of the agreement); that `hK` is load-bearing *inside*
`substC_tyApp'_comp` (I read `NestedRules.lean:1758`, did not construct a counterexample to a
version without it); `rMaj_node_eq` and `mpMaj_obj_eq`'s ctor-head identities (quoted from
`ParamRedex.lean` §17.1 / `ConstSubstNested.lean`, not re-elaborated); `docs/handoff-flipprice.md`
§5b's wording.

**Guesses, flagged as guesses:** that the "second producer for `j ∉ K` rules" (§1a/§4) is cheap —
I measured that the two heads are *equal* there, but I did not write the producer, so "cheap" is a
prediction about effort, not a theorem.  Likewise everything relayed to me in my brief about what
yesterday's stream did or did not have is treated as claim, not fact, and §2 above is the check.

## 6. Pick up first

1. **The own-member producer** (§1a).  `iotaHargs_of_heads_own`, hypotheses `R.OwnId D K` and
   `T.name ∉ K` in place of `hK`, with `hconv`/`hmaj` supplied by `OwnId.tyAppR'_eq` /
   `.ctorAppR_eq` plus a sort derivation.  With it, §4 + the sibling would produce `hdata` for a
   whole block, which neither does alone.  It belongs in `IotaHargsGen.lean` (not mine).
2. **The same joint instance at `ntreeAux`, `j = 1`, `nlistNil`** — `handoff-iotahargs.md` §8
   item 2's target.  It is now a smaller job than that handoff thought, because the shape of every
   slot is settled by §3 above; the only new work is `hbodyC` for the restored `List.nil (NTree #0)`.
3. **§8 item 1's `instAll (e.liftN (n + d) n) (bvars 0 n) 0 = e.liftN d n` is STILL untested.**
   `C.args = []` at every witness in the tree except `MRedex.TQWit.tqAux tqAuxNodeB`, so the
   two-region `hres` rewrite has no witness anywhere.  If someone wants that lemma exercised, the
   `tqAux` block is the only place, and §4's `hres` there is where to put it.
4. **`docs/handoff-flipprice.md` §5b needs a correction note** (it says (C) has no `np > 0`
   `IotaHargs` witness; there are three: `ntreeAux_hdata_of_rest`, `mpAuxB_hdata`, and now
   `mp_iotaHargs_node_inhabited`).  I did not edit it — not my file.
5. **Do not** close `tryEtaStructCore.WF` / `isDefEqUnitLike.WF` (ledger row 197), and **do not**
   make the flip.

## 7. The flip

Not made, not attempted, and (C) is **not** discharged in general — §4 above is the residual and it
still contains `hargs` twice plus `htele` plus a producer that does not exist.  Per my brief this
is the orchestrator's to sequence with the user, and I am stopping here.

