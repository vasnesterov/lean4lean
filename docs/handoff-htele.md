# Handoff: `htele` — and obligation (C) at BOTH parameterised blocks from general producers

**Written 2026-09-03**, on top of `2c57077`.
My files (all new, all mine):

| file | lines | contents |
|---|---|---|
| `Lean4Lean/Theory/Inductive/HTeleNTree.lean` | 456 | `IotaHargsGen` §4 at the canonical block's two companion rules; obligation (C) there, arity 0 |
| `Lean4Lean/Theory/Inductive/HTeleGen.lean` | 420 | `htele` in general; (C) at a whole block from (B)'s entry defeqs; deliberately `RecTyped`-free |
| `Lean4Lean/Theory/Inductive/HTeleRecB.lean` | 221 | the last link: (B)'s entry defeqs from (B)'s **data** families |

`lake build` of the three: **82 jobs, exit 0, zero `unusedSectionVars` warnings**.
Nothing else was edited. **The flip was not made.** `Verify/Soundness.lean`, `Verify/Axioms.lean`,
`Verify/Guard.lean`: not read for editing, not written, not `touch`ed (`git status --short` on the
three is empty).

## 0. Grading discipline

Every `#print axioms` line is **hole-freeness and nothing else** (`docs/vacuity-ledger.md` §0).
Content claims are stated separately with the witness named; where a hypothesis set is not known
jointly satisfiable I say so (§4b below). A reduction is graded as a reduction.

## 1. Result

**Outcome 1's second half is done; its first half is done modulo obligation (B)'s data.**

| | before | after |
|---|---|---|
| `IotaHargsGen` §4 instantiated at `ntreeAux` | **never** | at **both** companion rules |
| (C) at `ntreeAux` with no hand ι-witness | no | **yes** (`ntree_iotaRulesRS_wf_all_gen`, arity 0) |
| (C) at `MRedex.MPWit.mpAux` with no hand ι-witness | yes (`mp_iotaRulesRS_wf_own_gen`) | yes |
| (C) at a whole block from (B)'s data + companion heads | no | **yes** (`hdata_of_recHargs_and_heads`) |
| (C) at `ntreeAux` from (B)'s three data families alone | no | **yes** (`ntree_obligationC_of_recHargs`) |
| `htele` a separate obligation from (B)'s | assumed | **refuted** — see §3 |

So **obligation (C) now holds at both parameterised nested blocks in the tree through general
producers only**, and in general it asks for nothing that obligation (B) does not, except one extra
instance of a family (B) already has plus the companion-rule head data.

## 2. Job 2 — `IotaHargsGen` §4 at the canonical block (`HTeleNTree.lean`)

`docs/handoff-iotahargs.md` §8 item 2 and `docs/handoff-ownrule.md` §5 both name this as open.

* **`VIndRestore.IotaHeadHargs`** (§2) bundles §4's **twelve non-`htele` hypotheses**
  (`hidx`, `hOnp`, `hbvT`, `hbodyT`, `hpiT`, `hAsT`, `hsortT`, `hbvC`, `hbodyC`, `hpiC`, `hAsC`,
  `hres`), existentially quantifying the six shape witnesses, and `iotaHargs_of_headHargs` restates
  §4 over it. The split is what lets `htele` come from a *different* source, which is what
  `HTeleGen.lean` §2 needs.
* **§2a: the bundle is inhabited at both companion rules** — `n_headHargs_nil`,
  `n_headHargs_cons`, each from the five `F₃` constant lookups plus `F₃.Ordered`. All six
  hypotheses load-bearing (`henv` by `lean_minimal_hypotheses`; `hnode` checked by hand — dropping
  it from `n_headHargs_nil`'s `include` fails, because it enters through `rOnCtx`).
* **§2b**: `n_iotaHargs_nil_gen`, `n_iotaHargs_cons_gen` — `IotaHargs` at both, through §4.
* **§3**: `n_hdata_all_gen` (own rule from `OwnRule` §3, companions from §2b) and
  **`ntree_iotaRulesRS_wf_all_gen` (arity 0)** — obligation (C) at the canonical block with **no
  hand ι-witness anywhere**. `rIotaRest_nil` / `_cons` / `_node` are all now unused by this route.

## 3. Job 1 — `htele` in general (`HTeleGen.lean`, `HTeleRecB.lean`)

`VInductDecl'.iotaCtx_teleDefEq` (§T15.4) already splits `htele` into `hmot`, `hmin`, `hfld`, and
its own docstring says `hmot`/`hmin` are *"literally the same hypotheses"* as (B)'s entry defeqs.
The one thing that was not identified is `hfld`, and it is:

> **(C)'s field block is obligation (B)'s field-block defeq at `q = D.nmin`.**
> (B) asks for `MinorFldDefEq q C` at each minor index `q < D.nmin`; (C) asks for the *same
> predicate* at `q = D.nmin`, where `List.take D.nmin` is the whole minor block.

`VIndRestore.teleDefEq_fld_iota_of_minorFld` (`HTeleGen.lean` §1) is that identity: one
`List.take_of_length_le` and two `VExpr.map_substC_liftTele`, so `σ.Closed` and nothing else. It is
a genuinely **new index**, not one of (B)'s (`n_minorFld_iota_ne_own`, `n_ctorsAll_length`), and it
is **inhabited at the canonical block at all three ι-rules** (`n_minorFldI_all`): free at
`nlistNil`, whose field block is empty, and one `rbetaL` each at `ntreeNode` and `nlistCons` — the
same β step `rIotaTele_node` performs.

Then the two closures:

* `VIndRestore.hdata_of_entries_and_heads` (`HTeleGen.lean` §2) — `hdata` at a whole block from
  (B)'s two **entry defeq** families, the `q = D.nmin` field defeq, and `IotaHeadHargs` at the
  **companion** rules. No `σ.WF`, no `hp : D.params = []`, no `hcl0`, no bound on `D.np`.
* `VIndRestore.hdata_of_recHargs_and_heads` (`HTeleRecB.lean` §2) — the same from (B)'s **data**
  families, by deriving the entry defeqs through `RecTyped.lean`'s `motiveEntry_defeq_of_hargs` /
  `minorEntry_defeq_of_hargs` and their free off-`K` siblings.
* Instantiated: `ntree_obligationC_of_entries` (arity 2) and `ntree_obligationC_of_recHargs`
  (arity 3) — **obligation (C) at the canonical block from (B)'s three data families alone.**

**(B)'s fourth family, `RecBodyHargs`, is not needed** — (C)'s telescope is `iotaCtx`, which has no
recursor-body entry (`n_iotaCtx_has_no_body_entry`, `rfl`). So the count is: (B) uses four data
families, (C) uses three of them plus one extra instance of one of them plus the companion heads.

## 4. Anti-vacuity, stated apart from hole-freeness

### 4a What is measured

* The bundle inhabitations of §2a are *joint*: all twelve slots at once, at each of two rules.
* `ntree_iotaRulesRS_wf_all_gen` is **arity 0** — the seven staging environments come from
  `ntree_stage₃_exists`, so nothing is assumed.
* The degeneracy, **re-measured rather than cited**, as the brief demanded:
  `n_companion_unindexed` (`(ntreeAux.types.getD 1 default).indices = []`), `n_nil_args_nil`,
  `n_cons_args_nil`, `n_window_empty`. So four of §4's twelve slots (`hidx`, `hAsT`, `hpiT`,
  `hsortT`) sit at an **empty** `instAll` window here, exactly as at `MRedex.MPWit.mpAux`.
* The eight that are **not** degenerate: `n_np_pos` (`np = 1`, so `hbvT`/`hbvC` are real parameter
  lookups and not `HasArgs.nil`), `n_hpiC_cons_moves`, `n_hres_cons_moves`, `n_hAsC_needs_beta`,
  and `n_hres_nil_identity` (disclosed as the `nf = 0` identity, not claimed as content).
* For §3's field defeq: `n_minorFldI_node_moves`, `n_minorFldI_cons_moves` (the blocks really move)
  and `n_minorFldI_nil_trivial` (the `nlistNil` one does not) — bounded on both sides.
* `n_hmot_offK_branch_reached` — §2's `hmot`/`hmin` really reach their off-`K` branches at this
  block, so it is not the vacuous `∈ K`-for-all-types version `RecTyped.lean` §6a refutes.

### 4b What is NOT established

* §2's and §3's hypothesis sets are **not known jointly satisfiable at `D.np > 0`**: at
  `T.name ∈ K` the entry defeqs / data families are the open `hargs` obligation, inhabited nowhere
  at `D.np > 0` (`RecTyped.lean` §6c; `VIndRestore.instAt_indep_of_tyArgs`). Grade
  `hdata_of_entries_and_heads`, `hdata_of_recHargs_and_heads`, `ntree_obligationC_of_entries` and
  `ntree_obligationC_of_recHargs` as **hole-free, composed end to end, inhabitation of the data
  families unknown**.
* `IotaHeadHargs` has **no general producer**. §2a is a witness inhabitation at one block; the
  `MRedex.MPWit` components (`IotaWit.lean` §3) are the other. Neither is general.
* The general `htele` route is **weaker at both witnesses** than what the tree already had — see
  §5.1.

## 5. Where the brief and the previous handoffs are wrong

This is the part worth reading.

### 5.1 `htele` is not the last residual — it was already proved at both witnesses

The brief says *"`htele` is [the own-member producer's] entire residual … Attack it"* and offers as
outcome 2 *"`htele` proved at the canonical block"*. **`htele` has been proved at the canonical
block since before this round, at all three ι-rules**: `InductiveDeclExamples.rIotaTele_nil`,
`rIotaTele_node`, `rIotaTele_cons` (`Theory/Typing/ConstSubstNested.lean` §J.3, from five constant
lookups and nothing else), and at the second parameterised block `MRedex.MPWit.mpIotaTele_obj` /
`_node`. `OwnRule.lean` §4 *itself passes `rIotaTele_node` as `htele`* — the brief's own source
document says so (`docs/handoff-ownrule.md` §4: *"`htele` from §J's `rIotaTele_node`"*). So outcome
2's first half was not an available outcome; the only live target was `htele` **in general**, which
is what §3 above does.

### 5.2 The "nine concrete conversions, all of which move" is not `htele`, for the second time

`docs/handoff-iotahargs.md` §1 already corrected this once: there are two different nines —
route 2's nine *rule components* (`type`/`lhs`/`rhs` × 3, `ntree_iota_components_ne`) and route 1's
nine `IotaHargs` *pieces* (`hfunM`/`hconv`/`hmaj` × 3, of which `rMaj_node_eq` is an identity).
**Neither is `htele`.** `htele`'s own measurement is §J's table: of `ntreeAux`'s three ι-contexts
(lengths 8, 6, 8) the entries that move are **5, 4, 5**, the first six entries of all three are
literally `rTele`/`rTeleR`, and the nil rule's ι-context *is* §E's recursor telescope on the nose
(`rIotaCtx_nil_eq`). So `htele` at this block costs `rTeleDefEq` plus **one β step per constructor
that has fields** — which is exactly what §J.3 pays. The brief's warning not to *"mistake the
discount for the work"* applies to itself here: the previous round's `rMaj_node_eq` finding was
about `hmaj`, and quoting it against `htele` is a third mis-attribution of the same measurement.

### 5.3 "only `hbodyC` is new" — right at `nlistNil`, wrong at `nlistCons`

The brief flags this as *"its estimate, not a measurement"*. Measured, and it is half right:

* At **`nlistNil`** (`nf = 0`) the estimate holds: `AsT = AsC = []`, `hpiC`/`hres` are the `nf = 0`
  identities, and the only content is `hbodyT`/`hbodyC`.
* At **`nlistCons`** (`nf = 2`) three further slots carry content: `hpiC` moves
  (`n_hpiC_cons_moves`), `hres` moves (`n_hres_cons_moves`), and — the one that is not just
  arithmetic — **`hAsC` needs a β conversion**. The ι-context declares the second field at the
  *stored* type `rV #7`; §4's `AsC` presents it at the *restored* `List (NTree #7)`, and those are
  different terms (`n_hAsC_needs_beta`), so the `HasArgs.cons` step is
  `.defeqDF (rbetaL …) (.bvar .zero)` and not a bare `Lookup`. **`MRedex.MPWit`'s instantiation did
  not exercise this**: `mp_hAsC_second_is_redex` records that there the second `AsC` entry *was*
  the context entry syntactically. So the canonical block is not a re-run of that one.

### 5.4 `hbodyT`/`hbodyC` are not "the irreducible core" at any witness

`docs/handoff-iotahargs.md` §6's table calls them *"genuinely data … the irreducible core, for (B)
and (C) alike"*. At the canonical block they are **discharged outright**, and the reason is
structural: the restored companion heads are `List` and `List.nil` / `List.cons` from the
*pre-existing* `listDecl`, so `n_hbodyT` / `n_hbodyC_nil` / `n_hbodyC_cons` are one `constDF` and
one `appDF` each (`n_tyBody_is_stored_const` shows the head). The same is true at
`MRedex.MPWit.mpAux` (`mp_tyBody_hasType`, `mpBetaN`). "Irreducible" is a claim about the general
case; at **every** parameterised witness in the tree it is paid.

### 5.5 `docs/handoff-ownrule.md` §5 and `docs/handoff-iotahargs.md` §5d are now out of date

* *"at `ntreeAux` `hdata` does not yet follow from the two general producers alone"* — true when
  written, **false now** (§2 above).
* *"Grade §4 as hole-free, shape-checked, inhabitation unknown"* — now inhabited at **two blocks**
  and, at the canonical one, at **two rules of different shape**.
* `docs/handoff-iotahargs.md` §6's row *"`htele`'s `hmot`, `hmin` — (B)'s, verbatim"* is right; its
  neighbouring row for `hfld` (*"reduced to `hargs`"* via §T16.1) is right but misses the cheaper
  identification: `hfld` is (B)'s `MinorFldDefEq` **at one more index**, so it needs no separate
  producer chain at all.

### 5.6 A vacuity I nearly shipped, caught by instantiating

My first draft of the general producer used **one** environment variable where (B)'s producers use
**two**: `motiveEntry_defeq_of_hargs` takes `henv`/`hD`/`hfresh` at the *pre-block* environment and
`hsrc`/`hσ` at the *staging pair*. Conflating them makes the theorem uninstantiable at `ntreeAux`,
where the pre-block env is `env₁` and the ι-stage source is `E₃` — a clean axiom line over an empty
hypothesis set. It was caught by trying to instantiate, not by reading. `ntree_recConsts_wf₃`
(`HTeleRecB.lean` §3) is the bridge the split then needs: `ntree_recConsts_wf` is stated at `E₂`,
and `VEnv.addIndRecs_le` moves it to `E₃`.

### 5.7 Cross-stream: `TeleCongr.lean`'s note about my file is already stale

`Theory/Inductive/TeleCongr.lean`'s header says `MinorCtorHargs` *"still carries `hAs` as a
conjunct, because deleting it from the definition ripples into `Theory/Inductive/HargsShared.lean`
and `Theory/Inductive/HTeleGen.lean`, which destructure it."* As of this round **`HTeleGen.lean`
does not destructure it** — it is deliberately `RecTyped`-free (§6). The destructuring lives in
`HTeleRecB.lean`, and **I have no objection to `hAs` being dropped**: adapting that file is two
lines. `HargsShared.lean` is not mine.

## 6. Foreign build failures seen and not fixed, per instruction

* **`Theory/Inductive/RecTyped.lean` was mid-edit.** For a stretch of this session
  `VIndRestore.MinorCtorHargs` was a three-component `∃ B` while
  `VEnv.recConstsR_wf_of_recHargsD` at `:996` still destructured
  `⟨As, B, B', hcbody, hpi, hAs, hfun⟩`, so the module did not elaborate and everything importing it
  was blocked. It compiles again now (seven components). An earlier draft of `HTeleGen.lean`
  imported it and was blocked; I dropped the import and restated (B)'s two entry families in the
  shape `iotaCtx_teleDefEq` binds, so **`HTeleGen.lean` cannot be broken by that file**.
  `HTeleRecB.lean` is the only file of mine that imports it, and it is the one that will break if
  their API moves again. That is a deliberate blast-radius decision, recorded in both files.
* **`Verify/Inductive/RestrictCompanion.lean:320–323`** fails at the end of the session
  (`Type mismatch`, `Application type mismatch`, `subst failed`) — the `Verify/Inductive/Restrict*`
  stream's file, and it is the census's single `NOT BUILT` module. Untouched.

## 7. Verification record

* `lake build` of my three modules: **82 jobs, exit 0**;
  `grep -c "automatically included section variable"` over that log: **0** (baseline for the whole
  tree is 20; the final full build printed 18 before stopping at the foreign failure above).
* All 47 `#print axioms` lines across the three files: hole-free.
  `[propext, Quot.sound]` for most of the syntactic and `decide` results; `[propext]` alone for the
  three typing lemmas of `HTeleNTree` §1, `n_companion_unindexed` and `n_iotaCtx_has_no_body_entry`;
  plus `Classical.choice` for everything downstream of `VInductDecl'.ctorApp'_hasType`
  (pre-existing, not introduced here).  `n_np_pos`, `n_hbv_spine_ne_nil` and `n_ctorsAll_length`
  depend on no axioms at all.
* Declaration names read off each file's own `namespace` lines, never composed from the path.
* `lake env lean --run scripts/sorry-census-all.lean`: **HOLES 13**. `BUILT: 405`;
  `in population but NOT BUILT: 1` — `Lean4Lean.Verify.Inductive.RestrictCompanion`, foreign.
* `scripts/dup-names.lean`: *"no duplicate Lean4Lean declarations across the joined cone"*.
* Layering: `grep -rln "^import Lean4Lean.Verify" Lean4Lean/Theory/` is **empty**.
* Frozen files: `git status --short` on `Verify/Soundness.lean`, `Verify/Axioms.lean`,
  `Verify/Guard.lean` is empty; none was written or `touch`ed.
* My three files are orphan modules (imported by nothing outside themselves), as new leaves should
  be. `TeleCongr.lean` names `HTeleGen.lean` in a docstring only.
* **The flip was not made**, and (C) is **not** discharged in general: it now reduces to obligation
  (B)'s data families plus `IotaHeadHargs` at companion rules, and neither is inhabited at
  `D.np > 0`. The census is still 13.
* `tryEtaStructCore.WF` and `isDefEqUnitLike.WF` (ledger row 197): untouched.

### 7a Measured vs read off

**Measured by me this session:** every axiom line, arity and job count above; every `decide` in
`HTeleNTree` §0/§0b/§4 and `HTeleGen` §3/§5d; the twelve-slot joint inhabitation at both companion
rules; that `hnode` is load-bearing for `n_headHargs_nil` (by deleting it from the `include` and
watching it fail); `lean_minimal_hypotheses` on `n_headHargs_nil`/`_cons` (it grades only explicit
binders — the five constant lookups are section variables, so `henv` is the only verdict it
returns, and I say so rather than claiming five); the ambient context of the `q = D.nmin` field
defeq being `rTele.reverse` at this block; the census, dup-names and layering checks; the two
foreign failures of §6, including the exact line and the mismatch that caused the `RecTyped` one.

**Read off source, not independently re-run:** that `rIotaTele_*` and `mpIotaTele_*` are `htele`
at the two blocks (I read their statements — but I also *use* `rIotaTele_nil`/`_cons` in
`HTeleNTree` §2b, so at the canonical block this is composed rather than read); §J's
moving-entry table (read from the docstring, not re-`#eval`ed); `VIndRestore.instAt_indep_of_tyArgs`
as the lower bound on `hargs`; `TeleCongr.lean`'s header note.

## 8. Pick up first

1. **A general producer for `IotaHeadHargs`.** This is now the only (C)-specific residual, and it is
   the head data at the *ι-rule's* context rather than at a motive/minor entry's. `IotaHargsGen`
   §4's own hypothesis list is the target shape; two witness inhabitations exist (`HTeleNTree` §2a,
   `IotaWit.lean` §3). Whether it reduces to (B)'s `MotiveHargs`/`MinorCtorHargs` by a weakening is
   **not** measured — the contexts differ by the field block, and `hbody_weak` (§T11) is the lemma
   that would do it if the subject is closed at `D.np`. That is the next honest question.
2. **(B)'s data families** — unchanged as the bottom of both obligations. Nothing in this round
   moves them.
3. **Do not** re-attack `htele`: §5.1/§5.2 above. At both witnesses it is proved; in general it is
   `iotaCtx_teleDefEq` plus §1's index shift, and both halves are in the tree now.
4. **Do not** close `tryEtaStructCore.WF` / `isDefEqUnitLike.WF` (ledger row 197), and **do not**
   make the flip.
