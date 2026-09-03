# Handoff: `IotaHargs` — obligation (C) at `D.np > 0`, and what is left of it

**Written 2026-09-03**, on top of `9f8b1f4`, from the brief that `docs/handoff-flipprice.md` §8
item 1 sets: *"discharge `R.IotaHargs` — the only remaining input to
`VEnv.iotaRulesRS_wf_of_hargsD_of_barrier`."*

My file: `Lean4Lean/Theory/Inductive/IotaHargsGen.lean` (new, mine, 76 jobs, exit 0).
Nothing else was edited. **The flip was not made** and is not mine to make.

## 0. Grading discipline

Every `#print axioms` line below is **hole-freeness and nothing else** (`docs/vacuity-ledger.md`
§0). Where I claim content I say separately *what was measured* and *at which witness*, and
where a hypothesis set is **not** known jointly satisfiable I say that too — §5 is that list.
A reduction is not a discharge; §4 of the file is a reduction and I grade it as one.

## 1. The headline correction: the brief's target was already in the tree

I was told the task was *"(C)'s `IotaHargs` — nine concrete conversions at `ntreeAux`, all of which
move, and the reduction around them is free"*, with outcome 2 being *"some of the nine conversions
proved, the rest with the specific obstruction named"*.

**All nine were already proved before this stream started, and at a second parameterised witness
too.** Measured, not read off:

* `InductiveDeclExamples.rIotaRest_node` / `_nil` / `_cons` (`NestedTele.lean` §T16.15) are the
  three `∃ A₀ v` triples, hole-free, and `ntreeAux_hdata_of_rest` (arity 13) assembles them with
  §J's three `htele` into `hdata` — which is why `ntreeAux_obligationC` has **arity 0**.
* `MRedex.MPWit.mpIotaHargs_obj` / `_node` (arity 5 each, `ParamRedex.lean` §17.2) do the same at
  the **non-canonical parameterised redex block**, and `mpAuxB_hdata` (arity 9) assembles them.
  The brief named only `ntreeAux`; there are **two** parameterised witnesses with `IotaHargs`
  discharged, and the second one is the harder shape (a stored redex).

So outcome 2 was unavailable as an outcome: the only live target was `IotaHargs` **in general**,
which is what §3–§4 of my file do.

Two further corrections to what I was relayed, both checked:

* **"all of which move, so no `rfl` discount applies"** conflates two different nines.
  `ntree_iota_components_ne` (`ConstSubstNested.lean:2727`) is about route **2**'s nine *rule
  components* (`type`/`lhs`/`rhs` × 3 rules) and yes, all nine move. Route **1** — the `IotaHargs`
  route, the one the brief points at — has a different nine (`hfunM`/`hconv`/`hmaj` × 3 rules), and
  `rMaj_node_eq` (`:3028`, `decide`) says **`hmaj` at `NTree.node` is an identity**: the two sides
  are literally equal. So a `rfl` discount *does* apply to one of route 1's nine, and
  `NestedTele.lean` §T16.14's own docstring already says so ("one is measured free").
* **"the reduction around them is free"** is true of `iotaRulesRS_wf_of_components` (no environment
  hypotheses) and false of the route actually used at `np > 0`:
  `VEnv.iotaRulesRS_wf_of_hargsD` carries `hσ : WFD`, `hI : D.IotaCtx`, `henv : e₃.Ordered`,
  `hσc`, `hpos` and the name discipline. `handoff-flipprice.md` §5b says this correctly
  ("reductions, not discharges"); the brief's phrasing drops it.
* `handoff-flipprice.md` §6's residual table calls (C)'s residual *"a `TeleDefEq` on the ι-context
  plus **three typed conversions**"*. Measured: `IotaHargs` is `htele` + **one typing** (`hfunM`, a
  `HasType`) + **two** conversions (`hconv`, `hmaj`). After §3 below, `hfunM` is not a residual at
  all, so the table over-counts by two.

## 2. Environment facts (structural query, not grep)

Run over the **compiled** environment (`/tmp/iotascan.lean`, a copy of
`Verify/Inductive/FlipPriceScan.lean`'s method extended to report whether the name occurs in the
*conclusion* or only in a hypothesis; it imports `Verify.Soundness` + the nested cone, so it sees
`Verify/` too — which is why it lives outside `Theory/` and not in my file: the layering rule).

Before my file: **8** declarations mention `VIndRestore.IotaHargs`. Of the four with it in the
**conclusion**, all four are at witnesses (`mpIotaHargs_obj`, `mpIotaHargs_node`, `mpAuxB_hdata`,
`ntreeAux_hdata_of_rest`); the other four are consumers (`iotaRulesRS_wf_of_hargsD` and the three
reductions built on it). **So there was no general producer of `IotaHargs` in the tree** — an
environment fact, not a grep.

After my file: **9**, the new one being `VIndRestore.iotaHargs_of_heads` (arity 38), the first with
`IotaHargs` in the conclusion and no witness in its statement.

## 3. Proved: `hfunM` is derived, not stated — §T16.10's named gap, closed

`NestedTele.lean` §T16.10 lists (C)'s residual and says of the third item:

> `hfunM` — §T8's motive-partial application… §T8 shows it is `hmot` + `hidx`, not data; what §T16
> does not do is the domain identification (`tyApp'_instAll'`, the step `recApp_partial_hasType`
> performs internally), so `hfunM` is **stated, not derived**.

It is now derived. Four declarations, all `[propext, Quot.sound]` except the first:

| declaration | arity | axioms | what it is |
| --- | --- | --- | --- |
| `VExpr.substC_instAll` | 5 | `[propext]` | `substC` through `instAll`. **Absent from the tree**: `substC_liftN` and `substC_inst` (`Theory/Typing/ConstSubst.lean:124/139`) existed, the iterated form did not |
| `VInductDecl'.tyApp'_substC_instAll` | 10 | `[propext, Quot.sound]` | §T16.10's `tyApp'_instAll'`: `VInductDecl'.tyApp'_instAll` (`Lemmas.lean:1461`) one `substC` out. Three rewrites; `σ.Closed` is the only non-arithmetic hypothesis; no `np` bound, no environment |
| `VInductDecl'.lookup_motive_iotaCtx_substC` | 5 | `[propext, Quot.sound]` | `hmot` **at the ι-rule context**, derived from `lookup_motive_substC` at `Δ := fields ++ minors`, `Γ₀ := params`. So `hmot` was not a residual either |
| `VIndRestore.iotaHargs_hfunM` | 11 | `[propext, Quot.sound]` | **`IotaHargs`' `hfunM` from `hidx` alone.** No environment hypothesis, no `np` bound |

`lean_minimal_hypotheses` on `iotaHargs_hfunM`: **all five explicit hypotheses load-bearing**
(`hσ`, `hT`, `hj`, `hlen`, `hidx`) — no dead premise.

## 4. Reduced (not discharged): `IotaHargs` assembled

`VIndRestore.iotaHargs_of_heads`, arity **38**, `[propext, Quot.sound]`. It produces
`R.IotaHargs D σ e j C` from

* `htele` — §T15.4's telescope defeq, taken as a hypothesis;
* the **two `hargs` bundles**, i.e. `substC_tyApp'_defeq_tyAppR'_comp` and
  `substC_ctorApp'_defeq_ctorAppR_comp`'s inputs at the ι-rule's own context
  (`hOnp`, `hbvT`/`hbvC`, `hbodyT`/`hbodyC`, `hpiT`/`hpiC`, `hAsT`/`hAsC`, `hsortT`);
* `hidx` — §3's one datum;
* `hres` — the constructor's result identification, `instAll BC' (bvars 0 nf) = A₀`.

It fixes `A₀ := D.tyAppR' R j (D.nm + D.nmin + C.fields.length) …`, the *contracted* head, which is
what makes `hconv` the type-head defeq read backwards (`.symm`) and `hmaj` the constructor-head
defeq with its type moved by `hres`.

**This is a reduction, and `hfunM` is the only thing it removes from §T16.10's list.** It is worth
having because it says nothing *else* is needed: in particular no `hσ`, no `Ordered`-after-
substitution, and no bound on `D.np`.

## 5. Anti-vacuity, stated separately from hole-freeness

### 5a. §3 is jointly inhabited at `ntreeAux` — and reproduces the hand proof

`InductiveDeclExamples.rIotaRest_nil_gen` / `_cons_gen` / `_node_gen` (arity 4 each) are
`NestedTele.lean` §T16.15's three triples with **the `hfunM` component replaced by §3's general
derivation** and `hconv`/`hmaj` left exactly as the witness has them. They typecheck, so §3's
conclusion is the shape the hand proof needed, and its five hypotheses hold simultaneously at a
real parameterised nested block (`ntree_hfunM`, arity 5: the only inputs are
`ntree_csubst_closed`, two `decide`s and `HasArgs.nil`).

### 5b. …but that inhabitation is degenerate in one coordinate, and I say which

**Measured** (`ntree_types_unindexed`, `ntree_ctorsAll_args_nil`, both `decide`; and
`IndexedNested.lean`'s `tq_cone_unindexed`): every type of `ntreeAux`, of `MPWit.mpAux` and of
`MRWit.mrAux` has `T.indices = []`, and all three `ntreeAux` constructors have `C.args = []`. So at
every witness that had `IotaHargs` before today, `hidx` is `HasArgs.nil` and §2's `instAll` window
is **empty**. §5a therefore bounds §3 from below only in the `ni = 0` direction.

### 5c. §2's `ni > 0` content, at the one indexed parameterised nested block

`MRedex.TQWit.tqAux tqAuxNodeB` (`Theory/Inductive/IndexedNested.lean`) has `np = 1`, `ni = 1` at
both members and `tqObj.args = [Prop]`. Four new declarations there (§6 of my file):

* `tq_csubst_closed` — §2's only non-arithmetic hypothesis, proved (via `csubst_closed` +
  `tq_tyArgs_closedNp`, both new);
* `tq_tyApp'_substC_fires` (`decide`) — the substitution really fires at the companion member, so
  §2 is **not** `tyApp'_instAll` in disguise;
* `tq_tyApp'_window_moves` (`decide`) — the lifted substituted domain is not already the answer, so
  the `instAll` step is not an identity;
* `tq_tyApp'_substC_instAll_decide` (`decide`) — the equation itself at `j = 1`, `ni = 1`, `K = 3`,
  `as = [Prop]`, confirmed by kernel computation **independently of §2**; and
  `tq_tyApp'_substC_instAll_gen` derives the same equation *through* §2, so §2's hypothesis set is
  inhabited at `ni > 0`.

### 5d. §4's hypothesis set is NOT known to be jointly satisfiable

What **is** measured (§7 of my file, all `decide`):

* `ntree_A0_nil_eq` / `_cons_eq` / `_node_eq`: §4's canonical `A₀` is **exactly** the `A₀` each of
  the three hand proofs chose independently (`.app rLt (.app rNt (.bvar 5))`,
  `… (.bvar 7)`, `.app rNt (.bvar 7)`). So §4's `hconv`/`hmaj` slots are stated at the types the
  witnesses satisfy — this is the check that would have caught a wrong offset in `k`.
* `ntree_hres_satisfiable`: `hres` holds at all three rules with `BC'` the `A₀` lifted over the
  field telescope, which is the `B'` that `instAt_ctor_hpi` computes.

What is **not** checked, at any witness: `hOnp`, `hbvT`, `hbvC`, `hbodyT`, `hbodyC`, `hAsT`,
`hAsC`, `hpiT`, `hpiC`, `hsortT`, `htele`. I did not build a single simultaneous instance of §4.
**Grade §4 as "hole-free, shape-checked, inhabitation unknown."** §6 below is where each of those
comes from, and none of them is refuted anywhere I could find — but "not refuted" is not
"inhabited", and this is exactly the gap ledger rows 195/199b/201 are about.

## 6. What still blocks (C) in general, and where each piece comes from

After §3, the residual of `VEnv.iotaRulesRS_wf_of_hargsD_of_barrier` is:

| piece | status | source |
| --- | --- | --- |
| `hidx` | data (D-series) | `VIndCtor.WF.args_ty` + `HasArgs.substCD` (§T1a). One `HasArgs`, no β content |
| `htele`'s `hmot`, `hmin` | **(B)'s, verbatim** | `iotaCtx_teleDefEq`'s docstring: *"Same two middle blocks as (B) — literally the same hypotheses, so one pair of entry defeqs serves both obligations"*. The concurrent (B) stream's `Theory/Inductive/RecTyped.lean` has `motiveEntry_defeq_of_hargs` (`:306`) and `minorEntry_defeq_of_hargs` (`:384`) — **(C)'s `htele` is two thirds done in a file I do not own** |
| `htele`'s `hfld` | reduced to `hargs` | `substC_atRec_canonType_defeq` (§T16.1) + `teleDefEq_fld_iota_of_fields` (§T16.6) |
| `hOnp` | available, but only over `WFD` | `iotaCtx_substC_onCtxD` (§T15.4) + `onCtx_params_append` (§T9) + `onCtxParamsAtRec_substCD`. **The `σ.WF` version is refuted at the ι-stage** (`ntree_csubst_WF₃_false`), so the `WFD` one is required — and `RecTyped.lean:87` already has `VInductDecl'.onCtxParamsAtRec_substCD`. I did **not** add a second copy (grep-then-scan caught it; a duplicate would have been the fourth such incident in this repo) |
| `hbvT`, `hbvC` | no data | §T6.1's `hasArgs_params_bvars_ctx` — a context split, `hasArgs_params_bvars_minorCtx'` is the same shape one block over |
| `hpiC` + `hres` | reduced to `instAt_ctor_hpi` + one de Bruijn identity | `instAt_ctor_hpi` (§T10) gives `AsC = instAllTele (atRecTele (C.fieldTypesR D R)) (bvars k np) 0` and `BC' = instAll (tyAppR' R j nf (atRecTele C.args)) (bvars k np) nf`. `hres` then needs exactly `instAll (instAll (tyAppR' R j nf (atRecTele C.args)) (bvars k np) nf) (bvars 0 nf) 0 = tyAppR' R j (nm+nmin+nf) ((C.args.map fun a => (atRec a).liftN (nm+nmin) nf).map (substC · σ))` — two nested `instAll`s plus the σ-identity on `C.args`. **Not attempted**; §8 item 1 decomposes it, and it is *two* pieces, not one |
| `hpiT`, `hsortT` | shape facts | the companion's stored *type* is only definitionally canonical (F1), which is why §T10 says the ctor head's `hsplit` is a theorem and the type head's is not |
| `hbodyT`, `hbodyC` | **genuinely data** | §8.7's `hargs`; `instAt_indep_of_tyArgs` (`NestedRules.lean:1582`) says no restoration-independent argument can produce it. This is the irreducible core, for (B) and (C) alike |

So the honest summary of (C) at `np > 0` after today: **one datum (`hargs`, twice), one D-series
datum (`hidx`), `hpiT`/`hsortT`/`hres` as shape identities, and `htele` — whose two harder thirds
are the concurrent (B) stream's `motiveEntry_defeq_of_hargs` / `minorEntry_defeq_of_hargs`.**
`hfunM` and `hmot` are off the list.

## 7. Verification record

* `lake build Lean4Lean.Theory.Inductive.IotaHargsGen`: **76 jobs, exit 0**. All eighteen
  `#print axioms` lines in §8 of the file: `[propext, Quot.sound]`, except
  `VExpr.substC_instAll` at `[propext]`. Names read off the file's own `namespace` lines, never
  composed from the path.
* `lake env lean --run scripts/sorry-census-all.lean`: **13 holes** over the whole built
  population; `BUILT: 387`, `in population but NOT BUILT: 1`.
* `scripts/dup-names.lean`: *"no duplicate Lean4Lean declarations across the joined cone"*.
* Layering: `grep -rln "^import Lean4Lean.Verify" Lean4Lean/Theory/` is **empty**.
* Frozen files (`Verify/Soundness.lean`, `Verify/Axioms.lean`, `Verify/Guard.lean`): not read for
  editing, not written, not touched.
* My file adds **no holes** and is an orphan module (imported by nothing), as a new leaf should be.

### 7a. Foreign build failures seen and not fixed, per instruction

* `lake build` (full, 1571 jobs) fails at **`Lean4Lean/Theory/Inductive/CtorBeta.lean:579–606`**
  ("failed to synthesize", "Expected type must not contain free variables", `introN` failed) — the
  concurrent blocker-(A) stream's file, mid-edit. It is the census's one `NOT BUILT` module:
  `Lean4Lean.Theory.Inductive.CtorBeta`. Untouched.
* `Theory/Inductive/RecTyped.lean` and `RecTypedScan.lean` (blocker (B)) and
  `Theory/Typing/SpineVar*.lean` build. I did **not** import `RecTyped.lean` — it is in flight and
  importing it would couple my build to theirs — so the §6 claim about
  `motiveEntry_defeq_of_hargs` / `minorEntry_defeq_of_hargs` is **read off their source**, not
  composed.

### 7b. Measured vs read off

**Measured by me this session:** the environment scan of §2 (8 → 9, with the conclusion/hypothesis
split); every axiom line and arity in §3–§4; `lean_minimal_hypotheses` on `iotaHargs_hfunM`; every
`decide` in §5b–§5d; the `ni = 0` degeneracy at all three unindexed witnesses; that all nine of
route 1's pieces at `ntreeAux` and both of `MP`'s were already proved; `rMaj_node_eq`'s identity;
the census, the layering check, the duplicate-name check; that `substC_instAll` was absent and that
`onCtxParamsAtRec_substCD` was **present** (in `RecTyped.lean`).

**Read off source, not independently re-run:** `RecTyped.lean`'s two entry-defeq producers being
(C)'s `hmot`/`hmin` (I read their statements, did not instantiate them); `ntree_csubst_WF₃_false`
refuting `σ.WF` at the ι-stage (read from §T16.11's docstring and the declaration's name, not
re-elaborated); `instAt_indep_of_tyArgs`' lower bound on `hargs`.

## 8. Pick up first

1. **`hres` from `instAt_ctor_hpi`.**  I did the de Bruijn arithmetic by hand and it does not
   close in one step, so here is the decomposition — **hand analysis, not machine-checked, treat it
   as a guess about difficulty and not about truth**:
   * the `R.tyArgs j` entries go through with existing machinery: `instAll_bvars_lift` (needs
     `a.ClosedN D.np`, which is §4's `hcl`) then `VExpr.liftN'_liftN'` twice then
     `VExpr.instAll_liftN`, landing on `(D.atRec a).liftN (D.nm + D.nmin + C.fields.length)` — the
     right-hand side's entry, modulo `nf + off = off + nf`;
   * the `C.args` entries do **not**: `(D.atRec a).liftN k nf` under `instAll · (bvars 0 nf) 0` is a
     *two-region* rewrite — identity on the field block (indices `< nf`), lowering by `nf` on the
     parameter block — and `instAll_bvars_lift` does not apply (its `ClosedN` hypothesis fails) while
     `instAll_liftN` needs the whole term to be a lift at cutoff `0`. **A new lemma is needed**,
     of the shape `instAll (e.liftN (n + d) n) (bvars 0 n) 0 = e.liftN d n`;
   * and the right-hand side's `C.args` entries carry a `substC` the left-hand side does not, so
     `hres` also needs **σ to be the identity on `C.args`**. That is `VIndCtor.WF.args_fresh` (F5)
     — but note `VIndRestore.noBlock_noCSubst` (`RestoreBridge.lean:160`) is stated for `csubstTy`,
     and `hres` lives at `csubst`, whose domain escapes `blockNames` (row 28). So this half wants the
     barrier composition: `VExpr.NoConstIn.noCSubst` at `IsNestedName` with
     `VIndRestore.NameBarrier.dom` — the same ingredient `Verify/Inductive/FlipPriceCompose.lean` §5
     uses, one place further in.
2. **A single simultaneous instance of §4** at `ntreeAux`/`nlistNil`, to convert §5d from
   "inhabitation unknown" to a certificate. `nlistNil` is the cheap one: `nf = 0`, so `AsT = AsC =
   []` and `hpiT`/`hpiC`/`hsortT`/`hres` collapse to the equations §7 of my file already `decide`s.
   The load-bearing hypothesis is `hbodyC` — the restored `List.nil (NTree #0)`'s typing.
3. **`htele` by composition with the (B) stream**, once `RecTyped.lean` lands: `iotaCtx_teleDefEq`
   + `motiveEntry_defeq_of_hargs` + `minorEntry_defeq_of_hargs` + `teleDefEq_fld_iota_of_fields`.
   This is the "compose two things already in the tree" move and it is *cross-stream*, which is why
   I am flagging it rather than doing it: their file is in flight.
4. **Do not** close `tryEtaStructCore.WF` / `isDefEqUnitLike.WF` (ledger row 197) and **do not**
   make the flip: (C) is still not discharged in general, and the census is still 13.
