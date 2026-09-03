# Handoff: obligation (B)'s typed data (`RecTyped`)

**Written 2026-09-03.**  Files (both mine, both new):
`Lean4Lean/Theory/Inductive/RecTyped.lean` — the work;
`Lean4Lean/Theory/Inductive/RecTypedScan.lean` — a structural query over the *compiled
environment*, so this file's ABSENCE claims are not grep results.

Target: blocker **(B)** of `docs/handoff-flipprice.md` §6 — the per-block / per-entry typed data
that `VEnv.recConstsR_wf_of_blocksD` / `_of_entriesD` (`Theory/Inductive/NestedTele.lean` §T15.3a)
take as `hmot` / `hmin` / `hbody`.

## 0. Verdict, in one line

**(B) at `D.np > 0` is now reduced, in general and hole-free, to four bundled data families —
`VEnv.recConstsR_wf_of_recHargsD` — and that is a REDUCTION, not a discharge.**  The four families
are `hargs` plus `hfld`, which is precisely what §T15.8 already called the residual; nothing here
produces them.  I did **not** make the flip, and it is not available.

Two findings are worth more than the reduction:

1. **The obvious composition is VACUOUS, and I have the refutation.**  Feeding §T5's
   `substC_motiveType_defeq'` and §T6's `substC_minorType_defeq` to *every* entry of the recursor
   telescope requires `∀ t T, D.types[t]? = some T → T.name ∈ K` — and
   `InductiveDeclExamples.ntree_recTyped_hK_false` refutes that at `ntreeAux`: `K` lists the
   **companions**, and an auxiliary block always also contains the *outer* head.  My first draft
   of the closure had exactly that hypothesis, compiled, and printed a clean `[propext,
   Classical.choice, Quot.sound]` while being unsatisfiable at every real nested block.  It was
   caught only by trying to instantiate it at `ntreeAux`, which is the method §0 of the vacuity
   ledger prescribes.
2. **Ledger ruling 152d is executed for (B).**  Row 143d's identity rule — *anything indexed by
   the block's own member restores trivially* — is now a **theorem** for all three of (B)'s entry
   families, from `OwnId` alone: `motiveEntry_defeq_off_K`,
   `VIndRestore.minorEntry_defeq_off_K`, `recBody_defeq_off_K`.  And the rule's boundary is
   sharpened rather than asserted: off `K` the **only** thing that survives is the field
   telescope, `ntree_node_fieldTypesR_ne` (`decide`) showing it really does move at the block's
   own member.

## 1. What is in the file

`lake build Lean4Lean.Theory.Inductive.RecTyped`: **72 jobs, exit 0**.
`lake build Lean4Lean.Theory.Inductive.RecTypedScan`: **77 jobs, exit 0**.
Full `lake build`: **1571 jobs, exit 0**.

### §1 The `CSubst.WFD` variants of §T3's inversion

`Theory/Typing/ConstSubstNested.lean` §B refutes `σ.WF E₂ F₂ U` between the staging pair of a
parameterised nested block (`ntree_csubst_WF₂_false`; `mp_csubst_WF₂_false` at the redex block).
So `VConstant.WF.substC_mkPi_inv`, `VEnv.recTypeTele_substC_onCtx` and
`VEnv.recTypeEntry_substC_onCtx` — the three lemmas §T3/§T9 rely on for (B)'s telescope typing —
are **vacuous in `hσ` exactly where (B) is open**.  §1 restates all three over `WFD`
(`…substCD_mkPi_inv`, `recTypeTele_substCD_onCtx`, `recTypeEntry_substCD_onCtx`), plus
`VInductDecl'.onCtxParamsAtRec_substCD`.

This is not a new observation — §T1a says it for the `OnCtx`/`HasArgs` transports — but §T9's and
§T10's own statements were never given `WFD` forms, and **`recTypeEntry_substC_onCtx` has zero
users in the tree** (measured: every other occurrence of the name is prose).  So "(B)'s `hOn` is
free from `hsrc` + `hσ`" was, until now, free only under a hypothesis nothing satisfies at
`np > 0`.

### §2 The free items, transported to the contexts (B)'s closure actually binds

`recConstsR_wf_of_entriesD` binds `hmot` over
`((D.motives.map (substC · σ)).take t).reverse ++ ((D.atRecTele D.params).map (substC · σ)).reverse`
and `hmin` one block further in.  §T5/§T6 are stated at a *general* ambient context, so they fit —
but the items §T9/§T10/§T16.2 call free are stated at shapes that must be transported.  §2 does
that: `motiveEntry_substCD_onCtx`, `minorEntry_substCD_onCtx`, `minorEntry_substCD_body`,
`recPar_substCD_onCtx`, `VInductDecl'.atRecTele_params_closedTele`, `OnCtx.entry_inv`.

One saving worth naming: `recPar_substCD_onCtx` gets `hpar` out of the *same* telescope `OnCtx`
(the parameter block is its outermost segment) rather than from `onCtxParamsAtRec_substCD`.  That
removes a **second** `CSubst.WFD`, at `(env, e₂)`, which the closure would otherwise have had to
carry alongside its own at `(E₂, e₂)`.

### §3 The producers

* `VIndRestore.motiveEntry_defeq_of_hargs` — `hmot` from the type head's `hargs`;
* `VIndRestore.minorEntry_defeq_of_hargs` — `hmin` from the constructor head's `hargs` + `hfld`;
* `VIndRestore.recBody_defeq_of_hargs` — `hbody` from the major premise's head defeq;
* and the three off-`K` twins, which take **no** head data at all.

`hbody`/`hcbody` are taken at the **params-only** context and weakened by
`VIndRestore.hbody_weak` — §T11's factorisation, so the data enters *once per `Faithful` clause*
rather than once per entry.

### §4–§5 The bundles and the closure

`VIndRestore.MotiveHargs`, `MinorFldDefEq`, `MinorCtorHargs`, `RecBodyHargs`, and

    VEnv.recConstsR_wf_of_recHargsD
      (henv hD hfresh hsrc hσ hσc he₂ hfr hat hown helim hcl)
      (hmotD hfldD hminD hbodyD) : ∀ c ∈ D.recConstsR R K, VConstant.WF e₂ c.2

`hmotD`/`hminD`/`hbodyD` are asked for **only at `T.name ∈ K`**; `hfldD` at every `q`.

### §6 Anti-vacuity, and §7 the axiom audit

## 2. Hole-freeness (measured) — and it is NOT evidence of content

| declaration | axioms |
| --- | --- |
| `VEnv.recConstsR_wf_of_recHargsD` | `[propext, Classical.choice, Quot.sound]` |
| `VEnv.motiveEntry_substCD_onCtx` | `[propext, Quot.sound]` |
| `VEnv.minorEntry_substCD_onCtx` / `_body` | `[propext, Quot.sound]` |
| `VEnv.recPar_substCD_onCtx` | `[propext, Quot.sound]` |
| `VIndRestore.motiveEntry_defeq_of_hargs` | `[propext, Classical.choice, Quot.sound]` |
| `VIndRestore.minorEntry_defeq_of_hargs` | `[propext, Classical.choice, Quot.sound]` |
| `VIndRestore.recBody_defeq_of_hargs` | `[propext, Quot.sound]` |
| `motiveEntry_defeq_off_K` | `[propext, Quot.sound]` |
| `VIndRestore.minorEntry_defeq_off_K` | `[propext, Quot.sound]` |
| `recBody_defeq_off_K` | `[propext, Quot.sound]` |
| `InductiveDeclExamples.ntree_recTyped_hK_false` | `[propext, Quot.sound]` |
| `InductiveDeclExamples.ntreeAux_obligationB_of_bundles` | `[propext, Classical.choice, Quot.sound]` |
| `InductiveDeclExamples.ntreeAux_recHargs_premises_inhabited` | `[propext, Classical.choice, Quot.sound]`, **arity 0** |
| `InductiveDeclExamples.ntree_minorFld_nil` | `[propext, Quot.sound]` |
| `InductiveDeclExamples.ntree_node_fieldTypesR_ne` | `[propext, Quot.sound]` |

Names read off the file's own `namespace` lines and its own `#print axioms` block, **not**
composed from the path.  Note the two odd ones: `motiveEntry_defeq_off_K` and
`recBody_defeq_off_K` sit at the top level of `namespace Lean4Lean` (not under `VIndRestore`),
because they were relocated after `end VEnv`; their full names have **no** `VIndRestore.` prefix.

## 3. Inhabitation, stated separately from hole-freeness

### 3a. Established: the non-bundle premises hold JOINTLY at a parameterised nested block

`InductiveDeclExamples.ntreeAux_obligationB_of_bundles` is §5 with **every** hypothesis except
the four data families discharged at `ntreeAux` (`np = 1`, `Canonical`), from the five staging
equations alone:

    listEnv_ordered · ntreeAux_WF · ntree_csubst_fresh · ntree_recConsts_wf ·
    ntree_csubst_WFD₂ · ntree_csubst_closed · ntreeF₂_ordered · ntreeRestore_substFree ·
    ntreeRestore_domSep.substAt · ntreeRestore_ownId · (helim by decide) ·
    ntree_tyArgs_closedN_np

This is the *joint* check the ledger asks for, not a per-hypothesis one, and it is the (B)
counterpart of `ntreeAux_obligationC_of_hdata`.

And it is **not** relative to the staging equations either: `ntreeAux_recHargs_premises_inhabited`
is **arity 0** — `ntree_stage₂_exists` supplies the five equations, and all **twelve** non-bundle
premises of §5 are exhibited holding simultaneously at one block with one `D`, one `R`, one `σ`.
That is the strongest form of this check available without doing the open work, and it is the form
row 11a asks for.

### 3b. NOT established: the four data families at `np > 0`

I have **no** witness for `MotiveHargs`, `MinorCtorHargs` or `RecBodyHargs` at any block with
`D.np > 0`, and I do not claim their hypothesis set is known satisfiable there.  They are
`hargs`, and `VIndRestore.instAt_indep_of_tyArgs` (`NestedRules.lean:1509`) says no
restoration-independent argument produces it.  What *is* known: (B) is achievable at `np = 1` by
some route, because `InductiveDeclExamples.ntreeAux_obligationB` **and**
`MRedex.MPWit.mpAuxB_obligationB` are both arity 0 — see §5 below, where the second of those is a
correction to `handoff-flipprice.md`.

### 3c. Degenerate witness, disclosed

`ntree_minorFld_nil` inhabits `MinorFldDefEq` at `nlistNil` — a constructor with **no fields**, so
the telescope defeq is `TeleDefEq.nil`.  It shows the bundle is not uniformly false and nothing
more; `ntree_node_fieldTypesR_ne` is the complement, showing the field telescope really moves
where the content is.

### 3d. The `[]`-collapse check (§T5's trap), run on every new statement

No hypothesis of §3–§5 carries a `bvars` spine at a context that can be empty:

* `MotiveHargs.hAs`' context has length `ni + t + np`, and the spine is `bvars 0 ni`;
* `MinorCtorHargs.hfun`'s head is `bvar (nr + nf + q + (nm - 1 - t))` in a context of length
  `nf + nr + (nm + q) + np`, and `D.nm ≥ 1` always (`nm_pos_of_types_ne`), so
  `minorBody_hfun_false_of_nil` cannot fire — the same reason §T11's instrument-7 note gives;
* `hbody`/`hcbody` are at the params-only context with a subject closed at `D.np`.

## 4. The vacuity I caught in my own first draft — in full, because it is the transferable part

My first `recConstsR_wf_of_recHargsD` took

    hK : ∀ (t : Nat) (T : VIndType), D.types[t]? = some T → T.name ∈ K

because that is the hypothesis `substC_motiveType_defeq'` and `substC_minorType_defeq` each bind
per entry, and the closure quantifies over *all* entries.  It compiled.  Its axiom line was clean.
Its premises are **jointly unsatisfiable at every real nested block**, and
`ntree_recTyped_hK_false` is the machine-checked refutation at `ntreeAux`.

**The repair is the off-`K` branch**, and it is not a patch but content: `OwnId.tyAppR'_eq` and
`OwnId.ctorAppR_eq` collapse the restored heads to the source ones off `K`, so the two sides of
those entry defeqs are *syntactically equal* and the defeq is a **typing**, which
`OnCtx.entry_inv` / `OnCtx.mkPi_entry_inv` already supply from `hsrc` + `hσ`.  So:

* the motive entry off `K`: **free**;
* the recursor body off `K`: **free**;
* the minor entry off `K`: **`hfld` alone** — the conclusion is reflexive, but the *field
  telescope* still moves, because `C.fieldTypesR` rewrites a companion occurrence inside a
  constructor of the block's own head.  That is the `NTree.node` case, and it is why the off-`K`
  branch does not make the minor block free.

**Correction to `NestedTele.lean` §T15.8** (I have not edited it — not my file): its residual list
for (B) — *"the motive block — §T5's `substC_motiveType_defeq'` …; the minor block — §T6's
`substC_minorType_defeq` …"* — is stated only for **companion** entries.  Those two lemmas carry
`hK : T.name ∈ K` and therefore say nothing about the block's own head, which every auxiliary
block contains.  §T15.8 does not record the gap, and no document in the tree does.

**And it sharpens ledger ruling 152d rather than merely confirming it.**  152d asks for a *proof*
of row 143d's identity rule from `OwnId` + `substC_tyApp_comp`.  For (B) the proof needs only
`OwnId` (the two `_eq` collapses), no `substC_tyApp_comp`, and it now covers all three entry
families.  The boundary the rule needs is: the collapse applies to positions indexed by the
**entry's type index** (`tyAppR'`, `ctorAppR`); it does **not** apply to the field telescope,
which is indexed by each field's own target.  `ntree_node_fieldTypesR_ne` is that boundary,
`decide`-checked, and it is consistent with row 127f rather than a counterexample to it (127f's
identity is at a *redex* field, whose head is the block's own member; `ntreeNode`'s field points
at a companion).

## 5. Corrections to what I was relayed, and to the documents

Every item here I checked myself.

1. **`FlipPriceScan.lean` — the instrument `handoff-flipprice.md` §9a's ABSENCE claim rests on —
   runs over an environment that does not contain `ParamRedex.lean`, and its count is therefore an
   undercount.**  §9a says the scan "finds **exactly five** declarations whose type mentions both
   `VEnv.addInductR` and `VEnv.Ordered`" and that "the only arity-0 ones are the two witnesses".
   Re-run with `ParamRedex` imported (`RecTypedScan.lean`, same query): **six**, and **three**
   arity-0 — the third is `MRedex.MPWit.mpAuxB_addInductR_ordered`, an end-to-end
   `Ordered`-after-a-nested-step at `np = 1` at a block that is **not** `Canonical`.
   `ParamRedex.lean` is imported only by `IndexedNested.lean`, `Experimental/ConeJoin.lean` and my
   scan, and none of `FlipPriceScan`'s six imports reaches it — so this is a property of the
   instrument, not of the tree.
   §9a's *substantive* claim **survives**: all three arity-0 hits are witnesses at concrete blocks,
   and the general ones still carry 8 / 11 / 12 hypotheses, so there is still no hypothesis-free
   general `Ordered`-after-a-nested-step.  What does not survive is the pricing consequence: the
   parameterised case has **two** independent end-to-end confirmations, one canonical (`ntreeAux`)
   and one a redex block (`mpAux mpAuxNodeB`), and `MRedex.MPWit.mpAuxB_obligationB` is a *second*
   arity-0 witness for (B).  Also in that file and named in no handoff: `mpAuxB_hdata` (arity 9),
   a (C) `IotaHargs` at a parameterised block — which `handoff-flipprice.md` §5b says it has no
   witness for.  I have **not** audited whether `mpAuxB_hdata`'s nine hypotheses are jointly
   satisfiable; that is blocker (C)'s stream's call.
2. **"(B) is likely the easiest of the three, since (B) has no `ihValues` layer"** (flipprice §8
   item 3) — **not supported by the residual count.**  After this reduction (B) has **four** data
   families (two distinct heads: the type head for the motive block and recursor body, the
   constructor head for the minor block, plus `hfld`), where (C) has **one** bundle
   (`IotaHargs` = `htele` + one typing + two conversions) over **one** context.  §T11 already says
   why: (B)'s two blocks apply *different constants with different declared types*, so no single
   `HasArgs` can serve both.  This is a count of families, not a claim about difficulty — but it
   is the opposite ordering from the one I was given.
3. **`VEnv.recConstsR_wf_of_np_zero_via_blocks` (arity 15) exists and is named in no handoff.**
   It is §T15.6's recovery of the `np = 0` closure *through* the general one — i.e. the
   non-vacuity certificate for `recConstsR_wf_of_blocks`.  Worth citing whenever §T15.8's
   "certified non-vacuous by §T15.6" is quoted.
4. Everything else relayed reproduced: `substC_motiveType_defeq'` (arity 29) and
   `substC_minorType_defeq` (arity 32) are the live general entry lemmas; `recConstsR_wf_of_blocksD`
   / `_of_entriesD` (arity 13 each) are the live general closures; the census reads 13; the
   `VIndRestore.NameBarrier` composition is where flipprice §5 says it is.

## 6. ABSENCE claims, and how they were measured

`RecTypedScan.lean` walks the **compiled environment** and enumerates every `Lean4Lean`
declaration whose *type* mentions a given constant, with arities.  Results:

* **(B)'s conclusion** (`VInductDecl'.recConstsR` **and** `VConstant.WF`): **19** declarations.
  The general ones take either the entry defeqs (`_of_blocks`, `_of_blocksD`, `_of_entries`,
  `_of_entriesD`, arity 13), a syntactic bridge (`_of_substC`, `_of_substC'`, `_of_substCD'`,
  `_of_substC_of_eq`), or `hp : D.params = []` (`_of_np_zero`, `_of_np_zero_via_blocks`).  The
  arity-0 ones are the two witnesses.  **So before this file there was no `hargs`-shaped closure
  for (B) — no counterpart of `iotaRulesRS_wf_of_hargsD` — and that is an environment fact.**
* `motiveTypeR`: 12 declarations; `minorTypeR`: 10.  Both entry lemmas and both closures are in
  those lists; nothing else general is.
* `IotaHargs` (for comparison): 6, including (C)'s closure and `mpAuxB_hdata`.
* `VEnv.addInductR` **and** `VEnv.Ordered` — `FlipPriceScan`'s own query, re-run over an
  environment that includes `ParamRedex.lean`: **6**, of which **3** have arity 0
  (`ntreeAux_addInductR_ordered`, `nfnAux_addInductR_ordered`,
  `MRedex.MPWit.mpAuxB_addInductR_ordered`).  See §5 item 1.

**Zero-user ingredients this file composed** (measured by grep across the tree, excluding each
name's own declaration line and prose; I state the method because grep has been wrong in this
repo twice today, and for these the environment scan agrees):

| ingredient | users before | users now |
| --- | --- | --- |
| `VIndRestore.substC_motiveType_defeq'` | 0 | 1 (mine) |
| `VIndRestore.substC_minorType_defeq` | 0 | 1 (mine) |
| `VIndRestore.substC_recBody_defeq` | 0 | 1 (mine) |
| `VIndRestore.hbody_weak` | 0 | 2 (mine) |
| `VEnv.onCtx_params_append` | 0 | 2 (mine) |
| `VEnv.recTypeEntry_substC_onCtx` | 0 | **still 0** — the `σ.WF` form is vacuous at `np > 0`; §1's `WFD` twin replaces it |

**Still zero users, and they are the next composition** (see §7): `VEnv.HasArgs.congr_tele`,
`VEnv.TeleDefEq.instN`, `VExpr.instAllTele_bvars_lift`,
`VIndRestore.atRecTele_fieldTypesR_substC_eq`, `VIndCtor.atRecTele_fieldTypesR_closedTele`.

## 7. Pick up first

1. **Discharge `hAs` out of `MinorCtorHargs`, from machinery that already exists and is unused.**
   §T12.1/§T13 built exactly this and nothing consumes it: §T10's `instAt_ctor_hpi` *derives*
   `hpi` with `As = instAllTele (D.atRecTele (C.fieldTypesR D R)) (bvars k D.np) 0` from
   `Faithful.ctor_agree` + `VIndCtor.WF.params_len`; `instAllTele_bvars_lift` turns that into a
   `liftTele`; `HasArgs.bvars` types the spine against the source-substituted telescope;
   `TeleDefEq.weakN` + `HasArgs.congr_tele` bridge source-to-restored using `hfld`; and
   `atRecTele_fieldTypesR_substC_eq` / `atRecTele_fieldTypesR_closedTele` are the two side
   conditions, both **proved**.  If that composes, `MinorCtorHargs` drops from four items to
   three (`hcbody`, `hpi` derived, `hfun`) and `hpi` stops being data.  Cost: a `Faithful`
   hypothesis on the closure — which `addInductR_ordered'` already carries at every witness
   (`ntreeRestore_faithful`, `NestedHead.lean:841`).  **I did not attempt this; the estimate is a
   guess from reading §T12.1's own arithmetic note, which claims the offsets already line up.**
2. **The same for `MotiveHargs`' `hpi`/`hAs`** — but note the asymmetry row 74b records: for the
   *type* head `hsplit` is data (F1 leaves `T.type` only definitionally canonical), so
   `instAt_ctor_hpi` has **no** counterpart there.  Expect `MotiveHargs` to stay four items.
3. **`RecBodyHargs`' `hconcl` looks free and I did not check it.**  §T8 says the recursor body's
   conclusion is `hmot` (the motive `Lookup`, `D`-free, `lookup_motive_substC`) applied to the
   index spine and `.bvar 0`; `iotaLamBody_hasType`'s call site builds that shape.  If it is free,
   `RecBodyHargs` collapses to its head defeq alone.  **Guess, unmeasured.**
4. **Re-mark `NestedTele.lean` §T15.8** per §4 above: its (B) residual list covers only the
   companion entries.  And `docs/vacuity-ledger.md` ruling 152d can record that the identity rule
   is now *proved* for (B)'s three head positions and *bounded* at the field telescope.

## 8. Verification record

* `lake build Lean4Lean.Theory.Inductive.RecTyped`: **72 jobs**, exit 0.
* `lake build Lean4Lean.Theory.Inductive.RecTypedScan`: **77 jobs**, exit 0.
* Full `lake build`: **1571 jobs**, exit 0.
* `lake env lean --run scripts/sorry-census-all.lean`: **13 holes**; `in population but NOT
  BUILT: 0`; `BUILT: 388`.  Both my files appear among the 32 orphan modules (imported by
  nothing), as measurement/composition files should, and add **no** holes.
* Layering: `grep -rln "^import Lean4Lean.Verify" Lean4Lean/Theory/` is **empty**.
* Frozen files (`Verify/Soundness.lean`, `Verify/Axioms.lean`, `Verify/Guard.lean`): not read for
  editing, not written, not `touch`ed — `git status` on all three is clean.
* Files created: only `Lean4Lean/Theory/Inductive/RecTyped.lean`,
  `Lean4Lean/Theory/Inductive/RecTypedScan.lean`, `docs/handoff-rectyped.md`.  No other file
  edited.  Concurrent streams' files (`Theory/Inductive/IotaHargsGen.lean`,
  `Theory/Inductive/CtorBeta*.lean`, `Theory/Typing/SpineVar*.lean`) appeared during the session
  and were **read only**.
* **The flip was not made**, per the brief; and it is not available — (B) is a reduction, and (A)
  and (C) are untouched here.

### 8a. Measured vs read off

**Measured by me this session:** every axiom line in §2; the scan counts in §6 (19 / 12 / 10 / 6)
and every arity quoted; `ntree_recTyped_hK_false` and `ntree_node_fieldTypesR_ne` (`decide`);
`ntreeAux_obligationB_of_bundles`' twelve discharged hypotheses (they type-check); the census,
the layering check, the job counts; the user counts in §6 (grep, method stated).

**Read off source or documents, not independently re-run:** that `σ.WF` is refuted between both
staging pairs (`ntree_csubst_WF₂_false`, `mp_csubst_WF₂_false`) — read from §T1a and §15 of
`ParamRedex.lean`; `instAt_indep_of_tyArgs`' claim that `hargs` is restoration-independent — read
from `NestedRules.lean:1509`; row 143d's and 127f's history — read from the ledger; §T12.1's
claim that the lifted-versus-instantiated offsets line up (item 1 of §7) — read from its own
docstring, **not** re-derived, and flagged there as a guess.
