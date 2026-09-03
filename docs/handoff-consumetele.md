# handoff-consumetele: three "just apply it" items, of which **two are not applicable and one is already done**

*Stream started 2026-09-03. Written incrementally. Grading follows `docs/vacuity-ledger.md` §0.*

## 0. Bottom line, per item

| brief item | verdict |
| --- | --- |
| **1.** Apply `handoff-telecongr.md` §6's two implied edits (`CtorBeta.lean`, `RecTyped.lean`) | **NOT APPLICABLE as specified — module-order impossible.** Both discharges live *downstream* of the files that would consume them. Machine-checked, two probes. Requires editing `TeleCongr.lean` (a fifth file) → stopped and reported, with the exact recipe in §2 |
| **2.** Delete the redundant `substC_tyAppR_free` | **NOT APPLICABLE as specified — the brief's "one consumer" is TWO.** The second is `HypTrimWitness.lean:122`, the very `rfl` that proves the redundancy. Attempted, ripple measured at exactly one error, reverted (§3) |
| **3.** Verify or refute §T15.8's own-head marking | **BOTH: the composition is VERIFIED (and was already in the tree when it was flagged), and the marking it rests on is REFUTED for one of the three families.** New module + `NestedTele.lean` §T15.8 amended (§4) |
| **4.** `IndStage.lean`'s two unused `hE` | **REFUTED — false positives, nothing to trim.** `hE` is *already* omitted at both, by a bare `omit hE`. Machine-checked on the signatures (§5). No edit made, and "a one-line fix each" would have been a no-op |

Net: **one file created, one file's prose amended, zero statements changed anywhere.**
`CtorBeta.lean`, `RecTyped.lean` and `IndStage.lean` are byte-identical to `HEAD`.

## 1. Where the brief is wrong — the highest-value output, up front

1. **"Delete the now-redundant `substC_tyAppR_free` … It lives in `CtorBeta.lean` with one
   consumer."** It has **two**. The second is `Lean4Lean/Theory/Inductive/HypTrimWitness.lean:122`

       theorem free_eq_trimmed : @VIndRestore.substC_tyAppR_free = @VIndRestore.substC_tyAppR := rfl

   i.e. the machine check that licenses the deletion is itself a consumer of the thing to delete.
   `handoff-hyptrim.md` §5 item 1 has the same "one consumer" error, so this propagated.
2. **"Apply `TeleCongr`'s two implied edits."** Neither is applicable. `handoff-telecongr.md` §2
   asserts "`TeleCongr.lean` imports `CtorBeta.lean`, so nothing there needs to change for §4 to
   be usable" — true for *usability*, and the reason the edits are *impossible*: the discharge is
   downstream of its consumer (§2).
3. **"the same round left two zero-ripple unused-hypothesis instances in `SetModel/IndStage.lean`
   (`hE`)."** There are none. Both flagged theorems sit after a **bare `omit hE`** (line 144) and
   carry no `IsMinorPremise` argument at all (§5).
4. **The item-3 marking was wrong in a way neither the brief nor the marking anticipated.** The
   brief expected the *composition* to be the risk. The composition is fine and was already
   verified in the tree. What is wrong is the sentence one clause earlier: "off `K` the entries are
   **free** … from `OwnId` alone" — true for two of the three families, false for the third (§4).
5. **`lean_minimal_hypotheses` returned "load-bearing" for all eight binders of
   `motiveEntry_defeq_off_K` when the oleans were stale**, with every `breaks` entry reading
   *"Imports are out of date"*. A caller who reads only the `status` field gets a clean
   all-load-bearing verdict from a tool that did no work. This is the same false-negative shape as
   the two defects the brief cites. **Restart the LSP before believing that tool.**

## 2. Item 1: both edits are module-order impossible, not merely rippled

`handoff-telecongr.md` §6 asks for:

* **(a)** make `ctorConstsCR_wf_of_betaD₄` *the* statement in `CtorBeta.lean` (delete `hbeta`'s
  `hbv`, add `henv`), and
* **(b)** make `MinorCtorHargs` a two-component bundle in `RecTyped.lean`.

Neither can be done in the named file, because the thing that discharges the deleted component is
declared in `TeleCongr.lean`, which **imports** both files. Machine-checked, not read off prose:

    import Lean4Lean.Theory.Inductive.NestedTele   -- everything CtorBeta.lean can see
    #check @Lean4Lean.VIndCtor.WF.hasArgs_params_bvars_of_wf
    -- error: Unknown constant

    import Lean4Lean.Theory.Inductive.RecTyped      -- everything RecTyped.lean can see
    #check @Lean4Lean.VIndRestore.minorCtorHargs_of_hargs
    -- error: Unknown constant

So (a) would leave `CtorBeta.lean` stating a theorem it cannot prove, and (b) the same for
`RecTyped.lean`. Adding the four-component form *alongside* the five-component one is not the
edit either — that is exactly what `ctorConstsCR_wf_of_betaD₄` already is.

### The recipe, and it is cheap — but it is a `TeleCongr.lean` edit

I verified the enabling step rather than assuming it. `TeleCongr.lean` §1–§3 (lines 29–178:
`VEnv.TeleDefEq.of_isDefEqCtx_aux`, `.of_isDefEqCtx`, `.substC`, `.weak0`,
`VIndRestore.csubstTy_freshIn`, `VIndCtor.WF.hasArgs_params_bvars`, `.hasArgs_params_bvars_of_wf`)
**compiles against `NestedTele` alone** — extracted verbatim into a scratch module importing only
`Lean4Lean.Theory.Inductive.NestedTele`, zero errors. So:

1. Move `TeleCongr.lean` §1–§3 upstream of `CtorBeta.lean` — into `NestedTele.lean`, or into a new
   module `CtorBeta.lean` imports. **Deleting them from `TeleCongr.lean` is unavoidable**; leaving
   them creates a duplicate-declaration error the moment both are in scope.
2. Then `CtorBeta.lean` can state the four-component `ctorConstsCR_wf_of_betaD` + `henv`, and
   `TeleCongr.lean` §4 (`ctorConstsCR_wf_of_betaD₄`) is deleted as redundant.
3. Symmetrically for (b): move `TeleCongr.lean` §6/§6b (`minorCtor_hAs`,
   `minorCtorHargs_of_hargs`, `minorCtorHargs_of_hargs'`) into `RecTyped.lean` — **not verified by
   me** that §6 needs nothing from `CtorBeta.lean`; §1–§3 is the half I checked.
4. `HasArgs.congr_tele`'s docstring at `NestedTele.lean:1550` and `CtorBeta.lean` §6d's
   parenthetical still say the pair is "the outstanding obstruction". Those are stale either way
   and are `NestedTele.lean`/`CtorBeta.lean` edits, not `TeleCongr.lean` ones.

**Cost of the whole thing: three files, one of them outside my ownership.** Per the brief's rule I
stopped rather than making it. Note the shape for the ledger: `handoff-telecongr.md` §6 wrote both
edits as one-line descriptions of a *deletion*, and both are actually **module moves**.

## 3. Item 2: attempted, measured, reverted

The `CtorBeta.lean` half works exactly as advertised. Performed:

* deleted `VIndRestore.substC_tyAppR_free` (11 lines) and its `#print axioms` line;
* changed `CtorBeta.lean:433` from `substC_tyAppR_free hnn hna` to `substC_tyAppR hnn hna`.

`CtorBeta.lean` then elaborated clean, axiom lines unchanged — the brief's "verbatim" is correct,
and the argument order works because `RestoreBridge.lean`'s `omit hp hnd hown hlw hcl in` leaves
`hnn`, `hna` as the only included section variables, in declaration order.

**The ripple, measured:** `lake build Lean4Lean.Theory.Inductive.HypTrimWitness` →

    error: Lean4Lean/Theory/Inductive/HypTrimWitness.lean:122:5:
      Unknown constant `Lean4Lean.VIndRestore.substC_tyAppR_free`

Exactly one error, in exactly one file, and that file is not mine. Reverted; `git diff` on
`CtorBeta.lean` is empty.

**The edit the orchestrator needs to make, in full:** in `Lean4Lean/Theory/Inductive/CtorBeta.lean`
apply the two bullets above, and in `Lean4Lean/Theory/Inductive/HypTrimWitness.lean` delete the
`/-! ## 3b … -/` block and the `free_eq_trimmed` theorem (lines 113–123). `free_eq_trimmed` has
served its purpose the moment the deletion lands, so this is a retirement rather than a loss.

## 4. Item 3: the composition is verified; the marking around it is refuted

New file: `Lean4Lean/Theory/Inductive/ConsumeTeleOffK.lean`. Nine theorems, all hole-free.

### 4a. The flagged risk did not exist — it was already checked, in the file the theorems live in

`handoff-hyptrim.md` §5 item 5: *"what is **not** checked here is that (B)'s closures consume them
in the shape they are stated in. That composition is the next thing someone will assume and should
not."*

It was already checked when that sentence was written. `VEnv.recConstsR_wf_of_recHargsD`
(`RecTyped.lean:773`) — obligation (B) at `np > 0` — refines `VEnv.recConstsR_wf_of_entriesD` and
closes all three off-`K` branches with a **bare `exact`**, no `simpa` and no reshaping, at
`RecTyped.lean:809` / `:821` / `:828`. That is ~370 lines below the three `_off_K` theorems, in the
same file. This is the third instance in three rounds of "the composition already existed in a file
nobody read to the end".

§1 of the new module restates the three fits as named theorems — `offK_fits_hmot`,
`offK_fits_hbody`, `offK_fits_hmin` — stated as literally the closure's hypothesis slots with `σ`
**fixed at `R.csubst D K`** (the closure's own substitution, not the `_off_K` theorems' generic
`σ`), guarded to off-`K` members, each closed by `exact`.

**Instantiated, not admired.** A generic `by_cases hK` proves nothing about whether the off-`K`
branch is reachable. At `ntreeAux` (`nm = 2`, `np = 1`, `K = [`_nested.List_1]`) there is one
member on **each** side: `ntree_member_zero_off_K` and `ntree_member_one_in_K`. So
`ntreeAux_obligationB_of_bundles`, which is that closure at that block, exercises the off-`K`
composition rather than stepping over it.

**Inhabitation and hole-freeness, stated separately.** §1's three theorems are **hole-free**
(axiom lines in §4 of the file, no `sorryAx`) and their hypothesis bundle is **inhabited**, not
merely non-contradictory: `he₂`, `hσ` (`WFD`), `hσc`, `hown` and the `hsrc` that `hrec` comes from
are five of the twelve premises `RecTyped.lean`'s `ntreeAux_recHargs_premises_inhabited` supplies
**outright** at `ntreeAux` — arity-0, from `ntree_stage₂_exists`, nothing hypothesised. What is
*not* inhabited is `offK_fits_hmin`'s `hfld`, which is the whole point of §4b.

### 4b. …but "off `K` the entries are free, from `OwnId` alone" is FALSE for one of the three

§T15.8 said, of all three families, that `RecTyped.lean` proves the off-`K` branch **"from `OwnId`
alone"**, and listed the own-head entries of **all three** as "discharged". Read off the compiled
signatures:

| theorem | data hypothesis | verdict |
| --- | --- | --- |
| `motiveEntry_defeq_off_K` | none | free ✓ |
| `recBody_defeq_off_K` | none | free ✓ |
| `VIndRestore.minorEntry_defeq_off_K` | **a `TeleDefEq` — `MinorFldDefEq`** | **NOT free ✗** |

`MinorFldDefEq` is one of the four open data families of `RecTyped.lean` §5, and that closure
demands `hfldD` at **every** `q`, off `K` included. So the minor entry off `K` is a *reduction*,
not a discharge.

**And it is not an idle hypothesis** — this is the part that had to be computed rather than read.
`RecTyped.lean`'s `ntree_node_fieldTypesR_ne` shows the two `atRecTele` telescopes differ, but
`MinorFldDefEq` compares them **after `substC σ` and under `liftTele (D.nm + q)`**, and a σ that
mapped the companion constant onto the restored form would have collapsed the difference and made
`hfld` free after all by `TeleDefEq.of_eq`. It does not:

    ntree_offK_minorFld_telescopes_ne  -- by decide

at `q = 0`, `ntreeAux.ctorsAll[0]? = some (0, ntreeNode)` — the own head's constructor, off `K`,
and the entry where the nested `List (NTree α)` occurrence sits. `ntree_csubst_hits_companion`
records that σ is **not** the empty substitution there, which is the trap that would have made the
inequality hold for an uninteresting reason.

**The mechanism, and it is the transferable part:** off `K` the restoration is the identity on the
own head's *application* (`OwnId.tyAppR'_eq` / `.ctorAppR_eq`) but **not** on the *field telescope*
of that head's constructors — which is exactly where a nested occurrence lives. §T15.8 generalised
"the head is reflexive" to "the entry is free" across all three families; that step is valid for
the two families whose entries are only about heads, and invalid for the one that is also about a
telescope. `minorEntry_defeq_off_K`'s own docstring says so in as many words ("the *only* residual
is the field-telescope defeq … this is **not** vacuous work"), and `RecTyped.lean` §5's docstring
says so too. **Every file was accurate; only the cross-file summary was not — and the summary is
the text a reader quotes.**

### 4c. What was amended, and it is prose only

`NestedTele.lean` §T15.8, two paragraphs. `git diff` is comment-only — every changed line is inside
the `/-! … -/` module doc; **no statement in the file changed**, which matters because two
concurrent streams import it.

* the "free … from `OwnId` alone" paragraph now says which two are free and which one is not, and
  cites the witness;
* the residual list's *"plus, off `K`, the own-head entries of all three (B) families, discharged
  as above"* now distinguishes motive/body (discharged) from minor (reduced to `hfld`). **The
  residual's arithmetic is unchanged** — `hfld` was already the second item — but its **scope** is:
  `hfld` is now known to be demanded off `K` too, so it is not a companion-only charge;
* a paragraph recording that the composition *is* verified, against the later marking.

### 4d. Grade, and what is not claimed

**Grade: a refutation of a marking, plus a citable restatement of a composition that already
existed. No obligation moved.** Explicitly not claimed:

* `MinorFldDefEq` at `q = 0` is **neither inhabited nor refuted** here. `RecTyped.lean`'s
  `ntree_minorFld_nil` inhabits it at `q = 1` (`nlistNil`, no fields) and discloses that as
  degenerate; §2 is the complementary **lower** bound — the entry where it is not degenerate is
  also the entry where nothing reflexive closes it. Those two together bracket it; neither settles
  it.
* Nothing about the **non-`D`** closures `recConstsR_wf_of_entries` / `_of_blocks` that §T15.8
  names. Their entry slots are textually identical to the `D` ones (only `hσ` differs, `WF` for
  `WFD`), so §1 transports along `CSubst.WF.wfd` — but §T15.3a records those two as **vacuous in
  `hσ`** at every parameterised block, so the `D` closure is the one the composition must fit and
  the one §1 is stated at. **A reader who "verifies the composition" against the non-`D` closures
  is verifying it against a vacuous statement.**
* No flip, no census movement, `PiInv` untouched.

## 5. Item 4: refuted on the signatures

`handoff-hyptrim.md` §3's table row: `SetModel/IndStage.lean` | `Ind_subsingleton_stage`,
`indRec_indep_of_proof_stage` (`hE`) | *"real, and zero ripple — a one-line fix each"*.

There is nothing to fix. `IndStage.lean:144` is a bare **`omit hE`** — no `in`, so it omits for the
rest of the `Discharged` section — and both flagged theorems are at `:147` and `:152`, after it.
Compiled signatures:

    @Ind_subsingleton_stage        : … IsInaccessible k → IsStageSignature k S → S.WF →
                                      IsSubsingletonSignature S → …
    @indRec_indep_of_proof_stage  : … IsInaccessible k → IsStageSignature k S → S.WF →
                                      IsSubsingletonSignature S → …
    @recGraph_unique_stage        : … IsInaccessible k → IsStageSignature k S → S.WF →
                                      IsMinorPremise S (vsetV k) R e → …          ← hE, for contrast

Neither carries an `IsMinorPremise` argument. `hE` was never a hypothesis of either.

**The mechanism, and it invalidates the scanner rather than the file.** `handoff-hyptrim.md` §3
says the scanner honours "`omit … in` and `include … in`". It does not mention the **bare
`omit …`** form, which omits for the remainder of the section. Every theorem after `IndStage.lean`
line 144 was therefore wrongly treated as having `hE` in scope.

**And the elaboration step did not catch it, for a reason worth naming.** The stated safeguard was
"each then elaborated with the hypotheses actually omitted". Omitting a hypothesis that *was never
included* elaborates cleanly — so the safeguard reports "unused, zero ripple" **precisely because
there was nothing there**. A test that passes vacuously is indistinguishable from a test that
passes. The fix for the instrument is to require, before reporting, that the hypothesis appear in
the theorem's **compiled signature** — the check run above, three `#check`s.

This does not touch the other rows: `RestoreBridge.lean`'s three were real and are fixed;
`NestedHead.lean`'s and `ConstSubstNested.lean`'s were validated by an error attributed to
consumers, which is a positive signal the vacuous-pass cannot produce; `ParamRedex.lean`'s five
were already reported as false positives. So the sweep's precision is **5 of 12**, not 7 of 12 —
and both of the two it lost are of this new kind.

## 6. Verification

* **`lake build` green, 1579 jobs** (1575 at baseline). **The +4 is not all mine**: three of the
  four new modules are concurrent streams' (`HypTrim2Witness.lean`, `OwnRule.lean`,
  `Verify/Inductive/ArgsTypedSupply.lean`); mine is the one, `ConsumeTeleOffK.lean`. Reported as
  measured rather than as the +1 I would have predicted.
* **Census 13 before and 13 after, from the same tree**: `lake env lean --run
  scripts/sorry-census-all.lean` → `HOLES … 13`, `BUILT: 396; in population but NOT BUILT: 0`
  (392 at baseline; +4 modules, same attribution as above). This round adds no holes and closes
  none.
* `ConsumeTeleOffK.olean` present at
  `.lake/build/lib/lean/Lean4Lean/Theory/Inductive/ConsumeTeleOffK.olean`, checked directly rather
  than inferred from a green build.
* **9 theorems in the new module; all `#print axioms` lines are in §4 of the file**, none carrying
  `sorryAx`: `[propext, Quot.sound]` for seven, `[propext]` for `ntree_ctorsAll_zero` and
  `ntree_zero_lt_minors`.
* **Statement preservation:** `git diff` on `NestedTele.lean` is entirely inside one `/-! … -/`
  block. `CtorBeta.lean`, `RecTyped.lean`, `IndStage.lean`: `git diff` **empty** (CtorBeta was
  edited and reverted, §3).
* **Frozen files:** `Verify/Soundness.lean`, `Verify/Axioms.lean`, `Verify/Guard.lean` not opened,
  not written, not `touch`ed; `git diff --stat` on all three empty.
* `grep -rln "^import Lean4Lean.Verify" Lean4Lean/Theory/` — empty.
* Guards recorded but **not** evidence for anything here: Guard's closure is 24 modules and
  excludes all of `Theory/Inductive/`.
* No `git` state changed. No `lake update`. Nothing sent anywhere.
* **Harness sensitivity checked before trusting a silent pass.** `lake env lean` on
  `NestedTele.lean` prints nothing on success *and* the file contains zero `#print axioms`
  commands, so "no output" is ambiguous. Appending `theorem zzz : False := rfl` produced errors at
  the appended line, confirming the whole 4268-line file elaborates and that failures surface.

## 7. Environment note for the next stream

A concurrent stream had `Theory/Typing/ConstSubstNested.lean` transiently broken for part of this
round. That module is **upstream of `NestedTele.lean` via `RestoreBridge.lean`**, so it blocks every
build in `Theory/Inductive/`, and the failed build **deleted** its `.olean`, which blocks
`lake env lean` too. `SetModel/IndStage.lean` is *not* downstream of it, which is why item 4 got
done during the outage. If `Theory/Inductive/` will not build, check that file before suspecting
your own edits.

## 8. Pick up first

1. **The `HypTrimWitness.lean` + `CtorBeta.lean` pair (§3).** Two files, mechanical, fully
   specified above. This is the smallest remaining item in this corner.
2. **The `TeleCongr.lean` module move (§2).** Three files. §1–§3's upstream move is verified sound;
   §6's is not.
3. **`MinorFldDefEq` at `ntreeAux`'s `q = 0`.** Now bracketed from both sides (§4d) and the single
   most informative open question in the minor block: it is demanded off `K` as well as on it, so
   it is not a companion-only charge, and §T16.1 claims to reduce it to the same head datum.
4. **Re-audit the `include` sweep for the bare-`omit` blind spot (§5).** The scanner is gone
   (`/tmp` copies), but the population was 785 theorems and the defect class is mechanical: any
   theorem after a bare `omit x` in the same section. Require a compiled-signature check before
   reporting.
5. **Do not trust `lean_minimal_hypotheses` without restarting the LSP first** (§1 item 5).
