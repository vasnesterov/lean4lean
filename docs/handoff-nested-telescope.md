# Handoff: the nested-restoration telescope corner (`Theory/Inductive/NestedTele.lean` §T1–§T14)

**Scope.** Obligations (B) and (C) of `VEnv.addInductR_ordered'` — the recursor's restored type
and the restored ι-rules — for a nested block with **parameters** (`D.np > 0`). All the work
described here lives in `Lean4Lean/Theory/Inductive/NestedTele.lean`, which is imported only by
`Lean4Lean/Experimental/ConeJoin.lean:129` and is therefore **outside `kernel_sound`'s cone**.

## Headline, stated plainly

**(B) and (C) still do not lift off `np = 0`. The closure theorems are still not stated.**
`VEnv.recConstsR_wf_of_np_zero` and `VEnv.iotaRulesRS_wf_of_np_zero`
(`Theory/Inductive/NestedRules.lean` §7.7) remain the only closures.

What *is* true: **every identified residual except `hargs` is discharged**, and `hargs`'s
hypothesis bundle **passes row 11a's joint-satisfiability test at a real parameterised block**
(§T14). So stating the assembly is now worth doing rather than a gamble. That is the boundary
this handoff sits on.

## What I would pick up first

**State the two closure theorems** — `recConstsR_wf_of_substC'` and
`iotaRulesRS_wf_of_substC'` at `np > 0` with `hargs` as the only hypothesis — and nothing else
first. I agree with the coordinator's expectation. Two reasons specific to now: (i) row 11a has
passed, so the bundle is known non-vacuous, which was the only thing that made stating it risky;
(ii) all the glue exists (`TeleDefEq.of_entries`, `TeleDefEq.append`, the two entry defeqs, the
body defeq, `congr_tele`), so this is assembly and de Bruijn bookkeeping, not new mathematics.

One warning about *how* to do it: **do not thread `hargs` per block or per entry.**
`VIndRestore.hbody_weak` exists precisely so it enters once at the params-only context and
weakens to each entry's context. And per §T14, on a canonically stored companion it is **one**
datum, not two.

## Proved (machine-checked, all `[propext, Quot.sound]` or better)

Names are as declared; all are in `NestedTele.lean` unless noted.

**§T1–T2, transport and structure.** `VEnv.OnCtx.substC`, `HasArgs.substC`,
`HasArgsDF.substC`, `OnCtx.substC_tele`, `VExpr.map_substC_instTele`; `TeleDefEq.append`,
`TeleDefEq.of_eq`.

**§T3, the outer pi-peel.** `VConstant.WF.substC_mkPi_inv`, `VEnv.recTypeTele_substC_onCtx` —
`hsrc` + `hσ` peel the substituted recursor telescope's `OnCtx` on `Ordered` alone.

**§T4–T5, the motive entry.** `HasArgs.bvars_lt`, `motive_params_spine_false`;
`substC_motiveType_defeq_hyps_false`, `substC_motiveType_defeq_of_head_hyps_false` (the vacuity
at §8.9's own binders); the general-`Γ` repair `substC_motiveType_defeq_of_head'`,
`substC_motiveType_defeq'`, `substC_motiveType_defeq_of_head_of_gen`; and `hbv` discharged at
the real ambient context by `hasArgs_params_bvars_motiveCtx` / `_motiveCtx'` /
`_of_np_zero`.

**§T6, the minor entry** (was entirely untouched before this work).
`substC_minorType_defeq'` reduces it to two moving parts — the field telescope and the *last*
argument of the conclusion — and the `simp only` in its proof is the machine check that nothing
else differs. `substC_minorBody_defeq` does the conclusion with **one `appDF`**, not a
`HasArgsDF` spine congruence, because only the last argument moves (`mkApp_concat` splits
there). `substC_minorType_defeq` is the join, with `hbv` discharged internally
(`hasArgs_params_bvars_ctx` / `_minorCtx` / `_minorCtx'`) and **no `np` bound**. Bounded the
other way by `minor_params_spine_false`, `substC_minorType_hbv_false_of_nil`,
`HasArgs.bvars_ctx_false`, and inhabited at `np = 0` by `teleDefEq_fld_of_np_zero`.

**§T7, (C)'s telescope typing.** `OnCtx.take_of_reverse`, `IsType.mkPi_inv_of_defeq`,
`mkPi_substC_onCtx_of_defeq`, `iotaRule_tele_onCtx_of_type_defeq`; and
`substC_iotaType_defeq`, which **is** `substC_minorBody_defeq` at `nr := 0` — its proof term is
that lemma applied and nothing else. Do not count it twice.

**§T8, `hfun` is not data.** `VEnv.motiveApp_partial_hasType` (the intermediate
`VInductDecl'.motiveApp_hasType'` builds and its statement discards, `Lemmas.lean:1493`) and
`VIndRestore.substC_motiveApp_partial` (its instance at the substituted motive block).

**§T9, four residuals reduced.** `OnCtx.mkPi_entry_inv` (the *second* peel — entries are `mkPi`s
*inside* one entry of the telescope, which `take_of_reverse` does not reach),
`recTypeEntry_substC_onCtx`, `onCtx_params_append`, `Lookup.range_map`,
`VInductDecl'.lookup_motive_substC`, `HasArgs.substC_liftTele`,
`substC_minorBody_defeq_of_conv`, `minorBody_hfun_false_of_nil`.

**§T10, `hpar` free and `hpi` derivable.** `VEnv.OnCtx.noCSubst`, `OnCtx.substC_eq`,
`VInductDecl'.onCtxParamsAtRec_substC`; `VIndCtor.splitPis_type_instL`;
`VIndRestore.instAt_ctor_body_eq`, `instAt_ctor_hpi`.

**§T11, glue.** `VEnv.TeleDefEq.of_entries` (nothing turned a pointwise family of entry defeqs
into a `TeleDefEq` before), `VInductDecl'.nm_pos_of_types_ne`, `VIndRestore.hbody_weak`.

**§T12, the blocker.** `VEnv.TeleDefEq.instN`, `TeleDefEq.weakN`, `HasArgs.congr_tele`,
`VExpr.instAllTele_bvars_lift`.

**§T13, the two side conditions.** `VExpr.NoCSubst.splitPis` / `.instAll` / `.mkPi_tele`;
`VIndRecArg.canonTypeR_closedN`; `VIndCtor.fieldTypesR_closedTele` /
`atRecTele_fieldTypesR_closedTele`; `VIndRestore.fieldTypesR_noCSubst` /
`atRecTele_fieldTypesR_substC_eq`.

**§T14, row 11a.** `InductiveDeclExamples.ntree_hargs_telescopes_coincide`,
`ntree_hargs_telescope_eq`, `ntree_hargs_spine_eq`.

Two lemmas inherit `Classical.choice` from the pre-existing `VExpr.mkPi_inj`
(`Theory/Inductive/Telescope.lean:237`): `instAt_ctor_body_eq` and `instAt_ctor_hpi`, and
`fieldTypesR_noCSubst` / `atRecTele_fieldTypesR_substC_eq` through them. Nothing I wrote
introduces it. It is inside guard 2's whitelist.

## Stated-but-open

* The **closure theorems** for `recConstsR_wf_of_substC'` and `iotaRulesRS_wf_of_substC'` at
  `np > 0`. Not stated.
* `hargs` — the presented spine typed against the presented head's binders. Genuinely data:
  `VIndRestore.instAt_indep_of_tyArgs` (`NestedRules.lean:1509`) shows no
  restoration-independent argument produces it, because `instAt` takes the same value for every
  spine once the head's body is closed. Do not try to derive it from `Faithful`.
* Injectivity of `recType` in the `indices` field — and see the row-76a correction below for why
  it may never be on this path.

## Refuted / bounded

* `VIndRestore.substC_motiveType_defeq` (§8.9) is **vacuous above `np = 0`**: its `hOn`/`hbv`
  are jointly contradictory (`substC_motiveType_defeq_hyps_false`), and
  `substC_motiveType_defeq_of_head` likewise one step earlier. The advertised "no bound on
  `D.np`" was precisely wrong; the bound is `np = 0`.
* The strict-equality route has **two** `np`-obstructions — `hp : D.params = []`, and `hcl0`
  (`∀ a ∈ R.tyArgs i, a.ClosedN 0`), which the parameterised witness *refutes*
  (`ntree_not_tyArgs_closed0`, `NestedRules.lean:1105`). The **typed** route has none: it needs
  only `ClosedN D.np`, which the same witness satisfies (`ntree_tyArgs_closedN_np`, `:1116`).
  **This asymmetry has now been confirmed three times** — head defeqs, `hmatch`, and
  `fieldTypesR` closedness (`canonTypeR_closedN`). Prefer typed everywhere.
* `regularity_two_typing_false` (`Theory/Typing/PropShadow.lean:315`): the stratified two-typing
  form of regularity is outright false, which is why (C) cannot get its `type` component from
  "the type of a typed term is a type".

## What was tried and failed — and the step it failed at

This is the half that gets re-derived. Read it before proposing a route.

1. **Three routes for `hpar` (`OnCtx ((D.atRecTele D.params).reverse) (e.IsType D.recUvars)`),
   all wrong in their stated form.** (a) "Prove the `csubst`-analogue of
   `VIndRestore.noBlock_noCSubst` (`RestoreBridge.lean:160`)" — **subsumed**: `Ordered.noCSubst`
   / `IsDefEq.noCSubst'` (`Theory/Typing/ConstSubst.lean:393`, `:351`) work for *any* fresh `σ`
   and do not care that `csubst`'s domain is wider than `blockNames`. (b) "Derive
   `NoBlock D.params` from the typing" — unnecessary; `noCSubst'` *is* that argument at the right
   generality. (c) "State it as a side condition with two bounds" — not needed. The actual
   proof is `WF.onCtxParamsAtRec` + `OnCtx.substC_eq` + `csubst_freshIn`
   (`NestedRules.lean:1187`, which already needs no new side condition). **`hpar` is free.**
2. **`OnCtx.substC_eq` / `WF.params` for the *field* telescope: this cannot work.** I claimed it
   was "the §T10 argument one telescope over". It is not. `OnCtx.substC_eq` runs off a context
   typed in `env`; `C.fieldTypesR D R` is not one, and its **non-recursive** entries are
   literally `F.type`, which `Restore.lean`'s own docstring says is only *definitionally*
   block-free — a companion constant can sit under a redex inside one, so `substC` is **not**
   the identity on it by that route. The route that works (§T13): the telescope is a fragment of
   a **declared constant's type**, so `Ordered.noCSubstC` + `csubst_freshIn` + `NoCSubst`
   preservation (`instL`, `inst` existed; `splitPis`, `instAll`, `mkPi_tele` added) +
   `instAt_ctor_body_eq`. **Wrong reason, right conclusion** — and the wrong reason would send
   you to `WF.params`, where nothing about `fieldTypesR` can be proved.
3. **Inducting `HasArgs.congr_tele` on the `TeleDefEq`: fails.** In the `rfl` case the
   `TeleDefEq`'s IH sits at `A :: Γ` while the goal is at `Γ`, so the recursive call must be made
   on the *instantiated* telescope, which is not a `TeleDefEq` sub-derivation. Induct on the
   **`HasArgs`** derivation instead, with the `TeleDefEq` universally quantified;
   `HasArgs.cons`'s tail is already at `instTele a As`, so it is structural.
4. **A standalone telescope-prefix `Ctx.InstN` witness is not needed.** `TeleDefEq.instN` threads
   the witness through the induction and extends it by `Ctx.InstN.succ` at each step. A standalone
   `Ctx.InstN Δ.length (Δ.reverse ++ A :: Γ) ((instTele a Δ 0).reverse ++ Γ)` *is* constructible,
   but only by induction from the inside out, which is awkward to state. Reach for threading.
   Same shape for `TeleDefEq.weakN` with `Ctx.LiftN`.
5. **`hAs` cannot be discharged the way `hbv` was.** `HasArgs.bvars` types a telescope's own
   spine against *the telescope in the context*; `hAs` needs it against the **restored** field
   telescope that §T10's derived `hpi` delivers. The gap is bridged by `congr_tele` +
   `TeleDefEq.weakN` + `instAllTele_bvars_lift` + §T13's two side conditions. There is also a
   **second route**: `hpi` is a *hypothesis*, so the caller may convert `B` first (`defeqDF`
   along `mkPi_congrU hfld.symm`, with `hOn` free) and then `hAs` is `HasArgs.bvars` outright.
   Both meet the same de Bruijn identity.
6. **Do not derive the data residual from `Faithful`.** `instAt_indep_of_tyArgs` closes that off.
7. **§T13's deferral of row 11a was itself a mistake, and it is the most useful line here.**
   I recorded the test as un-runnable "for want of a closure statement". Row 11a is about the
   **hypotheses**, not the conclusion, so it never needed one — it could have been run two rounds
   earlier. What it actually needed was a parameterised `Faithful` witness, and
   `ntreeRestore_faithful` had been sitting in `NestedHead.lean:841` the whole time.
   **Grep for the witness before deferring the test.**

## Measured vs. read off source

**Measured** (`#eval` / `rfl` / `decide` / `#print axioms` / a green build):
`ntreeAux.np = 1` and `nfnAux.np = 0` (`#eval`); the three `hargs` telescopes at the witness all
equal `[VExpr.sort (VLevel.param 0).succ]` and the spine equals
`[(VExpr.const NTree [param 0]).app (bvar 0)]` (`#eval`, then `rfl` in
`ntree_hargs_telescopes_coincide` / `_telescope_eq` / `_spine_eq`); every theorem named above
elaborates; axiom sets as stated; guards 1–3 ✓ on
`lake build Lean4Lean.Theory.Inductive.NestedTele Lean4Lean.Verify.Guard` (1185 jobs);
`Lean4Lean.Experimental.ConeJoin` **imports cleanly** (an importability fact — *not* a census).

**Read off source, not measured:** that `ElimNestedInductive`'s `replaceIfNested` stores nested
recursive positions canonically (hence that F1 non-canonical storage is the exceptional case);
that `Built.member` is the only thing pinning `D`'s companion members; the `Faithful.ctors_complete`
→ `Declared.constants_ctor` chain giving the constructor's stored type syntactically. Treat these
as claims to re-check, not facts.

**Not run by me:** `scripts/sorry-census.lean` and `scripts/dup-names.lean`. Two streams were
mid-edit inside `ConeJoin`'s closure for most of the session; the missing `.olean` *moved between
retries*, which is the signature of an active rebuild elsewhere and the reason to report the
instrument as **not run** rather than infer a result. The coordinator's quiescent runs:
census **13**, dup-names clean, build green (1401–1402 jobs).

## The row-76a correction (important, and it is mine)

I recorded that `hargs` is "two data, and **two rather than one is forced** by the construction,
because the two blocks apply different constants with different declared types". The constants
*are* different (`List` vs `List.cons` at the witness). The **telescopes are not**, and the
telescopes are what the `HasArgs` statement mentions — F3 makes a constructor's parameter binders
a definitionally equal copy of the block's, and on a canonically stored member they are
*syntactically* equal.

Corrected:

* **`hargs` is one datum on any canonically stored companion** — every witness in this tree, and
  everything `ElimNestedInductive` generates.
* It is forced to be genuinely two **only under F1**: a companion whose stored type is presented
  non-canonically, so `splitPis npJ T.type` is not the parameter telescope. This is exactly
  §T10's asymmetry — `hsplit` is data for the type head, a *theorem* for the constructor head
  (`VIndCtor.splitPis_type_instL`, by F2).
* **F1 is therefore the only case that needs the `recType`-injectivity question**, so that
  question may never be on this path. Do not treat it as blocking.

"Forced" was too strong. Both this and the `WF.params` error above were caught by **building a
witness**, not by re-reading the argument.

## Traps

* **Instrument 7 (`[]`-vacuity) on every new statement, including composed ones.** Three
  collapses in this corner: `substC_motiveType_defeq` at `np > 0`; the minor `hbv` at `Γ = []`
  (`substC_minorType_hbv_false_of_nil`); and `substC_minorBody_defeq`'s `hfun` at `Γ = []`
  (`minorBody_hfun_false_of_nil` — a `bvar` head has no type in the empty context, so **every
  §T6 statement is vacuous at `[]`** and the general-`Γ` form is forced, not merely convenient).
  A conjunction of individually non-vacuous statements can still be jointly empty: check the
  composed statement.
* **What stops the collapse recurring at entry 0 of the composed bridge:** the parameter block is
  identical on both sides, so it costs `TeleDefEq.rfl` — **a constructor carrying no typing**.
  Had the parameter block moved, entry 0 would need a defeq at `[]` and the `bvars` spine would
  be out of scope there.
* **`VInductDecl'.WF.types_ne` is load-bearing for §T6's satisfiability.** It gives `D.nm ≥ 1`
  (`nm_pos_of_types_ne`), which keeps every minor entry's ambient context non-empty and so keeps
  §T6 out of `minorBody_hfun_false_of_nil`. Not visible from §T6 alone.
* **Keep `PiInv` out, and this matters more now.** `HasArgs.of_mkApp'`
  (`Theory/Typing/PatWF.lean:146`) takes `env.WF` **and** `env.PiInv`. `ConvPiFromEntry` is false
  over `Ordered`, and the Π/Π-inversion corner's residual is now `trans`, so routing through it
  puts this whole cone behind `VEnv.WF` *and* behind live work. Nothing in `NestedTele.lean` uses
  it — the only occurrences are prose saying so; keep it that way. All the conversions here are
  **forward** (substitution, weakening, `defeqDF`), never spine inversion.
* **`VIndCtor.typeR` must not become the substitution** (row 36).
* **Do not add a conjunct to `AddNested` / `Built` / `InductStepNested`.** `SubstFree` would have
  to move from `NestedRules.lean` to `Restore.lean` first.
* Statements about the *entry* defeqs need their own `OnCtx`: `IsType.mkPi_congr'` discharges it
  internally at the **outer** bridge, but the entries go through `mkPi_congrU` (a `TeleDefEq.cons`
  needs a defeq *at a sort*, not an `IsType`), which takes `hOn` explicitly.
  `OnCtx.take_of_reverse` + `OnCtx.mkPi_entry_inv` supply all of them from one telescope typing.

## Ownership as of this handoff

`Theory/Inductive/*` (incl. `NestedTele.lean`, `NestedHead.lean`, `RestoreBridge.lean`) and
`Theory/Typing/ConstSubstNested.lean`. **Not** `Verify/*` (two streams inside it), not
`Theory/SetModel/*`, not `Theory/Typing/{Inj*,CR*,ParRedK*,K*,Strengthen*,UniqueTyping,`
`NormalEqStrengthen,ChurchRosser}`. `Verify/Soundness.lean`, `Verify/Axioms.lean`,
`Verify/Guard.lean` are frozen. Do not edit `Experimental/ConeJoin.lean` — `NestedTele.lean` is
already imported there (line 129), so no import line is owed.
