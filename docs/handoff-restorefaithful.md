# handoff: `RestoreFaithful.lean` — the zero-`_nested`-constants measurement, as theorems

Owner file: `Lean4Lean/Verify/Inductive/RestoreFaithful.lean` (new, 460 lines, builds clean, zero
warnings, all axiom sets `[propext, Classical.choice, Quot.sound]` or smaller, no `sorryAx`
anywhere in any cone).  Nothing else in the tree was edited.

## The brief

A shell measurement: after declaring a genuinely nested inductive — `inductive Tree where | node :
List Tree → Tree` — an environment scan finds **zero** `_nested`-prefixed constants; the auxiliary
block lives only inside `add_inductive`.  Task: make that machine-checked, be rigorous about the
measurement/theorem gap, link the condition to `checkNoNestedAuxName`, and instantiate at
`ntreeAux` so that nothing is vacuous.

## §1 The condition on the incoming block, and the check that establishes it

* `NoNestedDeclNames types` — no member name and no constructor name of the Lean-level block
  carries the reserved prefix.
* `checkNoNestedAuxName_ok_iff : checkNoNestedAuxName n = .ok () ↔ ¬ IsNestedName n` (cone 4349).
  **Both directions**, so the condition is exactly what the landed check buys
  (`Lean4Lean/Inductive/Add.lean`:1086).
* `checkNoNestedAuxName.WF`, `guardLoop_ctors_noNested`, `guardLoop_noNested` (cone 4640),
  `addInductive_WF_noNestedDeclNames` (cone 7774): **acceptance by `Environment.addInductive`
  implies `NoNestedDeclNames`.**  The loop is transcribed verbatim from the implementation and
  every other check in it is given the trivial postcondition, so the statement carries exactly the
  contribution of `Add.lean`:1104 and :1109.  Pattern copied from
  `Verify/Inductive/RunIdentity.lean` §6.1 (`guardLoop_blockClosed`).

That is requirement (c): the condition's justification depends on `checkNoNestedAuxName`, proved
rather than asserted.

## §2 The environment condition, and preservation by the *restored* step

The environment-side condition already existed: `VEnv.NoNestedN`
(`Verify/Inductive/ProjNoNested.lean`:367) — "no declared name carries the prefix".  I reused it;
`noNestedC_of_noNestedN` there already derives the `NoNestedC` half, so there was nothing to redo.

New:

* `not_isNestedName_appendIndexAfter'_mkRecName` (cone 3565) — the renamed auxiliary recursor
  `I.rec_k` is outside the barrier.  `mkRecName n` never has macro scopes (`hasMacroScopes` tests
  the last component against `"_hyg"`), so `Name.modifyBase` is just the function; the string half
  is `"rec_" ++ toString i ≠ "_nested"`.  **This is the general version of `RestoreData.auxRec`,
  which is currently a *field*** (see the trims below).
* `NoNestedDeclNames.indDeclNames` / `.indDeclNamesN` (cone 3615) — the whole Lean-level name
  budget of a nested block, auxiliary recursors included, is clean from §1 alone.
* `VEnv.NoNestedN.addConstList` (cone 485), `.addInductR` (cone 1060) — the invariant is preserved
  by the restored step; the entire content is the *name* hypothesis.
* `VEnv.NoNestedN.addInductR_of_tr` (cone 3995) — the same with the name hypothesis discharged
  from §1, through `TrIndDeclN.mem_indDeclNamesN` (`Verify/Environment/InductR.lean`:329).  This
  is the honest form of the measurement: hypothesis on the block *the user wrote*, not on the
  abstract block, whose companion members are `_nested`-named on purpose.

## §3 The discharges, by which condition each obligation needs

| obligation | condition | status |
| --- | --- | --- |
| `RestoreData.auxRec` (`NestedRestore.lean`:308) | §1 alone | **discharged outright** — `NoNestedDeclNames.auxRecName`, cone 3588 |
| `RestoreData.ownName` (`:300`) | §1 + `run_prefix` | **discharged** — `ownName_of_gate`, cone 5796 |
| `RestoreData.ownCtor` (`:302`) | §1 + `run_prefix` | **discharged** — `ownCtor_of_gate`, cone 5796 |
| `RestoreData.head` (`:304`) | §2 + "the presented head is declared" | **reduced** — `presentedHead_clean_of_declared`, cone 671; residual named below |
| `RestoreData.headNe` (`:306`) | neither | untouched — a shape fact about `presentedHead`, not a prefix fact |
| `RestoreData.args` (`:309`) | §2 | already routed through `ProjNoNested.lean`'s `hnn` consumers |
| `(R.csubstTy D K).FreshIn env` (`RestrictStep.lean`:81, `RestrictCompanion.lean`:640/717, `SpineClause.lean`:201) | **neither** | already discharged, and *not* from either condition: `VIndRestore.csubstTy_freshIn` (`Theory/Inductive/TeleMove2.lean`:98) gets it from the type-staging success alone |

The last row is a negative result about my own condition, recorded so nobody proves it twice: the
`Restrict*` freshness hypothesis is **not** one of the things the measurement buys.

`ownName_of_gate`/`ownCtor_of_gate` are compositions of `ownName_of_run`/`ownCtor_of_run`
(`Verify/Inductive/NestedOccData.lean` §8) with §1.  §8 had already reduced those two fields to a
hypothesis about the checker's *input*, and recorded it as "the unchecked name-discipline fact
(ledger row 58)".  It is checked now; §1 is the proof.  So the payoff
`docs/decision-nested-prefix.md` promised for option (a) — "`ownName`/`ownCtor` become theorems
and three consumers unblock" — is delivered, with one qualification: the two fields need the
`run` success as well as the gate, so a caller who has only the gate still cannot build them.

**The residual for `RestoreData.head`**, precisely: `presentedHead` reads `aux2nested`'s *value*
(the nested application, e.g. `List (Tree α)`) and takes its head constant.  Nothing in the tree
proves that head is a declared constant of the ambient environment, though it must be — that is
how `replaceIfNested` found it.  A statement about `aux2nested`'s values, not about names, so §1
cannot supply it.

## §4 Instantiation at `ntreeAux` — closed, computed, non-vacuous

`ntreeAux` (`Theory/Inductive/NestedHead.lean`:624) is the parameterised nested block (`uvars = 1`,
`params = [.sort (.succ (.param 0))]`, member 0 the user's `NTree`, member 1 the companion
`_nested.List_1`).  `nfnAux` — the degenerate `uvars = 0`, `params = []` one — is deliberately not
used.

* `ntree_allNamesCR_eq` (`rfl`): `ntreeAux.allNamesCR ntreeRestore ntreeK`
  `= [NTree, NTree.node, NTree.rec, NTree.rec_1]`.  **This is the measurement, computed**: the
  restored step declares four names and not one of them is `_nested`-prefixed; the companion
  family's only trace is the renamed recursor `NTree.rec_1`.
* `ntree_allNamesCR_length = 4` (`rfl`) — so the `∀ n ∈ …` statements below are not vacuous.
* `ntree_allNamesCR_clean` (`decide`, cone 982) and `ntree_allNames_not_clean` (`decide`, cone
  792): the restored budget is clean, the **unrestored** one (`ntreeAux.allNames`, what
  `addInduct'` declares) is not.
* `ntree_addInductR_exists`, `ntree_addInductR_noNestedN`, `ntree_addIndTypes_exists`,
  `ntree_addIndTypes_not_noNestedN`, and the headline
  `ntree_restoration_keeps_the_environment_clean` (cone 1202, **no hypotheses at all**):

      from VEnv.empty, restored:   addInductR succeeds  ∧ the result satisfies NoNestedN
      from VEnv.empty, unrestored: addIndTypes succeeds ∧ the result does NOT

  Same starting environment, same block.  So "zero `_nested` constants in the environment" is a
  property of the *restoration*, not of the block — which is exactly what the restoration layer
  claims to model.
* `ntree_addInduct'_not_noNestedN` — the same contrast at the ι-rule-carrying step, from
  `noNestedN_false_of_companion` (`OccArgsTyping.lean`:337).  Conditional on `addInduct'`
  succeeding, as the general theorem is; the unconditional version is the `addIndTypes` one above.

`ntreeAux_params_WF` (NestedHead.lean:897, cone 617) was **not needed**: every statement here is
about names, and names need no well-formedness.  It is mentioned so the next reader does not go
looking for a reason it is missing.

## §5 Verdict: the condition must be **established**, and today it cannot be outside inductives

1. Not assumable: one `addConst` at a prefixed name refutes `NoNestedN`
   (`NestedWit.noNestedN_not_preserved`, `ProjNoNested.lean`:604).  An invariant must be carried.
2. The inductive branch's step is proved (§2) and rests on §1, i.e. on `checkNoNestedAuxName`.
3. The other branches break it.  `checkConstantVal` (`Lean4Lean/Environment.lean`:12) — the common
   gate of `addAxiom`, `addDefinition`, `addTheorem`, `addOpaque` — calls `checkName`, and
   `checkName` (`Lean4Lean/Environment/Basic.lean`:54) tests only "already declared" and
   `Environment.primitives`.  No prefix test.

Measured, self-checking, in the file (§5.1, a `#eval` that `throwError`s if any flag flips):

    axiom _nested.zzz : Prop        -> ACCEPTED by Lean4Lean.addDecl
    inductive _nested.Zzz : Type    -> REJECTED  (checkNoNestedAuxName firing; before it landed
                                                 this exact shape was accepted and stored)
    def _nested.ddd : Type := Prop  -> ACCEPTED

So: **every §3 discharge that needs §2 is conditional on an invariant the implementation
establishes for inductives only**, while the discharges that need only §1 (`auxRec`, `ownName`,
`ownCtor`) are unconditional for any block the gate accepted.

Where it would have to be established: by induction on `TrEnv'`
(`Verify/Environment/Basic.lean`:634 and its constructors), whose `axiom`/`defn`/`opaque`/`quot`
cases each need "the added name is not prefixed".  The single-constant step is
`VEnv.NoNestedN.addConst` (cone 491), stated so the missing hypothesis is visible in a statement.
One line beside `checkName` in `checkConstantVal` would supply it for all four branches (plus
`Quot.lean`'s `addQuot`) — another restrictive-direction divergence of the same kind and cost as
`checkNoNestedAuxName`'s.

## Proposed changes to files I do not own (NOT applied)

1. **`Lean4Lean/Verify/Inductive/NestedRestore.lean`:299 and :302** — the docstrings "**Not
   checked by the implementation.** §7" on `ownName`/`ownCtor` are **stale**.  `checkNoNestedAuxName`
   checks exactly this, and `ownName_of_gate`/`ownCtor_of_gate` are the compositions.  Docstring
   correction only, no statement change.
2. **`Lean4Lean/Verify/Inductive/NestedRestore.lean`:308** — field
   `auxRec : ∀ k, ¬ IsNestedName (auxRecName types k)` is **derivable** from
   `NoNestedDeclNames types` (`NoNestedDeclNames.auxRecName`), so it is removable if the structure
   carries the gate condition instead.  Small win: current construction sites prove it by `decide`
   anyway.  Flagged, not urgent, and the field owner's call.
3. **`Lean4Lean/Inductive/Add.lean`, `checkNoNestedAuxName`'s docstring** — it still says
   "Neither kernel checks this today … so `ownName`/`ownCtor` stay *hypotheses* rather than
   theorems -- with three consumers waiting on them."  lean4lean now does check it (the docstring
   is on the check itself), and the two fields are no longer hypotheses for gate-accepted blocks.
   Rewording, no behaviour change.
4. **`docs/decision-nested-prefix.md`** — option (a) was taken and its payoff is now delivered;
   the file still reads as an open decision.  Also its §"What I checked myself this round" claim
   that `resTy`'s conclusion "is false at exactly the inputs in question" is now moot for
   lean4lean, since those inputs are rejected.
5. **`Lean4Lean/Environment.lean`:12 (`checkConstantVal`)** — one `checkNoNestedAuxName v.name`
   beside `checkName` is what §5 point 3 needs.  Implementation change with a divergence entry;
   not mine to make, and it should be costed against the Kernel Arena first.

## For the concurrent streams

* **`StrengthenFamily.lean` / `ValAtParam.lean` / `FlipConstruct.lean`** (all around `ntreeAux`):
  if any of you needs `(R.csubstTy D K).FreshIn env`, it is **already proved** —
  `VIndRestore.csubstTy_freshIn`, `Theory/Inductive/TeleMove2.lean`:98, from the type-staging
  success alone.  Do not route it through `NoNestedN`; that is a longer road to the same place.
* If any of you needs "the restored step declares no `_nested` name" at `ntreeAux`, it is
  `InductiveDeclExamples.ntree_allNamesCR_clean` (and the explicit list is
  `ntree_allNamesCR_eq`); if you need the invariant to survive the step,
  `VEnv.NoNestedN.addInductR`.
* Nobody should re-derive `IsNestedName (auxRecName types k)`'s negation by hand:
  `not_isNestedName_appendIndexAfter'_mkRecName` is the general lemma, and
  `NestedRestoreWit.lean`:133's `nfn_auxRec` is its `nfn` instance.

## What I could not do, with reasons

* **Compose §1 with §3 inside `Environment.addInductive`.**  `addInductive_WF_noNestedDeclNames`
  gives the condition from acceptance; `ownName_of_gate` consumes the condition plus the `run`
  success.  Sequencing them into one statement about `addInductive` means reasoning across the
  gate loop and `ElimNestedInductive.run` inside the same `do` block — an `Except.WF.bind` over
  the `MWF`/`EWF` boundary, which lives in `Verify/Inductive/AddInductiveStep.lean`, a file I do
  not own.  The two halves are proved; the glue is one bind in that file.
* **Prove `TrEnv' → NoNestedN` false outright.**  It *is* false (point 3 above, and the `#eval`
  measures the acceptance), but exhibiting it as a theorem needs a `TrEnv'` instance carrying a
  `_nested`-named axiom, i.e. a `TrExprS` witness and the `axiom` constructor's side conditions.
  Priced but not built; the `#eval` plus `noNestedN_not_preserved` covers the same ground for the
  purposes of §5.
* **Discharge `RestoreData.head`.**  Blocked on the residual named in §3 (that `presentedHead`
  lands on a declared constant), which is a fact about `aux2nested`'s values.
