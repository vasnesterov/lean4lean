# The vacuity ledger

*Written 2026-08-31, after four instances of the same failure mode turned up in one round, and
a survey then found four more already refuted elsewhere in the tree. Seventy-eight statements are
now measured; twelve are vacuous, near-vacuous or false, and one of those twelve is a design
ruling of my own (row 36), three are refuted outright, two routes
are dead, and nine are bounded or acquitted.*

**The injectivity corner's semantic tally is now final: 1 usable conjunct of 5**, and per rows
30/30a the remaining tax is a single shared node. The whole corner is now:

| target | needs |
| --- | --- |
| hole A, over `PiInv` | `ConvStep2 ∧ SortInv` |
| hole B | the five conjuncts (incl. `PiInv`) `∧ ConvStep2` |
| full nine-entry `RigidShapeUniq` | hole B `∧ SortInv` |

So **`ConvStep2` is the node both holes share**, not the remainder of one — effort on it pays
twice. `ConvStep2` itself is still open, and `convStep2Level_iff_sortUniq` shows identifying the
two link levels *is* `SortUniq`, so all the slack lives in its `∃ u`. Two of
`rigidShapeUniqNS_iff_family`'s five are positive and need faithfulness no soundness model has
(rows 8–9); two are refuted even under `CoherentOn` (row 29); only the sort/Π one is live, and
`interp_sort_ne_interp_forallE` already proves its residual. Everything else in that corner is
syntactic.

## 0. Why this file exists

This project has two automated measurements of how far the proof has to go, and **both are
blind to the same failure mode**.

| instrument | counts | blind to |
| --- | --- | --- |
| `scripts/sorry-census.lean` | declarations whose value mentions `sorryAx` | a hole that is not a `sorry` |
| guard 3 (`Verify/Guard.lean`) | `partial` / `@[extern]` / `@[implemented_by]` reachable from `addDecl` | anything in the *specification* |
| `scripts/hole-cone.lean` | which `sorry`s a given theorem depends on | **a hypothesis** — a cone walks `deps`, and a hypothesis is not a dependency |

### Four kinds of overstatement, each needing a different guard

Recorded on 2026-09-01 after all four occurred in a single day, all mine. They look alike in a
report and are not alike at all.

1. **Fabricated citation.** Row 11b named `not_modelFitsInput` in its *witness* column and no such
   theorem existed — a claim recorded as a result, in the one document whose value is that every row
   is backed by something proved. *Guard:* every witness column carries a `file:line`; a row without
   one is a claim (row 11b′).
2. **Measurement by grep.** "`staged` occurs 46 times, so the repair is incomplete" — those were
   `StagedOcc`/`stagedOcc` identifier hits; the field did not exist and the repair had landed.
   *Guard:* structural facts need a structural query (`grep "staged :"`, `#print axioms`, the LSP),
   never a substring count.
3. **Dropped qualifier.** "`IsDefEqU.sort_forallE_inv` is proved" — true of its local `sorry`, false
   of its axiom set, which carries both holes it would be used to attack (row 41). *Guard:*
   `#print axioms`, not the absence of a `sorry`.
4. **False negative asserted as established.** "Every route to `ConvStep2` goes through `sortDF`" —
   refuted in three lines, and the claim was in the source file too (row 40). *Guard:* a negative is
   a theorem like any other; if it is not proved, mark it a conjecture. An unproved negative is
   worse than an unproved positive, because it stops people looking.

Kinds 1 and 4 are the expensive ones: both send work in the wrong direction, and kind 4 also
suppresses work that would have succeeded.

**A refutation is only as strong as the reachability of its witness.** Rows 32 and 33 were both
filed as "refuted" and they are not the same thing: `descend` fails at `refParams` over `refEnv`,
an instance that *exists*, so its `sorry` is unfillable; `parRed` fails only at a `Params` instance
registering an `.app` pattern, and **no instance in this tree does one** — indeed `refParams` *proves*
the `ParRedK` statement. Flattening the two cost a round of misdirection. **Grade every refutation
by whether its witness is reachable**, and say so in the row.

**An instrument can also be simply wrong, which is worse than blind.** `scripts/hole-rank.lean`
built its graph with a filter that excluded internal names, so a declaration compiled by
well-founded recursion (its recursive calls routed through `NormalEq.trans._unary`) had no outgoing
edges and every walk truncated there. It therefore reported `NormalEq.descend`'s cone as *not*
reaching `IsDefEqU.weakN_iff` when it reached it in seven hops — it printed "no cycle" at the one
place a cycle existed — and every `users`/`sole` figure it produced was an undercount
(`weakN_iff` 60 → 69 in the Guard+K closure). Fixed 2026-08-31: internal names are pass-through
nodes in the graph, `inScope` filters only what is counted and printed. **Every transitive-user
count quoted before that fix is a floor, not a figure.**

**A seventh, and it is cheap to test for, which is why missing it three times is embarrassing.** A
statement can be green because its hypotheses are **unsatisfiable at the degenerate instance** —
empty context, nil telescope, zero grade — while being perfectly good at the general one. Three
statements in the nested-telescope corner were empty at `Γ = []` above the trivial case (rows 65a,
70e), each found only by instantiating there deliberately. The general form was *forced* in all
three, so nothing was lost; but a round was spent reporting one of them as a win. **Before
reporting any statement, instantiate it at the degenerate instance and confirm the hypotheses are
satisfiable.** One `lean_multi_attempt`, and it has paid three times.

**And fixing one instrument is not fixing the instruments.** `scripts/sorry-census.lean` and
`scripts/weakn-gate-split.lean` carried the *same* line (`if n.isInternal then continue` inside
the graph build) for a further day, so every count they produced in that window was an
undercount too — repaired 2026-09-01, and the headline figure moved materially:
`IsDefEqU.weakN_iff` has **296** transitive users, not 293, and the typing half frees **43** of
them, not 18 of 131 (`docs/handoff-weakn.md` §5.3, where the old figures are kept alongside the
correction). When an instrument is found wrong, grep every script for the same construct before
recording the fix.

And a **sixth**, and it is the most dangerous so far because it sits *below* the field level that
row 11a taught us to check. `SetModel.Above M P := ∃ m, IsInaccessibleChain m M.κ → P`
(`InterpSound.lean:696`). If there is **any** `m` at which `M.κ` fails to be a chain, that
implication is vacuously true and so is `Above M P` — **for every `P`, including `False`**. And such
a `κ` exists: `not_isInaccessibleChain_const` (`InaccChainOmega.lean:303`). Every field of
`OracleOK`, `QuotOracleOK`, `InductOracleOK` and `DefEqOK` is an `Above`. **CORRECTED, same day, and the correction is mine to own.** I wrote that "any such claim stated at
an *arbitrary* `κ` measures nothing" and that every pre-existing positive bound needed re-auditing.
**Both halves were wrong**, and this is the taxonomy's kind 4 — a hazard asserted as established
without checking whether anything actually exhibited it.

*Arbitrary* means universally quantified: instantiate at `omegaChain V` and `above_iff_of_chain`
strips the wrapper, so **a `∀ κ` claim is exactly as strong as its payload at the only `κ` the
reduction uses**. The genuinely worthless shape is a claim that *chooses* its `κ` — `∃ κ` with no
chain condition, or a fixed non-chain `κ` — and **the audit found none in the directory**: every
`∃ κ` statement there carries `IsInaccessibleChain` in its body. Stronger still,
`ModelFitsLeanInput` takes `hκ` as a hypothesis, so the wrapper collapses *inside* it: four
equivalences (`oracleOK_iff_of_chain`, `defEqOK_iff_of_chain`, `inductOracleOK_iff_of_chain`,
`coherentOn_iff_of_chain`) show **the wrapper weakens nothing at or below `ModelFits`**.

What survives is a real but narrow hazard, and one actual gap. The hazard: `above_false_zeroChain`
proves `Above ⟨fun _ ↦ ∅, ls, c⟩ False` with **no hypotheses at all** — `IsInaccessible` demands
`ω ∈ k`, so `∅` fails at length 1, which is cheaper than the `not_isInaccessibleChain_const` witness
I cited. So the wrapper *is* trivially satisfiable at a chosen bad `κ`; nothing in the tree chooses
one. The gap: `coherentOn_zero`'s conclusion was wrapped with no stripped restatement — the single
row of the audit table needing repair, now supplied as `coherentOn'_zero`. **Guard, in its
surviving form: a positive bound must factor through `Above.pure`, be stated with the wrapper
stripped, or quantify over `κ` — but never choose one.**

And a **fifth**, found by measurement on 2026-08-31 and the subtlest so far: **a model-side
statement can be vacuous because the model has no valuation for the context the judgement lives
in.** `interpCtx M L [∀ p : Prop, p]` is empty — the denotation of `∀ p : Prop, p` is `∅` in every
model and on both branches of the proof split — while the context itself is legitimate over every
environment. So any hypothesis of the shape "for all `ρ ∈ interpCtx M L Γ` …", quantified over all
`Γ`, is false. Rows 23–24 are the first measurement of that debt; nothing in this repo looks for
it, and it is invisible to all four instruments above because it is neither a `sorry`, nor a
marker, nor a dependency, nor a named hypothesis — it is an emptiness inside a hypothesis that
looks perfectly ordinary.

And a fourth blindness, the mirror image of the third and just as costly: **an obligation
carried as a hypothesis of a *proved* theorem counts as zero.** `VEnv.addInductR_ordered'`
(`Theory/Inductive/NestedOrdered.lean:146`) is proved, sorry-free, and in nobody's hole cone —
and it carries three undischarged obligations (`hctors`, `hrecs`, `hrules`) that are the entire
nested-soundness content of the inductive route. Factoring a hole into named hypotheses is good
practice and this repo does it well; the cost is that the census then reads 0 where the work
is. §6 lists the four such obligations that block the goal today.

The failure mode none of them sees: **a statement that is green because it says nothing.**

A lemma whose hypotheses cannot be jointly satisfied is *provable*, records as sorry-free,
appears in no cone as a hole, and contributes exactly nothing. It is strictly worse than a
`sorry`, because a `sorry` is honest — it is red, it is counted, and it names itself. A
vacuous lemma looks like progress.

Guard 2 — the stop condition — is `#print axioms Lean4Lean.kernel_sound`. It cannot tell the
difference. **A chain of vacuous lemmas can make guard 2 print "proof COMPLETE" over a proof
of nothing.** That is not a hypothetical; §4 below is a machine-checked demonstration.

So: a third instrument, `scripts/empty-inductives.lean`, plus this ledger, which is the part
that cannot be automated — for each load-bearing statement, whether its hypotheses are
known-satisfiable, known-unsatisfiable, or **unmeasured**.

## 1. The root: one empty inductive

    ~/.elan/bin/lake env lean scripts/empty-inductives.lean
    empty-inductives: 1 in the Lean4Lean namespace
      Lean4Lean.AddInduct: reach 31, Prop  <-- VACUITY SOURCE

`Lean4Lean.AddInduct` (`Verify/Environment/Basic.lean:149`) is declared

    inductive AddInduct (m₁ : ConstMap) (env₁ : VEnv) (decl : VInductDecl')
        (m₂ : ConstMap) (env₂ : VEnv) : Prop
      -- TODO

with **no constructors**, and it is the single root cause of every entry in §3. It is the only
empty inductive in the package, and the mechanism by which it does damage is worth stating
precisely, because it is *not* the obvious one:

1. `AddInduct` is empty, so it is equivalent to `False`.
2. It appears as a **premise of the `induct` constructor of `TrEnv'`**. So that constructor can
   never fire, and `TrEnv' safety m Q venv` is unsatisfiable for any `m` holding an
   `.inductInfo` at the relevant safety level. This is not vacuity — it makes `TrEnv'` *too
   strong*, i.e. false where it should hold.
3. *Therefore* every statement that takes `TrEnv'` (or `TrEnv`, or `VEnvs.WF`) as a
   **hypothesis** at such an environment is vacuous.

Two hops, and the second hop is where the green comes from. Both `AddInduct.to_addInduct`
(`Basic.lean:153`, proved `nomatch H`) and `VEnvs.WF.no_inductInfo`
(`Verify/InductFlip.lean:366`) are the emptiness in usable form.

`scripts/empty-inductives.lean` prints `reach` = the number of declarations naming `AddInduct`
directly. Today all 31 are `AddInduct`'s own auto-generated eliminators, `TrEnv'`'s API, and
`AddInductFlip`. That is the blast radius to audit.

## 2. The flip, stated exactly

The repair has a name in the tree already. `AddInductFlip`
(`Verify/Inductive/AddDeclWF.lean:463`):

    def AddInductFlip : Prop :=
      ∀ {m m' : ConstMap} {env env' : VEnv} {D : VInductDecl'} {K : List Name} {R : VIndRestore},
        AddInductStagesR m env D K R m' env' → AddInduct m env D m' env'

and `InductStepNested.trEnv'` (same file, :470) proves that **the flip alone** carries the
honest arm to the `TrEnv'` step — no extra hypothesis, no side condition. So the distance from
here to a non-vacuous `TrEnv'` is exactly this one `Prop`.

Discharging it means giving `AddInduct` constructors, which turns
`AddInduct.to_addInduct`'s `nomatch H` into a real obligation. Its cost is measured in
`docs/critical-path.md` §"what the flip costs": census **14 → 17**, the three being
`reduceProjCore_none`, `reduceProjCore.WF`, `inductiveReduceRec_eq_none` — theorems asserting
the checker never handles inductives, sorry-free today *only because* `AddInduct` is empty.

**This is the human's decision and no agent should take it.** It is not a frozen-file edit
(`Basic.lean` is proof machinery); it is a decision only because it raises the census, and a
rising census is the one thing that looks like regression while being progress.

## 3. Registry of measured statements

Every row is backed by a **proved** lemma in the tree, not an argument in a docstring. Kinds:

- **vacuous** — the statement's own hypotheses are jointly unsatisfiable; it is provable and
  says nothing.
- **false** — the statement is refutable as written; it must be *re-derived from a different
  statement*, never assumed.
- **dead route** — a proposed sufficient condition is itself unattainable, so that route to
  the goal is closed (this is useful negative information, not a defect).
- **bounded** — a residual hypothesis proved *neither* trivially true *nor* false. This is the
  good outcome and the discipline §5 asks for.

| # | statement | kind | proved by | flip repairs? |
| --- | --- | --- | --- | --- |
| 1 | `addDecl.WF`, `inductDecl` branch | **false** | `addDecl_inductDecl_WF_false` (`Verify/Inductive/AddDeclWF.lean:306`) | **yes** — this is the flip's purpose. Reshape to `AddDeclPost` meanwhile. |
| 2 | `foldAddDecl_tr` (`Verify/Bridge.lean:172`) | **false** |  `foldAddDecl_tr_false` (`Verify/PreludeVacuity.lean:93`); **proved theorem, see §4a** | **yes** |
| 3 | `PreludeBridge stdPrelude` (`Verify/Bridge.lean:225`) | **vacuous** | `preludeBridge_vacuous_at_nil` (`PreludeVacuity.lean`) | **yes** — real only after the flip |
| 4 | `TrEnv .safe env venv` at any `env` holding a safe inductive | **false** | `TrEnv.not_safe_inductInfo` (`PreludeVacuity.lean:73`) | **yes** — the mechanism itself |
| 5 | `addQuot.WF`, non-initialized branch | **vacuous** | `addQuot_trivial_of_wf` (`Verify/QuotReach.lean:261`), `no_wf_envEqInd` (:241) | **yes** |
| 6 | `coherentOn_addConstList` / `coherentOn_addInduct`, `hocc` at the pre-block environment | **vacuous** | `addConstList_hocc_unsat` (`Theory/SetModel/CnstRecursion.lean:117`), `hocc_unsat_eqIndDecl` (:150) | **no** — independent mis-statement; repaired by `StagedOcc` + `coherentOn_addConstList'`, separation witnessed by `stagedOcc_separates` (:179) |
| 7 | model parameter `LevelAssign` | **circular** — the parameter *contained* the hole it was used to prove | `levelAssign_gives_sortUniq` (`Theory/SemanticRouteClosed.lean:136`) | **no** — independent; already repaired by replacing the parameter |
| 8 | `LevelSeparating` as a route to `SortUniq` | **dead route** | `hasChains_refutes_levelSeparating` (`SemanticRouteClosed.lean:235`) | n/a |
| 9 | `ForallPropDomInj` (`PiInv`'s domain conjunct) | **dead route** | `not_forallPropDomInj` (`SemanticRouteClosed.lean:403`) | n/a |
| 10 | `OracleOK` residual | **bounded** | `not_oracleOK_falseProp` (`CnstRecursion.lean:651`) — not satisfiable by an inconsistent oracle | n/a |
| 11 | `InductOracleOK` residual | **its first field `staged` is FALSE at ordinary blocks**, so the residual is unsatisfiable there and `coherentOn_cnstOf`'s `.induct` case is **vacuous** at every declaration list holding an inductive whose declared types name an ambient constant. `staged` quantifies over *all* `env`, and `addInduct'` checks no types, so it is instantiable at `VEnv.empty` — forcing the first type former's stored type to mention **no constant whatsoever**, while `VInductDecl'.WF` asks only that it be a type over the ambient environment. **Repaired**: `stagedOcc_allConsts` gives the field unconditionally from `Ordered` + `D.WF`, so the residual drops from three fields to two (`InductOracleOK₂`, `coherentOn_cnstOf₂`), and nothing is lost | `not_inductOracleOK_of_head_const`, `not_inductOracleOK_boxDecl`, `not_oracleFits_boxDecl`, `coherentOn_cnstOf_vacuous_boxDecl`, with the certified two-declaration history `boxDecl_history` (`Theory/SetModel/InductOracleAudit.lean`) | n/a |
| 11a | **row 11's own "bounded both ways" claim** | **the two-way bound did not cover the broken field.** `inductOracleOK_empty` is at the block with *no type formers*, whose `allConsts` is `[]` (`empty_block_allConsts`, `rfl`) — so its `staged` is `True`. The positive bound said nothing about the field that is refuted, which is exactly how the defect survived an audit that was supposed to catch it. **A two-way bound must be checked field by field, not on the structure as a whole** | measured by the model stream, 2026-08-31; the repaired residual *is* bounded both ways (`not_inductOracleOK_falseProp` transfers via `.consts`, `inductOracleOK_empty` via `.to₂`) | n/a |
| 11b | `ModelFitsInput` / `CnstRecursion.upper_bound_of` | **row-2-shaped**: a proved theorem whose second hypothesis is false exactly when it has anything to say. **And one level deeper than this row first claimed** — the same refutation kills `leanTTConsistent_of`'s hypothesis `H` *verbatim*, so it is not an artefact of §7's packaging. Cause: `noUnsafe` excludes only `.unsafeDef`, **not `.axiom`**, and `VDecl.WF`'s `.axiom` rule asks only that the type be a type — so `axiom Bad : ∀ p : Prop, p` is a certified one-declaration history. Repair, conceding nothing: narrow to `PureOverPrelude`, since `.axiom` is the one former that is `noUnsafe` but not `isPure` (`leanWF_iff`, `upper_bound_of_omega`) | `not_modelFitsInput`, `not_modelFits_uniform`, `badAx_history`, `badEnv_not_consistent` (`Theory/SetModel/ModelFitsVacuous.lean`); bounded both ways by `not_pureOverPrelude_badAx` / `pureOverPrelude_prelude`, and closed in general by `axiom_mem_pureOverPrelude` | n/a |
| 11b′ | **this row's own witness column, as I first wrote it** | **the citation was fabricated.** Row 11b named `not_modelFitsInput` as its witness with no `file:line`, and **no such theorem existed** — I recorded a claim as a result in the one document whose value is that every row is backed by something proved. It is now proved (above), but the ledger asserted it for a full day before anyone checked. **Every witness column in this file needs a `file:line`, and a row without one is a claim, not a measurement.** | found by the model stream, 2026-09-01 | n/a |
| 40 | "every route to `ConvStep2` goes through `defeqDF`'s `sortDF` premise, so aligning the two link levels *is* `SortUniq`" — mine, and also stated in `InjChainStep.lean` §6 | **false.** `BaseUniqChain.ConvC.transport` builds one `defeqDF` per chain link at an **arbitrary** type, never at a pair of syntactic sorts; at a `.bvar` midpoint the two base types are *syntactically equal* (`Lookup.uniq`), so no `sortDF` link exists. `ConvStep2` holds **unconditionally** at `.bvar`/`.sort`/`.const` midpoints from `Ordered env` alone, so the obstruction is exactly Π- and application-headed midpoints | `convStep2At_of_baseUniqCAt`, `convStep2At_of_midFree`, `convStep2At_sort_discharges` (`Theory/Typing/InjMidpoint.lean`) | n/a |
| 41 | `IsDefEqU.sort_forallE_inv` (and `WF.sortUniq'`) as "proved" | **available only with a qualifier I dropped.** Neither has a local `sorry`, but `#print axioms` on `sort_forallE_inv` gives `[propext, sorryAx, Classical.choice, Quot.sound]` — its `trans` case consumes **hole B**, its `proofIrrel` case **hole A**. So it must not be fed to anything attacking either hole. "No local `sorry`" is not "available"; the test is `#print axioms` | measured by the `ConvStep2` stream, `Injectivity.lean:1252` and `:556` | n/a |
| 46 | `AppKetaRow`'s "hard half" | **free.** `EtaKNormalEqInv` factors the row into a statement mentioning no development, and follows from `WeakNInvDS` alone; its core `NormalEq.ketaHere_inv` is **unconditional**. So "the residual is entirely on the function side" resolves to: the function side is what `descendV` already handles, `etaL` included | `etaKNormalEqInv_of_weakNInvDS`, `NormalEq.ketaHere_inv` (`Theory/Typing/KKetaRow.lean`) | n/a |
| 47 | "what would close `AppKetaRow` is a relation strictly between `DomEq` and `NormalEq` that commutes with `ParRedK` unconditionally" — mine, and repeated from `KSite7Rows.lean` | **a dead end.** Any relation containing an eta constructor loses head-shape preservation, which is the *only* reason `DomEq.parRedK` goes through. What actually works is two unrelated things: a **grading** of `ParRedK` by redex-nesting height (so `keta` descends — `ParRedKn`, whose `weakN` and `app_bvar` are grade-*preserving*, exactly where derivation size and `\|H1\|+\|H2\|` fail), and separately **narrowing one operand of `NormalEq.trans` to `DomEq`** — a composition lemma, not a new relation | `ParRedKn`, `ketaRow_of_weakNInvDS`, `parRedKStatementN_zero` (hole-free), `ketaRow_of_weakNInvDS_at_one` (same file) | n/a |
| 48 | site 7's two `weakN_iff` entries | **one removed.** `NormalEq.trans`'s appeal to strengthening needs `etaR` left **and** `etaL` right, so killing either suffices: `DomEq.trans_normalEq` / `NormalEq.trans_domEq` are clean of `weakN_iff` *and* `rigidShapeUniqNS` (cone 3510). `etaR_case_clean`'s type is **character-for-character identical** to `etaR_case`'s, and only the latter carries `weakN_iff`; checked in situ by `parRedKStatement_of_rows_clean`. The surviving entry is `appDF × beta` via `ParRedExt.parRed_beta` | same file | n/a |
| 49 | my `NormalEq.trans` call-site count | **wrong two ways at once.** I said "30 call sites, 10 outside `ChurchRosser`" while my own parenthetical summed to 8. Measured: **28 uses, 8 outside** by occurrence; **11 direct users** by declaration (`ChurchRosser` 6, `KCanonical` 3, `KSite7` 1, `KSite7Rows` 1). I was occurrence-counting and declaration-counting in the same sentence, transposed. `Experimental/NormalEq.lean`'s hits are a *different* `NormalEq.trans`, over `TY` | `lean_references` at `ChurchRosser.lean:604` plus a reverse-dep walk | n/a |
| 43 | `VEnv.ConstAppSkipUninhab` — `weak'_inv`'s residual, localised | **a genuine reduction, hole-free**: arbitrary `Ctx.Lift'` → one binder, and that binder may be assumed uninhabited in its own prefix. Cone 1207 with **no** holes, and `ConstAppTypeStrengthen.skip_step` gives the converse pointwise, so nothing is conceded. Complementary bound: the residual *holds* at every depth over **inhabited** lifts (`constAppTypeStrengthen_inhab`, cone 1156, no holes), strictly extending the depth-zero bound. Content survives exactly to the extent uninhabited types over `VEnv.WF` exist — itself open | `constAppTypeStrengthen_of_skipUninhab`, `skip_step`, `constAppTypeStrengthen_inhab`, `Ctx.InhabLift.sorts` (`Verify/Typing/ProjWeakInv.lean`) | n/a |
| 44 | my concentration warning for `weak'_inv` — that discharging it would newly land users on `rigidShapeUniqNS` | **false.** `rigidShapeUniqNS` *and* `NormalEq.descend` are already in `TrExprS.weakFV'_inv`'s cone without passing through `weak'_inv`, by two explicit paths; and `rigidShapeUniqNS` is not "new with `HasArgs.of_mkApp`" — it arrives with Π-inversion generally, via `IsDefEqU.forallE_inv` (cone 3537). Nothing is relabelled for any actual consumer | measured by the `weak'_inv` stream, 2026-09-01 | n/a |
| 45 | "the sole consumer `TrExprS.weakFV'_inv` cannot supply `OnCtx Γ`" — mine | **false.** `VLCtx.FVLift'.wf` (`Verify/Typing/Lemmas.lean:314`) converts `VLCtx.WF` for the larger context to the smaller, and `weakFV'_inv` **already calls it** at `Lemmas.lean:2001`. Consequence: "close the bookkeeping gap independently" buys nothing — `weakN_iff` reaches the consumer by a path that never touches `weak'_inv`, so the 3661 → 3628 cone drop I quoted is an artefact of viewing it in isolation | `TrProj.weakFV'_inv_of_strengthen` (proved by construction) | n/a |
| 42 | `rigidShapeUniqNS_iff_family` as an unqualified `iff` | **carries two side hypotheses** my table omitted, `hsu : SortUniq` and `htr : ProofTransport`. Only the ⟸ direction is `SortUniq`-free — which *is* the direction rows 30/30a use, so those rows stand, but the `iff` is not available without `SortUniq` | `RigidNodeCircle.lean:245` | n/a |
| 11c″ | **Input A** of `CnstRecursion.lean` §7 | **DISCHARGED.** `ModelExistsInput` really was Foundation-gluing, ~10 lines: `Theory.small_satisfiable_of_consistent` returns a model in `Type 0` for `ℒₛₑₜ : Language.{0}` (so no `ULift` is needed, and none is available), `QuotNormalize` quotients the bare structure's arbitrary congruence into a `SetStructure`, and the `𝗘𝗤` instance that step needs comes from the theory via `eq_subset_zfcInacc` — the two non-obvious steps that had kept it unapplied. So `inaccModelInput : InaccModelInput` is a **theorem**, and `upper_bound_of_modelFits` puts the whole model side on **one** input | `modelExistsInput`, `inaccModelInput`, `upper_bound_of_modelFits` (`Theory/SetModel/ModelExists.lean`); bounded both ways by `consistent_of_setModel` / `modelExists_iff_consistent` (the *consistency-free* form is equivalent to `Consistent 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰` — deliberately **not** stated as `↔ True`, which is true and useless) and `not_forall_model_false` (the row-24 test: under consistency the class the premise binds over is inhabited) | n/a |
| 62 | `PropDescend env 0` as a top-level model input | **replaced by `InstDescendUp env 0`.** `modelFits_of_propSplitUp_inputs` needs only `Ordered`, `PropUniq 0`, `PropTypeAgree 0`, `InstDescendUp 0` and `OracleFits`. Bounded both ways — `propDescend_iff_instDescendUp : PropDescend nv ↔ SortLiftDescend nv ∧ ProofLiftDescend nv ∧ InstDescendUp nv` — so the *only* difference between the old and new reductions is the two strengthening-shaped `lift` fields (`IsDefEqU.weakN_iff`, 211 users). Field-by-field witnesses per row 11a, the second field's conclusion being a *proof* so it is not an instance of the first. Technical content is `Ctx.Lift'.split_mid`: a lift splits at a marked context entry, with **no typing and no environment** | `modelFits_of_propSplitUp_inputs`, `propDescend_iff_instDescendUp`, `instDescendUp_{prop,proof}_inst_witness` (`Theory/SetModel/PropUpFits.lean`) | n/a |
| 62a | **`docs/model-interface.md`'s 2026-08-30 entry** | **it was ahead of the machine-checked chain — a doc optimistic relative to the proofs, the opposite of my usual direction.** It already listed the model import as `PropTypeAgree ∧ PropUniq ∧ InstDescendUp`, and `PropSplitUp.lean` (684 lines, sorry-free, in ConeJoin) really had reduced `Stable` to `InstDescendUp`. **But that entry was never connected to `ModelFits`**: `ModelFits` fixes one `L` for all components, `AboveAudit.ctxAgreeRd_propSplitOf` was the tree's *only* producer of `CtxAgreeRd` and is proved for `propSplitOf` alone, `exists_stable_propSplitUp` says nothing about its `L`'s relation slot, and `R := Eq` fails `hRd`. So before row 62 there was **no path at all** from `InstDescendUp` to `ModelFits`, and the sole route did take `PropDescend 0`. Both documents were wrong in opposite directions; they now agree | verified by the model stream, 2026-09-01 | n/a |
| 63 | `PropTypeAgree env 0` | **irreducible, and already tight** — `nonempty_propSplit_iff_agree : Nonempty (PropSplit env nv) ↔ PropUniq nv ∧ PropTypeAgree nv`, so **no choice of predicate removes it**, the `propSplitUp` route included. Lower bound machine-checked (`sortNotProof_of_propTypeAgree`), upper bound `PropTypeAgree.of_zero`. Not junk-refutable either: a row-24-shaped search over arbitrary `Γ` with no `OnCtx` found nothing, because two types of differing prop-ness reduce at every head either to `PropUniq` or to a genuine defeq between unrelated types. It is the real unique-typing content | `NotProofNoModel.nonempty_propSplit_iff_agree` | n/a |
| 64 | "`TypingStrengthening` is an obligation stated without an inhabitant its consumers always have" — my own suggestion to test the manoeuvre that had worked three times | **closed as a route, by a proved negative.** Every instance whose *stripped entry* has an inhabitant is already a theorem with no hypothesis at all (`TypingStrengthening.of_instN`, `[propext, Quot.sound]`), and at the one-entry level the uninhabited restriction is *equivalent* to the unrestricted statement (`TypingStrengthening1.split`, clean, `Ordered` only). So an extra hypothesis can relieve the typing half only by yielding an inhabitant of the stripped entry — and any consumer holding one needs no hypothesis. This is the typing-half analogue of `Strengthen.lean` §12, which had covered only the conversion target | `TypingStrengthening.of_instN`, `PiDescend.of_instN`, `TypingStrengthening1.split`, `TypingStrengthening1Uninhab.typingStrengthening1` (`Theory/Typing/StrengthenInhabGate.lean`), all four `sorryAx`-free — re-verified by me, not taken on report | n/a |
| 64a | **row 64's own reduction, as the stream's prose stated it** ("`TypingStrengthening` ⟺ one-entry ⟺ uninhabited-entry, both ways") | **the two halves have different hygiene, and only the weaker one is clean.** The direction that *closes the route* — inhabited instances are free — is `sorryAx`-free at every `n`. The direction that would *guide work* — that handling uninhabited single-entry strips suffices — runs through `TypingStrengthening1.typing`, which carries **`forallE_inv_stratified` and `rigidShapeUniqNS`**, so `TypingStrengthening1Uninhab.iff_typing` and §4's vacuity dual are hole-tainted too. The collapse to one entry is itself gated on the injectivity holes this gate was supposed to help pay for. No cycle through `weakN_iff` (absent from every cone in the file), but the reduction is not free | `#print axioms` on all six: `of_instN`/`PiDescend.of_instN`/`typingStrengthening1`/`split` clean, `TypingStrengthening1.typing` and `typingStrengthening_of_allInhabited` carry `sorryAx` (measured by me at `d67375b`) | n/a |
| 64b | `hasType_app_bvar0_of_inhab` — the same manoeuvre at the **tenth** typing gate | **it works, and has no caller.** Given an inhabitant of the binder it needs neither `TypingStrengthening` nor `IsDefEqU.weakN_iff` nor `rigidShapeUniqNS`: cone **3449** with a hole set (`forallE_inv_stratified` alone) that is a strict subset of *both* existing versions' (3465 and 3609). But neither of its two call sites can supply the inhabitant — `ChurchRosser.lean:1453`'s `etaL` case takes its binder from the η-premise, `:1474`'s `proofIrrel`/`app` case from an unpopulated context head. **Read by inspection of those two branches, not machine-checked**, and recorded as such: a lemma looking for a caller, not a reduction of site 7 | `hasType_app_bvar0_of_inhab` (same file, §5) | n/a |
| 64c | "`SortConvStrengthening` is exactly `PiDescend`" — the confluence stream's own claim, in `NormalEqStrengthen.lean:154` | **only `⟸` is proved, there or anywhere.** The converse needs `SortConvStrengthening` at a pair whose right side is `.forallE A B`, which is not in the image of the lift because its codomain lives in the *extended* upstairs context. Consequence: restating `PiDescend` as type-level Π-shape descent is a **strengthening, not a reduction** — do not aim a round at it. Retracted by the stream that wrote it, and the docstring now says "no stronger than" with the obstruction spelled out | corrected in situ, 2026-09-01 | n/a |
| 64d | my figures for the `weakN_iff` gate split, as briefed this round (293 users / 250 residual) | **wrong twice over, in opposite directions.** At `d67375b` the nine-gate split is **296 / 253 / 43**; adding `hasType_app_bvar0` — which *is* a tenth gate, `CRPiDescend.lean:152` having the verbatim statement with `TypingStrengthening` as its only added hypothesis — gives **296 / 250 / 46**. My 293 came from `CRPiDescend.lean:83`'s table, which excludes that file's own declarations (+3), and my 250 was the ten-gate residual quoted against the nine-gate total. Separately I attributed `ParRedKGraded.lean:429`'s "18 of the hole's users" to `NormalEq.descend`; read in context it is about `weakN_iff`, so the correct replacement there is 43/46. For the record, `NormalEq.descend`'s own figure is **193 users, of which the ten typing gates free 0** — it does not route through the `weakN` wrappers at all | `scripts/weakn-gate-split.lean` (tenth gate added), `scripts/sorry-census.lean`, both re-run at `d67375b` | n/a |
| 65 | (B)'s **minor** entry block of `TeleDefEq [] As As'` — "entirely untouched" | **closed, and off `np = 0` on the chain.** `minorType` and `minorTypeR` differ in exactly **two** positions (the field telescope and the *last* argument of the conclusion), so the conclusion needs **one `appDF`**, not a spine congruence — `mkApp_concat` splits at the only argument that moves. `substC_minorType_defeq` joins entry and conclusion with `hbv` discharged internally and **no `hp : D.params = []`, no `hcl0`**, confirming the typed route carries no `np`-obstruction at the minor block either. `hfld` is inhabited (`teleDefEq_fld_of_np_zero`) | `substC_minorBody_defeq`, `substC_minorType_defeq'`, `substC_minorType_defeq`, `hasArgs_params_bvars_minorCtx'` (`Theory/Inductive/NestedTele.lean` §T6); 17 new theorems, all `[propext, Quot.sound]` or better, census unchanged at 13 | n/a |
| 65a | "general `Γ` was a gratuitous `[]` in §8.9" — my framing of last round's repair | **understated: general `Γ` is *necessary*, not merely available.** The `Γ = []` instance of the minor block's `hbv` is **refuted** above `np = 0` (`substC_minorType_hbv_false_of_nil`, via the new `HasArgs.bvars_ctx_false`), while at the real `Γ` it is derivable for every `np` (`hasArgs_params_bvars_minorCtx'`). So the motive block's vacuity above `np = 0` (§T5) was not an artefact of how §8.9 happened to be stated — the same collapse occurs at the minor block, and the general-`Γ` statement is the only non-vacuous one | same file | n/a |
| 66 | "(C) needs `htype` as data, and typed defeqs throughout" — mine, briefed twice | **exact for the strict route only, and the typed route needs strictly less than I said.** `iotaRulesRS_wf_of_substC'` (`ConstSubstNested.lean:381`) does **not** bind `htype` and cannot need it: its own `type` component is an `IsDefEq … (.sort v)`, whose `.hasType.1` *is* the `IsType [] (df.type.substC σ)` in question. Stronger, and machine-checked: the `type` component **discharges the telescope typing the `lhs`/`rhs` components need** — `mkLams_congr` wants `OnCtx (As.reverse ++ Γ)` and `IsType.mkPi_inv` peels exactly that off `type`'s left endpoint on `Ordered` alone. Order matters and there is no circularity: `type` first, then the other two for free. **So (C) needs one telescope-typing datum, not three** — *amended by row 70: the peel is two-stage, because `iotaCtx` splices `minorsR`, so (C)'s entry defeqs sit one level **inside** its telescope and need `OnCtx.mkPi_entry_inv` as well as `mkPi_inv`* | `iotaRule_tele_onCtx_of_type_defeq`, `IsType.mkPi_inv_of_defeq`, `mkPi_substC_onCtx_of_defeq`, plus `substC_iotaType_defeq` (which is `substC_minorBody_defeq` at `nr := 0`, the proof term being that lemma applied) | n/a |
| 66a | "for (B) the `OnCtx` half is already discharged inside `IsType.mkPi_congr'`" — mine, and I briefed it as the reason not to aim at telescope typing | **true at the outer bridge, false at the entry defeqs** — one level down, the shape of rows 11/11a. `TeleDefEq.cons` wants a defeq *at a sort*, so entries must route through `mkPi_congrU`, which takes `hOn` **explicitly**; both `substC_motiveType_defeq'` and `substC_minorType_defeq'` do. Repaired at no cost by `OnCtx.take_of_reverse`: one `OnCtx` of the whole reversed telescope restricts to every prefix, hence to every entry's `hOn` | same file | n/a |
| 67 | the residual list I briefed for (B) above `np = 0` (`hOn`/`hOnp`/`hbody`/`hAs`) | ~~**incomplete — it omits `hmatch`**~~ — **`hmatch` is RETRACTED as an obligation by row 70d, the same day it was filed.** *Was:* incomplete, omitting `hmatch`, which is the one thing the minor entry adds over the motive entry.** `hmatch` is the type match between the restored constructor's result type `instAll B' (bvars nr nf)` (from §8.9's `hcbody`/`hpi`) and the substituted motive's domain `instAll (((tyApp' t …).substC σ).liftN (k+1) ni) ιs 0`. That is `Faithful.ctor_agree` content — "the restored constructor really constructs the substituted type" — and `instAt_indep_of_tyArgs` bounds `hcbody`/`hAs` from below while saying **nothing** about it. Offsetting it, `hfun` turned out **not** to be data: `motiveApp_hasType'` (`Lemmas.lean:1493`) builds it and throws it away, so it is `hmot` + `hidx`, restated `VInductDecl'`-free as `motiveApp_partial_hasType` and instantiable at the substituted block | `substC_motiveApp_partial`, `motiveApp_partial_hasType` (same file, §T8) | n/a |
| 68 | `OccResidue`'s four clauses — the last gap between `Result.mkRestore` and `Built` | **two of four close in general, and the reduction is exact.** `OccData` is six name-and-head fields mentioning no judgement at all; given it, `head` (a `getAppFn`-of-`mkAppRange` fact about the shape `Add.lean:840,844` actually pushes) and `ctorName_inv` (a `replacePrefix` round trip) are theorems, and `OccData.occResidue` reduces `OccResidue` to `SemResidue` = `member` + `occurs` and nothing else. `mkRestore_built`/`_faithful`/`_canonical`/`_AddNested`/`_AddNestedStep` all re-derived from `RestoreData ∧ OccData ∧ SemResidue`. General kit proved on the way: `Name.replacePrefix_replacePrefix` with **no side condition on `q`** (needs a new component count `nameDepth` to rule out `q = .str (n.replacePrefix p q) s`) | `OccData.head`, `.ctorName_inv`, `.occResidue`, `Result.getAppFn_stored` (`Verify/Inductive/NestedOccData.lean`); **all cones 0 holes**, `[propext, Quot.sound]` or `+Classical.choice` | n/a |
| 68a | "`member` is the only `TrExprS`-level clause of `OccResidue`" — mine, briefed twice, **and written into `NestedRestoreWit.lean:866`** | **false, and the file contradicted itself four lines from its own top** (§1 says "No `TrExprS` appears"). `Built.member` is an equation between two `VIndType`s; the transitive constant cone of its *type* is **29** declarations and contains no `TrExpr`, no `TrExprS`, no `Lean.Expr` — likewise `VNestedOcc.member` 5, `SemResidue.member` 30, `OccResidue.member` 31, `Faithful` 7. At the `NFn` block it closes by `rfl`. This is the second time I have attached "`TrExprS`-level" to this clause after being corrected once for `Faithful`; the docstring is now fixed and cross-references the measurement | measured by the restore stream, 2026-09-01; correction recorded in `NestedOccData.lean` §5 | n/a |
| 68b | "the calculus transfers; its theorems do not" — my own caution about `AddInductiveStep.lean`'s `EWF` | **one step too generous.** `EWF` (`:139`) is a closed `def` with `nestedAux = #[]` written into **both** halves, so all nine combinators are statements about that predicate and none is reusable as written — `EWF.modify'`'s side condition `∀ s, (f s).nestedAux = s.nestedAux` is *exactly* what `Add.lean:845`'s `nestedAux.push` violates, and `EWF.get'`'s postcondition re-injects the degenerate hypothesis. What actually transfers is only the invariant-free layer (`get_eq`/`modify_eq`/`mkFreshId_eq`/`bind_eq`/`pure_eq`/`throw_eq`/`run'_eq`, `bind_ok`, `run'_ok`, `:107-136`). Repaired by `MWF env P x Q` — a Hoare triple with the state invariant a **parameter** on both sides — and `EWF_iff` exhibits `EWF` as its instance at `P s := s.nestedAux = #[]`, so nothing existing is lost | `MWF`, `EWF_iff`, and the eleven combinators (`Verify/Inductive/NestedRunInvariant.lean`) | n/a |
| 68c | "`NestedRestore.lean` §3 already has the `Lean.Name` kit" — mine | **present but insufficient.** §3's `IsNestedName.replacePrefix` is a barrier-*preservation* lemma; `ctorName_inv` needs the round-trip *inversion*, which is new and needs a component count (`nameDepth`) that §3 has no analogue of | same file | n/a |
| 68d | the obvious shape for `OccData`'s constructor-renaming field | **a trap: the function-equality form is FALSE at the witness already in the tree.** `pfnOcc.ctorName n = if n = ``PFn.mk then `_nested.PFn_1.mk else n` disagrees with `replacePrefix` off `PFn.mk` — e.g. at `` `PFn.foo ``. The field must be restricted to `∀ C ∈ (occ j).src.ctors`, which is also all `ctorName_inv` needs. A field stated the natural way would have been refutable on day one | `pfnOcc` (existing witness) vs `OccData.ctorName` as restricted | n/a |
| 68e | name-discipline facts neither kernel checks — previously two (`RestoreData.ownName`/`ownCtor`) | **three.** `OccData.srcCtorPrefix` — *`J`'s constructor names carry `J`'s own name as a prefix* — is load-bearing for `ctorName_inv`: without it `Add.lean:855`'s `replacePrefix` is the identity and the auxiliary constructor keeps the source block's name. Unlike the other two it is about the **previously declared** block, not the one being added. **Flagged, not acted on**, per row 58: adding such a check could reject what C++ accepts, and there is no witness that it fails | surfaced by the restore stream, 2026-09-01 | n/a |
| 68f | `RestoreData` at `run`'s *monadic* output | **the vehicle exists, the invariant does not, and the next step is not a typing lemma.** `RestoreData`'s four prefix-side fields (`name`, `ctor`, `ownName`, `ownCtor`) reduce to one named `def`, `ReplaceAppendsOnly`, which is **satisfiable** rather than an unsatisfiable precondition (`replaceAppendsOnly_of_no_inductInfo`) — so this is not a row-2. It is unproved because `replaceIfNested`'s body is `for J_name in I_val.all do … modify …`, a `forIn` in `M`, and **neither calculus has a `forIn` combinator**. The next concrete step is that combinator | `ReplaceAppendsOnly`, `replaceAppendsOnly_of_no_inductInfo`, `nameSkel`/`SkelExt`/`SkelExt.push` (same file) | n/a |
| 69 | `ConvPiFromEntry` — the typing-free Π half of `ConvStep2`, which I briefed as "the tightest statement in the tree" and "the form a CR development can be aimed at" | **FALSE at the strength every reduction in this corner carries.** Every theorem in `InjMidLocal.lean`, `InjChainLower.lean` and `InjPiInhab.lean` assumes `Ordered env` and nothing more. `roguePiEnv` — one constant `C : Sort 1` and **two** δ-rules for it, `C ≡ ∀(_:Prop),Prop` and `C ≡ ∀(_:Prop),∀(_:Prop),Prop`, both at `df.type = Sort 1` — is `Ordered` (machine-checked), because `Ordered.defeq` asks only `df.WF env` and both rules satisfy it. At that environment `ConvPiFromEntry` forces a sort/Π conversion. **So any proof must consume `VEnv.WF`, not `Ordered`** — and §7 names the clause that saves it: `RuleShape.delta` pins a δ-rule's lhs to `.const ci.name _` and `addConst` refuses a duplicate name, so a WF environment cannot carry two δ-rules for one constant, while `Ordered` can. This retires the localisation program as stated, not merely one route | `ordered_roguePiEnv`, `convPiFromEntry_forces`, `not_convPiFromEntry_of_convSortPiDisj`, `rogue_rules_share_lhs` (`Theory/Typing/InjPiRogue.lean`), all `[propext, Quot.sound]` — re-verified by me, not taken on report. **The one gap, stated:** `ConvSortPiDisj roguePiEnv 0` is not itself proved; it is conjunct 3 of `rigidShapeUniqNS_iff_family`, whose semantic residual `InjSortPiModel.interp_sort_ne_interp_forallE` holds outright, and nothing doubts sort/Π disjointness at a two-rule env with no sort on either side of either rule. The "at most one δ-rule per constant" half is flagged `[analysis]` — about `VEnv.WF'`'s history, not checked | n/a |
| 69a | "two chains with a **common source** is a weakening of `ConvPiInvCod`" — mine, and the reason I called `ConvPiFromEntry` the tightest form | **presentation, not strength.** `ConvPiInvCod.convPiFromEntry` is three lines and takes **no hypothesis at all**, because `ConvC.symm` and `ConvC.trans` are unconditional — two chains out of a common source compose into one chain between the two Π's. So the common-source form is not tighter in that direction, and "no subject, no typing judgment" bought nothing measurable. Row 51's lesson repeated one level up: **a localisation that constrains presentation while leaving the hard quantifier alone is not a reduction** | `ConvPiInvCod.convPiFromEntry` (`[propext]`) | n/a |
| 69b | the CR route "aimed at `ConvPiFromEntry`" | **cannot be aimed there.** `ConvC`'s links are full `IsDefEqStrong`, which already *has* `trans`, so the chain layer decomposes no transitivity — it only frees the sort index. A Π/Π single link inverts freely at every constructor by shape, `proofIrrel` included (`.sort (imax u v) : .sort .zero` would need `succ (imax u v) ≈ 0`). What is left is exactly `trans` (already mined to two closed terms by `InjMidpoint`) and `extra` (this file). Strengthening the induction to track Π-shapes closes `trans` only by producing two fresh chains from a common midpoint — **the statement itself, not a sub-derivation.** `ConvPiFromEntry ⟸ PiInvRaw` is already in the tree, so a CR development belongs at the reference's judgment over `VEnv.WF` | `ConvC.eq_or_raw` + `convPiInv_of_piInvRaw` (existing); analysis in `InjPiRogue.lean` §6, flagged as such | n/a |
| 69c | my census figures, briefed this round | **all three low, and all three by the graph bug.** At HEAD: `IsDefEqU.forallE_inv_stratified` **650** transitive users (I briefed 637), `WF.rigidShapeUniqNS` **409** (I briefed 397), and **13** declarations directly contain `sorryAx`, not 14. Two independent streams reported the same three corrections, which is the check working | `scripts/sorry-census.lean` at `61166b7` | n/a |
| 70 | `hOn`/`hOnp` as obligations of (B)'s entry defeqs | **`hOn` is not an obligation at all, and the residual drops from five items to two.** `recConstsR_wf_of_substC'` keeps `hsrc`/`hσ`, and §T3's `VConstant.WF.substC_mkPi_inv` peels the outer telescope off them on `Ordered` alone. What was genuinely missing is a **second peel**, and `OnCtx.take_of_reverse` does *not* reach it: the motive and minor entries are `mkPi`s sitting **inside one entry** of the recursor telescope, not segments of it. `OnCtx.mkPi_entry_inv` does that peel and `recTypeEntry_substC_onCtx` composes the two, giving every entry defeq's `hOn` from `hsrc` + `hσ`. **Applies to (C) as well** — `iotaCtx` splices `minorsR`, so row 66's one-datum claim needs the same amendment | `OnCtx.mkPi_entry_inv`, `recTypeEntry_substC_onCtx` (`Theory/Inductive/NestedTele.lean` §T9), `[propext, Quot.sound]`; re-verified by me | n/a |
| 70a | `hOnp` | **reduces to `hOn` plus ONE global datum, not one per entry.** `hOnp` re-adds the params on *top* of the entry context (the β-step), so it is not a prefix and `take_of_reverse` cannot see it; `onCtx_params_append` handles it. **And that lemma is literally `OnCtx.appendR` applied** (`StructureClosed.lean:713`) — flagged as such in its own docstring by the stream that wrote it, and recorded here so nobody counts it as new content. Cf. `substC_iotaType_defeq`, which is `substC_minorBody_defeq` applied: this corner has now produced two results whose whole content is an existing lemma at a new instance, and both said so | same file | n/a |
| 70b | `hpar : OnCtx ((D.atRecTele D.params).reverse) (e.IsType D.recUvars)` | **the one telescope-typing residual left, and NOT claimed free.** `VInductDecl'.WF.onCtxParamsAtRec` (`Lemmas.lean:848`) is exactly it at the *source* environment; transporting to `e` needs `substC` to be the identity on `D.params`. That ought to hold — `csubst`'s domain is inside the block's own names (§7.2 `csubst_dom`) and `D.params` are typed before the block's types are added, hence block-free — but **`VInductDecl'.WF` carries the *typing*, not a `NoBlock D.params` clause**, and `VIndRestore.noBlock_noCSubst` (`RestoreBridge.lean:160`) is stated for `csubstTy`, not `csubst`. So it is a side condition about parameters, **not** a β-gap, and the honest status is open | stated open by the telescope stream, 2026-09-01 | n/a |
| 70c | `hmot`/`hidx` restated at the substituted environment | **neither needs new mathematics or an `np` bound.** `hmot`: `lookup_motive`'s content is `List.map_range_reverse_split`, already `D`-free — only the *statement* mentions `D`, so `Lookup.range_map` plus its instance `lookup_motive_substC` gives it as pure de Bruijn arithmetic with no environment and no block. `hidx`: `HasArgs.substC_liftTele` is §T1's `HasArgs.substC` composed with `map_substC_liftTele`, so `hidx` at `e` is `VIndCtor.WF.args_ty` transported — the same datum the call site already uses. This is the §T8 template (restate the intermediate with no `VInductDecl'` in it) applied twice more | same file | n/a |
| 70d | `hmatch` — the residual I added to the ledger one commit earlier | **RETRACTED as an obligation: refuted in its strict form, free in its typed form.** The match need not be an equation — `IsDefEq.defeqDF` converts along a type defeq, so `substC_minorBody_defeq_of_conv` takes `hmaj` at the restored constructor's result type `A₀` plus `hconv : A₀ ≡ A`, and `hconv` **is** §8.9's `substC_tyApp'_defeq_tyAppR'_comp`, which carries no `np` bound. The strict reading is `substC_tyApp'_eq_tyAppR'`, whose `hcl0` the parameterised witness refutes while the typed route's `ClosedN D.np` it satisfies — the *same* strict-vs-typed split as everywhere else in this corner. **What survives is smaller and is honestly open:** a σ-free syntactic identification of the chosen `B'` with `D.tyAppR' R t M ιs`, `Faithful.ctor_agree`/`Canonical` bookkeeping, with **no positive `np > 0` instance constructed**, and not derivable from `instAt_indep_of_tyArgs` | `substC_minorBody_defeq_of_conv` (`[propext]`); strict side `ntree_not_tyArgs_closed0` (`NestedRules.lean:1105`) vs `ntree_tyArgs_closedN_np` (`:1116`) | n/a |
| 70d′ | **the stream's own first-draft citation for row 70d** | it named `ntreeNode_substC_ne_typeR` (`ConstSubstNested.lean:774`) as the refutation of `hmatch`'s strict equation. **It is not** — that theorem is about `C.type`/`C.typeR`, i.e. obligation **(A)**'s strict equation. Same phenomenon, one obligation over. Caught and fixed in the file before reporting, and recorded because it is the third fabricated-or-misaimed citation this week and the *first* one a stream caught in its own work rather than in mine | self-corrected, 2026-09-01 | n/a |
| 70e | "general `Γ` versus `[]`" in the nested telescope corner — **now a pattern, not an incident** | **three statements in a row were empty at `Γ = []` above the trivial case:** `substC_motiveType_defeq` (§T5), the minor block's `hbv` (row 65a), and now **every §T6 statement** — `minorBody_hfun_false_of_nil` shows a `bvar` head has no type in the empty context, so `substC_minorBody_defeq`'s `hfun` is unsatisfiable there. In each case the general-`Γ` form was **forced**, not merely convenient, and each was found only because the `[]` instance was checked deliberately. **Standing instrument for this corner: before reporting any statement here, instantiate it at the degenerate context and confirm the hypotheses are satisfiable.** It costs one `lean_multi_attempt` and it has now paid three times | `minorBody_hfun_false_of_nil`, `substC_minorType_hbv_false_of_nil`, §T5's motive-entry contradiction (same file) | n/a |
| 59 | "`ChurchRosser.lean:1438` is irreducible" — mine, and `ParRedKGraded.lean:425` flagged itself inspection-only | **refuted, machine-checked.** The composition is not forced: carry the argument mismatch in the *statement* instead. `parRed_beta_gen` does the same proof with `NormalEq.instN₂` (itself `weakN_iff`-free) in the `lamDF`/`etaL`/`etaR` cases, and `NormalEq.trans`, `NormalEq.weakN_iff` and `NormalEq.weakN_inv_DFC` all **leave the cone** (3875 → 3847). A real strengthening, not a restatement: `parRed_beta_of_gen` recovers the original for free, while `parRed_beta_gen_of_beta` recovers the generalisation **only through the very `trans` it removes** | `parRed_beta_gen`, `parRed_beta_of_gen`, `parRed_beta_gen_of_beta`, `appDF_beta_of_parRedKn'` (`Theory/Typing/CRBetaGen.lean`) | n/a |
| 60 | my count of `parRed_beta`'s `weakN_iff` appeals | **four, not five — I missed the one that survives.** `hasType_app_bvar0` (`ChurchRosser.lean:1336`, verified; called at `:1453` and `:1474`) appeals at `:1347` to strengthen a conversion with **two distinct endpoints** — the conversion half, not a typing gate, which is exactly why its neighbour `IsDefEq.skips` is excluded from the gate set. After a gate-cut of the nine `StrengthenNarrow` §5 wrappers *plus* `hasType_app_bvar0`, the rewired row **does not reach** the hole; without that one it still does. So the row's appeal is exactly `TypingStrengthening + hasType_app_bvar0`, and the residual is **Π-shape descent** for a `C` not syntactically a Π — which `forallE_inv_stratified` cannot supply (both sides must already be Π), and which `weakN_inv_one_of_inhabited` cannot reach (the binder is the Π-domain, and `Γ ⊢ lam A body : forallE A B` gives no inhabitant of `A`) | measured by the beta stream, 2026-09-01 | n/a |
| 61 | "reduce the residual to inhabited binders" as a way out | **the two ends meet only in an inconsistent environment.** An uninhabited proposition over an `Ordered` env is *equivalent* to `Consistent` (`consistent_iff_exists_uninhabited_prop` — note it takes `env.Ordered`, **not** `VEnv.WF`, correcting how I stated it), while the closing hypothesis `AllTypesInhabited` **implies** inconsistency. So the manoeuvre costs a consistency assumption on the wrong side | `consistent_iff_exists_uninhabited_prop`, `AllTypesInhabited.not_consistent` (`Verify/Typing/ProjInhab.lean`) | n/a |
| 56 | `VIndRestore` from checker data — the item I called "the critical path" | **it exists now.** `Result.mkRestore` computes `K` and the three *name* fields from `ElimNestedInductive.Result`, and `mkRestore_discipline` proves `OwnId ∧ NameBarrier ∧ SubstFree ∧ KeysFree` of it simultaneously, from a 14-field `RestoreData` bundle. **So the ordering rule I set — discharge implementation-side before adding the premise — is now satisfiable**, where the previous round found its precondition unmet. Still owed for a full `VEnv.AddNested`: `Faithful` (a `TrExprS`-level agreement plus `Declared`) and `Canonical` (about `D` alone) — neither is a name fact, neither is reachable from `RestoreData` | `Result.mkRestore`, `mkRestore_discipline`, `mkRestore_ownId`, `mkRestore_recName_aux` (`Verify/Inductive/NestedRestore.lean`); all `[propext, Quot.sound]` | n/a |
| 57 | `VIndRestore.NameBarrier` — the new abstract predicate | **bounded field by field, both ways.** `NameBarrier.substFree` derives `SubstFree` with **no `env`, no `Faithful`, no `DomNodup`** — via `csubst_dom` alone. Positive: all seven fields hold at `nfnRestore`, and `nfnRestore_substFree'` re-derives the hand proof through the barrier. Negative: one-field overrides refute each of `resTy`/`resRec`/`resCtor`/`resArgs` *and* its matching `SubstFree` clause, plus a `K`-move refuting the `aux*` group with the `res*` clauses still holding. And unlike `Faithful` it is **not** `K`-vacuous (`not_nestedBarrier_nil` against `substFree_nil`) | same file | n/a |
| 58 | "the declaration's own name does not carry the `_nested` prefix" — a hypothesis of `RestoreData` | **not an environment invariant, and neither kernel checks it.** I verified both halves: `checkNoNestedAux` (`Lean4Lean/Inductive/Add.lean:922-923`) scans constructor **types** for `_nested`-headed `.const`/`.proj`, and C++ `check_no_nested_aux` (`inductive.cpp:1227`) is the identical expression scan; there is no name-level test against `*g_nested` anywhere in `src/kernel`, and `Lean.isReservedName` has no `_nested` registration. So `inductive _nested.Foo` is accepted by **both** kernels. **This is not a claimed bug**: no witness is constructed, and two mitigations may close every path — `mk_unique_name` (`inductive.cpp:1105`) skips env-present names, so a user `_nested.X_1` cannot be reused as an auxiliary name, and `mkAuxRecNameMap`'s renamed recursors end `rec_k`, never `rec`. **Decision (mine): do not add the check.** It would reject what C++ accepts, i.e. a behavioural divergence, against CLAUDE.md's guideline to stay close to the C++ kernel — and the honest treatment is what the spec already does, carry it as a hypothesis. If anyone constructs a witness, this becomes a `bugs-found.md` entry rather than a ledger row | verified independently, 2026-09-01 | n/a |
| 54 | "`hargs` is the same statement as §8.8's `hbody`" — mine, from the previous commit | **overstated.** `hargs` is a `HasArgs` (spine typed against the head's split pi telescope); `hbody` is a `HasType` of the *assembled* `R.tyBody D j`. Forward works (`hargs` + `hsplit` + the constant's typing ⟹ `hbody`, by `HasType.mkApp'`), but the **converse needs spine inversion** — `HasArgs.of_mkApp` and `.of_mkApp'` both take `henv : env.WF`, which is circular here. So §8.8's residual is strictly **weaker**. Same obligation in the "one route discharges both" sense; *not* the same statement, and I wrote it as the latter | measured by the bridges stream, 2026-09-01 | n/a |
| 55 | "`hp : D.params = []` enters (B)/(C) at exactly (A)'s two head equations" — mine | **incomplete, and the omission matters.** There is a **third** site (`σ.Closed`, instantiated as `csubst_closed' hp hcl0`), though that one is not an obstruction — the unprimed `csubst_closed` asks only for `ClosedTele D.params 0` and `ClosedN D.np`, both of which `csubst_WF` already carries. But I also missed **a second `np`-flavoured hypothesis entirely**: §7.4's head *equations* need `hcl0 : ∀ i, ∀ a ∈ R.tyArgs i, a.ClosedN 0`, which is **refuted** at the parameterised witness (`ntree_not_tyArgs_closed0`, `NestedRules.lean:1105`) — a *separate* obstruction, not derived from `hp`. Net: **the strict-equality route has two `np`-obstructions and the typed route has none** (`ntree_tyArgs_closedN_np` shows the weaker `ClosedN D.np` form holds at the same witness) | same stream; both witnesses verified | n/a |
| 51 | the `SortChainAt` localisation of `ConvStep2`'s `.forallE` head | **it buys nothing — not even locality.** `SortChainAt` at the *single* term `.bvar 0`, with no quantification over subjects, is **equivalent** to the global `ConvSortInv` it was meant to localise (verified `[propext, Quot.sound]`). Mechanism: the localisation constrains the *subject* while leaving the *context* universally quantified, and the arbitrary sort enters through the context — in `.sort u :: Γ`, `Lookup.zero` types `.bvar 0` at `(.sort u).lift`, which **is** `.sort u` on the nose since sorts are closed. So `MidCost` at the one closed term `(X : Prop) → X` already yields the whole sort half, and with the Π half yields `ConvStep2`. My "buys locality, not strength" was too kind: the right statement is **no route can exist that exploits the subject's head, because the subject's head is not where the difficulty is** | `sortChainAt_bvar_iff_convSortInv`, `convSortInv_of_midCost_one`, `convStep2_of_midCost_one` (`Theory/Typing/InjChainLower.lean`) | n/a |
| 51a | reading `InjMidLocal`'s "`.bvar` is a free head" as "variables are cheap" | **a trap.** `BaseUniqCAt env U (.bvar i)` *is* free (`baseUniqCAt_bvar`, via `Lookup.uniq`) while `SortChainAt env U (.bvar 0)` is the **entire hole**. Same term, different predicate — `false`-level versus `true`-level — and all the content lives in the `HasTypeStrong.defeq` wrapper. The original row is about the former and stays correct | same file | n/a |
| 52 | `InjMidLocal` §7's negative controls as covering its own residuals | **they do not, and cannot.** They fire because `IsDefEq.extra` has three premises and no typings; `IsDefEqStrong.extra` has **nine**, five of them typings, so at `rogueSortEnv` it demands a `Sort 1 ≡ Sort 2` the environment lacks. Worse, a two-link chain `.sort u ⇝ M ⇝ .sort v` needs `M` typed at both `≈ .succ u` and `≈ .succ v` — producing one *requires* a `SortUniq` violation. So no rogue-environment refutation of `SortChainAt`/`ConvSortInv` exists by that idiom. **SUPERSEDED for the two Π-side entries by row 69, and this is the cost of an `[analysis]` flag: the claim was never machine-checked and it was false.** The premise count is sound only where the level bookkeeping `.sort l : .sort (.succ l)` forces the mismatch — i.e. for *sort* chains. On the Π side the nine premises are satisfiable with no anomaly at all, and `roguePiEnv` refutes `PiChainAt`, `ConvPiInvCod` **and** `ConvPiFromEntry` over `Ordered` | Flagged `[analysis]` in the file, not machine-checked — which is exactly why it survived | measured by the chain stream, 2026-09-01 | n/a |
| 53 | `ConvPiInv`'s **domain** conjunct | **dead code** — every consumer in the tree takes `.2`. `ConvPiInvCod` drops it and re-derives the whole `BaseUniqChain` + `InjMidLocal` development. Consequence for the accounting: `not_forallPropDomInj`'s refutation of `PiInv`'s domain conjunct in the set model (row 9) is now **irrelevant to `ConvStep2`**. It rescues nothing — the codomain conjunct still needs faithfulness — but it removes one obstruction from the ledger | `ConvPiInvCod`, `baseUniqCAt_of_cod`, `convStep2_of_cod`, `sortUniq_of_cod` (same file) | n/a |
| 50 | `CtxInvariant`'s relation existential in `ModelFits` | **eliminated, then discharged.** `CtxAgree` (equal length + indistinguishable under every common prefix) is the **greatest** `CtxInvariant` relation, so `modelFits_iff_ctxAgreeRd` removes the existential; and for the natural split it is *discharged* — `IsDefEq.defeqDFC'` already generalises an arbitrary prefix and `propSplitOf`'s predicates carry their own typing derivations, so unlike `ctxInvariant_prop_agrees` no `hB` is needed. `modelFits_of_propSplit_inputs` reduces the model-side input to `PropTypeAgree env 0` (which gives `PropUniq` via `PropUniqFromFalse`), `PropDescend env 0`, and `OracleFits` | `ctxInvariant_ctxAgree`, `ctxAgree_of_ctxInvariant`, `propSplitOf_ctxAgree`, `modelFits_of_propSplit_inputs` (`Theory/SetModel/AboveAudit.lean`); bounded by `ctxAgree_refl` and `not_ctxAgree_sortShift` via the new `prop_forces_false_bvar` | n/a |
| 11c′ | ~~`hκ` as "the real open content" of the model side~~ — **superseded by 11c″** | *Was:* **closed, but it *reduces* Input A rather than discharging it.** `exists_inaccessibleChain_omega` (`Theory/SetModel/InaccChainOmega.lean`) gives one `κ` with `∀ m, IsInaccessibleChain m κ` from `𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰` alone — audited: `IsInaccessibleChain` has exactly two fields and both are proved, and the pigeonhole against the schema is sound. But `inaccModelInput_of_modelExists` replaces `InaccModelInput` with `ModelExistsInput` — pure model existence from consistency, provable from Foundation, **not applied anywhere**. So the mathematical half is closed and the library-glue half is not | `exists_inaccessibleChain_omega`, bounded by `not_isInaccessibleChain_const` / `inaccSeq_zero_le` | n/a |
| 11c | `AxiomsValidated` as an open obligation | **not one** — it is a *consequence* of `CoherentOn` plus the declaration history, via the previously-missing `VEnv.WF'.constants_axiom`. The real open content is `hκ : ∀ m, IsInaccessibleChain m M.κ`: `AxiomsValidated.axioms` is the **only** obligation in `InterpSound.lean` stated *without* `Above M`, hence strictly stronger than `CoherentOn.const_type` | `axiomsValidated_of_coherentOn`, `axiomsValidatedAbove_of_coherentOn`; bounded both ways by `not_axiomsValidated_falseProp` (needing **no** `hκ`, precisely because the field is un-truncated) and `axiomsValidated_extAx` (satisfiable at a one-axiom list, not merely at `ds = []`) | n/a |
| 12 | `SortInv` from the model | **bounded** — exact, an `iff` | `sortEqRaw_iff` (`SemanticRouteClosed.lean:217`) | n/a |
| 13 | `inferProj` / `tryEtaStructCore` / `isDefEqUnitLike` never fire | **true today, and their falsity is the goal** | `inferProj_always_throws`, `tryEtaStructCore_never_true`, `isDefEqUnitLike_never_true` | the flip **kills** these three (correctly) |
| 14 | `LevelAssign` as originally stated (`LevelAssignUnguarded`) | **`IsEmpty`** — the strongest form there is | `no_levelAssign` (`Theory/SetModel/LevelAssignUnsat.lean:106`) | **no** — independent; repaired by guarding `lvl_sound` |
| 15 | `LevelAssign.Stable`'s `lvl_instN` as originally stated | **unsatisfiable** | `no_stable` (`LevelAssignUnsat.lean:172`) | **no** — repaired by the `env.HasType` guard, which its docstring flags as load-bearing |
| 16 | `CtxInvariant L R` **in isolation** | **trivially satisfiable, hence untestable alone** — take `R := Eq` | argued at `Theory/SetModel/CoherentWitness.lean:109`; the *pair* with `hRd` is machine-checked consistent by `ctxInvariant_prop_agrees` | n/a |
| 17 | `PropSplit` (the live parameter) | **satisfiable and non-trivial** | `exists_propSplit`, `propSplit_not_constant`, `prop_forces_false`/`prop_forces_true` (`PropSplitAudit.lean`) | n/a |
| 18 | `PropSplit.Stable` (the live parameter) | **satisfiable, and exact** | `exists_stable_propSplit`, `propSplitOf_stable_iff` (`StableAudit.lean`) | n/a |
| 19 | `Bridge.AddDeclWF` (`Verify/Bridge.lean:132`) | **false**, and `Bridge.addDeclWF` (:138) is a *proved theorem* of it — a second instance of §4a, on a shorter path than row 2's | `addDeclWF_false` (`Verify/PreludeVacuity.lean`) | **yes** |
| 20 | `AddInductiveStepWF`'s premise `ves.WF env` | **near-vacuous** — applicable only to the *first* inductive block, because `no_inductInfo` holds even at `.unsafe`, so `ves.WF env` requires an environment with no inductive at all | `VEnvs.WF.find?_ne_inductInfo` (`Verify/Inductive/AddInductiveStep.lean:213`) | **yes** |
| 21 | the nested rebuild inside `Environment.addInductive` | **unreachable** under row 20's premise: `numNested` is forced to `0`, so `mkAuxRecNameMap`, `restoreNested`, `processRec` and three re-check passes are dead code there | `run_run'_aux2nested`, `replaceAllNested_id` (same file) | **yes** |
| 22 | `AgreeInst` (Carneiro's entanglement) | **satisfiable, and the meaningful pair is inhabited** — same shape as row 16: `AgreeInst` alone says little, and what matters is `AgreeInst` together with `ρ₁ ∈ interpCtx Γ₁` | `agreeInst_zero` (`Theory/SetModel/InterpSound.lean:166`) exhibits the witness `snoc ρ ⟦e'⟧ρ`; `beta_sound` (:183) builds the pair from it with `mem_interpCtx_cons`, conditional on `h3e'` — part 3 for the substituted term, i.e. the entanglement stated as an explicit hypothesis rather than assumed | n/a |
| 23 | `InjSortPi.SortPiSupplyAll` — the per-conversion model supply for `sort_forallE_inv` | **restatement** — provably *equivalent* to its own conclusion `RigidSortPiDisj`, because the supply itself is refuted | `sortPiSupplyAll_iff` (`Theory/Typing/InjSortPiModel.lean`), both directions | n/a |
| 24 | the hypothesis of `SemanticRoute.semantic_sortInv_packaged` (the ∀-over-all-contexts form of the part-4 supply) | **vacuous** — false for **every** `env` and `nv`: the model has no valuation for the legitimate context `[∀ p : Prop, p]`, and reflexivity of `.sort .zero` supplies the conversion it cannot see | `sortInvSupply_vacuous`, from `interpCtx_vFalse` + `onCtx_vFalse` (`InjSortPiModel.lean`) | n/a |
| 25 | `InjSortPi.ConstNotUniv` — the part-4 residual for `RigidConstSortDisj`/`RigidConstPiDisj` | **dead route** unguarded: `ModelData.cnst` is a free field, so a constant may denote a universe stage | `not_constNotUniv`, `const_denot_arbitrary` (`InjSortPiModel.lean`) | n/a |
| 26 | `addInductR_ordered'`'s `hctors` — obligation **(A)** of the nested route | **CLOSED for `np = 0`** (`ctorConstsCR_wf_of_np_zero'`, unconditional, no cleanliness hypothesis) by moving the substitution to the *declaration sites* `ctorConstsCR`/`recConstsR` rather than into `typeR`. The row below records what it was, and the witness now proves (A) rather than refuting it (`nfnAuxDirty_obligationA`); it refutes **`hrules`** instead. *Was:* **false** under the premises `VDecl.WF.inductNested` actually has, not merely open. `VIndCtor.typeR` copies `C.params` and every *non-recursive* field's stored type verbatim, while `WF.params_eq` and `WF.pos`'s `none` branch make those only *definitionally* block-free — so a companion constant can sit under a redex there and the step declares a constant whose type names a constant the environment lacks | (deleted) `nfnAuxDirty_refutation`; now `nfnAuxDirty_obligationA` **proves** (A) there, and `nfnNodeDirty_fieldTypesR_dirty` + `nfnAuxDirty_iotaCtxR_eq` refute **(C)** instead | **closed for `np = 0`**; above it, the β-gap remains and the route is `ctorConstsCR_wf_of_substC'` (telescope defeq) |
| 27 | `Faithful` / `Built` / `Canonical` / `OwnId` / `D.WF` as a defence against row 26 | **insufficient, provably** — every clause of each is about the *companion* members, and the constructor that fails is *user-written* | `nfnAuxDirty_AddNestedB` + `nfnAuxDirty_step_not_ordered` (same file) | n/a |
| 28 | obligations **(B)** and **(C)**'s cleanliness condition as stated against `csubstTy` | **mis-stated** — (B)/(C) run on `R.csubst`, whose domain escapes `D.blockNames`, so no `VIndCtor.WF` clause makes a non-restored position σ-invariant | `csubstTy_dom_blockNames` (holds) vs `nfn_csubst_dom_escapes_blockNames` (fails), same file | n/a |
| 30 | `rigidShapeUniqNS_of_family` — the *useful* direction of the five-conjunct decomposition | **not unconditional** (as I had presented it), but the tax is far smaller than this row first said. **Row 30 as written was not tight and is superseded:** the dependence on hole A is exactly `ConvStep2`, not `ProofTransport`-via-hole-A and not `SortInv`. Two facts collapse it — `rigidShapeUniqNS_of_family` uses `htr` in **one** of nine branches and only at a `const`-headed spine, and `BaseUniqChain.baseUniqCAt_of` needs `ConvSortInv` only for its `.forallE` head, which a spine's head recursion never enters. **And `ProofTransport` is not tainted by hole A at all**: `proofTransport_of_convInv` supplies the unrestricted form `sorryAx`-free | `rigidShapeUniqNS_of_family_convStep2`, `baseUniqCAt_constSpine`, `proofTransportSpine_of`, `proofTransport_of_convInv` (`Theory/Typing/InjSpineTransport.lean`); non-vacuity by `proofTransportSpine_fires`; all seven binders load-bearing per `lean_minimal_hypotheses` | n/a |
| 30a | "an independent `sort_not_proof` / `forallE_not_proof` is the only way hole B pays off" — mine | **false.** `ConvStep2 ∧ PiInv` is another route and a cheaper one (strictly weaker than `SortUniq`), and nothing in the ⟸ direction of the decomposition mentions `sort_not_proof`. Separately, my claim that "the model route to `sort_not_proof` is open" was a **re-import of a claim I had already retracted** (`ORCHESTRATOR.md:305-323`): surviving cumulativity means a model cannot *refute* it, not that one can *prove* it — and `sortNotProof_of_propSplit` (`Theory/SetModel/NotProofNoModel.lean`) already gets it from `PropSplit` with no interpretation, dominating any model construction | the corrections are the injectivity stream's, 2026-08-31 | n/a |
| 36 | "`VIndCtor.typeR` should *be* the substitution" — **my own design ruling** | **refuted by two theorems already in the tree.** `ntreeNode_typeR` is `rfl` against `type_of% @NTree.node`, so Lean's stored type for a parameterised nested constructor *is* the contractum, i.e. `typeR`; `ntreeNode_substC_ne_typeR` says `substC` gives the redex; and `TrConstant` has no defeq slack. The redefinition would have made `addDecl.WF` **false** for every parameterised nested declaration — the exact defect I rejected the other option to avoid. My premise that `restoreNested` rewrites "everywhere" was also false: it re-abstracts the leading `nparams` binders **unchanged** (`Add.lean:700-732`), so `typeR`'s verbatim `C.params` is *faithful* | `ntreeNode_typeR` (`NestedHead.lean:588`), `ntreeNode_substC_ne_typeR` (`ConstSubstNested.lean`) | n/a — the repair was to substitute at the *declaration sites* instead |
| 32 | `VEnv.NormalEq.descend` | **refuted only conditionally — my reports upward said "unfillable" and that was wrong.** `not_descendStatement` takes `refEnv.SortUniq 0` and `refEnv.UniqTyping 0` as hypotheses, and `refEnv_sortUniq` carries `sorryAx` (verified: `[propext, sorryAx, Classical.choice, Quot.sound]`); `DescendRefute.lean` records satisfiability as **open**. What *is* unconditional is `descend_uniq_sortUniq_not_all : ¬(DescendStatement refParams ∧ SortUniq ∧ UniqTyping)`. **I wrote the governing rule — "a refutation is only as strong as the reachability of its witness" — into this file and then broke it in every brief that cited this row.** Original text follows. *Was:* **refuted**, not open — its `sorry` is unfillable. `DescendStatement` fails at a `Params` instance that exists (`refParams` over `refEnv`), given `SortUniq` and `UniqTyping` there | `not_descendStatement`, `not_descendStatement_etaArg`, `not_descendStatement_etaFun` (`Theory/Typing/DescendRefute.lean:425`+), all `sorryAx`-free | n/a — it must be **restated**, and the descent layer no longer depends on the strengthening hole regardless |
| 33 | `VEnv.parRed`'s statement | **refuted, but only at an instance that does not exist** — a *weaker grade* than row 32, and this row previously flattened the two. `not_parRedStatement_of_propMajor` needs a `Params` instance registering an `.app` pattern, and **no instance in this tree does** (`ParRedPropRefute.lean`'s own §Satisfiability says so); `refParams_parRedKStatement` even *proves* the `ParRedK` statement at `refParams`. Contrast row 32, where `descend` is refuted over `refEnv`, which exists. **Also corrected: the gate is `WeakNInvDS`, not `EtaRLiftInv`** — `KSite7.lean` replaced the latter 470 lines later in the same file, and `EtaRLiftInv`'s own refutation is likewise only conditional (`etaRLiftInv_of_no_etaK`). The restatement now exists: `parRedKStatement_of_rows (HD : WeakNInvDS) (HA : AppKetaRow)` (`Theory/Typing/KSite7Rows.lean`), two hypotheses, and **`NormalEq.descend` is out of its cone** | `not_parRedStatement_of_propMajor` (`ParRedPropRefute.lean:83`), read against that file's own satisfiability section | n/a |
| 33a | `AppKetaRow` — the restatement's new residual | **bounded both ways, and the factoring is exact**: given `WeakNInvDS`, site 7 and `AppKetaRow` are *equivalent* (`appKetaRow_of_parRedKStatement` shows it is a substitution instance, so no hidden strength). At a `keta .here` step with matching function sides it is provable outright (`appKetaRow_here_of_same_fun`), so the residual is entirely on the *function* side | `appKetaRow_of_no_etaK`, `refParams_appKetaRow` (holds where `EtaK` is empty — vacuous at every `Params` instance in the tree, and stated as such), `appKetaRow_of_parRedKStatement` | n/a |
| 37 | `VEnv.ConstRigidPat` as a route for `TrProj.weak'_inv` | **dead**, and my description of why was slightly wrong: it *does* occur as a conclusion (of `constRigidPat_of_weakNorm`), but that theorem's antecedent `VEnv.WeakNorm` is refuted sorry-free, so it has no *usable* producer. An environment-wide scan of declaration types finds `ConstRigidPat` in exactly one theorem | `PropLoopWeakNorm.not_weakNorm`, `not_weakNorm'`, `not_forall_weakNorm`, `not_forall_weakNorm_of_wf` | n/a |
| 38 | `VEnv.ConstAppTypeStrengthen` — `weak'_inv`'s new residual | **bounded three ways**: not false (holds at every depth-zero lift, conclusion holds at an explicit depth-one instance), not vacuous (hypotheses jointly satisfiable at a depth-one lift in every environment declaring a `Sort 0`-valued constant), and not trivially true (drop "the subject is a lift" and the conclusion fails at that same witness) | `constAppTypeStrengthen_depth_zero`, `_fires`, `_needs_lift` (`Verify/Typing/ProjWeakInv.lean`), all hole-free | n/a |
| 39 | "the three checker `.WF` holes are provably vacuous today" — mine | **two of three.** `inferProj_always_throws` and `tryEtaStructCore_never_true` are hole-free. **`isDefEqUnitLike_never_true` carries `sorryAx`** — cone 11027, holes including `NormalEq.descend`, which is *false* (row 32). So the vacuity of `isDefEqUnitLike.WF` is **asserted, not established**. Separately, `inferProj.WF` is *false* once its branch goes live (`bugs-found.md` item 10: `inferProj` never checks recursiveness while `IsStructure.noRec` demands `C.recFields = []`), so it must not be closed today | measured by the `TrProj` stream, 2026-08-31 | the flip makes all three live |
| 34 | `TransStrengtheningNarrowNeutral` / `…Spine` — the `weakN_iff` residual | **bounded three ways, and the conclusion is not free** — the first `Theory/Typing/` entry meeting §5a's standard | `transStrengtheningNarrowSpine_hyps_satisfiable`, `exists_wf_narrowSpine`, `no_neutral_proofIrrel`, with the collapse test `audit_witness_is_substitution_case` showing bound 1 tests only the *easy* case (`Theory/Typing/StrengthenAudit.lean`) | n/a |
| 35 | any *syntactic* narrowing of the residual's middle term `b` | **cannot help** — `b` is always convertible to a lift, and "may be taken to be a lift" is satisfied by `b₀ := e2`, so rounds 5–8's restrictions constrain representatives, not conversion classes. Only a normalisation result can sharpen it | `mid_defeq_lift`, `midNormalise_trivial` (same file), both hole-free, `[propext]` | n/a |
| 31 | `Experimental/ShapeLogRel.lean` as a usable asset | **not one, and the claim about it was wrong in every particular.** Reported to me as "6 100 lines, 0 sorries, blocked by one standalone axiom that proves `False`". Measured: **8 435 lines**, `sorry` in tactic position at several sites, **no `axiom` declared in it at all**, and it **does not compile** (`lake build Lean4Lean.Experimental.ShapeLogRel` fails on a `PiDefEq` goal). It is also not in `ConeJoin`'s closure, so no instrument sees it | direct measurement, 2026-08-31 | n/a |
| 37 | `VEnv.ConstRigidPat` **as `TrProj.weak'_inv`'s residual** | **dead route — and the conclusion drawn from it was wrong.** The route is dead exactly as reported: an environment-wide scan of every declaration *type* finds `ConstRigidPat` in **one** theorem in the tree (`constRigidPat_of_weakNorm`), and `VEnv.WeakNorm` is refuted at two `Params` instances with `[propext, Classical.choice, Quot.sound]` only. What does **not** follow is "`TrProj.weak'_inv` is blocked on rigidity": (C) is *sufficient* for the shape step, not necessary — it asks for a weak-head reduct of an arbitrary subject convertible with a `c`-spine, while the hole needs only that a **typing survive strengthening with its head intact**, for a subject that is a *lift* | `TrProj.weak'_inv_of_strengthen` (`Verify/Typing/ProjWeakInv.lean`) proves the hole's exact statement from `VEnv.ConstAppTypeStrengthen`; measured cone 3661, holes `weakN_iff, forallE_inv_stratified, rigidShapeUniqNS` — no `ConstRigidPat`, no `WeakNorm`, no `NormalEq.descend` | prove row 38 |
| 38 | `VEnv.ConstAppTypeStrengthen` — the replacement residual | **bounded both ways.** Holds at every depth-zero lift; hypotheses jointly satisfiable at a depth-one lift in every environment declaring a `Sort 0`-valued constant; **not** trivially true — drop "the subject is a lift" and the conclusion is false at that same witness. What is *not* yet measured, and is the next thing to measure: whether the interesting configuration (`as` mentioning a lifted-away variable and not defeq to a lift) is satisfiable at all — if it is not, the residual is a corollary of strengthening rather than a new obligation | `constAppTypeStrengthen_depth_zero`, `constAppTypeStrengthen_fires`, `constAppTypeStrengthen_needs_lift` (same file), all three `[propext, Quot.sound]`, hole-free cones | n/a |
| 39 | "`inferProj.WF`, `isDefEqUnitLike.WF` and `tryEtaStructCore.WF` are vacuous today" — §6's own bullet | **two of three, not three.** `inferProj_always_throws` and `tryEtaStructCore_never_true` are `[propext, Classical.choice, Quot.sound]` with **hole-free** cones (6973, 6794). `isDefEqUnitLike_never_true` is **not**: cone 11027, holes `weakN_iff, forallE_inv_stratified, rigidShapeUniqNS, NormalEq.descend` — and `descend` is false (row 32). So the vacuity of `isDefEqUnitLike.WF` is *asserted, not established*, and the one instrument that would notice (`#print axioms`) had not been run on it | measured 2026-08-31 by the `Verify/Typing` stream | re-prove `isDefEqUnitLike_never_true` without the conversion layer, or record it as conditional |
| 29 | `CoherentOn` as the rescue for `RigidConstPiDisj` / `RigidConstSortDisj` | **dead route, and the blocker was misdiagnosed for months.** `CoherentOn.const_type` constrains `M.cnst c us` by *membership* in `⟦ci.type⟧` and nothing more, and both target shapes live inside a declared type — so a `CoherentOn` model over a `VEnv.WF` environment with **no defeqs at all** still lets `.const c us` and `.sort .zero` share a denotation. The refuted guard is *stronger* than what the conjuncts supply (whole-environment rule-freeness vs `RuleFreeHead c`), so no weakening rescues them | `not_coherentConstNotUniv`, `not_coherentConstNotPi`, `coherent_const_denot_eq_sort`, `oracleOK_univ` (`Theory/SetModel/CoherentConstShape.lean`); non-degeneracy by `above_iff_of_chain` and `not_coherentOn_falseProp` + `coherentOn_axEnv_separates` | n/a |

**Row 11 is the ledger's own worst moment: row 6 recurring inside row 6's repair.** Row 6 was an
occurrence hypothesis stated at the wrong environment; `staged` states one at *all* environments.
And row 11a is why it survived — the two-way bound that was supposed to catch it was itself
vacuous on the broken field. Read rows 11/11a together before trusting any "bounded both ways" in
this file that was not checked field by field.

Rows 1–5 are one bug. Rows 6, 7, 14 and 15 are independent of it, and that is the ledger's main
finding: **the failure mode is not confined to `AddInduct`.** It recurred in the abstract theory
(row 6, a hypothesis stated at the wrong environment) and three times over in the model
interface (rows 7, 14, 15). Nothing connects them.

**Correction to row 12 from rows 23–24.**  Row 12 records `SortInv` from the model as *bounded —
exact, an `iff`*, on the strength of `sortEqRaw_iff`.  That `iff` is about `SortEqRaw`, which
mentions no context and no valuation `ρ`.  It does **not** certify `SortEqSupply`, the statement
`semantic_sortInv` and `semantic_sortInv_packaged` actually consume, and row 24 shows the
packaged form of that supply is vacuous.  Row 12 stands for what it says; it was being read as
covering more.  What survives of the upstream route is `U_injOn` and `semantic_sortInv` itself —
*where the model can see the conversion*.  Anything that wants the model on a judgement in an
arbitrary context owes a valuation for that context, and rows 23–24 are the first measurement of
that debt.

**Row 23 is the good failure.**  The route it records has a residual that is a *theorem*
(`interp_sort_ne_interp_forallE`), unlike rows 8, 9 and 25 whose residuals are refuted; what
collapses is only the per-conversion *packaging*, which `Above`-wrapped soundness forces.  The
distinction is worth keeping: a proved residual behind a collapsing package is a dividend waiting
on `SetModel.sound`'s deferred inputs, whereas a refuted residual is a closed road.

Rows 16–18 are the *good* rows, and §5a is about where they came from.

Rows 20–21 are worth reading together, because they are the sharpest single illustration of what
row 4 costs. `AddInductiveStepWF` is the obligation that was supposed to be *where nested
inductive declarations get verified*. Under its own premise it contains **no nested content at
all**: `ves.WF env` forbids any `.inductInfo` in the environment, so `isNestedInductiveApp?` never
fires, `numNested` is `0`, and `addInductive` returns before reaching the rebuild. Naming an
obligation after the hard case does not make the obligation cover it.

## 4. The trap: how guard 2 could print a false "proof COMPLETE"

`Verify/Inductive/AddDeclWF.lean` §5.4 item 3 proposes making `foldAddDecl_tr` a *hypothesis*
of the assembly, so that the chain type-checks while the inductive case is open. That is
exactly the wrong move, and it is refuted in the tree
(`Verify/PreludeVacuity.lean`):

    theorem anything_of_foldAddDecl_tr_hypothesis (hex : PreludeHoldsSafeInduct)
        (hbad : ∀ (fuel : FuelConfig) (ds : List Declaration) (env : Kernel.Environment),
          foldAddDecl fuel ds = .ok env → ∃ venv : VEnv, TrEnv .safe env venv ∧ venv.WF)
        (Q : Prop) : Q :=
      absurd hbad (foldAddDecl_tr_false hex)

Assuming row 2 proves **any proposition**, `kernel_sound` included, and `#print axioms` would
report nothing amiss because no axiom was added — the falsity entered as a hypothesis. The
`hex` side condition is discharged by an `#eval` in the same file, which confirms `stdPrelude`
leaves `Eq` an `.inductInfo` with `isUnsafe = false`.

The same trap exists one link earlier and shorter: `anything_of_addDeclWF_hypothesis`, from
row 19. `Bridge.AddDeclWF` is a single `def` away from `addDecl.WF` itself, so it is the more
tempting of the two to assume.

**Standing rule.** A statement in the **false** column of §3 is never to be assumed as a
hypothesis, a parameter, an `axiom`, or a `variable`. It must be *replaced* by a statement that
is true, and the replacement's non-vacuity recorded here.

## 4a. A *proved* theorem with a false statement — and what that condemns

Row 2 deserves its own section, because `foldAddDecl_tr` is not an open goal. It is a
**proved theorem** (`Verify/Bridge.lean:172`), five lines, no `sorry` of its own:

    theorem foldAddDecl_tr (hok : foldAddDecl fuel ds = .ok env) :
        ∃ venv : VEnv, TrEnv .safe env venv ∧ venv.WF := by
      obtain ⟨ves, wf⟩ := foldAddDecl_WF hok
      exact ⟨ves.venv .safe, wf.tr, wf.tr.wf⟩

and its statement is false (`foldAddDecl_tr_false`, modulo `hex`, which the `#eval` in
`PreludeVacuity.lean` confirms). A proof of a false statement means the proof rests on a
`sorry` that **cannot be filled** — filling it would prove `False`.

Its hole cone is exactly nine declarations:

    Lean4Lean.addDecl.WF                                  <-- row 1, the condemned one
    Lean4Lean.TrProj.uniq
    Lean4Lean.TrProj.weak'_inv
    Lean4Lean.TypeChecker.Inner.inferProj.WF
    Lean4Lean.TypeChecker.Inner.isDefEqUnitLike.WF
    Lean4Lean.TypeChecker.Inner.tryEtaStructCore.WF
    Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified
    Lean4Lean.VEnv.IsDefEqU.weakN_iff
    Lean4Lean.VEnv.WF.rigidShapeUniqNS

**Read this correctly.** The natural inference — "these nine are all suspect" — is wrong, and
getting it wrong would stall the work that is actually sound. Falsity does not propagate
backwards along a proof: a true lemma can perfectly well be used in an unsound derivation. What
the measurement establishes is that **at least one** of the nine is unfillable as stated, and
row 1 already identifies which: `addDecl.WF`'s `inductDecl` arm, refuted by
`addDecl_inductDecl_WF_false` independently of this cone.

The other eight are ordinary open holes, upstream of a bad consumer. `IsDefEqU.weakN_iff`,
`forallE_inv_stratified`, `rigidShapeUniqNS`, the two `TrProj` lemmas — none of them is
implicated. Rows 13 and §6 note separately that the three checker `.WF` holes will only acquire
*content* after the flip, which is a different observation (they are vacuity-adjacent, not
condemned).

For contrast, the `False`-witness half of the assembly measures clean: `hasType_falseProp`'s
cone is **7244 declarations with zero holes**. The soundness statement's other wing is finished.

Reproduce with the walker in `scripts/hole-cone.lean` seeded at
`Lean4Lean.Bridge.foldAddDecl_tr`, `Lean4Lean.addDecl.WF`, `Lean4Lean.Bridge.hasType_falseProp`.

## 5. The diagnostic, and the discipline

### The defect signature

`Theory/SetModel/CoherentWitness.lean:109` states the general rule, and it is better than an
inventory because it predicts:

> The defect signature is a structure quantifying over a relation **parameter** that the
> relation's own constructors never constrain.

It covers all three model-side refutations and correctly *acquits* the fourth candidate:

* row 14, `LevelAssign` — `IsDefEq.bvar` places no condition on the context, so `lvl_wf` and
  `lvl_sound` could be pointed at a context holding an out-of-range universe parameter.
* row 15, `Stable.lvl_instN` — `Ctx.InstN` declares `e₀` as a parameter its `zero` constructor
  never mentions, so the field could be pointed at an arbitrary substituted term.
* row 6, `coherentOn_addConstList`'s `hocc` — stated at the *pre-block* environment, which the
  constructors of the block-building relation never tie to the post-block one.
* **acquitted:** `CtxInvariant`'s companion `hRd` — its `A` and `A'` are not free, they arrive
  with a derivation `Γ ⊢ A ≡ A' : .sort u`, and that derivation is exactly what makes the two
  demands agree (`ctxInvariant_prop_agrees`, machine-checked).

Row 4 fits the same shape one level up: `TrEnv'`'s `induct` constructor constrains its premise
with `AddInduct`, which no constructor of anything can satisfy.

**So the check to run when writing a structure with several fields over a shared parameter:**
for each field, ask what pins the parameter. If nothing does, two fields can be pointed at
inconsistent instances and the structure is empty.

### Three checks, in order of cost

1. **Before proving a lemma, satisfy its hypotheses.** Exhibit one environment / one
   declaration / one value where they all hold — an `#eval` is enough, and `#eval` witnesses in
   `PreludeVacuity.lean` and `AddDeclWF.lean` are the pattern. If you cannot, the lemma is a
   candidate for §3.
2. **When you reduce a goal to a residual, bound the residual both ways.** Prove it is not
   trivially true (some instance fails) *and* not false (some instance holds). Rows 10–12 are
   what this looks like; `not_inductOracleOK_falseProp` + `inductOracleOK_empty` is the model.
   A reduction to an unmeasured residual is not progress, it is relocation.
3. **`lake env lean scripts/empty-inductives.lean` must print an accounted-for list.** Every
   empty inductive in the package needs an entry here saying why it is empty. Today: one, and
   §1 is its entry.

## 5a. This is already done well in one place — copy it

`Theory/SetModel/` is the best-audited directory in the tree, and every practice §5 asks for was
invented there. It carries **three files whose entire purpose is this audit**:

| file | what it establishes |
| --- | --- |
| `LevelAssignUnsat.lean` | the two refutations (rows 14, 15), each with the *repair* stated and the guard's load-bearing role documented at the field |
| `PropSplitAudit.lean` | satisfiability (`exists_propSplit`) **and** non-triviality of the replacement (`propSplit_not_constant`, plus `prop_forces_false` / `prop_forces_true` — a forced-`False` case and a forced-`True` case, which is non-triviality in both directions) |
| `StableAudit.lean` | satisfiability of the guarded `Stable` (`exists_stable_propSplit`) and an **exact** characterisation (`propSplitOf_stable_iff`), plus the bridge `toPropSplit_stable` from the old parameter |

Note what `no_stable`'s repair did: the `env.HasType nv Γ₀ e₀ A₀` guard now sits in
`PropSplit.Stable`'s `prop_instN` field with a docstring that says *why* it is load-bearing and
names the lemma that would fail without it. That is the pattern — **the refutation lives next to
the guard it justifies**, so nobody removes the guard as redundant.

`CnstRecursion.lean`'s residual bounds (rows 10–11) and `SemanticRouteClosed.lean`'s dead routes
(rows 8–9) are the same discipline applied outward.

## 6. Unmeasured — the to-do

Load-bearing statements whose hypotheses have **not** been checked for joint satisfiability.

The gap is **not** uniform, and an earlier draft of this section implied otherwise, which was
unfair and would have misdirected effort. `Theory/SetModel/` is audited to the standard of §5a.
What is unaudited is `Verify/` and `Theory/Typing/` — and note that rows 1–5, all in `Verify/`,
were found the moment anyone looked.

- ~~`Bridge.AddDeclWF`~~ — **now measured**, see row 19.
- The `TrProj` family — `TrProj.weak'_inv` (29 users), `TrProj.uniq` (93). These have open
  `sorry`s, so they are counted; what is unmeasured is whether their *hypotheses* are
  satisfiable at a structure the checker actually reaches, given row 13.
- `inferProj.WF` (0 users), `isDefEqUnitLike.WF` (1), `tryEtaStructCore.WF` (2) — the three
  checker `.WF` holes. Row 13 says the functions never fire today, so these three are
  vacuity-adjacent by construction: they will only acquire content after the flip.
- `docs/soundness-ledger.md`'s "Full ingredient list". Row 6 was found in it, so at least one
  entry marked available was not satisfiability-checked. Note that this bullet listed `AgreeInst`
  as unmeasured and **that was wrong** — see row 22, and the process note below. Its three entries marked *hypothesis*
  — `AgreeInst` entanglement, `Stable`, `CtxInvariant` — are in fact all covered (rows 16–18 and
  §5a), and its `LevelAssign` rows are stale by rows 7/14. **The file needs re-marking against
  this ledger**, and the remaining unchecked entries identified rather than assumed.
- `Theory/Typing/` step lemmas. No file in that directory does what `PropSplitAudit.lean` does.
  Worth a single audit file on the model of §5a rather than case-by-case doubt.

### The four uncounted obligations that block the inductive route

Found by reading for the fourth blindness above rather than by running anything. **None of these
is a decision; all four are ordinary open theorems that the census reads as 0.** They are what
stands between the tree and a nested-capable `AddInduct`, i.e. between here and the version of
the flip that would actually unblock `kernel_sound`:

1. `hctors` — a *declared* constructor's **restored** stored type is a type in the environment
   carrying the step's type constants.
2. `hrecs` — each **renamed** recursor's **restored** type is a type in the environment carrying
   those and the constructors.
3. `hrules` — each **restored** ι-rule is a well-formed definitional equation there.

   All three are hypotheses of `VEnv.addInductR_ordered'`, to be discharged from
   `OwnId` + `Faithful` + `D.WF env`. They are known **satisfiable**: `nfnAux_addInductR_ordered`
   (`Theory/Typing/ConstSubstNested.lean:1235`) supplies all three in a non-trivial instance, and
   `addInductR_ordered_nil` shows that at the identity restoration they collapse to what
   `addInduct'` already discharges. So this is a genuine open proof, not a vacuity.

   **And they are further along than "three open obligations" suggests.** All three are already
   reduced *in general* to one syntactic condition each, by
   `VEnv.ctorConstsCR_wf_of_substC` / `recConstsR_wf_of_substC` / `iotaRulesR_wf_of_substC`
   (`ConstSubstNested.lean:50, 78, 95`). Each takes a `σ : CSubst` with `σ.WF`, and a *bridge*
   asking only that the restoration's substitution carries the ordinary stored type to the
   restored one:

       (C.type D j).substC σ = C.typeR D R j          -- constructors
       (D.recType j).substC σ = D.recTypeR R j        -- recursors
       D.iotaRules.map (·.substC σ) = D.iotaRulesR R  -- ι-rules

   The `σ` is general too — `VIndRestore.csubst D K`, built from the restoration's five fields —
   and `nfn_csubst` / `nfn_csubstTy` / `ntree_csubstTy` check by computation that it *is* the
   substitution the hand-written witnesses used, with no hypothesis about the block entering.
   `csubst_closed` / `csubstTy_closed` discharge the side conditions at both witnesses.

   **CORRECTION (same day, later): the first of the three is FALSE, not open.** See rows 26–28.
   `hctors` fails under the premises `VDecl.WF.inductNested` actually has, and no strengthening of
   `Faithful`/`Built`/`Canonical`/`OwnId`/`D.WF` repairs it, because they all constrain the
   *companion* members while the failing constructor is *user-written*. It needs a **new
   conjunct** — `VIndCtor.RestoreClean` on `AddNested` and `Built` — or `VIndCtor.typeR` redefined
   so restoration applies everywhere, which is the faithful model of the implementation's
   whole-expression `restoreNested` and would make all three bridges trivial.

   What *is* proved in general: (A) for every **parameterless** nested block
   (`ctorConstsCR_wf_of_np_zero`), with the parameterful case reduced to exactly `D.np` β-steps per
   companion occurrence and nothing else. And (B)/(C) need their cleanliness condition restated
   against `csubst` rather than `csubstTy` (row 28).

   So: not three syntactic identities. One false statement needing a new conjunct, one proved case
   plus a measured β-gap, and two mis-stated conditions.

4. ~~The `induct` arm of `VEnv.WF'.keys`.~~ **Already done — `Theory/Inductive/NestedKeys.lean`.**
   And done better than "a different argument": the *invariant* is false, not just the proof.
   `KeyMajorUnique` — a rule is determined by the head of its major premise — fails in any
   environment holding a nested block, because the companion's restored ι-rule and the real
   block's own ι-rule share a major (`[NFn.rec_1, PFn.mk]` against `[PFn.rec, PFn.mk]`;
   `nfn_keyMajorUnique_false`). The replacement `VEnv.KeyUnique` (whole key determines the rule)
   is **preserved** by a nested step (`keysR_induct`), is *not* refuted by the same witness
   (`nfn_keys_ne`), and the sole consumer is re-proved from it
   (`Pat.iota_rule_uniq_keyUnique`). `nfn_keys_summary` packages all of it with no hypotheses.

   **The swap is now landed** (`8942782`): `WF'.keys` carries
   `KeysDeclared ∧ KeyHeadDelta ∧ KeyUnique`, and `keys_induct` uses head-freshness only, so its
   arm and `keysR_induct` have the same shape. `KeyMajorUnique` stays as a definition — the
   refutations are statements about it — but nothing derives it from `VEnv.WF`. It was **not** the
   "plumbing in two files" I predicted here: `keysU_addDefEq` and `keysU_addDefEqs` had to be
   written, and the first needs `df.key ≠ []`, a hypothesis the refuted version never required.

**A second process note, and it is the same failure twice.** I listed `AgreeInst` satisfiability
as unmeasured in this file's first draft. `agreeInst_zero` (`InterpSound.lean:166`) already
exhibits the witness and `beta_sound` already builds the pair with it — row 22. Combined with
item 4 below, that is **two claims of "open" in one day that were already closed in the tree**,
both from trusting a summary instead of reading the code. The rule is the same one item 4 produced
and it now applies to this file as much as to any docstring: **read the code before recording
something as open.** An instrument that overstates the work left is not conservative, it is just
wrong in the direction that wastes effort.

**A process note, from getting item 4 wrong.** I read `NestedOrdered.lean:170`'s docstring —
"it is the second of the two obligations that the `inductNested` rule waits on" — took it at face
value, and wrote a fresh refutation of `KeyMajorUnique` at the `NTree`/`List.cons` witness before
grepping. `Theory/Inductive/NestedKeys.lean` had already refuted it at `NFn`/`PFn`, stated the
replacement, proved the nested arm, and re-proved the consumer. The duplicate was deleted.
`dup-names.lean` could never have caught it: the names differed, only the *result* was the same.
**The rule that would have: grep for the invariant's name across the tree before proving anything
about it.** And note the direction of the drift — the stale docstring overstated what was open,
which is the direction that wastes work rather than the direction that hides it.

**This corrects a framing carried in `docs/critical-path.md` and in §2 above.** The `AddInduct`
flip was described as the thing standing between the tree and the main theorem, and therefore as
a decision. Half of that is wrong. The *non-nested* flip is available today and is a decision
(it costs census 14 → 17 and leaves nested blocks vacuous). The *nested* flip — the only one that
unblocks `kernel_sound`, and the one CLAUDE.md's "nested declarations are a primary target"
requires — is blocked on the four items above, and no decision makes them go away.

## 7. Related files

- `docs/critical-path.md` — what stands between here and `kernel_sound`, with Corrections 3
  and 4 recording rows 1–4.
- `docs/frozen-edit-requests.md` — the proposals touching frozen files, none made. Its closing
  section notes that the flip is *not* one.
- `docs/soundness-ledger.md` — the abstract-side inventory; row 6 is its correction.
- `scripts/empty-inductives.lean` — the instrument for §1; wired into `scripts/status-report.sh`.
- `Theory/SetModel/LevelAssignUnsat.lean`, `PropSplitAudit.lean`, `CoherentWitness.lean`,
  `StableAudit.lean` — the audit apparatus of §5a, and the source of the defect signature.
  Read these before writing a new one.
