# Handoff: `hargs` attacked once — the scope half is necessary, and it is free

**Written 2026-09-03. WRITTEN INCREMENTALLY — earlier entries were true when written.**
One file, mine, new: `Lean4Lean/Verify/Inductive/HargsAttack.lean`. Nothing else created or edited.
Frozen files (`Verify/Soundness.lean`, `Verify/Axioms.lean`, `Verify/Guard.lean`) not read for
editing, not written, not `touch`ed. No state-changing `git`. `docs/vacuity-ledger.md` untouched.

## 0. The pre-flight, which is the most important part of this round

The brief says of `hargs`: *"It is **consumed** at many sites and **produced nowhere**. A
`shape.lean` scan reported 8 hits, 0 structure fields, all consumers, and **nothing refuting it**."*

**The "produced nowhere" half is a false absence, and it is the fourteenth in this project.**
Measured with `scripts/exists.lean` against the compiled environment (432 built modules), before I
wrote a line of Lean:

| declaration | module | arity | cone | hole-free |
| --- | --- | --- | --- | --- |
| `Lean4Lean.InductiveDeclExamples.ntreeAux_spineHargsC` | `Verify.Inductive.SpineClause` | **0** | 3772 | yes |
| `Lean4Lean.InductiveDeclExamples.ntreeAux_datum_of_wf_inhabited` | `Verify.Inductive.ArgsTypedSupply` | **0** | 2388 | yes |
| `Lean4Lean.InductiveDeclExamples.ntreeAux_argsTypedK_of_wf` | `Verify.Inductive.ArgsTypedSupply` | 3 | 2039 | yes |
| `Lean4Lean.VIndRestore.SpineHargsC` | `Verify.Inductive.SpineClause` | 5 | 611 | yes |
| `Lean4Lean.VIndRestore.restrictStep_entry` | `Verify.Inductive.RestrictStep` | 9 | 3257 | yes |

`ntreeAux_spineHargsC` **is** `hargs` at `ntreeAux`, at `AddInductStagesR`'s first stage, arity 0,
existentially closed, hole-free — i.e. exactly deliverable (d) of my brief, already in the tree, at
the same block, delivered by the round before mine. `NestedWit.nfnAux_spineHargsN` is the same at the
second witness. So the round order is: `HargsShared` isolated the datum → `ArgsTypedSupply` produced
it at two blocks from `D.WF` → `RestrictCompanion` moved it to the consumption environment →
`SpineClause` restated it over checker-side data and **measured the `TrIndDeclN` field edit at three
sites** → `RestrictStep` proved the general case is an `↔` with one constant-strengthening step.

**What is actually open** is the general case, and `RestrictStep`'s `restrictStep_entry` already says
what it is: `D.ArgsTypedK K e₁ occ ↔ R.ValStrengthen D K e₂ e₁`, one closed `HasType` across one
`addConstList`, i.e. a `VEnv.AxiomConservativityWF` instance — which my brief forbids me to use, and
rightly. So "produce `hargs` in general" was not available to this round by construction, and I did
not attempt it.

I therefore attacked the one thing about `hargs` that no round had measured: **its scope.**

## 1. Headline

| # | claim | grade |
| --- | --- | --- |
| 1 | **`hargs` implies the corner's *other* spine hypothesis.** `∀ a ∈ R.tyArgs j, a.ClosedN D.np` (`hcl`, carried as a separate hypothesis in **14 modules**) is a consequence of the datum: a typed spine is a scoped spine | **proved**, general, hole-free |
| 2 | **…so `SpineClause.lean` §4's transport loses a hypothesis**: `csubstTy_WF_of_hargs` gives `(R.csubstTy D K).WF e₂ e D.uvars` from the clause with `(R.csubstTy D K).Closed` **discharged** | **proved**, general, hole-free |
| 3 | **`ConstSubstNested.lean`'s `csubstTy_closed` asks for its spine hypothesis unguarded**, at every `j` including `j ≥ D.types.length` where `Built`, `OwnId` and `Faithful` are all silent. Guarded, it is provable, and guarding is what lets claim 2 exist | **proved** (`csubstTy_closed_guarded`) |
| 4 | **The negative: `Occurs`, `OccursN` and `KFresh` are blind to the spine's scope**, and `hargs` is FALSE of an unscoped spine. So no consequence of the occurrence record produces `hargs`, at any block — the `Occurs`/`OccursN` route is closed the way `instAt_indep_of_tyArgs` closed the `Faithful` route | **proved**, general, hole-free |
| 5 | **`Faithful` measured, clause by clause**: `ty_agree` transports to an arbitrary spine (under `instAt_indep`'s condition), `ctors_complete` transports unconditionally, `ctor_agree` does not | **proved** for two of three; third read off |
| 6 | **The missing clause, and both traps**: `VIndRestore.SpineClosedC`, environment-free, no `occ`, no staging premise; existentially closing it is vacuous; and it is **free at the datum**, so the flip's price stays **one** clause | **proved** |
| 7 | The implementation already enforces claim 6's clause, by an explicit `throw` | read off `Inductive/Add.lean` |
| 8 | Arity-0 witness at `ntreeAux` running claims 1–4 and 6 through the general theorems | **proved** |

## 2. `hargs`, and what it would take to produce it

Stated in my file as `VIndRestore.HargsAt` (per member) with `spineHargsC_iff_hargsAt : Iff.rfl`
against `SpineClause.lean`'s bundle, and `tyVal_hasType_of_spineHargsC` proves it is *literally*
§8.7's residual (`tyVal_hasType_of_hargs` applied to it, `hsplit` already free).

`instAt_indep_of_tyArgs` is a lower bound on any proof: whatever produces `hargs` must be
restoration-*dependent*. §3c of my file measures the candidates the brief named. The result is a
lattice, not a list:

* **length only** — `VNestedOcc`, `Occurs` (`Occurs.setArgs`);
* **length + a condition on constants** — `OccursN` (`args_noNested`), `KFresh` (`argsNoK`);
  `OccursN.setArgs` / `KFresh.setArgs` transport both to **any** spine of the right length made of
  de Bruijn variables, because a variable mentions no constant;
* **a syntactic equation** — `Faithful.ctor_agree` (through `C.typeR D R j`, which substitutes
  `R.csubstTy`, whose values contain `R.tyArgs`), `Built.member`, `TrIndDeclN.trCtors` (`TrExprS` of
  `C.typeR D R j`);
* **a typing** — nothing.

The middle two rows are the whole answer to "what is available": everything short of a judgement is
either scope-blind or pins the spine into a *stored type*, and a stored type carries no scope
obligation of its own — `instAt_indep_of_tyArgs` is precisely the observation that the companion
member's stored type may not read the spine at all.

## 3. Claim 1/2/3 — the scope invariant, and the hypothesis it kills

`VEnv.HasArgs.closedN`: each argument of a `HasArgs` over `Γ` is `ClosedN Γ.length`. Engine:
`VEnv.IsDefEq.closedN` (the scope invariant of typing, `Theory/Typing/Lemmas.lean`) plus
`VEnv.HasArgs.mem_wf` (`ArgsTypedSupply.lean`). **No inversion, no `VEnv.HasArgs.of_mkApp`, no
`PiInv`** — the corner's `PiInv`-free invariant (`NestedTele.lean` §T12/§T15/§T16) is intact for a
sixth round; `of_mkApp` occurs in my file **once**, in the prose above, and **zero** times in code.

Then `spineHargsC_closedN` (datum ⟹ guarded `hcl`), `csubstTy_closed_of_spineHargsC`
(⟹ `(R.csubstTy D K).Closed`, with `VExpr.ClosedTele D.params 0` coming free from `D.WF.params`),
and `csubstTy_WF_of_hargs` — `SpineClause.lean` §4's `csubstTy_WF_of_spineHargsC` with `hcl` gone.

Why this matters beyond one hypothesis: `grep -rln 'a.ClosedN D.np'` finds it in **14 modules**
besides mine — `ConstSubstNested.lean`, `RestoreBridge.lean`, `NestedRules.lean`, `NestedTele.lean`,
`CtorBeta.lean`, `RecTyped.lean`, `HTeleGen.lean`, `HTeleNTree.lean`, `HTeleRecB.lean`,
`IotaHargsGen.lean`, `HargsShared.lean`, `HypTrimWitness.lean`, `FldDischarge.lean`,
`ValRestGeneral.lean` — including `substC_tyApp_defeq_tyAppR_comp` (obligation (A)'s β-gap head
defeq) and `csubst_hbridgeD_of_betaD` (arity **32**). Its only producers in the tree are
witness-specific (`ParamRedex.lean` §7's `mpRestore_tyArgs_closedNp`, `NestedRules.lean`'s
`ntree_tyArgs_closedN_np`). It was being counted as a second residual; it is a consequence of the
first. (Module count is a grep, i.e. a floor on the sites and an exact count of the modules.)

**The guard, and why it is a correction rather than a lemma.** `csubstTy_closed`'s hypothesis is
`∀ j, ∀ a ∈ R.tyArgs j, a.ClosedN D.np` — unguarded. Every clause of `Built`, `OwnId` and `Faithful`
is guarded by `D.types[j]? = some T`, so at `j ≥ D.types.length` the unguarded form is not derivable
from any bundle in the tree. It is also unnecessary: `csubstTyList` filters over `D.types.zipIdx`,
and `VIndRestore.csubstTy_dom` hands the index facts back. `csubstTy_closed_guarded` is the same
proof with `csubstTy_dom` in place of a discarded membership. (Same shape as `RestrictStep.lean`
§4(a)'s finding about `ArgsTypedK.restrict_of_val`'s unguarded `hargs` — that is now twice.)

## 4. Claim 4 — the negative, and the family

* `VEnv.not_hasArgs_of_not_closedN` — a spine with an argument loose in the context is not a
  well-typed spine, against **any** telescope, at any `Ordered` environment with a closed context.
* `VNestedOcc.looseSpine N D` = `N` with its spine replaced by `N.decl.np` copies of `.bvar D.np`
  — the first variable *past* the new block's parameter telescope.
* `looseSpine_occursN` : `OccursN` survives it, at the same environment, for every `N`.
* `looseSpine_not_argsTypedH` : the datum fails, for every `D` and every `Ordered e` with the
  parameter context well formed. The only non-degeneracy needed is `0 < N.decl.np`.

So: **at every occurrence record whose foreign block has a parameter, there is a spine at which the
whole environment-free bundle holds and `hargs` is false.** `args_noNested` cannot help — a de Bruijn
variable mentions no constant at all. This is the `Occurs`/`OccursN` analogue of
`instAt_indep_of_tyArgs`, and it is *unconditional* where that one needs a closed split body.

**What the negative is NOT.** It does not refute `hargs` at a real block, and it must not be read
that way: it refutes `hargs`-from-the-occurrence-record. The three syntactic rows of §2's lattice
(`Faithful.ctor_agree`, `Built.member`, `TrIndDeclN.trCtors`) do move when the spine moves, so a
separating witness *against those* needs a whole re-spined block, which I did not build. Those three
rows are read off their definitions and labelled as such in the file.

## 5. Claim 7 — the implementation enforces exactly the missing clause

`ElimNestedInductive.isNestedInductiveApp?` (`Lean4Lean/Inductive/Add.lean`, ~line 796) sets
`looseBVars` if any of the occurrence's first `numParams` arguments `hasLooseBVars`, and then

```
if looseBVars then
  throw <| .other s!"invalid nested inductive datatype '{fn}', \
    nested inductive datatypes parameters cannot contain local variables."
```

`replaceAllNested` traverses the constructor type with only the block's parameters opened as fvars
(`withParams ctor.type nparams`), so an occurrence under a *field* binder would have loose bvars in
its spine — and that is the case the throw rejects. So §4's family is **not a soundness bug**: it is a
condition the implementation checks and the abstract theory has not recorded. Anyone tempted to read
§4 as a kernel bug should read this paragraph first. (`bugs-found.md` and `divergences.md` are
untouched; there is nothing to record in either.)

## 6. Claim 6 — the clause, with both traps checked

```lean
def VIndRestore.SpineClosedC (R : VIndRestore) (D : VInductDecl') (K : List Name) : Prop :=
  ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K →
    ∀ a ∈ R.tyArgs j, a.ClosedN D.np
```

* **Trap 1, statability.** Over `R`, `D`, `K` and nothing else: no `occ`, no `npJ`, no environment,
  and — unlike `SpineClause.lean` §5's `SpineHargsN` — **no staging premise**, because closedness is
  not a judgement. Vocabulary: `VExpr.ClosedN`, `VIndRestore.tyArgs`, `VInductDecl'.types`/`np`,
  `VIndType.name`, all in scope in `Verify/Environment/InductR.lean` where `TrIndDeclN` lives (that
  file's own measured probe field already writes `VExpr.splitPis` and `D.types[j]? = some T`). So it
  is statable as a `TrIndDeclN` field *and* as a `Built`/`KFresh` field — the trap a previous round
  hit (a clause that could not be *stated* where it was needed) does not bite here.
* **Trap 2, vacuity.** `exists_spineClosedC` : `∃ R, R.SpineClosedC D K` is **provably trivial** for
  every block and every `K` (the empty presentation). So it has to be a field on the restoration the
  step already carries — the same trap `VInductDecl'.exists_spineHargsK` records for the `occ` form
  of the datum.
* **And it is free.** `spineClosedC_of_spineHargsC`. **So the flip's price stays one clause**: if
  `SpineClause.lean` §4's measured `trSpine` field lands, the scope condition is not a second field.
  `not_spineHargsC_of_not_spineClosedC` is the converse direction — the clause is *necessary*.

**My recommendation to the orchestrator, stated as a recommendation and not as an edit**: do **not**
add a scope field. Add `SpineClause.lean` §4's `trSpine` (three discharges, all measured by that
round) and take `SpineClosedC` as its corollary. If for some reason `trSpine` is not wanted, the
scope clause alone is the cheapest thing in this corner — no environment, no staging — but it is not
sufficient for `hargs` and I make no claim that it is.

## 7. Claim 8 — the witness

`InductiveDeclExamples.ntreeAux_hargs_scope_witness`, **arity 0**, existentially closed, at
`ntreeAux` (`uvars = 1`, `params = [Type u]`, `np = 1`, `recUvars = 2`, spine `[NTree.{u} #0]`).
Nine conjuncts: the staging (three), the datum at stage 1, §6's clause, `(csubstTy).Closed`, the
**whole** `(R.csubstTy D K).WF env₂ env₃ 1`, and §4's separating pair at the real occurrence
`List (NTree α)`.

Its value is the **route**: the two `ClosedN` conjuncts are *not* `decide`d, they come from the datum
through `spineHargsC_closedN`; the `WF` conjunct is `csubstTy_WF_of_hargs`, the general theorem, with
its `hcl` discharged by the general theorem. The only block-specific inputs are `ntreeAux_spineHargsC`
(the datum, `SpineClause.lean`), `ntreeAux_built`, `ntreeAux_WF'`, `ntreeAux_params_WF`,
`listOcc_occurs`, `listEnv_ordered` and `ntreeAux_tyLvls_wf` — all pre-existing.

### 7a. Non-degeneracy

* `listOcc_decl_np_pos : 0 < listOcc.decl.np` — the foreign block has a parameter, so §4's spine is
  not `[]` and the refutation is not about an empty `HasArgs`.
* `ntree_not_spineClosed_zero` — the **strengthening** of §6's clause to `ClosedN 0` is FALSE at the
  **companion** member, so the clause is not the trivial "closed spine" condition. This is *not*
  `NestedRules.lean`'s `ntree_not_tyArgs_closed0`, which refutes the unguarded `hcl0` at `j = 0`, the
  block's **own** member, where `OwnId` forces `R.tyArgs 0 = bvars 0 D.np` — a statement about the
  identity presentation, not about the presented spine.
* `listOcc_looseSpine_ne` — the separating spine differs from the real one, so §7's last two
  conjuncts are not about the same record.

## 8. Corrections to what I was handed

1. **"produced nowhere … nothing refuting it"** — §0. `hargs` is produced at two blocks, one of them
   arity 0 at the very block my brief asks for a witness at. The `shape.lean` scan that reported "8
   hits, all consumers" was asking about the *shape*; the producers are `SpineHargsC`-shaped and
   `ArgsTypedK`-shaped, which that scan's heads do not match. A shape scan is a floor, not a census.
2. **"(A) reaches it via `csubst_hbridgeD_of_betaD` (arity 32) → `BetaD` → `hbody`"** — correct, and
   one of that theorem's 32 arguments is `hcl`, which §3 now derives from the datum. I did not edit
   `FldDischarge.lean` (not mine); the general theorem is in my file and its owner can compose it.
3. **`instAt_indep_of_tyArgs` "proves that no restoration-independent argument can produce it"** —
   true, and §3c generalises it from `instAt` to `Faithful.ty_agree`, which is the form the sentence
   is usually *used* in. But note it does **not** cover `Faithful.ctor_agree`, whose right-hand side
   `C.typeR D R j` moves with the spine. The lower bound is about two of `Faithful`'s three clauses.
4. **The brief's candidate list is right and incomplete**: `TrIndDeclN.trCtors` does constrain the
   spine (through `TrExprS` of the *restored* constructor type, at `addIndTypesC`-env, which is the
   consumption environment) — but only as a translation, and `TrExprS` is not a typing judgement.
   That is where a future round should look if it wants a *cheaper* clause than `trSpine`: the
   checker really does typecheck the user's constructor type at that environment, and `TrIndDeclN`
   keeps only the translation of it.

## 9. Verification record

* `Lean4Lean/Verify/Inductive/HargsAttack.lean`: 520 lines, **26 declarations** (3 defs, 23
  theorems), **23 `#print axioms` lines, every one `[propext]`, `[propext, Quot.sound]` or
  `+ Classical.choice` — no `sorryAx` anywhere**.  Names read off the file's own `namespace` lines
  and re-checked with `scripts/exists.lean` against the compiled environment (433 modules): all 26
  `FOUND`, `own value is a hole: false`, `cone reaches sorryAx: false`.
* `lake build Lean4Lean.Verify.Inductive.HargsAttack`: exit 0, **204 jobs**, **no warnings from my
  file** (`grep 'HargsAttack' ` over the build log is `info:` lines only).
* Full `lake build`: **1619 jobs, exit 0, zero `error:` lines**.
  `grep -c 'automatically included section variable'`: **1**, and it is
  `Foundation/FirstOrder/SetTheory/Z.lean` — upstream, **0** from Lean4Lean.
* Guards: `guard 1 ✓ (24 frozen axioms)`, `guard 2 ✓ (whitelist; proof INCOMPLETE — sorryAx
  present, unchanged)`, `guard 3 ✓ (2/2)`.
* `scripts/sorry-census-all.lean`: **13 holes**, `BUILT: 436`, **`in population but NOT BUILT: 0`**.
  My file is in the population and adds none.
* `scripts/dup-names.lean`: "no duplicate Lean4Lean declarations across the joined cone".
* `of_mkApp`: **1 occurrence in my file, in prose, 0 in code** — the nested corner stays
  `PiInv`-free for a sixth round.  `VEnv.HasArgs.of_mkApp`, `VEnv.IsDefEq.uniq` and
  `VEnv.AxiomConservativityWF` appear nowhere in my code, per the brief.
* Frozen files (`Verify/Soundness.lean`, `Verify/Axioms.lean`, `Verify/Guard.lean`): not read for
  editing, not written, not `touch`ed; absent from `git status`.  `docs/vacuity-ledger.md`
  untouched.  `git status --short` in the final state lists exactly my two new files.
* Other streams' files read and imported, never edited: `HargsShared.lean`, `NestedRules.lean`,
  `NestedBuild.lean`, `Restore.lean`, `RestoreBridge.lean`, `ConstSubstNested.lean`,
  `TeleMove2.lean`, `SpineClause.lean`, `ValAtParam.lean`, `ValAtPrice.lean`,
  `RestrictCompanion.lean`, `RestrictStep.lean`, `ArgsTypedSupply.lean`, `FldDischarge.lean`,
  `ValRestGeneral.lean`, `Verify/Environment/InductR.lean`, `Inductive/Add.lean`.
* No state-changing `git`, no `lake update`, nothing sent outside this repo.
  `tryEtaStructCore.WF` / `isDefEqUnitLike.WF` (row 197): untouched.  **The flip was not made.**

### 9a. Measured vs read off

**Measured this round:** every axiom line, per declaration, from the compiler, and again with
`exists.lean`; the pre-flight table in §0 (arities, cones, hole-freeness of five pre-existing
declarations, before writing Lean); that `Occurs`/`OccursN`/`KFresh` transport under an arbitrary
spine (Lean accepted the transports — that *is* the measurement, not a reading of the definitions);
that `Faithful.ty_agree` and `ctors_complete` transport and that `csubstTy_closed`'s hypothesis can be
guarded (by proving both); the witness and every `decide` in §7/§7a; the census, dup-names, guards,
job counts and section-variable count.

**Read off source, not independently proved:** `Inductive/Add.lean`'s `throw` (§5 — a reading of the
implementation, and the *reason* the family in §4 is not a bug, so it is load-bearing prose and I flag
it as a reading); that `Faithful.ctor_agree`, `Built.member` and `TrIndDeclN.trCtors` see the spine
(read from `typeR`/`member`/`TrIndCtorR`'s definitions — no separating witness built, §4's last
paragraph); the 14 `hcl` modules (grep — exact as a module count, a floor as a site count); `RestrictStep.lean`'s `restrictStep_entry` verdict on the general case (read from its
statement and handoff, not re-derived).

## 10. Pick up first

1. **The clause is `trSpine`, and its scope half is free.** §6.
2. **`TrIndDeclN` keeps `TrExprS` of the restored constructor type but not its typing.** §8 item 4.
   The checker's `AddInductive.run` *does* typecheck the user's constructor type in an environment
   where the block's own type constants are declared — which is `addIndTypesC`-env, exactly where
   `hargs` is consumed. A clause recording that typing would be strictly more natural than one
   recording a `HasArgs`, and it would need a Π-descent into the field position to be used — which
   is why `trSpine` is still the cheaper edit today. Do not start on it without pricing the descent
   against `docs/research-sort-inv.md`.
3. **Do not** try to prove `hargs` from `Occurs`/`OccursN`/`KFresh`/`Faithful.ty_agree` — §4 and §3c
   are machine-checked negatives.
4. **Do not** close `tryEtaStructCore.WF` / `isDefEqUnitLike.WF` (row 197), and **do not** make the
   flip.
