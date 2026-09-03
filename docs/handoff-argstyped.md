# Handoff: carrying the nested flip's shared datum across the `Theory`/`Verify` boundary

**Written 2026-09-03.**  One file, mine, new:
`Lean4Lean/Verify/Inductive/ArgsTypedSupply.lean` (914 lines, **197 jobs**, exit 0, no warnings
from my file).  Nothing else was created or edited.  Frozen files (`Verify/Soundness.lean`,
`Verify/Axioms.lean`, `Verify/Guard.lean`) not read for editing, not written, not `touch`ed; they
do not appear in `git status`.  **The flip was not made** and is not available.

## 0. Grading discipline

Every `#print axioms` line in the file is **hole-freeness and nothing else**
(`docs/vacuity-ledger.md` §0, rows 195/199b/205).  Inhabitation is asserted separately, in §5
below.  **All 54 declarations are hole-free** (47 carry a `#print axioms` line, and `grep -c sorryAx` over the build output is **0**) — no `sorryAx` anywhere, and
in particular **no `HasArgs.of_mkApp`**, so the nested corner's `PiInv`-free invariant
(`NestedTele.lean` §T12/§T15/§T16) is intact, as the brief required.

## 1. Headline: the brief named the wrong door, and the right one was already open

| # | claim | grade |
|---|---|---|
| 1 | **`docs/handoff-hargsshared.md` §4a's "`D.WF venv` cannot supply the datum either" is FALSE.**  The companion member's *constructors* are members of `D.types`, so `VInductDecl'.WF.ctors` sees the substituted field types, and `VIndField.WF.pos` types the spine | **proved**, hole-free, at **two** blocks |
| 2 | Hence: **the shared datum, and at `nfnAux` also §8.7's `val` clause, hold with NOTHING hypothesised** — closed theorems, no free variables | **proved** `[propext, (Classical.choice,) Quot.sound]` |
| 3 | The clause is **not derivable from `RestoreData` + `OccData`** — and the two invariance theorems that show why are general, not witness-specific | **proved**, hole-free |
| 4 | §8.7's `val` clause from the clause **in general**, hole-free, no `of_mkApp` | **proved** |
| 5 | The clause is **one** datum, not two: §4b's "honest count" collapses without `HasArgs.congr_tele` | **proved**, under a syntactic side condition both witnesses satisfy |
| 6 | `docs/handoff-hargsshared.md` §7 item 2's requested generalisation (no pre-block environment can carry the clause) | **proved**, general |
| 7 | §4a's own one-line theorem `addInductStagesR_no_spineTyped` | **NOT landed** — §7 below says what it costs |

## 2. Where you are wrong

**(a) The discharge site.**  The brief says:

> That round named its discharge site and could not reach it: **`TrIndDeclN` / `RestoreData`, on
> the `Verify/` side.**

That is where a *new clause* would have to go, and §3 of my file proves a new clause is what the
**general** discharge costs.  But it is not where the datum comes from at either block in the tree.
`InductStepNested` (`Verify/Environment/InductR.lean:476`) has **four** conjuncts, and
`docs/handoff-hargsshared.md` §4a ruled out three of them to reach `TrIndDeclN` by elimination.  Its
ruling on the third is wrong:

> `D.WF venv` **cannot** supply the datum either, and that is already a theorem:
> `VIndRestore.instAt_indep_of_tyArgs` … shows the companion member's stored type is blind to the
> presented spine when the split body is closed.

`instAt_indep_of_tyArgs` is true and is about `VNestedOcc.instAt` — the companion member's **stored
type**.  `List`'s type is `Type u → Type u`, `(splitPis 1 ·).2` is the closed term `Type u`, and
`instAll` throws the spine away.  All correct.  But `VInductDecl'.WF.ctors` is quantified over
**every** `j` with `D.types[j]? = some T` and **every** `C ∈ T.ctors`, and the companion member is
in `D.types` — so `D.WF` also runs on the companion's constructors, whose field types are
`VExpr.instAll (F₀.type.instL N.lvls) N.args k`.  Those are *not* blind to the spine.  The
elimination argument therefore does not go through, and the "by elimination the source is
`TrIndDeclN`" conclusion is unsupported.

**Concretely** (`VInductDecl'.WF.recField_canonResult`, general; then the two instantiations): the
foreign block has a constructor whose field type *is* one of its parameters (`PFn.mk`'s first field
`.bvar 0`; `List.cons`'s first field likewise).  Nesting substitutes the spine argument for it, the
recogniser fires — this is exactly the field nesting *manufactures*, which `listOcc_recog_field0`
already records — and `VIndField.WF.pos`'s sixth conjunct is

    env₁.HasType D.uvars (r.binders.reverse ++ Γ) (r.canonResult D i) (.sort D.lvl)

which at that field is `NFn : Type` / `NTree #0 : Type u` over `D.params.reverse`.  That is the
clause's entire content at both blocks.

**(b) Outcome 3 was not the right shape.**  The brief offered "a measurement showing it cannot be
supplied there".  What is true is finer: it cannot be supplied from the **name-discipline** bundles
(§3, and that half is general and now machine-checked), and it **can** be supplied from `D.WF` at
both blocks (§5).  Reporting only the negative would have been the more expensive error of the two,
in the ledger's own classification (failure kind 4).

**(c) "Its ownership was `Theory/`."**  Half true and worth recording: the *statement* had to move
to `Verify/` to be about `RestoreData`/`OccData` (§3), but the *producer* is a `Theory/`-side
hypothesis (`D.WF`) that `HargsShared.lean` could have used without crossing the boundary at all.
The round before mine had the ingredient in scope and ruled it out on a misread citation.

**(d) I did not verify** the brief's `Inductive/Add.lean:1121` pointer, and make no claim about it.

## 3. Claim 3: the clause is new content — measured, and generally

Two invariance theorems, both one line, both general:

* `ElimNestedInductive.Result.OccData.setArgs` — `OccData types occ` implies
  `OccData types (fun j => { occ j with args := as j })` for **arbitrary** `as`.  The proof
  transports all six fields verbatim; that is only type-correct because **none of them mentions
  `VNestedOcc.args`**.  This is the measured form of "`OccData` cannot see the spine".
* `ElimNestedInductive.Result.RestoreData.setArgs` — `RestoreData` transfers to any other spine
  satisfying its one spine field, `args : ∀ j, ∀ a ∈ tyArgs j, a.NoConstIn IsNestedName`.  So
  `RestoreData` sees the spine through exactly one **environment-free name** condition.  (That is
  the shape `Verify/Inductive/OccArgsTyping.lean` §4 proved was the only satisfiable one — its
  refutation of every *environment*-indexed spelling is what makes this a boundary rather than an
  oversight.)

Then the junk instantiation, at the tree's own nested witness:
`pfnOccJunkArgs = { pfnOcc with args := [.const `Junk []] }`, `nfnAsJunkArgs = fun _ => [Junk]`.
`argsTypedK_independent_of_restoreData_occData` bundles: **all fourteen** `RestoreData` fields,
**all six** `OccData` fields, the spine agreement `Built.tyArgs` needs, and
`¬ nfnAux.ArgsTypedK nfnK e (fun _ => pfnOccJunkArgs)` — at **every** `Ordered` environment that
does not declare `Junk`, which is every environment of the step.  So no derivation of the clause
from those two bundles exists, and it cannot be added to either as a *derived* field.

What `Built` adds is worth saying precisely: `Built.member` **does** pin the spine, syntactically,
against the companion member the block declares — junking the spine breaks `member`, because
`pfnAuxMk`'s first field type is literally `NFn`.  It pins it to a *term*, not to a typing.  The
typing is `D.WF`'s job, which is §5.

## 4. Claim 4: §8.7's `val` clause, in general, hole-free

`VIndRestore.tyVal_hasType_of_argsTypedK` / `_of_argsTypedK'`.  The point is that **no conversion
is needed**: `VNestedOcc.ArgsTypedH.ty` *is* `tyVal_hasType_of_hargs`' `hargs`, once four existing
facts identify the telescope —

* `Built.tyName` : `R.tyName j = (occ j).tyName`,
* `Built.tyLvls` : `R.tyLvls j = (occ j).lvls`,
* `Built.tyArgs` : `R.tyArgs j = (occ j).args`,
* `Occurs.ty_const` : the looked-up `ci` **is** `⟨(occ j).decl.uvars, (occ j).src.type⟩`,

so `R.declTele ci ((occ j).decl.np) j` is literally
`(splitPis (occ j).decl.np ((occ j).src.type.instL (occ j).lvls)).1`.  No `of_mkApp`, no `e.WF`, no
length side condition, no `PiInv`.  `hargs_of_argsTypedK` is the transport; it is four rewrites.

The other three sites go through the *applied* form, which `Built.spineTyped_ty_of_argsTypedK` /
`_ctor_of_argsTypedK` deliver (they are `HargsShared`'s producers with `ArgsTypedH.toArgsTyped`
pre-composed, so nothing new is proved there — it is wiring, and I say so).

## 5. Inhabitation, stated separately from hole-freeness

**Two closed theorems, no free variables, nothing hypothesised:**

* `NestedWit.nfnAux_datum_of_wf_inhabited` — at `nfnAux` (`NFn` nesting `PFn`, the block
  `NestedRestoreWit.lean` builds the checker's `Result` for): environments exist at which the
  clause holds, **the shared datum holds at the presented type head**, and **§8.7's `val` clause
  holds**.  `[propext, Classical.choice, Quot.sound]`.
* `InductiveDeclExamples.ntreeAux_datum_of_wf_inhabited` — at `ntreeAux` (`NTree α` with a
  `List (NTree α)` field, `np = 1`, the block Lean's own kernel runs the nested elimination on):
  the clause and the datum at the presented head `List.{u} (NTree.{u} #0)`.
  `[propext, Quot.sound]`.

The **joint** check the ledger's row 205 asks for is `NestedWit.nfnAux_argsTypedK_inhabited`: one
block, one `D`, one `K`, one `R` (`nfnRestore' = mkRestore …`, the restoration the *checker's*
`Result` computes), one `occ`, one environment, and simultaneously the clause, `Built`,
`RestoreData`, `OccData` and the datum.  Its environment is `AddInductStagesR`'s **first stage** —
`env₂` extended by `nfnAux.typeConstsC nfnK` — which is the staging §8.7 wants; §5.3's is
`env.addIndTypes nfnAux`, which is where `WF.ctors` is staged.  At this witness §8.7 fires at
**both** (`nfnAux_tyVal_hasType`, `nfnAux_tyVal_hasType_of_wf`).

Non-degeneracy, `decide`-checked: `pfnOcc_args_ne_nil` (the `HasArgs` is not `.nil`),
`pfnOcc_args_ne_bvars` (not the identity presentation, so not `idRestore` in disguise),
`pfnOcc_tyName_ne_own` (the presented head is a **foreign** constant), `nfnK_companion` (the index
really is in `K`, so the producers do not fire vacuously).  `ntreeAux` adds `np = 1` and a spine
that is an *applied* head, so neither witness's shape is load-bearing.

`nfnAux_WF : ∀ {env}, nfnAux.WF env` (`Theory/Inductive/NestedBuild.lean`) is **unconditional**, so
at that witness the `D.WF` route leaves no hypothesis but the staging, and
`nfnAux_addIndTypes_exists` discharges the staging.  `ntreeAux_WF` takes the `listDecl` staging,
which `ntree_stage₂_exists` supplies.

### 5a. What is NOT inhabited here

* Nothing shows the clause at any block other than these two.
* `MotiveShape` / `MinorCtorShape` — the residuals `HargsShared` §5 leaves once the datum is
  supplied — are not touched.  They are another stream's.
* No `AddInductStagesR` instance appears anywhere in my file (see §7).

## 6. Two more results worth carrying forward

**(a) The clause is one datum, not two.**  `VNestedOcc.argsTypedH_of_ty` builds the whole clause
from `ArgsTypedH.ty` alone, given
`∀ C ∈ N.src.ctors, (splitPis N.decl.np ((C.type …).instL N.lvls)).1 = (splitPis N.decl.np (N.src.type.instL N.lvls)).1`
— **syntactic** telescope agreement.  `docs/handoff-hargsshared.md` §4b's "honest count: the datum
is two, not one … collapsing the two would go through `VEnv.HasArgs.congr_tele`" is therefore about
the general case only; both witnesses satisfy the syntactic condition by `decide`
(`pfnOcc_ctorTele_agree`, `listOcc_ctorTele_agree`, the latter for **both** of `List`'s
constructors).  So the `congr_tele` stream is not on the critical path for this datum.

**(b) The boundary, in general.**  `VNestedOcc.not_argsTypedH_of_not_constsIn`: if any spine
argument fails `VExpr.ConstsIn · e.contains` then the clause is false at `e`.  Its engine is a new
one-line lemma `VEnv.HasArgs.mem_wf` (each argument of a well-typed spine is well typed) — no `WF`,
no inversion, no `PiInv`.  This is `docs/handoff-hargsshared.md` §7 item 2's requested
generalisation of `ntree_not_spineTyped_pre`, and `pfnOcc_not_argsTypedH_pre` instantiates it at the
second witness, where the spine is a **bare constant** and the block has **no parameters** — so the
pre-block refutation is not an artefact of the `ntreeAux` shape either.

## 7. `addInductStagesR_no_spineTyped`: not landed, and what it costs

The brief made this a secondary deliverable.  I did not land it, and the reason is a measurement
rather than an absence of effort:

* At a **companion** index the refutation needs a junk spine to survive `AddIndConsts`, whose `cons`
  carries `TrConstant .safe env ci ci'`.  `TrConstant` needs the declared type to be a *translation*
  of a closed `Expr`, so the junk cannot be an undeclared constant (translation fails) and cannot be
  a `.bvar` (a closed `Expr` translates to a closed `VExpr`).  It has to be a declared constant at
  the wrong type — and then refuting the datum is application inversion plus uniqueness of types,
  i.e. `IsDefEqU.forallE_inv`, which is a `sorry` in `Theory/Typing/Injectivity.lean` and is exactly
  the `PiInv` line the nested corner is keeping out.
* At a **non-companion** index it is cheap — `mkRestore.tyName j = .anonymous` off the block, so
  `HeadApp` is `.const .anonymous []` and `VEnv.addInductR_constants_of_not_mem` plus
  `IsDefEq.constsIn` refute it — but it needs `env'.Ordered` at the *output* of the stages, which
  `addInductStagesR_wit'` does not carry, and it would only refute the datum at an index where the
  datum is never wanted.  I judged that not worth the `Ordered` derivation.
* **And §5 removes the use §4a made of it.**  §4a's verdict on `AddInductStagesR` may well be right;
  what mattered was the elimination argument it fed, and that is refuted independently (§2a).  A
  machine-checked §4a is now bookkeeping, not a blocker.

## 8. What is left for the general discharge

`Verify/Inductive/ArgsTypedSupply.lean` §9 states this in the file; in brief, the `D.WF` route
rests on four coincidences, all four holding at both witnesses and none general:

1. the field must sit at declaration position `0`, or the prefix context is not `D.params.reverse`;
2. the foreign block must **have** a constructor field that is a bare parameter (a phantom
   parameter has none);
3. the recogniser must fire — a **block-free** spine argument (`List (Nat × NTree α)`'s `Nat`
   position) lands in `pos`'s `none` branch, which gives only `IsDefEqType F.type A` for some
   block-free `A`;
4. `D.lvl` must be the parameter's sort level; `VIndType.WF.canon` only makes it `isEquiv` to each
   member's result level.

**And one environment gap, which is the sharpest single residual.**  `WF.ctors` is staged at
`env.addIndTypes D`, which declares the **companions**; §8.7 consumes `hargs` at
`AddInductStagesR`'s second stage, which does not.  The two are incomparable.  Nothing in the
*statement* obstructs a transport — `RestoreData.args` / `OccursN.args_noNested` say the spine is
free of `_nested` names — but a **restriction lemma** ("a derivation whose subject avoids the
companion names can be replayed in an environment without them") is missing.  That one lemma is what
would turn §5 into a general route rather than a two-witness one.

If instead the clause is to be a hypothesis, the edit is one clause on `TrIndDeclN`
(`Verify/Environment/InductR.lean`), staged exactly as `trCtors` is, stated for the companion tail:
`VInductDecl'.ArgsTypedK` restated over `R` rather than over `occ` (interchangeable by
`hargs_of_argsTypedK`).  `TrIndDeclN` is a **hypothesis** relation, so a new conjunct needs the
consumer audit `Verify/Inductive/TrIndDeclNCtorOwn.lean` established the pattern for.  **I did not
make that edit**: `InductR.lean` is not mine, and the flip is yours to sequence.

## 9. Pick up first

1. **The restriction lemma** in §8 — it is the whole distance between §5's two witnesses and a
   general discharge, and it is a statement about `VEnv` alone, with no nested vocabulary in it.
2. **Instantiate the `D.WF` route at a third block** where coincidence 3 fails: a nested occurrence
   with a **block-free** spine argument, e.g. `List (Nat × NTree α)`.  My prediction is that the
   `none` branch gives `IsDefEqType`, hence a typing at *some* sort, and that the level then has to
   come from `VIndType.WF.canon` — that would extend the route to the second of the four
   coincidences and is the cheapest next measurement.
3. **`ParamRedex.lean`'s `mpAux mpAuxNodeB`** is still the untried third witness
   (`docs/handoff-hargsshared.md` §7 item 3); `mp_hargs` is already `ArgsTypedH.ty` there under one
   lookup hypothesis, and my `pfnOcc_argsTypedH_of_hasType` / `listOcc_argsTypedH_of_hasType` are
   the shape it would plug into.
4. **Do not** close `tryEtaStructCore.WF` / `isDefEqUnitLike.WF` (row 197), and **do not** make the
   flip: the general discharge is not achieved and the census is still 13.

## 10. Verification record

* `lake build Lean4Lean.Verify.Inductive.ArgsTypedSupply`: **197 jobs**, exit 0, no warnings from my
  file.  **54 declarations, 47 `#print axioms` lines, zero `sorryAx`**; every `#print axioms` name read off the file's own
  `namespace` lines, never composed from the path.
* `lake env lean --run scripts/sorry-census-all.lean`: **13 holes**; `BUILT: 398`; **`in population
  but NOT BUILT: 0`**.  My file adds **no** holes and is an orphan module (imported by nothing), as
  a new leaf should be.
* Full `lake build`: **1581 jobs, exit 0, zero `error:` lines.**  (Three concurrent streams' files —
  `Theory/Typing/ShapeIndep.lean`, `Theory/Typing/ConstSubstNested.lean`,
  `Theory/Inductive/NestedTele.lean` — were transiently broken or missing their `.olean` during my
  session, at one point taking the census's `NOT BUILT` to 1; all three recovered, and I rebuilt
  before every probe.  Reported because "`lake build` exit 1" was **not** evidence about my source
  in any of the three cases.)
* `lake env lean --run scripts/dup-names.lean`: "no duplicate Lean4Lean declarations across the
  joined cone".
* Layering: `grep -rln "^import Lean4Lean.Verify" Lean4Lean/Theory/` is empty; my file is under
  `Verify/` and imports one `Theory` module (`Theory.Inductive.HargsShared`) plus three `Verify`
  ones.
* Frozen files: not read for editing, not written, not `touch`ed; absent from `git status`.
* Other streams' files (`HargsShared.lean`, `SpineTransfer.lean`, `NestedOccData.lean`,
  `OccArgsTyping.lean`, `NestedRestore.lean`, `InductR.lean`, `NestedBuild.lean`,
  `ConstSubstNested.lean`): read and imported, never edited.
* No state-changing `git`, no `lake update`, nothing sent outside this repo.

### 10a. Measured vs read off

**Measured this session:** every axiom line, per declaration, from the build output; that
`OccData`'s six fields transport verbatim under an arbitrary spine change (Lean accepted the
transport — this is the measurement, not a reading of the definition); that `RestoreData` mentions
the spine in exactly one field (same method); the `D.WF` extraction at **both** witnesses, including
`pfnAuxMk.fields[0]?` and `(⟨[],0,[]⟩ : VIndRecArg).canonResult` by `rfl`; the syntactic telescope
agreements by `decide`; that `nfnAux_WF` is unconditional (`#check @nfnAux_WF`); every witness and
`decide` in §5; the census (13 holes, BUILT 398, NOT BUILT 0); dup-names; the
layering check; the job count.

**Read off source, not independently proved:** that `RestoreData` has fourteen fields and `OccData`
six (counted by hand from their definitions, and consistent with `NestedRestoreWit.lean`'s own
"all fourteen"); `AddIndConsts`' clause list and hence §7's first bullet (a reading of
`Verify/Environment/Basic.lean:221`, not a theorem — this is the same kind of reading
`docs/handoff-hargsshared.md` §4a made, and I flag it as such rather than repeating its mistake);
`IsDefEqU.forallE_inv`'s `sorry` status (read from `Theory/Typing/Injectivity.lean`'s warning line);
the brief's `Inductive/Add.lean:1121` pointer, **not** checked.
