# Handoff: `hargs`, once, for all three obligations (`HargsShared`)

**Written 2026-09-03.**  One file, mine, new:
`Lean4Lean/Theory/Inductive/HargsShared.lean` (733 lines, **80 jobs**, exit 0).
Nothing else was created or edited.  Frozen files not read for editing, not written, not
`touch`ed.  **The flip was not made** and is not available.

Target, as given: *"where `AddInductStagesR` supplies §8.7's `hsplit`/`hargs`.  That discharges
§7's `hbeta`, (B)'s blocks, and (C)'s `IotaHargs` together."*  I was told to treat that as a
stream's claim, not fact.  **Half of it is refuted and half is proved**, and the refuted half is
the more useful of the two.

## 0. Grading discipline

Every `#print axioms` line below is **hole-freeness and nothing else** (`docs/vacuity-ledger.md`
§0, rows 195/199b/205).  Inhabitation is asserted separately and only where §5 checks it.  Two
declarations in this file carry `sorryAx` and I say which and why (§3).  **This file is a
reduction of four residuals to one, not a discharge**; the remaining datum is named in §4.

## 1. Headline, in four claims

| # | claim | grade |
|---|---|---|
| 1 | **§8.7's `hsplit` is FREE** — a hypothesis-free one-liner, for **both** heads.  A stated negative in the tree (`NestedTele.lean` §T12: "for the type head that cannot be proved") is **refuted**, and ledger row 74b's asymmetry is about a different proposition | **proved**, `[propext]` |
| 2 | The four `hbody`/`hargs` sites of (A), (B), (C) and §8.7 are **one datum**, transported by two lemmas that already existed | **proved**, hole-free |
| 3 | That datum's home is a clause on `VNestedOcc`, and `Built` + that clause gives it at **every** presented head | **proved**, hole-free |
| 4 | **`AddInductStagesR` does not supply it** | measured on the *definition*, plus a machine-checked half (§3c); flagged below as what it is |

## 2. Claim 1: `hsplit` is free — a refuted negative

`VIndRestore.tyVal_hasType_of_faithful` (`Theory/Inductive/NestedRules.lean:1549`) takes

    hsplit : ∀ ci, env.constants (R.tyName j) = some ci →
      ci.type.instL (R.tyLvls j)
        = mkPi (splitPis (npJ j) (ci.type.instL (R.tyLvls j))).1
               (splitPis (npJ j) (ci.type.instL (R.tyLvls j))).2

`VExpr.mkPi_splitPis` (`Theory/Inductive/NestedBuild.lean:118`) says
`mkPi (splitPis n e).1 (splitPis n e).2 = e` at **every** `n` and **every** `e`.  So `hsplit` is
`(mkPi_splitPis _ _).symm`: `VIndRestore.hsplit_free`, arity 3, **`[propext]`**, no hypotheses,
no `Faithful`, no environment.

**Stated precisely, because the tree's negative is about a different sentence.**
`NestedTele.lean` §T12 ("And the ctor head's `hsplit` is a theorem too — the asymmetry with the
type head", `:1169–1177`) and `docs/vacuity-ledger.md` row 74b both say `hsplit` is derivable for
the constructor head (F2, `VIndCtor.splitPis_type_instL`) and **not** for the type head (F1).
What is not derivable is *"the presented head's type has `npJ j` leading pis syntactically"*,
i.e. `(splitPis (npJ j) X).1.length = npJ j`.  That is **not** what `hsplit` says: `splitPis`
truncates silently, and `hsplit` compares `X` with the re-assembly of whatever it produced.  The
truncated case smuggles nothing, because `hargs` is stated against the *same* truncated telescope
(so it then forces a correspondingly short spine) and `Faithful.ty_agree`'s `instAt` uses the same
`splitPis`.  So the strong sentence is never needed, and `hsplit` is dead weight.

Consequences, each of which I checked:

* **§8.7 has one residual, not two.**  `VIndRestore.tyVal_hasType_of_hargs` is
  `tyVal_hasType_of_faithful` with `hsplit` discharged: `[propext, Quot.sound]`, hole-free.
* `ParamRedex.lean`'s `mp_hsplit` (`:661`) was not needed; nor was
  `VIndCtor.splitPis_type_instL` for this purpose.
* This is ledger §0's **failure kind 4** ("a negative asserted as established"), which the ledger
  itself calls the expensive kind because it stops people looking.  `mkPi_splitPis` had **one**
  user in the tree (`NestedBuild.lean:169`) and none in the nested-restoration corner — a
  zero-user ingredient two files away from the statement it discharges.
* `tyVal_hasType_of_faithful` itself had **zero users** before this file (measured: every other
  occurrence of the name in the tree is prose).

## 3. Claim 2: one datum, four sites

### 3a. The datum

    def VIndRestore.HeadApp (R) (n : Name) (j : Nat) : VExpr :=
      (VExpr.const n (R.tyLvls j)).mkApp (R.tyArgs j)

    def VIndRestore.SpineTypedAt (R) (D) (e : VEnv) (n : Name) (j : Nat) (B : VExpr) : Prop :=
      e.HasType D.uvars D.params.reverse (R.HeadApp n j) B

`R.tyBody D j = R.HeadApp (R.tyName j) j` and `R.ctorBody D j C = R.HeadApp (R.ctorName C.name) j`,
both `rfl`.  Note **`e`, not `env`**: see §3c.

### 3b. The four sites, and the two transports

| site | obligation | how it is reached |
|---|---|---|
| `MotiveHargs`' head typing | (B), and (C) via `iotaCtx_teleDefEq`'s `hmot` | `spineTypedAt_atRec` — `VInductDecl'.atRec_hasType`, existing |
| `MinorCtorHargs`' head typing | (B), and (C) via `hmin` | the same lemma, at the constructor head |
| §8.8's `hbody` at `D.params.reverse ++ Γ` | (A) | `spineTypedAt_append` — `VEnv.IsDefEq.weakR`, existing |
| §8.7's `hargs` | the `val` clause of `(R.csubst D K).WF`, i.e. (B)/(C)'s `hσ` | `spineTypedAt_of_hargs` / `hargs_of_spineTyped` |

Two decomposition theorems make "how much of the bundle is the shared datum" checkable rather
than asserted:

    VIndRestore.motiveHargs_iff     : MotiveHargs     ↔ ∃ B, (head typing at B) ∧ MotiveShape … B
    VIndRestore.minorCtorHargs_iff  : MinorCtorHargs  ↔ ∃ B, (head typing at B) ∧ MinorCtorShape … B

both `[propext]`.  **Measured, not read off**: `MotiveShape` and `MinorCtorShape` do not mention
`R` at all — Lean rejected `R.MotiveShape` as having no `VIndRestore` parameter — so the
restoration enters (B)'s bundles *only* through the shared datum and through `σ`.  That is the
sharpest form of "the three obligations share one datum" I could find: one conjunct of four in
each bundle, the same conjunct in both, and the rest is `R`-free.

Producers: `motiveHargs_of_spineTypedAt`, `minorCtorHargs_of_spineTypedAt`,
`substC_tyApp_defeq_tyAppR_of_spineTypedAt` (§8.8 with `hbody` replaced),
`tyVal_hasType_of_hargs` (§8.7 with `hsplit` gone).  All `[propext, Quot.sound]`.

### 3c. Two boundaries, both of which change how the datum must be supplied

**(i) The datum is FALSE at the pre-block environment.**
`InductiveDeclExamples.ntree_not_spineTyped_pre` (`[propext, Classical.choice, Quot.sound]`,
hole-free): at `ntreeAux`, `¬ ntreeRestore.SpineTyped ntreeAux env₁ ``List`` 1`, because the
presented spine is `List.{u} (NTree.{u} #0)` and `NTree` is a constant the **step declares**
(`VEnv.IsDefEq.constsIn` + `env₁.constants ``NTree = none`).  So any account of the datum that
reads it off the pre-block environment is refuted at a real parameterised nested block.  This is
also *why* §8.7 states `hargs` at `e₂` and the lookup at `env`; I had to correct my own first
draft, which put the datum at `env`.

**(ii) The applied form costs the `PiInv` hole; the `HasArgs` form does not.**
`hargs_of_spineTyped` and `tyVal_hasType_of_spineTyped` carry **`sorryAx`**
(`[propext, sorryAx, Classical.choice, Quot.sound]`), through `VEnv.HasArgs.of_mkApp`
(`Theory/Typing/SpineInv.lean`, whose own docstring says "this is *not* `sorry`-free: it uses
`IsDefEqU.forallE_inv`").  The forward direction `spineTypedAt_of_hargs` is hole-free.

This is worse than a hole count.  `NestedTele.lean` §T12's "the `PiInv` line" and §T15/§T16's
repeated *"nothing here uses `HasArgs.of_mkApp'`, so the whole cone stays `PiInv`-free"* are a
deliberate invariant of the nested corner; `hargs_of_spineTyped` is the **first** use of
`HasArgs.of_mkApp` in it (measured: the unprimed lemma had exactly two users, both in
`Verify/Typing/Proj*`).  **So the datum must be supplied in `HasArgs` form**, and §8b of the file
does that: `VNestedOcc.ArgsTypedH` plus `ArgsTypedH.toArgsTyped`, both hole-free.  Supplying it in
applied form would put the whole nested corner behind `VEnv.WF` and `PiInv`.

I would have missed this if I had only read axiom lines at the end; it showed up because §10
prints axioms per declaration rather than for the file.

## 4. Claim 3: where the datum comes from — and claim 4: not from `AddInductStagesR`

### 4a. Refuted: `AddInductStagesR`

Read off the definition (`Verify/Environment/InductR.lean:102`), **not** proved — I cannot state
it, because `AddInductStagesR` is in `Verify/` and my file is in `Theory/` (the layering rule):

    AddInductStagesR m₁ env₁ D K R m₂ env₂ :=
      ∃ …, AddIndConsts (IndShapeOf …) (D.typeConstsC K) … ∧
           AddIndConsts (CtorShapeOf …) (D.ctorConstsCR R K) … ∧
           AddIndConsts (…recInfo…)     (D.recConstsR R K)  … ∧
           env₂ = e₃.addIndRulesR D K R

and `AddIndConsts`' `cons` (`Verify/Environment/Basic.lean:221`) carries `ci.name = n`, `S ci`,
`TrConstant .safe env ci ci'`, `m.find? n = none`, `env.addConst n ci' = some env₁`.  **There is
no typing judgement anywhere in it**: `TrConstant` is a translation relation between an `Expr`
`ConstantInfo` and a `VConstant`, and `VEnv.addConst` checks only name freshness.  Obligations
(A) and (B) *are* the `VConstant.WF` statements that `AddInductStagesR` deliberately does not
make.  So `AddInductStagesR` cannot supply a typing judgement about `R.tyArgs j`, and the "pick up
first" I was handed is **refuted at the level of the definition**.

**The one-line `Verify`-side theorem that would settle it as a proof rather than a reading** —
I am not allowed to write it, so it is stated here for whoever owns `Verify/`:

    theorem addInductStagesR_no_spineTyped :
      ∃ m₁ env₁ D K R m₂ env₂, AddInductStagesR m₁ env₁ D K R m₂ env₂ ∧
        ¬ ∃ B, env₂.HasType D.uvars D.params.reverse (R.HeadApp (R.tyName j) j) B

I did not attempt it (it needs a junk-spine `Expr`-side witness) and I flag the §4a verdict as
**a reading of a definition, not a theorem**.

What `InductStepNested` (`InductR.lean:481`) carries besides `AddInductStagesR` is
`TrIndDeclN venv lp np types false numNested D K R`, `∃ et, venv.addIndTypes D = some et`, and
`D.WF venv`.  `D.WF venv` **cannot** supply the datum either, and that is already a theorem:
`VIndRestore.instAt_indep_of_tyArgs` (`NestedRules.lean`) shows the companion member's stored type
is blind to the presented spine when the split body is closed.  By elimination the source is
`TrIndDeclN` — the `Expr`-side occurrence — which is exactly where §4b puts it.

### 4b. Proved: the clause belongs on the occurrence record

`VInductDecl'.Built` (`Theory/Inductive/NestedBuild.lean`) is the only structure in `Theory/` that
pins `R.tyArgs`: `Built.tyArgs` says `R.tyArgs j = (occ j).args`.  So:

    structure VNestedOcc.ArgsTypedH (N) (D) (e : VEnv) : Prop where
      lvls : ∀ l ∈ N.lvls, l.WF D.uvars
      ty   : e.HasArgs D.uvars D.params.reverse
               (splitPis N.decl.np (N.src.type.instL N.lvls)).1 N.args
      ctor : ∀ C ∈ N.src.ctors, e.HasArgs D.uvars D.params.reverse
               (splitPis N.decl.np ((C.type N.decl N.idx).instL N.lvls)).1 N.args

`ArgsTypedH.toArgsTyped` descends it (hole-free) using only `Occurs.ty_const`,
`Occurs.ctor_const` and `Occurs.lvls_len`; then

    VInductDecl'.Built.spineTyped_ty    : Built + the clause → the datum at the type head
    VInductDecl'.Built.spineTyped_ctor  : … and at every constructor head of the member

both `[propext, Quot.sound]`.  The constructor bridge is `Built.member` (the companion member's
constructor list *is* `J`'s, mapped) composed with `Built.ctorName_inv`, so the conclusion lands
at `R.ctorName C.name` — the form `MinorCtorHargs` consumes.

**Honest count: the datum is two, not one.**  The type head's telescope is `J`'s member's
parameter block, the constructor head's is that constructor's own `C.params`; F3
(`VIndCtor.WF.params_eq`) relates them only definitionally.  Collapsing the two into one would go
through `VEnv.HasArgs.congr_tele` — which the (B) stream named and a **concurrent stream owns**, so
I stayed off it.  Until that lands, `ArgsTypedH` has two clauses and I say so.

**Discharge site, named**: `ArgsTypedH` is a `Theory`-level clause about `VNestedOcc`; the
`Verify`-side obligation is to produce it in `ElimNestedInductive.Result.RestoreData` /
`TrIndDeclN`, from the typing of the occurrence in the source constructor type — the same place
`OccursN.args_noNested` is discharged (`Verify/Inductive/NestedRestore.lean`,
`RestoreData.mkRestore_built_of_spine`).  Nothing in this file proves it.

## 5. Inhabitation, stated separately from hole-freeness

At `ntreeAux` — `NTree α` with a `List (NTree α)` field, `D.np = 1`, `Canonical`, the block Lean's
own kernel runs the nested elimination on.

* `ntree_spineTypedAt_ty` — the datum at the **type** head, at `F₂`;
* `ntree_spineTyped_nil`, `ntree_spineTyped_cons` — at both **constructor** heads;
* `ntree_listOcc_argsTypedH` — §4b's clause in `HasArgs` form, all three components at one
  environment (so the clause's own hypothesis set is **jointly** inhabited, ledger row 205);
* `ntree_listOcc_argsTyped_of_H` — and its hole-free descent;
* **`ntree_datum_of_built`** — `ntreeAux_built` **and** the clause, both at `ntreeAux`, run through
  §4b's producer.  This is the joint check: the two hypothesis families of `Built.spineTyped_ty`
  hold simultaneously at one block with one `D`, one `R`, one `occ`, one staging;
* `ntree_datum_of_built_ctor` — the same at every constructor head;
* `ntree_headTyped_atRec` — §3b's transport **firing**: the datum, stated once at
  `ntreeAux.uvars = 1` over the parameter telescope, arrives at `ntreeAux.recUvars = 2` over
  `(ntreeAux.atRecTele ntreeAux.params).reverse`, the context `MotiveHargs`/`MinorCtorHargs` bind
  their head typing in;
* `ntree_spineTypedAt_ty_inhabited` — with the staging equations **supplied** by
  `ntree_stage₂_exists` rather than assumed, so there is a hypothesis-free existential form.

All `[propext, Quot.sound]`.

### 5a. Non-degeneracy, `decide`-checked

* `ntree_np_pos : 0 < ntreeAux.np` — not the `D.np = 0` statement;
* `ntree_tyArgs_ne_nil` — the spine is not `[]`, so §3b's `HasArgs` is not `.nil`;
* `ntree_tyArgs_ne_bvars` — the presentation is **not** the identity one, so this is not
  `VInductDecl'.idRestore` in disguise;
* `ntree_tyName_ne_own` — the presented head is a **foreign** constant, not the block's own member.

### 5b. What is NOT established

* No witness for the datum at any block other than `ntreeAux`.  I did **not** instantiate at
  `mpAux mpAuxNodeB` (`ParamRedex.lean`), although `mp_hargs` (`:672`) is already the datum's
  `HasArgs` form there, under one lookup hypothesis — see §7 item 3.
* `MotiveShape` / `MinorCtorShape` — the residuals §3b leaves — are **not** inhabited here at any
  block.  They are §T10/§T12.1's `hpi`/`hAs`/`hsort`/`hfun`, another stream's.
* Nothing here produces `ArgsTypedH` in general.  §4a's elimination argument says the source is
  `TrIndDeclN`; that is an argument, not a proof.

## 6. Corrections to what I was relayed and to the documents

Each checked by me.

1. **"where `AddInductStagesR` supplies §8.7's `hsplit`/`hargs`" — refuted for `hargs`** (§4a:
   `AddInductStagesR` contains no typing judgement) **and vacuous for `hsplit`** (§2: `hsplit`
   needs no supplier).  The (A) stream's "pick up first" is the wrong door.
2. **`NestedTele.lean` §T12 (`:1169–1177`) asserts a negative that is false as the reader will
   take it**: "For the **type** head that cannot be proved … which is why `hsplit` is a hypothesis
   of `tyVal_hasType_of_faithful`".  `hsplit` as written is a tautology.  The sentence is true of
   the stronger *length* statement, which §8.7 does not use.  `docs/vacuity-ledger.md` row 74b
   repeats it.  **Not edited — neither file is mine.**
3. **The three streams' "same datum" is right, and I can now say how much is shared**: exactly one
   conjunct of four in each of (B)'s two bundles, and the bundles' other three conjuncts are
   `R`-free.  `docs/handoff-ctorbeta.md` §4 item 8 ("the two are now the *same* datum … whichever
   is done first should be done as a lemma about `hargs`") is confirmed, and extends to (C).
4. **`docs/handoff-iotahargs.md` §6's row for `hpiT`/`hsortT` ("shape facts", justified by "the
   companion's stored *type* is only definitionally canonical (F1), which is why §T10 says the
   ctor head's `hsplit` is a theorem and the type head's is not")** rests on the same mistaken
   reason.  The row's *classification* survives — `hpiT`/`hsortT` are still shape facts about the
   instantiated body — but the reason given is not the reason that holds.
5. **The orchestrator's `mpAuxB_hdata` / `mpAuxB_addInductR_ordered` correction reproduced**: both
   are at `ParamRedex.lean:2397` / `:2487`, and `ParamRedex.lean` builds.  I did not use them (§7).
6. **`FlipPriceScan.lean`'s import set**: I checked before trusting any absence.  It now imports
   `ParamRedex`; but I made no absence claim through it — my two absence claims (`mkPi_splitPis`
   users, `tyVal_hasType_of_faithful` users, `HasArgs.of_mkApp` users) are **greps**, and I label
   them as such.  They are name-occurrence counts over the whole tree with the declaration site and
   prose separated by hand, not structural queries; treat them as floors.
7. **A correction to myself, recorded because it is the shape of the errors the ledger tracks**: my
   first draft stated the datum over the *pre-block* environment `env`.  It is false there
   (§3c(i)), and I only found out by trying to instantiate it at `ntreeAux` and noticing `NTree` is
   not in `env₁`.  "Instantiate, don't admire" caught it, exactly as row 205 predicts.

## 7. Pick up first

1. **Supply `ArgsTypedH` on the `Verify/` side.**  That is now the whole remaining datum for
   §8.7, and one of four conjuncts for (B)/(C)'s bundles and (A)'s β-gap.  It is a `HasArgs` about
   the occurrence's spine over the block's parameters, at the post-step environment — i.e. exactly
   what `ElimNestedInductive` reads out of an already-typechecked constructor type.  **Supply it in
   `HasArgs` form, not applied form** (§3c(ii)): the applied form drags the nested corner behind
   `PiInv`.
2. **`ntree_not_spineTyped_pre` should be generalised**, and it is cheap: the argument is
   `IsDefEq.constsIn` plus "the presented spine mentions a name the step declares".  A general
   version would say *no* pre-block statement of the datum is available, at any block, which turns
   §4a's elimination argument into a theorem about half of the space.
3. **Instantiate at `mpAux mpAuxNodeB`** (`ParamRedex.lean`), the non-canonical parameterised redex
   block.  `mp_hargs` is already `ArgsTypedH.ty` there under one lookup hypothesis, and
   `mp_split_body_closed` shows that block is precisely the configuration
   `instAt_indep_of_tyArgs` names — so a second, structurally different inhabitation is close, and
   would separate a general route from one fitted to `ntreeAux`.  I ran out of session before it.
4. **`MotiveShape` / `MinorCtorShape` are now the *whole* residual of (B)** once the datum is
   supplied, and they are `R`-free.  That is a much smaller target than "(B)'s four data
   families", and it is the concurrent `HasArgs.congr_tele` stream's natural landing site.
5. **Do not** close `tryEtaStructCore.WF` / `isDefEqUnitLike.WF` (row 197), and **do not** make the
   flip: the datum is not discharged in general and the census is still 13.

## 8. Verification record

* `lake build Lean4Lean.Theory.Inductive.HargsShared`: **80 jobs**, exit 0, no warnings from my
  file.
* Full `lake build`: **1575 jobs**, exit 0, zero `error:` lines.
* `lake env lean --run scripts/sorry-census-all.lean`: **13 holes**; `BUILT: 392`;
  `in population but NOT BUILT: 0`.  My file is an orphan module (imported by nothing), as a new
  leaf should be, and adds **no** holes to the census — note that it *does* contain two
  `sorryAx`-carrying declarations (§3c(ii)), which the census does not count because they are not
  `sorry`s of their own; I report them here instead, which is the point of §0 of the ledger.
* `lake env lean --run scripts/dup-names.lean`: "no duplicate Lean4Lean declarations across the
  joined cone".
* Layering: `grep -rln "^import Lean4Lean.Verify" Lean4Lean/Theory/` is **empty**.  My file imports
  two modules, both `Theory` (`Theory.Inductive.RecTyped`, `Theory.Typing.SpineInv`).
* Frozen files (`Verify/Soundness.lean`, `Verify/Axioms.lean`, `Verify/Guard.lean`): not read for
  editing, not written, not `touch`ed; `git status` on all three is clean.
* Other streams' files (`Theory/Inductive/TeleCongr*`, `IotaWit*`, `RestoreBridge.lean`,
  `NestedTele.lean`, `CtorBeta*`, `RecTyped*`, `IotaHargsGen.lean`): read and imported, never
  edited.
* No state-changing `git`, no `lake update`, nothing sent outside this repo.

### 8a. Measured vs read off

**Measured by me this session:** every axiom line in this file (per declaration, from the build
output, names read off the file's own `namespace` and `#print axioms` lines); that
`hargs_of_spineTyped` and `tyVal_hasType_of_spineTyped` carry `sorryAx` and the other 29 do not;
`hsplit_free` at `[propext]`; that `MotiveShape`/`MinorCtorShape` do not mention `R` (Lean
rejected the dot notation); every witness and `decide` in §5; the census (13, NOT BUILT 0, BUILT
392); dup-names; the layering check; the job counts; that `tyVal_hasType_of_faithful` and
`mkPi_splitPis`-in-the-nested-corner had no users (grep, method stated in §6 item 6).

**Read off source or documents, not independently proved:** §4a's verdict on `AddInductStagesR`
(a reading of its definition and of `AddIndConsts`, not a theorem — flagged as such there);
`instAt_indep_of_tyArgs`' lower bound on `hargs` (read from `NestedRules.lean`); that (C)'s
`htele` `hmot`/`hmin` are `MotiveHargs`/`MinorCtorHargs` verbatim (read from `NestedTele.lean`
§T16's docstring via `docs/handoff-iotahargs.md` §6, **not** re-derived — so claim 2's coverage of
(C) is one link weaker than its coverage of (A) and (B)); `mp_hargs`' content at `mpAux` (read from
`ParamRedex.lean` §7, not instantiated).
