# Handoff: the restriction lemma — proved, priced, and not the producer

**Written 2026-09-03.**  One file, mine, new: `Lean4Lean/Verify/Inductive/RestrictCompanion.lean`
(764 lines, **32 declarations**, 29 `#print axioms` lines, exit 0, no warnings from my file).
Nothing else was created or edited.  Frozen files (`Verify/Soundness.lean`, `Verify/Axioms.lean`,
`Verify/Guard.lean`) were not read for editing, not written, not `touch`ed; they do not appear in
`git status`.  **The flip was not made** — the datum does *not* generalise (§2 below is the reason).

## 0. Grading discipline

Every `#print axioms` line in the file is **hole-freeness and nothing else**
(`docs/vacuity-ledger.md` §0).  Inhabitation is §4 here.  **30 of the 32 declarations are hole-free**
(`[propext]`, `[propext, Quot.sound]`, or `+ Classical.choice`).  The **two** that are `sorryAx`-
tainted are tainted *deliberately and are the measurement itself* — §3(d) — and my file adds **no
hole**: the census is still 13.  No `HasArgs.of_mkApp` anywhere in code (five occurrences, all in
prose), so the nested corner's `PiInv`-free invariant is intact.

## 1. Headline

| # | claim | grade |
|---|---|---|
| 1 | **The restriction lemma is PROVED** — general, hole-free, `of_mkApp`-free: `VEnv.IsDefEqU/HasType/HasArgs.restrictC`, and for the datum itself `VNestedOcc.ArgsTypedH.restrictC` / `VInductDecl'.ArgsTypedK.restrictC` | **proved** `[propext, Quot.sound]` |
| 2 | **…but it cannot be the datum's producer**: its hypothesis `σ.WF env₀ env₁ U` has a `val` field which at a companion member **is** §8.7's `val` clause at the *target* environment, i.e. the datum's own consequence there | **proved**, both halves (`restrictC_sandwich`) |
| 3 | **The two stagings are NOT incomparable**: `addIndTypesC`-env ≤ `addIndTypes`-env, so the transport factors as restrict-then-`mono` | **proved** (`addIndTypesC_le_addIndTypes`) |
| 4 | **The `VEnv`-only, hypothesis-free reading of the brief's lemma IS the open hole**: it is `AxiomConservativityWF`, equivalent to `StrengtheningTarget` = `IsDefEqU.weakN_iff`'s `sorry` | **proved** (re-export + the wiring) |
| 5 | **The whole general route is complete except one closed typing per companion member** (`VIndRestore.ValAt`), and that same clause **one environment up is free** | **proved** (`csubstTy_WF_of_val`, `ArgsTypedK.restrict_of_val`, `valAt_of_argsTypedK`) |
| 6 | The datum at `AddInductStagesR`'s **first stage** for the **parameterised** block (`NTree`/`List`), by the restriction — hypothesis-free | **proved** `[propext, Classical.choice, Quot.sound]` |

## 2. Where the brief is wrong

**(a) "That one `VEnv`-only lemma is the whole distance from two witnesses to a general route."**
Wrong in both halves, and the two errors point in opposite directions.

* The lemma is **not the distance**.  It is proved in twenty lines, because `Theory/` already had the
  transport: `VEnv.IsDefEq.substC` (`Theory/Typing/ConstSubst.lean`) is "the third way to move a
  judgement between environments, and the only one that can *remove* a constant", is hole-free, and
  composes with `VExpr.NoCSubst.substC_eq` to give exactly "a derivation whose subject avoids the
  dropped names replays without them".  What was missing was not a proof but the observation that
  `substC` is that transport.  And it was **already being used for the neighbouring obligation**:
  `Theory/Typing/ConstSubstNested.lean` fires `substC` to move a *constructor's* stored type across
  exactly these two environments (obligation (A) of `NestedOrdered.lean`).  So the previous round's
  §8 residual was stated as if no constant-removing transport existed while the file next door was
  using one on the same pair of environments.  Correcting the *attribution* matters because it is
  also what supplies §4's joint inhabitation.
* But proving it does **not** produce a general route.  `substC` needs `σ.WF env₀ env₁ U`, whose
  `val` field says the replacing value inhabits the dropped constant's declared type **in the target
  environment**.  At the nested step the substitution is `R.csubstTy D K`, its value at companion
  member `j` is `R.tyVal D j`, and the declared type is `T.type` — so the field reads
  `e₁.HasType D.uvars [] (R.tyVal D j) T.type`, which is *§8.7's own `val` clause at `e₁`*, and
  `ArgsTypedSupply.lean`'s `tyVal_hasType_of_argsTypedK` derives it **from the datum at `e₁`**.  A
  restriction lemma transports this datum; it cannot produce it.  That is the sandwich, and it is
  why the flip is not available.
* And the **hypothesis-free `VEnv`-only** reading — drop a constant with nothing assumed about its
  type — is `VEnv.AxiomConservativityWF`, which `Theory/Typing/ConstVar.lean` already proves is
  **equivalent to `StrengtheningTarget`**, the forward direction of `VEnv.IsDefEqU.weakN_iff` and a
  `sorry` of `Theory/Typing/UniqueTyping.lean`.  So that reading is not a small lemma: it is the
  tree's strengthening hole, and proving it would close `weakN_iff` as a corollary.

**(b) "Incomparable."**  True only of the **second** stage (it declares the constructor constants
and not the companions).  The **first** stage — `env.addIndTypesC D K`, which
`AddInductStagesR.addIndTypesC` produces — satisfies `addIndTypesC-env ≤ addIndTypes-env`
(`VEnv.addIndTypesC_le_addIndTypes`, proved).  So the transport is one-directional along a `≤`-chain:

    addIndTypes-env --restrict--> addIndTypesC-env --mono--> stage 2 --mono--> output

and only the first leg was missing.  It drops **constants only**: `addIndTypes` is an
`addConstList`, so it registers no defeq and the ι-rules arrive strictly later.  Calling the pair
"incomparable" hid the fact that a *single* `substC` step spans the gap.

**(c) "check that shape first: a derivation can mention a constant in a type without the subject
mentioning it".**  Right — and it is exactly why `ConstsIn`-style pruning fails and `substC`
succeeds (`substC` rewrites the whole derivation, types and `trans` middle terms included).  But the
shape is **already machine-checked upstream**: `VEnv.axiomConservativity_fires`
(`Theory/Typing/StrengthenAxiom.lean`) exhibits two `c`-free endpoints joined by a `trans` whose
middle term is not `c`-free.  So it is not a new refutation, and outcome 3 in the brief's sense does
not apply: the restriction is **not false as stated**.

**(d) The typed/untyped split, which the brief does not mention, and which prices the unconditional
route twice over.**  `AxiomConservativityWF` is about `IsDefEqU` — it *loses the type*.  The datum is
a `HasArgs`, i.e. typed.  Recovering the type costs `IsDefEq.uniqU`, and **`uniqU` and
`IsDefEqU.defeqDF` are both `sorryAx`-tainted** (measured this session), through the very hole
`AxiomConservativityWF` is equivalent to.  Hence my two deliberately tainted declarations,
`IsDefEq.restrict_of_conservativity` and `HasArgs.restrict_of_conservativity`: they are the machine-
checked statement that **a `PiInv`-free corner cannot use the unconditional route at all**, even
granting its hypothesis.  §1's `substC` route is hole-free throughout, and that is its one decisive
advantage.

**(e) Not verified:** I did not check the brief's characterisation of §8.7's four sites beyond the
`val` clause, and I make no claim about the other three.  I did not read `Inductive/Add.lean`.

## 3. What is proved, section by section

* **§1** `restrictC` for `IsDefEqU`, `HasType`, `HasArgs`, and for `ArgsTypedH`/`ArgsTypedK`.  The
  telescope is *carried*, never inverted.
* **§2** `addIndTypesC_le_addIndTypes` (+ `mem_typeConsts_of_mem_typeConstsC`).
* **§3** `CSubst.WF.val_hasType`, `restrictC_hypothesis_gives_val`, `restrictC_conclusion_gives_val`,
  `restrictC_sandwich`.  Stated as a **sandwich, not a circle**: the datum implies the `val` clause
  outright, the converse would need `of_mkApp`, so no claim of equivalence is made.
* **§4** the unconditional route: untyped form (hole-free wiring), typed form (tainted, deliberately),
  `restrict_unconditional_iff_target`.
* **§6/§7** the datum's restriction with its side conditions discharged: three of the four
  `NoCSubst` conditions come from `Occurs` + `Ordered` + freshness (`VExpr.ConstsIn.noCSubst` is the
  new bridge between the two freshness vocabularies); only the **spine** condition is a hypothesis,
  and `RestoreData.args` / `OccursN.args_noNested` supply it in the tree.  So everything is
  concentrated in `σ.WF`, which is what makes §3 the whole price.
* **§8** `ntreeAux_argsTypedK_restrict` and `ntreeAux_datum_at_stage₁` — closed, nothing
  hypothesised.
* **§11** `VIndRestore.csubstTy_WF_of_val`: three of the substitution's four fields proved in
  general (closedness upstream; `const` by a case split on the two `addConstList`s using §2;
  `defeq` by `addConstList_defeqs` + `Ordered.noCSubstD`), the fourth taken as the named residual
  `VIndRestore.ValAt`.  Then `ArgsTypedK.restrict_of_val` (the general route under the residual) and
  `valAt_of_argsTypedK` (the same clause at the larger environment is free).
  **§11b is the collapse test**: at `K = []` the substitution is the identity and both sides of the
  transport are vacuous, so all of §11's content lives at `K ≠ []`.

## 4. Inhabitation, stated separately from hole-freeness

* **`ntreeAux_datum_at_stage₁`** is closed: `∃ env₁ env₂ env₃`, the two stagings, `env₃ ≤ env₂`, and
  the datum at `env₃`.  `env₃ = env₁.addIndTypesC ntreeAux ntreeK` is `AddInductStagesR`'s **first**
  stage, i.e. where §8.7 wants it; `ArgsTypedSupply.lean` §10 had the `ntree` datum only at `env₂`.
  So the parameterised witness now joins `nfnAux` at stage 1, by the restriction rather than by hand.
* **The hypothesis set of §1 is jointly inhabited at both witnesses**, and not by me:
  `InductiveDeclExamples.nfnSubst_WF` and `ntreeSubst_WF` (`Theory/Typing/ConstSubstNested.lean`)
  supply `σ.WF` at exactly `addIndTypes`-env → `addConstList (typeConstsC …)`-env, for `np = 0` and
  `np = 1`.  `ntree_csubstTy` says `ntreeRestore.csubstTy ntreeAux ntreeK = ntreeSubst`, so it is the
  same substitution my general theorems are about.
* **Non-degeneracy**: `K ≠ []` at both witnesses, the substituted constant really is in the domain
  (`ntree_csubstTy_aux : … `_nested.List_1 = some ntreeVal`, upstream, `rfl`), and §11b is the
  measurement that at `K = []` the statements are inert.
* **What is NOT inhabited here**: `VIndRestore.ValAt D K e₂ e₁` at any block *independently of the
  datum*.  At both witnesses it follows from the `σ.WF` above (whose own `val` was discharged by
  `type_tac` on a concrete spine); in general it is the datum at `e₁`, which is the point of §3.
  I did **not** exhibit a third block, and I did not touch `MotiveShape` / `MinorCtorShape`.

## 5. Pick up first

1. **`VIndRestore.ValAt D K e₂ e₁` is now the entire residual of the nested transport** — one
   *closed* typing per companion member, subject and type both companion-free, no context, no
   spine, no telescope.  Two ways at it, and only these two:
   * a **producer at `e₁`**: `docs/handoff-argstyped.md` §9's `TrIndDeclN` clause, staged as
     `trCtors` is.  §3 is the argument it is not derivable from what is there; §1/§11 are now the
     transport it would compose with, so the clause could be stated in the *weaker* `ValAt` form
     (one closed typing) rather than as a `HasArgs` family — **that is a strictly cheaper edit than
     §9's, and it is the concrete recommendation of this round.**
   * a direct construction of `ValAt` at `e₁` for a general block, i.e. typing
     `mkLams D.params ((const tyName lvls).mkApp args)` at `∀ params, Sort u` in the smaller
     environment.  This is *weaker* than the datum (the converse needs `of_mkApp`), so it is not
     ruled out by §3 — it is the one place a cheaper general route could still hide.  Look for it in
     `Built.member`, which pins the spine syntactically against the companion member.
2. **Do not** attempt the unconditional restriction: §4 shows it is `weakN_iff`, and its typed form
   additionally needs `uniqU`, which is tainted by that same hole.  The `LiftTrim`/`StrengthenAxiom`
   stream owns that front.
3. **Do not** close `tryEtaStructCore.WF` / `isDefEqUnitLike.WF` (row 197), and **do not** make the
   flip: the datum does not generalise, and the census is still 13.

## 6. Verification record

* `lake build`: **1589 jobs, exit 0, zero `error:` lines.**  `Lean4Lean.Verify.Inductive.RestrictCompanion`
  builds in 1.4 s and is an orphan module (imported by nothing), as a new leaf should be.
* `lake build 2>&1 | grep -c "automatically included section variable"`: **18** (baseline 20); **0**
  of them from my file.
* `lake env lean --run scripts/sorry-census-all.lean`: **13 holes**; `BUILT: 406`; **`in population
  but NOT BUILT: 0`**.  My file adds no hole.
* `lake env lean --run scripts/dup-names.lean`: "no duplicate Lean4Lean declarations across the
  joined cone".  Two collisions were caught *during* the round and are recorded in the file rather
  than silently fixed: `VExpr.NoCSubst.splitPis` (already in `Theory/Inductive/NestedTele.lean`) and
  `VIndRestore.csubstTy_dom` (already in `Theory/Inductive/RestoreBridge.lean`, and its
  `csubstTy_eq_some` is what I ended up using).  Both were invisible to `grep` on my first pass and
  visible to Lean at the point of use.
* Guards: `guard 1 ✓ (24 frozen axioms)`, `guard 2 ✓ (whitelist; proof INCOMPLETE — sorryAx present,
  unchanged)`, `guard 3 ✓ (2/2)`.
* `#print axioms` names read off the file's own `namespace` lines, never composed from the path.
* Frozen files: not read for editing, not written, not `touch`ed; absent from `git status`.
* Other streams' files (`ConstSubst.lean`, `ConstSubstNested.lean`, `ConstVar.lean`,
  `StrengthenAxiom.lean`, `Strengthen.lean`, `RestoreBridge.lean`, `NestedTele.lean`,
  `ArgsTypedSupply.lean`, `InductR.lean`, `CompanionResolve.lean`): read and imported, never edited.
* No state-changing `git`, no `lake update`, nothing sent outside this repo.

### 6a. Measured vs read off

**Measured this session:** every axiom line, per declaration, from the compiler; that
`IsDefEq.uniqU` and `IsDefEqU.defeqDF` are `sorryAx`-tainted and `IsDefEq.substC`,
`IsDefEqU.strengthen_of_instN` and `axiomConservativityWF_iff_target` are not; the two name
collisions (by Lean, at the point of use); `addIndTypesC ≤ addIndTypes`; the whole of §§1–11; the
census (13, BUILT 406, NOT BUILT 0); dup-names; the section-variable count (18); the job count.

**Read off source, not independently proved:** that `StrengtheningTarget` is `weakN_iff`'s forward
direction (read from `Theory/Typing/Strengthen.lean`'s header and `UniqueTyping.lean:174`, not
re-derived); that `AddInductStagesR`'s second stage declares the constructor constants (read from
`Verify/Environment/InductR.lean`'s definition); that `VInductDecl'.WFC` is unavailable on the
nested path because a companion's constructor type is not well formed at `addIndTypesC`-env (read
from `InductR.lean` §4's own note — I did **not** check it, and if it is wrong then `WFC` is a third
route and a much shorter one); the claim that `nfnSubst_WF`'s and `ntreeSubst_WF`'s `val` clauses are
discharged "by `type_tac` on a concrete spine" (read from their proof text).
