# Handoff: `VIndRestore.ValAt` — the `ty` half suffices, the cheap refutation is unavailable, and the `WFC` route is closed

**Written 2026-09-03.**  One file, mine, new: `Lean4Lean/Verify/Inductive/ValAtPrice.lean`
(548 lines, **22 declarations**, 22 `#print axioms` lines, all hole-free).  Nothing else was
created or edited.  Frozen files (`Verify/Soundness.lean`, `Verify/Axioms.lean`,
`Verify/Guard.lean`) were not read for editing, not written, not `touch`ed; they do not appear in
`git status`.  **The flip was not made.**  `ValAt` is **not** constructed in general — outcome 1
was not reached; what I have is outcome 2 plus two measurements, one of which closes the previous
round's biggest flagged unknown.

## 0. Grading discipline

Every `#print axioms` line is hole-freeness and nothing else (`docs/vacuity-ledger.md` §0);
inhabitation is §4 below and §7 of the file.  **22 of 22 declarations are hole-free**
(`[]`, `[propext]`, `[propext, Quot.sound]`, or `+ Classical.choice`); the census is still **13**.
No `HasArgs.of_mkApp` anywhere in code (2 occurrences, both prose), so the corner's `PiInv`-free
invariant is intact.  `tryEtaStructCore.WF` / `isDefEqUnitLike.WF` (row 197) untouched.

## 1. Headline

| # | claim | grade |
|---|---|---|
| 1 | **`ValAt` from the datum's `ty` half alone**, at the target environment: one `HasArgs` per companion member, `ArgsTypedH`'s `ctor` family and `lvls` condition never mentioned (`VIndRestore.valAt_of_spineHargsK`, input named `VInductDecl'.SpineHargsK`) | **proved**, and **fired at the `NFn`/`PFn` witness**, existentially closed |
| 2 | **The brief's lead is measured and does not close it**: `Built.member` pins the spine into the built member's *stored type*, and `D.WF env`'s clauses about that type are staged at `env`, which forces them to be **`env`-clean** — so they are provably blind to a spine mentioning the block's own members.  `D.WF`'s only spine-typing clause is `ctors`, staged at `e₂` | **proved** (`builtMember_codomain_constsIn`, `WF.indices_constsIn`) |
| 3 | **The cheap refutation of the residual is provably unavailable.**  `not_argsTypedH_of_not_constsIn` kills the spine typing at the pre-block environment; at `e₁` its premise is **false**: the datum at `e₂` plus `KFresh.argsNoK` puts every spine argument's constants in `e₁`, because `e₂ \ e₁` **is** `K` | **proved** (`ArgsTypedK.args_constsIn`, `tyVal_constsIn`, obstruction stated as `not_valAt_of_not_constsIn`) |
| 4 | **The `WFC` route is closed, generally**: `D.WFC env K` forces **every companion member to have an empty constructor list**, hence (with `Built.member`) forces the *foreign* block to be constructor-free | **proved** (`WFC.companion_ctors_nil`, `WFC.nested_src_ctors_nil`) |
| 5 | …and it **bites at the tree's own nested witness**: `¬ nfnAux.WFC env₂ nfnK`, existentially closed | **proved** (`NestedWit.nfnAux_not_WFC`) |

## 2. Where the brief is wrong, or imprecise

**(a) "`ValAt` … is the fourth [field]" — right, but the shape of the remaining work was misstated
in one direction.**  The brief says *"`ValAt` at `e₁` is also weaker than the datum, so a cheap
general construction there is the one place not ruled out; look in `Built.member`."*  Both halves
need correction:

* `ValAt` **is** weaker than the datum, and §3 of my file sharpens exactly *how much* weaker: what
  a producer must carry is the datum's `ty` half at `e₁` and nothing else.  But **weaker does not
  mean cheaper here**: `SpineHargsK → ValAt` is proved, and `ValAt → SpineHargsK` is `of_mkApp`.
  So stating a checker-side clause in the weaker `ValAt` form (the previous round's
  recommendation, `docs/handoff-restrict.md` §5 item 1) leaves the producer with **no known
  general route to it**, because the one general producer, `tyVal_hasType_of_hargs`, consumes a
  `HasArgs`.  The cheaper *edit* is therefore not `ValAt` but `SpineHargsK`: one `HasArgs` per
  companion member at `addIndTypesC`-env.  **That is this round's concrete recommendation, and it
  supersedes the previous round's.**
* `Built.member` is **not** where a cheap construction hides, and the reason is structural rather
  than a failure to find it (§3 below).

**(b) "`Built.member` … pins the spine syntactically against the companion member."**  It pins the
spine into the built member's **stored type** — `member.type = mkPi D.params (instAll (splitPis np
(src.type.instL lvls)).2 args)` — and into its **index telescope**.  Both are constrained by
`D.WF env` only through clauses staged at **`env`** (`VIndType.WF.isType`, `VIndType.WF.indices`),
and `VEnv.Ordered.constsIn` forces anything typed at `env` to mention only `env`'s constants.  A
*nesting* spine mentions the block's own members, which `env` does not declare — that is exactly
`NestedWit.pfnOcc_not_argsTypedH_pre`'s content.  So for every configuration in which `D.WF env`
holds at all, the built member's type and indices are **spine-blind**, and the pin carries no
typing information.  What is left is `VInductDecl'.WF.ctors`, staged at `e₂`, which *does* type the
spine in general (`WF.recField_canonResult`) — one environment too high.  **That is the whole
residual, and it is a restriction step, not a missing construction.**

**(c) A consequence of (b) worth flagging as a possible defect elsewhere, not proved here.**  If a
nested block's *foreign* member has an index whose type depends on a foreign **parameter**, then
`member.indices = instAllTele (src.indices.map (·.instL lvls)) args 0` **mentions the spine**, and
`WF.indices_constsIn` then forces the spine to be `env`-clean — which a nesting spine is not.  So
`D.WF env` looks **unsatisfiable** for that class of nested declarations, and the same argument
applies to `WF.isType` when the foreign member's post-parameter codomain depends on a parameter.  I
did **not** build a witness and I do **not** claim it; the general half is machine-checked
(`WF.indices_constsIn`), the instantiation is not.  If it is real it is a staging defect in
`VInductDecl'.WF` (`Theory/Inductive/Decl.lean`), and it matters for CLAUDE.md's "full Lean type
theory, nested declarations included".  Whoever owns `Decl.lean`'s staging should check it.

**(d) The previous round's flagged unknown, now closed — and it was right.**
`docs/handoff-restrict.md` §6a listed as *read off, not checked*: "`VInductDecl'.WFC` is unavailable
on the nested path … if it is wrong then `WFC` is a third route and a much shorter one."  It is
right, and generally so (§4 of my file): a constructor's `result` clause types the member-headed
application `C.canonResult D j`, whose head is the member's own name, and a companion's name is by
construction absent from `addIndTypesC`-env.  So `D.WFC env K` ⟹ every companion member has
`ctors = []`.  There is **no third route**.  The theorem is sharp rather than vacuous:
`fooComp_WFC` (`CompanionResolve.lean` §7, read off) satisfies `WFC` at a companion with
`ctors = []`, which is exactly the case my theorem leaves open, and `nfnAux_not_WFC` refutes the
nested case outright.

**(e) Not verified by me:** that the datum at `e₂` is available in general (I use it as a
hypothesis; `WF.recField_canonResult` plus a structural condition on the foreign block's
constructors is the general route, and both tree witnesses satisfy it — I did not state that
condition); §8.7's other three sites; anything about `Inductive/Add.lean`.

## 3. What is proved, section by section

* **§1** two library gaps filled: `VExpr.constsIn_mkLams_body`, `constsIn_mkPi_body` (the `mkLams`
  and `mkPi`-body inverses `ProjNoNested.lean` §1.1 lacked) and `ConstsIn.and_noConsts` — the
  intersection of the two freshness vocabularies (`ConstsIn` at a predicate, `NoConsts` at a list).
  Plus `ctxConstsIn_mem`.
* **§2** the two stagings at the level of **names**, in the direction `RestrictCompanion.lean` §2
  does not cover: `VEnv.contains_addIndTypesC_of_addIndTypes` (a name `e₂` declares and `K` does not
  name is declared by `e₁`) and `VEnv.not_contains_addIndTypesC` (a `K`-name is absent from `e₁`).
  Together: **`e₂ \ e₁` is exactly `K`.**
* **§3** `VInductDecl'.SpineHargsK` (the datum's `ty` half, over the companion members),
  `SpineHargsK.of_argsTypedK`, `VIndRestore.hargs_of_spineHargsK`, and
  **`VIndRestore.valAt_of_spineHargsK`** — `ValAt` from it.  §3a is the collapse test: at `K = []`
  both sides are vacuous, so the content lives at `K ≠ []`, which both witnesses satisfy.
* **§4** `builtMember_codomain_constsIn`, `WF.indices_constsIn` — the spine-blindness of `D.WF`'s
  `env`-staged clauses.
* **§5** `not_valAt_of_not_constsIn` (the obstruction, general: no block, no `Built`),
  `ArgsTypedK.args_constsIn`, `VIndRestore.tyVal_constsIn` (its premise is false at `e₁`).
* **§6** `WFC.companion_ctors_nil`, `WFC.nested_src_ctors_nil`, and §6a `nfnAux_not_WFC`.
* **§7** inhabitation, by instantiation (see §4 here).

## 4. Inhabitation, stated separately from hole-freeness

* **§3's producer fires**: `NestedWit.nfnAux_valAt_of_spineHargsK` — `∃ env₂ E₁ F₁`, the three
  staging equations, `SpineHargsK` at `F₁`, and `ValAt` at `(E₁, F₁)`.  Closed, nothing
  hypothesised.  (`ArgsTypedSupply.lean` §10's `nfnAux_tyVal_hasType` closes the same clause from
  the *whole* datum; the point is that the smaller input suffices at a real witness.)
* **§5's theorem fires**: `NestedWit.nfnAux_tyVal_constsIn`, closed.  At this witness the
  conclusion is also directly checkable (the value is `PFn NFn`; `F₁` declares both), which makes
  it a test of the general theorem rather than only a use of it.
* **§6 fires as a refutation**: `nfnAux_not_WFC`, closed.  Used contrapositively, so vacuity of its
  hypothesis set would not matter; it is not vacuous anyway (`fooComp_WFC`, read off).
* **Degeneracy, reported**: `nfnAux` has `uvars = 0`, `params = []`, so §5's `hΓ`/`hp` hypotheses
  are `trivial` at that witness.  I did **not** instantiate §3 or §5 at the parameterised block
  (`ntreeAux`, `np = 1`, `uvars = 1`), where those two have content.  `K ≠ []` at both.
* **What is NOT inhabited here**: `SpineHargsK` (equivalently `ValAt`) at `e₁` for a *general*
  block, independently of the datum.  At both tree witnesses it comes from the block's own member
  constants being declared at `e₁` (`nfnF₁_nfn`, and the `NTree` analogue), which is
  witness-specific reasoning: the spine is `[NFn]` / `[NTree #0]` and its typing is one lookup.

## 5. Pick up first

1. **The residual, in its final shape**: `VInductDecl'.SpineHargsK D K e₁ occ` — for each companion
   member, **one `HasArgs`** stating that the presented spine instantiates the foreign member's
   parameter telescope, at `e₁ = env.addIndTypesC D K`.  `valAt_of_spineHargsK` +
   `csubstTy_WF_of_val` + `ArgsTypedK.restrict_of_val` turn it into the whole nested transport.
   **State the `TrIndDeclN` / `RestoreData` clause in this form**, not as `ValAt` (§2(a)): the
   checker really does have it, because the spine is a subterm of a constructor type the kernel
   type-checked.
2. **Two doors, and only two** (unchanged in kind, sharper in content): (i) a producer at `e₁` on
   the checker side, as in 1; (ii) restricting the *same* `HasArgs` from `e₂` — where `D.WF`
   supplies it — down to `e₁`, which is `RestrictCompanion.lean` §3's sandwich and, unconditionally,
   the strengthening hole.  §5 of my file is evidence the second door's statement is **true**: the
   constant-level obstruction to it is provably absent, so only a proof is missing.  **Do not**
   spend a round trying to refute the residual by constant-counting; that is now closed.
3. **Do not** try `WFC` (§6): closed, generally.
4. **Possible defect for `Decl.lean`'s owner**: §2(c) — `VInductDecl'.WF`'s `types` clause is staged
   at `env`, which may make it unsatisfiable for nesting through a foreign block with a
   parameter-dependent index type.  General half machine-checked, instantiation not attempted.
5. **Do not** close `tryEtaStructCore.WF` / `isDefEqUnitLike.WF`, and do not make the flip.

## 6. Verification record

* `lake build`: **1595 jobs, exit 0, zero `error:` lines**.  (Earlier in the round the tree was
  briefly red on `Theory.Inductive.FamInhabNTree`, another stream's file; it was green by the end.
  My file is an orphan leaf, imported by nothing.)
* `lake build Lean4Lean.Verify.Inductive.ValAtPrice`: exit 0, 199 jobs, no warnings from my file.
* `lake build 2>&1 | grep -c "automatically included section variable"`: **1** on this
  (incremental) log, and it is `Foundation/FirstOrder/SetTheory/Z.lean`, i.e. upstream — **0 from
  my file**.  The count is not comparable with the baseline 18, which was measured on a log where
  more Lean4Lean modules were re-elaborated; the load-bearing part is that my file adds none.
* `lake env lean --run scripts/sorry-census-all.lean`: **13 holes**; `BUILT: 412`; **`in population
  but NOT BUILT: 0`**.  My file is in the population and adds no hole.
* `lake env lean --run scripts/dup-names.lean`: "no duplicate Lean4Lean declarations across the
  joined cone".
* Guards (`lake build Lean4Lean.Verify.Guard`): `guard 1 ✓ (24 frozen axioms)`,
  `guard 2 ✓ (whitelist; proof INCOMPLETE — sorryAx present, unchanged)`, `guard 3 ✓ (2/2)`.
* `#print axioms` names read off the file's own `namespace` lines, never composed from the path.
* Other streams' files read and imported, never edited: `RestrictCompanion.lean`,
  `ArgsTypedSupply.lean`, `ProjNoNested.lean`, `CompanionResolve.lean`, `HargsShared.lean`,
  `NestedBuild.lean`, `Decl.lean`, `Lemmas.lean`, `ConstSubst.lean`, `ConstSubstNested.lean`,
  `SpineTransfer.lean`, `OccArgsTyping.lean`, `Consts.lean`, `StrengthenAxiom.lean`.
* No state-changing `git`, no `lake update`, nothing sent outside this repo.

### 6a. Measured vs read off

**Measured this session:** every axiom line, per declaration, from the compiler; all of §§1–7 of my
file; that `VIndCtor.WF.onCtxAllFields` discharges §6's field-context side condition, so §6 has no
extra hypothesis; the census (13, BUILT 412, NOT BUILT 0); dup-names; the guards; the job count.

**Read off source, not independently proved:** that `fooComp_WFC` satisfies `WFC` at a companion
with `ctors = []` (from `CompanionResolve.lean` §7's statement, not re-derived); that
`VEnv.HasArgs.of_mkApp` is `sorryAx`-tainted (from `HargsShared.lean` §6's own docstring and
`docs/handoff-restrict.md`); that `WF.recField_canonResult` is the general route from `WF.ctors` to
a spine typing at `e₂` (from `ArgsTypedSupply.lean` §5.1's statement — I used neither).
