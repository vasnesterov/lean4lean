import Lean4Lean.Theory.Typing.InjPiInhab
import Lean4Lean.Theory.Typing.DeltaUnique
import Lean4Lean.Theory.Typing.PatternRules

/-!
# `ConvPiFromEntry` is not provable over `Ordered env`, and the barrier claimed against the
rogue idiom on the Π side does not exist

`Theory/Typing/InjPiInhab.lean` §7 states the Π half of `ConvStep2` with no typing judgment in
it:

    ConvPiFromEntry :  CtxStrong env U (X::Γ) →
                       ConvC env U (X::Γ) X.lift (.forallE A B) →
                       ConvC env U (X::Γ) X.lift (.forallE A' B') → ConvC env U (A::X::Γ) B B'

and `piChainAt_bvar_iff_convPiFromEntry` makes it equivalent to `PiChainAt env U (.bvar 0)` over
`Ordered env`.  Every reduction in `InjMidLocal.lean`, `InjChainLower.lean` and `InjPiInhab.lean`
carries `Ordered env` and nothing stronger.  **At that strength the statement is false**, and
this file exhibits the environment.

## Two corrections, both machine-checked here

**1. The common source is free.**  `ConvPiInvCod.convPiFromEntry` is three lines and takes *no
hypothesis at all*: `ConvC` is symmetric and transitive unconditionally (`ConvC.symm`,
`ConvC.trans`, `BaseUniqChain.lean`), so two chains out of a common source compose into one
chain between the two Π's.  So `ConvPiFromEntry` is not a weakening of `ConvPiInvCod` in that
direction, and "two chains with a **common source**" is presentation, not strength.  The other
direction is `InjPiInhab.lean`'s own §2/§7 cycle (`Ordered env` plus the `.bvar 0` inhabitant).

**2. `InjChainLower.lean`'s `[analysis]` — "no rogue-environment refutation of `SortChainAt`,
`PiChainAt`, `ConvSortInv` or `ConvPiInvCod` is available by this idiom" — does not hold up on the two
Π-side entries.**  Precisely: the *argument* given there is invalid for them, and the idiom does
reach them.  The argument is a premise count: `IsDefEqStrong.extra`
(`Theory/Typing/Strong.lean:77`) has nine premises, five of them typings, and at `rogueSortEnv`
they demand `[] ⊢ .sort .zero : .sort (.succ (.succ .zero))`, which that environment does not
contain.  That argument is sound **for sort chains only**, where the level bookkeeping
(`.sort l : .sort (.succ l)`) forces the mismatch.  It says nothing about Π chains, and on the
Π side the premises are satisfiable with no anomaly whatever: a δ-shaped rule

    C ≡ ∀ (_ : Prop), Prop        at type   Sort 1

has both sides genuinely typed at `Sort 1` in the empty context, so all nine premises hold and
`IsDefEqStrong.extra` becomes a `ConvC` link.  `rogue_link1`, `rogue_link2` and `rogue_piPi`
below are that link, twice, plus the Π/Π chain they compose to — with **syntactically distinct
codomains** (`rogue_fires`), at an environment proved `Ordered` (`ordered_roguePiEnv`).

## The environment, and what `ConvPiFromEntry` forces at it

`roguePiEnv` declares one constant `C : Sort 1` and **two** definitional equations for it:

    rogueDf1 :  C ≡ ∀ (_ : Prop), Prop                    at  Sort 1
    rogueDf2 :  C ≡ ∀ (_ : Prop), ∀ (_ : Prop), Prop      at  Sort 1

`Ordered.defeq` asks only `df.WF env` — that both sides be typed at `df.type` in the empty
context — and both rules satisfy it, so `Ordered roguePiEnv` holds (`ordered_roguePiEnv`,
`sorryAx`-free).  Instantiating `ConvPiFromEntry` at `Γ = []`, `X = C` (so `X.lift = X`, `C`
being closed) with the two links as the two chains gives, by `convPiFromEntry_forces`:

    ConvC roguePiEnv 0 [Prop, C] Prop (∀ (_ : Prop), Prop)

i.e. `ConvPiFromEntry` at `roguePiEnv` forces a **sort/Π** conversion.  So:

    not_convPiFromEntry_of_convSortPiDisj :
      ConvSortPiDisj roguePiEnv 0 → ¬ ConvPiFromEntry roguePiEnv 0

and the same for `ConvPiInvCod`, `ConvPiInvCodInhab` and `PiChainAt … (.bvar 0)`.
`ConvSortPiDisj` is the `ConvC` form of `RigidSortPiDisj` = `IsDefEqU.sort_forallE_inv`, and
`SortPiDisjRaw.convSortPiDisj` derives it from the reference's typing-free judgment through
`InjMidLocal.ConvC.eq_or_raw` (unconditional).

**Read the bound honestly.**  This is not a completed refutation: `ConvSortPiDisj roguePiEnv 0`
is *not* proved here, and it cannot be, for a reason worth recording — see §"Why no refutation
is constructible" below.  What is proved is that the Π-side residual at `Ordered` strength is at
most **one instance of the other hole's one semantically-live conjunct** away from being false.
`RigidSortPiDisj` is not a part of `ConvPiFromEntry`; it is conjunct 3 of the five that
`RigidNodeCircle.rigidShapeUniqNS_iff_family` decomposes `WF.rigidShapeUniqNS` into, and
`InjSortPiModel.interp_sort_ne_interp_forallE` proves its *semantic* residual outright (the
packaging is what collapses there, not the content).  Nobody in this development doubts sort/Π
disjointness at a two-rule environment with no sort on either side of either rule.  So the
operational conclusion is not conditional:

> **Stop pointing proof attempts at `ConvPiFromEntry` over `Ordered env`.**  Any proof must
> consume `VEnv.WF`, and §7 names exactly which clause of it: `VEnv.RuleShape.delta` pins a
> δ-rule's lhs to `.const ci.name _` and `VEnv.addConst` refuses a duplicate name, so a
> `VEnv.WF` environment cannot carry **two** δ-rules for one constant.  `Ordered` can, and that
> is the only thing `roguePiEnv` needs.

## Why no refutation is constructible in this tree

Refuting `ConvPiFromEntry` at *any* environment requires exhibiting a pair of terms that are
**not** `ConvC`-linked, and this tree proves no such fact without `sorryAx`.  Checked, not
assumed:

* the non-derivability *statements* about unbounded conversion in `Theory/` are the three
  negative conjuncts of `WF.rigidShapeUniqNS` (`RigidSortPiDisj`, `RigidConstPiDisj`,
  `RigidConstSortDisj`) and `DefInvRefute`/`UniqueTypingN`'s `SortForallEDisjN`; **all are
  open**, and `InjSortPiModel.lean` items 2–3 record that the model route to them is circular
  (`RigidSortPiDisj`) or refuted (`RigidConstPiDisj`, `RigidConstSortDisj`).
  `StrengthenAudit.no_neutral_proofIrrel` is the one *inhabited* `¬ IsDefEqU` in the tree and it
  is built from `IsDefEqU.sort_forallE_inv`, i.e. from the hole;
* `Theory/Consistency.lean` states consistency **without proof**, and `Theory/SetModel/` carries
  `sorry` in nine files (`Interp.lean`, `InterpSound.lean`, `SoundInduction.lean`, …), so the
  semantic route cannot supply one either;
* the tree has exactly **two** techniques that do prove a conversion absent, and neither
  applies.  (i) `IsDefEq.closedN`, the scope invariant, used by
  `ConstVar.cvarMain_needs_entries`: useless here, because `B` and `B'` live in contexts of
  **equal length** (`A::X::Γ` and `A'::X::Γ`), so neither is out of scope for the other's
  context.  (ii) inversion at a *bounded* alternation index, used by
  `SubstCRefute.inst_does_not_preserve_index` (`¬ IsDefEqN 1 1 …`, via its `stuck` lemma) and by
  `DefInvRefute.sortForallEDisjN_zero` (index 0, free for every environment): useless here,
  because a `ConvC` chain carries no index bound at all — its links stratify to `IsDefEqN U nᵢ`
  at unrelated `nᵢ`, and covering every `nᵢ` **is** the open `SortForallEDisjN` hypothesis.

Any other separation must survive `IsDefEqStrong.beta`, which can turn an application into a Π
(`.app (.lam _ (.bvar 0)) (∀ (_ : Prop), Prop) ≡ ∀ (_ : Prop), Prop`), so a head- or
occurrence-counting invariant cannot be β-stable: separating two terms here is a normalisation
or model obligation, not a syntactic one.  That is why the residual is left named.


## Round 2 (2026-09-01): the `VEnv.WF` clause is TRUE, and it was already a theorem

The first version of this file flagged `[analysis]`: "`RuleShape.delta` pins a δ-rule's lhs to
`.const ci.name _` and `addConst` refuses a duplicate name, so a `VEnv.WF` environment cannot
carry two δ-rules for one constant — a statement about `VEnv.WF'`'s history, not machine-checked
here."  **It is true, and it did not need proving: `DeltaUnique.WF.defEqHeadsUnique` is exactly
it** (`Theory/Typing/DeltaUnique.lean`, `sorryAx`-free; `Classical.choice` only, from
`WF.choose_spec`).  Missing it was my error, not a gap in the tree — `DeltaUnique.lean`'s whole
Part I is this invariant, run as a `WF'` induction on the conjunction with `DefEqHeadsDeclared`
because neither half goes through alone.  So the flag is retired and replaced by

    not_defEqHeadsUnique_roguePiEnv : ¬ roguePiEnv.DefEqHeadsUnique
    not_wf_roguePiEnv               : ¬ VEnv.WF roguePiEnv          (§8)

`roguePiEnv` is `Ordered` and **not** `VEnv.WF`, both machine-checked.  The refutation therefore
does not extend to `VEnv.WF`, and the hypothesis that repairs the statement is named.

### The boundary is one link, not zero (§9)

`def rogueC : Sort 1 := ∀ (_ : Prop), Prop` is an ordinary pure declaration, so
`wfPiEnv := roguePiEnv` *minus its second rule* is well-formed (`wf_wfPiEnv`, built as a genuine
`VDecl.WF.def` step over `∅`) and still carries a `ConvC` link from a `const` to a Π-shape
(`wfPiEnv_link`).  So well-formedness does **not** shut the rogue idiom out of the Π side by
making rules harmless; it removes the *second* link out of the same source, and only that.
`wfPiEnv_defeqs_iff` is the check that the witness dies rather than being blocked: at `wfPiEnv`
both chains of §5 would be the same link, so `B = B'` and the conclusion is `ConvC.refl`.

### A second, independent clause `Ordered` lacks (§10)

`WF.noPiLhs`: **no rule of a well-formed environment has a Π-shaped left-hand side**, in any level
instance — from `PatternRules.WF.ruleShape` plus a shape computation on the three `RuleShape`
constructors (δ: a `const`; quot: a `lam`; ι: `mkLams Γ' (iotaLhs …)`, a `lam` or an `app`,
`iotaLhs` always carrying the major premise).  Consequence, `WF.piPi_extra_closed`: **the `extra`
case of single-link Π/Π inversion is discharged at `VEnv.WF`.**  Of the three cases that carry the
content of that inversion, `extra` is now closed by well-formedness; see §12/§15 for the two
corrections to what Round 2 said about the other two.

The lhs/rhs asymmetry in §10 is real and is checked (`noPiLhs_fires`): `wfPiEnv` is well-formed,
carries a rule, and that rule's **right**-hand side *is* a Π.  So §10 is not the vacuous
observation that well-formed environments have no interesting rules.

### Which reductions survive the strength change: all of them, trivially (§11)

`VEnv.WF.ordered` exists, so every `Ordered`-strength theorem in `InjMidLocal.lean`,
`InjChainLower.lean` and `InjPiInhab.lean` holds at `VEnv.WF` by passing `henv.ordered`.
`piChainAt_bvar_iff_convPiFromEntry_wf` and `convStep2_of_convSortInv_convPiFromEntry_wf` record
that, and it must **not** be read as a repair: they are the same theorems with a stronger
hypothesis.  Everything the strength change buys is in §8 and §10.

### Is the `VEnv.WF`-strength statement still refutable?  No witness, and the reason is the
### confluence hypothesis itself

Proving *un*refutability would be proving the statement, so what is offered is the three blockers,
each a theorem, plus an honest search report.  The blockers: `WF.defEqHeadsUnique` (no two δ-rules
per head), `WF.noPiLhs` (no Π-shaped lhs), and `DeltaUnique.WF.keyUnique` (no two rules sharing a
key, so no ι/ι or ι/δ overlap).  **Remark, not a hinge:** together these say the rule set of a
well-formed environment is one left-linear rule per head with no overlaps, i.e. *orthogonal* — and
orthogonality is exactly the hypothesis under which δ ∪ β is confluent.  So a rogue `VEnv.WF`
witness would be a non-confluence of Lean's own rule set, not an artefact of `Ordered`.  Routes
tried and found not to give one: `unsafeDef` (circular by design, `MutualDefUnsound.lean` — but a
circular value gives *one* rule, e.g. `C ≡ ∀ (_ : Prop), C`, whose chains are joined by that same
rule); a mutual `unsafeDef` block with rules `A ≡ ∀ (_ : Prop), B`, `B ≡ ∀ (_ : Prop), Prop` (the
two Π-chains out of `A` have codomains `B` and `∀ (_ : Prop), Prop`, joined by `B`'s rule); a
second δ-rule for `Quot.lift` alongside the quot rule (`addConst` refuses the redeclaration, the
same mechanism as §8).  This paragraph is a search report and nothing in the file depends on it.

## Round 3 (2026-09-01): two of my own Round-2 claims were wrong, and `trans` does not localise

Round 2's §10 closed with: "of the three cases that carry the content of Π/Π inversion — `trans`,
`proofIrrel`, `extra` — the third is closed by well-formedness and `proofIrrel` is closed by
shape; `trans` is the whole residual, and it is `InjMidpoint.lean`'s midpoint."  **Only the
`extra` clause of that sentence survives.**

**Correction 1 (§12): `ConvStep2`'s midpoint is not the Π/Π `trans` midpoint.**
`convStep2At_of_sort_eq` — when the two link levels are the same expression, the composition is
`IsDefEqStrong.trans` and costs nothing.  So `ConvStep2`'s entire content is the *level mismatch*.
A `trans` node of `IsDefEqStrong` carries **one** type index on both halves by construction, so
the Π/Π `trans` case is not an instance of `ConvStep2`'s obligation at all: what it needs is
Π-shape descent across the midpoint, not level alignment.  Two obligations, not one seen twice.

**Correction 2 (§15): the `proofIrrel` case is not closed by shape.**  The level argument I gave
("`.succ (.imax u v) ≈ .zero` is impossible") is arithmetic applied to something that is not a
level equation.  `IsDefEqStrong.proofIrrel` carries the type index `p`, so at a Π/Π link indexed
`.sort u` the case fires exactly when `env.IsDefEqStrong U Γ (.sort u) (.sort u) (.sort .zero)` is
derivable, and refuting that is a sort/sort inversion.  The tree agrees:
`Injectivity.not_isProof_of_defeqU_forallE` routes through `forallE_not_proof`, whose hypothesis
is `VEnv.SortUniq`, supplied there by the hole `WF.sortUniq'`.  What the case costs is named as
`SortNotPropStrong` and bounded above by `SortUniq` (`sortNotPropStrong_of_sortUniq`) — strictly weaker than
`SortUniq`, but *not* free.

### Task 1, answered: the `VEnv.WF` clauses do not constrain a midpoint (§13)

`WF.defEqHeadsUnique`, `WF.noPiLhs` and `DeltaUnique.WF.keyUnique` are facts about the rule set;
a midpoint is a term.  `midpoint_app_at_empty` exhibits an `.app`-headed midpoint between two
Π-shapes at one sort **over `∅`**, reached by β alone — where all three clauses are vacuous.  So
the answer is **no**, in the strongest available form, and the guess that orthogonality of the
rule set bounds which terms two chains pass through is refuted rather than accepted.

### Task 2's test, and it FAILS: `trans` does not localise (§14)

Row 51's pattern exactly.  `PiMid` — the Π/Π `trans` case written out, two links through an
arbitrary midpoint at one sort — is **equivalent to the single-link statement `PiLinkInvCod` with
no hypothesis at all** (`piMid_iff_piLinkInvCod`), because `IsDefEqStrong.trans` is a rule one way
and `ConvC.one` composes the other.  So "localise the residual at its midpoint" is a restatement.
Nothing is built on it.

`convPiInvCod_of_convStep2_piLinkInvCod` (§16) prices the single-link form: chain form and link
form differ by exactly `ConvStep2` (via `InjChainStep.ConvC.collapseE`), and `PiLinkInvCod` is
strictly weaker input than the `PiInv` that `InjChainStep.convPiInv_of_convStep2` uses.  But the
circle is explicit and is the point: `ConvPiInvCod → ConvPiFromEntry` (§1, free) and
`ConvSortInv ∧ ConvPiFromEntry → ConvStep2`, so §16 buys `ConvStep2 → ConvStep2` unless
`ConvStep2` arrives from outside the corner.  Same verdict as row 51, reached by another route.

### What confluence would have to give, tight (§17)

The only content-bearing restriction of the `trans` case is to a **non-Π** midpoint, and the
Π-midpoint sub-case then needs the two codomain chains — in `A::Γ` and `A''::Γ` — brought into one
context.  The tree had no `IsDefEqStrong.defeqDFC`; §17 supplies the chain form,
`ConvC.defeqDFC`, from `IsDefEq.defeqDF_l` link by link over `Ordered env`.  The request is then

    PiMidNonPi : CtxStrong Γ → (∀ D E, M ≠ .forallE D E) →
                 IsDefEqStrong Γ (.forallE A B) M (.sort u) →
                 IsDefEqStrong Γ M (.forallE A' B') (.sort u) → ConvC (A::Γ) B B'

— *Π-shape descent and nothing else*: no reduction relation, no subject, no typing judgment, no
level arithmetic; it is what "a term convertible to a Π reduces to a Π" buys, in `ConvC` form.
`PiLinkInvCod.piMidNonPi` bounds it above by the statement it is being asked to supply, so the
request is not stronger than the target, and `piMidNonPi_side_fires` checks that the non-Π side
condition is satisfiable at §13's firing midpoint.  Alongside it: `SortNotPropStrong` (the `proofIrrel`
case) and `PiLinkInvDom` (needed only to *apply* `ConvC.defeqDFC`).

**Not claimed:** that those three plus `VEnv.WF` close `PiLinkInvCod`.  That induction is not
done, and no theorem here depends on it.

## Round 4 (2026-09-01): `SortNotPropStrong` costs the sort half; `WF.noPiLhs` was a duplicate

**Correction 3 (§18).**  `DeclRules.WF.instL_lhs_ne_forallE` (`Theory/Typing/DeclRules.lean:239`)
is Round 2's §10 statement character for character, and `WF.instL_lhs_ne_sort` (`:234`) is its sort
analogue; both come from `WF.defeq_isDeclRule`/`IsDeclRule.lhs_shape`.  **§10 re-proved an existing
theorem** (independently, through `PatternRules.RuleShape`).  `noPiLhs_of_declRules` records the
identification.  The only original content of Round 2 is §8, `not_wf_roguePiEnv`.

**Question 1 — is `SortNotPropStrong` free at `VEnv.WF`?  No, and the reason is sharp (§19).**
`sortNotPropStrong_of_convSortInv`: peel the `true`-level typing `Γ ⊢ .sort u : .sort .zero` with
`HasTypeStrong.peelChain`; the base rule can only be `sort'`, which pins the base type to
`.sort (.succ l')`, leaving `ConvC Γ (.sort (.succ l')) (.sort .zero)`; `ConvSortInv` turns that
into `.succ l' ≈ .zero`, refuted by `VLevel.eval` (`succ_not_equiv_zero`).  So

> **the `proofIrrel` case of the Π side costs the sort side.**

`sortUniq_iff_convSortInv` (`BaseUniqChain.lean`) makes `ConvSortInv` and `SortUniq` the same
hypothesis, and `InjChainLower.sortChainAt_bvar_iff_convSortInv` makes it the corner's sort
residual at `.bvar 0`.  `WF.instL_lhs_ne_sort` is exactly the right lemma and it does close the
`extra` route (`WF.sortSort_extra_closed`) — but the `extra` route was never the residual, on
either side.  So the two halves of `ConvStep2` are **not independent**: the Π half's `proofIrrel`
case consumes the sort half.

**Question 2 — refutable at a `VEnv.WF` environment?  No witness found, and the rule routes are
closed.**  Refuting `SortNotPropStrong` needs `ConvC Γ (.sort (.succ l')) (.sort .zero)`.  A link
between two syntactic sorts can come from `sortDF` (which forces the levels equivalent —
`succ_not_equiv_zero` kills it), from `extra` (closed by §18), or from `symm`/`trans`/`defeqDF`
(the wall).  Two δ-rules identifying `Sort 1` with `Prop` through a common constant are refused by
`WF.defEqHeadsUnique` (§8); two *different* constants give no link between their values.  So the
search has nowhere to go for the same orthogonality reason as Round 2's, and no claim of
unrefutability is made.

**Four for four (§20).**  The sort side localises no better than the Π side, for the identical
reason: `sortMid_iff_sortLinkInv` is a free equivalence in both directions
(`IsDefEqStrong.trans` is a rule), and `convSortInv_of_convStep2_sortLinkInv` prices the chain
form against the link form at exactly `ConvStep2`, mirroring §14/§16.  So the standing "test a
localisation against its own target first" rule holds on both halves.

**`PiLinkInvDom`, priced (§21).**  It **is** row 53's dead conjunct in single-link guise as an
*output* — `ConvPiInv.piLinkInvDom` is `.1` of the chain form and every consumer takes `.2`.
Neither half implies the other and nothing makes it strictly weaker than `PiLinkInvCod`; they are
two projections of one statement.  Where it is not dead is as an **input** to §17's induction, and
that is flagged in §21 as a remark rather than a hinge, because the induction is not written:
strengthening the conclusion to both contexts at once (the `Injectivity.RigidPiUniq` shape) does
not remove the need to move `B'' ⇝ B'` from `A''::Γ` into `A::Γ`.

**No dependency taken on the confluence layer.**  `PiMidNonPi` stays a request (§17), unchanged.

## Round 5 (2026-09-01): the sort side reduces, and the critical path has one prerequisite

**Task 1 — is `ConvSortInv` refutable at a `VEnv.WF` environment?**  No witness, and now the case
list is a theorem rather than prose.  `sortLinkInv_of_wf` (§22) is an induction on
`IsDefEqStrong` whose conclusion is the level equation `a ≈ b` — carrying **no context and no type
index** — and that is what makes it go through where §17's Π-side induction could not: `defeqDF` is
free (the index changes, the conclusion does not mention it), `symm` is `Eq.symm`, and
`trans`-through-a-sort is `Eq.trans`.  Eleven of the thirteen constructors close inside the proof:
seven by endpoint shape, `sortDF` by its own side condition, `extra` by
`DeclRules.WF.instL_lhs_ne_sort`, `symm`/`defeqDF` by the induction hypothesis.  **Exactly two
survive** — `trans` at a non-sort midpoint (`SortMidNonSort`) and `proofIrrel` (`SortNotProof`) —
and both are *descent* statements about a term that is not a sort, not statements about rules.
So every rule-level route into a sort/sort link is shut, and a rogue `VEnv.WF` witness would have
to exhibit a term converting to two `≉` sorts, i.e. a non-confluence of Lean's own rule set.  No
such witness is claimed and none was found.

**And this localisation, unlike the previous five tests, is a genuine reduction.**
`SortLinkInvU.sortMidNonSort` gives target → residual for free; the converse has **no route**,
because a single link offers no non-sort midpoint and the sort-midpoint case is supplied by the
induction hypothesis, which only the induction has.  One correction inside the round: the first
draft asserted `SortLinkInv → SortMidNonSort`, which does not typecheck — `SortMidNonSort`
quantifies over an arbitrary index, so the right target is the index-free `SortLinkInvU`.

**`SortNotProof` is not a new obligation**: it is `Injectivity.not_isProof_of_defeqU_sort` at
`e = .sort a`, which that file proves from `WF.sortUniq'` — from `SortUniq`, i.e. from the very
statement being reduced.  Cited, not imported (the bound runs through `sorryAx`).

**Task 2 — priced against the reference (§23).**  `unique.tex` proves clause (1) of definitional
inversion — which *is* `ConvSortInv` — **only** through `thm:ckappa`, whose transitivity is the
Church–Rosser property, and its own §8 says the theorem cannot be proved before CR.  So
`ConvSortInv` presupposes confluence.  Better: the reference discharges clauses (1), (2) and (3)
by the *same* two moves, so this tree's `SortMidNonSort`, `PiMidNonPi` and `RigidSortPiDisj` are
**three instances of one fact** — a κ-normal rigid head has no reduct of another shape — plus CR.
**The critical path has one prerequisite, not two.**  The `proofIrrel` residuals are the exception:
the reference kills them with unique typing at the *previous* index, and `SubstCRefute.lean` has
refuted the step of that proof (`VEnv.SubstC`, `unique.tex:51`), so that route is not available
here as written.

No dependency taken on the confluence layer; `PiMidNonPi` and `SortMidNonSort` are requests.

## Axioms and cone

`#print axioms` block at the end: every declaration is `sorryAx`-free; `Classical.choice` appears
nowhere.  The import closure is `InjPiInhab.lean`'s — `UniqueTyping.lean`, `ChurchRosser.lean`
and `Strengthen.lean` absent — so `IsDefEqU.sort_inv`, `WF.sortUniq'`, `IsDefEq.uniq`,
`IsDefEqU.trans` and `NormalEq.descend` are not consumed and not present.
-/

namespace Lean4Lean
namespace VEnv

variable {env : VEnv} {U : Nat}

/-! ## §1 The common source is free -/

theorem ConvPiInvCod.convPiFromEntry (h : ConvPiInvCod env U) : ConvPiFromEntry env U :=
  fun hΓ h1 h2 => h hΓ (h1.symm.trans h2)

/-! ## §2 The rogue Π environment -/

def rogueC : Lean.Name := `Lean4Lean.roguePiConst

def roguePiCi : VConstant := ⟨0, .sort (.succ .zero)⟩

/-- `∀ (_ : Prop), Prop` -/
def roguePi1 : VExpr := .forallE (.sort .zero) (.sort .zero)
/-- `∀ (_ : Prop), ∀ (_ : Prop), Prop` -/
def roguePi2 : VExpr := .forallE (.sort .zero) roguePi1

def rogueDf1 : VDefEq := ⟨0, .const rogueC [], roguePi1, .sort (.succ .zero)⟩
def rogueDf2 : VDefEq := ⟨0, .const rogueC [], roguePi2, .sort (.succ .zero)⟩

def rogueEnv1 : VEnv where
  constants n := if rogueC = n then some roguePiCi else none
  defeqs _ := False

def roguePiEnv : VEnv := (rogueEnv1.addDefEq rogueDf1).addDefEq rogueDf2

theorem roguePropType {Γ : List VExpr} :
    env.HasType U Γ (.sort .zero) (.sort (.succ .zero)) := .sortDF trivial trivial rfl

theorem rogueSort1Type {Γ : List VExpr} :
    env.HasType U Γ (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) :=
  .sortDF (by exact trivial) (by exact trivial) rfl

theorem rogue_imax_one_one : VLevel.imax (.succ .zero) (.succ .zero) ≈ (.succ .zero : VLevel) := by
  simp [VLevel.equiv_def, VLevel.eval, Lean.Nat.imax]

theorem roguePi1_type {Γ : List VExpr} :
    env.HasType U Γ roguePi1 (.sort (.succ .zero)) :=
  .defeqDF (.sortDF (by exact ⟨trivial, trivial⟩) trivial rogue_imax_one_one)
    (.forallEDF roguePropType roguePropType)

theorem roguePi2_type {Γ : List VExpr} :
    env.HasType U Γ roguePi2 (.sort (.succ .zero)) :=
  .defeqDF (.sortDF (by exact ⟨trivial, trivial⟩) trivial rogue_imax_one_one)
    (.forallEDF roguePropType roguePi1_type)

theorem rogueC_type {Γ : List VExpr} (h : env.constants rogueC = some roguePiCi) :
    env.HasType U Γ (.const rogueC []) (.sort (.succ .zero)) := by
  have := IsDefEq.constDF (env := env) (uvars := U) (Γ := Γ) (ls := []) (ls' := [])
    h (by simp) (by simp) rfl (by simp)
  exact by simpa [roguePiCi, VExpr.instL, VLevel.inst, VEnv.HasType] using this

/-! ## §3 `roguePiEnv` is `Ordered` -/

theorem rogueEnv1_constants : rogueEnv1.constants rogueC = some roguePiCi := by simp [rogueEnv1]

theorem roguePiEnv_constants : roguePiEnv.constants rogueC = some roguePiCi := rogueEnv1_constants

theorem roguePiEnv_defeqs1 : roguePiEnv.defeqs rogueDf1 := by
  simp [roguePiEnv, VEnv.addDefEq, rogueEnv1]

theorem roguePiEnv_defeqs2 : roguePiEnv.defeqs rogueDf2 := by
  simp [roguePiEnv, VEnv.addDefEq, rogueEnv1]

theorem addConst_rogueEnv1 : VEnv.empty.addConst rogueC roguePiCi = some rogueEnv1 := by
  simp [VEnv.addConst, VEnv.empty, rogueEnv1]

theorem ordered_rogueEnv1 : Ordered rogueEnv1 :=
  .const .empty ⟨_, rogueSort1Type⟩ addConst_rogueEnv1

theorem ordered_roguePiEnv : Ordered roguePiEnv :=
  .defeq (.defeq ordered_rogueEnv1 ⟨rogueC_type rogueEnv1_constants, roguePi1_type⟩)
    ⟨rogueC_type rogueEnv1_constants, roguePi2_type⟩

/-! ## §4 Two `ConvC` links out of one source, at an `Ordered` environment -/

theorem rogue_onCtx : OnCtx [VExpr.const rogueC []] (roguePiEnv.IsType 0) :=
  ⟨trivial, _, rogueC_type roguePiEnv_constants⟩

theorem rogue_ctxStrong : CtxStrong roguePiEnv 0 [VExpr.const rogueC []] :=
  .strong ordered_roguePiEnv rogue_onCtx

theorem rogue_link1 :
    ConvC roguePiEnv 0 [VExpr.const rogueC []] (VExpr.const rogueC []) roguePi1 := by
  have h := IsDefEq.extra (env := roguePiEnv) (uvars := 0) (Γ := [VExpr.const rogueC []])
    (ls := []) (df := rogueDf1) roguePiEnv_defeqs1 (by simp) rfl
  simp [rogueDf1, roguePi1, VExpr.instL, VLevel.inst] at h
  exact .one (h.strong ordered_roguePiEnv rogue_onCtx)

theorem rogue_link2 :
    ConvC roguePiEnv 0 [VExpr.const rogueC []] (VExpr.const rogueC []) roguePi2 := by
  have h := IsDefEq.extra (env := roguePiEnv) (uvars := 0) (Γ := [VExpr.const rogueC []])
    (ls := []) (df := rogueDf2) roguePiEnv_defeqs2 (by simp) rfl
  simp [rogueDf2, roguePi2, roguePi1, VExpr.instL, VLevel.inst] at h
  exact .one (h.strong ordered_roguePiEnv rogue_onCtx)

/-! ## §5 What `ConvPiFromEntry` forces at `roguePiEnv` -/

/-- The two Π-shapes are chain-linked at an `Ordered` environment, with **syntactically
distinct codomains** — `ConvPiInvCod`'s premise, fired by the rogue idiom. -/
theorem rogue_piPi : ConvC roguePiEnv 0 [VExpr.const rogueC []] roguePi1 roguePi2 :=
  rogue_link1.symm.trans rogue_link2

theorem rogue_cod_ne : (VExpr.sort .zero) ≠ roguePi1 := by simp [roguePi1]

theorem rogue_lift : (VExpr.const rogueC []).lift = VExpr.const rogueC [] := rfl

/-- **The forcing theorem.**  `ConvPiFromEntry` at `roguePiEnv` — an `Ordered` environment —
forces the closed conversion `Prop ≡ ∀ (_ : Prop), Prop`. -/
theorem convPiFromEntry_forces (h : ConvPiFromEntry roguePiEnv 0) :
    ConvC roguePiEnv 0 [VExpr.sort .zero, VExpr.const rogueC []] (.sort .zero) roguePi1 :=
  h (Γ := []) (X := .const rogueC []) (A := .sort .zero) (B := .sort .zero)
    (A' := .sort .zero) (B' := roguePi1) rogue_ctxStrong
    (by rw [rogue_lift]; exact rogue_link1) (by rw [rogue_lift]; exact rogue_link2)

/-- The separation fact the refutation needs, named. -/
def RoguePiSep : Prop :=
  ¬ ConvC roguePiEnv 0 [VExpr.sort .zero, VExpr.const rogueC []] (.sort .zero) roguePi1

theorem not_convPiFromEntry_of_sep (h : RoguePiSep) : ¬ ConvPiFromEntry roguePiEnv 0 :=
  fun H => h (convPiFromEntry_forces H)

theorem not_convPiInvCod_of_sep (h : RoguePiSep) : ¬ ConvPiInvCod roguePiEnv 0 :=
  fun H => not_convPiFromEntry_of_sep h H.convPiFromEntry

theorem not_piChainAt_bvar_of_sep (h : RoguePiSep) : ¬ PiChainAt roguePiEnv 0 (.bvar 0) :=
  fun H => not_convPiFromEntry_of_sep h (convPiFromEntry_of_piChainAt_bvar ordered_roguePiEnv H)

theorem not_convPiInvCodInhab_of_sep (h : RoguePiSep) : ¬ ConvPiInvCodInhab roguePiEnv 0 :=
  fun H => not_piChainAt_bvar_of_sep h (piChainAt_of_convPiInvCodInhab H baseUniqCAt_bvar)

/-! ## §6 The residual, named and bounded -/

/-- **Sort/Π disjointness along a chain** — the `ConvC` form of `RigidSortPiDisj`
(`IsDefEqU.sort_forallE_inv`), the one conjunct of `WF.rigidShapeUniqNS` whose *semantic*
residual is a theorem (`InjSortPiModel.interp_sort_ne_interp_forallE`). -/
def ConvSortPiDisj (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {u : VLevel} {A B : VExpr}, ¬ ConvC env U Γ (.sort u) (.forallE A B)

/-- The same over the reference's typing-free judgment (`RawDefEq.lean`). -/
def SortPiDisjRaw (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {u : VLevel} {A B : VExpr}, ¬ env.IsDefEqRaw U Γ (.sort u) (.forallE A B)

theorem SortPiDisjRaw.convSortPiDisj (h : SortPiDisjRaw env U) : ConvSortPiDisj env U := by
  intro Γ u A B hc
  match hc.eq_or_raw with
  | .inl e => exact absurd e (by simp)
  | .inr r => exact h r

/-- **`ConvPiFromEntry` is FALSE at an `Ordered` environment, modulo sort/Π disjointness at
that environment.**  Nothing here proves `ConvSortPiDisj roguePiEnv 0`; it is the residual, and
it is *not* part of `ConvPiFromEntry` — it is a conjunct of the other hole. -/
theorem not_convPiFromEntry_of_convSortPiDisj (h : ConvSortPiDisj roguePiEnv 0) :
    ¬ ConvPiFromEntry roguePiEnv 0 := fun H => h (convPiFromEntry_forces H)

theorem not_convPiFromEntry_of_sortPiDisjRaw (h : SortPiDisjRaw roguePiEnv 0) :
    ¬ ConvPiFromEntry roguePiEnv 0 := not_convPiFromEntry_of_convSortPiDisj h.convSortPiDisj

theorem not_convPiInvCod_of_convSortPiDisj (h : ConvSortPiDisj roguePiEnv 0) :
    ¬ ConvPiInvCod roguePiEnv 0 :=
  fun H => not_convPiFromEntry_of_convSortPiDisj h H.convPiFromEntry

theorem not_piChainAt_bvar_of_convSortPiDisj (h : ConvSortPiDisj roguePiEnv 0) :
    ¬ PiChainAt roguePiEnv 0 (.bvar 0) :=
  fun H => not_convPiFromEntry_of_convSortPiDisj h
    (convPiFromEntry_of_piChainAt_bvar ordered_roguePiEnv H)

theorem not_convPiInvCodInhab_of_convSortPiDisj (h : ConvSortPiDisj roguePiEnv 0) :
    ¬ ConvPiInvCodInhab roguePiEnv 0 :=
  fun H => not_piChainAt_bvar_of_convSortPiDisj h (piChainAt_of_convPiInvCodInhab H baseUniqCAt_bvar)

/-! ## §7 What separates `Ordered` from `VEnv.WF` here, exactly -/

/-- **The two rogue rules share a left-hand side.**  `VEnv.RuleShape.delta`
(`PatternRules.lean`) pins a δ-rule's lhs to `.const ci.name _`, and `VEnv.addConst` refuses a
name it already holds, so a `VEnv.WF` environment cannot carry two δ-rules for one constant.
`Ordered` has no such clause — `Ordered.defeq` asks only `df.WF env`, which both rules satisfy
(`ordered_roguePiEnv`).  That missing clause is what makes `roguePiEnv` possible, and it
is therefore a hypothesis a confluence development aimed at `ConvPiFromEntry` has to consume.

**But it is one clause too weak, and "that single missing clause" overstates it (noted 2026-09-05
from `Theory/Typing/InjMethod.lean`).**  This file's rogue needs **two** δ-rules on **one constant**,
so it pins `DefEqHeadsUnique`.  `InjMethod.injEnv` needs **one** rule that is **not `const`-headed at
all** -- `⟨0, .sort .zero, .forallE (.sort .zero) (.sort .zero), .sort (.succ .zero)⟩`, one rule and
**zero constants** -- and it is `Ordered` (`ordered_injEnv`) and refutes clause (3) of
`rigidShapeUniqNS` at every `n ≥ 1` (`not_sortForallEDisjN_of_ordered`, hole-free).  What that pins is
`VEnv.RuleShape.delta` itself, which is **logically prior** to `DefEqHeadsUnique`: uniqueness of heads
presupposes there is a head to be unique.  So the separation between `Ordered` and `VEnv.WF` here is
**at least two** clauses deep, and a development consuming only `DefEqHeadsUnique` does not reach
`InjMethod`'s witness.  That file also proves its own limit (`not_wf_injEnv`), and records that the
same idiom **cannot** be pushed to the sort-side clause, because no legal `VDefEq` relates two sorts
at distinct levels -- `.sort u : .sort (.succ u)` forces the declared types apart.
("At most one δ-rule per constant" is **not** `[analysis]` any more: it is
`DeltaUnique.WF.defEqHeadsUnique`, and §8 cashes it in as `not_wf_roguePiEnv`.) -/
theorem rogue_rules_share_lhs : rogueDf1.lhs = rogueDf2.lhs ∧ rogueDf1 ≠ rogueDf2 := by
  refine ⟨rfl, ?_⟩
  intro h; rw [rogueDf1, rogueDf2] at h; injection h with _ _ h; simp [roguePi1, roguePi2] at h

/-- Non-vacuity: `ConvPiInvCod`'s premise fires at `roguePiEnv` with the two codomains
syntactically distinct, so §6 is not about an empty set of instances.  (Firing a premise is not
evidence that the hypothesis is satisfiable.) -/
theorem rogue_fires : ConvC roguePiEnv 0 [VExpr.const rogueC []] roguePi1 roguePi2 ∧
    (VExpr.sort .zero : VExpr) ≠ roguePi1 := ⟨rogue_piPi, rogue_cod_ne⟩

/-! ## §8 The `VEnv.WF` clause, checked -/

/-- `roguePiEnv` carries **two** δ-rules with the head `rogueC`, and they are distinct. -/
theorem not_defEqHeadsUnique_roguePiEnv : ¬ roguePiEnv.DefEqHeadsUnique := by
  intro H
  exact rogue_rules_share_lhs.2
    (H _ _ rogueC roguePiEnv_defeqs1 roguePiEnv_defeqs2 ⟨[], rfl⟩ ⟨[], rfl⟩)

/-- **The clause, no longer `[analysis]`.**  `roguePiEnv` is not a well-formed environment, and
the reason is `DeltaUnique.WF.defEqHeadsUnique` — `VEnv.WF`'s declaration history, in which
`addConst` rejects a duplicate name, so no name carries two δ-rules. -/
theorem not_wf_roguePiEnv : ¬ VEnv.WF roguePiEnv :=
  fun h => not_defEqHeadsUnique_roguePiEnv h.defEqHeadsUnique

/-- **Degenerate check for §8.**  `DefEqHeadsUnique` is not false everywhere — it holds at the
empty environment, vacuously — so `not_defEqHeadsUnique_roguePiEnv` is content and not an artefact
of a predicate nothing satisfies. -/
theorem defEqHeadsUnique_empty : (∅ : VEnv).DefEqHeadsUnique := fun _ _ _ h => h.elim

/-! ## §9 The boundary: **one** such link does survive `VEnv.WF`

`def rogueC : Sort 1 := ∀ (_ : Prop), Prop` is a perfectly ordinary pure declaration, so the
*first* rogue rule alone builds a `VEnv.WF` environment.  `roguePiEnv` is that environment plus
one more rule for the same constant, and §8 is what refuses the second.  So the barrier is
precisely "at most one δ-rule per constant", not "no δ-rule may have a Π-shaped value" — the
latter is false (`wfPiEnv_link`). -/

def rogueDefVal : VDefVal where
  uvars := 0
  type := .sort (.succ .zero)
  name := rogueC
  value := roguePi1

theorem rogueDefVal_toDefEq : rogueDefVal.toDefEq = rogueDf1 := by
  simp [rogueDefVal, VDefVal.toDefEq, rogueDf1, VLevel.params]

/-- `roguePiEnv` minus its second rule. -/
def wfPiEnv : VEnv := rogueEnv1.addDefEq rogueDf1

theorem roguePiEnv_eq : roguePiEnv = wfPiEnv.addDefEq rogueDf2 := rfl

theorem rogue_decl_wf : VDecl.WF VEnv.empty (.def rogueDefVal) wfPiEnv := by
  have h := VDecl.WF.def (env := VEnv.empty) (ci := rogueDefVal) (env' := rogueEnv1)
    (show VDefVal.WF _ _ from roguePi1_type) (by exact addConst_rogueEnv1)
  rwa [rogueDefVal_toDefEq] at h

theorem wf_wfPiEnv : VEnv.WF wfPiEnv := ⟨[.def rogueDefVal], .decl rogue_decl_wf .empty⟩

theorem wfPiEnv_defeqs1 : wfPiEnv.defeqs rogueDf1 := .inl rfl

theorem wfPiEnv_constants : wfPiEnv.constants rogueC = some roguePiCi := rogueEnv1_constants

theorem ordered_wfPiEnv : Ordered wfPiEnv :=
  .defeq ordered_rogueEnv1 ⟨rogueC_type rogueEnv1_constants, roguePi1_type⟩

theorem wfPiEnv_onCtx : OnCtx [VExpr.const rogueC []] (wfPiEnv.IsType 0) :=
  ⟨trivial, _, rogueC_type wfPiEnv_constants⟩

/-- **A `ConvC` link from a `const` to a Π-type, at a `VEnv.WF` environment.**  So the rogue
idiom is *not* shut out of the Π side by well-formedness; what well-formedness removes is the
**second** link out of the same source. -/
theorem wfPiEnv_link : ConvC wfPiEnv 0 [VExpr.const rogueC []] (VExpr.const rogueC []) roguePi1 := by
  have h := IsDefEq.extra (env := wfPiEnv) (uvars := 0) (Γ := [VExpr.const rogueC []])
    (ls := []) (df := rogueDf1) wfPiEnv_defeqs1 (by simp) rfl
  simp [rogueDf1, roguePi1, VExpr.instL, VLevel.inst] at h
  exact .one (h.strong ordered_wfPiEnv wfPiEnv_onCtx)

/-- **`wfPiEnv` has exactly one rule.**  This is the check that §9's environment does not merely
*fail* to carry a second link but cannot: instantiating §5 at `wfPiEnv` would have to use the same
link for both chains, so `B = B'` and the conclusion is `ConvC.refl`.  The witness dies, it is not
merely blocked. -/
theorem wfPiEnv_defeqs_iff {df : VDefEq} : wfPiEnv.defeqs df ↔ df = rogueDf1 :=
  ⟨fun h => h.resolve_right (fun h => h.elim), .inl⟩

/-! ## §10 What `VEnv.WF` gives on the Π side: no rule has a Π-shaped left-hand side

`RuleShape` (`PatternRules.lean`) says every rule of a well-formed environment is a δ-rule, the
quotient rule, or an ι-rule.  All three have a left-hand side whose head is a `const`, a `lam` or
an `app`, in **every** level instance.  So the `extra` route to a `ConvC` link *out of* a Π-shape
is closed at `VEnv.WF` — which is the second thing `Ordered` does not give, alongside §8.

The statement is about the **left**-hand side only, and that asymmetry is real, not an
oversight: `rogueDf1.rhs` **is** a Π (`noPiLhs_fires`), and `wfPiEnv` is well-formed. -/

/-- `df.lhs` is not a Π-shape, in any level instance. -/
def NoPiLhs (df : VDefEq) : Prop := ∀ ls A B, df.lhs.instL ls ≠ .forallE A B

theorem instL_ne_forallE : ∀ {e : VExpr}, (∀ A B, e ≠ .forallE A B) →
    ∀ {ls : List VLevel} {A B : VExpr}, e.instL ls ≠ .forallE A B
  | .bvar _, _ => nofun
  | .sort _, _ => nofun
  | .const _ _, _ => nofun
  | .app _ _, _ => nofun
  | .lam _ _, _ => nofun
  | .forallE A B, h => fun _ => absurd rfl (h A B)

theorem mkLams_ne_forallE {As : List VExpr} {b : VExpr} (hb : ∀ A B, b ≠ .forallE A B) :
    ∀ A B, VExpr.mkLams As b ≠ .forallE A B := by
  cases As with
  | nil => exact hb
  | cons A As => rintro A B ⟨⟩

/-- **Every rule shape has a non-Π left-hand side.** -/
theorem RuleShape.noPiLhs {env : VEnv} {df : VDefEq} : env.RuleShape df → NoPiLhs df
  | .delta ci _ => fun _ _ _ => instL_ne_forallE (by rintro A B ⟨⟩)
  | .quot _ _ => fun _ _ _ => instL_ne_forallE (by rintro A B h; exact absurd h nofun)
  | .iota D j q T C .. => fun _ _ _ => instL_ne_forallE
      (mkLams_ne_forallE (by rw [VInductDecl'.iotaLhs, VExpr.mkApp_concat]; nofun))

/-- **No rule of a well-formed environment has a Π-shaped left-hand side.** -/
theorem WF.noPiLhs {env : VEnv} (h : VEnv.WF env) {df : VDefEq} (hdf : env.defeqs df) :
    NoPiLhs df := (h.ruleShape hdf).noPiLhs

/-- Non-vacuity, at the one place where it could be vacuous: §10 is *not* the observation that a
well-formed environment has no interesting rules.  `wfPiEnv` is well-formed, carries a rule, and
that rule's **right**-hand side is a Π. -/
theorem noPiLhs_fires :
    wfPiEnv.defeqs rogueDf1 ∧ NoPiLhs rogueDf1 ∧ rogueDf1.rhs = VExpr.forallE (.sort .zero) (.sort .zero) :=
  ⟨wfPiEnv_defeqs1, WF.noPiLhs wf_wfPiEnv wfPiEnv_defeqs1, rfl⟩

/-- **The payoff: the `extra` case of single-link Π/Π inversion is discharged at `VEnv.WF`.**
An `IsDefEqStrong.extra` link relates `df.lhs.instL ls` to `df.rhs.instL ls`; for it to relate
two Π-shapes (in either order, `symm` being a rule) one of them must be the **left**-hand side,
and §10 forbids that.  So of the three cases that carry the content of Π/Π inversion — `trans`,
`proofIrrel`, `extra` — the third is closed by well-formedness alone, and `proofIrrel` is closed
by shape (a Π's type is a sort, and `.sort (.imax u v) : p` with `p : .sort .zero` would need
`.succ (.imax u v) ≈ .zero`).  `trans` is the whole residual, and it is `InjMidpoint.lean`'s
midpoint. -/
theorem WF.piPi_extra_closed {env : VEnv} (h : VEnv.WF env) {df : VDefEq}
    (hdf : env.defeqs df) {ls : List VLevel} {A B A' B' : VExpr} :
    ¬ (df.lhs.instL ls = .forallE A B ∧ df.rhs.instL ls = .forallE A' B') :=
  fun ⟨hl, _⟩ => WF.noPiLhs h hdf ls A B hl

/-- **Degenerate check for §10.**  `NoPiLhs` is a refutable predicate: the rule that *would* break
Π/Π inversion — one whose left-hand side is a Π — fails it.  So `WF.noPiLhs` is not a tautology
about `VDefEq`, and `WF.piPi_extra_closed` is not vacuous by construction. -/
theorem not_noPiLhs_piRule :
    ¬ NoPiLhs ⟨0, .forallE (.sort .zero) (.sort .zero), .sort .zero, .sort (.succ .zero)⟩ :=
  fun h => h [] _ _ rfl

/-! ## §11 The reductions at `VEnv.WF` strength

`VEnv.WF.ordered` (`EnvLemmas.lean`) means **every** `Ordered`-strength reduction in
`InjMidLocal.lean`, `InjChainLower.lean` and `InjPiInhab.lean` survives the strength change
verbatim: pass `henv.ordered`.  There is no work to do and no theorem to re-prove, and it would
be misleading to present the restatements below as a repair — they are the same theorems with a
stronger hypothesis, recorded so that the `VEnv.WF`-strength target has a name.

What the strength change buys is **not** in these statements.  It is §8 and §10: the two clauses
that refuse `roguePiEnv`. -/

theorem piChainAt_bvar_iff_convPiFromEntry_wf (henv : VEnv.WF env) :
    PiChainAt env U (.bvar 0) ↔ ConvPiFromEntry env U :=
  piChainAt_bvar_iff_convPiFromEntry henv.ordered

theorem convStep2_of_convSortInv_convPiFromEntry_wf (henv : VEnv.WF env)
    (hsi : ConvSortInv env U) (hpe : ConvPiFromEntry env U) : ConvStep2 env U :=
  convStep2_of_convSortInv_convPiFromEntry henv.ordered hsi hpe

/-- The degenerate instance, checked as the brief demands: at the empty environment the
equivalence is not vacuous on the left — `PiChainAt ∅ 0 (.bvar 0)`'s premises are inhabited
(`ProofRetypeHeads.prhPi12` fires over *every* environment, `InjPiInhab.piChainAt_bvar_fires`) —
and `∅` is well-formed, so §11 has a firing instance at the degenerate point. -/
theorem empty_wf : VEnv.WF (∅ : VEnv) := ⟨[], .empty⟩

/-! ## §12 CORRECTION: `ConvStep2`'s midpoint is **not** the Π/Π `trans` midpoint

§10's closing sentence — "`trans` is the whole residual, and it is `InjMidpoint.lean`'s
midpoint" — is **wrong**, and this section is the check.  `ConvStep2At env U Y` composes
`IsDefEqStrong Γ X Y (.sort a)` with `IsDefEqStrong Γ Y Z (.sort b)` at **different** levels
`a`, `b`; when the two levels are the same expression the conclusion is `IsDefEqStrong.trans`
and there is nothing to pay (`convStep2At_of_sort_eq`).  So `ConvStep2`'s entire content is the
*level mismatch*.

The Π/Π `trans` case is the opposite shape: `IsDefEqStrong.trans` is a **rule**, so both halves
of a `trans` node carry the *same* type index `.sort u`, and what is needed there is not level
alignment but Π-shape descent across the midpoint.  Closing `ConvStep2` therefore does not close
it and closing it does not close `ConvStep2`; they are two obligations, not one seen twice. -/

theorem convStep2At_of_sort_eq {Y : VExpr} {Γ : List VExpr} {X Z : VExpr} {a : VLevel}
    (h1 : env.IsDefEqStrong U Γ X Y (.sort a)) (h2 : env.IsDefEqStrong U Γ Y Z (.sort a)) :
    ∃ u, env.IsDefEqStrong U Γ X Z (.sort u) := ⟨a, .trans h1 h2⟩

/-! ## §13 Task 1, answered: the `VEnv.WF` clauses do **not** constrain a midpoint

`WF.defEqHeadsUnique`, `WF.noPiLhs` and `DeltaUnique.WF.keyUnique` are facts about the *rule
set*.  A midpoint is a term, and the costly midpoint heads of `InjMidpoint.MidFree` are reached
by **β alone** — so they are reached at the *empty* environment, where all three clauses are
vacuous.  `midpoint_app_at_empty` is that witness: an `.app`-headed midpoint sitting between two
Π-shapes, at one and the same sort, over `∅`.

So orthogonality of the rule set bounds nothing about midpoints, and the answer to "do the three
clauses constrain what a midpoint can be" is **no**, in the strongest available form. -/

/-- The midpoint, named: a β-redex, `.app`-headed. -/
def appMid : VExpr := .app (.lam (.sort (.succ .zero)) (.bvar 0)) roguePi1

theorem appMid_isApp : ∃ f a, appMid = .app f a := ⟨_, _, rfl⟩

theorem midpoint_app_at_empty :
    (∅ : VEnv).IsDefEqStrong 0 [] roguePi1 appMid (.sort (.succ .zero)) ∧
      (∅ : VEnv).IsDefEqStrong 0 [] appMid roguePi1 (.sort (.succ .zero)) := by
  have hb : (∅ : VEnv).HasType 0 [VExpr.sort (.succ .zero)] (.bvar 0) (.sort (.succ .zero)) :=
    .bvar .zero
  have hbeta : (∅ : VEnv).IsDefEq 0 [] appMid roguePi1 (.sort (.succ .zero)) := by
    have h := IsDefEq.beta (env := ∅) (uvars := 0) (Γ := []) (A := .sort (.succ .zero))
      (B := .sort (.succ .zero)) (e := .bvar 0) (e' := roguePi1) hb roguePi1_type
    simpa [appMid, VExpr.inst] using h
  have h1 : (∅ : VEnv).IsDefEqStrong 0 [] appMid roguePi1 (.sort (.succ .zero)) :=
    hbeta.strong .empty trivial
  exact ⟨h1.symm, h1⟩

/-! ## §14 Task 2's test, and it FAILS: localising `trans` at its midpoint buys nothing

Row 51's pattern, exactly.  `PiMid` is the Π/Π `trans` case written out — two links through an
arbitrary midpoint at one sort — and `PiLinkInvCod` is the single-link statement it was supposed
to localise.  They are **equivalent with no hypothesis at all** (`piMid_iff_piLinkInvCod`),
because `IsDefEqStrong.trans` is a rule in one direction and `ConvC.one` composes in the other.
So "localise the residual at its midpoint" is a restatement; do not build on it.

The only content-bearing restriction is to a **non-Π** midpoint (`PiMidNonPi`, §17), and that
one is not free: the Π-midpoint sub-case then needs the induction hypothesis twice *and* a
context conversion for `ConvC` (the two codomain chains land in `A::Γ` and `A''::Γ`).  No
`IsDefEqStrong.defeqDFC` exists in this tree — checked — so that lemma is a prerequisite, not a
detail. -/

/-- Π-injectivity's codomain half for a **single** `IsDefEqStrong` link at a syntactic sort. -/
def PiLinkInvCod (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {A B A' B' : VExpr} {u : VLevel}, CtxStrong env U Γ →
    env.IsDefEqStrong U Γ (.forallE A B) (.forallE A' B') (.sort u) → ConvC env U (A::Γ) B B'

/-- The same, written as the `trans` case: two links through an arbitrary midpoint at one sort. -/
def PiMid (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {A B A' B' M : VExpr} {u : VLevel}, CtxStrong env U Γ →
    env.IsDefEqStrong U Γ (.forallE A B) M (.sort u) →
    env.IsDefEqStrong U Γ M (.forallE A' B') (.sort u) → ConvC env U (A::Γ) B B'

/-- **The collapse test, FAILING.**  Both directions, no hypotheses. -/
theorem piMid_iff_piLinkInvCod : PiMid env U ↔ PiLinkInvCod env U := by
  constructor
  · intro H Γ A B A' B' u hΓ h
    exact H hΓ h (h.symm.trans h)
  · intro H Γ A B A' B' M u hΓ h1 h2
    exact H hΓ (h1.trans h2)

/-! ## §15 CORRECTION: the `proofIrrel` case is **not** closed by shape

§10 also claimed `proofIrrel` is "closed by shape (a Π's type is a sort, and
`.sort (.imax u v) : p` with `p : .sort .zero` would need `.succ (.imax u v) ≈ .zero`)".  That
reasoning is a *level* argument applied to a judgment that is not a level equation.
`IsDefEqStrong.proofIrrel`'s conclusion carries the type index `p`, so for a Π/Π link at
`.sort u` the case fires exactly when `env.IsDefEqStrong U Γ (.sort u) (.sort u) (.sort .zero)`
is derivable — and refuting *that* is a sort/sort inversion, not arithmetic.  The tree agrees:
`Injectivity.not_isProof_of_defeqU_forallE` ("a term convertible with a Π is not a proof") goes
through `forallE_not_proof`, whose hypothesis is `VEnv.SortUniq`, supplied there by the hole
`WF.sortUniq'`.

What the case actually costs is named below.  **Amended in Round 4 (§19):** the sharp upper bound
is `ConvSortInv`, not `SortUniq` — and `BaseUniqChain.sortUniq_iff_convSortInv` makes those the
same hypothesis, so "strictly weaker than `SortUniq`" was unjustified.  No lower bound is
established: `SortNotPropStrong` is one instance (one subject shape, one index) and nothing here
shows it is as strong as `ConvSortInv`. -/

/-- A sort is never a proposition, in `IsDefEqStrong` form.  **Name note:** `PropConv.lean`
already declares a `VEnv.SortNotProp`, over the *stratified* `IsDefEqN` at a fixed index; the two
are different statements and the collision is real, so this one carries the `Strong` suffix.  (It
was caught by importing `Experimental/ConeJoin.lean` into a measurement file — the file builds
standalone either way, which is exactly the failure mode `scripts/dup-names.lean` exists for.) -/
def SortNotPropStrong (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {u : VLevel}, ¬ env.IsDefEqStrong U Γ (.sort u) (.sort u) (.sort .zero)

/-- `SortNotPropStrong` is cheap *given* `SortUniq` — which is the upper bound, not a discharge. -/
theorem sortNotPropStrong_of_sortUniq (hsu : env.SortUniq U) (hΓ : OnCtx Γ (env.IsType U))
    {u : VLevel} (hu : u.WF U) : ¬ env.IsDefEqStrong U Γ (.sort u) (.sort u) (.sort .zero) := by
  intro h
  have h1 : env.HasType U Γ (.sort u) (.sort .zero) := h.defeq
  have h2 : env.HasType U Γ (.sort u) (.sort (.succ u)) := .sortDF hu hu rfl
  have := VLevel.equiv_def.1 (hsu (u := .succ u) (v := .zero) hΓ hu trivial h2 h1) []
  simp [VLevel.eval] at this

/-! ## §16 What the single-link form is worth: it is `ConvPiInvCod` **given `ConvStep2`**

`InjChainStep.ConvC.collapseE` collapses a whole `ConvC` chain to one link given `ConvStep2`, so
the chain form and the single-link form differ by exactly `ConvStep2`.  Compare
`InjChainStep.convPiInv_of_convStep2`, which does the same collapse and then applies `PiInv` —
the `IsDefEqU` form, i.e. the hole.  `PiLinkInvCod` is **strictly weaker input** than `PiInv`:
its premise is an `IsDefEqStrong` at a *syntactic* sort rather than an `IsDefEqU` (more premises,
narrower index) and its conclusion is a `ConvC` chain rather than one `IsDefEq`.

**And the circle is explicit, which is the point.**  `ConvPiFromEntry` follows from
`ConvPiInvCod` with no hypothesis (§1), and `convStep2_of_convSortInv_convPiFromEntry` turns
`ConvSortInv ∧ ConvPiFromEntry` into `ConvStep2`.  So §16 buys `ConvStep2 → ConvStep2` unless
`ConvStep2` arrives from outside the corner.  That is the same verdict row 51 records for the
`SortChainAt` localisation, reached here by a different route, and it is why the single-link
localisation is **not** progress on its own. -/

theorem convPiInvCod_of_convStep2_piLinkInvCod (hcs : ConvStep2 env U)
    (hpl : PiLinkInvCod env U) : ConvPiInvCod env U := by
  intro Γ A B A' B' hΓ h
  match h.collapseE hcs hΓ with
  | .inl eq => cases eq; exact .refl
  | .inr ⟨_, hw⟩ => exact hpl hΓ hw

/-! ## §17 The prerequisite the induction needs, supplied — and the request for the CR stream

§14 says the case analysis of a single Π/Π link is not a reduction: `PiMid ↔ PiLinkInvCod` with
no hypotheses, so only a genuine **induction on the derivation** can make progress, and there the
`trans`-with-a-Π-midpoint sub-case needs the two codomain chains — landing in `A::Γ` and
`A''::Γ` — brought into one context.  No `IsDefEqStrong.defeqDFC` exists in this tree.  It is not
needed: `IsDefEq.defeqDF_l` (`Lemmas.lean`) plus `IsDefEq.strong` gives the chain form link by
link, over `Ordered env` alone.  That is `ConvC.defeqDFC` below, and it is the missing
prerequisite rather than a detail.

With it in hand the request that can be handed to the confluence/`descend` stream is exactly
`PiMidNonPi` together with `SortNotPropStrong` (§15), plus the domain half `PiLinkInvDom`:

* `PiMidNonPi` is Π-shape descent and nothing else: *a term sitting between two Π-shapes at one
  sort, and itself not syntactically a Π, has its two neighbours' codomains chain-linked.*  It is
  what "a term convertible to a Π reduces to a Π" buys, stated with no reduction relation, no
  subject, no typing judgment and no level arithmetic in it.
* `SortNotPropStrong` is the `proofIrrel` case and is a sort/sort inversion.
* `PiLinkInvDom` is needed only to *use* `ConvC.defeqDFC` in the Π-midpoint sub-case.

**Explicitly not claimed:** that these three plus `VEnv.WF` close `PiLinkInvCod`.  That induction
is not done here, and nothing in this file depends on it — every theorem above is independent of
§17 except `ConvC.defeqDFC`, which is a theorem in its own right. -/

/-- **Chain transport across a one-entry context conversion**, one `IsDefEq.defeqDF_l` per link,
over `Ordered env`. -/
theorem ConvC.defeqDF_l (henv : Ordered env) {Γ : List VExpr} {A A' : VExpr} {u : VLevel}
    (hΓ : CtxStrong env U Γ) (hA : env.IsDefEqStrong U Γ A A' (.sort u))
    {B B' : VExpr} (h : ConvC env U (A::Γ) B B') : ConvC env U (A'::Γ) B B' := by
  have hΓ' : OnCtx (A'::Γ) (env.IsType U) := ⟨hΓ.defeq, _, hA.defeq.hasType.2⟩
  induction h with
  | refl => exact .refl
  | step hl _ ih => exact .step ((hA.defeq.defeqDF_l henv hl.defeq).strong henv hΓ') ih

/-- **…and across a whole domain chain.**  The lemma the Π-midpoint sub-case of an induction on
`PiLinkInvCod` needs, and the one the tree did not have. -/
theorem ConvC.defeqDFC (henv : Ordered env) {Γ : List VExpr} (hΓ : CtxStrong env U Γ)
    {A A' : VExpr} (hA : ConvC env U Γ A A') {B B' : VExpr} :
    ConvC env U (A::Γ) B B' → ConvC env U (A'::Γ) B B' := by
  induction hA with
  | refl => exact id
  | step hl _ ih => exact fun h => ih (h.defeqDF_l henv hΓ hl)

/-- **Π-shape descent at a non-Π midpoint, at one sort.**  The request. -/
def PiMidNonPi (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {A B A' B' M : VExpr} {u : VLevel}, CtxStrong env U Γ →
    (∀ D E, M ≠ .forallE D E) →
    env.IsDefEqStrong U Γ (.forallE A B) M (.sort u) →
    env.IsDefEqStrong U Γ M (.forallE A' B') (.sort u) → ConvC env U (A::Γ) B B'

/-- The domain half of the single-link statement. -/
def PiLinkInvDom (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {A B A' B' : VExpr} {u : VLevel}, CtxStrong env U Γ →
    env.IsDefEqStrong U Γ (.forallE A B) (.forallE A' B') (.sort u) → ConvC env U Γ A A'

/-- `PiMidNonPi` is bounded above by the single-link statement, so the request is not stronger
than what it is being asked to supply. -/
theorem PiLinkInvCod.piMidNonPi (H : PiLinkInvCod env U) : PiMidNonPi env U :=
  fun hΓ _ h1 h2 => H hΓ (h1.trans h2)

/-- Non-vacuity of the *restriction*: §13's midpoint is `.app`-headed, hence not a Π, so
`PiMidNonPi`'s side condition is satisfiable at a firing instance — the restriction does not
empty the statement. -/
theorem piMidNonPi_side_fires : ∀ D E, appMid ≠ .forallE D E := by rintro D E ⟨⟩

/-! ## §18 CORRECTION: `WF.noPiLhs` was already in the tree

`DeclRules.WF.instL_lhs_ne_forallE` (`Theory/Typing/DeclRules.lean:239`) is §10's statement
character for character — "no rule rewrites a Π-type" — and `WF.instL_lhs_ne_sort` (`:234`) is its
sort analogue.  Both are proved from `WF.defeq_isDeclRule`/`IsDeclRule.lhs_shape`; §10 reached the
Π one independently through `PatternRules.RuleShape`.  **So §10 re-proved an existing theorem**,
and the interesting content of Round 2 is §8 (`not_wf_roguePiEnv`) alone.  `noPiLhs_of_declRules`
records the identification so the duplication is visible rather than latent; the two routes are
kept because `RuleShape` and `IsDeclRule` are different decompositions of the same fact and
nothing in the tree relates them. -/

theorem noPiLhs_of_declRules {env : VEnv} (h : VEnv.WF env) {df : VDefEq} (hdf : env.defeqs df) :
    NoPiLhs df := fun ls A B => h.instL_lhs_ne_forallE hdf ls A B

/-- The sort analogue of `WF.piPi_extra_closed`, from the sort half of `DeclRules.lean`: **the
`extra` case of a sort/sort link is closed by well-formedness**, exactly as the `extra` case of a
Π/Π link is.  So `VEnv.WF` buys one case on each side and the same case on each side. -/
theorem WF.sortSort_extra_closed {env : VEnv} (h : VEnv.WF env) {df : VDefEq}
    (hdf : env.defeqs df) {ls : List VLevel} {a b : VLevel} :
    ¬ (df.lhs.instL ls = .sort a ∧ df.rhs.instL ls = .sort b) :=
  fun ⟨hl, _⟩ => h.instL_lhs_ne_sort hdf ls a hl

/-! ## §19 Task 1: `SortNotPropStrong` is **not** free at `VEnv.WF` — it costs the *sort half*

The sharp upper bound is not `SortUniq` but `ConvSortInv`, and the route is `peelChain`: a
`true`-level typing `Γ ⊢ .sort u : .sort .zero` peels to the base rule `HasTypeStrong.sort'`,
which pins the base type to `.sort (.succ l')` with `l' ≈ u`, plus a chain
`ConvC Γ (.sort (.succ l')) (.sort .zero)`.  `ConvSortInv` turns that chain into
`.succ l' ≈ .zero`, which `VLevel.eval` refutes.

So **the `proofIrrel` case of the Π side costs the sort side.**  `BaseUniqChain`'s
`sortUniq_iff_convSortInv` makes `ConvSortInv` and `SortUniq` the same hypothesis, and
`InjChainLower.sortChainAt_bvar_iff_convSortInv` makes it the corner's sort residual at `.bvar 0`.
`VEnv.WF` does not touch it: §18 closes the `extra` case of a sort/sort link and nothing else, and
§20 shows the remaining `trans` case is the whole statement — the same shape as the Π side.

That answers question 1: **no**, `SortNotPropStrong` is not a corollary of well-formedness.
`WF.instL_lhs_ne_sort` is the right lemma and it does close the `extra` route, but the `extra`
route was never the residual on either side.

No lower bound is established: `SortNotPropStrong` is a single instance (one subject shape, one
index) and nothing here shows it is *as strong as* `ConvSortInv`. -/

theorem sortNotPropStrong_of_convSortInv (hsi : ConvSortInv env U) {Γ : List VExpr}
    (hΓ : CtxStrong env U Γ) {u : VLevel} :
    ¬ env.IsDefEqStrong U Γ (.sort u) (.sort u) (.sort .zero) := by
  intro h
  obtain ⟨B₀, hb, hc⟩ := h.hasType'.1.peelChain
  cases hb with
  | sort' h1 h2 h3 =>
    have := VLevel.equiv_def.1 (hsi hΓ hc) []
    simp [VLevel.eval] at this

/-- The level fact the `sortDF` route dies on, and the reason the *rule* routes to refuting
`SortNotPropStrong` at a well-formed environment are all closed: `sortDF` forces the two levels
equivalent, `extra` is closed by §18, and everything else is the `trans` wall of §20. -/
theorem succ_not_equiv_zero (l : VLevel) : ¬ (VLevel.succ l ≈ .zero) := by
  intro h
  have := VLevel.equiv_def.1 h []
  simp [VLevel.eval] at this

/-! ## §20 Four for four: the sort side localises no better than the Π side

`piMid_iff_piLinkInvCod` (§14) showed the Π/Π `trans` case *is* the single-link statement.  The
sort side is identical, for the identical reason — `IsDefEqStrong.trans` is a rule — and
`ConvC.collapseE` prices the chain form the same way.  So the standing rule ("test a localisation
against its own target before building on it") holds on both halves, and the score is four. -/

/-- Sort injectivity for a **single** `IsDefEqStrong` link. -/
def SortLinkInv (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {u v w : VLevel}, CtxStrong env U Γ →
    env.IsDefEqStrong U Γ (.sort u) (.sort v) (.sort w) → u ≈ v

/-- The same, written as the `trans` case. -/
def SortMid (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {u v w : VLevel} {M : VExpr}, CtxStrong env U Γ →
    env.IsDefEqStrong U Γ (.sort u) M (.sort w) →
    env.IsDefEqStrong U Γ M (.sort v) (.sort w) → u ≈ v

/-- **The collapse test on the sort side, FAILING.**  Both directions, no hypotheses. -/
theorem sortMid_iff_sortLinkInv : SortMid env U ↔ SortLinkInv env U := by
  constructor
  · intro H Γ u v w hΓ h
    exact H hΓ h (h.symm.trans h)
  · intro H Γ u v w M hΓ h1 h2
    exact H hΓ (h1.trans h2)

/-- And the chain form differs from the link form by exactly `ConvStep2`, as on the Π side. -/
theorem convSortInv_of_convStep2_sortLinkInv (hcs : ConvStep2 env U) (hsl : SortLinkInv env U) :
    ConvSortInv env U := by
  intro Γ u v hΓ h
  match h.collapseE hcs hΓ with
  | .inl eq => cases eq; rfl
  | .inr ⟨_, hw⟩ => exact hsl hΓ hw

/-! ## §21 `PiLinkInvDom`, priced

It **is** row 53's dead conjunct in single-link guise, as an *output*: `ConvPiInv.piLinkInvDom` is
`.1` of the chain form, and every consumer in the tree takes `.2`.  Neither half implies the
other and nothing here makes it strictly weaker than `PiLinkInvCod`; they are the two projections
of the same single-link inversion.

**Remark, not a hinge** (the induction it refers to is not written, so nothing may depend on
this): where it is *not* dead is as an **input**.  §17's Π-midpoint sub-case has the two codomain
chains landing in `A::Γ` and `A''::Γ`, and `ConvC.defeqDFC` needs a domain chain to move between
them.  Strengthening the conclusion to both contexts at once — the shape `Injectivity.RigidPiUniq`
uses — does not remove the need: from `ConvC (A::Γ) B B''`, `ConvC (A''::Γ) B B''`,
`ConvC (A''::Γ) B'' B'` and `ConvC (A'::Γ) B'' B'` one still cannot reach `ConvC (A::Γ) B B'`
without moving `B'' ⇝ B'` from `A''::Γ` into `A::Γ`.  So a domain link is an ingredient of any
proof of the codomain half by this route, which is a different status from "dead code" and worth
not conflating with it. -/

theorem ConvPiInv.piLinkInvDom (H : ConvPiInv env U) : PiLinkInvDom env U :=
  fun hΓ h => (H hΓ (.one h)).1

theorem ConvPiInv.piLinkInvCod (H : ConvPiInv env U) : PiLinkInvCod env U :=
  fun hΓ h => (H hΓ (.one h)).2

/-! ## §22 The sort side's residual, isolated by a real induction — and `extra` discharged inside it

§19 made `ConvSortInv` the corner's single residual (the Π side's `proofIrrel` case consumes it).
This section runs the induction that §17 could not run on the Π side, and the reason it goes
through is a structural asymmetry worth stating on its own:

> **the sort side's conclusion is a level equation, so it carries no context.**

The Π side's conclusion `ConvC (A::Γ) B B'` is indexed by the binder, which is why its
`trans`-with-a-Π-midpoint sub-case needs `ConvC.defeqDFC` and a domain half (§17, §21).  Here
`a ≈ b` mentions neither `Γ` nor the type index, so `symm` composes by `Eq.symm`, `trans` with a
*sort* midpoint composes by `Eq.trans`, and — the case that matters — `defeqDF` is free: the index
changes and the conclusion does not mention it.  Nothing has to be transported.

`sortLinkInv_of_wf` is the result.  Every rule-level case is closed inside the proof:

| constructor | how it closes |
| --- | --- |
| `bvar`, `constDF`, `appDF`, `lamDF`, `forallEDF`, `beta`, `eta` | endpoint shape: not a `.sort` |
| `sortDF` | its own side condition **is** `a ≈ b` |
| `extra` | `DeclRules.WF.instL_lhs_ne_sort` — no rule rewrites a sort |
| `symm`, `defeqDF` | induction hypothesis, unchanged |
| `trans`, midpoint a `.sort` | induction hypothesis twice, `Eq.trans` |
| `trans`, midpoint **not** a `.sort` | `SortMidNonSort` — **open** |
| `proofIrrel` | `SortNotProof` — **open** |

So the answer to "say exactly which cases remain open" is a theorem rather than prose: **exactly
two**, and both are *descent* statements about a term that is not a sort, not statements about
rules.  That is also the answer to "is `ConvSortInv` refutable at a `VEnv.WF` environment": every
rule-level route into a sort/sort link is closed by the table above, so a rogue `VEnv.WF` witness
would have to come through one of the two open cases — i.e. it would have to exhibit a term that
converts to two `≉` sorts, which is a non-confluence of Lean's own rule set rather than an
artefact of the environment.  **No such witness is claimed and none was found.** -/

/-- The `trans` case with a midpoint that is not a syntactic sort.  Note there is no level index
and no context conversion: both halves sit at one type index `A`, which the conclusion ignores. -/
def SortMidNonSort (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {a b : VLevel} {M A : VExpr}, (∀ c, M ≠ .sort c) →
    env.IsDefEqStrong U Γ (.sort a) M A → env.IsDefEqStrong U Γ M (.sort b) A → a ≈ b

/-- The `proofIrrel` case: **a sort is not a proof.**  Compare
`Injectivity.not_isProof_of_defeqU_sort`, which proves this from `WF.sortUniq'`, i.e. from the
hole; here it is a named residual instead. -/
def SortNotProof (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {p : VExpr} {a : VLevel},
    env.IsDefEqStrong U Γ p p (.sort .zero) → env.IsDefEqStrong U Γ (.sort a) (.sort a) p → False

theorem sortLinkInv_of_wf (henv : VEnv.WF env) (hm : SortMidNonSort env U)
    (hp : SortNotProof env U) {Γ : List VExpr} {e1 e2 A : VExpr}
    (h : env.IsDefEqStrong U Γ e1 e2 A) :
    ∀ {a b : VLevel}, e1 = .sort a → e2 = .sort b → a ≈ b := by
  induction h with
  | bvar _ _ _ => exact fun h => absurd h nofun
  | symm _ ih => exact fun h1 h2 => (ih h2 h1).symm
  | @trans _ _ M _ _ hl hr ihl ihr =>
    intro a b ea eb; subst ea; subst eb
    by_cases hs : ∃ c, M = .sort c
    · obtain ⟨c, rfl⟩ := hs; exact (ihl rfl rfl).trans (ihr rfl rfl)
    · exact hm (fun c e => hs ⟨c, e⟩) hl hr
  | sortDF _ _ h3 => exact fun ea eb => by cases ea; cases eb; exact h3
  | constDF _ _ _ _ _ _ _ _ => exact fun h => absurd h nofun
  | appDF _ _ _ _ _ _ _ => exact fun h => absurd h nofun
  | lamDF _ _ _ _ _ _ _ => exact fun h => absurd h nofun
  | forallEDF _ _ _ _ _ => exact fun h => absurd h nofun
  | defeqDF _ _ _ _ ih2 => exact ih2
  | beta _ _ _ _ _ _ _ _ => exact fun h => absurd h nofun
  | eta _ _ _ _ _ _ _ _ => exact fun h => absurd h nofun
  | proofIrrel h1 h2 _ _ _ _ =>
    intro a b ea eb; subst ea
    exact absurd (hp h1 h2) not_false
  | extra h1 _ _ _ _ _ _ _ _ =>
    exact fun ea _ => absurd ea (henv.instL_lhs_ne_sort h1 _ _)

/-- **The sort side's single-link statement, from two descent residuals and `VEnv.WF`.** -/
theorem sortLinkInv_of (henv : VEnv.WF env) (hm : SortMidNonSort env U)
    (hp : SortNotProof env U) : SortLinkInv env U :=
  fun _ h => sortLinkInv_of_wf henv hm hp h rfl rfl

/-- **…and hence the corner's single residual, given the chain collapse.**  Composed with §20. -/
theorem convSortInv_of (henv : VEnv.WF env) (hcs : ConvStep2 env U) (hm : SortMidNonSort env U)
    (hp : SortNotProof env U) : ConvSortInv env U :=
  convSortInv_of_convStep2_sortLinkInv hcs (sortLinkInv_of henv hm hp)

/-! ### The collapse test, and this time it **PASSES**

`SortMidNonSort` quantifies over an **arbitrary** type index `A`, not over `.sort w`.  That is
forced: the induction's conclusion must not mention the index — that is exactly what makes
`defeqDF` free — so the `trans` case inherits an arbitrary `A`.  The right target to measure
against is therefore the index-free single-link statement `SortLinkInvU`, and there:

* `SortLinkInvU.sortMidNonSort` — the target implies the residual, free, one `IsDefEqStrong.trans`;
* **the converse has no route.**  A single link `.sort a ≡ .sort b : A` offers no *non-sort*
  midpoint, and the sort-midpoint case of the `trans` node is supplied inside §22's induction by
  the induction hypothesis — which only the induction has.

So after four collapses this localisation is **not** one: restricting the midpoint to non-sorts
loses content, and `sortLinkInvU_of` is a genuine reduction rather than a restatement.  The
structural reason is the one stated above the table — the sort side's conclusion is a level
equation and carries no context, so the Π side's blocker (`ConvC.defeqDFC` plus a domain half,
§17/§21) has no analogue here.

**And `SortNotProof` is not a new obligation.**  It is `Injectivity.not_isProof_of_defeqU_sort`
at `e = .sort a` — `IsProof env U Γ e := ∃ p, HasType Γ p (.sort .zero) ∧ HasType Γ e p`
(`Injectivity.lean:699`) — which that file already proves, from `WF.sortUniq'`, i.e. from the hole
`SortUniq`.  Since `sortUniq_iff_convSortInv` makes `SortUniq` the very statement being reduced,
`SortNotProof` is free *given the target* and adds nothing to the residual.  (Stated as a citation,
not re-proved here: the bound runs through a `sorryAx`-carrying declaration, so it is deliberately
not imported.)

**Net:** at `VEnv.WF` and modulo `ConvStep2`, the corner's single residual `ConvSortInv` reduces to
**sort-descent at a non-sort midpoint**, `SortMidNonSort` — the sort analogue of §17's
`PiMidNonPi`, and the one of the two that actually reduces. -/

/-- The single-link statement with **no constraint on the type index** — the form §22's induction
actually proves, and the form `SortMidNonSort` must be measured against. -/
def SortLinkInvU (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {a b : VLevel} {A : VExpr},
    env.IsDefEqStrong U Γ (.sort a) (.sort b) A → a ≈ b

theorem SortLinkInvU.sortLinkInv (H : SortLinkInvU env U) : SortLinkInv env U := fun _ h => H h

/-- The target implies the residual — the only direction that holds. -/
theorem SortLinkInvU.sortMidNonSort (H : SortLinkInvU env U) : SortMidNonSort env U :=
  fun _ h1 h2 => H (h1.trans h2)

theorem sortLinkInvU_of (henv : VEnv.WF env) (hm : SortMidNonSort env U)
    (hp : SortNotProof env U) : SortLinkInvU env U :=
  fun h => sortLinkInv_of_wf henv hm hp h rfl rfl

/-- Degenerate check: at the empty environment `SortMidNonSort`'s premise is inhabited — §13's
β-redex `appMid` is not a syntactic sort and sits between two conversions at one index — so the
non-sort side condition does not empty the statement. -/
theorem sortMidNonSort_side_fires : ∀ c, appMid ≠ .sort c := by rintro c ⟨⟩

/-! ## §23 Task 2: priced against the reference — `ConvSortInv` **presupposes confluence**, and the
critical path has **one** prerequisite, not two

`~/lean-type-theory/unique.tex` proves uniqueness of typing, and its structure answers the
question exactly.  Citations are file:line in that document.

**(a) The reference cannot prove it before Church–Rosser, and says so.**  `unique.tex:8`: *"we
cannot yet prove this theorem.  The critical step is the Church-Rosser theorem … the Church-Rosser
theorem will require that this theorem is true, and we will be caught in a circularity unless we
are careful about the claims."*  The circularity is managed by the alternation index `⊢ₙ`
(`:11–16`), and `sec:kappa`'s opening note (`:64`) makes the direction explicit: *"importantly, we
will assume that `⊢ₙ` has unique typing."*  So CR at `n+1` consumes unique typing at `n`.

**(b) `ConvSortInv` *is* clause (1) of the reference's "definitional inversion"** (`:31–35`):
`Γ ⊢ₙ U_ℓ ≡ U_ℓ' ⟹ ℓ ≡ ℓ'`.  `thm:utype` (`:40`) derives unique typing *from* definitional
inversion, and `sortUniq_iff_convSortInv` makes the tree's `ConvSortInv` and `SortUniq` the same
hypothesis.  Definitional inversion at `n+1` (`thm:1dinv`, `:259`) is proved **only** by applying
`thm:ckappa` — completeness of κ-reduction (`:242`) — whose transitivity is *"the Church-Rosser
property implies it is also transitive"* (`:240`), and the top-level induction (`:283–287`) closes
`n+1` by "all the results of `sec:church_rosser` follow".  **There is no route in the reference to
clause (1) that avoids confluence.**  Answer to the second question: it presupposes confluence.

**(c) §22's two residuals are the reference's two cases, with the reference's two discharges.**
`thm:1dinv` clause (1) splits exactly as §22's table does:

| §22's open case | the reference's discharge (`:263`) |
| --- | --- |
| `SortMidNonSort` (`trans`, non-sort midpoint) | *"there are no `⇝_κ` reductions from `U_ℓ`"* — κ-normality of a universe, **plus CR** |
| `SortNotProof` (`proofIrrel`) | *"by unique typing at `n`, `P ≡ U_{SSℓ}`, so `0 ≡ SSℓ`, a contradiction"* — the **stratification**, not CR |

Independent confirmation that the case inventory is right, and it says which residual needs what.

**(d) One prerequisite, not two.**  Clause (2) (`:267`, the Π case) and clause (3) (`:274`,
sort/Π disjointness) are discharged by the *same* two moves: no `⇝_κ` reductions from a `∀` except
the compatibility rules, plus `proofIrrel` killed by unique typing at `n`.  So this tree's
`SortMidNonSort`, `PiMidNonPi` (§17) and `RigidSortPiDisj` are **three instances of one fact** —
*a κ-normal rigid head has no reduct of another shape* — together with CR.  That is a cleaner
statement of the critical path than "two fronts": the corner has one prerequisite, confluence,
and three consumers of it.

**(e) A caveat that is already in this tree, cited not re-derived.**  The reference's discharge of
the `proofIrrel` cases runs through unique typing at `n`, i.e. through `thm:utype` (`:40–54`),
whose application case uses closure of `⊢ₙ`-conversion under instantiation — `unique.tex:51`.
`Theory/Typing/SubstCRefute.lean` **refutes** that step (`VEnv.SubstC`, false at `n = 1` over
`∅`), so the reference's stratified route to `SortNotProof` is not available here as written.  The
CR-side residual (`SortMidNonSort`, `PiMidNonPi`) is unaffected by that refutation.

Nothing in this section is a Lean statement; it is a reading of the blueprint, and every claim in
it is a quotation with a line number so it can be checked without trusting the reading. -/

end VEnv
end Lean4Lean

section Audit
open Lean4Lean.VEnv
#print axioms Lean4Lean.VEnv.ConvPiInvCod.convPiFromEntry
#print axioms Lean4Lean.VEnv.ordered_roguePiEnv
#print axioms Lean4Lean.VEnv.rogue_link1
#print axioms Lean4Lean.VEnv.rogue_link2
#print axioms Lean4Lean.VEnv.rogue_piPi
#print axioms Lean4Lean.VEnv.convPiFromEntry_forces
#print axioms Lean4Lean.VEnv.not_convPiFromEntry_of_sep
#print axioms Lean4Lean.VEnv.not_convPiInvCod_of_sep
#print axioms Lean4Lean.VEnv.not_piChainAt_bvar_of_sep
#print axioms Lean4Lean.VEnv.not_convPiInvCodInhab_of_sep
#print axioms Lean4Lean.VEnv.SortPiDisjRaw.convSortPiDisj
#print axioms Lean4Lean.VEnv.not_convPiFromEntry_of_convSortPiDisj
#print axioms Lean4Lean.VEnv.not_convPiFromEntry_of_sortPiDisjRaw
#print axioms Lean4Lean.VEnv.not_convPiInvCod_of_convSortPiDisj
#print axioms Lean4Lean.VEnv.not_piChainAt_bvar_of_convSortPiDisj
#print axioms Lean4Lean.VEnv.not_convPiInvCodInhab_of_convSortPiDisj
#print axioms Lean4Lean.VEnv.rogue_rules_share_lhs
#print axioms Lean4Lean.VEnv.rogue_fires
#print axioms Lean4Lean.VEnv.not_defEqHeadsUnique_roguePiEnv
#print axioms Lean4Lean.VEnv.not_wf_roguePiEnv
#print axioms Lean4Lean.VEnv.defEqHeadsUnique_empty
#print axioms Lean4Lean.VEnv.rogue_decl_wf
#print axioms Lean4Lean.VEnv.wf_wfPiEnv
#print axioms Lean4Lean.VEnv.wfPiEnv_link
#print axioms Lean4Lean.VEnv.instL_ne_forallE
#print axioms Lean4Lean.VEnv.mkLams_ne_forallE
#print axioms Lean4Lean.VEnv.RuleShape.noPiLhs
#print axioms Lean4Lean.VEnv.WF.noPiLhs
#print axioms Lean4Lean.VEnv.noPiLhs_fires
#print axioms Lean4Lean.VEnv.not_noPiLhs_piRule
#print axioms Lean4Lean.VEnv.WF.piPi_extra_closed
#print axioms Lean4Lean.VEnv.piChainAt_bvar_iff_convPiFromEntry_wf
#print axioms Lean4Lean.VEnv.convStep2_of_convSortInv_convPiFromEntry_wf
#print axioms Lean4Lean.VEnv.empty_wf
#print axioms Lean4Lean.VEnv.convStep2At_of_sort_eq
#print axioms Lean4Lean.VEnv.appMid_isApp
#print axioms Lean4Lean.VEnv.midpoint_app_at_empty
#print axioms Lean4Lean.VEnv.piMid_iff_piLinkInvCod
#print axioms Lean4Lean.VEnv.sortNotPropStrong_of_sortUniq
#print axioms Lean4Lean.VEnv.convPiInvCod_of_convStep2_piLinkInvCod
#print axioms Lean4Lean.VEnv.ConvC.defeqDF_l
#print axioms Lean4Lean.VEnv.ConvC.defeqDFC
#print axioms Lean4Lean.VEnv.PiLinkInvCod.piMidNonPi
#print axioms Lean4Lean.VEnv.piMidNonPi_side_fires
#print axioms Lean4Lean.VEnv.noPiLhs_of_declRules
#print axioms Lean4Lean.VEnv.WF.sortSort_extra_closed
#print axioms Lean4Lean.VEnv.sortNotPropStrong_of_convSortInv
#print axioms Lean4Lean.VEnv.succ_not_equiv_zero
#print axioms Lean4Lean.VEnv.sortMid_iff_sortLinkInv
#print axioms Lean4Lean.VEnv.convSortInv_of_convStep2_sortLinkInv
#print axioms Lean4Lean.VEnv.ConvPiInv.piLinkInvDom
#print axioms Lean4Lean.VEnv.ConvPiInv.piLinkInvCod
#print axioms Lean4Lean.VEnv.sortLinkInv_of_wf
#print axioms Lean4Lean.VEnv.sortLinkInv_of
#print axioms Lean4Lean.VEnv.convSortInv_of
#print axioms Lean4Lean.VEnv.SortLinkInvU.sortLinkInv
#print axioms Lean4Lean.VEnv.sortLinkInvU_of
#print axioms Lean4Lean.VEnv.SortLinkInvU.sortMidNonSort
#print axioms Lean4Lean.VEnv.sortMidNonSort_side_fires
end Audit
