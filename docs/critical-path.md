# `kernel_sound`'s critical path

*Measured 2026-08-31. Reproduce with `~/.elan/bin/lake env lean scripts/kernel-sound-path.lean`.*

## Read this first: current state (2026-08-31, end of day)

**The body of this file is the original measurement plus five dated corrections.** Each
correction is worth reading for *how* the picture was wrong, but the headline "2 hypotheses +
9 holes" below is superseded. The current state is:

| | state |
| --- | --- |
| **1.** Kernel Arena | **MET** — 185 correct, 6 `either`, 0 incorrect. Holds at every commit today; the last commit touching the executable is `eddc0ff`. |
| **2.** `kernel_sound` | **NOT met.** Guard 2: `proof INCOMPLETE: sorryAx present`. Census **14**. |

What actually blocks condition 2, in the shape it really has:

1. **The typing holes**, which are ordinary open proofs and the bulk of the work. Counts as of the
   end of 2026-08-31, after `TrProj.uniq` closed: `forallE_inv_stratified` **534**,
   `rigidShapeUniqNS` **311**, `IsDefEqU.weakN_iff` **198** (narrowed to
   `TransStrengtheningNarrowNeutral`), `NormalEq.descend` **145**, `TrProj.weak'_inv` **30**.
   Note the counts *rose* while the census fell 14 → 13: closing `TrProj.uniq` routed its 94
   consumers through `projData_uniq` into these four instead of stopping at its own `sorry`. The
   blocking is more concentrated, not reduced — which is the honest reading of that census drop.
2. **The nested-inductive route — no longer blocked by a *false* statement, but still open.**
   As of end-of-day 2026-08-31, none of `addInductR_ordered'`'s three obligations is refuted: (A)
   was repaired by substituting at the *declaration sites* (not inside `typeR` — see ledger row 36
   for why the obvious move was unsound), and (C) by making `addIndRulesR` fold the *substituted*
   rules. The witness `nfnAuxDirty`, which refuted (A) and then (C), now refutes nothing.

   **What remains, and it is more than one item — an earlier version of this file said closing the
   rules fold would make the nested `AddInduct` reachable, which was wrong:**
   `addInductR_ordered` and `_ordered'` were always theorems; they are the *factoring*, not the
   content. Open in general:
   * **(A)** above `np = 0` — a β-gap, on the telescope-defeq route (`ctorConstsCR_wf_of_substC'`).
     Closed unconditionally for `np = 0` (`ctorConstsCR_wf_of_np_zero'`).
   * **(C)** in general — the head-by-head equation over
     `iotaCtx`/`iotaLhs`/`iotaLam`/`ihValues`/`iotaType`. Strictly harder than (A)'s: `csubst`'s
     domain holds the companion's *constructor* and *recursor* names, outside `D.blockNames`, so no
     `NoBlock` clause of `VIndCtor.WF` covers them, and the `csubstList` lookup lemmas do not exist.
   * **(B)** — a strict *sub-problem* of (C), since `iotaCtxR` splices `motivesR ++ minorsR`. The
     one ingredient both need is a `ctorApp' → ctorAppR` head equation mirroring
     `substC_tyApp_eq_tyAppR_map`.
   * **`VIndRestore.KeysFree`** must stop being a hypothesis — either it joins `AddNestedStep`'s
     premises (cheap for the checker, since `mkAuxRecNameMap` renames out of the `_nested`
     namespace) or it becomes a `Faithful` clause. It is **not** derivable from
     `Faithful` + `OwnId` + freshness: a companion member's own name is declared by no step.
   `addInductR_ordered'`'s `hctors` fails under the premises `VDecl.WF.inductNested` actually has
   (`nfnAuxDirty_refutation`, hypothesis-free), because `VIndCtor.typeR` under-restores: it copies
   `C.params` and non-recursive field types verbatim, and those are only *definitionally*
   block-free. No strengthening of `Faithful`/`Built`/`Canonical`/`OwnId` repairs it — they all
   constrain the *companion* members, and the failing constructor is *user-written*. The fix is a
   **new conjunct** (`VIndCtor.RestoreClean`), or redefining `typeR` as the substitution, which is
   the faithful model of the implementation's whole-expression `restoreNested`.
   Proved meanwhile: (A) in general for parameterless blocks, with the parameterful case reduced to
   exactly `D.np` β-steps per companion occurrence. (B)/(C) additionally need their cleanliness
   condition restated against `csubst`, not `csubstTy`. `docs/vacuity-ledger.md` rows 26–28.
3. **The `AddInduct` flip**, which is *two* flips (Correction 5). The non-nested one is available
   and is a decision (census 14 → 17, partial result). The nested one needs item 2 first.
4. **Statements that are false rather than open** — `addDecl.WF`'s `inductDecl` branch,
   `foldAddDecl_tr`, `Bridge.AddDeclWF` — which must be *re-derived*, never assumed.
   `docs/vacuity-ledger.md` is the registry, 22 statements measured, and §4 records how assuming
   one of them would make Guard 2 print "proof COMPLETE" over nothing.

The `False`-witness half of the soundness statement is **finished**: `hasType_falseProp`'s cone
is 7244 declarations with zero holes.

## Stop-condition status (original measurement)

| Condition | State |
|---|---|
| **1.** Kernel Arena: `uv run lka.py run --checker lean4lean-local`, every non-`either` test correct | **MET** — measured 2026-08-31 at commit `43d6d25`: **185 correct, 6 `either`, nothing incorrect** |
| **2.** `Lean4Lean.kernel_sound` proven (Guard 2 prints "proof COMPLETE") | **NOT met** — 2 hypotheses + 9 holes, enumerated below (**superseded**; see the block above) |

CLAUDE.md requires both **on the same commit**, so the goal is not reached. Condition 1 is not
"done" in a way that can be banked either: it must still hold at whatever commit finally closes
condition 2, and the `AddInduct` flip (re-priced in the addendum) is exactly the kind of change
that could disturb it. Re-run the Arena after any change to the executable checker.

Until now the project's only global progress number was the sorry census (`TOTAL 14`). That
counts holes in the census import cone, which is the right *global* figure but says nothing
about which holes actually block stop-condition 2. This document answers that, for the first
time, by measurement rather than argument.

`Lean4Lean/Verify/SoundnessAssembly.lean` proves `Bridge.kernel_sound_of`: the frozen
`kernel_sound` statement, verbatim, modulo two explicit hypotheses. `scripts/mirror-defeq.lean`
machine-checks that the frozen goal is closed by `exact` from it — and that `Verify/Bridge.lean`'s
four mirrored definitions really are equal to the frozen ones by `rfl`, which had been asserted
in a docstring and never checked.

## The path: 2 hypotheses + 9 holes

Hypotheses (the cone cannot see these — they are premises, not dependencies):

| # | Hypothesis | Owner |
|---|---|---|
| H1 | `Bridge.PreludeBridge stdPrelude` | inductive-declaration workstream: `AddInduct` has no constructors, so `TrEnv` provably contains no inductive at all, while `stdPrelude` is mostly `.inductDecl`s; plus a `foldAddDecl`-level invariant pinning the first `pre.length` steps |
| H2 | `Consistent 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰 → leanTTConsistent` | model workstream: the outer recursion building `ModelData.cnst` and `Coherent` along the declaration list (`docs/soundness-ledger.md` — the step lemmas and soundness are done) |

Holes, all nine of which enter through `Bridge.addDeclWF`.

**Every figure in this table is a pre-2026-09-01 undercount** — `scripts/sorry-census.lean` skipped
internal names while *building* the reverse-reachability graph, so a user reaching a hole through one
of its own equation lemmas was invisible (ledger §0). Current figures at the last quiescent run are
in the right-hand column; `TrProj.uniq` has since closed.

| Hole | Old (broken graph) | Current |
|---|---|---|
| `addDecl.WF` | 1 | **8** |
| `TypeChecker.Inner.inferProj.WF` | 0 | **68** |
| `TypeChecker.Inner.isDefEqUnitLike.WF` | 1 | **68** |
| `TypeChecker.Inner.tryEtaStructCore.WF` | 2 | **69** |
| `TrProj.weak'_inv` | 29 | **88** |
| `TrProj.uniq` | 93 | *closed* |
| `VEnv.IsDefEqU.weakN_iff` | 134 | **296** |
| `VEnv.WF.rigidShapeUniqNS` | 224 |
| `VEnv.IsDefEqU.forallE_inv_stratified` | 515 |

`Bridge.hasType_falseProp` — the transport of the `False` witness from the kernel environment to
the abstract one — has a cone of 7244 declarations and **zero** holes. The `False` side of the
theorem is finished; every remaining obligation is on the checker-refinement side or in the two
hypotheses.

## What is *not* on the path

Five of the 14 census holes are outside `kernel_sound_of`'s cone. Two of them for real reasons,
three for reasons that must not be misread as slack:

- `kernel_complete` — genuinely not blocking; its own doc comment says "not part of the binding
  goal".
- `VIndRecArg.exists_indep` — 0 transitive users, blocks nothing that exists.
- `kernel_sound` — the target itself.
- `leanTT_equiconsistent_zfc_omega_inaccessibles` — off the *cone* only because H2 is taken as a
  hypothesis rather than derived from the theorem. It is squarely on the path. A cone measurement
  can never see a hypothesis, which is exactly why H1 and H2 are tabulated separately above.
- `NormalEq.descend` (47 users) — off-cone because the results it supplies (`ParRed.weakN_inv`,
  and confluence generally) exist to *prove* `IsDefEqU.weakN_iff`, which is itself still a
  `sorry`; a hole's cone is empty, so its intended suppliers look unreachable. `descend` re-enters
  the cone the moment `weakN_iff` stops being a hole. Do not read this row as "the confluence
  work is idle".

## Consequences for sequencing

1. The three low-user checker `.WF` holes (0, 1, 2 users) are each on the critical path despite
   tiny user counts. User count measures *blast radius*, not *necessity*: `addDecl.WF` has one
   user and is unavoidable. Both numbers matter and they answer different questions.
2. The injectivity corner (`forallE_inv_stratified`, `rigidShapeUniqNS`) and the weakening node
   (`weakN_iff`) are on the path, so the strengthening/confluence programme is load-bearing, not
   optional. Per `Theory/Typing/RigidNodeCircle.lean`, `forallE_inv_stratified ≈ SortUniq` holds
   only *given* `PiInv` — so that is two fronts, not one hole seen twice.
3. Nothing on the path is unowned: H1 and H2 have named workstreams, and the nine holes are all
   either checker-side or in the injectivity/weakening region.
4. **The injectivity *localisation* programme is retired as stated, 2026-09-01.**  Every theorem
   in `InjMidLocal.lean`, `InjChainLower.lean` and `InjPiInhab.lean` assumes `Ordered env` and
   nothing more, and at that strength the Π-side target is **false**: `roguePiEnv`
   (`Theory/Typing/InjPiRogue.lean`) is a provably `Ordered` environment carrying **two** δ-rules
   for one constant, at which `ConvPiFromEntry` forces a sort/Π conversion.  `Ordered.defeq` asks
   only `df.WF env`, which both rules satisfy.  So a proof in this corner must consume
   `VEnv.WF` — specifically the clause that makes two δ-rules for one constant impossible
   (`RuleShape.delta` pins the lhs to `.const ci.name _` and `addConst` refuses a duplicate
   name).  Sequencing consequence: **do not commission further `Ordered`-only localisations of
   `ConvStep2`**; the next statement in this corner should carry `VEnv.WF` or be aimed at the
   reference's judgment.  Ledger rows 69–69b, and row 52's `[analysis]` claim that no rogue
   refutation was available here is superseded on both Π-side entries.

   **Amended the same day, and the amendment is a retraction.**  The follow-up finding that the
   `extra` case of Π/Π inversion closes at `VEnv.WF` (`WF.noPiLhs`) stands.  The two claims
   published alongside it do **not**: `proofIrrel` is *not* closed by shape — it needs
   `SortNotPropStrong`, bounded above by `SortUniq`, strictly weaker but not free — and
   `ConvStep2`'s midpoint is *not* the Π/Π `trans` midpoint.  `ConvStep2`'s entire content is the
   **level mismatch** (when the two link levels are the same expression the composition is
   `IsDefEqStrong.trans` and costs nothing), while `trans` needs **Π-shape descent**; closing
   either does not close the other.  So "`trans` is the entire residual" was wrong on two of its
   three clauses.  Ledger row 77.  A third attempt to localise `trans` also collapsed into its
   own target with no hypothesis (row 77b) — that makes three such collapses in this corner, so:
   **test any proposed localisation against its own target before building on it.**  What
   confluence would have to supply is now stated tightly as `PiMidNonPi` (row 77c), bounded above
   by the statement it is asked to supply.

   **Amended once more, and this is the load-bearing one.**  The two halves of `ConvStep2` are
   **not independent**: the Π side's `proofIrrel` case costs `SortNotPropStrong`, which follows
   from `ConvSortInv` (`sortNotPropStrong_of_convSortInv`), and
   `BaseUniqChain.sortUniq_iff_convSortInv` makes `ConvSortInv` the *same* hypothesis as
   `SortUniq` — the corner's own sort residual.  So **the Π half consumes the sort half**, and any
   plan that treats them as two fronts to be attacked separately is wrong.  Ledger row 82.
   Relatedly, `WF.noPiLhs` was already in the tree as `DeclRules.WF.instL_lhs_ne_forallE`, so of
   the `VEnv.WF` work only `not_wf_roguePiEnv` is original (row 82a), and the `extra` case — the
   one thing well-formedness buys — **was never the residual on either side**.  Localisation has
   now collapsed four times, on both halves.

## The convergence (2026-09-01): two independent corners both reduce to the rule table

This is the cleanest statement of the critical path the project has had, and it came from two
streams that were not working together.

**The injectivity corner reduces to sort-descent at a non-sort midpoint.**
`InjPiRogue.sortLinkInv_of_wf` runs the induction the Π side could not, because the sort side's
conclusion `a ≈ b` **carries no context and no type index** — so `defeqDF` is free, `symm` is
`Eq.symm`, and `trans`-through-a-sort is `Eq.trans`, with nothing to transport between contexts.
Eleven of thirteen constructors close inside the proof (`extra` by
`DeclRules.WF.instL_lhs_ne_sort`), leaving exactly two: `SortMidNonSort` (`trans` at a non-sort
midpoint) and `SortNotProof` (`proofIrrel`). **Both are descent statements about a term that is
not a sort — not statements about rules** — so every rule-level route into a sort/sort link is
shut, and a rogue `VEnv.WF` witness would have to be a non-confluence of Lean's own rule set.

**RETRACTED, 2026-09-01, the same day it was written.** This paragraph said "target → residual is
free, and the converse has no route", and called it the first genuine localisation in six attempts.
**Both halves are false.** A single link *does* offer a non-sort midpoint: β manufactures one for
**every** well-typed `X` at **every** index, because `Type 0` is inhabited by `Prop` in every
context — `InjOneFact.betaMid`, `betaMid_link`. So `sortMidNonSortC_iff_sortLinkInvUC` is an `iff`
and `sortLinkInv_of_wf` is **collapse six**, not a reduction. The same β witness makes
`piLinkInvCod_iff_piMidNonPi` an `iff` — **collapse seven**, so the `PiMidNonPi` "request" below
gives back exactly the statement it was asked to supply.

Worse, the mechanism was already recorded three paragraphs from the claim, in
`docs/handoff-injectivity.md` §4H.8 item 5 ("the costly midpoint heads are reached by **β alone**",
`midpoint_app_at_empty`), which the same section flagged `[analysis]`. **Two mutually inconsistent
claims, in one document, written by me on one day — and the `[analysis]`-flagged half was the
right one.**

**Generalised, and this is the durable result:** `midShapeless_vacuous` / `shapeMidP_iff` — for
**any** predicate `P` with `∀ X, P (betaMid X)`, the `P`-restricted midpoint statement is
equivalent to the unrestricted link statement. **No syntactic condition on a midpoint can ever
localise a `trans` node.** That kills "not a sort", "not a Π", "neither", "is an application", "is
a β-redex" and "no rigid head" in one theorem, and it is why localisation has now collapsed seven
times here.

**The one fact, and it is now a theorem rather than a reading of the reference.**
`InjOneFact.ShapeLinkAgree` states it once — one relation over `SPShape` (sort | pi) with
`Agree` diagonal-and-disjoint — and `shapeLinkAgree_iff` proves
`ShapeLinkAgree ↔ SortLinkInvUC ∧ PiLinkInvUC ∧ SortPiDisjUC`, **both directions**. So "one
prerequisite, three consumers" is established here, not inferred from `unique.tex`.
`shapeAgree_of_wf` then closes **eleven of thirteen** constructors at `VEnv.WF`, leaving
`ShapeMidShapeless` and `ShapeNotProof` — and it **discharges the item `InjPiRogue.lean` §17
explicitly left open**, that these plus `VEnv.WF` close `PiLinkInvCod`. What unblocked the Π-side
induction was *not* `ConvC.defeqDFC`: it was dropping the `.sort u` index and carrying the domain
chain in the conclusion, so `PiLinkInvDom` is **part of what the induction proves**, not a
hypothesis it needs.

**Where the CR boundary actually falls: the `trans` node and nothing weaker.** That is the sharp
content of `midShapeless_vacuous`, and it has a hard consequence for how the confluence layer is
asked for anything — **any request must name a reduction relation or a normal-form predicate.** A
request that proudly mentions no reduction relation is, for that reason, equivalent to its own
target. The minimal honest form is `ShapeCR`, parametric in `Red`, with `join` and `normal`; it
discharges the whole target (`shapeLinkAgree_of_shapeCR`) with no `VEnv.WF` and no induction, and
**both clauses are proved load-bearing** — `Red := Eq` fails `join`, conversion fails `normal`, the
latter by the β witness again. *Not claimed: that any `Red` satisfies both.* Note also that
`ShapeCR.join` **absorbs** `ShapeNotProof`, since a `proofIrrel` link is a link — so only the
constructor-by-constructor packaging separates the stratification residual from the CR one.

**Priced against the reference, the three residuals are one fact.** `~/lean-type-theory/unique.tex`
discharges its clauses (1), (2) and (3) — sort inversion, Π inversion, sort/Π disjointness — by the
*same* two moves (`:263`, `:267`, `:274`). So this tree's `SortMidNonSort`, `PiMidNonPi` and
`RigidSortPiDisj` are **three instances of one fact — a κ-normal rigid head has no reduct of another
shape — plus Church–Rosser.** One prerequisite, three consumers.

**SUPERSEDED, 2026-09-01 (later): `KDiamond` ITSELF IS FALSE, and so is M3 — but the rule table is
not at fault.** The canonical `.app`-pattern instance now exists
(`Lean4Lean/Verify/QuotAppParams.lean`, `quotParams := paramsOfPiInv quotVEnv_wf 0 (piInv_axiom _)`),
and at it:

* `quotParams_not_patMajorCanonical` and `quotParams_not_kDiamond` — **both false.** The witness:
  `quotRHS` is `g x` for the *matched* argument, so two matches at the same function side already
  differ syntactically (`quotRHS_depends_on_match`, `sorryAx`-free). Take major premises
  `Quot.mk α r x` and `Quot.mk α r ((fun y => y) x)` — definitionally equal **by β**, both typed
  `Quot.{1} α r`. M3 then demands `NormalEq (g x) (g ((fun y => y) x))`, and **`NormalEq` has no β
  step**. The same witness gives one redex, two `K⁺` steps, two reducts, refuting `KDiamond` — the
  very object `kDiamond_of_patMajorCanonical` reduces confluence *to*.
* **The rule table is not the defect.** `quotParams_kDiamond_joinable`: the two reducts are joinable
  in **one β-step**. So the joinability shape `KEta.lean`'s `EtaKDiamond` already uses survives, and
  what fails is `KDiamond`/M3 **demanding `NormalEq` of reducts on the nose**. *The repair is a
  restatement to joinability, not a new `Params` field and not a rule-table property.*
* **Both refutations are reachable there**, and the stated reason they could not be is false.
  `quotParams_not_parRedStatement` and `quotParams_not_crStatement` are `NormalEq.parRed`'s and
  `IsDefEq.church_rosser`'s statements *verbatim*. The blocker on record — "`Quot.mk r a` is not a
  proof of a `Prop`, so this needs an `addInduct'` witness (the `Eq.rec` shape)" — is wrong:
  `quotConst.type` is `(α : Sort u) → (α → α → Prop) → Sort u`, so at `u = 0`, `Quot.{0} α r` **is**
  a proposition while `β` stays in `Type 0`. The quotient rule supplies the shape by itself. The
  missing ingredient was never the pattern; it was `hne`, a `¬IsProof` fact, which
  `WF.propTypeAgreeOn` supplies.
* **Conditional, and it must not be quoted otherwise.** All four results carry `sorryAx`, with direct
  sorry sites exactly `IsDefEqU.forallE_inv_stratified` and `WF.rigidShapeUniqNS`. So ledger row 33's
  grade moves from *"refuted only at an instance that does not exist"* to **"refuted at an instance
  conditional on the injectivity corner"** — not unconditional.
* **Two consumers need reshaping, not just noting.** `KEtaDiamond.etaKDiamondAt_of_kDiamond` is a
  true implication whose premise is now known false at a concrete instance, so it needs the
  joinability form first. And the four `IsDefEq.church_rosser` call sites in
  `Verify/Typing/ConstSpine.lean` and `Verify/Typing/Rigidity.lean` rest on a statement false in the
  same sense — root cause the known one (`ParRed` lacks the K-step, so `.app f (.bvar 0)` is
  `ParRed`-normal while defeq to `g x`, and joinability collapses to `NormalEq` between two normal
  terms), i.e. ledger row 78b's `ParRed → ParRedK` repair, now with a reachable witness.

**THIRD NOTE, and this is where the section actually lands: after the repair, NEITHER corner
points at the rule table.** The joinability restatement works — `KDiamondJ` and
`PatMajorCanonicalJ` (`Theory/Typing/KDiamondJoin.lean`), with
`kDiamondJ_of_patMajorCanonicalJ` at **the same axiom cost as the original**
(`[propext, Quot.sound]`, `Classical.choice`-free), and the β-witness that refuted `KDiamond` dies
instance-independently (`joins_beta_arg`, hole-free). It is also not trivially true:
`joins_normal_iff` shows `Joins ↔ NormalEq` on `ParRedK`-normal terms, so the only way past
`NormalEq` is a real reduction step.

**But the localisation is gone — `KDiamondJ` is sandwiched between two Church–Rosser statements.**

* *Above:* `kDiamondJ_of_crK` — CR over `ParRedK` implies `KDiamondJ`. So it is an **instance** of CR,
  where `KDiamond` had been strictly stronger than one.
* *Below, and hole-free:* `quotPat_argJoin_of_kDiamondJ` — at any instance registering `quotPat`,
  `KDiamondJ` implies that for **arbitrary definitionally equal** carrier elements `x`, `x'`, the
  spine's `g x` and `g x'` join. Mechanism: take the major premise to be `Quot.mk α r x` and let the
  second `K⁺` step match at `x'`; `hdq` is an arbitrary `IsDefEq`, so nothing constrains `x'` beyond
  conversion.

So **proving `KDiamondJ` is proving confluence, and refuting it is refuting confluence** — neither is
reachable, and a refutation would refute CR for a real `VEnv.WF` environment, which nothing here
suggests. `KDescend.KDiamond`'s own docstring had warned that its content is "the upgrade from `≡` to
`≡ₚ`, which is exactly what confluence is being built to deliver"; joinability does not escape that,
it lands on it. **Ledger row 101a's "the repair is a restatement to joinability" is right about what
to do and silent about what it costs.**

Net for this section: the injectivity corner collapsed **seven** times (`midShapeless_vacuous`
explains why in one theorem), and the confluence corner's repaired target is itself a CR statement.
**Neither corner localises.** What survives is real but smaller than the section's title claimed:
`kDiamondJ_of_patMajorCanonicalJ` clean, the η-layer's two repairs identified and independent
(joinability fixes the *base* case, domain-pinning fixes the *`under`* case —
`etaKDDiamondAt_of_kDiamondJ` is both, `[propext, Quot.sound]`), and the whole route measured rather
than hoped.

**What the paragraph below claimed, kept for the record.**

**And Church–Rosser reduces to one named property of the rule table.**
`ParRedCycle.kDiamond_of_patMajorCanonical` (`[propext, Quot.sound]`, `Classical.choice`-free)
derives `KDiamond` from `PatMajorCanonical`, which mentions only `Params.Pat`,
`Pattern.Matches`, `HasType`/`IsDefEq` and `NormalEq` — **no `ParRed`, no `ParRedK`, no grading, no
reduction relation at all.** It is `design-inductive.md` §7.6's lemma **M3**.

So both corners now point at the same place: **the rule table.**

**PARTLY RETRACTED, 2026-09-01: true of `KDiamond`, FALSE of the η-layer.** `KDiamond` does **not
suffice** for `ParRedK` confluence. The λ-congruence induction has since been run
(`KEtaDiamond.etaKDiamondAt_of_kDiamond`), and its blocker is `PiDomAgree` — *two Π-typings of one
term in one context agree on the domain* — which the tree discharges only from `IsDefEq.uniqU` +
`IsDefEqU.forallE_inv`. Measured: `etaKDiamond_of_kDiamond_holes` holds relative to **exactly**
`{IsDefEqU.forallE_inv_stratified, WF.rigidShapeUniqNS}` — notably **not** `weakN_iff` and **not**
`NormalEq.descend`. So the η-layer creates no *new* obligation, but it reduces to **injectivity**,
not to the rule table. The convergence is therefore: `KDiamond` → rule table, `EtaKDiamond` →
injectivity corner — the known Church–Rosser ↔ definitional-inversion cycle
(`docs/research-forallE-inv.md` §4) touching the η-layer.

The domain agreement is **forced, not an artefact**: `EtaK.under` reads its λ-domain off an
*arbitrary* Π-typing of the subject, and `appParams_etaK_under_dom_distinct` exhibits two `EtaK`
derivations at one subject with the **same body** and **syntactically distinct** domains, so
`NormalEq.refl` is unavailable and `NormalEq.lamDF` — which demands exactly that conversion — is
what closes the pair.

**A route past it exists and is measured.** `EtaKD` pins `under`'s domain to a function of the
subject; then `etaKDDiamondAt_of_kDiamond` needs **`KDiamond` and nothing else** — cone 235, hole
cone empty, `[propext, Quot.sound]`, the same axiom set as `kDiamond_of_patMajorCanonical`. The
obligation it creates is stated and **not** discharged: `ParRedK`'s two refutation-kills build their
`EtaK` step at a domain handed to them, so under pinning they need that domain defined and
Π-typing-derivable — a statement about spine typing and the rule table, which is the direction this
section wants, but it is not proved. `EtaKD.toEtaKn` records that `EtaKD` is a *sub*relation, so the
kills as stated are about the larger one. What is *not* claimed: that
`KDiamond` suffices for `ParRedK` confluence (`EtaKDiamond` reduces to an equal-height diamond plus
a λ-congruence induction that is open), and that `PatMajorCanonical` is satisfiable — it is
**vacuous** at `cycParams`, so non-vacuity needs an instance registering an `.app` pattern, the same
instance `ParRedPropRefute.lean` and `KCanonical.lean` need and that `PatWFIota.lean` would supply.

**Two routes are closed for good, by theorem rather than by remark.** Adding the two missing steps
to `ParRed` cannot work: the cycle is *essential* (`cyc_of_answers`, `[propext]`, for an
**arbitrary** relation — `descend`'s own obligation demands both directions before any constructor
is written), no well-founded strict order orients it (`no_wf_orientation`), and **no grading
removes it** (`no_grading_removes_cycle`, `[propext]`) because a grading bounds structure *within*
a step and never the length of a chain. Proof irrelevance has no preferred direction and any
relation strong enough for `descend` inherits that.

**One divergence from the published reference, machine-checked.** The reference's route to the
`proofIrrel` residuals runs through unique typing at `n`, whose application case needs closure of
`⊢ₙ`-conversion under instantiation (`unique.tex:51`) — and `Theory/Typing/SubstCRefute.lean`
**refutes** exactly that (`VEnv.SubstC`, false at `n = 1` over `∅`). So the stratified route to
`SortNotProof` is not available here as written; the CR-side residuals are unaffected. Per
`CLAUDE.md` this stays in the repo.

## Honest statement of where this leaves the main theorem

`kernel_sound` is *not* closer to proved than the census suggested. What changed is that the
remaining distance is now enumerated instead of estimated: eleven named obligations, one of which
(`hasType_falseProp`'s half) is confirmed already discharged. The frozen `sorry` stays, and no
frozen edit is proposed yet — there is nothing to apply while H1 and H2 are un-inhabited.

---

## Addendum, same day: two corrections and a re-pricing

### Correction 1 — the confluence↔strengthening cycle is *not* broken

I recorded in commit `d20aa81` that entry (1) of the cycle
(`NormalEq.weakN_inv_DFC → IsDefEqU.weakN_iff`) had been removed. That was too strong. What
exists is a **bypass**: `NormalEq.weakN_inv_DFC'` proves the same thing from
`TypingStrengthening`, and `weakN_inv_DFC'` does not reach `weakN_iff`. But the original
`weakN_inv_DFC` is still in the tree and still a live direct user of the hole, and its users
still go through it. A bypass that nothing has been switched over to does not remove an edge.

Measured: `IsDefEqU.weakN_iff` has **12** direct users — `ConditionallyWHNF.weakN_inv`,
`IsDefEq.skips`, `IsDefEq.weakN_iff'`, `IsDefEqU.weak'_iff`, `KTable.kstep_liftN_inv_stepP`,
`NormalEq.weakN_inv_DFC`, `ParRed.weakN_inv`, `ParRedExt.parRed_beta`, `hasType_app_bvar0`,
`parRedK_weakN_invP`, `parRedK_weakN_invPS`, `VExpr.WF.weakN_iff`. Switching the consumers of
`weakN_inv_DFC` over to `weakN_inv_DFC'` removes one of the twelve.

### Correction 2 — entries (1) and (2) are not independent surfaces

`Theory/Typing/ParRedKWeakN.lean` proves `checkStrengthening_iff_target`:

    CheckStrengthening env U ↔ StrengtheningTarget env U

**both directions, cone 790, no `sorryAx` at all.** So the rule-table check obligation that
entry (2) was supposed to isolate *is* the hole restated, not a weaker sibling of it. The plan of
"attack the two entries separately" was therefore based on a distinction that does not exist, and
no cone reduction is available on that route. `PatCheckOfTyping` discharges entry (2)'s `extra`
case from typing strengthening alone, but its only discharge route runs through
`constApp_inv_of_wf`, which is measured hole-tainted — so it is a deferral, not an elimination.

Related circularity fact, measured: `patWF` (3892), `patWF_iota`, `patWF_quot`, `patWF_of_wf`,
`piInv_axiom` are all **clean**, but `constApp_inv_of_patWF` (7303), `constApp_inv_of_wf` (7465)
and `const_app_inv_of_wf` (7468) all reach `IsDefEqU.weakN_iff`, because constant-application
injectivity is proved via Church–Rosser. Do not treat const-injectivity as an independent supply.

### Re-pricing the `AddInduct` flip

`docs/handoff-addinduct.md` §6 specifies the flip that gives `AddInduct` its constructors (today
it has none, so `TrEnv'.induct` can never fire and `TrEnv` provably contains no inductive at all
— this is what blocks H1). §7.2 recommends **"not yet"**, priced at "nine sorry-free declarations
become `sorry`", and records that the decision is the human's.

I guessed that price had fallen because three checker `.WF` obligations are now holes. **That
guess was wrong** — `inferProj.WF`/`isDefEqUnitLike.WF`/`tryEtaStructCore.WF` (holes) are
different declarations from `inferProj_always_throws`/`tryEtaStructCore_never_true`/
`isDefEqUnitLike_never_true` (the vacuity lemmas the flip kills), and of the seventeen affected
declarations sixteen are still sorry-free.

What the measurement *does* change is the denomination. Of the seventeen, **nine are on
`kernel_sound_of`'s cone** and eight are not — and losing an off-path declaration costs the main
theorem nothing. Of the nine on-path casualties, six have **proved replacement arms already in
hand** per §6 (`TrEnv'.find?_shape`, `TrEnv.find?_shape`, `TrEnv'.defeqs_shape` gain disjuncts
with arms `AddInductStages.find?_shape`/`.defeqs`; `Aligned.addInduct` gets
`Aligned.addInductStages`; `TrEnv.not_ctorInfo`/`.not_recInfo` are simply false and are deleted).

So the flip's actual cost **to the main theorem** is three declarations with no replacement in
hand — `reduceProjCore_none`, `reduceProjCore.WF`, `inductiveReduceRec_eq_none` — i.e. census
14 → 17, not the nine the handoff priced. Everything else is either off-path or already proved.

Worth saying plainly about what is being "lost": these are theorems asserting the checker never
handles inductives. They are sorry-free today *only because* `AddInduct` is empty. For a kernel
whose theorem must cover full Lean type theory, their falsity is the goal, not a regression.

**This remains the human's decision and I am not taking it.** Of the two prerequisites from §7
once called independent of it, §7.1 (`addQuot.WF`'s `AddQuot` construction) is **done** —
`Environment.addQuot.WF` is proved and sorry-free — and it turned out **not** to be orthogonal
to `AddInduct`: `addQuot.WF` is still vacuous, because its hypothesis `ves.WF env` cannot hold
at an environment carrying an `.inductInfo` (`addQuot_trivial_of_wf`, `no_wf_envEqInd`;
`docs/vacuity-ledger.md` row 5). What genuinely can proceed is §7.3 (`addDecl.WF`'s
`inductDecl` branch, which must show the map the executable `addInductive` produces *is* the map
`AddInductStages` builds).

### Correction 3: one of the nine holes is not fillable as stated

The body of this document enumerates nine holes below `Bridge.kernel_sound_of` and treats them
uniformly as *open*. That is wrong for one of them. **`addDecl.WF`'s `inductDecl` branch is not
merely unproved; its statement is refuted.**

The chain, all four links re-read at the source:

1. `Verify/Environment.lean:240-275` — `addDecl.WF`'s `inductDecl` branch is `sorry`, and the
   docstring states the statement is refuted, not open.
2. `Verify/Inductive/AddDeclWF.lean:306` — `addDecl_inductDecl_WF_false` proves the negation from
   `VEnvs.WF.no_inductInfo` plus a hypothesis `hex` asserting the refuting environment exists.
   `hex` is **not proved**; it is backed by `#eval` check A at `:330`, which runs the real checker
   on the `R10.Wit.U` block and confirms it returns `.ok` with `U` an `inductInfo`. So the
   refutation is a proof modulo an evaluation-checked existence claim — decisive for planning,
   short of a closed proof of `¬ AddDeclWF`.
3. `Verify/Bridge.lean:132-136` — `Bridge.AddDeclWF` repeats the refuted statement **verbatim**,
   universally quantified over `decl`, so it includes the `inductDecl` case.
4. `Verify/Bridge.lean:138` — `theorem addDeclWF (fuel) : AddDeclWF fuel :=`
   `fun wf decl => addDecl.WF wf decl fuel`.

So `Bridge.kernel_sound_of` is itself a correctly-proved theorem, but its route reaches a
dependency that cannot be discharged. **`kernel_sound` cannot be obtained through
`Bridge.addDeclWF` as that statement now stands, no matter how much proof effort goes into the
other eight holes.** The statement has to be reshaped to `AddDeclPost` first
(`Verify/Inductive/AddDeclWF.lean` §5; `addDecl.WF_honest` is already proved there with no `sorry`
of its own, from the single obligation `AddInductiveStepWF`), and landing that is blocked by §5.4's
three changes — one of which is precisely `Bridge.AddDeclWF`, because it restates the false form.

The nuance that matters for the flip decision: `addDecl.WF` is false **because `AddInduct` is
empty**. `VEnvs.WF` forces the modelled environment to contain no `.inductInfo`, while the
executable checker demonstrably produces one. It is not intrinsically false — the flip is what
repairs it. Both repair routes, reshaping to `AddDeclPost` and giving `AddInduct` its
constructors, are blocked on the same emptiness that H1 needs. That sharpens the pending decision
above; it does not settle it, and I am still not taking it.

Revised reading of stop condition 2: **2 hypotheses + 8 holes + 1 refuted statement**, the last
being a reshape rather than a proof.

### Correction 4: H1 is vacuous, and `foldAddDecl_tr` is the false link

Correction 3 said one of the nine holes is refuted. Measuring *where* the falsity surfaces in
`Verify/Bridge.lean` gives a worse answer, and it invalidates this document's headline count of
"2 hypotheses". Proved in `Verify/PreludeVacuity.lean` (sorry-free; axioms = `propext`,
`Classical.choice`, `Quot.sound`):

* `TrEnv.not_safe_inductInfo` — `TrEnv .safe env venv` is unsatisfiable once `env` holds one
  **safe** inductive. Unconditional, no `VEnv`-side guard: `TrEnv'.ignore` needs
  `¬ safety ≤ ci.safety`, and `.safe` is the top of `DefinitionSafety`, so a safe constant is
  not ignorable, and no other `TrEnv'` constructor emits an `.inductInfo` while `AddInduct` is
  empty. The `isUnsafe = false` hypothesis is load-bearing:
  `no_inductInfo_false_at_safe` shows an *unsafe* inductive really can sit in a `.safe` map.
* Check B (`#eval`): the checker run on `stdPrelude` leaves `Eq` an `.inductInfo` with
  `isUnsafe = false`.
* Hence `foldAddDecl_tr` (`Bridge.lean:172`) is a **false statement**, refuted at
  `ds = stdPrelude` (`foldAddDecl_tr_false`). This is the link that `addDecl.WF`'s falsity
  reaches, and it sits upstream of everything else in the chain.
* Hence **H1 is vacuous.** `PreludeBridge stdPrelude` assumes `TrEnv .safe env venv`, which is
  unsatisfiable at the instances the main theorem uses (`preludeBridge_vacuous_at_nil`, stated
  at `ds = []`; covering every `ds` would need an `addDecl` constant-map monotonicity lemma the
  tree does not have). Discharging H1 as it stands buys the main theorem nothing. It becomes
  real content only *after* the flip, when `TrEnv` can hold an inductive at all.

So the honest reading of stop condition 2 is not "2 hypotheses + 8 holes + 1 refuted
statement". It is:

| item | status |
| --- | --- |
| H2, `Consistent 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰 → leanTTConsistent` | a real hypothesis, real content |
| H1, `PreludeBridge stdPrelude` | **vacuous today**; real only after the flip |
| `foldAddDecl_tr` | **false**; must be re-derived, not proved |
| `addDecl.WF` | **refuted**; reshape to `AddDeclPost` |
| the other 8 holes | genuinely open, genuinely fillable |
| the `False`-witness side (`hasType_falseProp`) | hole-free already |

### The trap, recorded so it cannot be walked into

`Verify/Inductive/AddDeclWF.lean` §5.4 item 3 proposes that `foldAddDecl_tr` "become a
hypothesis alongside `PreludeBridge`". `anything_of_foldAddDecl_tr_hypothesis` shows what that
would produce: assuming the refuted statement proves **any** proposition, `kernel_sound`'s
conclusion included, with no `sorryAx` anywhere — guard 2 would print "proof COMPLETE" over a
proof that means nothing. A hypothesis is honest only if it is satisfiable. The repair has to
weaken the chain's *conclusion* — `AddDeclPost`, plus a fold-level invariant that does not claim
`TrEnv .safe` — and never assume the false form.

This is the concrete reason the flip is no longer a trade to be priced against three new holes.
Every route from the checker to the abstract environment passes through `TrEnv .safe`, and while
`AddInduct` is empty that relation cannot hold of any environment containing `Eq`. The flip is
not a way to buy progress; it is the only thing that makes the route exist. The decision is
still the human's, and the price recorded above (census 14 → 17) is still the price.

### Correction 5: the flip is two flips, and the one that matters is not a decision

Corrections 3 and 4, and §2 of `docs/vacuity-ledger.md`, present the `AddInduct` flip as the
single thing standing between the tree and `kernel_sound`, and therefore as a decision waiting
on a human. Reading `Theory/Inductive/NestedOrdered.lean` shows that is half wrong.

There are **two** flips, and they are not the same change:

* **The non-nested flip** — `AddInduct := ∃ …, AddInductStages …`. Every arm is proved in
  `Verify/Environment/Basic.lean` (`.le`, `.map_wf`, `.find?_shape`, `.defeqs`,
  `.to_addInduct`), and `AddInductStages` is *satisfiable* (`Basic.lean:844`, all three stages
  fire). The one repair the handoff called "not yet in hand" — `addQuot.WF`'s second branch —
  **is** in hand now. So this flip is available today. It is genuinely a decision, because it
  costs census 14 → 17 and buys a *partial* result: `AddInductStages` is refuted for a nested
  block (`Basic.lean:108`), so `TrEnv'` stays unsatisfiable there and rows 1–5 of the vacuity
  ledger survive with a narrower witness.

* **The nested flip** — `AddInduct := ∃ K R, AddInductStagesR …`, which is what
  `AddInductFlip` is stated in terms of and the only version that covers full Lean type theory.
  This one is **not** a decision. It is blocked on four ordinary open obligations, listed in
  `docs/vacuity-ledger.md` §6. **Three** of them are open theorems: the hypotheses
  `hctors` / `hrecs` / `hrules` of `VEnv.addInductR_ordered'`. The fourth — the nested arm of
  `DeltaUnique`'s `keys_induct` — turned out to be **already done** in
  `Theory/Inductive/NestedKeys.lean`, and more sharply than expected: `KeyMajorUnique` is *false*
  after a nested step, the replacement `KeyUnique` is preserved, and the sole consumer is
  re-proved from it. What remains there is two mechanical edits, not a proof.

Why this was missed for several rounds: all four are **hypotheses of proved, sorry-free
theorems**, so the census reads 0 where the work is, and no hole cone can see them either — a
cone walks dependencies, and a hypothesis is not one. That is the fourth instrument-blindness
now recorded at the top of the vacuity ledger.

What this changes about priorities: waiting on the decision was never going to reach the goal,
because the decision only ever unlocked the partial flip. The four obligations are the work.
They are known satisfiable — `nfnAux_addInductR_ordered` discharges all three of the first kind
in a non-trivial instance, and `addInductR_ordered_nil` shows they collapse to `addInduct'`'s
own obligations at the identity restoration — so this is proving, not repairing.

One caution earned the hard way while writing this: `NestedOrdered.lean`'s docstring said the
`keys_induct` arm was "the second of the two obligations the `inductNested` rule waits on", and it
had been done for some time. Stale docstrings in this tree drift toward *overstating* what is
open — the direction that wastes work. Grep for a statement before proving it.
