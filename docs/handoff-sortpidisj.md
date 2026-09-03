# Handoff: the open coordinate `PiInvStrat → SortPiDisjUC`

*Written 2026-09-03.  Everything below is in `Lean4Lean/Theory/Typing/SortPiDisjPrice.lean`
(24 declarations, 86 jobs, **no `sorryAx` anywhere in the file** — every headline result prints
inside `{propext, Classical.choice, Quot.sound}`, and `sortClass_of_wf` / `sortPiDisjUC_of_sortPiCR`
print less than that).  Read `Theory/Typing/ForallInvPrice.lean` first; this file is its §3's one
open coordinate and nothing else.*

## Verdict

**Neither proved nor refuted.  Measured, and the measurement is sharp: the coordinate *is* hole B.**

Over `VEnv.WF env` and hole A (`PiInvStrat`):

| direction | theorem | extra hypotheses |
| --- | --- | --- |
| hole B ⟹ coordinate | `sortPiDisjUC_of_rigidShapeUniqNS` | **none** |
| coordinate ⟹ hole B | `rigidShapeUniqNS_of_sortPiDisjUC` | the three constant-spine conjuncts |
| both | `sortPiDisjUC_iff_rigidShapeUniqNS` | those three |

So `docs/vacuity-ledger.md` row 41's blockage is **not an artefact of `sort_forallE_inv`'s proof**.
That lemma's `trans` case eats hole B because the coordinate is hole B's sort/Π conjunct
(`RigidNodeCircle.rigidShapeUniqNS_iff_family` conjunct 2, the one conjunct the tree records as
live).  Any route that settles the coordinate settles that conjunct, by definition of the `iff`.

Consequences, both theorems and not advice:

* **Proving it proves hole B**, given hole A and the three constant conjuncts.  Since
  `ForallInvPrice.piInvStrat_and_rigidShapeUniqNS_of_shapeLinkAgree` already gets hole A from hole
  B's own hypothesis set, the corner is now a two-element chain with one link left.
* **Refuting it refutes hole B** (`refutation_refutes_rigidShapeUniqNS`, and this direction needs
  *no* constant conjunct).  `Injectivity.lean:1046` asserts `WF.rigidShapeUniqNS` for **every**
  well-formed environment, as a `sorry`.  A refutation makes that `sorry` unfillable — a large
  event, not a cheap settlement of a loose coordinate.  The orchestrator's brief ranks "refute" as
  outcome 2 and a good outcome; it is a good outcome, but its price is stated here so nobody
  reports one without noticing what else falls.

## Where the coordinate lives inside `IsDefEqStrong`: `trans`, and nothing else

`sortClass_of_wf` is `InjOneFact.shapeAgree_of_wf` with `SPShape.Agree` weakened to **shape class**
(`SPShape.SortClass`: sort or Π, nothing more).  Thirteen constructors, and after the weakening:

* `symm` and `trans`-through-a-shape are `Iff.symm` and `Iff.trans` — **no `Ordered`, no
  `ConvC.defeqDFC`** anywhere in the induction;
* endpoint clashes, `sortDF`, `forallEDF`, `defeqDF`: free;
* `extra`: `VEnv.WF` via `instL_lhs_ne_sort` / `instL_lhs_ne_forallE` — the **only** case that uses
  `WF`;
* `proofIrrel`: `shapeNotProofC_of_sortUniq` — the `SortInvIndep.ShapeNotProofC` interface from
  `VEnv.SortUniq`, which `Injectivity.sortUniq_of_piInvStrat` supplies from hole A.  So relative to
  hole A the "genuinely the stratification" residual of `InjOneFact.lean` §9 is **free**;
* `trans` at a shapeless midpoint: `SortPiMid`, the residual.

`sortPiDisjUC_of_sortPiMid : WF → PiInvStrat → SortPiMid → SortPiDisjUC`, and
`sortPiMid_of_sortPiDisjUC` is the converse in one `trans`, so `sortPiMid_iff` makes `SortPiMid`
**equivalent** to the coordinate.  §2 is therefore a *localisation*, not a reduction, and it is
labelled that way in the file — the discipline `PiInvResidual.lean` §5 sets.

**Bounding my own novelty:** `IsDefEqU.sort_forallE_inv`'s docstring (`Injectivity.lean:1240-1245`)
already names the same two residuals for the same statement one level up, including "`proofIrrel` …
is `VEnv.sort_not_proof` given `VEnv.SortUniq`".  New here: that the `trans` discharge is
*equivalent* to hole B rather than merely routed through it; the `ShapeNotProofC` form, which is
`sorryAx`-free and parametric where `not_isProof_of_defeqU_sort` routes through `WF.sortUniq'`; and
the class-level induction that drops `Ordered` and `ConvC.defeqDFC`.

## The confluence request is weaker than the corner's

`SortPiCR` = `InjOneFact.ShapeCR` with `normal` weakened from "a shape's reducts are shapes that
*agree*" to "a sort's reducts are sorts, a Π's reducts are Π's".  `sortPiDisjUC_of_sortPiCR` gets
the coordinate from it with **no `VEnv.WF`, no hole A, no induction**; `ShapeCR.sortPiCR` proves the
weakening is a weakening.  Controls: `not_sortPiCR_eq` (`Red := Eq` fails `join`),
`not_sortPiCR_conv` (conversion fails `sortNormal`, the `betaMid` β-redex again).  So a confluence
stream that cannot deliver `ShapeCR` may still be able to deliver `SortPiCR`, and that alone closes
this coordinate — and hence, by §1, hole B's live conjunct.

## Anti-vacuity and controls

* `sortPiDisjUC_inhabited_iff` — hypothesis-inhabited ⟺ hole-B-inhabited, the
  `ForallInvPrice.hyp_inhabited_iff` form, which is the strongest available for an equivalent of an
  open target.
* `not_sortPiMid_sortPiEnv` — `SortPiMid` is **false** at `ForallInvPrice.sortPiEnv`, at a genuinely
  *shapeless* midpoint (`.const rogueC []`, exhibited separately as `sortPi_links`).  So §2's
  hypothesis is not an artefact of its midpoint side conditions.
* `control_is_control` (`= ForallInvPrice.not_wf_sortPiEnv`) — that environment is not `VEnv.WF`
  (two δ-rules share an lhs), so §5 refutes the hypothesis only *off* `WF` and **nothing here
  refutes the coordinate**.
* `sortPi_premises_fire` — the degenerate instance `Γ = []` is checked: the premise class of
  `SortPiDisjUC` is non-empty there (at the non-`WF` control), so no statement above is
  true-because-empty at the instance this corner is always tested at
  (`docs/vacuity-ledger.md` §0, blindness seven).

## Corrections to the brief I was given

1. **"`VEnv.WF` occurs only in binder position anywhere in `Lean4Lean/`, never as a conclusion" is
   false**, and it was false before the correction the orchestrator sent mid-round.  Besides
   `WeakNProjGate.exists_typingStrengthening_env` (committed this round), the tree already had
   `InjPiRogue.wf_wfPiEnv : VEnv.WF wfPiEnv` (`Theory/Typing/InjPiRogue.lean:591`) — a concrete
   `sorryAx`-free well-formed environment — and `Verify/Inductive/Add.lean:733`'s `VContext.Ewf`.
   `wf_witness_exists` in my file is the one-liner.  Searched: `grep -rn` over the whole repo for
   `VEnv.WF` in conclusion position.  Definition site of the symbol searched for:
   `def VEnv.WF (env : VEnv) : Prop := ∃ ds, VEnv.WF' ds env` at
   `Lean4Lean/Theory/Typing/Env.lean:136`.  Tree covered: the repository root recursively, i.e.
   `Lean4Lean/` (all of `Theory/`, `Verify/`, `Experimental/`), `docs/`, `scripts/`.
2. **So outcome 2 is not blocked on witness availability.**  It is blocked by §1: any witness
   refutes hole B.  The brief invited me to say "the witness is unreachable"; that would have been
   the wrong reason for the right caution.
3. **The `sorry` line numbers in circulation are slightly off.**  Hole A: theorem at
   `Injectivity.lean:261`, `sorry` at `:268`.  Hole B: `WF.rigidShapeUniqNS` at `:1046` — *not*
   `:1252`, which is `IsDefEqU.sort_forallE_inv`, the blocked route.  Row 41 quotes `:1252` for the
   route and it is right about that; nothing quotes 1046.
4. **The semantic route is not available as a backstop and should not be quoted as one.**
   `InjSortPiModel.sortPiSupplyAll_iff` proves the model-side supply is *equivalent* to
   `RigidSortPiDisj`, so `semantic_rigidSortPiDisj` is a restatement.  The content
   (`interp_sort_ne_interp_forallE`) is a theorem, but cashing it needs `SetModel.sound`'s deferred
   inputs.  I did **not** use it, and no theorem here depends on the model.

## What I did not do, as the negatives they are

* **Not proved.**  The remaining obligation is `SortPiMid` — a shapeless midpoint between a sort and
  a Π — and by `sortPiMid_iff` that is the coordinate itself.  I found no level-based route: the
  shared-type reading is already exhausted by `UnivDiscrim`'s "Reason 2" (cited at
  `Injectivity.lean:520-524`), and hole A's own output at a manufactured Π/Π link
  (`∀ (_ : Sort a). C` vs `∀ (_ : ∀A.B). C`, congruence on the sort/Π link) hands back only facts
  already in hand — I tried this on paper, not in Lean, and it is a **guess** that no variant of it
  works.
* **Not refuted.**  No `VEnv.WF` environment satisfying hole A and refuting `SortPiDisjUC` is
  exhibited, and §1 says exhibiting one refutes hole B.
* **The graded route is dead for the same reason, and I checked it on paper only.**
  `DefInvRefute.SortForallEDisjN` has `sortForallEDisjN_zero` free, and the ledger notes
  `SortForallEDisjN ∅ 1 1` is open; reading the `Stratified` constructor list, `trans` at `n+1` has
  both premises at `n+1`, so there is no descent in `n` and the derivation-induction hits exactly
  the same shapeless-midpoint case.  **Guess, not theorem**: I did not formalise this.
* **Not tried: narrowing `SortPiMid` by midpoint class.**  `RigidConstSortDisj` and
  `RigidConstPiDisj` — two of the three constant-spine conjuncts already carried in §1 — say
  precisely that a *rule-free* constant spine is convertible to neither a sort nor a Π.  If the
  `.app`/`.const` midpoints of `sortClass_of_wf` were decomposed into spines, those two would kill
  the rule-free ones outright, leaving `bvar`, `lam`, and δ-reducible spines.  That is the cheapest
  unexplored narrowing I can see and it is the first thing to pick up.  It needs `VExpr.mkApp`
  spine decomposition, which is why I did not do it inside this round's budget.

## Pick up first

1. The midpoint-class narrowing just above — it is arithmetic on the existing hypothesis set, and
   it would turn `SortPiMid` into a residual about three named midpoint shapes.
2. `SortPiCR` handed to the confluence stream (`docs/handoff-confluence.md`), as the *weakest*
   request that closes this coordinate: `join` plus class-preservation, no `Agree` algebra.
3. Anyone closing hole B along `PiInvResidual.rigidShapeUniqNS_of_constSpine` gets this coordinate
   for free (`sortPiDisjUC_of_rigidShapeUniqNS`) **and** hole A for free
   (`ForallInvPrice` §8).  The corner is now one theorem.

## Substitutions that become available (I edited no file but my own)

* In `ForallInvPrice.convStep2_shapeLinkAgree_iff`, the right-hand side's second coordinate may be
  replaced by `env.RigidShapeUniqNS U` whenever the three constant-spine conjuncts are in hand
  (`sortPiDisjUC_iff_rigidShapeUniqNS`).  No edit is proposed; `ForallInvPrice.lean` is read-only
  for me and the substitution is stated, not made.
* Nothing in `Injectivity.lean` changes.  Both `sorry`s stay where they are, for the reason ledger
  row 177b gives.

## Cross-stream note (in flight, not depended on)

An uncommitted file by a concurrent stream, `Theory/Typing/RigidConstPrice.lean`, proves
`constFamily_iff_rigidShapeUniqNS`: over `VEnv.WF ∧ ConvStep2 ∧ ShapeLinkAgree`, the three
constant-spine conjuncts are **jointly equivalent to hole B**.  Note the two results do **not**
discharge each other's hypotheses: their base hypothesis `ShapeLinkAgree` *is* hole A ∧ this
coordinate (`ForallInvPrice` §3), so their backward direction already assumes what my forward
direction is trying to reach, and my forward direction assumes the three conjuncts their backward
direction produces.  Composed, the two say: over `WF` and hole A, **{coordinate ∧ const family} and
{coordinate ∧ hole B} are the same hypothesis set**, with the coordinate the only member of neither
reduction's output.  My file takes no dependency on theirs and does not import it.
