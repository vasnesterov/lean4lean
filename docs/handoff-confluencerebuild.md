# Handoff — pricing the confluence-layer rebuild (over `IsDefEqSE` or not)

Round of **2026-09-04**.  Owner files: `Lean4Lean/Theory/Typing/ConfluenceRebuildPrice.lean`
(new) and this file.  **Pricing round — nothing else is modified.**  `ChurchRosser.lean`,
`KDescend.lean`, `DescendRefute.lean`, `StructEtaPrice.lean` are read-only here.

## §1 Written BEFORE any Lean — the brief, the risk, and what to do if this round is lost

Eleven API crashes this session; the only round that wrote no handoff first is the only one whose
report was lost.  So: the brief, verbatim in substance, and my starting priors, so that a
successor can resume from here even if nothing below §1 ever gets written.

### The hypothesis under test (the orchestrator's, explicitly unproved)

That these three are **one job**:

1. `Lean4Lean.VEnv.NormalEq.descend` is known-false — refuted hole-free by
   `Lean4Lean.descend_uniq_sortUniq_not_all` (`Theory/Typing/DescendRefute.lean`).  Root cause on
   record: `NormalEq` has `proofIrrel` and `etaL`/`etaR`; `ParRed` has no counterpart.
2. `parRed`'s statement is **also** refuted verbatim —
   `Lean4Lean.VEnv.not_parRedStatement_of_propMajor` (`Theory/Typing/ParRedPropRefute.lean`) —
   and `parRed` is not itself one of the 13 holes, so that is a second false statement in the
   same file.
3. Structure eta must eventually enter the abstract relation, and the cases the eta repair owes
   appear only once `NormalEq`, `ParRed` **and** `church_rosser` are re-erected over
   `Lean4Lean.VEnv.IsDefEqSE` (`Theory/Typing/StructEtaPrice.lean`).

Hypothesis: the confluence layer must be rebuilt regardless of eta, so rebuild it over the
*extended* relation and discharge the eta prerequisite in the same pass.

### The known obstacle handed to me

Measured import closures reportedly put `DescendRefute` (55), `KDescend` (59), `KSite7App` (64)
and `ParRedPropRefute` (62) **all downstream of `ChurchRosser`**, so no in-place rewiring is
possible.  A previous round called the rebuild "blocked" for exactly this reason.  **Every figure
in the brief is to be treated as unverified** — the orchestrator reports fifteen brief errors this
session, including one inverted conclusion.

### My priors before measuring (record them so bias is visible)

* (b) I expect the layering obstacle is **not** fatal and the brief's own phrasing gives it away:
  "downstream of `ChurchRosser`" is a fact about the *refutation witnesses*, not about the
  *rebuilt layer*.  A rebuild lands in new modules that import `ChurchRosser`'s prerequisites but
  not `ChurchRosser`; the old declarations are then deleted.  The thing that would make it
  genuinely fatal is a cycle **through the new relation's definition site**, i.e. if
  `IsDefEqSE` has to live below `Basic.lean` while its η-expansion needs `Theory/Inductive`.
  `handoff-structetaprice.md` already flags exactly that cycle.  So I expect the fatal-looking
  item to be the `Basic.lean` cycle, not the `ChurchRosser` ordering.
* (a) I expect the two false statements are **one** job with each other and a **different** job
  from the eta re-erection, because both refutations turn on `proofIrrel` (a `Prop`-major-premise
  cycle), and structure eta is a `Type`-side rule.  If the restatement that repairs both is
  independent of which relation it is stated over, they are separable — and that is a
  machine-checkable claim: state the repair over an *arbitrary* relation.
* (c) I expect the price to be large: `StructEtaPrice` measured 136 hand-written eliminator
  sites across seven relations, of which `NormalEq` 31 + `ParRed` 26 + `ParRedK` 23 = 80 are the
  confluence layer's own.
* (d) I expect `SetModel.eq_singleton_of_recProp` verifies as claimed (hole-free), since the
  previous round printed axioms inline.

### If this round is lost after §1

Resume by: (i) re-running `scripts/exists.lean` on the six names in §2 below; (ii) computing
import closures with the one-liner in §3 rather than trusting 55/59/62/64; (iii) reading
`docs/handoff-confluence.md` §3 ("Why the rewiring is blocked") — that is the section this round
is auditing.

