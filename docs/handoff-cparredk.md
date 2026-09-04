# `CParRedK` — the complete development for `ParRedK`

Stream: `Lean4Lean/Theory/Typing/CParRedK.lean` (new) + this file. Started 2026-09-04 at HEAD
`e0aee76`, which I verified builds green **before** touching anything: bare `lake build`,
`Build completed successfully (1659 jobs)`, exit 0. The brief's figure for HEAD was 1659, so the
tree I started from is the tree the brief measured.

Target: the object `CRKProve.lean` says is missing — "a complete development `CParRedK`
(`exists.lean`: `CParRedK`, `CParRedK.exists`, `ParRedK.triangle`, `ParRedK.church_rosser` all
**NOT FOUND**)" — and then `ParRedKDiamond`, and then `CRKProve.crStatementK_of`.

---

## §1 Priors, written before any Lean and never edited

Written after reading, in this order: `CLAUDE.md`; `CRKProve.lean` in full;
`ChurchRosser.lean`:740–800 (`ParRed`, `NonNeutral`, `CParRed`), 1012–1240 (`CParRed.toParRed`,
`CParRed.exists`, `ParRed.triangle`, `ParRed.church_rosser`); `KEta.lean`:137–160 (`EtaK`),
325–400 (`ParRedK`), the `EtaKDiamond` definition; `KRule.lean`:55–161 (`KStep`);
`ParRedMissing.lean` in full; `KDiamondJoin.lean`'s header and outline; `KSite7App.lean`:440–535.
No Lean written, no cone measured, and I have **not** read `KKetaRow.lean`'s `ParRedKn`,
`KMeasure.lean`'s `EtaKn`, or `KEtaDiamond.lean`'s `EtaKD` beyond their one-line `inductive`
signatures from a grep.

### Shape priors

**S1 — Does the target already exist, searched by conclusion head?**
The obligation names are `CParRedK`, `CParRedK.exists`, `ParRedK.triangle`. Name search cannot
settle this (the brief's own rule), so the conclusion heads to search are:
`∃ _, <rel> Γ e _` for any relation that extends `ParRedK`; and the triangle head
`∃ o', ParRedK Γ e' o' ∧ NormalEq Γ o' o` (equivalently: any conclusion that is a conjunction of
a `ParRedK`/`ParRedKS` and a `NormalEq` **with the same right-hand metavariable pattern as the
triangle**, which is what distinguishes a triangle from `Joins`).
*Prediction:* the *inductive* `CParRedK` and the triangle are genuinely absent — I expect
`CRKProve`'s NOT-FOUND to survive at `e0aee76` — **but I predict the canonical-choice machinery
is already in the tree under a different name**, specifically `KEtaDiamond.lean`'s
`EtaKD (dom : VExpr → Option VExpr)`, whose `dom` argument is a *pinned* (deterministic) η-tower.
If so, the brief's "a canonical K-contractum … is where the work is" is already half-paid, and
the honest thing is to reuse `EtaKD`/`EtaKn` rather than invent a second pinning. Confidence
that `CParRedK` is absent: high. Confidence that a pinned η-tower already exists: 0.7.

**S2 — Is the work in the direction the brief thinks?**
The brief says: "Expect the classical decision (`NonNeutralK`) and a canonical K-contractum to be
where the work is", quoting `KSite7App.lean`'s ledger row 2 verbatim ("`CParRed.exists` — needs a
classical decision of `NonNeutralK` and a canonical K-contractum").
*Prediction: that row is wrong about which half is hard, and the classical decision is free.*
`CParRed.exists` inducts on the *term* with `VExpr.brecOn`. Every `CParRed` constructor recurses
only into **subterms** of `e` (`extra` develops the matched arguments `m2`, which are subterms;
it does **not** develop the rule's right-hand side). `ParRedK.keta` breaks exactly that
invariant: `keta : EtaK Γ e w → ParRedK Γ w w' → ParRedK Γ e w'` recurses into the *contractum*
`w`, which is not a subterm of `e` and for `EtaK.under` is strictly **larger** (`.lam A t` with
`t` obtained from `.app e.lift (.bvar 0)`). So:
- I predict `CParRedK.exists` is **not** provable by `VExpr.brecOn` at all, and the obstruction is
  not the decision procedure but **well-foundedness of the K-contraction chain**: a complete
  development must develop the contractum, and nothing in `Params` says the rule table
  terminates. I expect to need either a grade (`ParRedKn`-style) or an `Acc` premise on the
  subject, and I predict the grade already exists (see S1).
- Corollary prediction: `ParRedK` is **not a one-layer parallel reduction** — `keta`'s tail makes
  a single `ParRedK` step reach arbitrarily far down the K-chain. `CRKProve` §1's argument that
  the diamond's legs can be single steps ("`ParRedK` is a *parallel* reduction, so … the pair
  closes at single-step legs") uses that non-one-layer character *in its favour*; I predict the
  same property is what makes the *development* hard, i.e. the single-step legs and the missing
  development are two faces of one fact.
Confidence the decision is free: 0.85. Confidence the contractum-recursion is the real
obstruction: 0.8.

**S3 — Is what I am about to trust a measurement or a docstring?**
Three claims I will consume, classified before use:
- `CRKProve.lean`: "cone 3859 … holes `{weakN_iff, forallE_inv_stratified, WF.rigidShapeUniqNS}`
  — three, and `NormalEq.descend` is absent … gives 3931/3 and 3929/3 against the tree's 4431/4".
  This is labelled "measured 2026-09-04 at `ca04f43`". HEAD is `e0aee76`, **two commits later**
  (#42 dropped the frozen axiom `Expr.replace_eq`, 25→24; #43 trimmed `implGapWhitelist` 54→2).
  *Prediction:* the 3931/3 figure is a **measurement at a different commit**, and I must re-run
  it rather than quote it. I predict the *hole count* 3 is stable (both commits touched
  `Expr`-level/impl-gap machinery, not the `Theory` conversion cone) but the *population* 4431
  may have moved, because #42/#43 delete declarations. Confidence the hole set is unchanged: 0.8.
  Confidence the population number is unchanged: 0.4.
- `KSite7App.lean` ledger row 2, quoted in S2 — a **docstring**, not a measurement, and S2 says
  what I think it gets wrong. I will contradict it only with the quote in hand.
- `KEta.lean`'s `EtaKDiamond` docstring and `CRKProve.etaKDiamond_of_crStatementK` — the latter is
  a compiled theorem, so the circle is a *measurement*. `#print axioms` before I quote it.

**S4 — What is the *shape* of the residual, and is it EtaKDiamond or something weaker?**
`CRKProve` scored this UNTESTED and it is the question I was handed. Prediction, made before any
Lean: the triangle's resisting case is **`keta × keta` at two different tower heights**, and the
residual is **not** weaker than `EtaKDiamond` — it is *stronger*, i.e. triangle-shaped:
`EtaK Γ e w₁ → EtaK Γ e w₂ → CParRedK Γ w₂ o → ∃ o', ParRedK Γ w₁ o' ∧ NormalEq Γ o' o`
(single-step first leg, canonical second), where `EtaKDiamond`'s conclusion is `Joins` (multi-step
both legs). If that is right then the round's outcome is: the development exists, the triangle
reduces to a *triangle-shaped* η-residual, and `CRKProve`'s circle is **tighter** than it looks,
because a `Joins`-shaped input cannot discharge a triangle-shaped residual — the same asymmetry
`CRKProve.ParRedKS.church_rosser`'s docstring already records for the diamond
("with `Joins` legs … the diamond call needs shape `ParRedKS × ParRedK → Joins`, i.e. a *strip*
lemma, whose own induction is not structurally smaller"). I predict I will hit the *same* wall one
level down, and that this is the finding rather than a failure. Confidence: 0.6.

**S5 — Is `EtaK` deterministic?** If it were, the whole keta×keta case collapses to `rfl` and the
triangle closes with no η-residual at all. Prediction: **not provably deterministic**, and the
reason is `Params.pat_uniq`'s reach: `EtaK.here` at `e = .app f h` needs a registered
`.app p₁ p₂` matching a spine of length `arity p₁ + 1`, while `EtaK.under` needs one matching a
spine two longer, and two registered patterns of *different arity* on the same head have
`Pattern.inter = none`, so `pat_uniq`'s hypothesis is unsatisfiable and both may be registered.
I predict I can *prove* non-determinism is not excluded (i.e. no `EtaK.uniq` in the tree) but
cannot exhibit a two-tower instance without a new `Params`, so the honest verdict on
determinism will be "unproved, not false". Confidence: 0.75.

### Cost priors (after the shape priors, deliberately)

**C1** The definition + `toParRedK` + the `¬NonNeutralK` plumbing: cheap, under an hour.
**C2** `CParRedK.exists`: I expect this to be where the round is decided, and I expect it to
*fail* in its unconditional form. Budget the majority of the round here.
**C3** The triangle: I expect to reach it only in a *conditional* form and I do not expect
`crStatementK_of` to be fed unconditionally this round. So: **I predict the 3931/3 figure cannot
be banked**, and that the deliverable is a sharp statement of the residual plus its
irreducibility, not the unconditional theorem. Confidence: 0.7.

---

## §2 Measurements, appended as they land (never rewritten)

### M1 (answers S1) — the target is absent at HEAD; the pinning is *already proved*

`lake env lean --run scripts/exists.lean`, 2026-09-04, HEAD `e0aee76`, **population 473 built
modules** (`CRKProve`'s figure was 471 at `ca04f43`, so the population *did* move — S3's caution
was right, and I will not quote `CRKProve`'s numbers without re-running).

NOT FOUND: `CParRedK`, `CParRedK.exists`, `ParRedK.triangle`, `ParRedK.church_rosser`,
`NonNeutralK`, `CParRedKn` (and their `VEnv.`-qualified forms). **S1's absence half: confirmed.**

FOUND, and this is S1's other half scoring **better than predicted**:

| name | module | arity | cone | own hole | cone reaches `sorryAx` |
|---|---|---|---|---|---|
| `VEnv.ParRedK` | `KEta` | 4 | 4 | no | no |
| `VEnv.ParRedKn` | `KKetaRow` | 5 | 5 | no | no |
| `VEnv.EtaKn` | `KMeasure` | 5 | 5 | no | no |
| `VEnv.EtaKD` | `KEtaDiamond` | 6 | 6 | no | no |
| `VEnv.CParRed.exists` | `ChurchRosser` | 6 | **3461** | no | **no** |
| `VEnv.EtaKDiamond` | `KEta` | 1 | 37 | no | no |
| `VEnv.CRStatementK` | `CRShape` | 1 | 37 | no | no |

I predicted (0.7) that a pinned η-tower exists. It does — `EtaKD (dom : VExpr → Option VExpr)` —
but the *stronger* fact is `KMeasure.EtaKn.height_uniq`: **the η-tower height is a function of the
term, not of the derivation.** `EtaKn.height_eq` derives `e.appDepth + k = p₁.depth + 1` from
`Params.pat_app_depth_uniq`, so two `EtaK` derivations at the same subject have the *same* number
of `under` layers. Its docstring says this outright and corrects an earlier handoff:

> **The height is a function of the term, not of the derivation.** … This **corrects
> `docs/handoff-krule.md` §T6**, which prices `EtaKDiamond` as *not* implied by `KDiamond` on the
> grounds that "the two contracta live at different arities". They do not.

**Consequence for this round, and it reshapes the task:** the "canonical K-contractum" that
`KSite7App` row 2 asks for is *not* one problem but two, and only one of them is open. The
η-tower part is already canonical (height pinned by `height_uniq`, and `EtaK.under`'s premise
`Γ ⊢ e : .forallE A B` fixes `A` up to conversion). What is **not** canonical is the `KStep` at
the bottom of the tower: `KStep.mk`'s `hdq : IsDefEq Γ h c A₀` lets an *arbitrary* convertible `c`
be chosen, and different `c` give different `r.1.apply m1 m2`. That is exactly `KDiamond`/M3, and
`KDiamondJoin.lean` has already established it is only true up to **joinability**, not on the
nose (`quotParams_not_kDiamond`). So a complete development cannot pick a canonical K-contractum
by any construction internal to `KStep`; it must either take M3 as a hypothesis or make the
contractum a *choice* and pay for it in the triangle.

### M2 (answers S2, first half) — the grade exists and `keta` decreases it

`KKetaRow.ParRedKn` is `ParRedK` indexed by redex-nesting height: `beta`, `extra`, `keta` all take
`n → n+1`, congruences keep `n`, with `ParRedKn.toParRedK`, `ParRedKn.mono`, `ParRedKn.rfl` all
proved. So S2's predicted need for a grade is met by an object already in the tree — I do not
have to invent one. Its docstring is explicit that the uniform (non-additive) indexing is
deliberate:

> `ParRedKn` is therefore not a mere copy of `ParRedK` with a counter: the choice of `n` on both
> children of `app`/`lam`/`forallE` is what makes `app_bvar` below true.

### M3 (**corrects M1**, and a tooling defect worth its own line)

**`NonNeutralK` already exists** — `KEta.lean`:476, `Lean4Lean.VEnv.NonNeutralK`, arity 3,
cone 646, hole-free — with *exactly* the three-disjunct definition I was about to write, and with
a docstring that already assigns it to this job:

> `CParRed`'s neutrality test gains a third disjunct: a term whose η-expansion is a K-redex is not
> neutral either. `CParRed.exists` must decide it, classically.

I found this the worst possible way: Lean told me `` `Lean4Lean.VEnv.NonNeutralK` has already been
declared`` when I compiled my own copy. **M1's "NOT FOUND: … `NonNeutralK`" was false**, and the
cause is a defect in the tool, not in the tree:

> **`scripts/exists.lean` does not prepend `Lean4Lean` to the query name; `scripts/shape.lean`
> does.** So `exists.lean NonNeutralK` and `exists.lean VEnv.NonNeutralK` both print `NOT FOUND`
> for a constant that exists as `Lean4Lean.VEnv.NonNeutralK`. The script's own header says
> "`NOT FOUND` is the only output that licenses the word 'absent' in a brief" — and here it
> licensed a false one. Every absence claim made with an unqualified name through this script is
> unsound.

Re-run with fully qualified names, same commit and population:
`Lean4Lean.VEnv.CParRedK`, `Lean4Lean.VEnv.CParRedKn`, `Lean4Lean.VEnv.CParRedK.exists`,
`Lean4Lean.VEnv.ParRedK.triangle`, `Lean4Lean.VEnv.ParRedK.church_rosser` — **all still NOT
FOUND**, so M1's headline (the development and the triangle are absent) survives; only the
`NonNeutralK` row was wrong. The conclusion-head cross-check backs it up: `shape.lean` on
`{Lean4Lean.VEnv.ParRedK, Lean4Lean.VEnv.NormalEq}` returns 26 constants and not one is a
triangle or a development (the cheapest are `quotParams_parRedKDiamond_at_kDiamond_witness`,
`joins_normal_iff`, `not_joins_of_normal`, `parRedKStatement_of_domEq`); on
`{EtaK, ParRedK, NormalEq}` it returns 4, all `KMeasure` weakening-inversion lemmas.

**Score for S1: half right, and the wrong half was my own measurement.** The prediction "the
canonical-choice machinery is already in the tree under a different name" was right twice over
(`EtaKD`, `EtaKn.height_uniq`) and I *still* duplicated `NonNeutralK`, because I searched by
conclusion head for the *triangle* and by name for the *predicate* — and the name search was the
one that was broken. Using KEta's definition from here on.

### M4 — **the complete development exists.**  `CParRedKn` + `CParRedKn.exists`, compiled

`Lean4Lean/Theory/Typing/CParRedK.lean`. Definition: `CParRedKn : Nat → List VExpr → VExpr →
VExpr → Prop`, `ChurchRosser.CParRed`'s nine constructors with `NonNeutralK` (KEta's) for
`NonNeutral` in the two guarded ones, plus `keta`, plus a grade. Grade `0` is reflexivity
(`zero`); at grade `n+1` congruences/`beta`/`extra` keep the grade and **`keta` drops it to `n`**.

**S2 scored RIGHT, and this is the shape result.** `KSite7App.lean` ledger row 2 says, verbatim:

> `CParRed.exists` -- needs a classical decision of `NonNeutralK` and a canonical K-contractum.

The classical decision was **free**: `Classical.byCases` at exactly the two sites
`CParRed.exists` already uses it (`.const`, `.app`), and the third disjunct of `NonNeutralK` costs
one extra `rintro` branch. What that row does not mention is the thing that actually decides the
proof: `ParRedK.keta`'s second premise develops the **contractum**, which is not a subterm of the
subject and for `EtaK.under` is strictly larger (`.lam A t` with `t` from `.app e.lift (.bvar 0)`),
so **`VExpr.brecOn` alone cannot carry the proof** — every other `CParRed` constructor recurses
only into subterms, `extra` included (it develops the matched arguments, never the rule's RHS).
The grade is what fixes it: induct on the grade *outside* the `brecOn`, and the `keta` case is
discharged by the grade IH at the contractum. That is why the object is `CParRedKn` and not
`CParRedK`, and it is not a weakening — `ParRedK.toN` (`KKetaRow`) already proves
`ParRedK = ⋃ₙ ParRedKn`, so a grade-indexed development still dominates every `ParRedK` step.

And the "canonical K-contractum" half of that row is, on the measurement, **not achievable at
all** and does not have to be: `KStep.mk`'s `hdq : IsDefEq Γ h c A₀` admits any convertible `c`,
so the contractum is not a function of the redex — `quotParams_not_kDiamond` is exactly that.
`CParRedKn.keta` therefore takes `EtaK Γ e w` as a *free choice*, like `CParRed.extra` takes its
rule, and the non-canonicity is paid for in the triangle instead (§3 below). Row 2 asks for an
object that the tree already refutes the existence of.

Measured 2026-09-04, HEAD `e0aee76` + this file, `scripts/exists.lean`, population 475:

| name | arity | cone | own hole | holes in cone |
|---|---|---|---|---|
| `CParRedKn.exists` | 7 | **3603** | no | `{IsDefEqU.forallE_inv_stratified}` — **one** |
| `CParRedKn.toParRedK` | 6 | 680 | no | **none** |
| `CParRed.exists` (the `ParRed` analogue) | 6 | 3461 | no | none |

`#print axioms Lean4Lean.VEnv.CParRedKn.exists` = `[propext, sorryAx, Classical.choice, Quot.sound]`
— `sorryAx` **inherited, not mine**: my own value is not a hole and the single hole in the cone is
`IsDefEqU.forallE_inv_stratified`, which enters through `EtaK.defeqU`'s `under` case (it needs
`Γ ⊢ e : .forallE A B`'s own well-formedness to type the η-expansion). `Classical.choice` is the
`NonNeutralK` decision, i.e. the one cost row 2 *did* predict.

*One hole is not two, and the difference was a one-line choice.* My first version typed the
contractum with `(ParRedK.keta_step hek).hasType`, giving cone 3763 and holes
`{forallE_inv_stratified, WF.rigidShapeUniqNS}` — `ParRedK.defeq`'s `beta` case pulls
`IsDefEq.uniqU` in. Routing through `EtaK.defeqU` directly (which needs no `beta` case) drops
`rigidShapeUniqNS` and 160 constants. Recorded because the delta is invisible unless measured.

### M5 — the assembly compiles; the conditionality *moves*, it does not go away

`parRedKDiamond_of_triangle : ParRedKnTriangle → ParRedKDiamond` (cone 3842) and
`crStatementK_of_triangle : ParRedKStatement → ParRedKnTriangle → CRStatementK` (cone 3920), both
holes `{weakN_iff, forallE_inv_stratified, WF.rigidShapeUniqNS}` — the same three as
`CRKProve.crStatementK_of` (cone 3859), so **nothing new is tainted**. The proof is
`ParRed.church_rosser`'s three lines plus one: grade each step with `ParRedK.toN`, develop at the
maximum with `CParRedKn.exists`, run the triangle twice, join with `NormalEq.trans`/`.symm`.

**This answers S2's corollary prediction with a correction.** I predicted the single-step legs and
the missing development were "two faces of one fact". They are related but not the same: the grade
is what reconciles them. A *single* `CParRedKn m` cannot dominate every `ParRedK` step, because
`keta`'s tail is unbounded — but it does not have to, since `ParRedK.toN` bounds the *two given*
steps and the development is taken at their maximum. So `CRKProve` §1's single-step legs survive
and the development exists; the tension I predicted was real and the grade dissolves it.

### M6 (answers S4, and **scores it WRONG**) — the `keta` × `keta` row does *not* resist

S4 predicted (0.6): "the triangle's resisting case is `keta` × `keta` at two different tower
heights, and the residual is … stronger than `EtaKDiamond` … triangle-shaped". **Wrong on the
first clause and right for the wrong reason on the second.**

`keta_keta_row` (compiled, cone 3811) closes that row in three lines from a residual
`KetaDevAgree` plus the grade IH: develop the *step's* contractum at the same grade, close the
step against that development by the grade IH (available precisely because `keta` drops the grade),
transport across `KetaDevAgree`. Two things I had not seen:

- The "different tower heights" worry is **already dead in the tree**: `KMeasure.EtaKn.height_uniq`
  proves the height is a function of the subject (M1). I read that before writing S4 and still
  wrote "two different tower heights" — a shape prior contradicted by a measurement I had already
  taken.
- The residual is not triangle-shaped; it is **nose-shaped on developed subjects**, which is a
  direction I had not considered at all. It is weaker than `KDescend.KDiamond` (developments absorb
  a β the raw contracta cannot) and not comparable to `EtaKDiamond` (no legs, developed subjects).

What *does* resist is the pair of rows where the development fires `keta` and the step does
something else at the same node: `KetaAppRow` (step congruences at the application) and
`KetaExtraRow` (step fires a pattern rule). `keta_root_row` (cone 3867) compiles the whole
nine-subcase ledger: five vacuous by `EtaK.not_bvar/not_sort/not_lam/not_forallE` and the new
`EtaK.not_beta` (a β-redex has a λ spine head, so `EtaK.spineHead_const` excludes it — this kills
the `keta` × `beta` row **in both orders**), one closing outright (`const`, take `o' = o` and
`NormalEq.refl`), one from `KetaDevAgree`, two open.

**Verdict on the two open rows: unproved, not false**, and this is a bounded claim:
- Both hold at `refParams` (`refParams_ketaAppRow`, `refParams_ketaExtraRow`) — vacuously,
  `KStep` is empty there, and that is a consistency check, not evidence.
- No refutation of any triangle row exists in the tree: `shape.lean` on
  `{Lean4Lean.VEnv.ParRedK, Lean4Lean.VEnv.NormalEq}` returns 26 constants, none a negation.
- The missing work is *named*: `ParRed.triangle`'s `extra` inner induction (60 lines proving that a
  registered pattern survives reduction in matched positions, with `Params.pat_uniq` resolving the
  case where a redex fires inside the skeleton), extended by a `keta` constructor. I did **not**
  run it, so "unproved" here means "I did not prove it and nothing else does", not "it is hard".

### M7 (the firing, at the non-degenerate instance)

`quotParams` — `CRKProve` §3.1's one instance of eight where the rule contracts and `CRStatement`
is refutable. Three compiled theorems, all inside `attribute [local instance] quotParams`:

- `quotParams_dev_gx` : the development of `g x` is `g x`.
- `quotParams_dev_beta` : the development of `g ((fun y => y) x)` is **`g x`, on the nose** — the
  β-redex sits in the argument and the development contracts it.
- `quotParams_ketaDevAgree_at_kDiamond_witness` : `∃ o`, both develop to the *same* `o`, at every
  positive grade. Cone 9297, holes `{forallE_inv_stratified, WF.rigidShapeUniqNS}` — **exactly**
  `CRKProve.quotParams_parRedKDiamond_at_kDiamond_witness`'s cone 9287 and hole set, so the firing
  is as clean as the witnesses already in the tree and adds no taint.
- `quotParams_devAgree_normalEq` : the same pair as `KetaDevAgree`'s conclusion proper.
- `quotParams_dev_exists` : `CParRedKn.exists` instantiated at `qLiftT`, the term
  `CRKProve.quotParams_parRedK_qLiftT` moves with a `keta` step — so the development is taken at a
  subject whose root step really is `keta`, not at a rigid one.

The pair `(g x, g ((fun y => y) x))` is the pair `Verify/QuotAppParams.quotParams_not_kDiamond`
refutes the nose diamond with, and `not_normalEq_gx` shows the *raw* contracta are not `NormalEq`.
**That refutation is conditional on the injectivity corner and must not be quoted as
unconditional** (`CRKProve`'s own note, and commit `a561fa9` says so in capitals). What I add is
unconditional-relative-to-that: the *developments* coincide syntactically.

### M8 (answers S3) — 3931/3 reproduces exactly, and still cannot be banked

`scripts/exists.lean`, 2026-09-04, HEAD `e0aee76` + this file, population 477:

| declaration | cone | holes |
|---|---|---|
| `IsDefEqU.constApp_forallE_false_ofHyps` (`CRKProve`) | **3931** | 3 |
| `crStatementK_of` (`CRKProve`) | 3859 | 3 |
| `crStatementK_of_triangle` (this file) | 3920 | 3 |
| `parRedKDiamond_of_triangle` | 3842 | 3 |
| `keta_root_row` | 3867 | 3 |
| `keta_keta_row` | 3811 | 3 |
| `CParRedKn.exists` | 3603 | **1** |
| `CParRedKn.toParRedK` | 680 | **0** |

holes = subset of `{IsDefEqU.weakN_iff, IsDefEqU.forallE_inv_stratified, WF.rigidShapeUniqNS}`;
`NormalEq.descend` is absent from every row, as `CRKProve` found.

**S3 scored: right on the hole count (0.8 → correct), wrong on the population (0.4 → the
population moved 471 → 473 at HEAD and 477 with this module, but the *cone* figure 3931 is
byte-identical).** So the number was safe to quote after all — but only because I re-ran it, and
the thing that actually moved (the population) is the one I would have quoted wrongly.

`#print axioms`, all measured:

| declaration | axioms |
|---|---|
| `CParRedKn.toParRedK`, `EtaK.not_beta`, `ParRedKn.zero_eq`, `not_nonNeutralK_app_bvar` | `[propext, Quot.sound]` |
| `refParams_ketaDevAgree` | `[propext, Classical.choice, Quot.sound]` |
| `CParRedKn.exists`, `parRedKDiamond_of_triangle`, `crStatementK_of_triangle`, `keta_keta_row`, `keta_root_row`, all three `quotParams_*` | `[propext, sorryAx, Classical.choice, Quot.sound]` |

`sorryAx` is inherited in every case (own value never a hole), and `Classical.choice` is the
`NonNeutralK` decision — the one cost `KSite7App` row 2 correctly predicted.

---

## §3 Verdicts

**V1 — Does the complete development exist now?  YES, unconditionally.**
`CParRedKn` + `CParRedKn.exists`, `Lean4Lean/Theory/Typing/CParRedK.lean`, cone 3603, own value
not a hole, one inherited hole (`IsDefEqU.forallE_inv_stratified`) and `Classical.choice`. It is
graded, and the grade is forced (M4), not a weakening: `ParRedK.toN` makes `ParRedK = ⋃ₙ ParRedKn`
and `parRedKDiamond_of_triangle` shows the grading is transparent to the diamond.

**V2 — Can the 3931/3 figure be banked?  NO, and the reason is precise.**
The figure *reproduces exactly* at HEAD (M8), so it is not stale. But it is the cone of
`IsDefEqU.constApp_forallE_false_ofHyps`, a theorem with two hypotheses, and this round discharges
neither. What it does is replace the second one: `ParRedKDiamond` → `ParRedKnTriangle`, which is
better in three measurable ways — it is the exact analogue of a *theorem* (`ParRed.triangle`) one
relation over rather than of a theorem's conclusion; six of its nine new rows are compiled closed;
and the two that remain are named, vacuously true at the only degenerate instance, and unrefuted.
`CRKProve`'s warning was "nobody should bank it before `CParRedK` exists". `CParRedK` now exists,
and that is necessary, not sufficient.

**V3 — What resists, and is it false or unproved?**
`KetaAppRow` and `KetaExtraRow` — the two rows where the development fires `keta` and the step does
something else at the same node. **Unproved, not false.** Evidence for "not false", stated as
bounds rather than as a proof: both hold at `refParams`; no refutation of any triangle row exists in
the tree by conclusion-shape search; and the missing argument is a named, existing induction
(`ParRed.triangle`'s `extra` pattern-survival induction) extended by one constructor. I did not run
that induction, so this is "nobody has proved it", not "it is deep".

The row `CRKProve` and `KEta.lean` both expected to be the blocker — `keta` × `keta`, the row
`EtaKDiamond` was invented for — **is closed** (`keta_keta_row`), from a residual `KetaDevAgree`
that is strictly weaker than the refuted nose diamond and true at the witness that refutes it.

## §4 Limits of this result, and where I proved them

1. **The eight old triangle rows are not compiled.** `ParRedKnTriangle` is a hypothesis, and §5 of
   the source proves only the nine rows where `keta` is the development's root step. The other
   sixty-four rows are `ChurchRosser.ParRed.triangle`'s, and I assert only that they are *the same
   rows*, not that the port goes through — grade bookkeeping is a real cost (I hit it three times
   in §5 alone: `ParRedKn.extra`'s children sit at `n` while `CParRedKn.extra`'s sit at `n+1`,
   which is why `ParRedKnTriangle` carries `n ≤ m` and `KetaAppRow` carries `n ≤ m+1`). **Anyone
   quoting §5 as "the triangle is proved modulo two rows" would be overstating it: it is proved
   modulo two rows *and* an uncompiled port.**
2. **`KetaDevAgree` is not ground.** It follows from `CRStatementK` (two developments of one
   subject are defeq reducts; confluence upgrades defeq to `NormalEq`), so it sits inside the same
   circle `CRKProve.etaKDiamond_of_crStatementK` compiles. I did not compile that direction, so
   even this claim is stated, not measured. What §6 shows is only that it is *true at the
   configuration where its stronger cousin is false* — a satisfiability fact, not a discharge.
   `KDiamondJoin.lean` §3's conclusion stands: the break has to come from the rule table.
3. **`CParRedKn.exists` carries one hole where `CParRed.exists` carries none.** Measured, located
   (`EtaK.defeqU`'s `under` case), and reduced from two to one by routing around `ParRedK.defeq`.
   The remaining one is not obviously removable: typing the η-expansion needs the Π-typing's own
   well-formedness.
4. **The `quotParams` firing inherits `quotParams`'s taint** (`forallE_inv_stratified`,
   `WF.rigidShapeUniqNS`), which is the same taint every existing `quotParams` witness carries
   (cone 9297 vs `CRKProve`'s 9287). It is not a *new* dependency, and it is not unconditional.
5. **`ParRedKnTriangle` is a hypothesis about fixed inductives, which `ParRedMissing.lean` warns
   about.** I checked the warning applies to a different shape: its trap is stating a *missing
   reduction step* as a property of the relation being extended ("a missing reduction step must be
   stated as a **constructor of an extension**, never as a property of the relation being
   extended"), and its two refutations (`not_parRedProofRepl`, `not_parRedEtaContract`) are of Props
   that *add steps*. `ParRedKnTriangle` adds no step; it is a metatheorem of `ParRed.triangle`'s
   shape, and it is satisfied non-vacuously at `refParams` via `ChurchRosser`'s own theorem rather
   than by an empty hypothesis. That said, **I did not compile `refParams_parRedKnTriangle`** — it
   needs `ParRedKn → ParRed` and `CParRedKn → CParRed` at `refParams`, which is real work — so the
   non-vacuity claim for the *triangle itself* is argued, not measured. `refParams_ketaDevAgree`,
   `refParams_ketaAppRow`, `refParams_ketaExtraRow` *are* compiled, and all three are vacuous.

## §5 An edit outside my two files that I did **not** make

`scripts/exists.lean` produces **false absence reports** for unqualified names, which is how M1
came to say `NonNeutralK` was NOT FOUND (M3). Line 129 resolves the query name literally:

```lean
    let n := s.splitOn "." |>.foldl (fun acc c => Name.mkStr acc c) Name.anonymous
    match env.find? n with
```

`scripts/shape.lean` already does the right thing (lines ~110): it tries `n` **and**
`` `Lean4Lean ++ n``, and hard-fails if neither resolves. The exact edit, stated and not applied
because I own only two files:

```lean
    let n0 := s.splitOn "." |>.foldl (fun acc c => Name.mkStr acc c) Name.anonymous
    let n := if env.contains n0 then n0 else `Lean4Lean ++ n0
    match env.find? n with
```

with the printed name kept as `s` so output is unchanged for already-qualified queries. Without it,
every "NOT FOUND, therefore absent" claim made through this script with an unqualified name is
unsound — and the script's own header calls `NOT FOUND` "the only output that licenses the word
'absent' in a brief".

## §6 Method gaps, mine

1. **I ran the conclusion-head search for the *triangle* and a name search for the *predicate*, and
   only the name search was broken.** The brief's rule ("search by conclusion head, never by the
   obligation's name") is exactly what would have caught `NonNeutralK`, and I applied it to the
   hard target and not to the easy one. The general lesson is worse than the specific one: I
   trusted a script's negative output without checking that its resolver could have found a
   positive.
2. **S4 contradicted a measurement I had already taken.** I wrote "two different tower heights" in
   a shape prior *after* recording `EtaKn.height_uniq` in M1, which proves the heights are equal.
   Writing §1 before any Lean does not protect against writing §1 after a measurement and ignoring
   it.
3. **I did not attempt the triangle port and therefore cannot say whether it goes through.** That
   is the single biggest hole in this round's verdict, and it is a budget choice, not a finding: I
   spent the round on the object (V1) because the brief asked whether it exists, and the port is
   the natural next round. Concretely, the next round should port `ParRed.triangle`
   (`ChurchRosser.lean`:1073–1225) to `ParRedKn`/`CParRedKn`, reusing `keta_root_row` for the nine
   new rows, and will find out whether `KetaAppRow`/`KetaExtraRow` fall out of the `extra` inner
   induction's `.inr` branch.
4. **Nothing in this round tests `KetaDevAgree` against a *second* configuration.** One witness at
   `quotParams` is one witness. `appParams` (`PatAppParams.lean`) is the other instance registering
   `.app` patterns and I did not fire there.

## §7 Build record, dated — and HEAD moved under me

| when | commit | command | result |
|---|---|---|---|
| round start | `e0aee76` | bare `lake build` | green, **1659 jobs**, exit 0 (matches the brief's figure) |
| round end | `4b7ec7c` + `CParRedK.lean` | bare `lake build` | green, **1663 jobs**, exit 0 |

`4b7ec7c` ("the mutual branch stands unconditionally…") landed from another stream while I was
working, together with two new untracked modules (`Verify/Inductive/PosScan.lean`,
`Tests/PosScanProbe.lean`) and `docs/handoff-posscan.md`, which is where three of the four extra
jobs come from; the fourth is mine. **So the closing "green" is green at a commit the brief did not
name.** The cone figures in M1/M4/M5/M7/M8 were all taken at `e0aee76` + this file; M8's headline
3931/3 was re-checked and is unchanged, but a reader comparing job counts against the brief should
use this table, not the brief.

Files touched: `Lean4Lean/Theory/Typing/CParRedK.lean` (new), `docs/handoff-cparredk.md` (new).
Nothing else, and no state-changing git command was run.
