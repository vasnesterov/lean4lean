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

---
---

# Round 2 (2026-09-04, later) — running the port, and completing the ledger

*Numbering note.* My brief says "§1 and §2 are the previous round's, do not edit them. Add §3
onward." Round 1 in fact used §1–§7. I have edited **nothing** above this line; my priors are §8,
my measurements §9, my verdicts §10, limits §11, method gaps §12. Round 1's §3–§7 are its own.

Started at HEAD `3aca413`, with `CParRedK.lean` and `docs/handoff-cparredk.md` already in the tree
from Round 1 (both untracked/modified — the brief's 1662-job figure is measured with them present).

## §8 Priors, written before any Lean and never edited

Written after reading, in this order: `CLAUDE.md`; `docs/handoff-cparredk.md` §1–§7 in full;
`Lean4Lean/Theory/Typing/CParRedK.lean` in full (all 477 lines); `ChurchRosser.lean`:730–830
(`ParRed`, `NonNeutral`, `CParRed`, `ParRed.rfl/lams/weakN`) and 1010–1250
(`CParRed.toParRed`, `CParRed.exists`, **`ParRed.triangle` in full**, `ParRed.church_rosser`);
`KEta.lean`:120–240 (`EtaK`, `HasEtaK`, `EtaK.matches_head/spineHead_const/not_*`, `EtaK.defeqU`)
and 341–357 (`ParRedK`); `KKetaRow.lean`:301–331 (`ParRedKn`, `.toParRedK`); `KRule.lean`:50–170
(`KStep`, `KStep.defeq`, `Params.no_kpattern`); `KDiamondJoin.lean`:1–225 (its whole prose header,
§1–§8, and the outline of all 39 declarations). No Lean written, no cone measured yet.

### Shape priors

**S8.1 — Does the target already exist, searched by conclusion head?**
The target is `ParRedKn.triangle` — conclusion head `∃ o', ParRedK Γ e' o' ∧ NormalEq Γ o' o`
with `e'` a `ParRedKn` reduct and `o` a `CParRedKn` reduct. Round 1 already searched that exact
head (26 constants on `{ParRedK, NormalEq}`, none a triangle) so I expect NOT FOUND and will not
spend the round re-establishing it. The *interesting* search is one Round 1 did not run: a lemma
of shape "a `KStep`/`EtaK` redex survives parallel reduction of its matched positions", i.e.
conclusion head `EtaK Γ e' _` or `KStep Γ e' _` **with `e'` a reduct**, which is what
`KetaAppRow` needs. `KSite7App.lean`'s ledger is named in Round 1 as the home of the twin rows,
so that file is the place to look.
*Prediction:* the triangle is absent; and a survival lemma of that head is **also** absent (if it
existed, `KSite7App`'s row would be closed). Confidence triangle absent: 0.95. Confidence a
usable survival lemma exists somewhere: 0.3.

**S8.2 — Is the work in the direction the brief thinks? The ledger's *second axis*.**
The brief hands me "two open rows (`KetaAppRow`, `KetaExtraRow`) + one 64-row port". Round 1's
`keta_root_row` covers `keta` **on the development's side** against all nine `ParRedKn`
constructors. But the triangle's table is `CParRedKn` (10 constructors: Round 1 added `zero` and
`keta`) × `ParRedKn` (9 constructors: adds `keta`) = 90 rows, and `ParRed.triangle`'s own table
is 8 × 8 = 64. So the new rows are **90 − 64 = 26**, not 9:
* dev = `keta` × 9 steps — Round 1's `keta_root_row`. Covered.
* dev = `zero` × 9 steps — forces `m = 0`, hence `n = 0` by the triangle's `n ≤ m`, hence `e = e'`
  by `ParRedKn.zero_eq`, which Round 1 already proved. One easy row.
* **step = `keta` × the 8 *old* development constructors — 8 rows Round 1 never named.**
*Prediction, and it is my main shape claim:* that third bullet exists, is unnamed, and **seven of
its eight rows are vacuous by lemmas already in `CParRedK.lean`** — `EtaK.not_bvar/not_sort/
not_lam/not_forallE/not_beta` for five of them, and `NonNeutralK.of_etaK` against the
`¬ NonNeutralK` guard on `CParRedKn.const` and `CParRedKn.app` for the other two. The eighth,
**dev = `extra` × step = `keta`**, is *not* guarded (`CParRedKn.extra` carries no `¬ NonNeutralK`)
and is a genuine open row: it is two K-ish rules firing at one node, i.e. `KDiamond`-shaped, and
it is the mirror image of `KetaExtraRow`. So the honest count of open rows is **three, not two**,
and the brief's "close all three" is really "close all four".
Confidence the 8-row axis is unnamed: 0.85. Confidence exactly one of the eight is non-vacuous:
0.75. Confidence that this changes the bankability verdict: 0.9 (it can only make it worse).

**S8.3 — Is what I am about to trust a measurement or a docstring?**
Three claims, classified before use:
* The brief: "The break is `kDiamondJ_of_patMajorCanonicalJ` (hole-free, `[propext, Quot.sound]`):
  M3 restated as joinability, a rule-table property with no confluence in it." The parenthesis is
  a **measurement** (I will re-run `#print axioms`). The clause after the colon is a **reading**,
  and `KDiamondJoin.lean` §3 — the file the brief tells me to read first — says the opposite in
  its own headline: "the localisation `PatMajorCanonical → KDiamond` was supposed to deliver is
  *gone* — `KDiamondJ` is sandwiched between two Church–Rosser statements", with
  `quotPat_argJoin_of_kDiamondJ` (advertised hole-free) as the lower bound: `KDiamondJ` at
  `quotPat` implies `g x` and `g x'` join for *arbitrary convertible* `x, x'`, which is
  Church–Rosser at an application.
  *Prediction:* the brief's "break" is **not** a break — routing a residual through
  `PatMajorCanonicalJ` re-enters confluence one level down, exactly as
  `etaKDiamond_of_crStatementK` does. Therefore I should **not** aim my residuals at `KDiamondJ`.
  Confidence 0.8. I will check by reading `quotPat_argJoin_of_kDiamondJ`'s statement and axioms,
  not its docstring.
* Round 1's "the other sixty-four rows are `ChurchRosser.ParRed.triangle`'s, and I assert only
  that they are *the same rows*, not that the port goes through" — a **stated limit**, correctly
  labelled. I take it as an admission, not as evidence.
* `Verify/QuotAppParams.quotParams_not_kDiamond` is **conditional on the injectivity corner**
  (Round 1's §4.4, commit `a561fa9` "in capitals"). Anything I say about `KDiamond` being false
  inherits that condition and I will say so every time.

**S8.4 — Hypothesis diff against neighbours (method rule 3), before attacking either row.**
`keta_keta_row` — the neighbour that *closed* — carries, besides the six hypotheses `KetaAppRow`
has, the **grade induction hypothesis** `IH : ∀ n Γ e e' o A, n ≤ m' → … → ParRedKn n Γ e e' →
CParRedKn m' Γ e o → ∃ o', …`. `KetaAppRow` and `KetaExtraRow` as written carry **no IH at all**.
*Prediction:* that is the omission method rule 3 warns about, and it is load-bearing: without an
IH there is no way to descend into `f`/`a` (for the app row) or into the matched arguments (for
the extra row), and both rows are *understated* — as `Prop`s with no IH they are strictly stronger
than what the triangle needs. So a fair restatement adds the IH.
Confidence the IH is missing from both: 0.9 (this is nearly a reading, not a prediction).
Confidence that adding the IH is *sufficient* to close either: 0.35 — the app row also needs a
K-redex-survival fact (S8.1), which I predict is absent.

**S8.5 — What shape does the port actually have? The `extra` inner induction's third branch.**
`ParRed.triangle`'s `extra` case proves an inner two-way disjunction by induction on the *step*,
generalizing the pattern: either (i) the pattern **survives** — `p.Matches e' m1 m3` with the
matched arguments reduced — or (ii) a registered rule fired at a **subpattern** position, resolved
by `Pattern.matches_inter` + `Params.pat_uniq`.
*Prediction:* a `keta` step inside the skeleton fits **neither**, and for a reason that is
structural rather than an accident of the proof: `KStep.mk` matches its pattern at
`.app f c`, where `c` is a *converted* form of the subject's major premise `h`
(`hdq : IsDefEq Γ h c A₀`), so `p'.Matches e₁` — branch (ii)'s shape, and
`Pattern.matches_inter`'s requirement that both patterns match the **same term** — is simply not
available. `EtaK.under` is worse still: the match is at an η-expansion under a binder.
So the port needs a **third disjunct** and at least one further named residual, and Round 1's
"the other sixty-four rows are `ParRed.triangle`'s, verbatim modulo the grade" is **false as a
description of the port**, though true as a description of the table. Confidence 0.7.
Corollary prediction: this is the same residual as S8.2's dev-`extra` × step-`keta` row, seen from
inside the induction rather than at the root — so the port and the ledger converge on **one** new
object, not two. Confidence 0.5.

**S8.6 — Is the grade bookkeeping actually consistent across the port?**
`ParRedKn.extra`'s children sit at grade `n` with conclusion `n+1`; `CParRedKn.extra`'s children
sit at `n+1`, the *same* grade as its conclusion. `ParRedKn.app`'s children sit at `n`, same as
its conclusion. So in the `extra` × `extra` row the step's arguments are at `n` and the
development's at `m+1` with `n ≤ m+1` — fine — but in the `app` × `app` row both sides are at
their own conclusion's grade, and the inner `extra` induction recurses through `app` nodes where
the step's grade does **not** drop. *Prediction:* the grade side condition `n ≤ m` on
`ParRedKnTriangle` is the wrong one for the port and will need to be `n ≤ m` **with the outer
induction on `m` and an inner structural induction that never touches `m`** — i.e. the grade IH is
usable *only* in the `keta` rows, and every other row must go through the `brecOn` IH at the same
`m`. If instead any old row needs the grade to drop, the port does not go through at this shape.
Confidence the shape survives (grade only consumed by `keta`): 0.65.

### Cost priors (deliberately after the shape priors)

**C8.1** The second axis of the ledger (S8.2): 7 vacuous rows + 1 named. Cheap — under an hour,
because every lemma it needs is already in `CParRedK.lean`.
**C8.2** The port (S8.5). This is where the round is decided and where I will spend the bulk.
*Prediction:* I get `ParRedKn.triangle` **compiled as a theorem taking a named, closed list of
residual `Prop`s**, which is strictly better than Round 1's position (no uncompiled port), and I
do **not** discharge the residuals. Confidence 0.55 that the port compiles at all this round;
0.15 that it compiles with no residual beyond the three/four already named.
**C8.3** `KetaAppRow`/`KetaExtraRow`: I predict I close **neither** unconditionally, and that the
app row reduces to a K-redex-survival lemma which is itself a real theorem about `Params`.
Confidence 0.7.
**C8.4** *So my headline prediction is: `ParRedKnTriangle` is **not** closed this round and the
3931/3 figure **cannot** be banked, and the round's value is (a) the missing 8-row axis, (b) a
compiled port with an explicit residual list, (c) the S8.3 correction that `KDiamondJ` is not a
break.* Confidence 0.75. If I am wrong I expect to be wrong because S8.5 is wrong and the `keta`
step inside the skeleton *is* excludable by `EtaK.spineHead_const` plus a subpattern argument I
have not seen.

## §9 Measurements, appended as they land (never rewritten)

### M9.0 — baseline, before touching anything

Bare `lake build`, 2026-09-04, HEAD `3aca413` with Round 1's `CParRedK.lean` + this file present:
`Build completed successfully (1662 jobs)`, exit 0. Matches the brief's figure exactly. Pre-existing
`declaration uses 'sorry'` warnings: `Theory/Inductive/Decl.lean:750`,
`Theory/Typing/Injectivity.lean:261` and `:1046`, `Theory/Typing/UniqueTyping.lean:191`,
`Theory/Typing/ChurchRosser.lean:2016` — none in a file I own.

### M9.1 (answers S8.1) — no K-redex-survival lemma exists

`HEADS="VEnv.EtaK VEnv.ParRedK" lake env lean --run scripts/shape.lean`, 2026-09-04, HEAD
`3aca413`, **population 476 built modules**: 18 constants, 0 structure fields. Enumerated in full:
seven are `ParRedK`'s own generated recursors/`below`, two are `ParRedK.keta`/`.keta_step`, one is
`ParRedK.toParRed`, four are `KMeasure`'s weakening-inversion lemmas
(`keta_weakN_inv{,K,KS}`, `etaK_keta_liftN_inv`), one is `KMeasure.weakNInvStatementP_at_kdom`,
one is `KSite7.etaR_inner_keta`, one is `Verify.Typing.QuotKEta.quot_keta_needs_hyp` (arity 0), and
the last two are Round 1's own `keta_keta_row`/`keta_root_row`.
**Nothing concludes `EtaK Γ e' _` from `EtaK Γ e _` plus a reduction of `e`.** S8.1 scored right
on both halves (triangle absent — Round 1 measured that; survival lemma absent — 0.3 → correct).

`KSite7App.lean`'s own ledger corroborates from the other side: its two *open* site-7 rows are
`appDF × beta` and **`appDF × keta .under`**, and its `ParRed.triangle` row still reads "needs
`KDiamond` (`KDescend.lean`) and `EtaKDiamond` (`KEta.lean`), both stated and unproved" — a
**docstring that Round 1's `keta_keta_row` has already superseded** (the row it was written for
closes from `KetaDevAgree`, and `EtaKDiamond` is not used). Recorded because the brief and that
ledger disagree, and the ledger is the older text.

### M9.2 (answers S8.2, and it scores RIGHT) — the ledger has a **third block** and it was missing

`Lean4Lean/Theory/Typing/TrianglePort.lean` §2, compiled. The triangle's table is
`CParRedKn` (**ten** constructors) × `ParRedKn` (**nine**) = **ninety** rows, of which
`ParRed.triangle` proves 64. The twenty-six new ones split into four blocks:

| block | rows | status before this round | status now |
|---|---|---|---|
| dev = `keta` × the 8 old steps | 8 | `keta_root_row`, 6 closed / 2 open | unchanged |
| dev = `zero` × the 8 old steps | 8 | not named | **closed**, `zero_dev_row`, 4 lines |
| step = `keta` × all 10 developments | 10 | **not named at all** | **9 closed**, `keta_step_row`; 1 open |
| the old 8 × 8 table | 64 | unrun port | see M9.4 |

`8 + 8 + 10 + 64 = 90`, the `keta` × `keta` corner counted once (third block).

**S8.2 scored right on both clauses** (0.85 that the block is unnamed; 0.75 that exactly one row
of it survives). Round 1's prose — "nine rows where `keta` is the development's root step … the
other sixty-four are `ParRed.triangle`'s, verbatim modulo the grade" — omits ten rows, and the
omission is not a typo: `keta_root_row` cases the *step* under a `keta` development, so it cannot
see the rows where the development is something else. Nine of the ten fall out of lemmas Round 1
had already proved and did not use in this direction:

* `zero` is impossible (a `keta` step has grade `n+1`, and `n+1 ≤ m` forces `m ≥ 1`);
* `bvar`/`sort`/`lam`/`forallE`/`beta` by `EtaK.not_*`;
* **`const` and `app` by `NonNeutralK.of_etaK` against the development's own `¬ NonNeutralK`
  guard** — this is the block's one real observation, and it is a pleasing one: the only two
  developments a `keta` step can reach at the same node are exactly the two *guarded* ones, and
  the guard kills both;
* `keta` is Round 1's `keta_keta_row`.

The tenth is **new and open**: dev = `extra` × step = `keta`, named `ExtraKetaRow`. It is the only
development constructor with neither a guard nor an excluding shape lemma. **So the honest count
of open rows was three, not two, before the port is even attempted.**

Method rule 3 applied to the new row, not just to the old two: `ExtraKetaRow` **carries** the two
induction hypotheses in scope at its site — the strong grade IH `∀ k < m, TriangleAt k` (what
`keta_keta_row` needs) and `∀ a, TriangleAtOn m Γ (m2 a)` (what the `brecOn` below-structure
supplies for the matched arguments). Round 1's `KetaAppRow`/`KetaExtraRow` carry neither, which
S8.4 predicted and M9.3 measures.

Incidental, and a defect in my own statement rather than the tree's: `zero_dev_row` does **not**
need `OnCtx` (the binder is `_hΓ`), because `NormalEq.refl` needs only the typing. Recorded so the
unused binder is not read as an oversight.

### M9.3 (answers S8.4) — the hypothesis diff, read off the compiled statements

`KetaAppRow` and `KetaExtraRow` (`CParRedK.lean`:349, 357) each take, in order: a grade bound,
`OnCtx`, a typing, an `EtaK`, a `CParRedKn` of the contractum, and the step's premises. Their
neighbour `keta_keta_row` (`CParRedK.lean`:326) — **the row that closed** — takes all of those
*plus* an explicit `IH` at grade `m'`. **Neither open row carries any induction hypothesis at
all.** S8.4 scored right (0.9). Consequences, stated as bounds:

* As `Prop`s they are strictly stronger than what the triangle needs, so "unproved" is a verdict
  about an *overstated* obligation. Round 1's own §4 does not record this.
* Both new residuals in this round carry their IHs explicitly (`ExtraKetaRow`, `ExtraDevRow`
  take `∀ k < m, TriangleAt k` and `∀ a, TriangleAtOn m Γ (m2 a)`), and `TriangleAtOn` exists only
  so that the `brecOn` below-structure can be *handed over* rather than dropped. The port builds
  the `∀ a, TriangleAtOn m Γ (m2 a)` argument by an induction over the pattern, so `ExtraDevRow`
  receives a genuine hypothesis and not an axiom — that induction is `TrianglePort.lean`'s
  `extra` case, ten lines, compiled.
* I did **not** restate Round 1's two rows with IHs, because I do not own the shape they are
  consumed at (`keta_root_row` is Round 1's). The exact edit that would weaken them is stated in
  §11.

### M9.4 (answers S8.5 and S8.6) — **the port is RUN**, and it needed a different shape

`Lean4Lean/Theory/Typing/TrianglePort.lean`, §3–§4, compiled, **no `sorry` in the file**
(`grep -c sorry` = 0), `lake build Lean4Lean.Theory.Typing.TrianglePort` green.

**S8.5 scored half right, and the half it got wrong is the good news.** I predicted the port
would need a third disjunct inside `ParRed.triangle`'s `extra` inner induction, and hence a
further residual. What actually happened is that the whole `extra` development case is handed out
as **one** residual `ExtraDevRow` (nine rows), and every *other* development case ported cleanly.
So the port does not need a new *kind* of object; it needs the `extra` case, which is where
`ParRed.triangle`'s difficulty already was. The prediction that a `keta` step inside another
rule's skeleton cannot be resolved by `pat_uniq` survives as an *analysis* (§11.2) and is what
`ExtraDevRow` is paying for — but it is now inside a named residual rather than an unrun proof.

**Two structural changes were forced, and both are measured, not stylistic:**

1. **`cases H2`, not `induction H2`.** `ParRed.triangle` inducts on the development. Here the
   development's grade is `m+1` and the grade occurs in `IHlt : ∀ k < m+1, TriangleAt k`, so
   `induction H2` would generalise the grade and destroy the IH. The port therefore only *cases*
   on the development, and every use `ParRed.triangle` makes of an `H2`-induction hypothesis is
   served instead by the `VExpr.brecOn` below-structure at the corresponding subterm. That
   substitution works everywhere — I checked all eight cases — which is itself worth recording:
   **`ParRed.triangle`'s induction on `H2` is not load-bearing; `brecOn` alone carries it.**
2. **The grade bound has to be relaxed exactly twice, and S8.6 called it.** S8.6 predicted (0.65)
   that the grade is consumed only by `keta` and every other row goes through `brecOn` at the same
   `m`. Right, with one correction I had not predicted: in the `beta` development case against a
   `beta` *step*, the step's children sit at grade `n` while the step is at `n+1`, so the
   sub-triangle needs `n ≤ m+1` from `n+1 ≤ m+1` — `Nat.le_of_succ_le`, twice, at exactly the two
   sites Lean rejected `hnm`. Nowhere else in 72 rows does the bound need touching.

**The row table, compiled rather than tabulated:**

| block | rows | status |
|---|---|---|
| dev ∈ {`zero`} × all 9 steps | 9 | closed, `zero_dev_row` |
| dev ∈ {`bvar`,`sort`,`const`,`app`,`lam`,`forallE`,`beta`} × all 9 steps | 63 | **closed, the port** |
| dev = `keta` × all 9 steps | 9 | 7 closed + `KetaAppRow`, `KetaExtraRow` (Round 1) |
| dev = `extra` × all 9 steps | 9 | `ExtraDevRow` (this round) |

72 of 90 rows compiled. `parRedKnTriangle_of : KetaDevAgree → KetaAppRow → KetaExtraRow →
ExtraDevRow → ParRedKnTriangle`, and then `parRedKDiamond_of_rows`, `crStatementK_of_rows`.

**So Round 1's refusal is now answerable in a sharper form:** the triangle is proved **modulo four
named residual `Prop`s and no unrun port**. That is strictly better than "modulo two rows and an
uncompiled 64-row port", and strictly worse than closed.

### M9.5 — a limit of Round 1's that the port closes outright

`refParams_parRedKnTriangle : @ParRedKnTriangle refParams`, **unconditional, compiled**. Round 1's
§4.5 recorded this as open: "I did **not** compile `refParams_parRedKnTriangle` — it needs
`ParRedKn → ParRed` and `CParRedKn → CParRed` at `refParams`, which is real work". The port makes
it free — the four residuals are each vacuous at `refParams` (`DescendRefute.refNoPat` for the new
one: that instance registers no pattern at all), so the triangle follows from the *general*
theorem and no translation back to `ChurchRosser.ParRed.triangle` is needed. It remains a
consistency check and not evidence: at `refParams` both `KStep` and `Pat` are empty. What it does
establish is that the four residuals are **jointly satisfiable**.

### M9.6 — the firing, at `quotParams`

`quotParams_triangle_fires` and `quotParams_triangle_at_keta`, compiled inside
`attribute [local instance] quotParams`. The subject is `qLiftT`, the term
`CRKProve.quotParams_parRedK_qLiftT` moves by a `keta` step whose `EtaK` derivation is
`.under _ (.here quotParams_kstep_eta)` — an η-tower of height one over a **live** `KStep`. So
`NonNeutralK` holds at the subject and the development `CParRedKn.exists` returns has `keta` as
its root step; nothing here is vacuous by an empty premise, unlike `refParams`. The conclusion is
the triangle's own: a `ParRedK` leg out of the step's reduct meeting the development up to
`NormalEq`, at the grade `ParRedK.toN` assigns the step.

### M9.7 — the accounting, re-measured 2026-09-04 at HEAD `3aca413` + Round 1's + `TrianglePort.lean`

`scripts/exists.lean`, **population 478 built modules** (Round 1 measured 477 with its own module;
+1 is mine). Holes = subset of
`{IsDefEqU.weakN_iff, IsDefEqU.forallE_inv_stratified, WF.rigidShapeUniqNS}`; `NormalEq.descend`
absent from every row, as `CRKProve` and Round 1 both found.

| declaration | module | arity | cone | holes | own value a hole |
|---|---|---|---|---|---|
| `IsDefEqU.constApp_forallE_false_ofHyps` | `CRKProve` | 11 | **3931** | 3 | no |
| `crStatementK_of` | `CRKProve` | 3 | 3859 | 3 | no |
| `crStatementK_of_triangle` | `CParRedK` | 3 | 3920 | 3 | no |
| **`crStatementK_of_rows`** | `TrianglePort` | 6 | **4028** | 3 | no |
| `parRedKDiamond_of_rows` | `TrianglePort` | 5 | 3976 | 3 | no |
| `parRedKnTriangle_of` | `TrianglePort` | 5 | 3963 | 3 | no |
| `triangleAt_all` | `TrianglePort` | 6 | 3960 | 3 | no |
| `triangleAt_of` | `TrianglePort` | 7 | 3959 | 3 | no |
| `keta_step_row` | `TrianglePort` | 18 | 3838 | 3 | no |
| `refParams_parRedKnTriangle` | `TrianglePort` | 0 | 7036 | 3 | no |
| `quotParams_triangle_at_keta` | `TrianglePort` | 4 | 9575 | 3 | no |
| `refParams_extraDevRow` | `TrianglePort` | 0 | 6561 | **0** | no |
| `zero_dev_row` | `TrianglePort` | 12 | 705 | **0** | no |
| `ExtraDevRow` / `ExtraKetaRow` (the `Prop`s) | `TrianglePort` | 1 | 657 / 658 | **0** | no |
| `ExtraDevRow.toKeta`, `parRedKnTriangle_of_at`, `TriangleAt.on` | `TrianglePort` | 2/2/1 | 661/43/43 | **0** | no |

**3931/3 reproduces byte-identically at a third commit** (`ca04f43` → `e0aee76` → `3aca413`), so
the figure itself is stable; the *population* has moved twice (471 → 477 → 478), which is again
the number a reader would quote wrongly.

`#print axioms`, measured this round:

| axioms | declarations |
|---|---|
| `[propext, Quot.sound]` | `zero_dev_row`, `ExtraDevRow.toKeta`, `parRedKnTriangle_of_at`, `TriangleAt.on` |
| `[propext, Classical.choice, Quot.sound]` | `refParams_extraDevRow` |
| `[propext, sorryAx, Classical.choice, Quot.sound]` | `keta_step_row`, `triangleAt_of`, `triangleAt_all`, `parRedKnTriangle_of`, `parRedKDiamond_of_rows`, `crStatementK_of_rows`, `refParams_parRedKnTriangle`, both `quotParams_*` |

`sorryAx` is **inherited in every case** — `exists.lean` reports "own value is a hole: false" for
every row above, and the entry points are the same three pre-existing holes. `Classical.choice`
comes from `CParRedKn.exists`'s `NonNeutralK` decision (Round 1's), not from anything new.

The four watched declarations note in `exists.lean`'s output — `IsDefEq.uniq`, `IsDefEq.uniqU` in
cone — is inherited identically by `CRKProve.crStatementK_of` (3859) and Round 1's
`crStatementK_of_triangle` (3920), so **nothing new is tainted and nothing new is watched.**

### M9.8 (answers S8.3, and it scores RIGHT) — the brief's "break" is not a break

The brief says: "The break is `kDiamondJ_of_patMajorCanonicalJ` (hole-free, `[propext,
Quot.sound]`): M3 restated as joinability, a rule-table property with no confluence in it."

* The **parenthesis reproduces**: `KDiamondJoin.lean` §7's table lists
  `kDiamondJ_of_patMajorCanonicalJ` under `[propext, Quot.sound]`, i.e. `sorryAx`-free *and*
  `Classical.choice`-free. Not in dispute.
* The **clause after the colon is contradicted by the very file the brief tells me to read
  first.** `KDiamondJoin.lean` §3's headline is: "the localisation `PatMajorCanonical → KDiamond`
  was supposed to deliver is *gone* — `KDiamondJ` is sandwiched between two Church–Rosser
  statements", with two named bounds: above, `kDiamondJ_of_crK` (`KDiamondJ` follows from CR over
  `ParRedK`); below, `quotPat_argJoin_of_kDiamondJ`, advertised **hole-free**, which shows that at
  any instance registering `quotPat`, `KDiamondJ` implies that `g x` and `g x'` join for
  **arbitrary definitionally equal** `x, x'` — "that is Church–Rosser at an application, not a
  property of the rule table". §8 of the same file says explicitly that it does *not* claim the
  localisation survives.

So S8.3 scored right (0.8), and the consequence for this round was operational, not rhetorical:
**I did not aim any residual at `KDiamondJ`.** The four residuals are stated over
`ParRedKn`/`CParRedKn` and `NormalEq` directly, and §4a instead narrows one of them with
`KMeasure.EtaKn.fuel_eq`, which is a *measure* fact resting on `Params.pat_app_depth_uniq` — a
rule-table property with genuinely no confluence in it.

### M9.9 — the `keta` branch of `ExtraDevRow` splits in two, and half of it is now a theorem

`TrianglePort.lean` §4a, compiled: `EtaK.not_here_of_partial`, `EtaK.under_of_partial`,
`matches_not_lam`, `etaK_leaves_skeleton`, `etaK_root_fuel_zero`.

S8.5's analysis — that a `keta` step inside another rule's skeleton fits *neither* branch of
`ParRed.triangle`'s `extra` inner disjunction — is now half a theorem rather than all prose. The
tool is `KMeasure.EtaKn.fuel_eq`: the η-tower's height is `P₁.depth + 1 - e.appDepth`.

* **At the root** of the redex, `Pattern.Matches.appDepth` gives `e.appDepth = P₁.depth + 1`, so
  the fuel is `0` and the step must be `EtaK.here` — a bare `KStep`, i.e. the row is
  `KDiamond`-shaped. That is `etaK_root_fuel_zero`, and it is `ExtraKetaRow`'s configuration.
* **At any strict skeleton node**, `e.appDepth ≤ P₁.depth`, so the fuel is `≥ 1` and
  `EtaK.here` is **impossible** (`EtaK.not_here_of_partial`): the step is forced to be
  `EtaK.under`, its contractum is a `.lam`, and `etaK_leaves_skeleton` concludes that **no pattern
  whatsoever matches the contractum**. So the "pattern survives with reduced arguments" branch is
  unavailable there *by a theorem*, not by an unproved case.

Two things this pins down that were guesses before:

1. The row is **not vacuous** at strict skeleton nodes — the fuel equation is satisfiable there
   (`k = P₁.depth + 1 - e.appDepth ≥ 1`), so I cannot dispose of it by an exclusion lemma the way
   `keta_step_row` disposes of seven rows. I looked for that exclusion and the measure says it does
   not exist.
2. A **tooling correction worth its own line**: `VExpr.headConst?` looks *through* binders —
   `(.lam A t).headConst? = t.headConst?` — so a λ **does** have a `headConst?`, and
   `Pattern.Matches.headName` therefore does *not* exclude a λ. `Pattern.Matches.spineHead_const`
   does. I found this by writing the wrong proof first and having Lean hand me
   `t.headConst? = some p.headName` as an unsolved goal. Anyone reasoning "no pattern matches a λ,
   because patterns have constant heads" from `headName` is reasoning from a false premise.

---

## §10 Verdicts (Round 2)

**W1 — Is `ParRedKnTriangle` closed?  NO.**  It is proved from a **closed list of four named
residual `Prop`s**, with **no unrun port**: `parRedKnTriangle_of : KetaDevAgree → KetaAppRow →
KetaExtraRow → ExtraDevRow → ParRedKnTriangle` (cone 3963, holes 3, own value not a hole,
2026-09-04 at HEAD `3aca413`, population 478). 72 of the triangle's 90 rows are compiled; the
remaining 18 are the two rows Round 1 left open plus the nine of `ExtraDevRow`, which contains the
tenth row of the axis Round 1's ledger omitted.

**W2 — Can the 3931/3 figure be banked?  NO.**  `IsDefEqU.constApp_forallE_false_ofHyps` is cone
**3931**, holes **3**, at a third distinct commit — the figure is stable and reproduces
byte-identically. It is still the cone of a theorem with two hypotheses, and this round discharges
neither. What it does is replace Round 1's *hypothesis* `ParRedKnTriangle` by a **row list**:
`crStatementK_of_rows` (cone 4028, the same three holes, nothing new tainted, nothing new watched).
The brief's framing — "you are the round that decides whether it can be banked" — is answered:
**it cannot**, and now for a reason with a shape rather than a size, namely four `Prop`s that can
be read in ten lines each.

**W3 — What resists, and is it false or unproved?  Unproved, and now located.**
* `KetaDevAgree` — Round 1's, fired at `quotParams` there. Not attacked this round.
* `KetaAppRow`, `KetaExtraRow` — Round 1's, and **both understated**: neither carries the
  induction hypothesis that their closing neighbour `keta_keta_row` carries (M9.3). So "unproved"
  is a verdict about obligations stronger than the triangle needs.
* `ExtraDevRow` — **new this round**, nine rows, and its `keta` branch splits by a *measure*:
  `EtaK.here` at the root (fuel 0, `KDiamond`-shaped) versus `EtaK.under` at every strict skeleton
  node (fuel ≥ 1, contractum a `.lam`, matching no pattern at all — `etaK_leaves_skeleton`, M9.9).
  Both halves are satisfiable, so no exclusion lemma disposes of the row; I looked, and the fuel
  equation says why there is none.

Evidence for "not false", stated as bounds and not as a proof: all four are **jointly satisfiable**
(`refParams_parRedKnTriangle`, unconditional — which closes a limit Round 1 recorded as open);
`shape.lean` on `{VEnv.EtaK, VEnv.ParRedK}` at population 476 returns 18 constants, none a negation
of any row (M9.1); and no `¬ CRStatementK` exists anywhere in the tree (grep over
`Lean4Lean/`, zero hits — an absence by enumeration of a one-line pattern, so weaker evidence than
the shape search).

**W4 — the honest new bad news.**  The open-row count was **three, not two**, before the port was
attempted, and is **four `Prop`s / 18 rows** after it. Round 1's ledger omitted an entire axis of
ten rows (step = `keta` against a non-`keta` development). Nine fell out of lemmas already in the
tree; the tenth did not.

## §11 Limits of this result, and where I proved them

1. **`ExtraDevRow` is a residual, not a transcription.**  `ParRed.triangle`'s `extra` case — the
   inner induction over the step proving "pattern survives ∨ a rule fired at a subpattern" — is
   **not** transcribed here. That is a budget decision and I state it as one: the eight old rows of
   that case are provable (the original proves them), so `ExtraDevRow` is *not* eight open rows
   plus one; it is one open row (step = `keta`, split by M9.9 into root and skeleton halves) with
   eight rows of transcription debt around it. **Anyone quoting §10 as "the triangle is proved
   modulo four rows" would be overstating it: it is modulo four `Prop`s, one of which still
   contains transcription work that is known-provable.** The precise next step is in §12.3.
2. **The keta-in-skeleton half is analysis where it is not theorem.**  `etaK_leaves_skeleton` proves
   the contractum leaves the skeleton. It does **not** prove that the surrounding reduct cannot be
   related to the rule's RHS by some other route, and it does not construct the one-hole pattern
   context that a full third disjunct would need. Round 1's shape prior S8.5 predicted a third
   disjunct; what I have is the reason one is needed, not the disjunct.
3. **I did not weaken Round 1's two rows, and the exact edit is stated rather than made.**
   `KetaAppRow`/`KetaExtraRow` live in `CParRedK.lean`, which I own, but their consumer
   `keta_root_row` is Round 1's proof and re-shaping the rows would rewrite it. The edit that would
   make them as weak as the triangle permits, stated verbatim so the next round need not re-derive
   it — add to each row, as its first two hypotheses,

   ```lean
       (∀ k, k < m → TriangleAt k) → (∀ a, TriangleAtOn m Γ (m2 a)) →
   ```

   (for `KetaAppRow`, `TriangleAtOn m Γ f` and `TriangleAtOn m Γ a` in place of the second), and
   pass `IHlt`/the pattern-induction output at `keta_root_row`'s two call sites. `TriangleAt` and
   `TriangleAtOn` are in `TrianglePort.lean`, which imports `CParRedK.lean`, so the definitions
   would have to move **down** into `CParRedK.lean` first. I did not do it because it is a
   cross-file re-shaping of another round's compiled proof, and the round's headline does not
   depend on it.
4. **`refParams_parRedKnTriangle` is a consistency check, not evidence.**  At `refParams` both
   `KStep` and `Pat` are empty (`refParams_no_etaK`, `DescendRefute.refNoPat`), so every row that
   could be interesting is vacuous. Its value is exactly one thing: the four residuals are jointly
   satisfiable, so the list cannot be discharged by deriving `False` from it.
5. **The `quotParams` firing is conditional on the four residuals and inherits `quotParams`'s
   taint.**  `quotParams_triangle_at_keta` (cone 9575, holes `{weakN_iff,
   forallE_inv_stratified, WF.rigidShapeUniqNS}`) is *not* an unconditional statement about
   `quotParams`; it is the port instantiated there. What is unconditional about it is that the
   instance is non-degenerate: `KStep` is inhabited (`quotParams_kstep_eta`), the subject is
   `EtaK`-reducible with an η-tower of height one, and the development's root step is therefore
   `keta`. Compare Round 1's `quotParams_ketaDevAgree_at_kDiamond_witness` (cone 9297) and
   `CRKProve`'s (9287): the same taint, no new dependency.
6. **`ParRed.triangle`'s `H2`-induction turns out not to be load-bearing, and I only checked that
   for the eight cases I ported.**  The port replaces it by `brecOn` throughout (M9.4). I did not
   check the `extra` case, because I did not port it — so the claim is "`brecOn` suffices for 72 of
   the 90 rows", not for all of them.
7. **Nothing here tests the residuals at a second non-degenerate instance.**  `appParams`
   (`PatAppParams.lean`) is the other instance registering `.app` patterns, and Round 1's §6.4
   already recorded not firing there. I did not either.

## §12 Method gaps, mine

1. **I inherited a row table and did not recount it before believing it.**  My brief said "two open
   rows plus a 64-row port"; that is 9 + 64 = 73 of a 90-row table, and the arithmetic is visible
   from the two inductives' constructor counts alone. I did write it down as a shape prior (S8.2)
   *before* any Lean — but only because the previous round's method rules forced a prior on "is the
   work in the direction the brief thinks". Without that rule I would have started porting.
2. **I proved `matches_not_lam` the wrong way first, from `headName`, and Lean caught it.**
   `VExpr.headConst?` looks through binders. The habit that produced the error is reading a lemma's
   *name* as its content (`headName` ⇒ "the head constant" ⇒ "λ has none"). Cost: one build.
   Recorded in M9.9 because the false premise is attractive.
3. **I did not attempt `KetaAppRow` or `KetaExtraRow` at all**, having predicted (C8.3, 0.7) that I
   would close neither. That is a self-fulfilling prior and I should name it as such: the diff in
   M9.3 says both are understated, which is precisely the condition under which an attempt is worth
   making, and I used the budget on the port instead. The next round should restate them per §11.3
   *first* and then attempt them, because attempting the overstated form is what "a gate proved
   unprovable this week purely because it omitted a hypothesis" describes.
4. **I did not run the `extra` case, so the biggest single row block is still a residual**, and my
   verdict W1 is therefore weaker than it reads at a glance. §11.1 says so explicitly, but a reader
   scanning "four residuals, no unrun port" could miss that one of the four *contains* known-
   provable work. The concrete next step: transcribe `ChurchRosser.lean`:1160–1225's inner
   induction with `ParRedKn`/`ParRedK` for `ParRed`, adding a third disjunct for `keta` whose
   root half is `ExtraKetaRow` and whose skeleton half needs a one-hole pattern context; §4a's five
   lemmas are the tools for the skeleton half and are already compiled.
5. **`Pattern.Matches.appDepth` and `EtaKn.fuel_eq` were the round's most useful tools and I found
   them by reading `KMeasure.lean` for a different reason** (checking Round 1's `height_uniq`
   claim). I did not search for a measure; I stumbled on one. A conclusion-head search for
   `{VEnv.EtaKn, Nat}`-shaped facts would have found `fuel_eq` in one query.

## §13 Build record, dated

| when | commit | command | result |
|---|---|---|---|
| round start | `3aca413` + Round 1's two files | bare `lake build` | green, **1662 jobs**, exit 0 (matches the brief) |
| round end | `3aca413` + Round 1's two files + `TrianglePort.lean` | bare `lake build` | green, **1664 jobs**, exit 0 |

Guards at round end: **guard 1 ✓** (Axioms.lean declares exactly the 24 frozen axioms),
**guard 2 ✓** (kernel_sound axioms within whitelist; proof INCOMPLETE: sorryAx present — unchanged),
**guard 3 ✓** (2/2 implementation gaps remaining — unchanged). **Census 13, unchanged**
(`grep -c "declaration uses \`sorry\`"` on the build log = 13, and none of the thirteen is in a file
I own). **`grep -c sorry Lean4Lean/Theory/Typing/TrianglePort.lean` = 0**, and the file emits **no
warnings** of any kind in the final build.

Files touched this round: `Lean4Lean/Theory/Typing/TrianglePort.lean` (new),
`docs/handoff-cparredk.md` (§8–§13 appended; §1–§7 untouched). **`CParRedK.lean` was not modified**
— see §11.3 for the edit I considered and did not make. No state-changing git command was run, and
no frozen file was read for editing or edited.

---

## §14 One measurement that landed after §10–§13 were written (appended, not merged)

`scripts/exists.lean`, 2026-09-04, HEAD `3aca413` + Round 1's + `TrianglePort.lean`, population
**478**. The §4a narrowing is **entirely hole-free** — every one of its five declarations has
`cone reaches sorryAx: false`, which puts it in the same class as `zero_dev_row` and
`kDiamondJ_of_patMajorCanonicalJ` rather than in the tainted majority:

| declaration | arity | cone | reaches `sorryAx` |
|---|---|---|---|
| `EtaK.not_here_of_partial` | 10 | 1808 | **no** |
| `EtaK.under_of_partial` | 11 | 1814 | **no** |
| `etaK_root_fuel_zero` | 12 | 1812 | **no** |
| `etaK_leaves_skeleton` | 14 | 1821 | **no** |
| `matches_not_lam` | 5 | 417 | **no** |
| `TriangleAt`, `TriangleAtOn` (the defs) | 2 / 4 | 41 / 41 | **no** |
| `quotParams_triangle_fires` | 6 | 9544 | yes (the 3 pre-existing holes) |

So the round's *sharpening* of the residual costs nothing in taint: it rests on
`KMeasure.EtaKn.fuel_eq` → `Params.pat_app_depth_uniq` → `Params.pat_simple`, and none of that
chain touches the injectivity corner. That matters for the next round's route: the fuel measure is
usable to narrow the remaining rows without importing any of `{weakN_iff,
forallE_inv_stratified, WF.rigidShapeUniqNS}`, which is more than can be said for anything that
goes through `NormalEq.trans` or `ParRedK.hasType`.

---

# Round 3 (2026-09-04, later still) — the restatement, and where the four residuals actually meet

*Numbering note, second occurrence.* My brief says "§1–§12 are two previous rounds'. Do not edit
them. Add §13 onward." Round 2 had already used **§13** (build record) and **§14** (a late
measurement), exactly as Round 1 had overrun the numbering its own brief predicted. I have edited
**nothing** above this line. The brief's "§13" is therefore this round's **§15 (priors)**, and the
rest follows: §16 measurements, §17 verdicts, §18 limits, §19 method gaps, §20 build record. A
reader looking for "Round 3's §13 scorecard" wants §15 and §16.

## §15 Priors, written before any Lean and never edited

Written after reading, in this order: `CLAUDE.md`; `docs/handoff-cparredk.md` §8–§14 in full (and
the headers of §1–§7); `Lean4Lean/Theory/Typing/TrianglePort.lean` in full (all 495 lines);
`CParRedK.lean`:250–420 (`EtaK.not_beta`, `ParRedKn.zero_eq`, `CParRedKn.zero_eq`,
`NonNeutralK.of_etaK`, `KetaDevAgree`, `keta_keta_row`, **`KetaAppRow`, `KetaExtraRow`,
`keta_root_row`**, `not_nonNeutralK_app_bvar`); `ChurchRosser.lean`:1040–1240 —
**`ParRed.triangle` in full, including the `extra` case's inner induction, which is the part
Round 2 did not transcribe**; `KRule.lean`:1–190 (`KStep`, `KStep.defeq`, `Params.no_kpattern`).
No Lean written, no cone measured, no build run yet.

### Shape priors (three of them, before any cost prior)

**S15.1 — Where do the four residuals *meet*?  I predict they meet at one object, and that object
is not named anywhere in the tree (0.85).**
Reading `ParRed.triangle`'s `extra` case shows its whole difficulty is a single anonymous
`have : (∃ m3 m3', p.Matches e' m1 m3 ∧ …) ∨ (∃ p₁ …, Subpattern p₁ p ∧ … Pat p' r ∧ …)` — a
**two-way survival disjunction**, proved by an inner induction over the *step*, and then consumed
twice. It is inline inside the theorem: not a `def`, not a `theorem`, not reusable. My prediction
is that this same disjunction (with `ParRedKn` for `ParRed`, plus a **third** disjunct for a
`keta` step) is what `KetaAppRow`, `KetaExtraRow` **and** `ExtraDevRow` all need, because in each
of those three rows a rule has fired at the root on one side while the other side has reduced
inside the skeleton. If that is right, the honest description of the round's target is not "four
residuals" but "**one engine and three consumers**", and the deliverable is the engine.

**S15.2 — Adding the induction hypotheses makes the two rows *weaker*, but I predict it does NOT
make them provable (0.8).**
Round 2's M9.3 measured `KetaAppRow`/`KetaExtraRow` as carrying no induction hypothesis at all,
and the brief instructs me to weaken them per §11.3 and then attempt them, on the analogy of a
gate that was unprovable purely for a missing hypothesis. I expect the analogy to hold **half
way**: the missing IHs are genuinely necessary (nothing else supplies the triangle at the matched
arguments or at the contractum, and the contractum is not a subterm so `brecOn` cannot), but they
are **not sufficient**, because no induction hypothesis of any shape tells you that
`EtaK Γ (.app f a) w` still has a counterpart at `.app f' a'`. That is survival, i.e. S15.1's
engine, and it is a fact about the rule table, not about the induction. **Concretely I predict:
after the restatement both rows reduce to the engine, and neither closes without it.** If instead
one of them closes outright from the IHs alone, S15.2 is wrong and I will say so in the same words.

**S15.3 — The `keta` case of the engine needs a third disjunct at the root and *no* disjunct at
strict skeleton nodes (0.75).**
Round 2's M9.9 proved both halves of the `keta` branch satisfiable and concluded no exclusion
lemma disposes of the row. I predict a sharper split than "both satisfiable, so both cost":
`etaK_leaves_skeleton` says a `keta` step at a strict skeleton node produces a `.lam`, which
matches no pattern — so the *first* disjunct ("the pattern survives") is provably unavailable
there, but the **second** disjunct is the one that applies, since the reduct having left the
skeleton is exactly "something fired below". So strict skeleton nodes cost a *routing* argument,
not a new disjunct; only the root, where the fuel is 0 and the step is a bare `KStep`, needs a
third disjunct, and that third disjunct is `ExtraKetaRow`/`KetaAppRow`-shaped. Net prediction:
the engine has **three** disjuncts, the third is inhabited only at the root, and the whole
`keta`-in-skeleton analysis of M9.9 is consumed by *routing to disjunct two*.

**S15.4 — `KStep` survival is not derivable from `KStep.defeq` (0.9).**
The tempting cheap route for `KetaAppRow` is: `EtaK` steps are `IsDefEqU` (`EtaK.defeqU`), the
step's congruence is an `IsDefEqU`, so `.app f' a'` and `o` are definitionally equal, done. That
is exactly the move `NormalEq` forbids — `NormalEq` is not implied by `IsDefEq`; deriving it from
`IsDefEq` *is* Church–Rosser, which is what the triangle is being proved to get. I write this
down before touching Lean because it is the shape of error that would let me "close" a row with a
proof that silently assumes the conclusion, and the brief's trap list does not contain it.

### Cost priors (deliberately after the shape priors)

**C15.1 — The §11.3 restatement compiles this round: 0.85.** Moving `TriangleAt`/`TriangleAtOn`
down into `CParRedK.lean` and adding two hypotheses to two `def`s is mechanical; the only risk is
`keta_root_row`'s two call sites and `TrianglePort.lean`'s `keta_root_row` invocation needing
arguments that are not in scope at the port's `keta` case. I believe they are: `IHlt` is in scope,
and the `brecOn` below-structure at `.app f a` gives the two `TriangleAtOn`s. **This is the one
thing in my brief I am confident of, so I will do it first and measure it, not last.**

**C15.2 — I close 0 of the four residuals outright: 0.6; I close 1: 0.25; 2 or more: 0.15.**
And per Round 2's §12.3 — *"I predicted I would close neither and then spent no budget on them —
self-fulfilling"* — **this prior is explicitly not a budget decision.** The budget goes to the
engine regardless of the prior, because S15.1 says the engine is what all three consumers need and
an engine that compiles converts four opaque residuals into one named one plus routing.

**C15.3 — The 3931/3 figure cannot be banked this round: 0.8.** It needs all four residuals
discharged. Even on my optimistic branch (engine compiles, three rows reduce to it) the engine
itself is then the residual and `KetaDevAgree` is untouched. I will say so plainly rather than
report a consolidation as a banking.

**C15.4 — Census stays 13 and the build stays green: 0.95.** I add no `sorry`; residuals are
`def … : Prop` hypotheses, which is the pattern both previous rounds used and which costs no
census.

**C15.5 — Cone noise from the move: ±3 on anything whose cone contains `TriangleAt` (0.9).** My
brief warns cone numbers are not invariant under moving a declaration between modules. Since
`TriangleAt`/`TriangleAtOn` (cone 41 each) move from `TrianglePort` to `CParRedK`, every figure
that reaches them may shift by a small amount and **that shift is not signal**. I will re-measure
rather than reuse Round 2's table, and mark the comparison.

## §16 Measurements, appended as they land (never rewritten)

### M16.0 — baseline

Bare `lake build` at HEAD `0cfbdc8` with Round 1's and Round 2's files in the tree: green,
**1665 jobs**, exit 0. Matches the brief exactly.

### M16.1 (answers C15.1, and it scores RIGHT) — the §11.3 restatement is **made**, not stated

`lake build Lean4Lean.Theory.Typing.TrianglePort` green (1292 jobs, the module's own closure). Four
edits, all inside my two files:

1. `TriangleAt`, `TriangleAtOn`, `parRedKnTriangle_of_at`, `TriangleAt.on` **moved down** from
   `TrianglePort.lean` into `CParRedK.lean` §4.1, character-for-character unchanged.
2. `KetaAppRow` now carries `(∀ k, k < m+1 → TriangleAt k)`, `TriangleAtOn (m+1) Γ f` and
   `TriangleAtOn (m+1) Γ a`; `KetaExtraRow` carries `(∀ k, k < m+1 → TriangleAt k)` and
   `(∀ x, TriangleAtOn (m+1) Γ (m2 x))`. Both are therefore **strictly weaker `Prop`s** than
   Round 1's: any proof of the old form is a proof of the new one.
3. `keta_root_row` takes the three in the only shape available before the *step* is cased:
   `IHlt`, plus `IHapp : ∀ {f a}, e = .app f a → TriangleAtOn (m'+1) Γ f ∧ TriangleAtOn (m'+1) Γ a`
   and `IHpat : ∀ {p m1 m2}, Pattern.Matches p e m1 m2 → ∀ x, TriangleAtOn (m'+1) Γ (m2 x)`.
   The guarded shape is forced: at `keta_root_row`'s entry `e` is an arbitrary term (the
   development's `keta` constructor constrains nothing), so "the triangle at the two children" is
   not yet a well-formed statement — it becomes one only after `cases h1` refines `e`.
4. **`IHpat` is Round 2's inline pattern induction, hoisted.** Round 2 ran it inside
   `triangleAt_of`'s `extra` development case; it is now a single `have` before `cases H2`, so the
   `keta` case gets it too, and the `extra` case shrank from ten lines to one
   (`exact HED (fun k hk => IHlt k (by omega)) (IHpat l2) hnm hΓ he l1 l2 l3 l4 H1`).
   **Round 2's §11.3 said the move "would rewrite" `keta_root_row`; it does, and the rewrite is
   four tokens plus a hoist.** Cost: two builds, one of which failed for a mechanical reason worth
   recording — the hoisted `have IHapp` depends on `e`, so `induction p generalizing e A` inside
   `IHpat` silently reverted it and every pattern IH acquired an extra argument. `clear IHapp`
   fixes it. That is the same class of error as reading a lemma's name for its content: I did not
   predict that hoisting one `have` would perturb the *arity* of an unrelated induction's IHs.

`refParams_ketaAppRow` / `refParams_ketaExtraRow` needed only extra `_` binders (the added
hypotheses sit before the `EtaK` that `refParams_no_etaK` refutes), so **the joint-satisfiability
witness survives the restatement** — which matters, because a restatement that broke it would have
been a restatement into something possibly inconsistent.

### M16.2 — **`KetaDevAgree` is REFUTED at `quotParams`**, and so is `ParRedKnTriangle`

`CParRedK.lean` §7, compiled, no `sorry` written. This is the round's result and it reverses the
stream's verdict, so here is the whole argument in five lines:

1. `KetaDevAgree` is quantified over **every** grade `m`, grade `0` included.
2. `CParRedKn 0` is the identity (`CParRedKn.zero_eq`, Round 1's own lemma).
3. So the `m = 0` instance says: *two `EtaK` contracta of one subject are `NormalEq` on the nose*.
4. That is `KDescend.KDiamond` with `EtaK.here` for `KStep` — and
   `Verify/QuotAppParams.quotParams_not_kDiamond` **already refutes it**, by the very pair Round 1
   §5.1 quotes in `KetaDevAgree`'s own docstring (`g x` versus `g ((fun y => y) x)`).
5. `quotParams_not_ketaDevAgree : ¬ KetaDevAgree` — three lines, and the only thing it needed that
   `quotParams_not_kDiamond` did not already have is a typing for the subject
   (`qRedex_hasType = .app qLift1_hasType (qMk1_hasType qT_x)`).

**Round 1's docstring contains the refutation's own premise.** It argues `KetaDevAgree` is weaker
than `KDiamond` because "a *development* of the second contracts that β-redex, so it lands on
`g x` and the two agree", and its §6 firing `quotParams_devAgree_normalEq` is stated at grade
`m+1`. That argument is **sound at positive grade and vacuous at grade 0**, where the development
is forbidden to move. The firing was therefore never a firing of the residual as stated: it
exhibits the positive-grade instances holding *while the grade-0 instance is false*.

And the refutation does not stop at the residual. `quotParams_not_parRedKnTriangle :
¬ ParRedKnTriangle`, at `n = m = 1`, which satisfies the triangle's own side condition `n ≤ m`:

* development `keta (.here quotParams_kstep_xbeta) .zero : CParRedKn 1 qc1 E (g ((fun y => y) x))`;
* step `keta (.here quotParams_kstep_x) ParRedKn.rfl : ParRedKn 1 qc1 E (g x)`;
* the step's reduct `g x = .app (.bvar 3) (.bvar 1)` is **`ParRedK`-rigid**
  (`parRedK_app_bvar_bvar_eq`, three lines from Round 1's `not_nonNeutralK_app_bvar`), so the
  triangle's existential has exactly one candidate, and `not_normalEq_gx` kills it.

`n = m = 1` is **not a corner case**: `parRedKDiamond_of_triangle` develops at exactly
`max n₁ n₂`, so `n = m` is the *principal* configuration of the assembly.

`quotParams_not_rows_jointly` then states the consequence in the only honest form — the four rows
cannot all hold — taking `parRedKnTriangle_of` as a hypothesis so that the statement lives in
`CParRedK.lean` and does not need `TrianglePort.lean`'s import direction reversed.

**The refutation is CONDITIONAL**, on exactly the corner `not_normalEq_gx` rests on: `PiInv` (the
instance) and `WF.propTypeAgreeOn` (the two `proofIrrel` blocks), both `sorryAx`, both
pre-existing, neither new. `#print axioms` is M16.4. It must not be quoted as unconditional.

### M16.3 — a **second** residual falls, and the contrast says the weakening is load-bearing

`KetaExtraRow0` (`CParRedK.lean` §5.2a) is Round 1's `KetaExtraRow` character for character,
retained only so that `quotParams_not_ketaExtraRow0` can refute it. At `m = n = 0` the row says:
*the pattern rule's contractum and the `EtaK` contractum of one subject are joined by a one-sided
`ParRedK` leg meeting a nose `NormalEq`*. At the witness the pattern contractum is `g x` — which
`parRedK_app_bvar_bvar_eq` shows is rigid — and the `EtaK` contractum is `g ((fun y => y) x)`, so
the leg cannot move and `not_normalEq_gx` applies. `KetaExtraRow0.toWeak` is compiled, so the
weakening is confirmed to be a weakening.

**The direction is the whole content, and it cuts both ways.** Had the β-redex been on the leg's
side the row would have *held*. That is exactly what happens to `ExtraKetaRow` and `ExtraDevRow`,
which I checked by hand at `m = 0` and `m = 1` and which this witness does **not** reach: their
step is `keta` and their development is `extra`, so the leg starts at `g ((fun y => y) x)` and can
β-contract onto `g x`. `KetaAppRow` is likewise not reached — at `m = 0` the trivial step satisfies
it, and `qLift`'s spine at the witness is rigid, so there is no non-trivial congruence step to run.

**Round 3's weakened `KetaExtraRow` is NOT refuted here**, and I say why rather than leaving it
ambiguous: the same proof would additionally have to supply `∀ x, TriangleAtOn 1 qc1 (m2 x)` at the
witness. That is provable (the matched arguments are `bvar`s in `qc1`, and `TriangleAtOn 0` is
`zero_dev_row` outright) but it needs a typing per matched index, and I did not spend the budget.
**So the restatement the brief asked for is load-bearing, not cosmetic** — it is the difference
between a row this witness kills and a row it does not reach. That is the opposite of the brief's
expectation, which was that the weakening would make the rows *provable*; it makes them *harder to
refute*, which is the same fact seen from the other side.

### M16.4 — the accounting, dated: **2026-09-04**, population **479** built modules

`scripts/exists.lean`, run at HEAD `0cfbdc8` + my two modified files (HEAD then moved — see §20).
Population 479 against Round 2's 478; the +1 is another stream's module, not mine (I added no
module). Cone figures marked ↓1 moved because `TriangleAt`/`TriangleAtOn` changed module, which is
the noise C15.5 predicted and **must not be read as signal**.

| declaration | module | arity | cone | holes |
|---|---|---|---|---|
| **`quotParams_not_ketaDevAgree`** | `CParRedK` | 0 | **9334** | **2** `{forallE_inv_stratified, WF.rigidShapeUniqNS}` |
| **`quotParams_not_parRedKnTriangle`** | `CParRedK` | 0 | **9377** | **2** (same) |
| **`quotParams_not_ketaExtraRow0`** | `CParRedK` | 0 | **9374** | **2** (same) |
| `quotParams_not_rows_jointly` | `CParRedK` | 2 | 9384 | 2 (same) |
| `quotParams_triangle_holds_with_slack` | `CParRedK` | 0 | 9354 | 2 (same) |
| `parRedK_app_bvar_bvar_eq` | `CParRedK` | 6 | 754 | **0** |
| `parRedK_bvar_eq` | `CParRedK` | 5 | 748 | **0** |
| `KetaDevAgreePos` (the def) | `CParRedK` | 1 | 58 | **0** |
| `KetaExtraRow0` (the def) | `CParRedK` | 1 | 656 | **0** |
| `TriangleAt` (the def, moved) | `CParRedK` | 2 | 41 | **0** |
| `not_normalEq_gx` (the tool) | `QuotAppParams` | 0 | 9295 | 2 (same) |
| `quotParams_not_kDiamond` | `QuotAppParams` | 0 | 9328 | 2 (same) |
| `IsDefEqU.constApp_forallE_false_ofHyps` | `CRKProve` | 11 | **3931** | **3** |
| `crStatementK_of_rows` | `TrianglePort` | 6 | 4027 ↓1 | 3 |
| `parRedKnTriangle_of` | `TrianglePort` | 5 | 3962 ↓1 | 3 |
| `refParams_parRedKnTriangle` | `TrianglePort` | 0 | 7035 ↓1 | 3 |

**3931/3 reproduces byte-identically at a FOURTH commit** (`ca04f43` → `e0aee76` → `3aca413` →
`0cfbdc8`), and the population has now moved four times (471 → 477 → 478 → 479). The figure is
stable; the population is the number a reader would quote wrongly, for the fourth round running.

`#print axioms` (`lean_verify`, method rule 4 — this is the check that licenses the word "refuted"):

| declaration | axioms | verdict |
|---|---|---|
| `quotParams_not_ketaDevAgree` | `[propext, sorryAx, Classical.choice, Quot.sound]` | **CONDITIONAL** |
| `quotParams_not_parRedKnTriangle` | `[propext, sorryAx, Classical.choice, Quot.sound]` | **CONDITIONAL** |
| `not_normalEq_gx` (the tool it rests on) | `[propext, sorryAx, Classical.choice, Quot.sound]` | identical set |
| `parRedK_app_bvar_bvar_eq` | `[propext, Quot.sound]` | **hole-free** |

Two things this pins down. First, the refutation's hole set is **exactly** `not_normalEq_gx`'s —
`{IsDefEqU.forallE_inv_stratified, WF.rigidShapeUniqNS}`, **two** holes — so it inherits the
injectivity corner and adds nothing. Second, and worth its own line: the thing being refuted has
**three** holes (`IsDefEqU.weakN_iff` as well), so **the refutation is cheaper in taint than the
route it closes.** It also does not enter `NormalEq.descend`, which is absent from every row here
as it has been in all three previous rounds.

**The refutation must not be quoted as unconditional.** It is: *conditional on `PiInv` and
`WF.propTypeAgreeOn`* — the same corner, pre-existing, both `sorryAx`.

## §17 Verdicts (Round 3)

**W1 — How many of the four residuals are closed?  ZERO.  How many are REFUTED?  One outright,
and a second in the form Round 1 stated it.**
`quotParams_not_ketaDevAgree : ¬ KetaDevAgree` (cone 9334, 2 holes, conditional on the injectivity
corner) and `quotParams_not_ketaExtraRow0 : ¬ KetaExtraRow0` (9374, same 2 holes). And the
reduction target itself: `quotParams_not_parRedKnTriangle : ¬ ParRedKnTriangle` (9377). So the
three previous rounds' shared framing — "unproved, not false; both hold vacuously at `refParams`
and no refutation exists anywhere in the tree" — is **wrong**, and the refutation was reachable in
three lines from lemmas that had been sitting in `Verify/QuotAppParams.lean` the whole time.

**W2 — Can the 3931/3 figure be banked?  NO, and now for the strongest available reason.**
`IsDefEqU.constApp_forallE_false_ofHyps` is cone **3931**, holes **3**, at a fourth distinct
commit. Rounds 1 and 2 answered "no, because the hypotheses are unproved". The answer is now:
**no, because the hypothesis is (conditionally) false.** `crStatementK_of_rows` (4027, 3 holes)
remains a theorem — an implication with an unsatisfiable premise. Anyone quoting it as
"`CRStatementK` modulo four rows" must now quote it as "modulo four rows, one of which is false".

**W3 — Did the hypothesis-diff find the two rows understated, as the brief predicted?  YES, and
it was the wrong diff.**
Round 2's M9.3 had already measured `KetaAppRow`/`KetaExtraRow` as carrying no induction hypothesis
while `keta_keta_row` carries one; I made the §11.3 restatement (M16.1) and it compiles. But the
diff that produced the round's result was against a different neighbour and on a different axis:
`KetaDevAgree`'s **grade quantifier** against `CParRedKn.zero_eq`, Round 1's own lemma one screen
above it. `KetaDevAgree` is `∀ {m}`, `CParRedKn 0` is the identity, and the `m = 0` instance is
therefore `KDiamond` — refuted in the tree since before this stream started. **The brief's method
rule 3 said to diff hypotheses; the rule that would have found this says: instantiate every
universally quantified numeral at its extreme value before believing a residual.** See §19.1.

**W4 — What the restatement turned out to be for.**  Not to make the rows provable (S15.2 called
that, 0.8) but to make one of them **harder to refute**: `KetaExtraRow0` falls and Round 3's
weakened `KetaExtraRow` does not, because the refutation would have to supply
`∀ x, TriangleAtOn 1 qc1 (m2 x)` (M16.3). That is the same fact as "the row was overstated", seen
from the other side, and it is a use for a weakening that no round predicted.

**W5 — The diagnosis, and it is not about the quotient rule.**
`CParRedK.lean` §7.2 states it and §7's `quotParams_triangle_holds_with_slack` measures it: the
same witness at `n = 1, m = 2` **satisfies** the triangle. So what is false is not "the triangle at
this witness" but "the triangle when the development has no grade to spare" — and
`parRedKDiamond_of_triangle` manufactures exactly that, since it develops at `max n₁ n₂` and runs
the triangle at `n = m`. The mechanism:

* `CParRedKn`'s grade is consumed by `keta` and by nothing else (`beta`, `extra`, every congruence
  keep it), so a `CParRedKn m` development is complete **except** that K-chains are truncated at
  depth `m`, and a `keta` at the root spends a unit the term below then lacks;
* `ParRedKn`'s grade is spent by `beta` and `extra` too, and its congruences spend nothing;
* so `keta` against `keta` is in lockstep (which is why `keta_keta_row` closes), and `keta` against
  a **congruence** is not (which is why `KetaAppRow` is the one row with a grade off-by-one);
* no fixed slack repairs it: a K-chain of length `k` costs the development `k` units and the step
  none, and `k` is bounded only by the development's own grade.

**So the apex of the triangle has to be a complete development, and `CParRedKn m` is not one.** An
ungraded `CParRedK` needs the K-chain to terminate, which nothing in `Params` supplies — which is
precisely what Round 1's own shape prior S2 observed about `CParRedKn.exists` before working around
it with the grade. **The grade is what makes existence provable and the triangle false.** That is
the sentence this stream has been three rounds away from.

### §17.1 Scorecard for §15's priors

| prior | claim | conf. | outcome |
|---|---|---|---|
| S15.1 | the four residuals meet at one unnamed survival engine, and the deliverable is the engine | 0.85 | **HALF RIGHT, and the half that was right cost the round nothing.** The engine analysis is correct for `KetaAppRow` and for `ExtraDevRow`'s eight old rows. It is **wrong** that all three consumers need it: `KetaExtraRow`/`ExtraKetaRow` are same-node rows needing rule-table facts. And I never built the engine — the result came from elsewhere. |
| S15.2 | adding the IHs makes the rows weaker but not provable | 0.8 | **RIGHT, and understated.** Not merely unprovable: one is false, and the list is jointly false. |
| S15.3 | the engine's `keta` case needs a third disjunct at the root only | 0.75 | **UNTESTED.** I did not build the engine. Recorded unscored rather than claimed. |
| S15.4 | `KStep` survival is not derivable from `KStep.defeq`; the `IsDefEq`-to-`NormalEq` move is the trap | 0.9 | **RIGHT, and load-bearing in a place I did not foresee.** The trap I wrote down in order to avoid it is the *mechanism* of the refutation: `NormalEq` has no β step, so it cannot absorb the one β-step separating the two contracta. The prior written to prevent an error became the proof. |
| C15.1 | the §11.3 restatement compiles this round | 0.85 | **RIGHT** (M16.1), two builds, one mechanical failure recorded. |
| C15.2 | I close 0 of the four | 0.6 | **RIGHT, and the wrong axis.** I closed 0 and refuted 1 (+1 in its original form). "Closed" was the wrong question to have a prior about. |
| C15.3 | 3931/3 cannot be banked | 0.8 | **RIGHT**, for a far stronger reason than predicted. |
| C15.4 | census stays 13, build green, no `sorry` written | 0.95 | Census **13** ✓, no `sorry` in either of my files ✓, my two modules green ✓; the *bare* build is red for another stream's reason (§20). |
| C15.5 | ±3 cone noise from moving `TriangleAt` | 0.9 | **RIGHT and exact**: −1 on each of the three `TrianglePort` figures, 0 elsewhere. |

## §18 Limits of this result, and where I proved them

1. **The refutation is CONDITIONAL and I will not write it any other way.**  It rests on
   `not_normalEq_gx`, whose cone reaches `IsDefEqU.forallE_inv_stratified` and
   `WF.rigidShapeUniqNS` (`PiInv` and `WF.propTypeAgreeOn` in `QuotAppParams`' own words). Both are
   pre-existing `sorryAx` holes and neither is new — `#print axioms` in M16.4 — but "`KetaDevAgree`
   is false" is not an unconditional statement, and the rigidity half
   (`parRedK_app_bvar_bvar_eq`, `[propext, Quot.sound]`) is the only hole-free part.
2. **`ParRedKDiamond` and `CRStatementK` are NOT refuted, and nothing here says they are.**
   A false antecedent says nothing about a consequent. Moreover the diamond's legs are two-sided
   `ParRedK` steps, so the refuting pair *joins* there
   (`Verify/QuotAppParams.quotParams_kDiamond_joinable`, already in the tree). What is refuted is
   the **triangle**: a one-sided leg meeting a nose `NormalEq` against a grade-truncated apex.
   `TrianglePort.lean` §6 item 5 states this in the file itself so it cannot be misread from the
   Lean alone.
3. **I refuted `KetaDevAgree` and `KetaExtraRow0`; I did NOT refute `KetaAppRow`,
   `KetaExtraRow` (weakened), `ExtraDevRow` or `ExtraKetaRow`, and I checked each rather than
   assuming.**  `KetaAppRow` at `m = 0` is satisfied by the trivial step and the witness's `qLift`
   spine is rigid, so there is no non-trivial congruence to run; `ExtraKetaRow`/`ExtraDevRow` have
   the β-redex on the *leg's* side and so hold at the witness; the weakened `KetaExtraRow` needs
   `∀ x, TriangleAtOn 1 qc1 (m2 x)`, which is provable but which I did not spend the budget on.
   **That last one is the obvious next step and I am naming it as unfinished, not as impossible.**
4. **The grade diagnosis (§17 W5, `CParRedK.lean` §7.2) is analysis, not a theorem.**
   `quotParams_triangle_holds_with_slack` proves the *tightness* of the refutation — one unit of
   slack rescues this row — and that is real Lean. The claim that **no** fixed slack rescues the
   table is an argument about the two grade disciplines, written out in §7.2 and not machine
   checked. In particular I did not construct a witness with a K-chain of length two.
5. **`KetaDevAgreePos` is stated and not proved, and it does not suffice.**  It is the corrected
   residual (`KetaDevAgree.toPos` compiled, so it is genuinely weaker), and
   `quotParams_ketaDevAgreePos_at_witness` shows this witness satisfies it *by equality*, not
   merely up to `NormalEq`. But §7.2's argument says the positive-grade restriction still leaves
   `KetaAppRow`'s off-by-one, so **restricting the grade is not the repair.** Anybody who reads
   §7.1 and then just changes `m` to `m+1` will have moved the problem, not fixed it.
6. **I did not build S15.1's survival engine**, so `ExtraDevRow`'s eight rows of known-provable
   transcription debt are exactly where Round 2 left them, and §4a's five measure lemmas are still
   unused by any proof. If the graded route is abandoned the engine is still needed by whatever
   replaces it, because it is a fact about patterns under parallel reduction and not about grades.
7. **`refParams` could not have detected any of this and I can say why.**  At `refParams` both
   `KStep` and `Pat` are empty, so `refParams_parRedKnTriangle` is unconditionally true *and* the
   refutation cannot be transported there. Round 2's joint-satisfiability check was therefore
   sound and worthless in the same breath: it established that the rows are consistent **at the one
   instance where every one of them is vacuous**. A satisfiability check at a degenerate instance
   is not evidence, and this round is what that costs.
8. **One thing I did not check at all**: whether the same grade-`0` instantiation refutes residuals
   in *other* files of this stream's neighbourhood (`KSite7App.lean`'s open rows, `KDiamondJoin`'s
   `KDiamondJ`, `KEtaDiamond`'s `EtaKD`). Every `∀ {m : Nat}` over `CParRedKn`/`ParRedKn` in the
   tree is now a candidate and I looked at none of them.

## §19 Method gaps, mine

1. **The rule that found this is not the rule I was given, and it is cheaper.**  My brief's method
   rule 3 is "before attempting a named residual, diff its hypotheses against its neighbours'". I
   did that (M16.1) and it produced a correct, compiled, and *incidental* restatement. What
   produced the result is: **instantiate every universally quantified numeral in a residual at its
   extreme value, and read what the residual then says.** `KetaDevAgree` at `m = 0`, one
   substitution, and the answer is a `Prop` the tree already refutes. I only did it because I was
   doing grade arithmetic for a different purpose (checking whether `KetaAppRow` reduces to
   survival) and the `m = 0` boundary fell out. **Three rounds ran method rule 3 and none ran
   this.** It belongs in the next brief above the hypothesis-diff, because it is strictly cheaper:
   no neighbour needs to be found.
2. **I spent the first two thirds of the round on an engine I never built, on the strength of a
   0.85 prior.**  S15.1 predicted the four residuals meet at one survival lemma and that the
   deliverable was that lemma. The prior was half wrong and, worse, it was *aimed*: I read
   `ParRed.triangle`'s `extra` case in full and reasoned about `Pattern.Matches` survival for a
   long time before doing any arithmetic on the grade. The generalizable error: I treated the
   brief's framing ("two of them are not hard", "eight rows of known-provable transcription debt")
   as a description of *where the work is* rather than as a hypothesis to test first. Round 2's
   §12.3 named the inverse failure (a pessimistic prior becoming a budget decision); mine is an
   **optimistic** prior becoming one.
3. **I asserted a grade off-by-one in `KetaAppRow` in my own reasoning several times before
   checking whether the same reasoning applied to the residual one row over.**  It did, and worse:
   the same arithmetic that shows `KetaAppRow` needs `n ≤ m` shows `KetaDevAgree`'s `m = 0`
   instance is `KDiamond`. I had the fact and did not turn it round for a while.
4. **A mechanical error worth its own line, because it will recur.**  Hoisting `have IHapp` above
   `cases H2` in `TrianglePort.triangleAt_of` silently changed the **arity** of an unrelated
   induction's hypotheses: `IHapp` mentions `e`, so `induction p generalizing e A` reverted it and
   every pattern IH acquired an extra argument. `clear IHapp` fixes it. The lesson is not about
   `clear`: it is that in this file the below-structure `e_ih` and everything that mentions the
   subject are entangled with any later `generalizing e`, so a `have` hoisted for reuse is not a
   free refactor.
5. **My brief's premise "no other stream is running, so a bare `lake build` is a clean signal" was
   false, and I only noticed at the end.**  `Lean4Lean/Verify/Inductive/InductMap.lean` and two
   handoff docs appeared untracked during the round, HEAD moved from `0cfbdc8` to `11efd98` under
   me, and the bare build is now **red** with three errors all inside that untracked file. I
   verified my own two modules independently (green, 1292 jobs) but I should have taken a
   `git status` + HEAD snapshot at the start *and* re-checked before quoting a bare-build number,
   rather than trusting a brief's claim about the environment. §20 records both measurements with
   times.

## §20 Build record, dated — and the environment moved under me twice

| when | HEAD | command | result |
|---|---|---|---|
| round start, 2026-09-04 ~22:0x | `0cfbdc8` | bare `lake build` | green, **1665 jobs**, exit 0 (matches the brief) |
| mid-round | `0cfbdc8` | `lake build …CParRedK` / `…TrianglePort` | green, 1291 / 1292 jobs |
| ~23:0x | `0cfbdc8` | bare `lake build` | green, **1666 jobs** — the +1 is another stream's new module, not mine |
| ~23:08 | `11efd98` | bare `lake build` | **RED**, 3 errors, all in `Lean4Lean/Verify/Inductive/InductMap.lean` (untracked, another stream, mid-edit) |
| round end | `11efd98` | bare `lake build` | green, **1667 jobs**, exit 0 |
| round end | `11efd98` | `lake build Lean4Lean.Verify.Guard` | guards 1/2/3 all ✓ |

**HEAD moved twice under me** (`0cfbdc8` → `11efd98`, the latter a `CLAUDE.md` correction), and
**another stream is live** in this tree despite my brief's "No other stream is running, so a bare
`lake build` is a clean signal". `InductMap.lean` and two handoff docs appeared untracked during
the round. Job counts therefore attribute as: my two modules add **0** modules and **0** jobs; the
1665 → 1667 drift is entirely another stream's. Every cone figure in M16.4 was measured at
population **479**, which already includes their module.

Guards at round end: **guard 1 ✓** (24 frozen axioms), **guard 2 ✓** (within whitelist; proof
INCOMPLETE, `sorryAx` present — unchanged), **guard 3 ✓** (2/2 implementation gaps — unchanged).
**Census 13, unchanged** (`grep -c "declaration uses \`sorry\`"` on the bare build log = 13), and
none of the thirteen is in a file I own. `grep -n sorry` on both my files returns **only prose
mentions of `sorryAx`** — no `sorry` tactic in either.

Files touched this round, and nothing else:
`Lean4Lean/Theory/Typing/CParRedK.lean` (§4.1 the moved definitions; §5.2 the two weakened rows and
`keta_root_row`'s three new hypotheses; §5.2a `KetaExtraRow0`; §5.3 the rigidity lemmas and
`KetaDevAgreePos`; **§7 the refutation**), `Lean4Lean/Theory/Typing/TrianglePort.lean` (§1 note,
`IHapp`/`IHpat` hoisted, the `extra` case shortened to one line, **§6 what the refutation does to
this file's own claims**), `docs/handoff-cparredk.md` (§15–§20 appended; **§1–§14 untouched**).

No state-changing git command was run. No frozen file (`Verify/Soundness.lean`,
`Verify/Axioms.lean`, `Verify/Guard.lean`) was read for editing or edited. No file outside my two
was modified — and this round did **not** need one, which is itself worth recording, because the
refutation's two tools (`not_normalEq_gx`, `quotParams_kstep_x/xbeta`) were already exported from
`Verify/QuotAppParams.lean` and already imported through `CRKProve.lean`.

### §20.1 The one-line handover

**`ParRedKnTriangle` is false (conditionally), `KetaDevAgree` is the false residual, the grade is
why, and the repair is not a smaller grade — it is a complete development, which needs the K-chain
to terminate.** Start the next round by instantiating `∀ {m : Nat}` at `0` in every residual in
this neighbourhood, before reading anything else.
