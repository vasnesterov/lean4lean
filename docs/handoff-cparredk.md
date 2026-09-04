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
