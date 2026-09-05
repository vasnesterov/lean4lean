# handoff-skipuninhab

Round start: 2026-09-05. HEAD `31b8790`. Brief reports: bare build green at 1679 jobs, guards
1/2/3 ✓, census 13 (all three to be re-measured, see §3).

Owner files: `Lean4Lean/Verify/Typing/SkipUninhab.lean` (new), this file. Everything else
read-only. **`Verify/Typing/Lemmas.lean` holds the hole and is not mine to edit** — if the
residual is dischargeable I prove the content in `SkipUninhab.lean` and state the exact edit.
`Verify/Soundness.lean`, `Verify/Axioms.lean`, `Verify/Guard.lean` frozen. No state-changing git.

Target: `Lean4Lean.VEnv.ProjSkipUninhab` (`Verify/Typing/ProjDataAttack.lean`:171) — the residual
of hole #1 `TrProj.weak'_inv` after last round's reduction through `TrProj.instN`. Stated at
`Ordered` strength. **Prove it, or refute it, or reduce it and name what remains.**

Marks: **[measured]** = a command run in this round; **[read]** = read off source in this round;
**[analysis]** = neither.

---

## §1 Shape questions

**Written before opening `TrProj`'s definition, `ProjInhab.lean`, `ProjExistClose.lean`,
`ProjWeakInvSplit.lean`, `Lemmas.lean`, `docs/handoff-projdata.md`, `docs/audit-hole-producers.md`,
or any script.** What was read at write time: `CLAUDE.md`; `git log -1`; `ls docs/`;
`Verify/Typing/ProjDataAttack.lean` **in full** (the brief points at it and quotes it);
`docs/handoff-transnarrow.md:1-80` and `docs/handoff-adddecl.md:1-100` for the house §1/§2 format
only. Prediction lines are written in one pass immediately after the questions and **before any
further read**. Answers are appended in §2. **A filled answer is never edited**; corrections go
in §2 with a date.

### The four shape questions, instantiated to "is `VEnv.ProjSkipUninhab` true?"

**Q1 — Does the target exist in the shape the brief gives it, judged on all three searches
(conclusion-head, hypothesis-shape, hole audit) and not on the name?**
(a) Is `VEnv.ProjSkipUninhab` a `def … : Prop` with `env U` explicit (so quantifier-extreme probes
work), and is `TrProj.weak'_inv_of_skipUninhab` really arity 14 / cone 3412 / hole-free at
`31b8790`?
(b) **Definitional aliases and generation drift** (rule 3, and rule 3's own recorded failure): the
type-only analogue is `VEnv.ConstAppSkipUninhab`, and the family also holds
`ConstAppTypeStrengthen`, `ProjStrengthen`, `ProjDataStrengthen`, `TypingStrengthening`,
`ConstAppDefeqStrengthen`. How many *distinct* one-uninhabited-binder statements exist in the
tree, and is `ProjSkipUninhab` the newest generation or already superseded? Every conclusion-head
search must cover every generation.
(c) **Hole audit** (rule 3, third search, not optional): does anything in the tree already *prove*
a one-uninhabited-binder strengthening statement — and if so, does its proof call
`IsDefEqU.weakN_iff`, `forallE_inv_stratified`, `rigidShapeUniqNS` or the `sorry` in
`Lemmas.lean`? A producer can exist **and be useless**.
(d) Has the type-only analogue `ConstAppSkipUninhab` already been *refuted* somewhere (the
vacuity ledger / a `_false` lemma)? If it has, the same counterexample may transfer and this round
is a refutation round, not a proof round.
  - Prediction (committed before the reads that resolve it): (a) yes, `def … : Prop`, `env U`
    explicit; the arity/cone/hole-freeness reproduce. (b) **at least four** distinct
    one-uninhabited-binder statements, `ProjSkipUninhab` newest. (c) **nothing proves one**; the
    strengthening statements in the tree are all either hypotheses or reductions. (d) **not
    refuted** — I expect no `_false` lemma for `ConstAppSkipUninhab`, because the family's
    docstrings uniformly say "unproved, not false".
  - Answer (§2): _____

**Q2 — Quantified arguments at the extremes, with the side condition's extremes read as *what it
permits* and I assumed it forbade** (rule 2, refinements 2 and 5).
(i) The side condition is `∀ Γ₀ A₀ e₀, Ctx.InstN Γ₀ e₀ A₀ k Γ' Γ → ¬ env.HasType U Γ₀ e₀ A₀` —
"the inserted binder is uninhabited below the cut". What it **permits** and I would have assumed
it forbade: **`A₀` need not be a type at all.** `ProjSkipUninhab` carries **no `OnCtx Γ'`** and
**no `VEnv.WF`**, so `Γ'` may be outright garbage — an *open* entry, a `Prop`-valued
non-type, anything. `projSkipUninhab_fires` already lives exactly there (`A₀ = .bvar 1`). Is the
statement **false at such a `Γ'`**?
(ii) `k` at its extremes: `k = 0` (`Γ' = A₀ :: Γ`, and `Ctx.InstN … 0 …` has the single `zero`
constructor) and `k = Γ'.length - 1`. Is `k = 0` a **normal form** — i.e. is the general `k` case
reducible to `k = 0` (rule 2's fifth refinement, which is how the neighbouring `transnarrow`
round won)? If yes the residual is a one-entry statement.
(iii) `e` at its extremes: `e = .bvar j`, `e = .sort`, `e` a `const`-application. Is there an `e`
for which `TrProj` at `Γ'` holds and at `Γ` cannot?
(iv) **Monotonicity before calling a witness cheap** (rule 2, refinement 4): if `ProjSkipUninhab`
holds at `env`, does it hold at every `env' ≥ env`? If it is *not* monotone, a counterexample env
cannot be extended to a `VEnv.WF` one for free, and the refutation route is capped at whatever
env I can exhibit.
  - Prediction (committed before the reads that resolve it): (i) **yes — this is the round's main
    bet: `ProjSkipUninhab` is FALSE as stated**, and false for the reason §4.2 of
    `ProjDataAttack.lean` records as the *scope* of its own witness: the statement's freedom from
    `OnCtx Γ'` is what makes the uninhabited hypothesis cheap to satisfy, and the same freedom
    should let `Γ'` type things `Γ` cannot. Route: `k = 0`, `A₀` open, `TrProj` at `Γ'` whose
    structure-application type mentions `bvar 0`. (ii) `k = 0` **is** a normal form, by the same
    `Ctx.LiftN`/`InstN` exchange the sibling round used. (iii) yes, and the witness is a
    `const`-application, not a bvar. (iv) **not monotone in an obvious direction**: the side
    condition `¬ HasType` is *anti*monotone in env while the conclusion is monotone, so
    `ProjSkipUninhab` is neither — which is itself worth stating, since it means adding
    declarations can break it.
  - Answer (§2): _____

**Q3 — Measurement or docstring? Every number and every claim in my brief, classified and re-run
at `31b8790`.**
(i) `TrProj.weak'_inv_of_skipUninhab`: arity 14, cone 3412, **zero holes, zero watched names**.
(ii) The previously-best route `TrProj.weak'_inv_of_strengthen`: cone 3698, holes
`{weakN_iff, forallE_inv_stratified, rigidShapeUniqNS}`, watched
`{HasArgs.of_mkApp, IsDefEq.uniq, IsDefEq.uniqU}`.
(iii) `TrProj.instN`: `Lemmas.lean`, arity 16, cone 2340, hole-free.
(iv) `VEnv.AllTypesInhabited.projStrengthen` hole-free; `projSkipUninhab_fires` hole-free.
(v) `addDecl.WF_honest`: eight holes, four live, one known false, one vacuous, two tripwires.
(vi) census 13, bare build 1679 jobs, guards 1/2/3 ✓.
(vii) **Date the family** (rule 4): `git log -1 --date=short` on every file I lean on. The brief
warns two "sharpest statement" pointers in this repo were three generations stale — is
`ProjDataAttack.lean` §4.3 the current sharpest, or has a later file superseded it?
  - Prediction (committed before the reads that resolve it): (i)-(iv) reproduce; (v) reproduces;
    (vi) census 13 and guards ✓, job count may differ from 1679 by a handful; (vii)
    `ProjDataAttack.lean` is **the newest file in the family** (dated 2026-09-04 in its own
    header) and is the current sharpest — but I predict at least one *other* file in the family
    is ≥ 2 generations stale and I will find a stale pointer in `audit-hole-producers.md` §M9.
  - Answer (§2): _____

**Q4 — If I predict a circularity, which move does it attach to, and does the target actually use
that move?** (rule 2, refinement 6 — a round last week vetoed a working probe by citing a true
fact about a *neighbouring* operation.)
(i) My structural prediction is that `ProjSkipUninhab`'s whole content is **typing strengthening
across one binder**, which is the same mathematics as `IsDefEqU.weakN_iff` (hole #2 of the four).
The move it attaches to is the `hty` field of `TrProj.mk`:
`env.HasType U Γ' (e.lift' l) ((VExpr.const S us).mkApp (ps ++ ιs))`, whose type must be
*re-chosen* at `Γ`. **Does `ProjSkipUninhab` actually need that move**, or does `TrProj`'s
existential over `D' T' C' us' ps' ιs'` give enough slack that the type never has to be
strengthened — e.g. because `TrProj`'s own premises already pin the type up to something
`Γ`-expressible?
(ii) The converse circularity: can `ProjSkipUninhab` be **derived from** `IsDefEqU.weakN_iff`?
If yes, the two live holes are ordered and this one is not independent work; if no, they are
genuinely separate and both must be paid.
(iii) Is there a *third* route that avoids both: `TrProj`'s subject is `e.liftN 1 k`, i.e.
`Skips 1 k`. Does the tree have a strengthening lemma for `HasType` whose only hypothesis is
`Skips` **on the subject** (not on the type)?
  - Prediction (committed before the reads that resolve it): (i) **yes, it needs the move** — the
    existential does not save it, because `ps`/`ιs` are pinned by the `IsStructure` block up to
    defeq, and defeq at `Γ'` is exactly what does not descend. (ii) **yes, derivable from
    `weakN_iff` plus a typing-strengthening lemma**, so not independent; but I predict
    `weakN_iff` alone is not enough (the typing half is separate — the sibling round split
    `TypingStrengthening1Inner` off from `TransStrengtheningNarrowInner` for exactly this
    reason). (iii) I predict **such a lemma does not exist** for `HasType`, only for `IsDefEq`
    under `weakN_iff`.
  - Answer (§2): _____

---

## §2 Verdicts

_(appended as each is resolved; never edited)_

### Q1 — answer (2026-09-05)

(a) **Yes** [read]. `VEnv.ProjSkipUninhab` is `Verify/Typing/ProjDataAttack.lean`:171, a
`def … : Prop` with `env U` explicit and seven implicit binders (`k Γ Γ' s i e e'`). It carries
**no `env.Ordered`, no `VEnv.WF`, no `OnCtx`** — not even `Ordered`, which its own consumer
`projStrengthen_of_skipUninhab_aux` supplies separately. Cone/arity figures re-measured in §3.

(b) **Six distinct statements in the one-uninhabited-binder family**, and `ProjSkipUninhab` is the
newest of the projection ones but **not** the newest of the family [read]:

| statement | file | `OnCtx Γ` | `OnCtx Γ'` | one binder | relation to its hole |
|---|---|---|---|---|---|
| `VEnv.Strengthening1Uninhab` | `Theory/Typing/Strengthen.lean` §12 | **yes** | **yes** | yes | **`iff_target`** |
| `VEnv.TypingStrengthening1Uninhab` | `Theory/Typing/StrengthenInhabGate.lean` §3 | yes | yes | yes | `iff_typing` |
| `VEnv.StrengtheningCanonUninhabInner` | `WeakNAttack.lean` §5 (per `UniqueTyping.lean`:191) | — | — | inner | `iff_target` |
| `VEnv.ConstAppSkipUninhab` | `Verify/Typing/ProjWeakInv.lean`:453 | no | **no** | yes | ⟹ only |
| `VEnv.ProjSkipUninhab` | `ProjDataAttack.lean`:171 | no | **no** | yes | ⟹ only |
| (`VEnv.ProjStrengthen` / `ProjDataStrengthen`) | `ProjExistClose.lean`:64,71 | no | yes | no | ⟺ hole |

**This is the round's first real finding and it inverts the brief's framing.** The `Theory/`-side
members of this family *keep both `OnCtx`s and are `iff` with their target*. The two `Verify/`-side
projection members drop `OnCtx` and are one-directional. So `ProjSkipUninhab` is not the sharpest
member of its own family — it is the only generation that gave `OnCtx` away, and the model for
getting it back was already in the tree, two files up the import chain
(`Strengthening1Uninhab.strengthening1` + `Strengthening1.onCtx_inv`).

(c) **Hole audit: nothing proves any of the six.** All are open. `Strengthening1Uninhab.iff_target`
and `TypingStrengthening1Uninhab.typingStrengthening1` are hole-free *reductions*, and
`TypingStrengthening1Uninhab.iff_typing` is measured at cone 3607 carrying
`forallE_inv_stratified` + `rigidShapeUniqNS` [read, from `StrengthenInhabGate.lean`'s own table].
The projection ones are hole-free reductions too. No producer, useless or otherwise.

(d) **Not refuted, and better than that: the analogue is refuted *as a residual*, not as a
statement** [read]. `ProjInhab.lean` §3/§4 (`constAppSkipUninhab_uninhab_premise_illFormed`)
proves that `ConstAppSkipUninhab`'s uninhabitedness premise is satisfiable **unconditionally, over
every environment**, by an inserted binder that is not a type at all — instances that
`ConstAppTypeStrengthen`'s `OnCtx Γ'` excludes. That file's verdict: "the one-binder form is
strictly stronger than the residual, and **it cannot be repaired by adding `OnCtx Γ'` without
re-importing the gate**". §4 below **refutes that last clause**: the repair exists and is
hole-free. Prediction (d) was right about the letter (no `_false` lemma) and wrong about what was
already known.

### Q4 — answer (2026-09-05)

(i) **Yes, `hty` is the move, and it is the only one** [read] — `TrProj` is a ten-field
single-constructor inductive (`Verify/Typing/Expr.lean`:82); of the ten, `hS`, three lengths,
`hi`, `hus` and F17 are context-free, and the two `HasArgs` plus `hty` are the context-carrying
ones. My prediction that the existential over `D' T' C' us' ps' ιs'` does not save it is
confirmed by `ProjDataStrengthen`'s own statement, which requantifies all six and still has to
produce `HasType Γ e ((const S us').mkApp (ps' ++ ιs'))`.

(ii) **Yes — and this is the round's second finding, now a theorem** (§5 below): hole #1 reduces,
hole-free, to `Strengthening1Uninhab` (hole #2's own residual, already `iff` with hole #2's
target) **plus** a one-binder projection statement carrying `OnCtx Γ` *and* `OnCtx Γ'`. So the
two live holes are **ordered**: paying hole #2 buys back both well-formedness premises here.
The prediction "derivable from `weakN_iff` plus a typing-strengthening lemma" was directionally
right and imprecise about which piece: it is `Strengthening1.onCtx_inv`, i.e. exactly the
`OnCtx.weak'_inv` step that `Lemmas.lean`:882-884 already identifies as the **single** point at
which `IsDefEqU.weakN_iff` enters `TrProj.weak'_inv`.

(iii) **Prediction wrong.** A `Skips`-on-the-subject strengthening lemma for `HasType` *does*
exist — `HasType.skips` (`Verify/Typing/Lemmas.lean`, cited at :722), which produces `B` with
`B.Skips n k` from a lifted subject. It is not enough on its own (steps 2 and 3 of the route at
:724-726 are `IsDefEq.uniqU` and `IsDefEqU.weakN_iff`), but the lemma is there and I predicted
absence.

### Q2 — answer (2026-09-05)

(i) **My main bet is NOT confirmed, and it is not refuted either — and the round found a better
answer than either.** I predicted `ProjSkipUninhab` is false, refutable at an ill-formed `Γ'`. What
the reads establish is that a refutation would have to be a genuine failure of one-step
strengthening at a junk context, and the junk *does not supply the resource I assumed it would*:
the only extra power a `Γ'` with an uninhabited entry `A₀` has over `Γ` is the term `.bvar k : A₀`,
and the subject of the `TrProj` premise is a **lift**, so it can never be that term. Reading
`Theory/Typing/Basic.lean`'s fourteen `IsDefEq` constructors, only two are context-sensitive
(`bvar` via `Lookup`, and `proofIrrel` via `Γ ⊢ p : .sort .zero`), and
`StrengthenVerdict.lean` §2/§5 has already run the `proofIrrel` attack and shown it dies at its
own witness. So the cheap refutation route is **closed, with the reason named**, and my prediction
was wrong in direction. What replaces it: §2 and §4 of `SkipUninhab.lean` — the residual does not
need to be true, because an *equivalent* residual with `OnCtx Γ'` retained exists and is proved.

(ii) **`k = 0` is not the normal form and the position quantifier is not where the content is** —
prediction wrong. The sibling `transnarrow` move does not transfer: the reason `k` collapses for
`Strengthening` is `Strengthening1.onCtx_inv`, which manufactures `OnCtx` from the strengthening
hypothesis *itself* by running it on `.forallE A (.sort .zero)`. A `TrProj` residual cannot do
that — it concludes `TrProj`, not `IsDefEqU` — which is exactly why the projection generations
dropped `OnCtx` instead. `k = 0` *is* the one position at which `OnCtx (A₀ :: Γ) → OnCtx Γ` is
free (it is `.1` of the pair), and that observation is what makes §3's residual statable with both
`OnCtx`s; but reducing an arbitrary `Lift'` to that position is precisely `OnCtx.weak'_inv`, the
gate. Correct normal form found instead: **do not reduce to one binder at all** (§2).

(iii) **Yes in shape, no witness.** The `e` for which `TrProj` at `Γ'` could hold and at `Γ` fail
must have its *type* re-chosen, and the only route to a type mentioning the stripped variable is a
`defeqDF` step, i.e. a conversion available upstairs and not downstairs — see (i). Prediction
"the witness is a `const`-application, not a bvar" is unverifiable because no witness exists.

(iv) **Monotonicity: prediction confirmed in direction, not machine-checked.** `ProjSkipUninhab`'s
side condition `¬ env.HasType …` is antitone in `env` while its conclusion `∃ e'', TrProj …` is
monotone, so the predicate is neither monotone nor antitone [analysis, not proved]. Consequence
worth carrying: a counterexample at a small environment cannot be extended to a `VEnv.WF` one for
free, which is a second, independent reason the refutation route in (i) is not cheap. Not proved
here because §2/§3 made it moot — with `OnCtx Γ'` retained the residual is an instance of the hole
and its truth at every `VEnv.WF` environment is exactly the hole's.

### Q3 — answer (2026-09-05), every figure re-run at `31b8790` + this file

(i) **Reproduced exactly** [measured]. `TrProj.weak'_inv_of_skipUninhab`: arity 14, cone **3412**,
`own value is a hole: false`, `cone reaches sorryAx: false`, `watched: none of 6`.

(ii) **Reproduced exactly** [measured]. `TrProj.weak'_inv_of_strengthen`: arity 14, cone **3698**,
holes `[IsDefEqU.weakN_iff, IsDefEqU.forallE_inv_stratified, WF.rigidShapeUniqNS]`, watched
`[HasArgs.of_mkApp, IsDefEq.uniq, IsDefEq.uniqU]`. All six.

(iii) **Reproduced** [measured]. `TrProj.instN`: `Verify/Typing/Lemmas.lean`, arity 16, cone
**2340**, hole-free.

(iv) **Reproduced** [measured]. `VEnv.AllTypesInhabited.projStrengthen` 4 / 2376 hole-free;
`projSkipUninhab_fires` 0 / 4354 hole-free. Also `VEnv.ProjSkipUninhab` 2 / 145 and
`VEnv.ProjStrengthen` 2 / 80.

(v) **NOT measured, and I am not relaying it.** I did not measure `addDecl.WF_honest`'s eight
holes / four live / one false / one vacuous / two tripwires. What I did measure is the census's own
transitive-user counts, which are the numbers that matter here: `TrProj.weak'_inv` **90**
transitive users; `IsDefEqU.weakN_iff` **311**; `forallE_inv_stratified` **742**;
`rigidShapeUniqNS` **461**; `NormalEq.descend` **200**.

(vi) **Census 13 on both instruments** [measured, twice]: `scripts/sorry-census.lean` reports
`TOTAL declarations directly containing sorryAx: 13`, and `scripts/sorry-census-all.lean` — the
filesystem-walking one, which is the only instrument whose population contains this round's new
module at all — reports `HOLES over the WHOLE built population, unioned across both passes: 13`,
with `SkipUninhab` listed among the 60 orphan modules and contributing none.
**Bare `lake build`: `Build completed successfully (1680 jobs)`** — 1679 before plus this one new
module, so the brief's 1679 is confirmed rather than contradicted. **Guards re-run explicitly**
(`lake env lean Lean4Lean/Verify/Guard.lean`, because a cached `Guard.lean` re-emits nothing during
`lake build` and this module is a leaf that cannot invalidate it): guard 1 "exactly the 24 frozen
axioms ✓", guard 2 "within whitelist ✓ (proof INCOMPLETE: sorryAx present)", guard 3 "2/2
remaining ✓".

(vii) **Dating the family — one of my predictions was right and it mattered** [measured,
`git log -1 --date=short`]:

| file | last touched |
|---|---|
| `Theory/Typing/UniqueTyping.lean` | **2026-09-05** (`31b8790`, this HEAD) |
| `Verify/Typing/ProjDataAttack.lean` | 2026-09-04 |
| `Theory/Typing/Strengthen.lean` | 2026-09-03 |
| `Theory/Typing/StrengthenVerdict.lean`, `Verify/Typing/ProjInhab.lean` | 2026-09-03 |
| `Theory/Typing/StrengthenInhabGate.lean` | 2026-09-01 |
| `Verify/Typing/ProjWeakInv.lean` | 2026-09-01 |

`ProjDataAttack.lean` **is** the newest file in the projection family and its §4.3 was the current
sharpest statement of the projection obstruction. But the sharpest statement of the *shape* problem
was four days older and in a different directory (`Strengthen.lean` §11-§12), and `ProjInhab.lean`
(2026-09-03) is **two generations behind** on the one claim this round overturns. The prediction
"at least one other file in the family is ≥ 2 generations stale" is confirmed, and it is the file
whose §3 says the repair is impossible.

---

## §3 Scorecard

| Q | prediction | verdict | what it cost / bought |
|---|---|---|---|
| Q1(a) | `def : Prop`, figures reproduce | ✓ | free |
| Q1(b) | ≥4 statements, `ProjSkipUninhab` newest | **✓ in count (six), ✗ in ranking** | the round's opening: the `Theory/`-side generations keep both `OnCtx`s and are `iff`; only the two `Verify/`-side projection ones gave `OnCtx` away |
| Q1(c) | nothing proves one | ✓ | free |
| Q1(d) | not refuted, no `_false` lemma | ✓ letter, ✗ substance | the *defect* was already proved (`constAppSkipUninhab_uninhab_premise_illFormed`) together with a claim that it is unrepairable — which §2 refutes |
| Q2(i) | **`ProjSkipUninhab` is FALSE** | **not confirmed, not refuted** | the round's main bet, and wrong in direction: the junk binder supplies only `.bvar k : A₀`, which the lifted subject can never be |
| Q2(ii) | `k = 0` is a normal form | ✗ | the sibling round's move does not transfer; `k = 0` is where `OnCtx` descends free, which is what makes §3 statable, but reaching it *is* the gate |
| Q2(iii) | witness is a `const`-application | unresolvable | no witness exists |
| Q2(iv) | neither monotone nor antitone | ✓ [analysis only] | moot once §2 made the residual an instance of the hole |
| Q3(i)-(iv),(vi) | reproduce | ✓ all | free |
| Q3(v) | reproduces | **not attempted** | recorded as a miss, not a result |
| Q3(vii) | `ProjDataAttack` newest & sharpest; one stale pointer | ✓ both | located the overturned claim |
| Q4(i) | `hty` is the move, existential does not save it | ✓ | free |
| Q4(ii) | derivable from `weakN_iff` + a typing lemma | ✓, and **sharpened to a smaller borrow** | the borrow is `OnCtx` strengthening at one binder, no conversion statement — §3 |
| Q4(iii) | no `Skips`-on-subject `HasType` lemma | ✗ | `HasType.skips` exists (`Lemmas.lean`, cited :722) |

Priors wrong in *direction*: **Q2(i), Q2(ii), Q4(iii)** — three, the most of any round in this
handoff series, and the round's result came from the two questions whose answers surprised me
(Q1(b) and Q2(ii)), not from the bet.

---

## §4 The measured table

All in `Lean4Lean/Verify/Typing/SkipUninhab.lean`. `exists.lean`, population 494 built modules,
watching the 6 by-policy names. **26 declarations, 24 hole-free and watched-free**; the two that
are not are the two that deliberately pay the standing gate, and they are isolated there so the
taint is visible in one place.

| declaration | arity | cone | holes | watched |
|---|---|---|---|---|
| `VEnv.ProjSkipOne` | 2 | 142 | none (def) | none |
| `VEnv.ProjSkipOne.skipUninhab` | 3 | 147 | none | none |
| `VEnv.ProjSkipUninhab.projSkipOne` | 4 | 2349 | none | none |
| **`VEnv.projSkipUninhab_iff_projSkipOne`** | 3 | **2351** | **none** | **none** |
| `VEnv.LiftUninhabAt` | 4 | 37 | none (def) | none |
| `VEnv.ProjStrengthenUninhab` | 2 | 89 | none (def) | none |
| `VEnv.ProjStrengthen.uninhab` | 3 | 91 | none | none |
| `VEnv.ProjStrengthenUninhab.projStrengthen` | 4 | 2381 | none | none |
| **`VEnv.projStrengthenUninhab_iff`** | 3 | **2383** | **none** | **none** |
| **`TrProj.weak'_inv_of_strengthenUninhab`** | 14 | **3415** | **none** | **none** |
| `VEnv.ProjSkipUninhab.projStrengthenUninhab` | 4 | 2380 | none | none |
| `VEnv.OnCtxSkip1` | 2 | 34 | none (def) | none |
| `VEnv.Strengthening1Uninhab.onCtxSkip1` | 4 | 3247 | none | none |
| `VEnv.onCtxSkip1_of_wf` | 3 | 3488 | `weakN_iff`, `forallE_inv_stratified` | `IsDefEq.uniq`, `IsDefEq.uniqU` |
| `VEnv.ProjSkip1Uninhab` | 2 | 157 | none (def) | none |
| `VEnv.ProjStrengthen.skip1Uninhab` | 3 | 368 | none | none |
| `VEnv.ProjSkip1Uninhab.projStrengthen` | 5 | 2377 | none | none |
| `VEnv.ProjSkip1Uninhab.projStrengthen_of_strengthening` | 5 | 3426 | none | none |
| `VEnv.ProjSkip1Uninhab.projStrengthen_of_wf` | 4 | 3672 | the two above | the two above |
| **`VEnv.projSkip1Uninhab_iff`** | 4 | **2380** | **none** | **none** |
| **`TrProj.weak'_inv_of_skip1Uninhab`** | 15 | **3428** | **none** | **none** |
| `TrProj.weak'_inv_of_skip1Uninhab_wf` | 14 | 3674 | the two above | the two above |
| `VEnv.AllTypesInhabited.projSkip1Uninhab` | 3 | 302 | none | none |
| `projSkip1Uninhab_premises` | 7 | 236 | none | none |
| `hasType_bvar_ge_length_absurd` | 8 | 1667 | none | none |
| `onCtx_projSkipUninhab_fires_false` | 0 | 3257 | none | none |

**Axioms** (`#print axioms`, fully qualified): `projSkipUninhab_iff_projSkipOne`,
`projStrengthenUninhab_iff`, `projSkip1Uninhab_iff`, `ProjStrengthenUninhab.projStrengthen`,
`ProjSkip1Uninhab.projStrengthen`, `TrProj.weak'_inv_of_strengthenUninhab`,
`TrProj.weak'_inv_of_skip1Uninhab`, `onCtx_projSkipUninhab_fires_false` each depend on exactly
`[propext, Classical.choice, Quot.sound]`; `AllTypesInhabited.projSkip1Uninhab` on
`[propext, Quot.sound]`. No `sorryAx`, no extra axiom.

### §4.1 The price comparison that matters

Same conclusion throughout — **hole #1's exact statement** — from a residual restricted to the
uninhabited case. The new column is the one the earlier rounds did not have.

| route | residual vs. the hole | cone | holes | watched |
|---|---|---|---|---|
| `constAppTypeStrengthen_of_skipUninhab` ⨟ `weak'_inv_of_strengthen` | **stronger** | 3698 | 3 | 3 |
| `TrProj.weak'_inv_of_skipUninhab` (2026-09-04) | **stronger** (no `OnCtx Γ'`) | 3412 | 0 | 0 |
| **`weak'_inv_of_strengthenUninhab` (§2)** | **⟺ equivalent** | **3415** | **0** | **0** |
| **`weak'_inv_of_skip1Uninhab` (§3 route A)** | one binder + both `OnCtx`, modulo hole #2's residual | **3428** | **0** | **0** |
| `weak'_inv_of_skip1Uninhab_wf` (§3 route B) | one binder + both `OnCtx`, from the residual **alone** | 3674 | 2 | 2 |

Read the first three rows together: **3 constants** buy the difference between a residual that is
strictly stronger than what it proves and one that is *equivalent* to it. Row 5 is the one to
compare with row 1, because both discharge the hole outright at a `VEnv.WF` environment with no
extra hypothesis: **3674 against 3698, four by-policy names against six** —
`WF.rigidShapeUniqNS` and `HasArgs.of_mkApp` are gone, and the residual it starts from is *weaker*
than `ConstAppTypeStrengthen` rather than stronger.

### §4.2 The three results, in one line each

1. **`ProjSkipUninhab` ⟺ `ProjSkipOne`** at every `Ordered` environment: the words "may be
   assumed uninhabited" are, at one binder, provably worth nothing. Any proof of the residual must
   come from the contexts and the `TrProj` derivation alone.
2. **`ProjStrengthenUninhab` ⟺ `ProjStrengthen`** at every `Ordered` environment, hole-free both
   ways: the hole's own statement restricted to lifts with an uninhabited inserted binder, with
   `OnCtx Γ'` **retained**. This refutes `ProjInhab.lean` §3's closing claim that the one-binder
   form "cannot be repaired by adding `OnCtx Γ'` without re-importing the gate": the repair is to
   stop insisting on *one binder* — hand the residual the whole remaining lift and `OnCtx Γ'`
   never has to cross an uninhabited binder.
3. **`ProjSkip1Uninhab` + `OnCtxSkip1` ⟹ the hole**, and `OnCtxSkip1` comes either hole-free from
   `Strengthening1Uninhab` (hole #2's residual) or from `VEnv.WF` at the standing price of
   `OnCtx.weakN_inv`. So hole #1 and hole #2 are **ordered**, and the whole of the borrowing is
   *`OnCtx` descends across one binder* — a statement in which no conversion judgement appears.

---

## §5 Limits of this round's result, stated as required

1. **Nothing is discharged. The census does not move** — 13 before, 13 after, on both instruments
   [measured]. `ProjSkipUninhab` is **neither proved nor refuted**, and §4.2's three results
   change what should be carried rather than closing anything.
2. **Everything here is downstream of the hole.** This file imports `ProjDataAttack.lean` →
   `ProjExistClose.lean` → … → `Verify/Typing/Lemmas.lean`, so **none of it can discharge the
   `sorry` in place**. §2's and §3's statements use only `TrProj.instN` (already *in*
   `Lemmas.lean`, 1200 lines below the hole), `Ctx.InstN.wf`, `Ctx.LiftN.exists_instN_typed` and
   `Lift.depth_succ`, so the migration `docs/handoff-projdata.md` §3 describes would carry them
   verbatim; §3 route A additionally needs `Theory/Typing/Strengthen.lean`, and route B needs
   `Theory/Typing/UniqueTyping.lean`, both of which are upstream of `Lemmas.lean`. I did **not**
   verify intra-module ordering inside `Lemmas.lean` for these; that check is
   `CONE_IN=SELF` on `scripts/exists.lean` and I did not run it.
3. **The repair costs known non-vacuity, and this is proved rather than conceded.**
   `ProjSkipUninhab` is known non-vacuous (`projSkipUninhab_fires`). §2's and §3's residuals are
   of **unknown** vacuity, because their `OnCtx Γ'` premise excludes that very witness —
   `onCtx_projSkipUninhab_fires_false` proves `¬ OnCtx (VExpr.bvar 1 :: prjCtx) (prjEnv.IsType 0)`,
   hole-free. Their premises are satisfiable exactly at a well-formed context with an uninhabited
   entry (`projSkip1Uninhab_premises`), which by `ProjInhab.lean` §1's iff is `env.Consistent`,
   proved nowhere in this tree. And `VEnv.AllTypesInhabited.projSkip1Uninhab` proves the dual: they
   are outright vacuous wherever no type is uninhabited. So they are vacuous **iff** the hole is
   already closed by `ProjDataAttack.lean` §2 — the same position `Strengthening1Uninhab` is in,
   and the strongest honest non-vacuity statement available.
4. **§3 is not unconditional.** `ProjSkip1Uninhab` alone does not give the hole hole-free; it needs
   `OnCtxSkip1`. I did not prove `OnCtxSkip1` and I do not believe it is provable without the gate:
   the only in-tree producers are `OnCtx.weakN_inv` (2 holes, 2 watched) and
   `TypingStrengthening.onCtx_weakN_inv`. What §3 establishes is the *size* of that debt, not its
   discharge.
5. **`ProjSkipUninhab`'s truth value is left open, and I claim only that a refutation is not
   cheap.** The argument (§2 Q2(i)) is that the only extra typing resource a `Γ'` with an
   uninhabited entry `A₀` has is `.bvar k : A₀`, and the `TrProj` premise's subject is a lift, so
   it can never be that term; new *conversions* upstairs would have to come from `bvar` or
   `proofIrrel`, the only two context-sensitive `IsDefEq` rules, and `StrengthenVerdict.lean` §5
   has already killed the `proofIrrel` attack at its own witness. **That is an argument about where
   a counterexample would have to come from, not a proof that none exists** — the same kind of
   claim `docs/handoff-projdata.md` §6 correctly flagged as not a result.
6. **Monotonicity is analysis, not measurement.** §2 Q2(iv) reasons that `ProjSkipUninhab` is
   neither monotone nor antitone in `env`; I did not prove it, because §2 made it moot.
7. **No Kernel Arena run.** No executable code was touched — one new proof-side leaf module — so
   the Arena gate is not engaged and was not run.

---

## §6 Method gaps in this round

* **My cheapest instrument was the wrong one, and the right one was rule 3's second search.** I
  spent the first third of the round on Q2's quantifier extremes hunting a counterexample, which is
  what rule 2 prescribes. What actually produced all three results was the *hypothesis-shape*
  search — tabulating which members of the one-uninhabited-binder family carry `OnCtx` (Q1(b)) —
  and that table took one grep. Rule 2's "cheapest instrument first" and rule 3's three searches
  compete for the first slot, and in a corner with six sibling statements the **family table**
  should come first, because it prices every route before you pick one.
* **`scripts/exists.lean` and `scripts/sorry-census.lean` disagree about population, silently.**
  `sorry-census.lean` imports a fixed pair of roots, so a hole in a leaf module like this one would
  be **invisible to it**; only `sorry-census-all.lean` reaches the 60 orphan modules. Both report
  13 here, so nothing was hidden this round, but a stream that reports "census unchanged" from
  `sorry-census.lean` alone after adding an orphan module has measured nothing. Rule 8 should name
  `sorry-census-all.lean`.
* **`lake build` does not re-run the guards.** They are `#eval`s in a cached module that a leaf
  addition cannot invalidate, so "bare build green" carries no guard information at all. I re-ran
  `lake env lean Lean4Lean/Verify/Guard.lean` explicitly; rule 8's "report guards" needs that extra
  command spelled out or it will be reported from cache.
* **Dot notation on a `def … : Prop` fails and the error names `Function`.** Two of my three
  compile errors were `H.foo` where `H`'s type is a `Prop`-valued `def` that unfolds to a `∀`;
  Lean reports "the environment does not contain `Function.foo`", which reads like a missing lemma
  rather than a notation problem. Every statement in this family is such a `def`. Worth knowing
  before the next round loses ten minutes to it.
* **I did not run `lean_minimal_hypotheses` on the two headline reductions**, so "`hS` /`hO` is
  load-bearing" is an argument (nothing else in the tree produces `OnCtx Γ₂` after an uninhabited
  step) rather than a measurement. The tool rejected the fully-qualified and the bare name on this
  file and I did not chase it.

### §6 correction (2026-09-05, same day, appended not edited)

The last bullet above is superseded: `lean_minimal_hypotheses` **was** run, after §6 was written,
once I found the name form it accepts. It takes the *trailing segment* of a source-level
declaration name, so `VEnv.ProjSkip1Uninhab.projStrengthen` is unreachable (the source name has a
dotted prefix that is part of the identifier, and several declarations share the trailing
`projStrengthen`) — the auxiliaries are reachable and are what carry the induction:

* `projStrengthen_of_strengthenUninhab_aux` — both explicit binders **load-bearing**
  (`henv : env.Ordered`, `hres : env.ProjStrengthenUninhab U`).
* `projStrengthen_of_skip1Uninhab_aux` — all three explicit binders **load-bearing**
  (`henv`, `hO : env.OnCtxSkip1 U`, `hres : env.ProjSkip1Uninhab U`).

So §5.4's claim is now measured rather than argued: §3 genuinely needs `OnCtxSkip1`, and §2
genuinely needs nothing beyond `Ordered` and its own residual. The tool's own caveat applies — it
reports "load-bearing" whenever the proof body names the binder, which is the truthful answer for a
hand-written induction but is not a proof that no other proof could avoid it.

The *real* remaining gap in this round's method is the one the tool exposed rather than closed:
**this repo's statements are all `Prop`-valued `def`s with dotted names, and two standard
instruments (`lean_minimal_hypotheses`'s name matching, and dot-notation on a hypothesis) both
mis-handle exactly that shape.** Both failures cost time this round and both will recur.

---

## §7 One correction to my own §4.2, made before reporting (2026-09-05)

§4.2 item 2 above said §2 "refutes `ProjInhab.lean` §3's closing claim". **That overclaims, and the
Lean file has been corrected; this entry records the correction rather than editing §4.2.**

`ProjInhab.lean` §3's claim is literally: the *one-binder* form "cannot be repaired by adding
`OnCtx Γ'` without re-importing the gate". Read literally it is **true, and this round confirms it
by measuring the price**: §3 route B is exactly that repair and exactly that re-import
(`weak'_inv_of_skip1Uninhab_wf`, 3674, holes `{weakN_iff, forallE_inv_stratified}`, watched
`{uniq, uniqU}`). What §2 refutes is the *broader reading* that has been travelling with it — that
the localisation of hole #1 to the uninhabited case cannot keep `OnCtx Γ'` at all. It can, and the
move is to give up "one binder" rather than to give up `OnCtx Γ'`. Two distinct trade-offs, both
now priced:

| residual | one binder? | `OnCtx Γ'`? | `OnCtx Γ`? | relation to hole #1 | extra debt |
|---|---|---|---|---|---|
| `ProjSkipUninhab` (2026-09-04) | yes | **no** | no | **⟸ only** (strictly stronger) | none |
| `ProjStrengthenUninhab` (§2) | **no** | yes | no | **⟺** | none |
| `ProjSkip1Uninhab` (§3) | yes | yes | yes | **⟸**, and ⟹ given `OnCtxSkip1` | `OnCtxSkip1` |

The row a future round should carry is the middle one if it wants a residual it cannot waste effort
on (it is true iff the hole is), and the bottom one if it wants the smallest statement to actually
attack (one binder, both contexts well formed) and is willing to owe `OnCtx` strengthening — which
hole #2 must pay for anyway.
