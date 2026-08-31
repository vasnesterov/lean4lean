# `kernel_sound`'s critical path

*Measured 2026-08-31. Reproduce with `~/.elan/bin/lake env lean scripts/kernel-sound-path.lean`.*

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

Holes, all nine of which enter through `Bridge.addDeclWF`:

| Hole | Census transitive users |
|---|---|
| `addDecl.WF` | 1 |
| `TypeChecker.Inner.inferProj.WF` | 0 |
| `TypeChecker.Inner.isDefEqUnitLike.WF` | 1 |
| `TypeChecker.Inner.tryEtaStructCore.WF` | 2 |
| `TrProj.weak'_inv` | 29 |
| `TrProj.uniq` | 93 |
| `VEnv.IsDefEqU.weakN_iff` | 134 |
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

**This remains the human's decision and I am not taking it.** Two prerequisites from §7 are
independent of it and can proceed now: §7.1 (`addQuot.WF`'s `AddQuot` construction — explicitly
orthogonal to `AddInduct`, and the only thing between the checker and a non-vacuous
`addQuot.WF`), and §7.3 (`addDecl.WF`'s `inductDecl` branch, which must show the map the
executable `addInductive` produces *is* the map `AddInductStages` builds).
