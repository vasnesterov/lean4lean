# `kernel_sound`'s critical path

*Measured 2026-08-31. Reproduce with `~/.elan/bin/lake env lean scripts/kernel-sound-path.lean`.*

## Stop-condition status

| Condition | State |
|---|---|
| **1.** Kernel Arena: `uv run lka.py run --checker lean4lean-local`, every non-`either` test correct | **MET** — measured 2026-08-31 at commit `43d6d25`: **185 correct, 6 `either`, nothing incorrect** |
| **2.** `Lean4Lean.kernel_sound` proven (Guard 2 prints "proof COMPLETE") | **NOT met** — 2 hypotheses + 9 holes, enumerated below |

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
