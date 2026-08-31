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
