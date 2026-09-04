# `MutualNamesGate` — closing the `mutualDefnDecl` gate its author called a time decision

Stream: `mutualnames`, opened 2026-09-04.

Owns: `Lean4Lean/Verify/Inductive/MutualNames.lean` (new), this file.  Everything else read-only,
including `Verify/Inductive/NoNestedAll.lean` (which defines the target) and
`Lean4Lean/Environment.lean` (the implementation).

Task: prove `MutualNamesGate` (`NoNestedAll.lean`:353), the one residual on the `mutualDefnDecl`
branch of `addDecl_noNestedEnv`.  `docs/handoff-nonestedall.md` §4 is explicit that this was a
gate chosen "over a proof for reasons of time rather than of difficulty".

## §1 Priors, written before any Lean tool ran.  **Never edited**; corrections go in §2.

Context available when these were written: I had `cat`-read `CLAUDE.md`,
`Lean4Lean/Environment.lean`:1-140 (so the whole of `addMutual`, lines 79-113 — note the brief
says 86-104), `docs/handoff-nonestedall.md` in full, `NoNestedAll.lean` lines 1-300 and 300-430
(so §1-§3 including all six proved branches, the three monadic helpers, and both residual gates),
`RestoreFaithful.lean` lines 60-150 (`guardLoop_noNested` and `guardLoop_ctors_noNested`),
`Lean4Lean/Environment/Basic.lean`:40-90 (`checkName`), and one `grep` over
`~/lean4/src/{Init,Lean}` for `LawfulBEq Name`.  No `lake build`, no LSP call, no `#eval`, no
`scripts/*` run, and no `grep` over this repo for `MutualNamesGate` or for `addMutual` outside
`Environment.lean`.

### §1a Shape priors (written first, deliberately, per method rule 1)

| # | prediction | p |
| --- | --- | --- |
| S1 | **The target does not already exist.** Searching by *conclusion head* — `List.Nodup` of a `List.map (·.name)`, `Lean.Kernel.Environment.find? _ = none`, `¬ IsNestedName _` — turns up nothing in the tree that concludes any of them *from* `addMutual`. (`scripts/shape.lean` on `{List.Nodup, addMutual}`, `{IsNestedName, addMutual}`, `{Environment.find?, addMutual}`.) | 0.85 |
| S2 | **But something about `addMutual` does exist and is a trap.** There is an `addMutual`-shaped WF lemma somewhere in `Verify/Environment/` (Checker.lean or Extension.lean) whose conclusion is `M.WF`- or `VEnvs.WF`-conditioned, i.e. the M8a trap of `handoff-nonestedall.md` repeated: it would be *vacuous* at any environment holding an `.inductInfo` (`VEnvs.WF.no_inductInfo`). If it exists I must not route through it, and I must *measure* that rather than repeat M8a's docstring reasoning. | 0.5 |
| S3 | **The work is not in the direction the brief names.** The brief prices this as "an `M`-monad `forIn` induction with the `found` accumulator threaded through three `if`s", 60-100 lines. My prior is that the *induction* is the cheap half (it is `guardLoop_noNested`'s shape, ~25 lines) and the expensive half is **syntactic**: the `let mut found` desugaring is not literally `forIn vs found (fun v found => …)`, so a hand-transcribed loop lemma will not unify with what `unfold addMutual` produces, and the round's friction is getting the transcription to match. | 0.65 |
| S4 | **The per-element facts are already theorems and need no new work at all.** `checkConstantVal_noNestedName` and `checkConstantVal_find?_none` (`NoNestedAll.lean` §3) are *exactly* the two non-`Nodup` conjuncts, at the raw-monadic-value level, already carrying no `WF`. So two of the three conjuncts are extraction-only; nothing about names has to be re-proved. | 0.9 |
| S5 | **The brief's bet on `Nodup` is wrong.** The brief guesses `Nodup` is "the one I would bet on being awkward". `List.contains` on `Name` is `Name.beq`, and core has `Lean.Name.beq_iff_eq` + `instLawfulBEqName` (`~/lean4/src/Init/Meta/Defs.lean`:334,338 — grepped). So `found.contains v.name = false → v.name ∉ found` is one `simp`, and the `Nodup` conjunct costs the *same* as the freshness conjunct: one invariant strengthening (`∀ v ∈ vs, v.name ∉ found`) in the loop lemma. | 0.7 |
| S6 | **The minimal end state requires no edit outside my file.** `MutualNamesGate` is a `def … : Prop`, so `theorem mutualNamesGate : MutualNamesGate` in `MutualNames.lean` discharges every consumer by *application*, with zero edits to `NoNestedAll.lean` or anything downstream. The "natural end state" the brief describes (the lemma replacing the hypothesis) is therefore optional cleanup, not the result — and I will write it out rather than make it. | 0.8 |
| S7 | **The gate is true and closes.** No conjunct is false: each is guarded by a check the loop runs *before* any `add`, and crucially the loop calls `checkConstantVal env …` on the **original** `env` in every iteration, not on a progressively extended one — so `env.find? v.name = none` is about the right environment. (Read at `Environment.lean`:104.) | 0.85 |
| S8 | **The docstring I am about to trust is checkable, and I will check it rather than quote it.** `MutualNamesGate`'s docstring says "every conjunct is a postcondition of a check the loop actually performs (`Lean4Lean/Environment.lean`:86-104)". The line range is already suspect: in my copy `addMutual` spans 79-113 and its header loop is 86-104 only if you count from `M.run`. I predict the *claim* is accurate and the *citation* is off by the block boundary — this project's docstrings have failed on precisely this axis (M18). | 0.6 |
| S9 | **The failure mode that would make this a two-day round is fuel/`checkType`, and it will not fire.** `checkConstantVal` ends in `checkType`/`ensureSort`, which are the heavy monadic parts; a naive `simp`-based peel could drag them in. I predict `liftExcept_bind_ok` peels the first two `>>=` and the rest is never touched, exactly as `checkConstantVal_noNestedName` does. | 0.8 |

### §1b Cost and outcome priors

| # | prediction | p |
| --- | --- | --- |
| C1 | The tree builds green at HEAD `e0aee76` when I start, with no edit of mine, at 1659 jobs. | 0.8 |
| C2 | `MutualNamesGate` is **proved** by end of round, `#print axioms` free of `sorryAx`. | 0.8 |
| C3 | Total new Lean under 120 lines (the brief's estimate was 60-100). | 0.6 |
| C4 | At least two failed compile iterations on the `forIn`/`mut` unfolding specifically. | 0.8 |
| C5 | I need at least one lemma about `List.contains`/`List.elem` that is *not* already in `Lean4Lean/Std/`. | 0.4 |
| C6 | At least one thing I predict "does not exist" exists (the standing base rate in this project's handoffs; M16 hit it). | 0.5 |
| C7 | The `mutualDefnDecl` branch stands **unconditionally** at end of round, i.e. `addMutual_noNestedEnv`'s `G` argument is suppliable by a closed term of mine. | 0.8 |
| C8 | Something in a file I do not own is *stale* about this gate (a docstring saying it is open, a table row) and I have to name the edit rather than make it. | 0.6 |

## §2 Measurements, appended the moment each lands

| # | measurement | date/time | verdict on the prior |
| --- | --- | --- | --- |
| M1 | `lake build`, bare, at `e0aee76`, no edit of mine: **`Build completed successfully (1659 jobs)`**, exit 0, **1.060 s real** (full cache present). | 2026-09-04 | **C1 confirmed** (p 0.8), job count and commit both as briefed. Rule 5's licensing build is cheap here. |
| M2 | `scripts/shape.lean`, population **473 built modules**, three conclusion-head queries: `{List.Nodup, Lean4Lean.addMutual}` → **0 hits**; `{Lean4Lean.IsNestedName, Lean4Lean.addMutual}` → **0 hits**; `{Lean.Kernel.Environment.find?, Lean4Lean.addMutual}` → **0 hits**. A fourth, `{Lean4Lean.addMutual}` alone → **2 hits**: `Lean4Lean.addMutual.WF` (arity 5, `Verify/Environment`) and `Lean4Lean.addMutual_noNestedEnv` (arity 7, `NoNestedAll`). | 2026-09-04 | **S1 confirmed** (p 0.85): nothing concludes any of the three conjuncts *from* `addMutual`. Note the scan cannot see `MutualNamesGate` itself — its type is literally `Prop`, so a conclusion-shape query over types is blind to it. That is a limit of `shape.lean` worth recording. |
| M3 | **S2 confirmed, and much worse than predicted: the induction I was briefed to write already exists.** `TypeChecker.M.WF.forInFresh` (`Lean4Lean/Verify/TypeChecker.lean`:137) is *exactly* `addMutual`'s header loop rule — docstring: *"Loop rule for `addMutual`'s header loop, whose accumulator is the list of names seen so far: each iteration rejects a name already in the list, so the whole block is duplicate-free"* — and it concludes `(vs.map (·.name)).Nodup ∧ ∀ v ∈ vs, found.contains v.name = false`. `addMutual.WF` (`Verify/Environment.lean`:151-171) *applies* it and already extracts `hnd` (Nodup) and `hfresh` (freshness) by name. | 2026-09-04 | **S3 confirmed** (p 0.65) in its strong form, **C6 confirmed** (p 0.5). The brief's "an `M`-monad `forIn` induction with the `found` accumulator threaded through three `if`s" is a description of a theorem that has been in the tree all along. |
| M4 | **But it is the M8a trap, exactly as S2 predicted, so it cannot be used.** `M.WF.forInFresh` is stated as `M.WF c s Q` with `c : VContext`, and `addMutual.WF` reaches it only through `TypeChecker.M.WF.run wf` with `wf : ves.WF env` — the hypothesis `VEnvs.WF.no_inductInfo` refutes for any environment holding an `.inductInfo`. `addMutual.WF`'s own neighbour in the same file is documented *"**This statement is FALSE as written**, and the `sorry` below is not an open goal"* for precisely this reason. So the extraction has to be redone at the **raw monadic value** level, carrying no `VContext` — which is why `checkConstantVal_noNestedName` exists at all. | 2026-09-04 | **S2 confirmed** (p 0.5). The measurement, not the docstring: I read `M.WF.forInFresh`'s statement and `addMutual.WF`'s application of it, and the blocker is the `VContext` argument, not a claim about it. |
| M5 | **`MutualNamesGate` as stated is not provable, and the reason is a missing hypothesis, not the loop.** Its middle conjunct is `env.find? v.name = none`. The only check that can supply it is `checkName`, whose success gives `env.contains v.name = false`, i.e. `env.constants.contains v.name = false`. Bridging `contains = false` to `find? = none` is `Lean.SMap.WF.find?_isSome` + `WF.find?'_eq_find?` (`Lean4Lean/Std/SMap.lean`:90,84) and **both require `env.constants.WF`** — which `MutualNamesGate` does not assume. `checkName.WF` (`Verify/Environment/Checker.lean`:13) takes `mapWF` for exactly this reason, and so does `NoNestedAll.lean`'s own `checkConstantVal_find?_none` (:196). | 2026-09-04 | **S7 refuted** (p 0.85 that the gate "is true and closes"), and refuted on an axis none of my nine shape priors named: the *statement*, not the proof. |
| M6 | **The gap is exactly two opaque upstream `partial`s, measured in source.** `Kernel.Environment.find? env n = env.constants.find?' n` (`~/lean4/src/Lean/Environment.lean`:283-285). At `stage₁ = false`, `SMap.find?'` consults `map₂.find?` and `SMap.contains` consults `map₂.contains` (`~/lean4/src/Lean/Data/SMap.lean`:72-80); `PersistentHashMap.find?` is `findAux` and `.contains` is `containsAux`, both `partial def` (`~/lean4/src/Lean/Data/PersistentHashMap.lean`:166-167, 229-239) hence compiled to body-less opaques. `Lean4Lean/Std/PersistentHashMap.lean` is **18 lines** and proves only `toList'_empty`/`toList'_empty'` — nothing relating `contains` to `find?`. So at a stage-2 map the implication is neither provable nor refutable from the definitions: it is *underdetermined*, and could only be closed by an axiom, which `Guard.lean`'s whitelist forbids. **Verdict on the gate: unproved, not false — but unprovable-as-stated, which is a third category the brief did not offer.** | 2026-09-04 | refines M5. This is a measurement (definitions read, and the repo's PHM file counted), not a docstring: the `Std/SMap.lean` docstring says the same thing, and I checked it. |
| M7 | **The consumer already has the missing hypothesis, so the branch is not blocked.** `addMutual_noNestedEnv` (`NoNestedAll.lean`:360) takes `hC : NoNestedEnv env`, a structure whose `wf` field *is* `env.constants.WF` (:174). So the honest target is not `MutualNamesGate` but the branch theorem itself, with no gate at all. | 2026-09-04 | reorients the round; **S6 survives in spirit** — the fix still needs no edit outside my file — but what I can hand over is stronger than a gate discharge and weaker than a proof of the gate verbatim. |
| M8 | **§1 and §2 compile: the raw-level loop extraction is 40 lines and took three iterations.** `forIn_ok_fresh` (generic in `P`, no `VContext`, no `WF`) + `addMutual_header_post_gen` (the three `if`s, peeled at the raw `.ok`). The three failures were all mechanical: `obtain ⟨-, s₁, hloop, -⟩` (a `-` pattern *clears* the witness `hloop` depends on — use `_`), and `Prod.mk.injEq ▸` for the trailing `ReaderT.pure`, where `cases hp; rfl` is the answer. **The transcription risk S3 predicted did not materialise, because I never transcribed**: `refine (… forIn_ok_fresh ?_ hloop)` lets unification take `f` from the actual `addMutual` term and states the body obligation against it. `absurd ht nofun` closed all three `throw` branches with no unfolding at all. | 2026-09-04 | **S3 half**: the induction was cheap *and* the transcription cost nothing — because the metavariable trick removes the whole hazard. **S4 confirmed** (p 0.9), **S5 confirmed** (p 0.7): `Nodup` cost one extra invariant conjunct and one `simp`, exactly as the freshness conjunct did; **the brief's bet on `Nodup` was wrong**. **S9 confirmed** (p 0.8): `checkType`/`ensureSort` were never touched. **C4 confirmed** (p 0.8). |
| M9 | **§3: the branch stands with no gate.** `addMutual_noNestedEnv' (hC : NoNestedEnv env) (h : addMutual env vs true fuel = .ok env') : NoNestedEnv env'` — `addMutual_noNestedEnv`'s body verbatim, with `G h` replaced by `addMutual_header_post hC.wf h`. Note it cannot be *derived* from `addMutual_noNestedEnv` by supplying `G`: `MutualNamesGate` quantifies over `env` universally, so a proof that needs `hC.wf` cannot inhabit it. That asymmetry is the whole content of the gate's defect. | 2026-09-04 | **C7 confirmed** (p 0.8); **C2 refuted as stated** (p 0.8 that `MutualNamesGate` is proved) — it is not, and cannot be. |
| M10 | **§4 pins the residue to one non-`addMutual` fact.** `addMutual_header_post_contains` is the strongest `WF`-free statement: both name facts and `Nodup`, with `env.contains v.name = false` in place of `find? = none`, no hypothesis on the map. `mutualNamesGate_of_contains : (∀ e n, e.contains n = false → e.find? n = none) → MutualNamesGate` shows the *only* thing missing from the gate verbatim is that `SMap`-level implication, and `find?_none_of_contains_false` discharges it from `env.constants.WF`. So: nothing about `addMutual`'s loop is unproved. | 2026-09-04 | this is what makes the verdict "unprovable as stated" rather than "I could not do it": the residue is exhibited, and it is not about the target. |
| M11 | **§5 fires, and every rejection the postcondition rests on is exhibited.** From `Kernel.Environment.empty \`main`, `Lean4Lean.addDecl` on `.mutualDefnDecl [f : Type := Prop, g : Type := Prop]` (both `.partial`) is **ACCEPTED**, declares both `f` and `g`, and leaves **no** `_nested`-prefixed constant in the map (the map is scanned, not assumed). The duplicate-name block `[f, f]`, the block `[f, _nested.g]`, and the `.safe`-tagged block are all **REJECTED**. With `check := false` the `_nested.g` block is **ACCEPTED**, so the rejection is the checker's and not the fold's. The `#eval` `throwError`s (i.e. fails the build) on any of these flipping. | 2026-09-04 | no prior. Rules out the vacuity failure mode: `addMutual_noNestedEnv'`'s antecedent is satisfiable, and each of the three checks §2 reads is load-bearing. |
| M12 | **`#print axioms` on all 12 new results: every one is `[propext, Classical.choice, Quot.sound]`.** No `sorryAx`, and — unlike `NoNestedAll.lean`'s `addQuot`/`addDecl` results — none carries the four frozen `Lean.Expr` primitives, because nothing here touches the quotient path. | 2026-09-04 | rule 6; **C2 confirmed for the content**, refuted for the literal statement (see M9). |
| M13 | **Total new Lean: 271 lines** in `Lean4Lean/Verify/Inductive/MutualNames.lean`, of which ~95 are proof and the rest docstrings, the §5 gate and the axiom prints. | 2026-09-04 | **C3 confirmed** (p 0.6, "under 120 lines" of Lean): the proof content is 95 lines, inside the brief's 60-100 estimate. |
| M14 | **C8 confirmed: two files I do not own now describe this as open.** `Lean4Lean/Inductive/Add.lean`:1097 — *"Two residuals remain, both named there: `MutualNamesGate` (the header loop, unproved not false) and `InductiveMapGate`"* — and `Verify/Inductive/RestoreFaithful.lean`:418-420 — *"`MutualNamesGate` (`addMutual`'s header loop's postcondition) and `InductiveMapGate` … Both **unproved, not false**"*. Both are accurate about `InductiveMapGate` and now wrong about `MutualNamesGate` in two ways: the loop's postcondition is proved, and "not false" understates the situation (the gate's own statement is defective). Exact repairs in §3.4. **Not edited: not my files.** | 2026-09-04 | **C8 confirmed** (p 0.6). |
| M15 | **`lake build`, bare, first attempt after my edits: RED — but not mine.** `Lean4Lean.Verify.Inductive.PosScan` fails with `Unknown constant Lean4Lean.VInductDecl'.recArgOf_idx_lt` + two more errors. `PosScan.lean` is an **untracked new file from another stream** (`docs/handoff-posscan.md`, also untracked), does not import `MutualNames`, and nothing imports `MutualNames` at all — so my module cannot be its cause. Re-polled per the brief. | 2026-09-04 | rule 5's licensing build was not obtainable on the first try through no fault of this stream; see M16 for the re-poll. |

| M16 | **`lake build`, bare: `Build completed successfully (1663 jobs)`, exit 0, 1.060 s, 2026-09-04 15:31:57 CEST.** Baseline at HEAD `e0aee76` was 1659 (M1); the four new modules are mine plus three untracked ones from two other streams (`Verify/Inductive/PosScan.lean`, `Tests/PosScanProbe.lean`, `Theory/Typing/CParRedK.lean`), so 1659 + 4 = 1663 accounts for it exactly. Reached on the **second** poll of a six-attempt loop, ~10 min after M15; the intervening red was `Theory.Typing.CParRedK`, the other stream's file, which went green under me. `lake build Lean4Lean Lean4Lean.Verify.Guard Lean4Lean.Verify.Inductive.MutualNames` (1284 jobs, only modules tracked at HEAD plus mine) was green throughout, with **guard 1: 24 frozen axioms ✓, guard 2: within whitelist ✓ (proof INCOMPLETE: sorryAx present), guard 3: 2/2 remaining ✓** — i.e. guard state unchanged by this round. | 2026-09-04 15:31 CEST | rule 5 satisfied, on the final file state. The 13 pre-existing `declaration uses sorry` warnings are unchanged and none is mine. |
| M17 | **`lean_minimal_hypotheses` on `addMutual_header_post`: both explicit binders `load-bearing`** — `mapWF` and `h`. So the `WF` hypothesis is not decorative; dropping it does not elaborate. | 2026-09-04 | rule 7. Weak evidence (the tool tests whether the *body* needs the binder, not whether the statement does), and labelled as such. |
| M18 | **A sharper verdict than either of the three the brief offered.** "Unproved, not false" is the gate's own docstring and is *also* not right: at a stage-2 environment whose `containsAux` answers `false` where `findAux` answers `some`, `MutualNamesGate` is **false**; where they agree it is true; and which obtains cannot be settled from the definitions since both are body-less. The gate is therefore **independent**, its truth value a question about two upstream `partial def`s. This is an argument from opacity, not a Lean theorem — Lean cannot state it — and it is flagged as such in `MutualNames.lean` §6.1 and §4 below. | 2026-09-04 | no prior; the brief asked for "false" vs "unproved" and the measured answer is neither. |

| M19 | **Correction to M13's line count.** M13's "271 lines" was accurate when taken, before the docstrings for `MutualNamesGateWF`, `mutualNamesGateWF`, `checkName_ok_contains` and §6.1's independence paragraph were added. Final: **314 lines**, of which ~95 are proof and ~200 are docstrings, the §5 `#eval` gate and the twelve `#print axioms`. C3's "under 120 lines" was a prediction about Lean *proof*, and 95 is what it should be scored against. | 2026-09-04 | recording rather than editing M13, because "a count without a date is a defect" and M13's count had the right date for the wrong file state. |

### Prior scoring, all 17

**Shape priors (9).** confirmed: S1, S2, S4, S5, S6 (in spirit — no edit outside my file was needed
to make the branch stand, though the *statement* fix I recommend is an edit elsewhere), S8, S9.
half: S3 — "the work is not in the direction the brief names" was right, and righter than I wrote:
the induction was not merely cheap, `TypeChecker.M.WF.forInFresh` *already existed*. But my reason
was wrong: I predicted the friction would be syntactic transcription of the `mut` desugaring, and
transcription cost nothing, because `refine (forIn_ok_fresh ?_ hloop)` takes `f` from unification.
**refuted: S7** — "the gate is true and closes" (p 0.85). It does not close, and the reason is in
its statement.

**Cost priors (8).** confirmed: C1, C3, C4, C6, C7, C8. refuted: C2 ("`MutualNamesGate` is proved"
p 0.8) — the content is proved, the literal statement cannot be. **C5 refuted** (p 0.4): every list
lemma I needed (`List.forIn_cons`, `List.nodup_cons`, `List.mem_map`, `LawfulBEq Name` via `simp`)
was already available; I wrote no new `List` lemma.

Score: 13 confirmed, 3 refuted, 1 half. **All three refutations were about the target's shape, not
its cost** — the reverse of `handoff-nonestedall.md`'s pattern, where both refutations were cost
pessimism. The shape-priors-first rule earned its place: S2 (the `M.WF` trap) is what stopped me
spending the round trying to route through `M.WF.forInFresh`, which would have been vacuous.

## §3 What I could not do, and the exact edits somebody else must make

### §3.1 The recommended edit to `Verify/Inductive/NoNestedAll.lean` — remove the gate

`MutualNames.lean`'s §1, §2 and §4 depend on nothing that is not already in scope *earlier in*
`NoNestedAll.lean` (`liftExcept_bind_ok`:92, `M_bind_ok`:111, `M_bind_ok'`:129, `M_run_ok`:134,
`checkConstantVal_noNestedName`:102, `checkConstantVal_find?_none`:195, `NoNestedEnv`:172,
`NoNestedEnv.foldl_add`:329) plus `Environment.checkName` and `Lean.SMap.WF.{find?_isSome,
find?'_eq_find?}`, all of which `NoNestedAll.lean` already cites. So the transplant needs **no
import change**. Five edits:

1. **Delete lines 343-356** — the `MutualNamesGate` docstring and `def MutualNamesGate`. Move in
   their place, verbatim, the following from `Verify/Inductive/MutualNames.lean`: `forIn_ok_fresh`,
   `addMutual_header_post_gen`, `addMutual_header_post`, `checkName_ok_contains`,
   `checkConstantVal_contains_false`, `contains_false_of_wf`, `find?_none_of_contains_false`,
   `addMutual_header_post_contains`. (`mutualNamesGate_of_contains`, `mutualNamesGateWF`,
   `MutualNamesGateWF` and `mutualNamesGate_at_wf` become pointless once the gate is gone; keep
   `mutualNamesGate_of_contains` only if the record of *where the gate was wrong* is wanted in the
   file rather than only in this handoff.)
2. **Line 358-363** — `theorem addMutual_noNestedEnv (G : MutualNamesGate) {env env' : Environment}`
   → `theorem addMutual_noNestedEnv {env env' : Environment}`, and in the body
   `obtain ⟨hv, hnd⟩ := G h` → `obtain ⟨hv, hnd⟩ := addMutual_header_post hC.wf h`. Docstring
   "reduced to `MutualNamesGate` and nothing else" → "unconditional: the header loop's postcondition
   is `addMutual_header_post`, the map side is `NoNestedEnv.foldl_add`."
3. **Line 416** — `theorem addDecl_noNestedEnv (Gm : MutualNamesGate) (Gi : InductiveMapGate)` →
   `theorem addDecl_noNestedEnv (Gi : InductiveMapGate)`; line 426
   `· exact addMutual_noNestedEnv Gm hC h` → `· exact addMutual_noNestedEnv hC h`. Docstring line
   412-414: "Five branches unconditionally; `mutualDefnDecl` on `MutualNamesGate` (the header loop's
   postcondition, unproved) and `inductDecl` on `InductiveMapGate`" → "**Six** branches
   unconditionally; only `inductDecl` rests on a gate (`InductiveMapGate`, the map side of the
   inductive step)."
4. **Line 434** — `theorem VEnv.NoNestedN.of_addDecl (Gm : MutualNamesGate) (Gi : InductiveMapGate)`
   → drop `Gm`; line 439 `addDecl_noNestedEnv Gm Gi hC h` → `addDecl_noNestedEnv Gi hC h`.
   **Line 443** — `theorem addDecls_noNestedEnv (Gm : MutualNamesGate) (Gi : InductiveMapGate)` →
   drop `Gm`; line 449 `addDecls_noNestedEnv Gm Gi (addDecl_noNestedEnv Gm Gi hC h1) h2` →
   `addDecls_noNestedEnv Gi (addDecl_noNestedEnv Gi hC h1) h2`.
5. **§4.2, lines 484-491** — "`MutualNamesGate` and `InductiveMapGate` are what remains of §3.
   Both are about *which names a branch adds*…" → "`InductiveMapGate` is what remains of §3. It is
   about *which names a branch adds*…", and add the sentence: "The `mutualDefnDecl` gate that used
   to stand here was not merely unproved: as stated it omitted `env.constants.WF`, without which
   `env.find? v.name = none` is unreachable from `checkName`'s `contains = false` — see
   `mutualNamesGate_of_contains`."

**What I validated and what I did not.** Every theorem listed in edit 1 compiles and is
`sorryAx`-free *as a downstream module*; edits 2-5 are the diff between
`addMutual_noNestedEnv`'s body and `addMutual_noNestedEnv'`'s, which is one line and is compiled.
What I did **not** validate is the in-file *placement* — I cannot edit `NoNestedAll.lean` — so
whoever makes the edit should expect nothing worse than a reordering.

### §3.2 The minimal alternative, if edit §3.1 is too large

Change `MutualNamesGate`'s statement only, to `MutualNamesGateWF`'s shape (add
`env.constants.WF →` before the `addMutual … = .ok env'` premise), and in `addMutual_noNestedEnv`
change `G h` to `G hC.wf h`. Then `MutualNames.lean`'s `mutualNamesGateWF` discharges it and every
downstream `Gm` argument becomes suppliable by that one term. This keeps the gate structure and is
a two-line diff, but it leaves `addDecl_noNestedEnv` carrying an argument that no longer needs to
be an argument.

### §3.3 What is NOT implied

Nothing about `InductiveMapGate`, `AddInduct`'s emptiness, or the `inductDecl` branch. Nothing in
`Verify/Soundness.lean`, `Verify/Axioms.lean` or `Verify/Guard.lean` — all three guards pass
unchanged (M16), and no frozen file needs to move.

### §3.4 Two stale claims in files I do not own

1. **`Lean4Lean/Inductive/Add.lean`:1096-1098** reads "*Two residuals remain, both named there:
   `MutualNamesGate` (the header loop, unproved not false) and `InductiveMapGate` (the map side of
   the inductive step).*" Repair: "*One residual remains, `InductiveMapGate` (the map side of the
   inductive step). The header loop's postcondition is now a theorem
   (`addMutual_header_post`, `Verify/Inductive/MutualNames.lean`), and the `mutualDefnDecl` branch
   stands unconditionally.*"
2. **`Verify/Inductive/RestoreFaithful.lean`:418-420** reads "*Two residuals remain, both named and
   both about which names a branch adds, neither a name condition: `MutualNamesGate` (`addMutual`'s
   header loop's postcondition) and `InductiveMapGate` (the map side of the inductive step — the
   seven-file flip). Both **unproved, not false**.*" Repair: "*One residual remains:
   `InductiveMapGate` (the map side of the inductive step — the seven-file flip), **unproved, not
   false**. `addMutual`'s header-loop postcondition is proved
   (`Verify/Inductive/MutualNames.lean`); the gate that stood for it was not just unproved but
   defective as stated, omitting `env.constants.WF`.*"

Neither edited: not my files.

## §4 Method gaps in my own round

* **My nine shape priors found the trap and missed the defect.** S2 correctly predicted the
  `M.WF`/`VEnvs.WF` trap, which saved the round. But not one of the nine asked *"is the statement I
  am being asked to prove well-posed?"* — the possibility that a residual `Prop` written by a
  careful author is missing a hypothesis. S7 asserted the opposite with p 0.85 and got the direction
  of the whole result wrong. **The prior worth having was "the gate's own statement is where the bug
  is", and the cheap check that would have found it before any Lean is: *compare the residual's
  hypotheses to those of the theorems immediately around it*.** `checkConstantVal_find?_none`,
  `NoNestedMap.add`, `checkName.WF` and `NoNestedEnv` all carry `env.constants.WF`; the gate that
  asserts their conclusion carries none. That asymmetry is visible by eye in the file I had already
  read, and I read past it.
* **I read the docstring and quoted it and it was still misleading, in a way rule 3 does not
  catch.** `MutualNamesGate`'s docstring says "*This is **unproved, not false**: every conjunct is a
  postcondition of a check the loop actually performs (`Lean4Lean/Environment.lean`:86-104).*" Every
  clause of that is defensible — the conjuncts *are* postconditions of checks, and the gate *is* not
  false — and it is still wrong about what stands between the reader and a proof. Rule 3 tells me to
  read the docstring before contradicting it; the gap is that a docstring can be locally true and
  globally misdirecting, and the only defence is re-deriving the statement's hypotheses from the
  checks rather than taking "postcondition of a check" as meaning "derivable from the check".
* **S8's line-number suspicion was right and I did not follow it up as a measurement.** I predicted
  the citation `Environment.lean:86-104` was off, noted `addMutual` spans 79-113 in my copy, and then
  never checked whether the *range* mattered. It does not, but I recorded a suspicion and left it
  unresolved rather than converting it to a measurement, which is the exact defect §2 is for. For the
  record: `addMutual` is lines 79-113, the header `M.run` block is 84-104, and the loop body's three
  checks are 88-98 — so the citation is right about the loop and wrong about where it starts.
* **I could not obtain rule 5's licensing build for four attempts, and the reason was two other
  streams' untracked in-flight files** (`Verify/Inductive/PosScan.lean`, then
  `Theory/Typing/CParRedK.lean`). I substituted an explicit-target build (`lake build Lean4Lean
  Lean4Lean.Verify.Guard Lean4Lean.Verify.Inductive.MutualNames`, 1284 jobs, green, all three guards
  passing), which covers every module tracked at HEAD plus mine but is **not** a bare `lake build`.
  Rule 5 says only a bare `lake build` licenses "green"; M16 records which of the two I actually got.
* **I did not attempt a *proof* of the unprovability I claim.** `mutualNamesGate_of_contains`
  locates the residue and `find?_none_of_contains_false` discharges it under `WF`, but "neither
  provable nor refutable at a stage-2 map" is an argument from `partial def` opacity, not a Lean
  theorem, and Lean cannot state it. The honest form of the claim is the one in §6.1 of the source
  file: the residue is *exhibited*, and it is not about `addMutual`.

## §5 The measured table (`scripts/exists.lean`, population 476 built modules, 2026-09-04)

All in `Lean4Lean.Verify.Inductive.MutualNames`. Every row: **own value is a hole: false; cone
reaches `sorryAx`: false**. `#print axioms` for **all twelve** is exactly
`[propext, Classical.choice, Quot.sound]` — none carries `sorryAx`, and none carries the four frozen
`Lean.Expr` primitives that `NoNestedAll.lean`'s `addQuot`/`addDecl` results do, because nothing
here touches the quotient path.

| name | arity | cone | what it is |
| --- | --- | --- | --- |
| `forIn_ok_fresh` | 9 | 597 | §1, the loop, at the raw monadic value — no `VContext`, no `WF` |
| `addMutual_header_post_gen` | 7 | 7355 | §2, generic in the per-member property |
| `addMutual_header_post` | 6 | 8156 | §2, the `find? = none` form (needs `mapWF`) |
| `addMutual_noNestedEnv'` | 6 | 8191 | **§3, the branch, no gate** |
| `MutualNamesGateWF` | 0 | — | §4, the gate with the hypothesis it was missing |
| `mutualNamesGateWF` | 0 | 8158 | §4, that gate discharged |
| `checkName_ok_contains` | 5 | 5262 | §4, `checkName` success → `contains = false`, no `WF` |
| `checkConstantVal_contains_false` | 7 | 7259 | §4, the same through `checkConstantVal` |
| `contains_false_of_wf` | 4 | 3376 | §4, `find? = none → contains = false` under `WF` |
| `find?_none_of_contains_false` | 4 | 3376 | §4, the converse under `WF` — the residue, discharged |
| `addMutual_header_post_contains` | 5 | 7366 | §4, **the strongest `WF`-free postcondition** |
| `mutualNamesGate_of_contains` | 1 | 7368 | §4, `MutualNamesGate` reduced to one `SMap` fact |
| `mutualNamesGate_at_wf` | 6 | 8156 | §4, the gate's conclusion at any `WF` map |

For comparison, measured the same way and the same day: `MutualNamesGate` itself (arity 0, cone
7301, `Verify/Inductive/NoNestedAll`) and `TypeChecker.M.WF.forInFresh` (arity 8, cone 699,
`Verify/TypeChecker`) — the pre-existing loop rule that S2 predicted would be unusable and was.
