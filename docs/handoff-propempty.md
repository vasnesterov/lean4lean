# handoff: is `VEnv.PropAgreeOn (∅ : VEnv) 0` true, false, or open?

Stream `propempty`. Owns `Lean4Lean/Theory/Typing/PropEmpty.lean` (new) and this file.
Start commit `4a13ad3`. Target stated by the brief: **prove or refute
`Lean4Lean.VEnv.PropAgreeOn (∅ : VEnv) 0`** — the weakest member of the `PropAgreeOn`
family, implied by every other instance via `mono_env` / `mono_univs`.

Asymmetry, carried from the brief and to be verified not trusted:
* FALSE ⇒ no hole-free `PropAgreeOn` derivation exists at *any* environment, and the whole
  route to killing the `proofIrrel` whitelist entry collapses. Catastrophic side.
* TRUE ⇒ necessary, **not** sufficient; settles nothing about general environments
  (`no_wf_hypothesis_avoids_empty_propAgreeOn` is why).

## §1 Questions, asked before the instruments were run

Rule: questions written first; predictions filled after reading and before running the
instrument; verdicts appended to §2. **No filled answer is ever edited**; every correction
is a new §2 entry.

### Q1 — conclusion-shape, all three aliases (the alias trap)
`VEnv.PropAgreeOn` (`SortInvIndep`), `VEnv.PropAgreeUp` (`PropAgreeLift`),
`VEnv.PropTypeAgreeOnCtx` (`SetModel/PropSplitAudit`) are relayed as `rfl`-equal,
arity 2, cone 578. Verify that equality myself, then: does any declaration in the built
population conclude *any* of the three **instantiated at `∅`** — or conclude its negation
(`¬ PropAgreeOn ∅ _`, `False` from it)? Run `scripts/shape.lean` on all three heads and read
hypotheses, not names. Also: is there an existing `∅`-instantiated corollary already sitting
in the tree that answers the round in one citation?

- Prediction: **All three are `rfl`-equal and I expect `Iff.rfl`/`rfl` to check** (the three bodies I read
are character-identical modulo `Nat`/`ℕ`). On the search: **no** declaration concludes any of the
three at `∅` unconditionally, and **no** declaration concludes a negation of any of them at any
environment. I expect exactly one `∅`-instantiated *conditional* producer,
`VEnv.propAgreeOn_empty_of_stratifiedNOn` (`PropAtWF`, needs `∀ n, PropTypeAgreeNOn ∅ 0 n` and
`∀ n, PropUniqNOn ∅ 0 n`), plus the antitone bound `propAgreeOn_bottom` / `propAgreeOn_le` and the
one-way negative `propAgreeOn_empty_false_imp`. I expect the `PropTypeAgreeOnCtx` head to be the
one with the most hits (the model side re-exports it), and I expect no fourth alias — `PropAtWF`'s
header already claims a source-level scan found exactly three, which I will not re-run but will
not rely on either: the compiled-environment query is the one that counts.
- Verdict: see §2.

### Q2 — cheapest instrument, current form: instantiate every argument at its extremes
`PropAgreeOn` is arity 2 (`env`, `U`); its *body* quantifies over more. Unfold the definition
and instantiate every quantified argument at its extremes, including the ones a **side
condition permits and I would assume it forbids**: the context (`[]` vs. non-empty),
the level list `ls` (`[]`, i.e. shorter than `U`, so out-of-range params take their default,
vs. long), the two terms/types (`.sort` vs. `.bvar` vs. stuck `.app`), and — since `U = 0` —
whether any universe is available above `Prop` at all. Which extreme is the one that can make
the body false at `∅`?

- Prediction: The extremes:
* `ls` — **not an extreme at all at `U = 0`, and that is a real simplification I expect to be able
  to prove**: `u.WF 0` forbids `.param` (there is no `i < 0`), so `u.eval ls` is independent of
  `ls`. So the `∀ ls` in the body is redundant at `U = 0`; `ls := []` is fully general. This is the
  one place where `U = 0` genuinely *shrinks* the statement rather than merely weakening it.
* `Γ` — the extreme the guard **permits and one would assume it forbids**: `OnCtx Γ (∅.IsType 0)`
  permits a context of a Prop *variable* (`Γ = [.sort .zero]`, entry `IsType` via
  `HasType.sort`) and then a *proof variable* over it (`Γ = [.bvar 0, .sort .zero]`, entry `IsType`
  because `.bvar 0 : .sort .zero`). So the `proofIrrel` premise shape is *available at `∅`* — the
  guard does not vacuously exclude it. This is the extreme that matters.
* the terms — `e := .sort l` and `e := .forallE _ _` I expect to be **closed cases**: a sort's and a
  Π's second type is a sort at a `.succ`/`.imax` level, and `(.imax u v).eval = 0 ↔ v.eval = 0`, so
  the Π case reduces to the codomain by the induction hypothesis and never needs level uniqueness.
  `e := .bvar i` is closed by `Lookup` determinism. The **only** open extreme is `e := .app f a`
  (stuck application) and `e := .lam _ _` given a sort-vs-Π conversion — i.e. the corner.
* `U = 0` leaves `.succ .zero` available, so the conclusion is not degenerate.

Net prediction: the body is non-vacuous at `∅`, no extreme makes it cheaply false, and the
statement is **equivalent to its `ls := []` instance**.
- Verdict: see §2.

### Q3 — transport: is an argument of this form already in the tree?
Twice this week transporting an existing method beat constructing one. Candidates:
`no_wf_hypothesis_avoids_empty` / `no_wf_hypothesis_avoids_empty_propAgreeOn` (arity 4,
cone 593), `empty_no_defeqs`, `empty_wf` (`InjPiRogue.lean`:721), the `∅`-typing inversion
family, and whatever `PiInvVac.not_propAgreeOn_of_route_open` actually says. Is there an
inversion lemma for `HasType ∅ …` / `IsDefEq ∅ …` strong enough that the `∅` case is a
*structural induction on a rule set with no δ and no constants*, i.e. a proof by transport
rather than construction?

- Prediction: Transport works for the *limits* and not for the positive. `no_wf_hypothesis_avoids_empty*`,
`mono_env`, `mono_univs` are already spent in `PropAtWF`. The genuinely new transport I expect to
find is the **direction of the reduction**: `PiInvVac.piInv_empty_of_propAgreeOn` puts
`PropAgreeOn` *upstream* of `PiInv`, so I predict the open route to `PropAgreeOn ∅ 0`
(`AppUniqLvl`/`PropUniqN.AppCase`) is **not** unblocked by `env = ∅`: `∅`-ness kills only
`IsDefEq.constDF` and `IsDefEq.extra`, and the app case's difficulty is `appDF` + `beta` + `eta` +
`proofIrrel`, every one of which survives at `∅`. I therefore expect to be able to *prove* that
the residual is `∅`-insensitive, rather than to discharge it. Concretely I expect: the two
stratified hypotheses at `∅` are open, and no hole-free `∅`-specific inversion lemma exists that
the general one does not.
- Verdict: see §2.

### Q4 — the refutation direction, and the limits of a positive
If FALSE: the witness must be two derivations at `∅` whose Prop-ness or whose types disagree
while conversion at `∅` (structural + β + η? + `proofIrrel`, `extra` dead by
`empty_no_defeqs`) cannot equate them. Is `proofIrrel`'s own side condition — the thing that
lets two *distinct* proofs of the same Prop be identified — the mechanism that makes the
statement true, or the mechanism that breaks it (the extreme the side condition *permits*)?
If TRUE: state and, where possible, *prove* the limit — that `PropAgreeOn ∅ 0` does not
transport upward, with `mono_env`'s direction as the proof.

- Prediction: **`proofIrrel` cannot break it directly, and I predict I can prove why**: its conclusion
`Γ ⊢ h ≡ h' : p` carries the *same* type `p` on both sides, so it never hands a term a second
type. It can only enter through `defeqDF`, which needs a type-level equation `A ≡ B : .sort w`;
to get one out of `proofIrrel` you need the equated pair to *be* types, i.e. you need a `p : Prop`
that is convertible to a sort — exactly `PiInvWF.SortZeroConvProp`, the route `PiInvVac` already
reduced. So the refutation, if it exists, is not cheap and lives in the same corner.
Predicted verdict: **still open**, leaning true. On the limit side I predict I can prove, not
merely assert, that a positive does not transport upward: `mono_env` runs `env' → env` along
`env ≤ env'`, so from `PropAgreeOn ∅ 0` there is *no* map to any `PropAgreeOn env U` — and I can
witness the failure schematically (a `PropAgreeOn ∅ 0 → ∀ env U, PropAgreeOn env U` implication
would, composed with `propAgreeOn_bottom`, make the whole family equivalent to its bottom, which
is exactly the collapse `no_wf_hypothesis_avoids_empty_propAgreeOn` says `VEnv.WF` cannot buy).
- Verdict: see §2.

## §2 Verdicts, appended in order

_(empty at creation)_

### M1 (Q1) — three-alias conclusion-shape search, population **489 built modules**

`scripts/shape.lean`, one run per head:

| head | constants concluding it | structure fields |
| --- | --- | --- |
| `Lean4Lean.VEnv.PropAgreeOn` | 46 | 0 |
| `Lean4Lean.VEnv.PropAgreeUp` | 1 | 0 |
| `Lean4Lean.VEnv.PropTypeAgreeOnCtx` | 24 | 0 |

`scripts/exists.lean` on the three names: **`VEnv.PropAgreeOn`, `VEnv.PropAgreeUp`,
`VEnv.PropTypeAgreeOnCtx` — each arity 2, cone 578, hole-free.** The relayed alias figures check
out, and the three-way query was necessary: the `PropAgreeOn` head misses
`propAgreeUp_of_stratifiedN` and all 24 `PropTypeAgreeOnCtx` hits.

**The two hits that could have ended the round, and do not.** The `PropTypeAgreeOnCtx` head is the
only one with an **arity-0** producer, i.e. an unconditional claim of the statement — and by
`propAgreeOn_bottom` any such instance at any `env`/`U` would give `PropAgreeOn ∅ 0` outright:

* `Lean4Lean.SetModel.PropAgreeWall.preludeEnv_propTypeAgreeOnCtx` — arity 0, cone **3854**,
  `cone reaches sorryAx: true`, holes `[Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified]`, and
  additionally `IsDefEq.uniq`/`IsDefEq.uniqU` in cone (policy-watched).
* `Lean4Lean.VEnv.WF.propTypeAgreeOn` — arity 3 (`VEnv.WF` only), cone **3481**, same hole, same
  two watched names.

So both unconditional-looking producers are hole derivations through the very hole the corner
exists to discharge. `SetModel.NEAudit.nonempty_propSplit_preludeEnv_iff` is arity 0 **and
hole-free**, but it is an `Iff` (`Nonempty (PropSplit preludeEnv 0) ↔ PropUniqOnCtx ∧
PropTypeAgreeOnCtx`), so it produces nothing.

`Lean4Lean.SetModel.PropAgreeWall.propTypeAgreeOnCtx_of_stratifiedN` (arity 4, cone 2703) *is*
hole-free — it is the model-side twin of `propAgreeUp_of_stratifiedN`, same stratified hypotheses.

**No negation of any alias is concluded anywhere unconditionally.** The one negative,
`Lean4Lean.VEnv.not_propAgreeOn_of_route_open` (arity 4, cone 2123, hole-free), is
`Ordered env → (ForallEProofPair env U ∨ SortZeroConvProp env U) → ¬ PropAgreeOn env U` — a
*conditional* refutation whose antecedent is itself an open route, so per method rule 4 it may not
be quoted as a refutation. It is, however, the exact shape a refutation of my target would take.

**Q1 prediction: held**, including the sub-prediction that the single-head query is incomplete.
Corrected detail: I predicted "no arity-0 producer"; there are two arity-0/arity-3
*unconditional-in-form* producers, and what kills them is the hole audit, not the shape search.
Hole-free-and-unconditional: still none.

### M2 (Q2) — the extremes, run on the body of `PropAgreeOn ∅ 0`

The instrument found the one that matters, and it is not any of the ones the round was primed for.

**`ls` — dead at `U = 0`, and already known.** `u.WF 0` forbids `.param` (`VLevel.WF n (.param i)`
is `i < n`), so `eval` is `ls`-independent. Three copies of this were already in the tree:
`VLevel.eval_indep_of_wf_zero` (`PropAgreeGuarded`:93), `VLevel.eval_indep_of_wf_zero_up`
(`PropAgreeLift`:89), `VLevel.eval_const_of_wf_zero` (`SetModel/PreludeOracle`:1531). Restated in
the reduced statement's shape as `propAgreeNil_ls_irrelevant`; the *converse* half
(`param_eval_zero_not_indep`) is new and is what turns "dead quantifier" into a measured limit.

**`Γ` — the load-bearing extreme, and the prediction was half right.** I predicted the guard
*permits* the `proofIrrel` premise shape at `∅`, and it does: `empty_proofIrrel_fires` builds
`OnCtx [.bvar 1, .bvar 0, .sort .zero] ((∅ : VEnv).IsType 0)` — `P : Prop, h : P, h' : P` — and a
`proofIrrel` step `∅ ⊢ .bvar 0 ≡ .bvar 1 : .bvar 2` between syntactically distinct terms, hole-free.

**What I did not predict, and it is the round's result: the `Γ` extreme is not an extreme, it is a
reduction.** `Γ = []` is *fully general*. `PropAgreeOn env U ↔ PropAgreeNil env U` over `Ordered`
(`propAgreeOn_iff_nil`), i.e. **the `∀ Γ` and the `OnCtx` guard carry no content.** The step is
`IsDefEq.lamDF` + `IsDefEq.forallEDF` plus `imax_eval_zero_iff`
(`(.imax u₁ u).eval ls = 0 ↔ u.eval ls = 0`): Π-abstraction preserves the propositionhood bit
exactly. This works *because* `PropAgreeOn`'s conclusion is the weak one — `.imax u₁ u ≈ .imax u₁ u'`
is strictly weaker than `u ≈ u'`, so `SortUniq` does **not** admit the same reduction.

**Term extremes: as predicted.** `.sort` and `.forallE` close by the `imax`/`succ` arithmetic,
`.bvar` by `Lookup` determinism, and the only open extreme is `.app` (Π-injectivity) — which the
`Γ`-reduction does not touch, because the induction that would exploit it goes under binders and
re-creates contexts.

**Q2 prediction: held on `ls`, held on `Γ`'s permissiveness, and undershot on `Γ`'s generality.**
I called `Γ = []` an extreme; it is the whole statement.

### M3 (Q3) — transport, and the `∅`-insensitivity of the residual

No hole-free `∅`-specific inversion lemma exists, as predicted, and the measurement of *why* is
now machine-checked rather than asserted. `∅` deletes exactly two rules of
`Theory/Typing/Basic.IsDefEq`: `constDF` (no constants) and `extra` (`empty_no_defeqs`). Every
other rule is live, and two of the live ones are witnessed firing at `∅` between syntactically
distinct terms: `β` (`empty_conv_nontrivial`, at `Γ = []`) and `proofIrrel`
(`empty_proofIrrel_fires`). The open residual on the live route is
`∀ n, PropUniqN.AppCase env U n` (= `AppCase.AppUniqLvl`) modulo four side conditions
(`SortDisjInvN`, `PropConvInv`, `RegPi`, `InstLvl`) — `PropAgreeGuarded` §2 — and it turns on
`appDF`/`beta`, neither of which `∅` removes. **So `env = ∅` buys nothing on the residual**, which
is the exact sense in which the round's target is the bottom rather than an easier problem.

One thing the transport instrument *did* find, and it is a handoff item rather than a result:
`PropConv.RegPi` is "not shown satisfiable" for a reason that is a **context** reason
(`Stratified.lam` does not ship the codomain typing; `Lookup` can hand back a Π whose components
were never typed). §1's Π-abstraction argument is the shape that removes contexts. Whether it can
be re-run on `PropUniqN`/`RegPi` inside the stratified system — where the index bookkeeping may
charge for `forallEDF` — is unmeasured here and deliberately not widened into.

**Q3 prediction: held.**

### M4 (Q4) — the refutation direction, and the limits

`proofIrrel`'s conclusion `Γ ⊢ h ≡ h' : p` carries the same type on both sides, so it cannot hand a
term a second type; it can only enter a refutation through `defeqDF`, which needs a *type-level*
equation `A ≡ B : .sort w`, i.e. needs a `Prop` convertible to a sort — `PiInvWF.SortZeroConvProp`,
the route `PiInvVac` already reduced. That is analysis, not a theorem, and is recorded as such: the
theorem-strength content is that the rule and its premise shape are **live and non-vacuous at `∅`
under the guard** (`empty_proofIrrel_fires`), so nothing here makes the refutation route vacuous.

Limits, proved: `PropAgreeNil.mono_env` and `PropAgreeNil.mono_univs` — the reduced statement is
antitone in both coordinates too, so §1 did not move the target in the lattice and
`PropAgreeNil (∅ : VEnv) 0` is still the bottom. `propAgreeNil_empty_of_any` is the one-way
direction (any instance anywhere supplies it); there is no converse, and `param_eval_zero_not_indep`
measures one thing the descent to `U = 0` throws away. `forallEProofPair_empty_dies_of_nil` is the
entry-kill driven by the reduced statement, and it is still **only at `∅`**.

**Q4 prediction: held.** Verdict on the round's question: **still open, neither proved nor
refuted** — with the target strictly smaller in its context coordinate.

## §3 The measured table

`Lean4Lean/Theory/Typing/PropEmpty.lean` (288 lines, new, hole-free — every declaration audited by
a `#print axioms` block at the foot of the file; no `sorryAx` anywhere).

Arities and cones are `scripts/exists.lean`'s output, not read off the statements.

| declaration (as `scripts/exists.lean` prints it) | arity / cone | content |
| --- | --- | --- |
| `Lean4Lean.VEnv.imax_eval_zero_iff` | 3 / 1495 | `(.imax u v).eval ls = 0 ↔ v.eval ls = 0` — Π-abstraction preserves the propositionhood bit |
| `Lean4Lean.VEnv.PropAgreeNil` | 2 / 574 | the target with `∀ Γ` and the `OnCtx` guard removed |
| `Lean4Lean.VEnv.PropAgreeOn.nil` | — | easy half |
| `Lean4Lean.VEnv.PropAgreeNil.propAgreeOn` | 4 / 2164 | **hard half** — induction on `Γ`, `lamDF` + `forallEDF` + `IsDefEq.sort_r` |
| `Lean4Lean.VEnv.propAgreeOn_iff_nil` | 3 / 2166 | **`PropAgreeOn env U ↔ PropAgreeNil env U` over `Ordered env`** |
| `Lean4Lean.VEnv.propAgreeOn_empty_iff_nil` | **0** / 2168 | the round's target, unconditionally restated with no context and no guard |
| `Lean4Lean.VEnv.propAgreeOn_empty_of_nil_anywhere` | — | one closed-context instance anywhere supplies it |
| `Lean4Lean.VEnv.forallEProofPair_empty_dies_of_nil` | 1 / 2181 | `PiInvVac`'s entry-kill driven by the reduced statement |
| `Lean4Lean.VEnv.PropAgreeNil.mono_env` / `.mono_univs` | 5 / 643 | the reduced statement is antitone in both coordinates |
| `Lean4Lean.VEnv.propAgreeNil_empty_of_any` | — | the one-way direction |
| `Lean4Lean.VEnv.propAgreeNil_premises_fire` | — | anti-vacuity of the reduced premises at `Γ = []`, two types syntactically different |
| `Lean4Lean.VEnv.empty_conv_nontrivial` | **0** / 618 | a `β` step at `∅`, `Γ = []`, between syntactically distinct closed terms |
| `Lean4Lean.VEnv.empty_proofIrrel_fires` | **0** / 653 | `OnCtx [.bvar 1, .bvar 0, .sort .zero] ((∅).IsType 0)` and a `proofIrrel` step `.bvar 0 ≡ .bvar 1 : .bvar 2` |
| `Lean4Lean.VEnv.propAgreeNil_ls_irrelevant` | — | the `∀ ls` is dead at `U = 0` |
| `Lean4Lean.VEnv.param_eval_zero_not_indep` | **0** / 656 | …and alive at `U ≥ 1`, so the descent to `U = 0` throws content away |

### Build state, on this working tree

`lake build` (bare): **exit 0, "Build completed successfully (1677 jobs)"**. The brief's baseline was
1675; `+1` is `Lean4Lean.Theory.Typing.PropEmpty` (mine), `+1` is
`Lean4Lean.Verify.Inductive.RebuildFinish` (another stream's, untracked alongside
`docs/handoff-rebuildfinish.md`). No warnings and no `sorry` from `PropEmpty.lean`.

Guards, from the build log: guard 1 ✓ (24 frozen axioms), guard 2 ✓ (`kernel_sound` axioms within
whitelist; proof still INCOMPLETE — `sorryAx` present), guard 3 ✓ (2/2 implementation gaps).

`scripts/sorry-census-all.lean`: **14**, not the brief's 13. The extra hole is
`Lean4Lean.addInductive_delta_nested [Lean4Lean.Verify.Inductive.RebuildFinish]` — the other
stream's, in a file I do not own. My module contributes none; `PropEmpty` appears in no census row.

## §4 Where my own method failed

1. **The instrument I ran as written still nearly missed the result.** "Instantiate every quantified
   argument at its extremes" made me treat `Γ = []` as *an extreme to test*, and I wrote that into
   Q2 in exactly those words. It is not an extreme; it is a normal form. The refinement the next
   round should carry: **when an extreme of a quantifier is cheap, check whether it is also
   general** — a `∀ x, P x` whose cheapest instance *implies* the rest is a reduction, not a probe,
   and the way to notice is to ask what the statement's conclusion is invariant under (here:
   `.imax u₁ ·`).
2. **I nearly stopped at "no unconditional producer" from the shape search alone.** Two hits were
   arity 0 and arity 3 with `VEnv.WF` only, and only `scripts/exists.lean`'s hole audit killed them.
   A conclusion-shape search is not an absence instrument on its own.
3. **`ls`-irrelevance existed three times over and I planned to prove it a fourth.** I caught it by
   grepping for `WF 0` rather than for a guessed lemma name; grepping the *hypothesis shape* found
   what a name search would not have. The lost work was small only because I checked before writing.
4. **The strongest thing I did not do**, and it is the handoff: §1's Π-abstraction argument is a
   context-elimination method, and `PropConv.RegPi` — the hypothesis on the live route that is *not
   shown satisfiable* — is open for a **context** reason (`Stratified.lam` does not ship the
   codomain typing; `Lookup` can hand back a Π whose components were never typed). Re-running §1's
   argument inside the stratified system, on `PropUniqN` / `RegPi`, is the obvious next move. I did
   not attempt it: the brief said one statement, and the index bookkeeping of `Stratified.forallEDF`
   is an unmeasured cost. It should be measured before it is funded.
