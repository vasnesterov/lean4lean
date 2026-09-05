# handoff: is `PropAgreeOn` derivable at `VEnv.WF` alone, hole-free?

Stream `propat-wf`. Owns `Lean4Lean/Theory/Typing/PropAtWF.lean` and this file.
Start commit `28cd89b`. Target stated by CONCLUSION SHAPE: **find or refute a hole-free
derivation whose conclusion is `env.PropAgreeOn U` from `VEnv.WF env` alone.**

## §1 Questions, asked before the instruments were run

Rule: questions written first, predictions filled after reading and before running the
instrument, verdicts appended to §2. **No filled answer is ever edited**; every correction is
a new §2 entry.

### Q1 — conclusion-shape, primary
Does any declaration in the built default-target population conclude something mentioning
`Lean4Lean.VEnv.PropAgreeOn` (or the model-side name for the same content,
`PropTypeAgreeOnCtx`) whose *only* hypotheses are `VEnv.WF env` / `Ordered env`?
Run `HEADS="VEnv.PropAgreeOn" scripts/shape.lean` and `HEADS="PropTypeAgreeOnCtx" …`, then
read every hit's hypotheses rather than its name.

- Prediction: **No.** I expect many hits with `PropAgreeOn` in *hypothesis* position (`SortInvIndep`, `PiInvResidual`, `ForallInvPrice`, `PiInvVac`, `SpineVarVacuity`) and exactly two families concluding it — `PropAgreeGuarded.propAgreeOn_of_stratifiedNOn` / `…_of_stratifiedN` — none of them from `VEnv.WF` alone. I also expect the shape search to **miss** `PropAgreeLift.propAgreeUp_of_stratifiedN`, because that file restates the same predicate under the fresh name `PropAgreeUp` to stay upstream of `Injectivity`; so head `VEnv.PropAgreeOn` alone is not a complete conclusion-shape query and I must run `PropAgreeUp` too.
- Verdict: see §2.

### Q2 — chain link 1, the relayed lemma
`VEnv.propAgreeOn_of_stratifiedNOn` (`Theory/Typing/PropAgreeGuarded.lean`) is relayed to me as
"arity 4, cone 2410, `sorryAx`-free", deriving `PropAgreeOn` from a stratified hypothesis. What
is its *actual* statement — which `U`, which hypotheses, which hole set — as
`scripts/exists.lean` prints it, not as the relay says?

- Prediction: Hole-free, `Ordered env` (not `VEnv.WF`) plus two `∀ n` stratified hypotheses `PropTypeAgreeNOn env 0 n` / `PropUniqNOn env 0 n`, and the conclusion is `PropAgreeOn env **0**` — `U` is *fixed at 0*, not universally quantified. So even a full success would deliver only the `U = 0` instance, which is a limit the relay did not carry.
- Verdict: see §2.

### Q3 — chain link 2, the stratified hypothesis
Is that stratified hypothesis (`∀ n, PropTypeAgreeNOn env 0 n` and `∀ n, PropUniqNOn env 0 n`,
or the unguarded `PropTypeAgreeN` / `PropUniqN`) available at `VEnv.WF` hole-free? Search by the
conclusion shapes `PropUniqN`, `PropTypeAgreeN`, `PropUniqN.AppCase`, `AppUniqLvl`, and check
each candidate's own cone for `sorryAx` and for the six tainted names
(`WF.uniq'`, `WF.sortUniq'`, `HasType.defeqU_l'`, `IsType.not_isProof`, `WF.proofTransport`,
`WF.sortUniq`, all of which carry `IsDefEqU.forallE_inv_stratified`).

- Prediction: **No.** The stratified hypothesis is the obstruction. `PropAgreeGuarded.propUniqN_iff_appCase_all` makes `∀ n, PropUniqN` *equivalent* to `∀ n, PropUniqN.AppCase` = `AppUniqLvl` over `SortDisjInvN`, and `PropAgreeLift` §3 records that both of route B's hypotheses are open at every index above `0` with `PropUniqN.zero` / `PropTypeAgreeN.zero` the only unconditional instances. I expect no hole-free producer of either `∀ n` form at `VEnv.WF`, and I expect the `AppCase`/`AppUniqLvl` corner to be where it stops.
- Verdict: see §2.

### Q4 — extremes, monotonicity, and the refutation direction
Cheapest instrument, current form. Instantiate every universally quantified argument of
`PropAgreeOn` at its extremes: `env := ∅` vs. a `VEnv.WF` environment built at the *permitted*
edge of `WF`'s side conditions (the round that found `VEnv.WF` permits an **unsafe** definition
is the precedent); `U := 0` vs. `U ≥ 1`; `ls := []` (shorter than `U`, so out-of-range params
evaluate at their default) vs. a long `ls`. Is `PropAgreeOn` monotone in `env` (so that an
`∅`-witness would be a witness everywhere, making the cheap witness the least likely), and is
there a `VEnv.WF` environment at which `PropAgreeOn` is **false** — i.e. is the answer a
refutation rather than a missing link?

- Prediction: `PropAgreeOn` is **antitone**, not monotone, in `env`: it is a `∀` over typing derivations, so a larger environment has more antecedents to satisfy. Hence `∅` is the *easiest* environment, not the hardest, and `PropAgreeOn (∅ : VEnv) U` is a **necessary condition** for any `VEnv.WF`-only derivation (since `VEnv.WF ∅` holds). `PiInvVac` reports it open at `∅`; if that holds up it decides Q1 outright and cheaply. On the refutation side I expect **no** refutation at `VEnv.WF`: `PropAgreeOn` is a weakening of unique typing, which is believed true for the theory, and `PiInvWF.unsafeSelfEnv_rules_refl` shows the one exotic thing `VEnv.WF` permits (`.unsafeDef`) adds only reflexive rules, hence no new conversions to exploit. So the expected answer is 'not derivable, and not refutable either' — a missing link, not a counterexample.
- Verdict: see §2.

## §2 Verdicts, appended in order

_(empty at creation)_

### M1 (Q1, first half) — `HEADS="VEnv.PropAgreeOn"`, population 488 modules

34 constants mention `VEnv.PropAgreeOn` in their type; 0 are structure fields. Exactly **two**
have it in *conclusion* position:

* `Lean4Lean.VEnv.propAgreeOn_of_stratifiedNOn` (arity 4, `Theory/Typing/PropAgreeGuarded`)
* `Lean4Lean.VEnv.propAgreeOn_of_stratifiedN` (arity 4, same module)

Everything else has it as a hypothesis, plus one negative
(`VEnv.not_propAgreeOn_of_route_open`, arity 4, `PiInvVac`). **Nothing concludes it from
`VEnv.WF` alone.** Prediction Q1 held on this half. Second half (alias names, and the
body-shape query that does not depend on the predicate's name) still to run — the prediction
that this head alone is an incomplete query is itself part of Q1.

### M2 (Q1, second half) — the alias search, and it finds the thing the head-`PropAgreeOn` query cannot

Three further names denote the same content, and each needed its own query:

* `HEADS="VEnv.PropAgreeUp"` → 1 hit, `VEnv.propAgreeUp_of_stratifiedN` (arity 4,
  `Theory/Typing/PropAgreeLift`) — the upstream copy, same stratified hypotheses.
* `HEADS="VEnv.PropTypeAgreeOnCtx"` → 24 hits, and one of them is
  **`Lean4Lean.VEnv.WF.propTypeAgreeOn` (arity 3, `Theory/SetModel/NotProofNoModel`)**:
  `theorem WF.propTypeAgreeOn (henv : env.WF) : env.PropTypeAgreeOnCtx nv`. That is the
  target's conclusion **from `VEnv.WF` alone, no second hypothesis**.
* `HEADS="VEnv.PropTypeAgree"` → 70 hits, all unguarded-form plumbing plus
  `SetModel/UpperBound.PropTypeAgreeInput : ∀ env, env.LeanWF → env.PropTypeAgree 0`, which is
  the same statement **named as an input**, i.e. carried rather than proved.

So Q1's prediction was **wrong on the half that mattered**: a `VEnv.WF`-only derivation of the
conclusion does exist and is named after neither predicate in the brief. Its docstring states
its own taint (`IsDefEq.uniqU` + `IsDefEqU.sort_inv`, i.e. straight through
`forallE_inv_stratified`), so the question becomes whether that taint is real and total, which is
what `exists.lean` decides next. Recorded here as a wrong prediction rather than edited away.

### M3 (Q1, Q2 decided) — `exists.lean`, population 488

| name | module | arity | cone | own hole | cone→`sorryAx` |
| --- | --- | --- | --- | --- | --- |
| `Lean4Lean.VEnv.WF.propTypeAgreeOn` | `Theory/SetModel/NotProofNoModel` | 3 | 3481 | no | **yes: `VEnv.IsDefEqU.forallE_inv_stratified`** |
| `Lean4Lean.VEnv.WF.propUniqOn` | same | 3 | 3476 | no | **yes: same hole** |
| `Lean4Lean.VEnv.propAgreeOn_of_stratifiedNOn` | `Theory/Typing/PropAgreeGuarded` | 4 | 2410 | no | no |
| `Lean4Lean.VEnv.propAgreeOn_of_stratifiedN` | same | 4 | 2415 | no | no |
| `Lean4Lean.VEnv.propAgreeUp_of_stratifiedN` | `Theory/Typing/PropAgreeLift` | 4 | 2410 | no | no |
| `Lean4Lean.SetModel.PropAgreeWall.propTypeAgreeOnCtx_of_stratifiedN` | `Theory/SetModel/PropAgreeWall` | 4 | 2703 | no | no |
| `Lean4Lean.VEnv.PropAgreeOn` / `.PropTypeAgreeOnCtx` / `.PropAgreeUp` | 3 modules | 2 | **578 each** | no | no |

**Q1 verdict: a `VEnv.WF`-only derivation exists and is circular.** `WF.propTypeAgreeOn` has
exactly the target conclusion from exactly the target hypothesis, and its cone reaches
`IsDefEqU.forallE_inv_stratified` — the hole the whole corner is trying to discharge — plus the
watched `IsDefEq.uniq` / `IsDefEq.uniqU`. So it is a **hole**-derivation, not a hole-free one, and
it cannot be used to close the `proofIrrel` route without circularity. My Q1 prediction ("no such
declaration") was wrong; the correction is that it exists and is unusable.

**Q2 verdict: prediction held exactly.** `propAgreeOn_of_stratifiedNOn` is hole-free
(cone 2410, no `sorryAx`, none of the six tainted names), takes `Ordered env` — *weaker* than
`VEnv.WF` — and two `∀ n` hypotheses, and its conclusion is `PropAgreeOn env **0**`: `U` is fixed
at `0`, not universally quantified. Source, `PropAgreeGuarded.lean:189-224`:
`(henv : Ordered env) (pta : ∀ n, PropTypeAgreeNOn env 0 n) (pun : ∀ n, PropUniqNOn env 0 n) :
PropAgreeOn env 0`. The relay's "arity 4, cone 2410, `sorryAx`-free" is accurate; the relay did
not carry the `U = 0` restriction, which bounds any success here to the `U = 0` instance.

The three predicate names having cone 578 each is consistent with the relayed claim that they are
definitionally the same statement; that is a size check, not a proof, and §3 of my file checks it
by `Iff.rfl` where the imports allow.

### M4 (Q3, Q4) — the family is **antitone**, `∅` is `WF`, and `Theory/Typing/AppUniqWF.lean` already ran this instrument one level down

Shape searches for the stratified hypothesis:

* `HEADS="VEnv.PropUniqN VEnv.WF"` → **0 hits**. `HEADS="VEnv.PropTypeAgreeN VEnv.WF"` → **0 hits**.
  So nothing in the tree derives either `∀ n` hypothesis from `VEnv.WF`, under any name that
  mentions both heads.
* `HEADS="VEnv.PropUniqNOn"` → 8 hits, of which the producers are only `PropUniqNOn.zero`
  (index 0) and `PropUniqN.propUniqNOn` (a weakening of an equally open statement); the rest are
  transfer lemmas and **three refutations** in `Theory/Typing/AppUniqRefute`
  (`piLvlEnv_propUniqNOn_false`, `piLvlEnv_propUniqNOn_all_false`,
  `ordered_not_enough_for_propUniqNOn`).
* `HEADS="VEnv.PropTypeAgreeNOn"` → 3 hits, producers only `PropTypeAgreeNOn.zero` and the
  weakening.
* `HEADS="VEnv.AppUniqLvl VEnv.WF"` → 2 hits, both in `Theory/Typing/AppUniqWF`, and they are the
  decisive ones.

`Theory/Typing/AppUniqWF.lean` already proves, hole-free, the instrument my brief asked me to run:

* `VEnv.wf_emptyEnv : VEnv.WF (∅ : VEnv)` and `VEnv.emptyEnv_le : (∅ : VEnv) ≤ env`;
* the whole `app`-case family is **antitone** in the environment — `AppUniqLvl.mono_env`,
  `PropUniqN.mono_env`, `PropUniqNOn.mono_env`, `PropUniqN.AppCase.mono_env` — because each
  statement has its environment only in its *premises* and its conclusion is a level equivalence,
  and the guard `OnCtx Γ (env.IsType U)` is monotone (`IsType.mono`), so it travels the same way;
* `VEnv.no_wf_hypothesis_avoids_empty` — **the general obstruction**: any schema
  `H env → AppUniqLvl env 0 1` with `H` implied by `VEnv.WF` proves `AppUniqLvl (∅ : VEnv) 0 1`,
  because `∅` is `WF` and therefore satisfies every consequence of `WF`.

**Q4 verdict: prediction held.** Antitone, not monotone; `∅` is the *easiest* environment and its
instance is a **necessary** condition of any `VEnv.WF`-only derivation. The bound is one-way:
refuting at `∅` refutes the target everywhere, proving at `∅` proves nothing about a larger
environment. No refutation of `PropAgreeOn` at a `VEnv.WF` environment exists in the tree, and
`PiInvWF.unsafeSelfEnv_rules_refl` remains the reason not to expect one from the `.unsafeDef`
edge of `WF`.

**Q3 verdict: prediction held; the stratified hypothesis is the obstruction.** Nothing derives
`∀ n, PropTypeAgreeNOn env 0 n` or `∀ n, PropUniqNOn env 0 n` from `VEnv.WF`, at any environment,
under any of the names searched; the only unconditional instances are at index `0`; and by
`propUniqNOn_le` even the `VEnv.WF`-quantified form collapses onto the empty-environment clause at
index 1.

### M5 — what I proved, in `Lean4Lean/Theory/Typing/PropAtWF.lean` (compiles, 13 declarations, all `[propext]` / `[propext, Quot.sound]`, no `sorryAx`)

The transport of `AppUniqWF.lean`'s instrument to `PropAgreeOn` itself, which nobody had run there:

* `VEnv.PropAgreeOn.mono_env` — `PropAgreeOn` is **antitone** in the environment (guard monotone by
  `IsType.mono`, premises by `HasType.mono`, conclusion environment-free).
* `VEnv.PropAgreeOn.mono_univs` — antitone in `U` too (`IsDefEq.mono_uvars`, `VLevel.WF.mono`), so
  `U = 0` is the **weakest** member of the `U`-chain and the hole-free producer emits exactly it.
* `VEnv.propAgreeOn_le`, `VEnv.propAgreeOn_bottom` — the bottom of both chains is
  `PropAgreeOn (∅ : VEnv) 0`.
* `VEnv.propAgreeOn_wf_lower`, `VEnv.no_wf_hypothesis_avoids_empty_propAgreeOn`,
  `VEnv.lhs_shape_not_enough_propAgreeOn`, `VEnv.rule_freeness_not_enough_propAgreeOn` — **the
  obstruction**: `∅` is `VEnv.WF`, so any schema `H env → PropAgreeOn env U` with `H` implied by
  `VEnv.WF` proves the empty-environment clause; `VEnv.WF`'s δ-rule structure, `lhs_shape`, and even
  total rule-freeness are all satisfied at `∅` and lift nothing.
* `VEnv.propAgreeOn_empty_false_imp` — a refutation at `∅` refutes the target everywhere.
* `VEnv.propAgreeOn_empty_of_stratifiedNOn`, `VEnv.propUniqNOn_all_wf_lower` — the chain at the
  bottom: `Ordered` is free at `∅`, so the price is exactly the two `∀ n` hypotheses, of which the
  `PropUniqNOn` half descends to `∅` as well.
* `VEnv.forallEProofPair_empty_dies_of_weakest`, `…_of_wf_route` — **the kill's hypothesis, named
  and weakened** (method rule 3): the `proofIrrel` entry at `∅` dies from the single weakest member
  of the family, `PropAgreeOn (∅ : VEnv) 0`, with `Ordered` free.

One measured asymmetry recorded rather than claimed: `PropTypeAgreeNOn`'s conclusion is
`IsPropN env U n Γ A'`, which mentions `env` in *conclusion* position, so the antitone argument that
works for `PropUniqNOn` does **not** apply to it. Whether it is antitone is unmeasured; that is why
`AppUniqWF`'s family stops where it does, and I did not extend it there.

### M6 — the three names are literally one proposition, machine-checked

In a scratch file (`lean_run_code`, importing `Theory/Typing/SortInvIndep`,
`Theory/Typing/PropAgreeLift` and `Theory/SetModel/PropSplitAudit` — an import combination
`PropAtWF.lean` deliberately does not take, to keep a `Theory/Typing` leaf out of the model layer):

```
example (env : VEnv) (U : Nat) : env.PropAgreeOn U ↔ env.PropAgreeUp U := Iff.rfl
example (env : VEnv) (U : Nat) : env.PropAgreeOn U ↔ env.PropTypeAgreeOnCtx U := Iff.rfl
example (env : VEnv) (U : Nat) : env.PropAgreeUp U ↔ env.PropTypeAgreeOnCtx U := Iff.rfl
example (env : VEnv) (U : Nat) : env.PropAgreeOn U = env.PropTypeAgreeOnCtx U := rfl
```

all four elaborate. So `WF.propTypeAgreeOn` really does conclude the target, not a cousin of it,
and the relayed `Iff.rfl` claim in `PropAgreeLift`'s docstring is confirmed (and strengthened to
`rfl`) rather than trusted.

### M7 — the chain, link by link, with each link's hole set

Reading `propAgreeOn_of_stratifiedNOn` bottom-up, at the environment my §2 bound puts it at:

| link | statement | status |
| --- | --- | --- |
| conclusion | `PropAgreeOn env 0` | **open** |
| producer | `propAgreeOn_of_stratifiedNOn` | hole-free, cone 2410, `Ordered` only, `U = 0` only |
| `Ordered env` | at `∅`: `PiInvVac.empty_ordered` | **free** |
| link A | `∀ n, PropTypeAgreeNOn env 0 n` | **open above index 0**; `PropTypeAgreeNOn.zero` is the only unconditional instance. Not antitone by the `PropUniqNOn` argument (its conclusion `IsPropN env U n Γ A'` mentions `env`), so it does not descend to `∅` for free |
| link B | `∀ n, PropUniqNOn env 0 n` | **open above index 0**; `PropUniqNOn.zero` only; antitone (`propUniqNOn_le`), so the `VEnv.WF`-quantified supply collapses to `∅` |
| link B, unguarded | `∀ n, PropUniqN env 0 n` | **equivalent** to `∀ n, PropUniqN.AppCase` over `∀ n, SortDisjInvN` (`propUniqN_iff_appCase_all`), and `AppCase.AppUniqLvl.iff` identifies that with `∀ n, AppUniqLvl`. The guarded form is *weaker* than the unguarded one, so the equivalence is at the unguarded level and the guarded link's exact price is unmeasured |
| bottom | `AppUniqLvl (∅ : VEnv) 0 1` | **open**, and `AppUniqWF.no_wf_hypothesis_avoids_empty` shows no consequence of `VEnv.WF` reaches above it |

Two side facts checked while walking this, both bearing on the chain and neither changing the
verdict: `RegPiSat.regPi_false` shows `PropConv.RegPi` — the side condition
`PropAgreeGuarded`'s §1 assembly needs — is not merely unproved but **false at every
environment**, with `RegPiOn` the satisfiable repair and `propTypeAgreeOn_of_residuals` the
re-priced assembly; and the three `AppUniqRefute` refutations of `PropUniqN`/`PropUniqNOn` are at
`piLvlEnv`, an `Ordered` non-`WF` environment, so by antitonicity they refute nothing at `∅`.

### M8 — bare build, guards, census (on this file plus the doc, nothing else touched)

`lake build`: **Build completed successfully (1675 jobs)** — 1674 before, +1 for
`Lean4Lean.Theory.Typing.PropAtWF`. Guards, verbatim:

* `guard 1: Axioms.lean declares exactly the 24 frozen axioms ✓`
* `guard 2: kernel_sound axioms within whitelist ✓ (proof INCOMPLETE: sorryAx present)`
* `guard 3: checker cone implementation gaps within frozen list (2/2 remaining) ✓`

Census: `TOTAL declarations directly containing sorryAx: 13` — unchanged; my file adds no hole and
its 13 declarations audit as `[propext]` or `[propext, Quot.sound]`. **No warnings** from
`PropAtWF.lean` (its only build output is the `#print axioms` info lines).

## §3 Scorecard

| Q | prediction | verdict |
| --- | --- | --- |
| Q1 — does anything conclude the target from `VEnv.WF` alone? | no | **WRONG**: `VEnv.WF.propTypeAgreeOn` does, from `VEnv.WF` and nothing else — and it is **circular** (cone → `IsDefEqU.forallE_inv_stratified`, via the watched `IsDefEq.uniq`/`uniqU`). The half of the prediction that held is that head `PropAgreeOn` alone is an incomplete query: three names denote the statement, and only the third finds it |
| Q2 — the relayed lemma's real statement | hole-free, `Ordered`, `U = 0` | **HELD**, exactly; `U = 0` is a limit the relay did not carry |
| Q3 — stratified hypothesis at `VEnv.WF` hole-free? | no; it is the obstruction | **HELD**: 0 hits for either `∀ n` form co-headed with `VEnv.WF`; unconditional instances at index 0 only |
| Q4 — monotonicity, and is the answer a refutation? | antitone, `∅` is the necessary condition, no refutation expected | **HELD**, and now proved for `PropAgreeOn` itself (`PropAgreeOn.mono_env`, `.mono_univs`) rather than inherited from the `app`-case family |

## §4 Method gaps in this round

1. **The alias problem is only empirically closed.** I established that exactly three definitions in
   the tree denote the target by scanning source for `Prop`-valued `def`s whose body mentions
   `OnCtx`, `HasType` and `VLevel.eval`. That is a *source* scan, so it would miss a predicate
   assembled from other definitions (a `structure` field, or a `def` built out of `IsPropN`), which
   is exactly the failure mode `shape.lean`'s own docstring warns about. A conclusion-shape query
   cannot see a `Prop`-valued definition at all.
2. **`PropTypeAgreeNOn`'s direction is unmeasured.** I showed the antitone argument does not apply
   (its conclusion mentions `env`) and did *not* build a witness either way. So "the chain's link A
   does not descend to `∅`" is an argument about the statement's shape, not a theorem.
3. **The `∅` bound is one-way and I proved no strictness.** `PropAgreeOn (∅ : VEnv) U` could in
   principle be strictly weaker than the `VEnv.WF`-quantified target; exhibiting a `VEnv.WF`
   environment that satisfies the first and refutes the second would need a ¬-conversion technique
   the tree does not have (`docs/handoff-injcensus.md` §V3).
4. **I did not attempt `PropAgreeOn (∅ : VEnv) 0`.** Having named it as the single weakest
   hypothesis in the family, I stopped there; whether the pure fragment's unique-typing bit is
   provable at `∅` is the next round's question, not this one's answer.

## §5 The one-sentence answer

**No** — `env.PropAgreeOn U` is **not** derivable from `VEnv.WF env` alone hole-free: the only
`VEnv.WF`-only derivation in the tree (`VEnv.WF.propTypeAgreeOn`) is circular through
`IsDefEqU.forallE_inv_stratified`, and the hole-free route
(`propAgreeOn_of_stratifiedNOn`) is blocked at its stratified hypotheses above index 0 — which by
`PropAgreeOn.mono_env` / `no_wf_hypothesis_avoids_empty_propAgreeOn` sit at the **empty**
environment, where the `VEnv.WF` hypothesis is worth nothing. So the `proofIrrel` route into
`PiInv` is **not** closed at `VEnv.WF`, and the single statement that would close its *entry* is
`PropAgreeOn (∅ : VEnv) 0`.
