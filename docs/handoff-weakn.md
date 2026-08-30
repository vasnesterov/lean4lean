# Handoff: strengthening — `IsDefEqU.weakN_iff`

**Target:** the forward (strengthening) direction of `Lean4Lean.VEnv.IsDefEqU.weakN_iff`,
`Theory/Typing/UniqueTyping.lean:172`.  **Still open. Not proved, not refuted.**

Marks, kept strictly separate throughout:
**[machine-checked]** = a named `sorry`-free Lean declaration in this tree;
**[measured]** = a machine run whose output is reproduced here;
**[read]** = read off source; **[analysis]** = neither.

This pass built the **`const`-to-variable transport** that the previous revision named as the
thing to pick up first, in `Theory/Typing/ConstVar.lean` (**79 declarations, 0 with `sorryAx`
in their transitive cone, 0 mentioning `weakN_iff`** [measured]).  The headline result is a
**verdict on the open question**, and it corrects the previous revision in three places.
Read §0 first.

---

## 0. The five things to know before touching this

0. **The open question is settled: the residual is EQUIVALENT to the target, not strictly
   stronger** — once its context is required to be well formed.

       AxiomConservativityWF env U  ↔  StrengtheningTarget env U     [machine-checked]
       AxiomConservativityUninhabWF env U  ↔  StrengtheningTarget env U   [machine-checked]
       AxiomConservativityWF env U  ↔  AxiomConservativityUninhabWF env U [machine-checked]

   (`VEnv.axiomConservativityWF_iff_target`, `…UninhabWF_iff_target`,
   `axiomConservativityWF_iff_uninhabWF`, all in `ConstVar.lean` §6–7, axioms
   `[propext, Classical.choice, Quot.sound]`.)  The previous revision's §2.1 —
   "reduction, direction proved one way only", "a priori stronger" — is **superseded**.
1. **The universe-scheme obstruction it named is gone, and it was never the obstruction.**
   §0.2 of the previous revision said `constDF` admits `.const c ls` at *every* level list
   while one context entry supplies one instance, so the residual is an axiom **scheme**.
   True — and handled: the transport puts **one entry per `≈`-class of level list the
   derivation uses**, and `VEnv.IsDefEq.instL_r` makes that entry serve the whole class.
   `lvlIdx_distinguishes` **[machine-checked]** confirms `Sort 0` and `Sort 1` get *different*
   entries, which is the check that would have falsified the construction.
2. **`ConstSubst.lean`'s header was wrong, and its own body already refuted it.**  It said
   `t.instL ls ≡ t.instL ls'` for `ls ≈ ls'` — "congruence of typing under `≈` of universe
   levels" — "is not available".  It **is**: `VEnv.IsDefEq.instL_r` (`Theory/Typing/Strong.lean:823`),
   sorry-free, cone 2325, `weakN_iff` **not** in its cone [measured].  That file's own
   `CSubst.val_of_hasType` (predates this pass, commit `6d89bb5`) already derives `val` from
   plain well-typedness with it.  The header is corrected in this pass; the body is untouched.
   **Anything a brief tells you is "not available" about level congruence is stale.**
3. **What is still open is the same crux, and only the crux.**  `AxiomConservativityWF` —
   *adding an axiom whose type has no inhabitant is conservative*, equivalently *a `VEnv.WF`
   environment with no model is conservative over its base for conversion* — is now known to
   be **exactly** the hole, in both directions.  No model argument reaches it (vacuous over an
   uninhabited entry, a theorem); `proofIrrel` provably cannot be the mechanism of a
   counterexample; inconsistent environments make the problem easier.
4. **One gap remains between `AxiomConservativity` (as `StrengthenAxiom.lean` states it) and
   the target, and it is not the universe scheme.**  `AxiomConservativity` quantifies over an
   **arbitrary** context `Γ`; `StrengtheningTarget`'s only hypothesis is `OnCtx Γ'`, and
   `Γ ++ Ts` cannot be well formed unless `Γ` is.  So the un-`OnCtx` version stays a priori
   stronger, by exactly that hypothesis.  This costs nothing: every use of the residual has
   `OnCtx Γ` in scope (`Strengthening1Uninhab` carries it), which is why
   `AxiomConservativityUninhabWF.strengthening1Uninhab` goes through unchanged. **[read + machine-checked]**

---

## 1. What landed this pass — `Theory/Typing/ConstVar.lean`

666 lines, 79 declarations, **0** with `sorryAx` in their transitive closure, **0** whose cone
contains `weakN_iff` (module-restricted cone scan, theorem values read explicitly, not a
name grep) [measured].

| name | statement |
|---|---|
| `LEqv`, `LWF`, `LCov`, `lvlIdx` | level lists up to `≈`, and the index of a class |
| `lvlIdx_split`, `lvlIdx_congr`, `lvlIdx_lt` | the index points at an `≈`-equivalent entry |
| `VExpr.cvar` | **the translation**: `.const c ls ↦ .bvar (d + Γ.length + lvlIdx L ls)` (`def`) |
| `VExpr.cvar_eq_self` | `cvar` is the **identity on `c`-free terms** |
| `VExpr.cvar_liftN`, `cvar_inst` | `cvar` commutes with lifting and instantiation |
| `cvarCtx`, `cvarTs`, `cvarCtx_split` | the translated context and the new entries |
| `lookup_mid`, `Lookup.appendR`, `lookup_cvarCtx` | the four `Lookup`s the induction needs |
| `VEnv.addConst_spec` | what `addConst` does to `constants` and `defeqs` |
| **`cvarMain`** | **the transport**: a derivation over `env'` becomes one over `env` |
| `VEnv.onCtx_append` | `OnCtx Γ` + closed well-formed `Ts` ⟹ `OnCtx (Γ ++ Ts)` |
| `AxiomConservativityWF`, `AxiomConservativityUninhabWF` | the residual with `OnCtx Γ` (`def`) |
| `AxiomConservativityUninhabWF.strengthening1Uninhab` | route 1, run from the sharpened residual |
| **`StrengtheningTarget.axiomConservativityWF`** | **the converse**, the new direction |
| `axiomConservativityWF_iff_target` | **the equivalence** |
| `axiomConservativityUninhabWF_iff_target` | the same for the uninhabited sharpening |
| `axiomConservativityWF_iff_uninhabWF` | **restricting to uninhabited axioms loses nothing** |
| `cvarMain_needs_entries` | non-vacuity, backed by a lemma (§3) |
| `lvlIdx_distinguishes` | the scheme really gets distinct entries (§3) |
| `cvarTs_liftN_fires` | the target is applied at `n = 1`, not `n = 0` |

### 1.1 The three decisions that made this small

The previous revision priced this route as "an induction over `IsDefEq`'s twelve rules with a
de Bruijn shift under binders, **plus extraction of the finitely many level lists in a
derivation**".  The extraction is **not expressible** — a derivation is a `Prop`, so there is
nothing to recurse over to collect its level lists.  Three choices removed it and two other
costs with it:

* **Quantify over covers, don't extract.**  `cvarMain`'s conclusion is
  `∃ L₂, LWF U L₂ ∧ ∀ L', LWF U L' → LCov L' L₂ → <derivation at L'>`.  The induction
  *produces* `L₂` (the lists its own `constDF`-at-`c` nodes use) and the conclusion is stated
  for every `L'` covering it.  Because every term in the conclusion is computed **at `L'`**,
  the `trans` case instantiates both hypotheses at the *same* `L'` and the middle terms are
  syntactically equal on the nose.  **No coverage predicate on terms, no index-stability
  lemma, and no context weakening are needed anywhere.**  An earlier design that threaded an
  input `L` and grew it needed all three.
* **Put the new entries at the BOTTOM of the context** (`Γ ++ Ts`, indices `d + Γ.length + i`),
  not the top.  Then `cvar` leaves every `bvar` alone, so `cvar` is the **identity on `c`-free
  terms** — which the target judgement's endpoints are — and `Ctx.LiftN.right` +
  `ClosedN.liftN_eq` make the final `StrengtheningTarget` application a rewrite rather than a
  computation.  Top placement would have shifted every variable by `|L|` and made the
  translation depend on `|L|`.
* **`IsDefEq.instL_r` for the `≈`-class.**  `constDF` relates `.const c ls` to `.const c ls'`
  whenever `ls ≈ ls'`, so both must map to the *same* variable, whose type is `ci.type.instL`
  at some representative.  `instL_r` supplies `ci.type.instL ls₁ ≡ ci.type.instL ls` and
  `defeqDF` closes it.  This is the lemma §0.2 says the tree was believed not to have.

Costs that *were* real: `cvar_inst` (the `bvar`/`instVar` case split), `lookup_cvarCtx`, and
`onCtx_append` — none of them hard, all of them mechanical.

### 1.2 The assembly, in one paragraph

`cvarMain henv hadd huv hci hΓc hd [] rfl` translates the whole derivation at depth 0; the
endpoints are `c`-free so `cvar_eq_self` returns them unchanged; `cvarTs ci L₂` is a list of
closed well-formed types (`IsType.instL` at `Γ = []`); `onCtx_append` makes `Γ ++ Ts` a
well-formed context; `Ctx.LiftN.right (CtxWF.closed …) Ts` is the stripping witness; and
`ClosedN.liftN_eq` shows the lift is the identity on the endpoints, so `StrengtheningTarget`
applies directly.

---

## 2. Where the target stands

The hole is **equivalent** to each of (all sorry-free, inherited unless marked **new**):

* `TransStrengthening` — its own `trans` case (`StrengtheningTarget.iff_trans`);
* `Strengthening1` — the same at a single stripped entry;
* `Strengthening1Uninhab` — the same at a single **uninhabited** entry;
* **`AxiomConservativityWF`** — conservativity of adding one axiom, over a well-formed
  context (**new**, both directions);
* **`AxiomConservativityUninhabWF`** — the same for an axiom with **no inhabitant**
  (**new**, both directions).

It is **implied by** (one direction only, and this is now the *only* one-directional link
left in the chain):

* `AxiomConservativity` / `AxiomConservativityUninhab` (`StrengthenAxiom.lean`) — these
  quantify over an arbitrary context; §0.4 gives the exact reason the converse does not go
  through, and it is a single missing hypothesis, not a structural gap.

Its *reflexive instance* is equivalent to `PiDescend` alone (inherited,
`TypingStrengthening.iff_piDescend`, `sorryAx` via `forallE_inv`).

### 2.1 The crux, unchanged **[analysis]**

Every route bottoms out in: *can an extra hypothesis — a context entry, or an empty axiom —
make two terms convertible when they are not convertible without it?*  This pass did not
dissolve it; it **closed the loop around it**, so that anyone attacking the axiom form knows
they are attacking the hole itself and not something stronger.

---

## 3. Non-vacuity and the collapse test

* **Collapse test (working rule 5), forward direction.**  Unchanged: `VEnv.addConst_ne`
  **[machine-checked]** shows `addConst` always changes the environment, so the residual's
  premise cannot degenerate into the target's.  Adding `OnCtx Γ` only weakens the residual, so
  the test carries over.
* **Collapse test, the new direction.**  The one way `StrengtheningTarget →
  AxiomConservativityWF` could be a tautology is if the list `L₂` were always empty, making
  the `Ctx.LiftN` handed to the target the identity.  `cvarMain_needs_entries`
  **[machine-checked]** rules that out *with a lemma, not an example*: at `L' = []` the
  translation of a `c`-headed term is `.bvar Γ.length`, and `IsDefEq.closedN` shows nothing is
  typed at it in `Γ`.  `cvarTs_liftN_fires` exhibits the `n = 1` instance.
* **The scheme is not collapsed.**  `lvlIdx_distinguishes` **[machine-checked]**:
  `¬ LEqv [zero] [succ zero]`, and the two get indices `0` and `1`.  Had `lvlIdx` identified
  `≈`-inequivalent lists, one entry would have been made to serve two different types and the
  construction would be wrong; this is the check that would have caught it.
* **The residual's premises are satisfiable.**  `AxiomConservativityWF` adds `OnCtx Γ` to
  `AxiomConservativity`, and `StrengthenAxiom.axiomConservativity_fires` **[machine-checked]**
  fires the latter at `Γ = []`, where `OnCtx` is trivial — two `c`-free endpoints joined by a
  `trans` through a middle term that is *not* `c`-free.
* **For `…UninhabWF` no witness can be exhibited here**, for the reason `Strengthening1Uninhab`'s
  cannot: exhibiting a closed uninhabited type over a `VEnv.WF` environment is itself open in
  this tree (`VEnv.Consistent` is a `def`; `leanTTConsistent` is proved nowhere) **[read]**.
  The dual is `strengtheningTarget_of_allClosedInhabited` **[machine-checked]**: if every
  closed well-formed type were inhabited the target would already be proved.  So the sharpened
  residual is vacuous **iff** the target holds.  *"No witness" is not evidence of truth* — and
  now `axiomConservativityWF_iff_uninhabWF` says the sharpening loses nothing either way.

---

## 4. Routes attempted, and the exact step each failed at

| route | failed at |
|---|---|
| direct induction on `IsDefEqU` | `trans`, and `trans` **is** the statement. **[machine-checked]** |
| "prove the typed form instead" | same `trans`; inter-derivable (`Strengthening.iff_typed`). **[machine-checked]** |
| a *propagated* restatement | makes `trans` free, needs a coherence clause whose base case is the target. **[analysis]** |
| Church–Rosser (`ChurchRosser.lean`) | four declarations circular through the `weakN` family; `NormalEq.descend` has three refuted branches. **[measured]** |
| `HeadReduction.lean` | its only conversion⟹reduction bridges are `church_rosser` calls. **[measured]** |
| model side (`Theory/SetModel/`) | vacuous over an uninhabited entry — a theorem about the residual. **[machine-checked]** |
| `VExpr.Skips` / `IsDefEq.skips` | downstream of the hole, not toward it. **[read]** |
| refutation by counterexample | five mechanisms traced, all collapse to the crux. **[analysis]** |
| substitution (inhabited entry) | **succeeds**, covers the target's general `n`. **[machine-checked]** |
| induction on `HasTypeStrong` (reflexive instance) | **succeeds**; residual `PiDescend`. **[machine-checked]** |
| route 1: axiom conservativity | **succeeds as a reduction**. **[machine-checked]** |
| **route 1's converse: `const`-to-variable transport** | **succeeds** (`ConstVar.lean`) — the residual is the hole. **[machine-checked, new]** |
| route 2: reduce to `k = 0` | **not attempted**, and deliberately — no reduction relation is coming. |
| extraction of a derivation's level lists | **abandoned as not expressible**, and **not needed** — §1.1. **[analysis, new]** |

**Do not re-attempt**: a direct conversion induction; the typed form; a model argument;
`skips`; re-deriving `Strengthening` from `TransStrengthening`-shaped residuals; a standalone
`PiDescendNeutral → PiDescend` (a tautology); the `_fires`-style tautological witnesses
`StrengthenWitness.lean` §2 records; re-deriving `ConstsIn` (it is in
`Theory/SetModel/Consts.lean`); **and re-deriving level congruence — `IsDefEq.instL_r` is it.**

---

## 5. Measurements this pass

* `scripts/dup-names.lean` (default run): **no duplicates** [measured].  That run does *not*
  import `ConstVar.lean`; a dedicated run importing `Verify/Guard` + `Experimental/ConeJoin` +
  `ConstVar` in one file was made and also reports **no duplicates**, which additionally proves
  `ConstVar.lean` is importable alongside the whole joined cone [measured].
* `scripts/sorry-census.lean`: **TOTAL 19**, unchanged.  A reduction or an equivalence
  discharges nothing, so *before = after*, and any claim to the contrary would be wrong.
* **User counts, stated carefully.**  The brief for this pass said `weakN_iff` had **57**
  transitive users; the census at the start of this session said **59** [measured] and at the
  end **61** [measured].  Every hole's count moved (`TrProj.uniq` 72→74,
  `forallE_inv_stratified` 241→246), and **`ConstVar.lean` contributes 0** — a module-restricted
  cone scan reports 0 of its 79 declarations with `weakN_iff` in their cone and 0 with
  `sorryAx` [measured].  Attribution of the +2 to the other streams' commits that landed
  mid-session (`cc03153`, `3b3b946`, …) is **inferred, not measured**.
* Axiom check on the new results: `cvarMain`, `StrengtheningTarget.axiomConservativityWF`,
  `axiomConservativityWF_iff_target`, `axiomConservativityUninhabWF_iff_target`,
  `axiomConservativityWF_iff_uninhabWF`, `AxiomConservativityUninhabWF.target` — all
  `[propext, Classical.choice, Quot.sound]`; `AxiomConservativityUninhabWF.strengthening1Uninhab`
  and `cvarTs_liftN_fires` need only `[propext, Quot.sound]` [measured].
  (`lvlIdx` is `noncomputable` — it decides `≈`, which is function equality — hence
  `Classical.choice` throughout.  Nothing else uses choice.)
* `IsDefEq.instL_r` cone: 2325 declarations, **no `sorryAx`**, **no `weakN_iff`** [measured].

---

## 6. What to pick up first

1. **`AxiomConservativityUninhabWF` is now the whole problem.**  In its sharpest framing: *a
   `VEnv.WF` environment with no model is conservative over its base for conversion.*  It is
   not "a route" any more — it is the hole, in both directions.  Attack it or refute it.
2. **If you attack it, the tree's pathological environments are the wrong shape.**
   `CycleConv.propLoopEnv` and `MutualDefUnsound` are pathological by adding **defeqs**; an
   axiom adds none.  They are evidence about a different mechanism.
3. **`ConstVar.lean` is reusable well beyond this corner.**  It is the fourth environment
   transport (`mono` adds, `instL` re-levels, `CSubst` replaces a constant by an *inhabitant*,
   `cvar` replaces it by a *variable*).  Anything that needs to remove a constant with no
   inhabitant — e.g. an auxiliary constant in a staging environment that is never populated —
   can use `cvarMain` directly; its only hypotheses are `Ordered env`, `addConst`, `ci.WF env`,
   `ci.uvars = U` and `CtxConstsIn (· ≠ c) Γ`.
4. **Optional, cheap, and tidying**: fold `AxiomConservativityWF` back into
   `StrengthenAxiom.lean` by adding the `OnCtx Γ` hypothesis to `AxiomConservativity` and
   `AxiomConservativityUninhab` in place (a *weakening*, safe direction), which would make
   `ConstVar.lean` §6's two definitions and the copied `strengthening1Uninhab` proof
   redundant.  Deliberately **not** done here: working rule 3 says define a separate predicate
   rather than edit a machine-checked one in place, and the copy is 25 lines.
5. **Do not** spend time on `HeadReduction.lean` or `ChurchRosser.lean`.
6. **`PiDescend`** (equivalently the reflexive instance) is unchanged and still open.

---

## 7. Files

* `Lean4Lean/Theory/Typing/ConstVar.lean` — **new**, 666 lines, 79 declarations, all sorry-free.
* `Lean4Lean/Theory/Typing/ConstSubst.lean` — **header corrected only** (§0.2); no code change.
* `Lean4Lean/Theory/Typing/StrengthenAxiom.lean` — **§6 prose corrected only** (the paragraph
  claiming the converse is unbuilt and the residual a priori stronger now points at
  `ConstVar.lean`); no code change, no definition change.
* `Lean4Lean/Theory/Typing/Strengthen.lean` — **unchanged** (755 lines).
* `Lean4Lean/Theory/Typing/StrengthenWitness.lean` — **unchanged**.
* `Lean4Lean/Theory/Typing/UniqueTyping.lean` — **unchanged**; the `sorry` at `:172` stands.
* `Lean4Lean/Theory/Typing/Strong.lean` — **read-only**; `IsDefEq.instL_r` at `:823` is the
  lemma this pass turned out to depend on.
