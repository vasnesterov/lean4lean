# Handoff: strengthening — `IsDefEqU.weakN_iff`

**Target:** the forward (strengthening) direction of `Lean4Lean.VEnv.IsDefEqU.weakN_iff`,
`Theory/Typing/UniqueTyping.lean:172`.  **Still open. Not proved, not refuted.**

Marks, kept strictly separate throughout:
**[machine-checked]** = a named `sorry`-free Lean declaration in this tree;
**[measured]** = a machine run whose output is reproduced here;
**[read]** = read off source; **[analysis]** = neither.

This pass **took route 1** of the previous revision's §2.3 (axiom conservativity) and built it:
`Theory/Typing/StrengthenAxiom.lean`, **56 declarations, 0 `sorryAx`-tainted** [measured].
It also **corrected route 1's price in three places** and found one **new structural fact**
about the residual that the sketch did not contain.  Read §0 first.

---

## 0. The six things to know before touching this

0. **Route 1 is built and the reduction is machine-checked.**  The chain is

       AxiomConservativityUninhab → Strengthening1Uninhab → Strengthening1 → StrengtheningTarget

   `AxiomConservativityUninhab.target` **[machine-checked, sorry-free]**, axioms
   `[propext, Classical.choice, Quot.sound]`.  `StrengtheningTarget` is the hole's own
   statement (`Strengthen.lean` §10).
1. **The residual is now: adding an axiom whose type has *no inhabitant* is conservative.**
   Not merely "adding an axiom".  §12 of `Strengthen.lean` confines the target to uninhabited
   context entries; `hasType_appCtx` transports that to the Π-closure, so the declared
   constant may be assumed empty.  Equivalently, and this is the sharpest framing this corner
   has reached: **a `VEnv.WF` environment with no model is conservative over its base for
   conversion.**  (`env'` really is `VEnv.WF` when `env` is — `VDecl.WF.axiom`.  If the
   axiom's type is empty in every model, `env'` has none. **[analysis]**)
2. **New, and not in the previous revision's sketch: the residual is an axiom *scheme*.**
   `VConstant.WF env ci` is `env.IsType ci.uvars [] ci.type`, so a constant whose type
   mentions the ambient universe parameters *must* be declared with `ci.uvars = U`; and
   `constDF` then admits `.const c ls` at **every** level list `ls` of length `U`, each
   inhabiting a different type `ci.type.instL ls`.  One context entry supplies one such
   instance.  So `AxiomConservativity` is **a priori stronger** than the target, and the
   reduction is proved **one direction only**. **[read + analysis]**
3. **Route 1's price was mis-stated.**  The previous revision priced it as "a Π-closure
   construction over a context plus its typing lemma; nothing like it is in
   `Theory/Typing/`".  Measured against the build: the Π-closure typing
   (`isType_mkForallCtx`) is **four lines**.  The real costs were three things the sketch did
   not name — the application spine (`appCtx`, `hasType_appCtx`, turning on
   `VExpr.instN_bvar0`), **fresh names** (§4 below), and the `c`-freeness side conditions.
4. **Prior art was missed, and it was one rename away from the un-importable-modules trap.**
   `VExpr.ConstsIn`, `CtxConstsIn`, `IsDefEq.constsIn` and `Ordered.constsIn` **already exist**
   in `Theory/SetModel/Consts.lean` — whose own header says they "would be at home in
   `Theory/Typing/Lemmas.lean`".  They were written independently here first and caught by a
   name scan, not by reading.  That file imports only `Theory/Typing/Lemmas.lean`, so it is
   imported instead; only `ctxConstsIn_of_onCtx` was genuinely missing. **[measured]**
5. **Everything in §§0–7 of the previous revision that is not corrected here still stands** —
   in particular `HeadReduction.lean` cannot deliver (§4), `church_rosser`'s refutation is
   *conditional* (§5.1), and no model argument reaches the residual (§3).

---

## 1. What landed this pass — `Theory/Typing/StrengthenAxiom.lean`

All sorry-free; the module was scanned exhaustively (**56 declarations, 0 containing
`sorryAx` in their transitive closure**) rather than spot-checked. **[measured]**

| name | statement |
|---|---|
| `ctxConstsIn_of_onCtx` | a well-formed context mentions only declared constants |
| `mkForallCtx` | Π-closure of a term over its context (`def`) |
| `isType_mkForallCtx` | **the Π-closure of a well-formed entry is a closed type** |
| `VExpr.appCtx` | a closed term applied to a context's own variables (`def`) |
| `hasType_appCtx` | **an inhabitant of the closure gives an inhabitant of the entry** |
| `Ordered.consts_finite` | an `Ordered` environment declares finitely many constants |
| `exists_name_not_mem` | `Name` is infinite |
| `Ordered.exists_addConst` | **an `Ordered` environment always admits one more axiom** |
| `Ctx.LiftN.exists_instN_typed` | `exists_instN` carrying `OnCtx Γ₀` and `IsType Γ₀ A₀` |
| `AxiomConservativity` | the residual (`def`) |
| `AxiomConservativityUninhab` | **the sharpened residual: the axiom's type is empty** (`def`) |
| `AxiomConservativity.uninhab` | the sharpened residual is the weaker obligation |
| `AxiomConservativityUninhab.strengthening1Uninhab` | **the reduction, core step** |
| `AxiomConservativityUninhab.target` | **the reduction to the hole's own statement** |
| `AxiomConservativity.target` | the same from the unsharpened residual |
| `strengtheningTarget_of_allClosedInhabited` | **the vacuity dual** (see §2.2) |
| `VEnv.addConst_ne` | `addConst` always changes the environment (collapse test, §2.3) |
| `axiomConservativity_fires` | non-vacuity: the constant occurs in the derivation |
| `appCtx_fires` | the construction fires at a real Π and a real application |

**Non-circularity.**  Nothing in the file mentions `IsDefEqU.weakN_iff`; it imports
`Strengthen.lean` (which does not either) and `SetModel/Consts.lean`. **[measured]**

### 1.1 The construction, in one paragraph

Given `Ctx.LiftN 1 k Γ Γ'` and `OnCtx Γ'`, `exists_instN_typed` splits `Γ'` into the entry
`A₀` and the context `Γ₀` below it, *with* their well-formedness, and quantifies the
substituted term **inside** the existential — which is what lets the inhabitant be built from
`Γ₀` afterwards (the previous `exists_instN` took `e₀` as a parameter, so `Γ₀` was not
available before `e₀` had to be chosen).  `mkForallCtx Γ₀ A₀` is then a closed type;
`Ordered.exists_addConst` declares it at a fresh name `c` with `uvars = U`;
`hasType_appCtx` turns `c` applied to `Γ₀`'s own variables into an inhabitant of `A₀` over
`Γ₀`; and `IsDefEqU.strengthen_of_instN` (`Strengthen.lean` §1) closes the strengthening over
`env'` outright.  All that is left is to come back down to `env`.

---

## 2. The residual, priced honestly

### 2.1 What is *not* proved: the converse

`StrengtheningTarget → AxiomConservativity` is not proved, and it is not free.  The natural
translation replaces `.const c ls` by a context variable, but by §0.2 a derivation may use
`.const c ls` at many `ls`.  A derivation is a finite object, so it mentions finitely many
level lists and the translation would land in a context extended by finitely many entries,
which `StrengtheningTarget` iterates over — so the two are *probably* equivalent.  **[analysis]**
What blocks writing it down:

* `Theory/Typing/ConstSubst.lean` transports a judgement along a constant substitution, but
  its `CSubst.WF.val` field demands the value **inhabit** the constant's type — precisely
  what is missing here — and its `closed` field demands the values be closed, which a
  context variable is not. **[read]**
* Nothing in the tree extracts the level lists occurring in a derivation. **[read]**

So the honest label is **reduction, direction proved one way only**, and the residual is
a priori stronger than the target.

### 2.2 Non-vacuity, and the vacuity dual

* `axiomConservativity_fires` **[machine-checked]**: over `VEnv.empty` extended by
  `c : Prop`, the `c`-free endpoints `Sort 0`, `Sort 0` are joined by a `trans` whose middle
  term is *not* `c`-free.  That is the only shape in which the residual has content, and the
  witness carries the `¬ ConstsIn` conjunct explicitly so it cannot degenerate.
* For `AxiomConservativityUninhab` **no witness can be exhibited here**, for the same reason
  `Strengthening1Uninhab`'s cannot: showing a closed type has no inhabitant over a `VEnv.WF`
  environment is itself open in this tree (`VEnv.Consistent` is a `def`; `leanTTConsistent`
  is proved nowhere). **[read]**  *"No witness" is not evidence of truth.*
* What is available is the dual, `strengtheningTarget_of_allClosedInhabited`
  **[machine-checked]**: **if every closed well-formed type over `env` were inhabited, the
  target would already be proved.**  So the sharpened residual is vacuous **iff** the target
  holds.  This is `Strengthen.lean` §12's `strengtheningTarget_of_allInhabited` moved from
  context entries to closed types, which is where route 1 puts the difficulty.

### 2.3 Collapse test (working rule 5)

The residual relates two judgements *in the same context over two different environments*;
the target relates two judgements *in the same environment over two different contexts*; and
the two environments are always distinct (`VEnv.addConst_ne`, **[machine-checked]** — an
`addConst` succeeds only at an undeclared name and then declares it).  There is no
instantiation of `c`, `ci`, `env'` that degenerates the residual's premise into the target's.
So this is not the shape §8 of `Strengthen.lean` turned out to be.

### 2.4 Why route 1 and not route 2

Route 2 (reduce to `k = 0` by λ-abstracting the prefix) was **not** attempted.  Its stated
payoff is "a future reduction relation would only have to deal with `Γ' = T :: Γ`", and this
document's §4 and §6 (previous revision, unretracted) establish that **no reduction relation
is coming**: `ChurchRosser.lean` is circular through the `weakN` family and
`HeadReduction.lean`'s only conversion⟹reduction bridges are `church_rosser` calls.  A
reduction whose consumer does not exist is not worth its de Bruijn bill.  Route 1 by contrast
moves the difficulty to *environments*, which is where the tree's transport machinery
(`IsDefEq.mono`, `instL`, `ConstSubst`, `Enlarged`) and its pathological witnesses
(`CycleConv.propLoopEnv`, `MutualDefUnsound`) already live. **[analysis]**

---

## 3. Where the target stands, after this pass

The hole is **equivalent** to each of (all sorry-free, inherited unless marked):

* `TransStrengthening` — its own `trans` case (`StrengtheningTarget.iff_trans`);
* `Strengthening1` — the same at a single stripped entry;
* `Strengthening1Uninhab` — the same at a single **uninhabited** entry;

and is **implied by** (new this pass, one direction only, §2.1):

* `AxiomConservativity` — conservativity of adding one axiom;
* `AxiomConservativityUninhab` — conservativity of adding one **empty** axiom.

Its *reflexive instance* is equivalent to `PiDescend` alone (inherited,
`TypingStrengthening.iff_piDescend`, `sorryAx` via `forallE_inv`).

### 3.1 The crux, unchanged  **[analysis]**

Every route bottoms out in: *can an extra hypothesis — a context entry, or now an empty
axiom — make two terms convertible when they are not convertible without it?*  The previous
revision's §2.1 reduction of `proofIrrel` and of `PiDescend`'s open cases to that question
stands verbatim, and so does §2.2's table of five refutation attempts, all of which collapse
to the same crux.  Route 1 does not dissolve it; it restates it without de Bruijn indices and
over a *closed, rigid* symbol.

---

## 4. Fresh names: the cost route 1's sketch omitted

To declare an axiom you must have a name nobody used.  `VEnv.constants` is a total function
`Name → Option VConstant`, so this is not free; it needs

* `Ordered.consts_finite` — an `Ordered` environment declares finitely many constants.  This
  is a **three-case induction** (`empty`, `const`, `defeq`), and it is cheap *only because
  `Ordered` is generated by single `addConst`s*.  The same statement over `VEnv.WF` would
  have to handle `addQuot`, `addInduct'`, `addConsts` and `addDefEqs`, and would have been a
  significant detour.  Taking the theorem at `Ordered` and paying `VEnv.WF.ordered` at the
  boundary is what kept this to fifteen lines. **[read + machine-checked]**
* `exists_name_not_mem` — `Name` is infinite, by the max-of-the-numeric-tails trick.

---

## 5. Routes attempted across all passes, and the exact step each failed at

| route | failed at |
|---|---|
| direct induction on `IsDefEqU` | `trans`, and `trans` **is** the statement. **[machine-checked]** |
| "prove the typed form instead" | same `trans`; inter-derivable (`Strengthening.iff_typed`). **[machine-checked]** |
| a *propagated* restatement | makes `trans` free, needs a coherence clause whose base case is the target. **[analysis]** |
| Church–Rosser (`ChurchRosser.lean`) | four declarations circular through the `weakN` family; `NormalEq.descend` has three refuted branches; `CRStatement` conditionally refuted. **[measured]** |
| `HeadReduction.lean` | its only conversion⟹reduction bridges are `church_rosser` calls; nothing clean in the file connects the two. **[measured]** |
| model side (`Theory/SetModel/`) | vacuous over an uninhabited entry — a theorem about the residual. **[machine-checked]** |
| `VExpr.Skips` / `IsDefEq.skips` | downstream of the hole, not toward it. **[read]** |
| refutation by counterexample | five mechanisms traced, all collapse to the crux. **[analysis]** |
| substitution (inhabited entry) | **succeeds**, and covers the target's general `n`. **[machine-checked]** |
| induction on `HasTypeStrong` (reflexive instance) | **succeeds**; residual `PiDescend`. **[machine-checked]** |
| `OnCtx Γ` from `OnCtx Γ'` inside the development | **succeeds**, non-circularly. **[machine-checked]** |
| **route 1: axiom conservativity** | **succeeds as a reduction** (`AxiomConservativityUninhab.target`); the residual is open, and its converse is unbuilt (§2.1). **[machine-checked, new]** |
| route 2: reduce to `k = 0` | **not attempted**, and deliberately — §2.4. |

**Do not re-attempt**: a direct conversion induction; the typed form; a model argument;
`skips`; re-deriving `Strengthening` from `TransStrengthening`-shaped residuals; a standalone
`PiDescendNeutral → PiDescend` (a tautology); the `_fires`-style tautological witnesses
`StrengthenWitness.lean` §2 records; and **re-deriving `ConstsIn`** (§0.4).

---

## 6. Measurements this pass

* `scripts/sorry-census.lean`: **TOTAL 19**, unchanged; `IsDefEqU.weakN_iff` **57 transitive
  users**, unchanged.  A reduction discharges nothing, so *before = after* on both numbers,
  and any claim to the contrary would be wrong. **[measured]**
* `Theory/Typing/StrengthenAxiom.lean`: 56 declarations, **0** with `sorryAx` in their
  transitive closure (module-wide scan, theorem values read explicitly). **[measured]**
* Name-collision scan over every identifier introduced: after importing
  `SetModel/Consts.lean`, **zero** collisions with the rest of `Lean4Lean/`. **[measured]**
* `Theory/Typing/ChurchRosser.lean` was red for part of this pass (unrelated: an inductive
  gained a `keta` constructor elsewhere) and was green again by the end.  It was not touched.

---

## 7. What to pick up first

1. **Settle whether route 1's residual is equivalent or strictly stronger** by building the
   **`const`-to-variable translation** (§2.1).  It is the third environment transport
   `ConstSubst.lean`'s header says the tree lacks — `mono` only adds constants, `instL` does
   not touch them, `CSubst` needs them inhabited — and it is reusable well beyond this
   corner.  Price: an induction over `IsDefEq`'s twelve rules with a de Bruijn shift under
   binders, plus extraction of the finitely many level lists in a derivation.
2. **Or attack `AxiomConservativityUninhab` directly**, in its §0.1 framing: a `VEnv.WF`
   environment with no model is conservative over its base for conversion.  The tree already
   has WF-but-pathological environments (`CycleConv.propLoopEnv`, `MutualDefUnsound`) — but
   note they are pathological by adding **defeqs**, and an axiom adds none, so they are
   evidence about a different mechanism and cannot be reused directly as counterexamples.
3. **`PiDescend`** (equivalently the reflexive instance) is unchanged and still open; two of
   its five cases close from `sort_forallE_inv`, the `.forallE` case needs the target.
4. **Do not** spend time on `HeadReduction.lean` or `ChurchRosser.lean` (§5).

---

## 8. Files

* `Lean4Lean/Theory/Typing/StrengthenAxiom.lean` — **new**, 56 declarations, all sorry-free.
* `Lean4Lean/Theory/Typing/Strengthen.lean` — **unchanged** (755 lines); §§1–12 as before.
* `Lean4Lean/Theory/Typing/StrengthenWitness.lean` — **unchanged**.  Its §2 `_fires` theorems
  are tautologies (its own header says so); quote §3's `_premises` theorems.
* `Lean4Lean/Theory/Typing/UniqueTyping.lean` — **unchanged**; the `sorry` at `:172` stands.
* `Lean4Lean/Theory/SetModel/Consts.lean` — **read-only**, now imported by the new file.
