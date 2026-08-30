# Handoff: strengthening — `IsDefEqU.weakN_iff`

**Target:** the forward (strengthening) direction of `Lean4Lean.VEnv.IsDefEqU.weakN_iff`,
`Theory/Typing/UniqueTyping.lean:174`.  **Still open. Not proved, not refuted.**

Marks, kept strictly separate throughout:
**[machine-checked]** = a named `sorry`-free Lean declaration in this tree;
**[measured]** = a machine run whose output is reproduced here;
**[read]** = read off source; **[analysis]** = neither.

Two rounds are recorded.  §0–§3 are **this** round (the "decide it" round: verdict, the
reference finding, the first positive instance, one killed attack).  §4–§8 are the previous
round's `ConstVar.lean` results, which stand unchanged and are still the reason the axiom
form is the hole rather than a route to it.

---

## 0. The verdict

**Not decided.**  The statement was neither proved nor refuted, and no witness was found.
*"No witness is not evidence of truth."*  What this round adds is three things that were not
in the tree, all machine-checked, plus one finding from outside it.

0. **The reference has this statement, and its proof of it does not go through.**
   `~/lean-type-theory/typesys.tex:88–89` — `thm:weak` parts (3) and (4) — are exactly
   strengthening:

   > (3) If `Γ,Δ ⊢ e : α` and `FV(e) ⊆ Γ` then `Γ ⊢ e : α`.
   > (4) If `Γ,Δ ⊢ e ≡ e'` and `FV(e) ∪ FV(e') ⊆ Γ` then `Γ ⊢ e ≡ e'`.

   `typesys.tex:95` proves them "by mutual induction on the first hypothesis".  **That
   induction cannot work**: the reference's conversion judgment carries an explicit
   transitivity rule with an arbitrary middle term (`axioms.tex:33`,
   `Γ ⊢ e₁ ≡ e₂ → Γ ⊢ e₂ ≡ e₃ → Γ ⊢ e₁ ≡ e₃`), and the hypothesis constrains `FV(e₁)` and
   `FV(e₃)` only, so neither induction hypothesis applies.  `VEnv.Strengthening.iff_trans`
   **[machine-checked, `[propext]` only]** is the sharp form: the `trans` case **is** the
   statement.  **[read, on the reference; machine-checked, on the tree]**

   Scope, stated in registers: the reference's (3)/(4) strip a **suffix** (de Bruijn `k = 0`);
   `weakN_iff` also strips an entry from the **middle** (general `k`).  The gap is in the
   proof as written, not a counterexample — this is a **proof gap in the published
   reference**, not a refutation of it, and there is nothing to file.  It does settle one
   thing: the hole is not an artefact of this formalisation.

1. **The hole has a positive instance now, and it is the first one.**
   `Theory/Typing/StrengthenVerdict.lean` exhibits a `VEnv.WF` environment at which
   `StrengtheningTarget` — hence `AxiomConservativityUninhabWF`, hence `weakN_iff`'s forward
   direction — **is a theorem**, for every `U` (`exists_univInhabEnv`,
   `exists_univInhabEnv_axiomConservativity`, `[propext, Classical.choice, Quot.sound]`).
   `Strengthen.lean` §12's `strengtheningTarget_of_allInhabited` had **no** environment
   instance anywhere in the tree before this [measured: `grep`, its only occurrences were its
   own statement and one docstring].
2. **A correction to a claim that has been travelling in the briefs.**  The claim is
   *"inconsistent environments make the problem easier — a closed `f : ∀ p, p` inhabits every
   `Prop` entry"*.  The parenthesis does not reach the conclusion.  `∀ p : Prop, p` applies
   only to entries at `.sort .zero`; `Strengthening1Uninhab` quantifies over entries at every
   sort, and `Theory/` has no `False.rec` to lift one **[analysis]**.  So
   `MutualDefUnsound.selfRefDV` and `LogRelRowZero.loopEnv`, both at `uvars = 0` and
   `falseProp`, do **not** discharge the target.  The constant that does is
   `∀ (α : Sort u), α`, which needs a universe parameter — `univDV` in the new file.
3. **The cheapest counterexample shape is dead, at its own witness.**  See §2.

---

## 1. Where the obstruction actually sits, after this round

Every mechanism traced this round bottoms out in **one** place, and it is not a new place:

* `proofIrrel` is the only rule whose side condition asks for a judgement at a **fixed**
  sort (`Γ ⊢ p : .sort .zero`).  It is therefore the only rule at which "what is a
  proposition" can differ between `Γ` and a context extending it.  But for it to relate two
  lifted terms upstairs and not downstairs, those terms must fail to be typeable at a common
  proposition downstairs — which is *typing* strengthening, i.e. `PiDescend`/`SortDescend`,
  i.e. the hole again.  **[analysis]**
* `beta` and `eta` can link a `Γ`-free term to one mentioning the stripped variable, but
  only through a discarded-argument position; making that link *essential* again requires a
  conversion between a `Γ`-free type and a variable-containing one.  **[analysis]**
* `extra` cannot separate the two contexts **at all**: every `VDefEq` a `VEnv.WF`
  environment carries is typed in the *empty* context (`VDefVal.WF`, `VDecl.WF.def`,
  `.unsafeDef`, ι-rules built by `VExpr.mkLams`, `quotDefEq`), so the rule fires in every
  context identically.  **[read]**
* `bvar` is the only genuinely context-sensitive rule, and the terms in question do not
  mention the stripped variable.

So a counterexample must be a *minimal* failure of conversion strengthening whose every
sub-failure is a smaller failure of conversion strengthening — which is the shape of an
induction that works for every rule except `trans`.  That is `Strengthening.iff_trans`,
restated.  **[analysis]**

**The corollary for search strategy, and it corrects the brief.**  The brief says *"No model
argument can reach it: soundness over an uninhabited context is vacuous."*  That is right
about **proving** the target and wrong as a blanket statement.  A refutation needs the
*negative* half — `Γ ⊬ e₁ ≡ e₂` at the **smaller** context, which is not vacuous — and a set
model is exactly the instrument for that.  The vacuity blocks the affirmative direction only.
`Theory/SetModel/` is therefore the right tool for anyone attacking this from the refutation
side, and the wrong one from the proof side.  **[analysis; correction to the brief]**

---

## 2. The attack that was built and killed

**The shape.**  Take `Γ' = .sort .zero :: Γ`.  Then `.bvar 0` is a *variable proposition*
upstairs and is not a proposition downstairs, so `proofIrrel` fires upstairs at a `p` that
downstairs is not even typeable.  To use it one needs two `Γ`-free terms of type `.bvar 0`,
and the cheapest supply is a constant whose declared type is `.bvar 0`.  Such a constant is
impossible in an `Ordered` environment, so the witness could only ever have refuted
`StrengtheningTarget` as an **unqualified** predicate (it is stated without `VEnv.WF env`;
the equivalences supply that separately) — which is still worth having, since it would show
the `WF` hypothesis load-bearing, the way `sortUniq_badEnv` does for `SortUniq`.

**Why it is dead.**  `constOpenType_hasType_any` **[machine-checked, `[propext]`]**: a
constant `c` with `env.constants c = some ⟨0, .bvar 0⟩` satisfies `Γ ⊢ c : e` for **every**
`e` that is inhabited in `Γ`, by one `beta` step —
`(fun (_ : A) => c) e : (.bvar 0).inst e = e`.  So both candidates land at the closed
proposition `∀ (p : Prop), p` **downstairs**, where `proofIrrel` equates them just as well:
`constOpenType_collapse` **[machine-checked]** derives `[] ⊢ c₁ ≡ c₂` outright.  The
separation is zero.  (`allProp_isProp` is the small lemma that `∀ (p : Prop), p` really is a
proposition — `.imax (.succ .zero) .zero ≈ .zero`, closed by `defeqDF`+`sortDF`.)

**What that tells the next attempt.**  The hypothesis that kills it is `Ordered`'s *declared
types are closed*.  Any bad-environment refutation must therefore separate the two contexts
without an open constant type — and `extra` cannot (§1), so `bvar` and `proofIrrel` are the
whole budget.

---

## 3. The positive instance, and exactly how little it proves

`Theory/Typing/StrengthenVerdict.lean`, 14 declarations, all `sorry`-free, all
`[propext(, Classical.choice), Quot.sound]` **[measured]**.

| name | statement |
|---|---|
| `univType`, `univCV`, `univDV` | `univInhab : ∀ (α : Sort u), α := univInhab`, one universe parameter |
| `univType_isType` | its type is a type over any environment |
| `hasType_univInhab_app` | **the universal inhabitant**: `Γ ⊢ .app (.const univInhab [u]) A : A` whenever `Γ ⊢ A : .sort u` |
| `onCtx_levelWF` | a well-formed context is level-well-formed (needed to get `u.WF U`) |
| `strengtheningTarget_of_univInhab` | **any `VEnv.WF` environment declaring `univInhab` satisfies the target**, at every `U` |
| `univInhabDecl_wf` | the `VDecl.WF.unsafeDef` step is well formed wherever the name is free |
| `exists_univInhabEnv` | **the environment exists and is `VEnv.WF`** |
| `exists_univInhabEnv_axiomConservativity` | the same through `ConstVar.lean`'s equivalence |
| `univInhab_no_uninhabited_entry` | **the scope statement** (below) |
| `constOpenType_hasType_any`, `allProp_isProp`, `constOpenType_collapse` | §2 |

**The scope statement is the important half.**  `univInhab_no_uninhabited_entry`
**[machine-checked]** says that at such an environment `Strengthening1Uninhab`'s
uninhabitedness hypothesis is satisfiable at **no** well-formed context.  So the positive
instance lives **entirely inside the case `Strengthen.lean` §1 already closes**, and tests
nothing whatever about the obstruction.  It is a satisfiability witness — the target is not
contradictory at a `VEnv.WF` environment — and nothing more.  Recording it that way is the
point: working rule 4 asks for the obligation to be fired at a witness, and this is the
honest report of what the only available witness covers.

The environment is inconsistent (it inhabits every type), which is the reason it is easy —
and it is the *first* environment for which "inconsistent makes it easier" is more than an
assertion.

---

## 4. The chain of equivalences (previous round, re-verified here)

The hole is **equivalent** to each of these, all `sorry`-free
**[measured, `#print axioms` re-run this round]**:

* `TransStrengthening` — its own `trans` case (`Strengthening.iff_trans`,
  `StrengtheningTarget.iff_trans`);
* `Strengthening1` — the same at a single stripped entry (`Strengthening1.iff_target`);
* `Strengthening1Uninhab` — the same at a single **uninhabited** entry
  (`Strengthening1Uninhab.iff_target`);
* `AxiomConservativityWF` — conservativity of adding one axiom, over a well-formed context
  (`axiomConservativityWF_iff_target`);
* `AxiomConservativityUninhabWF` — the same for an axiom with **no inhabitant**
  (`axiomConservativityUninhabWF_iff_target`), and
  `axiomConservativityWF_iff_uninhabWF`: restricting to uninhabited axioms loses nothing.

It is **implied by** (one direction only, still the only one-directional link left):

* `AxiomConservativity` / `AxiomConservativityUninhab` (`StrengthenAxiom.lean`), which
  quantify over an **arbitrary** context.  The converse fails by exactly one hypothesis:
  `StrengtheningTarget`'s only context hypothesis is `OnCtx Γ'`, and `Γ ++ Ts` cannot be well
  formed unless `Γ` is.  This costs nothing — every use has `OnCtx Γ` in scope.  **[read +
  machine-checked]**

Its *reflexive instance* is equivalent to `PiDescend` alone
(`TypingStrengthening.iff_piDescend`; `sorryAx` via `forallE_inv`).

---

## 5. `ConstVar.lean` — the previous round's transport (unchanged)

666 lines, 79 declarations, **0** with `sorryAx` in their transitive closure, **0** whose
cone contains `weakN_iff` [measured, previous round].  The headline is
`StrengtheningTarget.axiomConservativityWF`: given the target, an axiom added to `env` is
conservative — translate every occurrence of the new constant into a context variable, one
per `≈`-class of level list the derivation uses, and strip those variables again with the
target.

The three decisions that made it small, worth not re-deriving:

* **Quantify over covers, don't extract.**  `cvarMain`'s conclusion is
  `∃ L₂, LWF U L₂ ∧ ∀ L', LWF U L' → LCov L' L₂ → <derivation at L'>`.  Extraction of a
  derivation's level lists is **not expressible** (a derivation is a `Prop`) and **not
  needed**.  Because every term in the conclusion is computed at `L'`, the `trans` case
  instantiates both hypotheses at the same `L'` and the middle terms match on the nose.
* **New entries at the BOTTOM of the context** (`Γ ++ Ts`), so `cvar` is the identity on
  `c`-free terms and the final application is a rewrite, not a computation.
* **`IsDefEq.instL_r`** (`Strong.lean:823`) for the `≈`-class.  `ConstSubst.lean`'s header
  once said level congruence "is not available"; it is, and that file's own body already used
  it.  **Anything a brief tells you is "not available" about level congruence is stale.**

---

## 6. Routes attempted, and the exact step each failed at

| route | failed at |
|---|---|
| direct induction on `IsDefEqU` | `trans`, and `trans` **is** the statement. **[machine-checked]** |
| "prove the typed form instead" | same `trans`; inter-derivable (`Strengthening.iff_typed`). **[machine-checked]** |
| a *propagated* restatement | makes `trans` free, needs a coherence clause whose base case is the target. **[analysis]** |
| Church–Rosser (`ChurchRosser.lean`) | four declarations circular through the `weakN` family; `NormalEq.descend` has three refuted branches. **[measured]** |
| `HeadReduction.lean` | its only conversion⟹reduction bridges are `church_rosser` calls. **[measured]** |
| model side (`Theory/SetModel/`) | vacuous over an uninhabited entry — for the **proof**. For a **refutation** it is the right tool (§1). **[machine-checked / analysis]** |
| `VExpr.Skips` / `IsDefEq.skips` | downstream of the hole, not toward it. **[read]** |
| route 1: axiom conservativity, and its converse | **succeeds as an equivalence** (`ConstVar.lean`) — the residual *is* the hole. **[machine-checked]** |
| substitution (inhabited entry) | **succeeds**, covers the target's general `n`. **[machine-checked]** |
| induction on `HasTypeStrong` (reflexive instance) | **succeeds**; residual `PiDescend`. **[machine-checked]** |
| **λ-form** — "`λ(_:A).e₁ ≡ λ(_:A).e₂` implies `e₁ ≡ e₂`" | reduces the hole to one conversion at `k = 0`, and **the reduction of general `k` to `k = 0` needs typed λ-inversion**, i.e. `forallE_inv` (a `sorry` with 105 users).  `HasType.lam_inv` (`Strong.lean:904`) gives only `∃ B`, and moving the *equation* from the IH's type to `∀A.B` needs `IsDefEq.uniq`, which is `sorryAx`-tainted **[measured]**.  **Abandoned as tainted, not as wrong.** **[analysis, new]** |
| **`Stratified` (Carneiro's `⊢ₙ`)** | still has an explicit `trans` at `n+1` with an arbitrary middle term (`Stratified.lean:87`); the index drops only the *typing* premises.  No trans elimination is available there. **[read, new]** |
| **junk-environment refutation** (`proofIrrel` at a variable `Prop`) | **collapses at its own witness** — §2. **[machine-checked, new]** |
| **junk-*context* refutation** (`StrengtheningTarget` has no `OnCtx Γ`) | `Ctx.LiftN` + `OnCtx Γ'` forces `OnCtx Γ` at `k = 0`, and at general `k` recovering it is `SortDescend` — part of the hole.  No slack. **[analysis, new]** |
| extraction of a derivation's level lists | **abandoned as not expressible**, and **not needed** — §5. **[analysis]** |

**Do not re-attempt**: a direct conversion induction; the typed form; a model argument *for
the proof direction*; `skips`; re-deriving `Strengthening` from `TransStrengthening`-shaped
residuals; a standalone `PiDescendNeutral → PiDescend` (a tautology); the `_fires`-style
tautological witnesses `StrengthenWitness.lean` §2 records; re-deriving `ConstsIn`;
re-deriving level congruence (`IsDefEq.instL_r` is it); the λ-form *as an equivalence*
without `forallE_inv`; and the open-constant-type witness of §2.

---

## 7. Measurements this round

* `scripts/sorry-census.lean`: **TOTAL 19** at the start and **19** at the end [measured].
  Nothing was closed, so before = after; any claim of 18 would be wrong.
* `scripts/dup-names.lean` (default run): **no duplicates** [measured].  A dedicated run
  importing `Verify/Guard` + `Experimental/ConeJoin` + `ConstVar` + `StrengthenVerdict` in one
  file **caught a real collision** — `Lean4Lean.loop_wf` already existed in
  `Theory/Typing/LogRelRowZero.lean` — which was renamed away (`univInhabDecl_wf`), and the
  run then reports **no duplicates** [measured].  This is the fourth time that instrument has
  paid for itself; run it.
* Axioms on the new file's results: `exists_univInhabEnv`,
  `exists_univInhabEnv_axiomConservativity`, `strengtheningTarget_of_univInhab`,
  `univInhab_no_uninhabited_entry` are `[propext, Classical.choice, Quot.sound]` — the choice is
  inherited from `Strengthen.lean`'s closure, not used in the new proofs [measured, not
  attributed to a particular lemma];
  `univInhabDecl_wf`, `hasType_univInhab_app`, `allProp_isProp`, `onCtx_levelWF`,
  `constOpenType_collapse` are `[propext, Quot.sound]`; `constOpenType_hasType_any` is
  `[propext]` [measured].
* The previous round's five equivalences re-checked: all `[propext, Classical.choice,
  Quot.sound]`, no `sorryAx` [measured].
* `IsDefEq.uniq` and `IsDefEqU.of_l` **are** `sorryAx`-tainted [measured] — this is what
  ruled the λ-form out; do not assume `UniqueTyping.lean`'s non-`weakN_iff` lemmas are clean.

---

## 8. What to pick up first

1. **Read §0.0.**  The reference's own proof of this statement is gapped at `trans`.  Nobody
   has a proof of strengthening for this system to transcribe; a new argument is required.
2. **If you attack it: the only known routes are normalisation-flavoured** — an untyped
   conversion relation with a back-translation, or a logical relation.  `proofIrrel` blocks
   the first (there is no untyped rewriting relation whose equivalence closure is `IsDefEq`),
   and `LogRelRowZero.headStep_not_wf` blocks the second **at the `VEnv.WF` generality**
   (there is a `VEnv.WF` environment whose head reduction is not well founded).  Anything
   that gets past those two facts is new.
3. **If you refute it: use the model, and use a consistent environment.**  §1's correction.
   A counterexample must (a) live in an environment where `Γ ⊬ e₁ ≡ e₂` can be *established*
   — a set model does that — and (b) separate the contexts using only `bvar` and
   `proofIrrel`, since `extra` cannot and open constant types collapse (§2).
4. **`PiDescend`** — equivalently the reflexive instance — is unchanged and still open, and
   is the cheaper target: refuting it refutes the hole.
5. **Do not** spend time on `HeadReduction.lean` or `ChurchRosser.lean`.
6. Optional and cheap: fold `AxiomConservativityWF` back into `StrengthenAxiom.lean` by
   adding `OnCtx Γ` to `AxiomConservativity` in place (a weakening, safe direction).
   Deliberately not done: working rule 3 prefers a separate predicate, and the copy is 25
   lines.

---

## 9. Files

* `Lean4Lean/Theory/Typing/StrengthenVerdict.lean` — **new this round**, 14 declarations, all
  `sorry`-free.  §1's positive instance, §2's killed attack, and the reference note.
  **No other module imports it** — it is a witness/measurement file — but it *is* built by
  `lake build`, since the `Lean4Lean.Theory` library globs `Lean4Lean.Theory.*` [read,
  `lakefile.toml`], so it cannot rot silently.  It is **not** in `Experimental/ConeJoin`'s
  closure, so check it with the dedicated `dup-names` run in §7, not the default one.
* `Lean4Lean/Theory/Typing/ConstVar.lean` — previous round, unchanged.
* `Lean4Lean/Theory/Typing/{Strengthen,StrengthenAxiom,StrengthenWitness,ConstSubst,ConstSubstNested}.lean`
  — unchanged this round.
* `Lean4Lean/Theory/Typing/UniqueTyping.lean` — unchanged; the `sorry` at `:174` stands.
* Read-only and load-bearing: `Strong.lean` (`IsDefEq.instL_r`, `HasType.lam_inv`),
  `Stratified.lean` (has `trans`), `LogRelRowZero.lean` (`headStep_not_wf`, and the
  `loop_wf` name), `Theory/MutualDefUnsound.lean` (the `unsafeDef` pattern).
