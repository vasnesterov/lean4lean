# Handoff: the K-like rule — what it is, what it repairs, and what it does not

**Task.** Add the K-like reduction rule to `Theory/`'s pattern machinery, faithful to
`Lean4Lean/Inductive/Reduce.lean`'s `toCtorWhenK` and to Carneiro's `K⁺`
(`~/lean-type-theory/unique.tex:103`); say precisely where the two differ; re-derive what the
missing rule was blocking (`NormalEq.descend` at a *registered* pattern); settle the flagged
`Quot`-over-`Prop` question; re-price the alignment step.

Marks, kept strictly separate throughout:
**[machine-checked]** = a named `sorry`-free Lean declaration in this tree;
**[measured]** = a machine run whose output is reproduced;
**[read]** = read off source (`~/lean4/src/kernel`, `~/lean-type-theory`, or this tree);
**[analysis]** = neither.

---

## 0. The verdict, first

1. **The rule is landed, abstractly**: `Lean4Lean/Theory/Typing/KRule.lean` (new), `KStep`.
   It is stated **at the rule table `Pat`, not at "SS inductive"**, which is the one place
   this tree can and should improve on the reference — see (5). **[machine-checked]**

2. **It is admissible.** `KStep.defeq`: every `K⁺` step is already an `IsDefEqU`. So adding the
   rule to `ParRed` does not enlarge `IsDefEq`, and `kernel_sound`'s statement is untouched.
   **[machine-checked, `sorryAx`-tainted through exactly one hole — §1.2]**

3. **Three rule sets, three different strengths, all measured.** `Theory/` (before this
   session) had no K rule at all; the C++ kernel and `Reduce.lean` have one only for
   *nullary-constructor* inductive predicates (`Eq`, `HEq`); `unique.tex`'s `K⁺` covers all SS
   inductives (`Acc` included) but **not quotients**. §2, with a kernel-level probe of each.
   **[measured + read]**

4. **`NormalEq.descend` is still false — with a registration hypothesis, and with `K⁺`.** The
   new reason is not scope and not a missing rule: **`descend`'s conclusion demands that the
   left term reduce to a term that syntactically *matches* `q`, and a `K⁺` step never produces
   a match — it produces the rule's right-hand side.** §3. The restatement that does work is
   already written down elsewhere in the same file (`DescentLam.fire`'s conclusion), and under
   it all three E5 cases close by *one uniform move* that needs **less** than
   `docs/design-inductive.md` §7.6 assumed: no `pat_major_canonical`, no lemma M3.
   **[analysis; the three existing refutations are untouched and remain valid]**

5. **The `Quot`-over-`Prop` residual is real, and it is a gap in the reference.** It is
   localised to a single named false step — the `lift` bullet of `thm:gg_compat`
   (`unique.tex:180`), which asserts "`β : P`" where nothing forces it — and it propagates to
   a counterexample to `thm:ckappa`. There is a repair, and the repair is `K⁺` transposed to
   the quotient with a definable `inv`. Written up as `docs/upstream-report-ckappa-quot.md`.
   **Not sent to anyone, and must not be.** §4. **[measured probes + analysis]**

6. **The alignment step re-prices to exactly what it was.** `K⁺` does not touch
   `ParRed.defeq`'s β case, which is where Π-injectivity enters; `KStep.defeq` reaches
   `IsDefEqU.forallE_inv_stratified` itself, one hole, through `IsDefEqU.trans`. So the rule
   adds no dependency and removes none. §5. **[measured]**

7. **One correction that is not about mathematics.** `divergences.md` already carries a
   K⁺ entry (line 27) written as though the rule were in `ParRed`. It is not, and was not:
   `Params` has no `pat_small` and no `pat_major_canonical`, and `Lean4Lean/Theory/Inductive/
   Lemmas.lean:150` says so in as many words. §6. **[read]**

---

## 1. The rule

### 1.1 What `KStep` says

```lean
inductive KStep (Γ : List VExpr) : VExpr → VExpr → Prop where
  | mk {p₁ p₂ : Pattern} {r : (Pattern.app p₁ p₂).RHS × (Pattern.app p₁ p₂).Check}
      {f h c A₀ B₀ : VExpr} {m1 m2} :
      Pat (.app p₁ p₂) r →
      (Pattern.app p₁ p₂).Matches (.app f c) m1 m2 →
      r.2.OK (IsDefEqU env univs Γ) m1 m2 →
      HasType env univs Γ f (.forallE A₀ B₀) →
      IsDefEq env univs Γ h c A₀ →
      KStep Γ (.app f h) (r.1.apply m1 m2)
```

*"At a registered rule whose pattern is an application, the redex may be formed with any major
premise `h` that is definitionally equal to one the pattern matches; the contractum is the
rule's own right-hand side."*

Four design points, each of which was forced by something:

* **Indexed by `Pat`, not by "SS inductive".** Carneiro's `K⁺` is stated for SS inductives
  (`unique.tex:103`), which is why it does not reach the quotient rule; §4 shows that omission
  is a real gap. `Theory/`'s quotient rule is a `Pat` like any other (`PatternRules.lean`,
  `Pat.quot`), so the generic statement covers it at no extra cost. **[read + analysis]**

* **The side condition is a conversion, `Γ ⊢ h ≡ c : A₀`, not a syntactic test.** That is
  Carneiro's own reason for `K⁺` needing a context: the rule "applies only when
  `intro inv[p,h]` is well-typed (and is the reason why `↝_κ` needs a context)"
  (`unique.tex:107`). **[read]**

* **The typing premises are carried, not inverted.** `KStep` records `f`'s Π-type and types
  the conversion at that domain. This is not decoration: it keeps `KStep.defeq` out of
  `HasType.app_inv`'s and `IsDefEqU.of_l`'s cones, and it is the shape
  `docs/handoff-headreduction.md` §8 item 4 asks about (a reduction rule that carries its
  typing premises, as `IsDefEqStrong.beta` does). **[measured — §1.2]**

* **It is a rule, not a pattern.** `Params.no_kpattern` **[machine-checked]**: the pattern
  that would express K-like *matching* — `(Pattern.const rec).varN (m+1)`, the recursor's
  spine with the major position left as a bare `.var` — **intersects** that recursor's
  ι-pattern, so `Params.pat_uniq` (instantiated at `p₃ := p₁`) concludes the two patterns are
  equal, which they are not (`.app` versus `.var`). Carneiro takes the other branch of the
  same fork: his ι rule is restricted to **non-SS** inductives (`unique.tex:101`), so at most
  one of the two rules is live per recursor.

  Taking Carneiro's branch *here* — registering the K-pattern **instead of** the ι-pattern —
  fails for a sharper reason than uniqueness. The K-pattern matches every ι-redex, so
  `extra_pat` would still be satisfiable; but `Params.pat_wf` would then have to prove
  `Γ ⊢ rec C ms is h ≡ RHS` for an **arbitrary** `h`, which is false unless `h`'s type is a
  `Prop`. The guard would have to live in the rule's `Check`, and `Pattern.Check` cannot
  express it: its clauses are `defeq` between `RHS`-computable terms and `≈` between matched
  level lists, and neither can mention the *type* of a matched argument (`Pattern.lean`,
  `Check.OK`). **So the side condition cannot be a pattern-language condition at all**; it has
  to sit outside, which is what `KStep` does. **[read + analysis]**

### 1.2 What is proved, and what it costs **[measured]**

```
lake build Lean4Lean.Theory.Typing.KRule    -> Build completed successfully (59 jobs)

#print axioms KStep.defeq        -> [propext, sorryAx, Classical.choice, Quot.sound]
#print axioms KStep.stuck_fires  -> [propext, Quot.sound]
#print axioms Params.no_kpattern -> [propext, Quot.sound]

cone scan (declaration *values*, `.thmInfo` via `value? (allowOpaque := true)`):
  KStep.defeq        reaches sorry-carrying: [IsDefEqU.forallE_inv_stratified]
  KStep.stuck_fires  reaches sorry-carrying: []
  Params.no_kpattern reaches sorry-carrying: []
```

`KStep.defeq`'s single hole enters through `IsDefEqU.trans`, which is itself tainted by
`forallE_inv_stratified` **[measured]** — composing two `IsDefEq` links needs a shared type
index, and pinning it needs unique typing. That is the negative structural fact
`docs/handoff-sortuniq.md` §5 already records, arriving here again. It is *not* avoidable by
restating `KStep`: `Params.pat_wf`'s conclusion is the type-free `IsDefEqU`, so the second
half of the composition arrives untyped whatever the rule carries.

`KStep.stuck_fires` **[machine-checked]** is the non-vacuity check against the measured hole:
the *very term* `whnf_app_bvar` proves weak-head normal — `.app f (.bvar i)` with `f` normal
and not a `.lam` — is a `KStep` redex. Both conclusions are produced simultaneously from the
same hypotheses. Its hypotheses are the honest cost: someone must exhibit a `c` making
`.app f c` a redex, and no `Params` instance in the tree supplies one yet, because
`paramsOfWF`'s `PatWF` is open in its ι and quot cases (`docs/handoff-params.md` §1.1).

### 1.3 What is *not* done

* No `ParRed`/`CParRed` constructor. Adding one means: `ParRed.weakN`/`.instN` gain a case
  (routine — `Pattern.matches_liftN` and `matches_instN` exist), `ParRed.defeq` gains a case
  (that is `KStep.defeq`), `NonNeutral` gains a third disjunct, `CParRed.exists` becomes
  classical, and `ParRed.triangle` gains the real work. `ChurchRosser.lean` was **not edited**
  this session.
* No `Params` instance that supplies a canonical major premise. §3 argues this is *not*
  needed for the confluence argument, which is the main saving this session found.

---

## 2. How the rule differs from the implementation and from `unique.tex`

### 2.1 The three rule sets **[read]**

| | fires when the major premise is… | covers `Eq`/`HEq` | covers `Acc` | covers `Quot` over a `Prop` carrier |
|---|---|---|---|---|
| `Theory/` before this session (`Pattern.lean:293`) | syntactically the constructor | no | no | no |
| C++ kernel `init_K_target` (`inductive.cpp:595`) + `Reduce.lean` `toCtorWhenK` | anything, if the block is a single non-mutual `Prop`-valued inductive with **one constructor and no fields** | **yes** | **no** | no (`quot.cpp` needs `Quot.mk`) |
| `unique.tex` `K⁺` (`:103`) | anything, if the block is **SS** (subsingleton-eliminating) | yes | **yes** | **no** (`K⁺` says "SS inductive"; `Quot` is a primitive) |
| `KRule.lean` `KStep` | anything definitionally equal to a match, at **any registered rule** | yes | yes | **yes** |

The kernel's condition is strictly narrower than `K⁺`'s: `init_K_target` requires
`length(cnstrs) == 1` **and** that the constructor's type have no Π binder past the parameters
(`inductive.cpp:601-614`) **[read]**. `Acc.intro` has fields, so `Acc` fails it while being SS.

### 2.2 The measurement **[measured]**

Kernel-checked `theorem`s under Lean 4 v4.33.0-rc2 (`lake env lean`, so the repo's pinned
toolchain), each asserted by `rfl`:

| probe | result |
|---|---|
| `Eq` — `@Eq.rec α a C m a h = m` for a **variable** `h : a = a`, `C` landing in `Type` | **accepted** (K-like reduction fires) |
| `Acc` — `h = Acc.intro x (fun z hz => Acc.inv h hz)` | **accepted** (proof irrelevance) |
| `Acc` — `Acc.rec F (Acc.intro x g) = F x g (fun z hz => Acc.rec F (g z hz))` | **accepted** (ι) |
| `Acc` — `Acc.rec F h = F x (fun z hz => Acc.inv h hz) (…)` for a variable `h` | **rejected** |
| `Quot` — `q = Quot.mk R a`, `α : Prop` | **accepted** (proof irrelevance) |
| `Quot` — `Quot.lift f H (Quot.mk R a) = f a` | **accepted** (ι_q) |
| `Quot` — `Quot.lift f H q = f a` for a variable `q` | **rejected** |

Line 1 is `toCtorWhenK` doing its job; lines 2–4 are the `Acc` gap that `K⁺` closes and the
kernel does not; lines 5–7 are the `Quot` gap that *neither* closes. All three "rejected" rows
are instances of the non-transitivity of algorithmic equality that `typesys.tex:19-52`
describes and expects; none of them is a kernel bug.

### 2.3 Is this a divergence for `divergences.md`? **No — and that is a correction.**

`docs/handoff-headreduction.md` §8 item 2 says the K-rule gap means "the implementation is
currently *outside* its own specification on those inputs". **That is wrong.** The
specification the checker is verified against is the declarative judgment `IsDefEq`
(`Theory/Typing/Basic.lean`); `Pat`, `ParRed` and `NormalEq` are internal proof machinery in
the `[Params]` development, and nothing in `Lean4Lean/Verify/` relates `addDecl` to them.  The
only `Verify/` file that mentions the `[Params]` development at all is
`Verify/Typing/Rigidity.lean`, which *states* `VEnv.ConstRigid` and has **no consumer anywhere
in the tree** **[measured: `grep -rn ConstRigid` outside that file returns nothing]**.
`toCtorWhenK` is **admissible** in `IsDefEq`: its guard forces the major premise's type to be
a `Prop` (`normalizes_to_zero(m_result_level)`) and checks that the reconstructed constructor
application has a definitionally equal type, so `e ≡ newCtorApp` follows from
`IsDefEq.proofIrrel` **[read + analysis]**. Nothing the checker accepts is outside the theory.

The real defect is the opposite one and it is a documentation defect, not a behavioural one:
`Theory/`'s reduction relation was **incomplete** for its own `IsDefEq`, which is a
metatheory gap, not a divergence. §6 says what `divergences.md` should say instead.

---

## 3. What the missing rule was blocking: `descend`, restated

### 3.1 The three existing refutations stand, unchanged

`Theory/Typing/DescendRefute.lean`'s `not_descendStatement`, `not_descendStatement_etaArg`,
`not_descendStatement_etaFun` refute `descend` **as written**, over `refEnv`, which registers
no rules at all. They are about the unregistered `q`. Nothing in this session touches them and
none of them is deleted. **[read; they were [machine-checked] last round]**

### 3.2 With a registration hypothesis and `K⁺`, `descend` is *still* false **[analysis]**

Add `Pat q' r ∧ Subpattern q q'` and `hsu` to `descend` and put `KStep` in `ParRed`. The E5
cases still fail, for a reason neither previous round names:

> `descend`'s conclusion, unfolded (`DescentLam 0`), is
> `∃ t n1' n, ParRedS Γ g t ∧ q.Matches t n1' n ∧ … ∧ ∀ x, NormalEq Γ (n x) (n2 x)`.
> It asks for a reduct of `g` that **syntactically matches `q`**.
> A `K⁺` step does not produce a match. Its contractum is `r.1.apply m1 m2` — the rule's
> right-hand side, which has the rule's own shape and matches `q` only by accident.

So the missing rule was never going to repair `descend`'s *statement*; it repairs the
*development* only after the statement is changed. This is the third distinct defect found in
this one theorem, and it is the same class as the previous two: **the conclusion asks for less
information than the caller needs, or for the wrong information.** Here it asks for a match
where the caller only ever wants a common reduct.

### 3.3 The restatement that works — and it is cheaper than the design assumed **[analysis]**

> **Superseded in part by Round 2 (§R0.5, §R3).**  The restatement is now machine-checked
> (`Lean4Lean/Theory/Typing/KDescend.lean`) and this section's M3 claim is confirmed *for the
> descent* and **refuted for the reduction relation**: landing the rule in `ParRed` needs M3
> twice.  Read §§R0–R3 before acting on the cost estimate below.

The right conclusion is already written in the same file, as `DescentLam.fire`'s:

```
∃ t, Γ ⊢ g ≫* t ∧ Γ ⊢ t ≡ₚ S            -- S = the rule's right-hand side at the match
```

Under it, **all three E5 cases collapse into one move**:

> The `appDF` node is `g = .app f₁ a₁`, `g' = .app f₂ a₂`, with `(.app q₁ q₂).Matches g' n1 n2`
> and `a₁ ≡ₚ a₂`. Descend **only the function side** against `q₁`, obtaining `f₁ ≫* t₁` with
> `q₁.Matches t₁ u1 u2` and `u2 x ≡ₚ` the right-hand arguments. Then `g ≫* .app t₁ a₁`, and
> `KStep` fires there with `c := a₂` — the conversion premise `Γ ⊢ a₁ ≡ a₂` is
> `NormalEq.defeq` applied to the hypothesis already in hand. Its contractum is
> `r.1.apply u1 (Sum.elim u2 (a₂'s matched arguments))`, which is `≡ₚ` the target `S` by
> `NormalEq.apply_pat` (arguments) and `NormalEq.apply_instL` (levels), both of which exist.
> The rule's `Check` obligations transport by `Pattern.Check.OK.congr_normalEq` and
> `Check.OK.map_levels`, which also exist.

Consequences worth stating precisely, because they change the cost estimate in
`docs/design-inductive.md` §7.6:

* **The argument side is never descended.** E5 #2, #3 and #4 differ only in *why* the argument
  side failed to descend (eta, eta, proof); under this move none of them needs it to.
* **`Params.pat_major_canonical` is not needed, and neither is lemma M3** (§7.6 prices M3 at
  ~400 lines, "hard"). The canonical major premise the rule needs is `a₂` — handed over by the
  `NormalEq` hypothesis itself. M3 would still be needed to make `CParRed` *complete* (so that
  `CParRed.exists` can decide whether to fire `K⁺`), but that can be had classically instead,
  since the whole development is in `Prop` and `Classical.choice` is already whitelisted.
* **E3 is unchanged**: the function-is-a-proof escape still needs `hsu`, and
  `NormalEq.appDF_proof_escape` (`DescendRefute.lean`) already closes it.
* **`DescentLam` survives**, because the *function* side can still eta-expand.

One premise of the move is not free and should be budgeted: `KStep` asks for
`Γ ⊢ t₁ : .forallE A₀ B₀` at the *reduct* `t₁`, which needs subject reduction for `≫*`
(`ParRedS.hasType`). That is already in the `appDF`/`extra` case's cone, so it costs nothing
new here — but it means the move cannot be lifted out into a `Params`-free lemma.

**This is [analysis], not [machine-checked].** It is the recommended next unit of work and it
is a session-sized one: restate `descend`, thread `hsu` and the registration hypothesis, and
replace the three `sorry`s with the single move above. What makes it worth doing before
anything else in this corner is that it is the first version of the statement that is not
known false.

---

## 4. The `Quot`-over-`Prop` verdict: the gap is real, and it is in the reference

**Confirmed.** `docs/handoff-headreduction.md` §5.4 flagged it as unchecked analysis; it
checks out, and it is sharper than flagged — it is a single named false step, not a vague
omission.

* **Where it is.** `thm:gg_compat` (`unique.tex:167`, "Compatibility of `≫_κ` with `≡_p`"),
  the `lift` bullet at `:180`, discharges its case by "then `β : P` so `e₁ : β` is a proof".
  For the *recursor* bullet directly below, the analogous inference is sound: a proof major
  premise forces a non-SS inductive to be a small eliminator, hence a `Prop` motive. For
  `lift` there is no such link — `lift_R`'s target universe is an independent parameter
  (`axioms.tex:227`), so `α : P` and `β : U_1` are simultaneously legal. **[read]**
* **What it breaks.** `thm:gg_compat` is false at that instance, and it propagates:
  `thm:church_rosser`'s step (2) uses it to commute `≡_p` past `≫_κ`, `≡_κ`'s transitivity
  comes from Church–Rosser, and `thm:ckappa`'s first bullet is "immediate since `≡_κ` is an
  equivalence relation". The resulting counterexample to `thm:ckappa` is
  `Γ ⊢ lift_R β f H q ≡ f a` with `Γ ⊬ lift_R β f H q ≡_κ f a`. **[analysis]**
* **What it does *not* break.** Not `thm:unique`: `thm:1dinv` uses `thm:ckappa` only at
  `U ≡ U`, `∀ ≡ ∀` and `U ≢ ∀`, and this counterexample is not obviously at those instances.
  Not the kernel: `typesys.tex:50` already records this exact configuration as a source of
  non-transitivity of *algorithmic* equality, which is expected and is measured in §2.2.
* **The repair, and why it matters here.** Add `K⁺` for quotients over a `Prop` carrier, with
  `inv_R := lift_R α (λx. x) (λx y _. refl) : α/R → α`. That is well-typed for exactly
  Carneiro's own reason (`unique.tex:109`): when `α : P` every `f : α → β` satisfies `lift`'s
  soundness hypothesis automatically, because any two inhabitants of `α` are definitionally
  equal. **[measured: `qinv q = a` and `f (qinv q) = f a` are both kernel-accepted by `rfl`]**
  Then `f' inv_R[q] ≡_p f a` by proof irrelevance and the bullet goes through.
* **Why this tree does not have to inherit the gap.** `KStep` is indexed by the rule table, so
  the quotient rule is covered by the same constructor as every ι-rule. This is the one place
  where copying `unique.tex` literally would have imported a bug; stating the rule once,
  over `Pat`, cannot miss a rule shape.

Full write-up, in the form of `docs/upstream-report-thm1dinv.md`:
**`docs/upstream-report-ckappa-quot.md`. It is a draft. It has not been sent to anyone and
must not be; whether, when and to whom it goes is the repository owner's decision.**

---

## 5. Re-pricing the alignment step **[measured + read]**

`docs/handoff-headreduction.md` §0.3 / §4: `ParRed.defeq`'s `beta` case retypes the argument
through `IsDefEqU.forallE_inv ∘ IsDefEq.uniqU`, because `HasType.app_inv` returns the stored
Π's domain and `HasType.lam_inv` returns the λ's annotation, and only Π-injectivity bridges
them. Does `K⁺` change that?

**No, and the measurement is direct rather than argued.**

* The `beta` case of `ParRed.defeq` is untouched by adding a constructor elsewhere in
  `ParRed`; the offending line (`ChurchRosser.lean:696`) is unchanged.
* The new case's own regularity, `KStep.defeq`, reaches **exactly one** hole,
  `IsDefEqU.forallE_inv_stratified` — one of the two the alignment step exists to close — and
  it reaches it through `IsDefEqU.trans`, i.e. through *composition*, not through Π-inversion.
  **[measured, §1.2]** So the rule neither adds a dependency nor removes one.
* The 21 `sorryAx`-tainted declarations of `HeadReduction.lean` are unaffected: none of them
  is in `KRule.lean`'s cone and `KRule.lean` is downstream of all of them.

So the answer to "does the K-rule change the alignment pricing" is: **no**. What it changes is
the *other* corner — confluence — where §3 shows it turns a known-false lemma into a
plausible one for the first time.

One thing that did move, and is worth recording because it is the cheapest fact in this
document: **carrying typing premises on a reduction rule instead of inverting them removes two
constants from the cone** (`HasType.app_inv`, `IsDefEqU.of_l`). It does not remove the hole,
because `IsDefEqU.trans` is tainted too, but it is the first measured evidence for
`docs/handoff-headreduction.md` §8 item 4's idea. Anyone pursuing an `IsDefEqStrong`-indexed
reduction relation should note that the remaining obstacle there is *composition*, not
inversion.

---

## 6. Corrections this document makes

| document | claim | correction |
|---|---|---|
| `divergences.md:27-33` | describes a `K⁺` rule of `VEnv.ParRed`/`CParRed` and `Params.pat_major_canonical` as present | **Neither exists.** `Params` (`ChurchRosser.lean:12`) has no `pat_small` and no `pat_major_canonical`; `ParRed` (`:611`) has no `K⁺` constructor. `Lean4Lean/Theory/Inductive/Lemmas.lean:150` already says these fields "**do not exist** in the class as it stands". The entry documents unlanded design as landed. **[read]** |
| `divergences.md:27-33` | frames the K⁺ situation as a divergence from the kernel | It is not a behavioural divergence: `IsDefEq` is what the checker is verified against, and `toCtorWhenK` is admissible in it (§2.3). If an entry is wanted it should say that the *abstract reduction relation* is deliberately larger than the checker's, which is the sound direction, and that `reduceRecursor.WF` must therefore be a containment. |
| `docs/handoff-headreduction.md` §8 item 2 | "the implementation is currently *outside* its own specification on those inputs" | Wrong. §2.3. The gap is completeness of `Theory/`'s reduction relation, not soundness of the checker. |
| `docs/handoff-headreduction.md` §5.4 | the `Quot`-over-`Prop` residual, flagged as unchecked | Confirmed, and localised: `thm:gg_compat`'s `lift` bullet, `unique.tex:180`. §4. |
| `docs/handoff-headreduction.md` §5.3 | "With `K⁺` in the rule set … witness A's shape at a registered ι-pattern is repaired" | True of the *diamond*, false of `descend`: `descend`'s conclusion asks for a syntactic match and `K⁺` never produces one. §3.2. |
| `docs/handoff-descend.md` §8 item 1 | restate `descend` with a `Pat`/`Subpattern` hypothesis plus `hsu` | Necessary but not sufficient — the *conclusion* has to change too. §3.3. |
| `docs/design-inductive.md` §7.6 / table row I16 | lemma M3 + `pat_major_canonical`, "hard", ~400 lines | Not needed for the confluence argument: the canonical major premise is `a₂`, supplied by the `NormalEq` hypothesis. Needed only to keep `CParRed.exists` constructive, which the tree does not require. §3.3. **[analysis]** |
| the task brief | "`Theory/` … has **no** K-like reduction … Add it" | Correct, and done abstractly. But the brief's implied consequence — that adding it unblocks `descend` — does not hold without restating `descend`. §3. |

Nothing in `docs/handoff-descend.md` §§1–3 is contradicted; its three refutations stand.

---

## 7. Files

* `Lean4Lean/Theory/Typing/KRule.lean` — **new**, no `sorry`. `KStep`, `KStep.defeq`,
  `KStep.stuck_fires`, `kPattern`, `Params.no_kpattern`.
* `docs/upstream-report-ckappa-quot.md` — **new**. Draft only; not sent, and not to be sent.
* `docs/handoff-krule.md` — this document.
* `Lean4Lean/Theory/Typing/ChurchRosser.lean`, `HeadReduction.lean`, `HeadRedStuck.lean`,
  `DescendRefute.lean`, `Pattern.lean`, `PatternRules.lean`, `PatternDecode.lean` —
  **unchanged**. In particular no `sorry` was added or removed anywhere.

### Verification runs **[measured]**

```
lake build Lean4Lean.Theory.Typing.KRule   -> Build completed successfully (59 jobs)
#print axioms KStep.stuck_fires            -> [propext, Quot.sound]
#print axioms Params.no_kpattern           -> [propext, Quot.sound]
#print axioms KStep.defeq                  -> [propext, sorryAx, Classical.choice, Quot.sound]
cone(KStep.defeq)                          -> [IsDefEqU.forallE_inv_stratified]

lake env lean scripts/sorry-census.lean    -> TOTAL declarations directly containing
                                              sorryAx: 19    (unchanged from the brief)
```

The census reads declaration *values* and prints every name; it is the only count that should
ever be quoted.  This session added no `sorry` and removed none.

`Lean4Lean/Theory/Typing/Injectivity.lean` was red twice mid-session from another stream's
in-flight edits (`:120`, `:128`, `:136`, `:620`, `:645`); it went green on its own both times
and every number above is from after that. Nothing in this session edited a file it does not
own.

---

## 8. What to pick up first

1. **Restate `descend` per §3.3** and land the uniform E5 move. It is the first version of
   that statement not known false, and it is the only thing downstream of it that can move.
2. **Then** add the `K⁺` constructor to `ParRed`/`CParRed` and re-run `ParRed.triangle`. §1.3
   lists the six proofs that gain a case; five are routine.
3. **Fix `divergences.md`** (§6, first two rows). An entry describing unlanded work as landed
   is worse than no entry: the next reader will look for `pat_major_canonical` and not find it.
4. **Do not** expect any of this to move the alignment step. §5.

---

# Round 2 (this session): the wiring, and what it cost

**Task.** Wire `KStep` into the development; make §3.3's "one uniform move" machine-checked
instead of argued; confirm or refute that lemma M3 / `pat_major_canonical` is thereby not
needed; re-price `forallE_inv_stratified` and `weakN_iff`.

Same marks as above: **[machine-checked]** = a named `sorry`-free Lean declaration in this
tree; **[measured]** = a machine run whose output is reproduced; **[read]**; **[analysis]**.

## R0. Verdict

1. **§3.3's move is machine-checked**, in `Lean4Lean/Theory/Typing/KDescend.lean` (new,
   `sorry`-free source). All three refuted E5 branches collapse into one firing of `KStep`,
   with the canonical major premise handed over by the `NormalEq` hypothesis. The proof
   mentions no canonicity lemma. **[machine-checked]**

2. **The reason it works is smaller and sharper than §3.3 guessed, and it was already in
   `Params`.** `Params.pat_simple` forces every registered pattern to be
   `.app ((.const rec).varN m) ((.const ctor).varN n)` or `.const c`, so **an `.app` node
   occurs only at the very top of a pattern and both children are `.var`-chains**
   (`Params.pat_app_noApp`). `descend`'s three refuted branches are all in its `.app`-node
   case, and at a registered pattern that case happens **once**, at the top -- where there is
   a rule to fire. The descent proper (`NormalEq.descendV`) therefore never meets them:
   they are *unreachable*, not merely unproved. **[machine-checked]**

3. **E3 now costs nothing at all.** `descendV`'s `hsu` (universe uniqueness) is *discharged*,
   not carried: `Injectivity.lean`'s `VEnv.WF.sortUniq'` proves it relative to
   `IsDefEqU.forallE_inv_stratified` alone, which is already in the confluence cone through
   `IsDefEq.uniq`. `Params.sortUniq` does it in four lines. So the descent's two escapes cost,
   in total, **one** hypothesis. **[machine-checked]**

4. **That one hypothesis is `hK : KStep Γ e e' → ParRed Γ e e'`** -- the K-rule being a step of
   the reduction relation. It is *not* discharged, and §R3 says why: landing it breaks two
   things in `ChurchRosser.lean` that are not routine.

5. **§3.3's M3 claim is half right, and this session corrects the other half.**
   `pat_major_canonical` / lemma M3 is **not** needed for the descent -- confirmed, machine-
   checked. It **is** needed to land `hK`, twice: `ParRed.weakN_inv` becomes *false* without
   it, and `ParRed.triangle`'s new diagonal needs `KDiamond` (`KDescend.lean`). So M3 is not
   deleted from `docs/design-inductive.md` §7.6; it is **moved**, from the descent to the
   reduction relation's own metatheory. §R3. **[measured + analysis]**

6. **Re-pricing: nothing moved, and the measurement is direct.** With `descendV` in place the
   confluence chain still bottoms out in exactly `{forallE_inv_stratified, forallE_inv,
   weakN_iff}`, through the same three call sites as before. What *did* change is the count:
   `IsDefEq.church_rosser`'s cone reaches **four** `sorry`-carrying declarations today and the
   new route reaches **three** -- the one dropped is `NormalEq.descend`, i.e. the one that is
   **false**. §R4. **[measured]**

## R1. What landed

`Lean4Lean/Theory/Typing/KDescend.lean` (new; imports `KRule.lean` and `DescendRefute.lean`).

| declaration | says | own source |
|---|---|---|
| `Pattern.NoApp` | a pattern with no `.app` node | def |
| `Params.pat_app_noApp` | a registered `.app` pattern has `.app`-free children | `sorry`-free, cone empty |
| `Params.sortUniq` | universe uniqueness, discharged from `WF.sortUniq'` | `sorry`-free |
| `NormalEq.descendV` | `descend` restricted to `.app`-free patterns | `sorry`-free |
| `NormalEq.appDF_extra_of_descendV` | `appDF_extra_of_descend`'s conclusion, from `hK` | `sorry`-free |
| `KDiamond` | the residual `ParRed.triangle` needs from K | def |
| `KStep.uniq_defeq` | the free half of `KDiamond` (`≡`, not `≡ₚ`) | `sorry`-free |
| `refQ_not_noApp`, `refQ2_not_noApp` | the three refutations' patterns are excluded by `NoApp` | `sorry`-free |
| `refParams_no_kstep`, `refParams_hK` | `hK` is a consistent hypothesis | `sorry`-free |

`NormalEq.appDF_extra_of_descendV`'s statement is `NormalEq.appDF_extra_of_descend`'s,
verbatim, plus `hK`. So `NormalEq.parRed`'s `appDF` x `extra` case can be re-routed through it
the day `hK` lands, and nothing else in `NormalEq.parRed` changes.

**The move itself, for the record.** The old lemma descends the *whole* node against the whole
pattern `q₁.app q₂`, which forces the argument side to reduce to something matching `q₂` --
and `DescendRefute.lean` exhibits three terms for which it does not. The new one descends the
node against `.var q₁` instead: the function side's pattern with the argument position left
**free**, which `Pattern.Matches.var` accepts unconditionally. Then `KStep` fires at the
bottom of the eta tower with `c := b'`, the right-hand argument, and `Γ ⊢ ta' ≡ b'` is
`NormalEq.defeq` of the hypothesis the node already carries. Nothing asks anything of the
argument, so none of the three counterexamples applies -- and no canonical form is computed.

**Why the counterexamples cannot come back**, checked two ways: their patterns
(`refQ`, `refQ2`) have an `.app` node, so `descendV` never sees them (`refQ_not_noApp`); and
the top-node lemma carries `Pat p r`, which `refParams` cannot supply (`refParams_no_kstep`).
The three refutations stand, unedited, and remain the evidence that the restatement was
necessary. **[machine-checked]**

## R2. Measurements **[measured]**

```
lake build Lean4Lean.Theory.Typing.KDescend   -> Build completed successfully (70 jobs)

#print axioms Params.pat_app_noApp              -> [propext, Quot.sound]
#print axioms refQ_not_noApp                    -> [propext, Quot.sound]
#print axioms refParams_hK                      -> [propext, Classical.choice, Quot.sound]
#print axioms Params.sortUniq                   -> [propext, sorryAx, Classical.choice, Quot.sound]
#print axioms NormalEq.descendV                 -> [propext, sorryAx, Classical.choice, Quot.sound]
#print axioms NormalEq.appDF_extra_of_descendV  -> [propext, sorryAx, Classical.choice, Quot.sound]

cone scan (declaration values, `.thmInfo` via `value? (allowOpaque := true)`):
  Params.pat_app_noApp             -> []
  Params.sortUniq                  -> [forallE_inv_stratified]
  KStep.uniq_defeq                 -> [forallE_inv_stratified]
  NormalEq.descendV                -> [forallE_inv_stratified, forallE_inv, weakN_iff]
  NormalEq.appDF_extra_of_descendV -> [forallE_inv_stratified, forallE_inv, weakN_iff]

for comparison, the route being replaced:
  NormalEq.descend                 -> [NormalEq.descend, forallE_inv_stratified, forallE_inv, weakN_iff]
  NormalEq.appDF_extra_of_descend  -> [NormalEq.descend, forallE_inv_stratified, forallE_inv, weakN_iff]
  NormalEq.parRed                  -> [NormalEq.descend, forallE_inv_stratified, forallE_inv, weakN_iff]
  IsDefEq.church_rosser            -> [NormalEq.descend, forallE_inv_stratified, forallE_inv, weakN_iff]
```

Neither new theorem reaches `NormalEq.descend`: this is a replacement, not a wrapper.

## R3. Landing `hK`: the measured cost, and the two things that are not routine

The experiment was run and then reverted: a `kstep` constructor was added to
`VEnv.ParRed` in `ChurchRosser.lean`, in the shape that keeps the contractum's
constructor-side arguments *unreduced* (they are subterms of the canonical major premise `c`,
not of the redex, so `CParRed.exists`'s structural recursion cannot reach them):

```lean
| kstep : Pat (.app p₁ p₂) r → (.app p₁ p₂).Matches (.app f c) m1 m2 →
    r.2.OK (IsDefEqU env univs Γ) m1 m2 →
    Γ ⊢ f : .forallE A₀ B₀ → Γ ⊢ h ≡ c : A₀ →
    (∀ a, Γ ⊢ m2 (.inl a) ≫ m2'' a) →
    Γ ⊢ .app f h ≫ r.1.apply m1 (Sum.elim m2'' (fun x => m2 (.inr x)))
```

`lake build Lean4Lean.Theory.Typing.ChurchRosser` then reports **ten** sites **[measured]**:

| site | declaration | verdict |
|---|---|---|
| `:647` | `ParRed.weakN` | routine (`matches_liftN`, `RHS.liftN_apply`) |
| `:663` | `ParRed.instN` | routine (`matches_instN`, `RHS.instN_apply`) |
| `:688` | `ParRed.defeq` | routine -- it *is* `KStep.defeq` plus `apply_pat` |
| `:719` | `ParRed.defeqDFC` | routine |
| `:786` | `ParRed.weakN_inv` | **not routine: the goal is false.** See below |
| `:923` | `ParRed.triangle`, `app` case | needs `CParRed.kstep` first |
| `:958` | `ParRed.triangle`, `beta` case | needs `CParRed.kstep` first |
| `:1019` | `ParRed.triangle`, `extra` case's inner induction | the real work |
| `:2024` | `NormalEq.parRed`, `appDF` case | routine |
| `:2096` | `NormalEq.parRed`, `etaR` case | downstream of `ParRed.weakN_inv` |

Not counted, because they are separate inductives and so do not error: `NonNeutral` needs a
third disjunct, `CParRed` needs a `kstep` constructor, and `CParRed.exists` needs to decide
classically whether to fire it.

### R3.1 `ParRed.weakN_inv` becomes false **[analysis]**

`ParRed.weakN_inv` says a reduction of a *lifted* term is the lift of a reduction: no step
invents a variable. A K-step does. In `A::Γ`, the redex `(e.lift).app (h.lift)` may fire with
a canonical major premise `c` that mentions `.bvar 0` -- legitimately, because `h.lift ≡ c`
holds by proof irrelevance whenever the major premise's type is a `Prop`, which is the only
situation in which K fires at all. The contractum reads the constructor's arguments off `c`
and an ι-rule's right-hand side uses them, so the contractum mentions `.bvar 0` and is not the
lift of anything.

This is not a decoration: `ChurchRosser.lean:2096` (`NormalEq.parRed`'s `etaR` case, via
`ParRedExt.parRed_beta`) is a live consumer.

**And this is the first place M3 comes back.** Under `pat_major_canonical` the canonical form
is *definable* from the major premise -- Carneiro's `intro inv[p,h]` (`unique.tex:107`) -- so
`c` is a function of `h`, hence `c` at `h.lift` is `(c at h).lift`, and `weakN_inv` survives.
Without it the lemma has to be weakened to a `≡`- or `≡ₚ`-version and every consumer re-checked.

### R3.2 `ParRed.triangle` needs `KDiamond` **[machine-checked statement, analysis for the need]**

`CParRed` must fire K wherever `ParRed` can, so the complete development picks *some*
canonical major premise `c₀` while the arbitrary step picks `c₁`. The two contracta agree on
the function-side positions and differ exactly at the positions read off `c`. `triangle`'s
conclusion is `≡ₚ`, so the difference has to be `≡ₚ`.

`KDescend.lean` states this as `KDiamond` and proves its free half:

* `KStep.uniq_defeq` **[machine-checked]** -- two K-steps at the same redex are definitionally
  equal, immediately, from `KStep.defeq` composed with itself.
* the remaining content is the upgrade from `≡` to `≡ₚ`, which is what confluence exists to
  deliver. Assuming it *inside* the confluence proof is circular.

`Params.pat_uniq` does not supply it and cannot be applied: two K-steps at the same `f`-spine
may use patterns whose *argument* sides do not intersect -- two different constructors of the
same `Prop`-valued inductive, each definitionally equal to the major premise by proof
irrelevance. `Params.pat_uniq`'s `p₂.inter p₃ = some p₄` premise is then unsatisfiable.
**That configuration is exactly what Carneiro's `K⁺` excludes by restricting to
subsingleton-eliminating inductives** (`unique.tex:103`), and excluding it is what
`docs/design-inductive.md` §7.6's `pat_small` + `pat_major_canonical` are for.

So the honest price of `hK` is: five routine cases, one lemma to restate
(`ParRed.weakN_inv`), and M3. §3.3's estimate -- "M3 not needed, `CParRed.exists` can be
classical instead" -- was measuring the descent only.

## R4. Re-pricing `forallE_inv_stratified` and `weakN_iff` **[measured]**

Direct users of each hole inside `NormalEq.appDF_extra_of_descendV`'s cone:

```
IsDefEq.uniq              uses  IsDefEqU.forallE_inv_stratified
piInvStrat_axiom          uses  IsDefEqU.forallE_inv_stratified
ParRed.defeq              uses  IsDefEqU.forallE_inv
NormalEq.descendV         uses  IsDefEqU.forallE_inv
NormalEq.weakN_inv_DFC    uses  IsDefEqU.forallE_inv
NormalEq.weakN_inv_DFC    uses  IsDefEqU.weakN_iff
IsDefEq.weakN_iff'        uses  IsDefEqU.weakN_iff
VExpr.WF.weakN_iff        uses  IsDefEqU.weakN_iff
```

Verdict, against the brief's two questions:

* **`forallE_inv_stratified`: unchanged.** Its two entry points are `IsDefEq.uniq` and
  `piInvStrat_axiom`, neither of which the K-rule touches. `ParRed.defeq`'s `beta` case still
  reaches `forallE_inv` for the reason §5 gave. §5 stands.
* **`weakN_iff`: unchanged, and now visibly for a reason unrelated to the K-rule.** Its three
  entry points are `NormalEq.weakN_inv_DFC`, `IsDefEq.weakN_iff'` and `VExpr.WF.weakN_iff` --
  the *context*-weakening family, not the reduction relation. Nothing in this session's route
  goes near it. The brief's "same reduction relation reached from the other side" framing is
  not what the cone shows: `weakN_iff` enters through `NormalEq`'s and `IsDefEq`'s own
  weakening lemmas, one level below reduction.
* **One thing the K-rule *would* move, if landed:** `descendV` itself is a direct user of
  `forallE_inv`, in exactly one place -- the eta-layer branch, `(hty.uniqU henv hΓ l2)
  .forallE_inv henv hΓ`, retyping the argument at the λ's annotated domain. That is the same
  "invert the typing premise instead of carrying it" pattern §5's last paragraph flags. A
  `DescentLam` that carried the domain would remove it. Untried. **[measured + analysis]**

## R5. Corrections this round makes

| document | claim | correction |
|---|---|---|
| `docs/handoff-krule.md` §3.3 (above) | "`Params.pat_major_canonical` is not needed, and neither is lemma M3" | Right for the descent -- now machine-checked. **Wrong for the reduction relation**: landing the rule needs M3 twice, at `ParRed.weakN_inv` and at `ParRed.triangle`. §R3. |
| `docs/handoff-krule.md` §3.3 | "M3 would still be needed to make `CParRed` complete ... but that can be had classically instead" | Classical choice gives *a* canonical form, not a *unique* one, and `ParRed.triangle` needs uniqueness up to `≡ₚ`. §R3.2. |
| `docs/handoff-krule.md` §3.3 | "restate `descend`, thread `hsu` and the registration hypothesis, and replace the three `sorry`s" | The registration hypothesis is not threaded and `hsu` is not carried. What is threaded is `Pattern.NoApp`, which `Params.pat_simple` already implies, and `hsu` is discharged outright. §R0.2-3. |
| `docs/handoff-descend.md` §8 item 1 | restate `descend` with `Pat`/`Subpattern` + `hsu` | Neither is what the repair needed. `NoApp` is weaker than `Subpattern` of a registered pattern and is all the descent uses. |
| the brief's §"re-price" | "`IsDefEqU.weakN_iff` ... the same reduction relation, reached from the other side" | The cone says otherwise: `weakN_iff`'s three entry points are context-weakening lemmas, not reduction. §R4. |

Nothing in §§1-2, §4 or the three refutations in `DescendRefute.lean` is contradicted.

## R6. What to pick up first, revised

1. **Land `hK`.** Five routine cases (§R3's table), then the two that are not. Do
   `ParRed.weakN_inv` first: it is the one whose *statement* has to change, and the change
   propagates to `ParRedExt.parRed_beta` and `NormalEq.parRed`'s `etaR` case.
2. **M3 is back on the critical path.** Not for the descent -- for `ParRed.weakN_inv` and
   `KDiamond`. `docs/design-inductive.md` §7.6's row I16 should be reinstated, with the
   consumers corrected.
3. **`ChurchRosser.lean`'s `NormalEq.descend` should be deleted, not proved.** It is refuted,
   and `KDescend.lean` now carries a replacement for its only consumer. Deleting it changes
   `NormalEq.parRed`'s signature (it gains `hK`), which propagates to `IsDefEq.church_rosser`;
   that is a decision for whoever owns the confluence interface, so this session did **not**
   edit `ChurchRosser.lean`.
4. **Cheap and adjacent:** make `DescentLam` carry the λ's domain, and `descendV` stops being
   a direct user of `IsDefEqU.forallE_inv`. §R4.

## R7. Files, round 2

* `Lean4Lean/Theory/Typing/KDescend.lean` -- **new**, no `sorry`.
* `docs/handoff-krule.md` -- this section.
* `Lean4Lean/Theory/Typing/ChurchRosser.lean` -- **unchanged** (the `kstep` experiment of §R3
  was reverted byte-for-byte). `KRule.lean`, `DescendRefute.lean`, `HeadReduction.lean`,
  `HeadRedStuck.lean`, `Pattern.lean`, `PatternRules.lean`, `PatternDecode.lean` --
  **unchanged**. No `sorry` was added or removed anywhere.

```
lake env lean scripts/sorry-census.lean  ->  TOTAL declarations directly containing
                                             sorryAx: 19        (unchanged)
```

The census reads declaration *values* and prints every name; it is the only count that should
ever be quoted. This session added no `sorry` and removed none. (It was briefly unrunnable
mid-session -- `Lean4Lean/Verify/Primitive.lean` was red from another stream's in-flight edits
at `:1158`, `:1201`, `:1202`, and the census imports the whole tree. It went green on its own
and the number above is from after that.)


---

# Round 3 (this session): `hK` is not merely expensive — the target statement is false

**Task.** Build M3 (`pat_major_canonical`) and repair `ParRed.weakN_inv` with it; settle
`KDiamond`; then wire `KStep` into `ParRed`/`CParRed` and discharge `hK`.

Same marks: **[machine-checked]** = a named `sorry`-free Lean declaration in this tree;
**[measured]** = a machine run whose output is reproduced; **[read]**; **[analysis]**.

## S0. Verdict

1. **`IsDefEq.church_rosser`'s statement is FALSE at any `Params` instance that registers the
   ι-rule of a large-eliminating subsingleton — `Eq` — and the K-rule has nothing to do with
   it.**  `VEnv.not_crStatement_of_kstep` **[machine-checked]**: from a registered K-redex
   under an `eta`, `CRStatement` is refuted.  It uses only `KStep.defeq`, i.e. that the rule
   is *admissible*; `ParRed` never gets a K constructor in that proof.  §S4.

   This subsumes the round's brief.  No `Params` field, no repair of `NormalEq.descend`, and
   no K constructor can make the current `CRDefEq` conclusion true: `NormalEq` itself (or
   `ParRedS`, by an eta-expansion) has to grow.

2. **`hK` is not landable as posed, and the blocking site is not the one §R3 identified.**
   `VEnv.not_parRedStatement_of_hK` **[machine-checked, and axiom-clean — no `sorryAx` at
   all]**: `hK` refutes `NormalEq.parRed`.  The break is `NormalEq.parRed`'s `etaR` case,
   which §R3's table listed as "downstream of `ParRed.weakN_inv`".  It is downstream of
   nothing: with K in `ParRed`, `.lam A (.app e.lift (.bvar 0))` reduces to `.lam A t` while
   `e` does not reduce at all, and `NormalEq`'s only route to `.lam A t` is `etaR`, which asks
   for the K-redex to be `NormalEq` to its own contractum.  §S3.

3. **`KDiamond` is neither proved nor refuted; it is *priced*, machine-checked, at exactly two
   rule-table facts** — `KTable` (M3 / `pat_major_canonical`) and `KSmall` (`pat_small`).
   `VEnv.kDiamond_of : KTable → KSmall → KDiamond` **[machine-checked]**, each hypothesis used
   once, in disjoint branches of a dichotomy `KSmall` supplies.  §S2.  Given (1) and (2) this
   is now a *conditional* result: it says what the diamond would cost if the interface were
   repaired first.

4. **The brief's nominated refutation does not refute anything.**  At `Or.rec C ml mr h` the
   two K-steps give `ml x` and `mr y`, which *are* `NormalEq` — by `proofIrrel`, because `Or`
   is small-eliminating so the redex is a proof.  That is the *cheap* branch, and `KSmall` is
   its name.  The expensive branch is the opposite one: **one** constructor, **large**
   elimination (`Eq`, `Acc`, `Quot` over a `Prop` carrier).  §S2.

5. **M3 repairs `ParRed.weakN_inv` only in a `≡ₚ`-weakened form; the equality form is
   irreparable.**  `KTable.kstep_liftN_inv` **[machine-checked]**.  This corrects §R3.1,
   which said M3 lets `weakN_inv` survive.  §S5.

6. **Two of §R3's "five routine" sites are now lemmas with empty cones**
   (`KStep.weakN`, `KStep.instN`) **[machine-checked]**, so they cost nothing.

7. **The cone re-measurement confirms the brief**: `IsDefEq.church_rosser` reaches **four**
   `sorry`-carrying declarations today and **three** by the new route, the dropped one being
   `NormalEq.descend`; and the new file adds no hole to the cone.  §S6.  Given (1), that
   measurement should now be read as a statement about a route that does not terminate in a
   true theorem.

## S1. What landed: `Lean4Lean/Theory/Typing/KCanonical.lean` (new, `sorry`-free)

| declaration | says | cone |
|---|---|---|
| `Pattern.NoApp.matches_det` | two `.app`-free patterns matching one term are equal | empty, **axiom-free** |
| `VEnv.KTable` | **M3**: the canonical major premise, as a *function* of the redex | def |
| `VEnv.KSmall` | **`pat_small`**: distinct rules at one spine ⇒ the redex is a proof | def |
| `VEnv.kDiamond_of` | `KTable → KSmall → KDiamond` | `{fE_inv_strat, fE_inv, weakN_iff}` |
| `VEnv.KStep.weakN` | `ParRed.weakN`'s new case | **empty** |
| `VEnv.KStep.instN` | `ParRed.instN`'s new case | **empty** |
| `VEnv.KTable.kstep_liftN_inv` | `ParRed.weakN_inv`'s new case, in `≡ₚ` form | `{fE_inv_strat, fE_inv, weakN_iff}` |
| `VEnv.ParRedStatement`, `not_parRedStatement_of_hK` | **`hK` refutes `NormalEq.parRed`** | **empty**, no `sorryAx` |
| `VEnv.CRStatement`, `not_crStatement_of_kstep` | **a registered K-redex refutes Church–Rosser** | `{fE_inv_strat}` |
| `VEnv.parRedS_rigid`, `parRedS_lam_inv` | reduct-shape lemmas the two refutations need | empty |
| `VEnv.parRedStatement_holds`, `crStatement_holds` | the two `Prop`s are the tree's statements **verbatim** (`:= NormalEq.parRed`, `:= IsDefEq.church_rosser`) | inherited |
| `VEnv.refParams_kSmall`, `refParams_kTable` | both hypotheses are consistent (vacuously) | empty |

## S2. `KDiamond`, priced

### The two facts

```lean
structure KTable where
  kmajor : Pattern → VExpr → VExpr → VExpr
  kmajor_liftN : ∀ p f h n k,
    kmajor p (f.liftN n k) (h.liftN n k) = (kmajor p f h).liftN n k
  canon : … OnCtx Γ … → Pat (.app p₁ p₂) r →
    (.app p₁ p₂).Matches (.app f c) m1 m2 → Check.OK … m1 m2 r.2 →
    Γ ⊢ h ≡ c : A₀ → Γ ⊢ .app f c : A →
    (Γ ⊢ A : .sort .zero) ∨
    ∃ m1' m2', (.app p₁ p₂).Matches (.app f (kmajor p₂ f h)) m1' m2' ∧
      Γ ⊢ h ≡ kmajor p₂ f h : A₀ ∧
      (∀ lp, List.Forall₂ (· ≈ ·) (m1 lp) (m1' lp)) ∧ (∀ x, Γ ⊢ m2 x ≡ₚ m2' x)

def KSmall : Prop := ∀ …,
  Pat (.app p₁ p₂) r → Pat (.app p₁ p₂') r' →
  (.app p₁ p₂).Matches (.app f c) m1 m2 → (.app p₁ p₂').Matches (.app f c') m1' m2' →
  Γ ⊢ c ≡ c' : A₀ → Γ ⊢ .app f c : A →
  p₂ = p₂' ∨ Γ ⊢ A : .sort .zero
```

### Four drafts, three of them false or unsatisfiable — the audit is the deliverable

Each is one of `ORCHESTRATOR.md`'s listed shapes, and none was caught by reading the
statement; all four were caught by asking *what must satisfy this* and *what must consume it*.

* `kmajor : VExpr → VExpr → VExpr`, **unindexed by the pattern** — *unsatisfiable* at a
  multi-constructor `Prop`.  At `Or.rec C ml mr h` both ι-rules fire, and one canonical
  premise cannot match `(.const Or.inl).varN n` and `(.const Or.inr).varN n` at once.  This
  version also *appeared to make `KSmall` unnecessary* (`matches_det` derives `p₂ = p₂'` from
  the two canonical matches) — the "conclusion follows because the premise is unsatisfiable"
  trap, arrived at from the producer side.  `unique.tex:107`'s own notation is `inv[p,h]`,
  indexed by the pattern; copying it would have avoided this.
* `canon` **without the `Γ ⊢ A : .sort .zero` escape** — still unsatisfiable, even per pattern.
  A canonical `Or.inl x₀` definable from `(f, h)` need not exist: `x₀ : A` cannot be built when
  only `B` holds.  In exactly that situation the redex is a proof and the rule is not needed,
  so the field concludes a disjunction.
* `canon` **at `=` rather than `≡ₚ`** — *false*.  Two canonical forms of one proof may differ
  syntactically: `Eq.refl α a` and `Eq.refl α' a'` with `α`, `α'` δ-equal are both valid.
  This is the draft that decides §S5.
* `KSmall` **without the `Γ ⊢ c ≡ c' : A₀` premise** — *false*.  `Nat.rec`'s two ι-rules share
  a function side and `Nat.rec C z s Nat.zero` is not a proof.  What makes the field true is
  that two *definitionally equal* major premises cannot match different constructor patterns
  unless the type is a subsingleton.  The "quantifier ranging wider than intended" shape,
  caught by auditing against the consumer (the diamond always has `c ≡ c'` in hand).

In the cases where the rule *is* needed, `kmajor` is definable, which is §7.6's lemma M3:
`Eq.refl α a` reads `α`, `a` off the recursor's own spine `f`; `Acc.intro x (fun y hy =>
Acc.inv h hy)` likewise, using `h`; `Quot.mk r (invQ q)` likewise (§4 above). **[analysis]**

### Why `Params` supplies neither

`pat_uniq` fires only when `p₂.inter p₃ = some p₄`.  At two rules of one recursor the argument
sides are `(.const ctor).varN n` chains over *different* constants, so the intersection is
`none` and the field never applies.  `KRule.lean`'s `Params.no_kpattern` is the same
observation from the other side.  The one instantiation at which `pat_uniq` *does* fire is
`p₃ := p₁` with `inter_self`, and `kDiamond_of` uses exactly that to get `r ≍ r'`.
**[machine-checked]**

### Why there is no refutation of `KDiamond`, and why that is not evidence of truth

A counterexample would be a `Params` instance with two registered `.app` rules sharing a
function side whose contracta are not `NormalEq`.  Both contracta are definitionally equal
(`KStep.uniq_defeq`) and both are `ParRed`-normal, so such an instance is a counterexample to
Church–Rosser, not merely to `KDiamond` — which §S4 then obtains by a shorter route that needs
only *one* rule.  Building one needs a `VEnv.WF` environment with an `.app`-headed defeq rule,
and `VEnv.WF` admits those only through `VDecl.induct` and `VDecl.quot`; the tree's two
instances (`refParams`, `propLoopParams`) register `.const` patterns only, at which `KStep` is
empty and everything in the file holds vacuously (`refParams_kSmall`, `refParams_kTable`).
**That is a fact about the tree's witnesses, not evidence of truth.**

## S3. `hK` refutes `NormalEq.parRed` **[machine-checked]**

```lean
def ParRedStatement : Prop :=          -- NormalEq.parRed's statement, verbatim
  ∀ {Γ e₁ e₂ e₂'}, OnCtx Γ (IsType env univs) →
    NormalEq Γ e₁ e₂ → ParRed Γ e₂ e₂' → ∃ e₁', ParRedS Γ e₁ e₁' ∧ NormalEq Γ e₁' e₂'

theorem not_parRedStatement_of_hK
    (hK : ∀ {Δ a b}, KStep Δ a b → ParRed Δ a b)
    (hΓ) (hΓA) (he : Γ ⊢ e : .forallE A B)
    (hstep : KStep (A::Γ) (.app e.lift (.bvar 0)) t)
    (hlam : ∀ A' e', e ≠ .lam A' e')
    (hnp  : ∀ P, Γ ⊢ P : .sort .zero → ¬ (Γ ⊢ e : P))
    (hrig : ∀ o, ParRedS Γ e o → o = e)
    (hne  : ¬ NormalEq (A::Γ) (.app e.lift (.bvar 0)) t) :
    ¬ ParRedStatement
```

The witness is `KStep.stuck_fires` meeting `NormalEq.etaR`.  `.app e.lift (.bvar 0)` is
*exactly* the term `whnf_app_bvar` proves weak-head normal and `KStep` reduces.  Take
`e := Eq.rec α a C m a` — five arguments, one short of the ι-pattern, so `e` is
`ParRed`-normal — with `C` landing in `Type` and `m` a variable, and `A := Eq α a a`.  Then

* `Γ ⊢ e ≡ₚ .lam A (.app e.lift (.bvar 0))` by `etaR` + `refl`;
* `Γ ⊢ .lam A (.app e.lift (.bvar 0)) ≫ .lam A m.lift` by `ParRed.lam` and the K-step;
* so the conclusion demands `o` with `Γ ⊢ e ≫* o` and `Γ ⊢ o ≡ₚ .lam A m.lift`.

`e` is normal, so `o = e`, and `Γ ⊢ e ≡ₚ .lam A m.lift` can only be `etaR`, which asks for
`A::Γ ⊢ .app e.lift (.bvar 0) ≡ₚ m.lift` — a K-redex `NormalEq` to its own contractum.
`NormalEq` has no reduction rule, and `C` lands in `Type`, so `proofIrrel` is unavailable.
There is no such `o`.  **[machine-checked for the six hypotheses; the `Eq.rec` reading of them
is [analysis], and §2.2's first probe is the [measured] evidence that Lean itself reduces this
term.]**

## S4. The same obstruction without `hK`: Church–Rosser itself **[machine-checked]**

A K-step is *admissible* (`KStep.defeq`), so wherever one fires, `IsDefEq` already relates the
redex to the contractum — and under an `eta`, `IsDefEq` relates the *function* to a λ whose
body is the contractum.  `ParRed` cannot follow, K-rule or no K-rule, because `e` itself is not
a redex; and `NormalEq` cannot bridge, for the reason in §S3.

```lean
def CRStatement : Prop :=              -- IsDefEq.church_rosser's statement, verbatim
  ∀ {Γ e₁ e₂ A}, OnCtx Γ (IsType env univs) → IsDefEq env univs Γ e₁ e₂ A → CRDefEq Γ e₁ e₂

theorem not_crStatement_of_kstep
    (hΓ) (hΓA) (hA : Γ ⊢ A : .sort u) (he : Γ ⊢ e : .forallE A B)
    (hstep : KStep (A::Γ) (.app e.lift (.bvar 0)) t)
    (hlam) (hnp) (hrig : ∀ o, ParRed Γ e o → o = e)
    (hrigA : ∀ A', ParRed Γ A A' → A' = A) (hrigT : ∀ t', ParRed (A::Γ) t t' → t' = t)
    (hne : ¬ NormalEq (A::Γ) (.app e.lift (.bvar 0)) t) :
    ¬ CRStatement
```

`Γ ⊢ e ≡ .lam A t : .forallE A B` is built as `(IsDefEq.eta he).symm.trans (.lamDF hA hbody)`,
where `hbody` is `KStep.defeq`.  The `Eq.rec` witness discharges all nine hypotheses:
`A = Eq α a a` is a `Prop` and rule-free, hence `ParRed`-normal; `t = m.lift` is normal for a
variable `m`; `e` is normal, is not a λ, and is not a proof when `C` lands in `Type`.

**Consequence.**  `descend` being false is no longer the whole story.  Replacing it by
`descendV` + `hK` was supposed to leave `church_rosser` resting on the three injectivity holes
alone; but `CRStatement` is false at an `Eq`-registering instance, so if those three are true
— and they are theorems of Lean's type theory (`unique.tex`) — then the falsity has to live in
`NormalEq.parRed`, with or without K.  §S3 shows *where* it lives once K is added; §S4 shows
the statement was already unreachable.

**The two repair directions**, neither of which is a `Params` field:

* give `NormalEq` a closure at the K-redex position (`design-inductive.md` §7.6's second
  warning proposed exactly this: "allowing `NormalEq` a proof-irrelevance closure at the
  major-premise position"), or
* give `ParRedS` an eta-expansion step, so that `e ≫* .lam A (.app e.lift (.bvar 0))` and the
  K-step can then fire under the binder.

Both change `IsDefEq.church_rosser`'s conclusion, i.e. the confluence *interface*, and both
have to be checked against every consumer that **cases** on `NormalEq` — `Injectivity.lean`,
`NotProof.lean`, `HeadReduction.lean`.  That audit is the next round's job and it was not done
here.

## S5. `ParRed.weakN_inv`: what M3 buys, and what it does not

`KTable.kstep_liftN_inv` **[machine-checked]** gives
`KStep Γ' (.app (f.liftN n k) (h.liftN n k)) e' → ∃ e₀, Γ' ⊢ e' ≡ₚ e₀.liftN n k`.

The **equality** form is false once a liberal `kstep` is in `ParRed`, and that is not a
limitation of the proof:

> In `Acc r x :: Γ` the redex may fire with
> `c := Acc.intro x (fun y hy => Acc.inv (.bvar 0) hy)`, definitionally equal to the major
> premise by proof irrelevance and **mentioning `.bvar 0`**.  The ι-rule's right-hand side
> reads `g` off `c`, so the contractum mentions `.bvar 0` and is the lift of nothing.
> **[analysis]**

**The alternative was considered and rejected, and the reason is worth keeping.**  Restricting
`ParRed`'s K constructor to the canonical premise keeps `weakN_inv` at `=` and makes
`KDiamond` trivial — but it breaks `NormalEq.appDF_extra_of_descendV`, which fires the rule at
the premise its `NormalEq` hypothesis hands it (`c := b'`) and cannot show that one is
`kmajor` **on the nose**; showing it up to `≡ₚ` is what `canon` gives, and `≡ₚ` cannot satisfy
a syntactic side condition.  **The two obstructions pull in opposite directions: the descent
needs a liberal K-step, the lifting inversion wants a canonical one.**

## S6. Measurements **[measured]**

```
lake build Lean4Lean.Theory.Typing.KCanonical  -> Build completed successfully (71 jobs)

#print axioms Pattern.NoApp.matches_det     -> does not depend on any axioms
#print axioms VEnv.not_parRedStatement_of_hK-> [propext, Classical.choice, Quot.sound]
#print axioms VEnv.KStep.weakN              -> [propext, Classical.choice, Quot.sound]
#print axioms VEnv.KStep.instN              -> [propext, Classical.choice, Quot.sound]
#print axioms VEnv.parRedS_rigid            -> [propext, Quot.sound]
#print axioms VEnv.parRedS_lam_inv          -> [propext, Quot.sound]
#print axioms VEnv.kDiamond_of              -> [propext, sorryAx, Classical.choice, Quot.sound]
#print axioms VEnv.KTable.kstep_liftN_inv   -> [propext, sorryAx, Classical.choice, Quot.sound]
#print axioms VEnv.not_crStatement_of_kstep -> [propext, sorryAx, Classical.choice, Quot.sound]
#print axioms VEnv.parRedStatement_holds    -> [propext, sorryAx, Classical.choice, Quot.sound]
#print axioms VEnv.crStatement_holds        -> [propext, sorryAx, Classical.choice, Quot.sound]

forward cone scan (declaration values, `.thmInfo` via `value? (allowOpaque := true)`),
sorry-carrying declarations reached:
  Pattern.NoApp.matches_det        -> []
  not_parRedStatement_of_hK        -> []
  KStep.weakN                      -> []
  KStep.instN                      -> []
  not_crStatement_of_kstep         -> [forallE_inv_stratified]
  kDiamond_of                      -> [weakN_iff, forallE_inv_stratified, forallE_inv]
  KTable.kstep_liftN_inv           -> [weakN_iff, forallE_inv_stratified, forallE_inv]
  NormalEq.appDF_extra_of_descendV -> [weakN_iff, forallE_inv_stratified, forallE_inv]
  NormalEq.descendV                -> [weakN_iff, forallE_inv_stratified, forallE_inv]
  NormalEq.descend                 -> [weakN_iff, forallE_inv_stratified, forallE_inv]
  IsDefEq.church_rosser            -> [weakN_iff, forallE_inv_stratified,
                                       NormalEq.descend, forallE_inv]     (four)

lake env lean scripts/sorry-census.lean -> TOTAL declarations directly containing
                                           sorryAx: 19        (unchanged)
```

So the brief's "four today, three by the new route" is confirmed, and the new route's three are
the same three the old route already had — the new file adds nothing to the cone.
`not_parRedStatement_of_hK` reaches **no** hole at all: the refutation is unconditional on the
injectivity corner.

## S7. If the interface is repaired, `hK`'s remaining price

| §R3 site | verdict now |
|---|---|
| `ParRed.weakN` | **`KStep.weakN`** [machine-checked], empty cone |
| `ParRed.instN` | **`KStep.instN`** [machine-checked], empty cone |
| `ParRed.defeq` | `KStep.defeq` + `apply_pat` (unchanged) |
| `ParRed.defeqDFC` | routine (unchanged) |
| `ParRed.weakN_inv` | statement weakens to `≡ₚ`; content is **`KTable.kstep_liftN_inv`** [machine-checked] |
| `ParRed.triangle` ×3 | needs `CParRed.kstep`, then **`kDiamond_of`** [machine-checked], i.e. `KTable` + `KSmall` as `Params` fields |
| `NormalEq.parRed` `appDF` | routine (unchanged) |
| `NormalEq.parRed` `etaR` (`:2096`) | **FALSE**, §S3 — not "downstream of `weakN_inv`" |

`KTable` and `KSmall` have to become fields of `Params`; they cannot be hypotheses of
`ParRed.triangle`, because that propagates to `IsDefEq.church_rosser` and out into
`Injectivity.lean`, `NotProof.lean` and `Verify/`.  Adding two fields breaks every
construction site **[measured]**:

```
Lean4Lean/Theory/Typing/ParamsBuild.lean:52     paramsOfWF        (`where`)
Lean4Lean/Theory/Typing/ParamsBuild.lean:105    paramsOfDelta     (derived)
Lean4Lean/Theory/Typing/ParamsWitness.lean:132  propLoopParams    (`where`)
Lean4Lean/Theory/Typing/ParamsWitness.lean:217  propLoopParamsOfWF(derived)
Lean4Lean/Theory/Typing/PatternRules.lean:1784  paramsOfWF        (derived)
Lean4Lean/Theory/Typing/PatWF.lean:401          paramsOfIotaFree  (derived)
Lean4Lean/Theory/Typing/PatWFIota.lean:637      paramsOfPiInv     (derived)
Lean4Lean/Experimental/ParamsInstance.lean:164  paramsOfWF        (derived)
```

None of these is this stream's file.  At a δ-fragment instance both fields are one-line vacuous
(`refParams_kSmall`/`refParams_kTable` are the pattern); the generic `paramsOfWF` needs two new
arguments in the same shape as its existing `PatWF` residual.  **Do not spend this until §S4 is
resolved** — the fields buy a diamond for a statement that is false.

## S8. Corrections this round makes

| document | claim | correction |
|---|---|---|
| `docs/handoff-krule.md` §R3 table | `:2096` is "downstream of `ParRed.weakN_inv`" | It is independent, and it is **false**, not merely broken. §S3. |
| `docs/handoff-krule.md` §R3.1 | "Under `pat_major_canonical` … `weakN_inv` survives" | Only in `≡ₚ` form; the equality form is false for a liberal K-step regardless of M3. §S5. |
| `docs/handoff-krule.md` §R3.2 / the brief | the two-constructor `Prop` shape is the candidate refutation of `KDiamond` | Not a refutation: those contracta *are* `NormalEq`, by `proofIrrel`.  It is the cheap branch, and `KSmall` names it. §S2. |
| the brief | "if it refutes … our `Pat`-indexed generalisation cannot stand" | The premise does not arise.  What refutes is one level up and needs only *one* registered rule: `CRStatement`. §S4. |
| `docs/handoff-krule.md` §0.2, §R0.4 | adding `KStep` to `ParRed` "does not enlarge `IsDefEq`, so `kernel_sound`'s statement is untouched" | Still true of `IsDefEq`.  But it *does* break `NormalEq.parRed`, which the earlier rounds treated as a matter of proof effort. §S3. |
| `docs/design-inductive.md` §7.6 row I16 | M3 alone, "hard, ~400 lines" | Both `pat_small` and `pat_major_canonical` are needed; their consumers are `ParRed.triangle` (via `KDiamond`) and `ParRed.weakN_inv` — **not** the descent, which `KDescend.lean` closed without either.  Reinstate with `KCanonical.lean`'s `KSmall` and `KTable`, the versions that survived a satisfiability audit. |
| `docs/design-inductive.md` §7.6 warning 2 | "it *may* be the statement rather than the axiom that needs adjusting" | Confirmed, and no longer a conjecture. §S3, §S4. |
| `divergences.md:31` | `Params` has neither field | Still true of `Params`; both now exist as named statements in `KCanonical.lean`. |

Nothing in §§1–2, §4, `KRule.lean`, `KDescend.lean` or `DescendRefute.lean`'s three
refutations is contradicted, and none of those files was edited.

## S9. What to pick up first

1. **Decide how `NormalEq` (or `ParRedS`) grows**, §S4's two directions.  Everything else in
   this corner is downstream of that decision, including whether `KTable`/`KSmall` are worth
   adding to `Params` at all.  The audit that has to accompany it: every consumer that *cases*
   on `NormalEq` — `Injectivity.lean`, `NotProof.lean`, `HeadReduction.lean`,
   `ChurchRosser.lean` itself.
2. **Do not weaken `ParRed.weakN_inv` yet.**  It is only worth doing after (1), and the
   consumer at `:2096` is the case §S3 refutes.
3. **`NormalEq.descend` is still refuted and still in `church_rosser`'s cone**, and by §S4 it
   is no longer the only false thing there.  Deleting it is still right, but it no longer
   makes the route sound.


---

# Round 4 (this session): the restatement, and both refutations killed

**Task.** Design the corrected `NormalEq`/`ParRedS`; audit every consumer that *cases* on
`NormalEq` before changing the relation; re-run `not_crStatement_of_kstep` and
`not_parRedStatement_of_hK` against the restatement and show them **inapplicable**, with the
three `descend` refutations still standing; do **not** spend the `Params`-field change.

Same marks: **[machine-checked]** = a named `sorry`-free Lean declaration in this tree;
**[measured]** = a machine run whose output is reproduced; **[read]**; **[analysis]**.

## T0. Verdict

1. **The repair is in the reduction relation, not in `NormalEq`** — and that is the opposite
   of what §S4 and the brief nominated first.  `Lean4Lean/Theory/Typing/KEta.lean` (new,
   `sorry`-free) adds one guarded step, `EtaK`: *η-expand under `k ≥ 0` binders until the
   expansion is a registered K-redex, then fire it.*  `NormalEq` is **untouched**, and so are
   `CRStatement` and `ParRedStatement` — they are the same `Prop`s.  What changed is the
   relation they quantify over.  **[machine-checked]**

2. **Both refutations are dead, unconditionally, axiom-clean.**
   `VEnv.not_crStatement_of_kstep_dead` and `VEnv.not_parRedStatement_of_hK_dead`
   **[machine-checked, `#print axioms` = `[propext, Quot.sound]`, empty cones]**: over the
   enlarged relation `ParRedK`, *four of each refutation's hypotheses are jointly
   contradictory* — `he`, `hstep`, `hlam`, `hrig`.  No closure hypothesis, no `Params` field,
   no `hK`.  The hypothesis that dies is **`hrig`**, the rigidity of the witness: `Eq.rec α a
   C m a` is `ParRed`-normal and is *not* `ParRedK`-normal.  §T3.

3. **The consumer audit corrects the brief, and the correction is large.**
   `Injectivity.lean` and `NotProof.lean` **eliminate `NormalEq` zero times** — they mention
   it only in prose.  Across *both* import cones the only declarations outside this stream's
   files that eliminate `NormalEq` or `ParRed` live in **`Verify/Typing/ConstSpine.lean`**:
   four for `NormalEq` (untouched by this restatement) and **three for `ParRed`**, which need
   one new case each.  §T2.  **[measured, by a `.rec`/`.casesOn`/`.below` reverse scan over
   declaration values, not by grep]**

4. **Two of those three repairs are machine-checked here**, over `ParRedK`, verbatim
   statements: `ParRedK.forallE_inv`, `ParRedK.sort_inv`.  The third,
   `ParRed.constApp_inv`, consumes `EtaK.matches_head` **[machine-checked]**; its edit is
   given in §T5 and is **[analysis]**, because `VEnv.PatFreeHead` is defined downstream of
   `Theory/`.

5. **`hK` is discharged.**  `ParRedK.hK : KStep Γ a b → ParRedK Γ a b` **[machine-checked]**
   — `NormalEq.appDF_extra_of_descendV`'s only hypothesis.  `descendV` and
   `appDF_extra_of_descendV` need **no change**: both case only on `NormalEq` (unchanged) and
   *build* `ParRedS`, a positive occurrence.  §T4.

6. **The `Params`-field change was not spent**, as instructed.  §S7's eight construction
   sites are still eight, and `KTable`/`KSmall` are still only priced.  What the restatement
   adds to the diamond's price is one new residual, `EtaKDiamond`, stated and not proved.
   §T6.

7. **A reference-level finding, new and not in §4.**  `unique.tex`'s `thm:gg_compat`
   (Compatibility of `≫κ` with `≡ₚ`, `:167`) is **false at the same witness**, and its proof
   is missing the case: the bullet list has no η case for the *second* eta rule of `≡ₚ`.  The
   `thm:ckappa` proof papers over it with "The β and η rules are in `↝κ`" (`:251`) — η is
   **not** among `↝κ`'s rules (`:96–101`: β, δ, ζ, ι, ι_q, K⁺); it is in `≡ₚ` (`:118–119`).
   So this is not an artefact of the tree's `NormalEq`: the reference has the identical gap,
   and the repair this file lands is the reference's own missing rule.  §T7.  **[read +
   analysis]**  *Not sent to anyone, and must not be.*

## T1. What `EtaK` is, and why it is guarded

```lean
inductive EtaK : List VExpr → VExpr → VExpr → Prop where
  | here  {Γ e t t'} : KStep Γ e t → ParRed Γ t t' → EtaK Γ e t'
  | under {Γ e A B t} : Γ ⊢ e : .forallE A B →
      EtaK (A::Γ) (.app e.lift (.bvar 0)) t → EtaK Γ e (.lam A t)
```

Three things are deliberate, each forced.

* **It is not general η-expansion.**  A plain `e ≫ .lam A (.app e.lift (.bvar 0))` rule makes
  `ParRed` reflexively η-expand every Π-typed term, so `CParRed` has no complete development
  and `ParRed.constApp_inv` is false.  `EtaK`'s recursion must **bottom out in a real
  `KStep`** (`here`), so `EtaK` is empty wherever `KStep` is
  (`refParams_no_etaK` **[machine-checked]**) and fires only on constant-headed spines whose
  head is a registered pattern's head (`EtaK.matches_head`, `EtaK.spineHead_const`
  **[machine-checked]**).

* **`under` recurses, i.e. more than one binder.**  Not decoration: `Acc.rec C F`, short of
  *both* its index and its major premise, has `Acc.intro x (fun y hy => Acc.inv h hy)`
  well-typed with `x` a **bound** variable, so the K-step is two binders deep.  (`Eq.rec` is
  the one-binder case, and the two-binder version of *it* does not fire, because
  `Eq.refl α a : Eq α a b` forces `b ≡ a` and a bound `b` is not.)  **[analysis]**

* **`here` carries the contractum's parallel reduction**, so `EtaK` is the parallel-reduction
  form rather than the single-step form, and `here` with `t' = t` is exactly `hK`.  One
  hypothesis where the design otherwise needed two.

**Admissibility.**  `EtaK.defeqU` **[machine-checked]**: every `EtaK` step is already an
`IsDefEqU`, so `IsDefEq` — and therefore `Lean4Lean.kernel_sound`'s statement — is untouched.
Its `under` branch is, line for line, the derivation `not_crStatement_of_kstep` builds in order
to *refute* the old relation:

```lean
((IsDefEq.eta hty).symm).trans (.lamDF hA hbody)      -- hbody := KStep.defeq, under the binder
```

**That is the whole repair: the equation the refutation exhibits is admitted as a reduction.**
Its cone is `{forallE_inv_stratified, forallE_inv}` — the same two `KStep.defeq` and
`ParRed.defeq` already reach, and **no new hole** **[measured, §T8]**.

### Why not the other direction (grow `NormalEq`) — the check that decided it

§S4 offered two repairs and `docs/design-inductive.md` §7.6's second warning named the first
("a proof-irrelevance closure at the major-premise position").  It was tried on paper and
**it breaks the descent** — `NormalEq.descendV`, the one thing `KDescend.lean` closed.
**[analysis]**

> A K-closure on `NormalEq` has to be two-sided, because `NormalEq.symm` is a theorem.  Take
> `kstepR : KStep Γ e₂ e → Γ ⊢ e₁ ≡ₚ e → Γ ⊢ e₁ ≡ₚ e₂`.  `descendV`'s hypotheses are
> `Γ ⊢ g ≡ₚ g'` **and** `q.Matches g'`; in the `kstepR` case the sub-derivation relates `g` to
> the K-*contractum* `e`, and there is no `q`-match for `e` — the pattern matched `g'`.  There
> is nothing to recurse on.  The mirror constructor `kstepL` is worse in a different way: it
> recurses on `e`, which is not smaller than `g`, and `descendV`'s induction is
> `Nat.strongRecOn` on `sizeOf g`.
>
> Putting the closure inside the two eta constructors instead — `etaL`/`etaR` premised on
> `.app e'.lift (.bvar 0) ≫K w` and `w ≡ₚ e` — fails at the same point and more directly:
> `descendV`'s `etaL` case descends against `(.var q).Matches (.app e'.lift (.bvar 0))`, and
> `w` does not match.

The reduction side has the opposite polarity and therefore costs nothing there: `descendV`
and `appDF_extra_of_descendV` **case only on `NormalEq`** and **build** `ParRedS`.  §T4.

## T2. The consumer audit **[measured]**

The instrument is a reverse scan over declaration *values* (`ConstantInfo.value?` with
`allowOpaque := true`) for uses of `VEnv.NormalEq.rec / .casesOn / .recOn / .brecOn / .below`
and the same for `VEnv.ParRed` and `VEnv.CParRed`, run over **two** environments, because the
`Verify/Typing/Rigidity.lean` cone and the `Verify/Guard.lean` + `Experimental/ConeJoin.lean`
cone cannot be imported into one file (`Lean4Lean.VEnv.addDefEqList_defeqs_inv` is declared
twice).  Auto-generated `NormalEq.below.*`, `casesOn`, `recOn`, `brecOn`, `_unary` and
`match_*` are dropped from the tables below.

**Eliminates `NormalEq` — the complete list, both cones:**

| module | declarations | owner |
|---|---|---|
| `Theory/Typing/ChurchRosser.lean` | `NormalEq.defeq`, `.defeqDFC`, `.instN`, `.symm`, `.trans`, `.weakN`, `.weakN_inv_DFC`, `.descend`, `.parRed`, `ParRedExt.parRed_beta` | this stream |
| `Theory/Typing/HeadReduction.lean` | `IsDefEq.reduce_forallE`, `IsDefEq.reduce_sort` | this stream |
| `Theory/Typing/KDescend.lean` | `NormalEq.descendV` | this stream |
| `Theory/Typing/KCanonical.lean` | `not_crStatement_of_kstep`, `not_parRedStatement_of_hK` | this stream |
| **`Verify/Typing/ConstSpine.lean`** | `NormalEq.constApp_inv`, `.constApp_forallE`, `.constApp_sort`, `.constApp_whnf` | **not this stream** |

**`Injectivity.lean`: zero.  `NotProof.lean`: zero.**  Both mention `NormalEq` only in module
comments.  **This corrects the brief and §S9 item 1.**

**Eliminates `ParRed` — the complete list, both cones** (this is the list that *matters* for
the restatement):

| module | declarations | owner |
|---|---|---|
| `Theory/Typing/ChurchRosser.lean` | `ParRed.defeq`, `.defeqDFC`, `.instN`, `.weakN`, `.weakN_inv`, `.triangle`, `NormalEq.parRed` | this stream |
| `Theory/Typing/HeadReduction.lean` | `StRed.triangle` | this stream |
| `Theory/Typing/KCanonical.lean` | `parRedS_lam_inv` | this stream |
| `Theory/Typing/DescendRefute.lean` | `refParRed_bvar`, `_const`, `_constBvar`, `_id`, `_F3`, `_G2`, `_G3` | this stream |
| **`Verify/Typing/ConstSpine.lean`** | `ParRed.constApp_inv`, `ParRed.forallE_inv`, `ParRed.sort_inv` | **not this stream** |

`CParRed` is eliminated only by `CParRed.toParRed` and `ParRed.triangle`, both in
`ChurchRosser.lean`.

**So the entire audit surface outside this stream is three declarations in one file.**  That
is the measurement that decided the design: growing `NormalEq` costs four foreign
declarations *and* the descent; growing `ParRed` costs three foreign declarations and nothing
else.

## T3. The kill **[machine-checked]**

`ParRedK` is `ParRed` with one constructor added, `keta : EtaK Γ e e' → ParRedK Γ e e'`.  It
is a plain inductive (not mutual: `EtaK` is already defined, over `ParRed`), it contains
`ParRed` (`ParRed.toK`), and at the witness instance it *is* `ParRed`
(`refParams_parRedK_eq`).  It exists at every `Params` instance, which is what makes the two
theorems below unconditional — no `HasEtaK` hypothesis, no consistency caveat.

```lean
theorem not_crStatement_of_kstep_dead
    (he : Γ ⊢ e : .forallE A B)
    (hstep : KStep (A::Γ) (.app e.lift (.bvar 0)) t)
    (hlam : ∀ A' e', e ≠ .lam A' e')
    (hrig : ∀ o, ParRedK Γ e o → o = e) : False :=
  hlam A t (hrig _ (.keta (.under he (.here hstep .rfl)))).symm
```

and the same four lines for `not_parRedStatement_of_hK_dead`, with `hrig` over `ParRedKS`.

**Read this carefully, because it is the whole result.**  These four hypotheses are a
*sub-list* of the refutation's eleven (resp. nine); the only one whose truth value changes is
`hrig`.  In the old relation the witness `e := Eq.rec α a C m a` is normal — that is the
entire content of both refutations — and in the enlarged one it reduces, by exactly one step,
to `.lam A t`, the very term the refutations say nothing reaches.  Seven of
`not_crStatement_of_kstep`'s eleven hypotheses are **not needed at all**, including `hne` (the
`NormalEq` gap §S3 and §S4 diagnose).  *That* is the precise sense in which the repair belongs
to the reduction relation and not to `NormalEq`.

**Non-vacuity, stated honestly.**  The kill is conditional on `hstep` — the same `KStep`
hypothesis the refutation is conditional on.  So the kill and the refutation stand or fall on
identical footing: **wherever the refutation fires, the kill fires first.**  That is the
strongest form the "visibly kill its own witness" check can take here, and it is stronger than
a consistency check.  What is *not* shown is that any `Params` instance in this tree supplies
`hstep`; none does, because `paramsOfWF`'s `PatWF` is open in its ι and quotient cases
(`docs/handoff-params.md` §1.1).  `EtaK.eta_stuck_fires` **[machine-checked]** is the
non-vacuity pairing against the measured hole, in `KStep.stuck_fires`'s shape: the term
`whnf_app_bvar` proves weak-head normal is an `EtaK` redex *at the under-applied function*.

**The three `descend` refutations stand, unedited.**  `refParams_parRedK_eq`
**[machine-checked]** proves `@ParRedK refParams = @ParRed refParams`, because `KStep` and
hence `EtaK` are empty there (`refParams_no_kstep`, `refParams_no_etaK`).  All seven
`refParRed_*` lemmas and all three `not_descendStatement*` refutations are about that
instance, so they transfer verbatim and lose nothing.  `DescendRefute.lean` was not edited.

**The refutations' machinery survives too**, which is worth recording because it isolates the
failure: `parRedKS_rigid` and `parRedKS_lam_inv` **[machine-checked]** are
`KCanonical.lean`'s `parRedS_rigid` and `parRedS_lam_inv` re-proved for `ParRedK`.
`parRedS_lam_inv` gains exactly one case, closed by `EtaK.not_lam`.  Nothing in the
refutations is broken by the restatement *except* the rigidity of their witness.

## T4. `appDF_extra_of_descendV`, and why it needs no change **[machine-checked + analysis]**

`ParRedK.hK : KStep Γ a b → ParRedK Γ a b` **[machine-checked]** discharges the lemma's only
hypothesis.  Beyond that:

* `NormalEq.descendV` **cases on `NormalEq` and on `Pattern.Matches`, and on nothing else**
  (measured: it is in the `NormalEq`-eliminating table and *not* in the `ParRed`-eliminating
  one).  Every `ParRedS` in its proof is **constructed**.  Enlarging `ParRed` is a positive
  change there.
* `NormalEq.appDF_extra_of_descendV` likewise.  Its `ih1`/`ih2` take `ParRed` in negative
  position, but they are supplied by `NormalEq.parRed`'s induction and applied to steps the
  proof itself builds (`parRed_of_matches`), so a larger `ParRed` only makes them stronger.

**[analysis, and the honest limit of this claim]** the *statements* of both are written over
`ParRedS`; re-reading them over `ParRedKS` is the in-place edit of `ChurchRosser.lean`, not a
re-proof.  This round did not perform that edit (§T5), so "goes through" is verified as
*"casts on nothing that changes"*, by the structural measurement above, not by re-running the
proof.

## T5. The edit, stated exactly, and why it was not made

Landing the restatement is: add to `VEnv.ParRed` (`ChurchRosser.lean:576`)

```lean
  | keta : EtaK Γ e e' → Γ ⊢ e ≫ e'
```

making `ParRed` mutual with `EtaK` (moved into the same `mutual` block).  `ChurchRosser.lean`
is this stream's file.  **`Verify/Typing/ConstSpine.lean` is not**, and the edit reds it, so
the edit was not made.  The three cases it needs, with the lemma each consumes:

| site | new case | discharged by |
|---|---|---|
| `ConstSpine.lean:324` `ParRed.forallE_inv` | `\| keta h => obtain ⟨_,_,hc⟩ := h.spineHead_const; exact nomatch hc` | `EtaK.spineHead_const` — **verified as `ParRedK.forallE_inv`** |
| `ConstSpine.lean:330` `ParRed.sort_inv` | same | **verified as `ParRedK.sort_inv`** |
| `ConstSpine.lean:163` `ParRed.constApp_inv` | `\| keta h => obtain ⟨p₁,_,_,f,_,_,hpat,hm,hh⟩ := h.matches_head; …` then `hm.headConst`, `VExpr.headConst?_mkApp`, `hc _ _ hpat` — the same three lines as the existing `extra` case | `EtaK.matches_head` **[machine-checked]**; the assembly is **[analysis]** because `Pattern.headConst` and `VEnv.PatFreeHead` are defined in `ConstSpine.lean`, downstream of `Theory/` |

`ParRed.weakN`'s and `ParRed.instN`'s new cases are `EtaK.weakN` and `EtaK.instN`
**[machine-checked, empty cones]**.  `ParRed.defeq`'s is `EtaK.defeqU`.  `ParRed.defeqDFC`'s
is routine.  Everything else in §S7's table is unchanged.

## T6. What the restatement costs the diamond **[analysis]**

Unchanged: `KDiamond` still needs `KTable` + `KSmall` (`kDiamond_of`, §S2), and
**`Params` still gains no field this round.**  Added:

* `NonNeutralK` — `CParRed`'s neutrality test gains a third disjunct, `∃ e', EtaK Γ e e'`, and
  `CParRed.exists` must decide it classically.  Stated in `KEta.lean`.
* `EtaKDiamond` — two `EtaK` steps at one term must have `NormalEq`-close reducts.  **Not
  implied by `KDiamond`**: the two contracta live at different arities (different numbers of
  η-layers), which `KDiamond` does not see.  Stated, not proved; vacuous at `refParams`
  (`refParams_etaKDiamond`), and that is a consistency check, not evidence.
* **A termination obligation that is new and is *not* obviously discharged.**
  `CParRed.exists`'s structural recursion cannot handle `keta`: it recurses from `e` into
  `.app e.lift (.bvar 0)`, which is *larger*.  A measure does exist — the registered
  pattern's arity minus the term's application depth, which `EtaK.matches_head` bounds — but
  it has to be built, and it is the one genuinely new piece of work this design creates.
  Anyone landing `keta` should do this **first**; it is the step at which the design could
  still turn out to be wrong.
* `ParRed.weakN_inv` gets a *second* reason to weaken to `≡ₚ` form, on top of §S5's: a `keta`
  step at a lifted term produces a λ whose domain and body may mention the new binder.
  §S5's conclusion is unchanged, its cause is now over-determined.

## T7. The same gap in the reference **[read + analysis]**

`unique.tex`'s `≡ₚ` (`:113–119`) is `NormalEq` — reflexivity, compatibility, two eta rules,
proof irrelevance — and its `↝κ` (`:96–101`) is β, δ, ζ, ι, ι_q, K⁺.  **Neither has an
η-under-K route**, so the witness transfers:

> `e := \rec_{Eq}\,α\,a\,C\,m\,a`, `≡`-equal to `λ h. m` by η then K⁺ under the binder.  `e`
> and `λ h. m` are both `↝κ`-normal, so `e ≡κ λ h. m` reduces to `e ≡ₚ λ h. m`, which needs
> the second eta rule, i.e. `x : a=a ⊢ e\,x ≡ₚ m` — a K⁺-redex against a variable.  `≡ₚ` has
> no reduction and `C` may land in `Type`, so proof irrelevance is unavailable.

* **The false step is in `thm:gg_compat` (`:167`)**, and it is a *missing case*: the bullet
  list handles the eta rule only in the shape `e₁\,e₁' ≡ₚ (λx.e₃)\,e₃'`, never the second eta
  rule with the λ on the right and a compatibility `≫κ` under it.  At `e₁ = e`,
  `e₃ = λx.\,e\,x`, `e₂ = λx.\,m` there is no `e₄` with `e ≫κ e₄ ≡ₚ λx.\,m`, because `e` is
  `≫κ`-normal.
* **`thm:ckappa`'s proof (`:251`) papers over it**: "The β and η rules are in `↝κ`."  β is;
  **η is not** — it is in `≡ₚ` (`:118–119`), as `:120` says in as many words.  The composite
  `e ≡ λx.\,e\,x ≡ λx.\,m` is then discharged by transitivity of `≡κ`, which is Church–Rosser,
  which is `thm:gg_compat`.
* **The repair is the one landed here**: `K⁺` under η-expansion, as a rule of `↝κ`/`≫κ`.  This
  is a *second*, independent defect from §4's `Quot`-over-`Prop` one, at a different bullet of
  the same lemma, and unlike that one it does not need quotients — plain `Eq` suffices.
* **Scope registers.**  Our proxy: `not_crStatement_of_kstep` **[machine-checked]**.  The
  paper: **[read + analysis]**, above.  Lean itself: not a bug — `typesys.tex:19–52` already
  records non-transitivity of *algorithmic* equality, and §2.2's first probe measures that
  Lean reduces the redex.

**Not sent to anyone, and must not be** (`CLAUDE.md`).  If it is ever written up it belongs
beside `docs/upstream-report-ckappa-quot.md`, as a second section, not a second file.

## T8. Measurements **[measured]**

```
lake build Lean4Lean.Theory.Typing.KEta                  -> Build completed successfully (72 jobs)
lake build Lean4Lean.Verify.Typing.ConstSpine
     Lean4Lean.Theory.Typing.KCanonical
     Lean4Lean.Theory.Typing.HeadReduction               -> Build completed successfully (72 jobs)

#print axioms VExpr.headConst?_liftN                     -> [propext]
#print axioms VExpr.spineHead_liftN                      -> [propext]
#print axioms Pattern.Matches.spineHead_const            -> [propext]
#print axioms VEnv.EtaK.matches_head                     -> [propext, Quot.sound]
#print axioms VEnv.EtaK.spineHead_const                  -> [propext, Quot.sound]
#print axioms VEnv.EtaK.not_lam                          -> [propext, Quot.sound]
#print axioms VEnv.HasEtaK.hK                            -> [propext, Quot.sound]
#print axioms VEnv.ParRed.toK                            -> [propext, Quot.sound]
#print axioms VEnv.ParRedK.hK                            -> [propext, Quot.sound]
#print axioms VEnv.ParRedK.forallE_inv                   -> [propext, Quot.sound]
#print axioms VEnv.ParRedK.sort_inv                      -> [propext, Quot.sound]
#print axioms VEnv.not_crStatement_of_kstep_dead         -> [propext, Quot.sound]
#print axioms VEnv.not_parRedStatement_of_hK_dead        -> [propext, Quot.sound]
#print axioms VEnv.not_crStatement_of_kstep_inapplicable -> [propext, Quot.sound]
#print axioms VEnv.not_parRedStatement_of_hK_inapplicable-> [propext, Quot.sound]
#print axioms VEnv.EtaK.eta_stuck_fires                  -> [propext, Quot.sound]
#print axioms VEnv.EtaK.weakN                            -> [propext, Classical.choice, Quot.sound]
#print axioms VEnv.EtaK.instN                            -> [propext, Classical.choice, Quot.sound]
#print axioms VEnv.refParams_no_etaK                     -> [propext, Classical.choice, Quot.sound]
#print axioms VEnv.refParams_parRedK_eq                  -> [propext, Classical.choice, Quot.sound]
#print axioms VEnv.EtaK.defeqU                           -> [propext, sorryAx, Classical.choice, Quot.sound]

forward cone scan (declaration values, `.thmInfo` via `value? (allowOpaque := true)`),
sorry-carrying declarations reached:
  not_crStatement_of_kstep_dead          -> []
  not_parRedStatement_of_hK_dead         -> []
  not_crStatement_of_kstep_inapplicable  -> []
  not_parRedStatement_of_hK_inapplicable -> []
  EtaK.matches_head, EtaK.spineHead_const-> []
  ParRedK.forallE_inv, ParRedK.sort_inv  -> []
  ParRed.toK, EtaK.weakN, EtaK.instN     -> []
  refParams_parRedK_eq                   -> []
  EtaK.defeqU                            -> [forallE_inv_stratified, forallE_inv]

lake env lean scripts/sorry-census.lean  -> TOTAL declarations directly containing
                                            sorryAx: 19        (unchanged)
```

`EtaK.defeqU` adds **no** hole: its two are `ParRed.defeq`'s and `IsDefEqU.trans`'s, already in
the confluence cone.  **Both kills are axiom-clean** — not even `Classical.choice`.

## T9. Corrections this round makes

| document | claim | correction |
|---|---|---|
| the brief; `docs/handoff-krule.md` §S4, §S9 item 1 | the consumers to audit are `Injectivity.lean`, `NotProof.lean`, `HeadReduction.lean`, `ChurchRosser.lean` | `Injectivity.lean` and `NotProof.lean` eliminate `NormalEq` **zero times**.  The only foreign consumer, for either relation, is `Verify/Typing/ConstSpine.lean`.  §T2. **[measured]** |
| §S4 | two repair directions, `NormalEq` first | The `NormalEq` direction **breaks `descendV`**, in both of its two-sided forms.  The `ParRedS` direction costs three foreign one-line cases and nothing else.  §T1. |
| §S4, §S9 item 1 | "Both change `IsDefEq.church_rosser`'s conclusion, i.e. the confluence *interface*" | Not for the reduction-side repair: `CRStatement` and `ParRedStatement` are **unchanged `Prop`s**.  The interface is untouched; the relation grows underneath it. |
| §R3 table row `:2096`; §S3 | `NormalEq.parRed`'s `etaR` case is FALSE | It is false *for the relation in which the witness is normal*.  With `keta` the witness is not normal, and `EtaK.not_lam` **[machine-checked]** makes the `etaR × keta` configuration vacuous.  §T3. |
| §S0.2 | "`hK` is not landable as posed" | Correct, and the reason is now pinned: `hK` alone does not reduce the *under-applied* recursor.  `EtaK` does, and it subsumes `hK` (`ParRedK.hK`). |
| §S5 | `ParRed.weakN_inv` weakens to `≡ₚ` because a liberal K-step may invent a variable | Still true; `keta` gives a second, independent reason.  §T6. |
| §4 | the `Quot`-over-`Prop` gap is the defect in `thm:gg_compat` | It is **one** of two.  The other is the missing η bullet, needs only `Eq`, and is what this round's witness exhibits.  §T7. |
| `docs/design-inductive.md` §7.6 warning 2 | "allowing `NormalEq` a proof-irrelevance closure at the major-premise position" | The diagnosis was right and the prescription was not: the closure has to go in the reduction relation.  §T1. |

Nothing in §§1–2, §4's `Quot` analysis, `KRule.lean`, `KDescend.lean`, `KCanonical.lean` or
`DescendRefute.lean`'s three refutations is contradicted, and none of those files was edited.

## T10. Files, round 4

* `Lean4Lean/Theory/Typing/KEta.lean` — **new**, no `sorry`.  `EtaK`, `HasEtaK`, `ParRedK`,
  `ParRedKS`, the two kills in both conditional and unconditional form, the shape kit, the
  two `ConstSpine` repairs, `EtaK.weakN`/`.instN`, `NonNeutralK`, `EtaKDiamond`.
* `docs/handoff-krule.md` — this section.
* Everything else — **unchanged**.  In particular `ChurchRosser.lean`, `HeadReduction.lean`,
  `KCanonical.lean`, `KDescend.lean`, `KRule.lean`, `DescendRefute.lean` were **not edited**,
  and no file outside this stream was touched or reddened.

## T11. What to pick up first

1. **Build the `keta` termination measure** (§T6, third bullet) before landing anything.  It
   is the only new obligation the design creates, and it is where the design would fail if it
   is going to.  Pattern arity minus application depth, bounded by `EtaK.matches_head`.
2. **Then land `keta`**: the `ChurchRosser.lean` edit of §T5, together with the three
   `ConstSpine.lean` cases — which need the owner of `Verify/Typing/` to make them, or an
   explicit hand-over.  Two of the three are already verified here.
3. **Re-derive `NormalEq.parRed` for the enlarged relation.**  Its new `keta` case splits by
   the `NormalEq` constructor: `refl`, `proofIrrel`, `constDF` and `etaL` are one move each;
   `etaR` is **vacuous** (`EtaK.not_lam`); `appDF` is the real work and is the `appDF × extra`
   argument again, one η-layer up.
4. **Do not spend the `Params` fields** until 1–3 are done.  §S7's eight sites are still eight
   and the diamond is still priced, not proved.
