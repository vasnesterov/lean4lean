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
