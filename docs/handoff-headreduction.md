# Handoff: pricing `Theory/Typing/HeadReduction.lean`

**Task.** Price `HeadReduction.lean` — what it proves, what it assumes, how much is
`sorryAx`-tainted, and whether it can deliver the alignment step the Π-injectivity circle
needs. Check it for the defect that killed `NormalEq.descend`. If neither reduction relation
in the tree can work, say so with evidence.

Marks used throughout, kept strictly separate:
**[machine-checked]** = a named `sorry`-free Lean declaration in this tree;
**[measured]** = a machine run whose output is reproduced;
**[read]** = read off source (this tree, `~/lean4/src/kernel`, or `~/lean-type-theory`);
**[analysis]** = neither.

---

## 0. The verdict, first

1. **`HeadReduction.lean` cannot deliver the alignment step, and the reason is measured, not
   argued.** Of its 203 declarations, **21** are `sorryAx`-tainted, and **every one of the 21
   is in the cone of `IsDefEqU.forallE_inv` or `IsDefEqU.forallE_inv_stratified`** — the two
   targets the alignment step exists to close. The 182 clean declarations are exactly those
   that never mention `HasType`/`IsDefEq`. **[measured, §1]**

2. **Its two candidate tools are the wrong shape even granted non-circularly.**
   `IsDefEq.reduce_forallE`'s conclusion is `∃ A' B', Γ ⊢ e ⤳* .forallE A' B'` — it relates
   `A' B'` to *nothing*. Closing `forallE_inv`'s `trans` needs the components related to
   `A B`, which is `NormalEq`-level Π-congruence, i.e. `church_rosser` itself. **[read, §3]**

3. **New, and unrecorded anywhere in `docs/`: the circularity is at subject reduction for β.**
   `ParRed.defeq`'s `beta` case (`ChurchRosser.lean:696`) retypes the argument through
   `IsDefEqU.forallE_inv ∘ IsDefEq.uniqU`. That is the single entry point through which the
   whole standardisation layer (`StRed.triangle`, `ParRedS.standard`) inherits the target.
   It is **structural, not incidental** — `HasType.app_inv` returns the domain of the
   *stored* Π and `HasType.lam_inv` returns the *annotation*, and nothing but Π-injectivity
   relates them. **[measured + read, §4]**

4. **New: `descend`'s and `church_rosser`'s failure is a specification gap, not a
   mathematical dead end.** `Theory/` registers only *constructor-matching* ι and quotient
   rules and therefore has **no K-like reduction**. Carneiro's κ has one (`K⁺`,
   `unique.tex:103` (stated) / `:107` (explained)); the real Lean kernel has one (`inductive.cpp:595 init_K_target`);
   **this repository's own implementation has one** (`Lean4Lean/Inductive/Reduce.lean`,
   `toCtorWhenK`). Only `Theory/` does not. `unique.tex:66` says in as many words that
   without such a device Church–Rosser "is not true … because of proof irrelevance".
   **This corrects `docs/handoff-descend.md` §4's "There is no right guard".** **[read, §5]**

5. **Machine-checked here** (`Theory/Typing/HeadRedStuck.lean`, new, no `sorry`): the
   stuck-K-redex lemma `whnf_app_bvar`, and — conditional on **one** clearly stated remaining
   obligation **(K)** — refutations of both `IsDefEq.reduce_sort` and
   `IsDefEq.reduce_forallE`. **[machine-checked, §6]**

6. **Answer to "can neither reduction relation work?"** As they stand, no — but the right
   conclusion is *not* "build a new reduction relation from scratch". It is: **the rule set
   is wrong before the relation is.** Adding `K⁺` is a prerequisite for any confluence
   argument in this tree, `ChurchRosser.lean`'s included. And even with `K⁺`, `Quot` at a
   `Prop` carrier looks like a residual confluence counterexample that neither the thesis nor
   the C++ kernel covers (§5.3, **[analysis]** — this one is not machine-checked and should
   be checked before it is relied on).

**Session or month?** Neither, as posed. Reviving `HeadReduction.lean` as an alignment tool
is not a unit of work that exists: it would require (a) adding `K⁺` to `Pat`/`VEnv`, (b)
re-cutting `ParRed.defeq`'s β case without Π-injectivity — for which no route is known — and
(c) re-proving `descend` at the enlarged rule set. (b) is the same obstruction the whole
corner has. §8 says what to pick up instead.

---

## 1. The measurement **[measured]**

Instrument: `scripts/`-style reverse-dependency scan reading declaration **values**
(`.thmInfo` handled explicitly — the trap `scripts/cone-measure.lean` documents). Scope:
every non-internal declaration whose defining module is
`Lean4Lean.Theory.Typing.HeadReduction`, cone taken over the whole import closure.

```
=== HeadReduction.lean declarations: 203
=== sorryAx-tainted: 21    clean: 182
=== the only sorry-carrying declarations anywhere in its import closure: 9
  IsDefEqU.const_app_inv            [Typing.Injectivity]
  IsDefEqU.const_forallE_inv        [Typing.Injectivity]
  IsDefEqU.const_sort_inv           [Typing.Injectivity]
  IsDefEqU.forallE_inv              [Typing.Injectivity]
  IsDefEqU.forallE_inv_stratified   [Typing.Injectivity]
  IsDefEqU.sort_forallE_inv         [Typing.Injectivity]
  IsDefEqU.weakN_iff                [Typing.UniqueTyping]
  NormalEq.descend                  [Typing.ChurchRosser]
  VIndRecArg.exists_indep           [Inductive.Decl]
```

Per-declaration attribution of the 21 (`<-` lists the holes actually reached):

| declaration | holes reached |
|---|---|
| `IsDefEq.reduce_sort` | `forallE_inv`, `forallE_inv_stratified`, `sort_forallE_inv`, `weakN_iff`, **`descend`** |
| `IsDefEq.reduce_forallE` | `forallE_inv`, `forallE_inv_stratified`, `sort_forallE_inv`, `weakN_iff`, **`descend`** |
| `InferType.exists` | same five |
| `InferType.hasType`, `InferType.inst`, `InferType.instN`, `InferTypeS.hasType` | `forallE_inv`, `forallE_inv_stratified` |
| `InferType.weakU_inv`, `InferType.weak'_inv`, `InferTypeS.weakU_inv` | + `weakN_iff` |
| `ParRedS.standard`, `StRed.triangle`, `StRed.triangleS`, `StRed.defeq`, `StRed.defeqDFC` | `forallE_inv`, `forallE_inv_stratified` |
| `WHRed.defeq`, `WHRed.hasType`, `WHRedS.defeq`, `WHRedS.hasType` | `forallE_inv`, `forallE_inv_stratified` |
| `WHRed.weakU_inv`, `WHRedS.weakU_inv` | `forallE_inv_stratified`, `weakN_iff` |

**Only 3 of the 21 touch `church_rosser`/`descend`.** The other 18 are tainted purely by the
injectivity family. So the file is not "blocked by Church–Rosser" — it is blocked by the
alignment target itself, one import lower.

Frontier (constants outside the module, directly used by it, whose cone carries a hole),
with use counts:

```
3x ParRedS.defeq [ChurchRosser]     3x IsDefEq.uniqU [UniqueTyping]
2x IsDefEqU.sort_inv [Injectivity]  2x IsDefEqU.sort_forallE_inv [Injectivity]
2x HasType.defeqU_l [UniqueTyping]  2x IsDefEq.church_rosser [ChurchRosser]
2x IsDefEqU.forallE_inv [Injectivity]
1x each: IsDefEq.apply_pat, IsDefEqU.weak'_iff, OnCtx.weak'_inv, ParRedS.hasType,
         IsDefEq.weak'_iff, IsDefEq.uniq, ParRed.defeq
```

And the **clean** upstream, which matters for what is salvageable:
`HasType.app_inv`, `HasType.lam_inv`, `HasType.forallE_inv`, `HasType.sort_inv`,
`IsDefEq.strong`, `HasType.matches_inv`, `VEnv.SortUniq` — **all `sorry`-free**. **[measured]**

### 1.1 What is clean inside the file — the salvage list **[measured]**

182 declarations, i.e. everything that talks only about reduction:

* `WHRed` (weak head reduction: `app` / `major` / `beta` / `extra`), `WHRed.determ`
  — **weak head reduction is deterministic, unconditionally, no `sorry`**;
* `WHNF`, `WHNF.bvar/sort/lam/forallE/subpattern`, `IsMajorPremise.whnf`, `WHNF.whRedS`;
* `WHRedS`, `WHRedS.determ`, `WHRedS.app/major/weak'/weakN/instN/defeqDFC/parRedS`;
* `StRed` (Kashima's standard reduction), `StRed.rfl/bvar_l/sort_l/lam_l/forallE_l/
  parRedS/whRed/weak'/weakN/instN/apply_pat`;
* `InferType` (the algorithmic inference relation), **`InferType.determ`**,
  `InferType.weak'`, `InferType.weakN`, `InferTypeS`, `InferTypeS.determ`,
  `InferTypeS.weak'`.

That is a real asset. Determinism of `WHRed`, of `WHRedS` to normal form, and of `InferType`
are the three facts a verified checker actually needs from a reduction relation, and they
cost nothing from the injectivity corner. **Whatever replaces this development should keep
them.**

---

## 2. What the file assumes

* **`variable [Params]`** throughout (`HeadReduction.lean:19`). `Params` carries `env`,
  `henv : env.WF`, `univs`, an abstract `Pat` table, and the semantic field `pat_wf`.
* **`Params` is inhabited** — `paramsOfDelta` (δ fragment) and the hand-built
  `PropLoopParams.propLoopParams` over `CycleConv.propLoopEnv`. **[read,
  `Theory/Typing/ParamsBuild.lean`, `ParamsWitness.lean`]** The old "nothing inhabits it"
  blocker is genuinely gone.
* **But `Params` over any environment with an ι or quotient rule is itself gated on the
  target.** `paramsOfWF`'s one open field is `PatWF`, and `ParamsBuild.lean:69-71` says
  plainly: "It is the ι and quotient cases that need `IsDefEqU.forallE_inv` (open,
  `Theory/Typing/Injectivity.lean`)". **[read]** So over *real* environments the whole
  `[Params]` development — `ChurchRosser.lean` and `HeadReduction.lean` both — sits behind
  the alignment target a **second**, independent time. Only the δ fragment escapes, and the
  δ fragment is not Lean.

* Every semantic theorem additionally takes `OnCtx Γ (IsType env univs)`. Unremarkable.

---

## 3. Can it deliver the alignment step? No — three independent reasons

The alignment step, stated as precisely as the tree states it:

* the residual of `IsDefEqU.forallE_inv` is its **`trans` case**
  (`Injectivity.lean:556-559`): "`Γ ⊢ .forallE A B ≡ e₂ ≡ .forallE A' B'` with `e₂`
  arbitrary; **needs `e₂` to reduce to a Π**. This is the normalisation statement the whole
  corner now rests on." **[read]**
* the residual of `forallE_inv_stratified` is `p ≈ w` inside `uniqQ`'s `app` case — a
  `SortUniq` instance one of whose witnesses is index-bounded and the other is not
  (`docs/handoff-injectivity.md` §3.2). **[read]**

**(a) Shape.** `IsDefEq.reduce_forallE (H : Γ ⊢ e ≡ .forallE A B : V) : ∃ A' B', Γ ⊢ e ⤳*
.forallE A' B'` — the conclusion says nothing relating `A' B'` to `A B`. Closing `trans`
needs `A ≡ A'` and `B ≡ B'`, which is `NormalEq.forallEDF`-level congruence, available only
from `CRDefEq` — i.e. from `church_rosser`, not from its `HeadReduction` corollary.
**[read]**

**(b) Circularity, direct.** `reduce_forallE`'s own proof calls `IsDefEqU.forallE_inv` at
`HeadReduction.lean:492` and `sort_forallE_inv` at `:499`, and runs through
`H.church_rosser` at `:490`. **[read; confirmed [measured] in §1]**

**(c) Circularity, structural — the finding.** See §4. Even deleting (a) and (b) leaves it.

For completeness: the same derivation *is* written down for the sort half, in
`docs/research-sort-inv.md` §1b, with the verdict "the derivation already exists, and it is
circular", pointing at `HeadReduction.lean:482`. The Π half had not been written down; it
is here.

**One genuinely open sub-question, worth naming because nobody has asked it.** With
`SortUniq` now a theorem relative to `forallE_inv_stratified`
(`docs/handoff-injectivity.md` §3), the `etaL` and `proofIrrel` cases of the
`reduce_sort`/`reduce_forallE` derivations stop needing `sort_inv` *as an unproved input*
and start needing only `forallE_inv_stratified`. That does **not** break the circle (the
`trans` case's whole point is that `forallE_inv_stratified` is what we are proving), but it
does mean the two theorems' dependency lists in §1 are heavier than their *mathematics*
requires. Anyone re-cutting them should re-derive rather than assume the list.

---

## 4. Subject reduction for β needs Π-injectivity — the structural circularity

`ChurchRosser.lean:691-699`, verbatim:

```lean
| beta _ _ ih1 ih2 =>
  have ⟨_, _, hf, ha⟩ := he.app_inv henv hΓ         -- hf : Γ ⊢ λA.b : ∀A₀.B₀ ; ha : Γ ⊢ a : A₀
  have ⟨⟨_, hA⟩, _, hb⟩ := hf.lam_inv henv hΓ       -- hb : A::Γ ⊢ b : B      (A = the annotation)
  have hf' := hA.lam hb                             -- Γ ⊢ λA.b : ∀A.B
  have ⟨⟨_, u1⟩, _⟩ := IsDefEqU.forallE_inv henv hΓ (hf.uniqU henv hΓ hf')   -- A₀ ≡ A
  replace ha := ha.defeqU_r henv hΓ ⟨_, u1⟩         -- retype  a : A
  ...
```

`HasType.app_inv` hands back the domain of the **stored** Π; `HasType.lam_inv` hands back the
λ's **annotation**; `IsDefEq.beta` needs the argument typed at the annotation. Bridging the
two *is* Π-injectivity. **[read]**

Both inversions are themselves clean (`HasType.app_inv`, `HasType.lam_inv` reach no `sorry`
— **[measured]**), so the taint enters at exactly this one line, and from there:

```
ParRed.defeq → ParRedS.defeq / ParRedS.hasType
             → WHRed.defeq, WHRedS.defeq, StRed.defeq, StRed.defeqDFC
             → StRed.triangle → StRed.triangleS → ParRedS.standard
             → IsDefEq.reduce_sort / reduce_forallE → InferType.exists
```

which is the whole 18-declaration tail of §1. **[measured]**

**Why it is structural rather than an artefact of this proof.** `IsDefEqStrong`
(`Theory/Typing/Strong.lean`) *does* have a `beta` constructor that carries `Γ ⊢ e' : A` at
the annotation, and `IsDefEq.strong` is clean **[measured]** — so it is natural to hope the
step is free from there. It is not. `HasType.app_inv`/`lam_inv` are both proved by peeling
`HasTypeStrong.defeq` steps down to a `base`; each peeled step carries an
`IsDefEqStrong Γ (∀A.B) (∀A₁.B₁) (.sort w)`, and recovering the domain relation across the
chain is `forallE_inv`'s own induction. **[analysis]**

**Consequence for the "build a new reduction relation" plan.** Any reduction relation whose
soundness lemma ("reduction implies conversion") is proved by induction with a β case will
hit this line. The escape is not a different relation but a different *statement*: a
relation whose β rule carries the annotation typing as a premise, as `IsDefEqStrong.beta`
does. Whether that relation can then be *related back* to an arbitrary `IsDefEq` derivation
is exactly the question, and no one in the tree has priced it — `docs/` has never proposed
`IsDefEqStrong` as a reduction base. **[analysis]**

---

## 5. The `descend` defect, re-diagnosed: a missing rule, not a false theorem

### 5.1 The tree has no K-like reduction **[read + machine-checked]**

`Theory/Typing/Pattern.lean:293`:

```lean
| .iota r m c n => .app (.varN (.const r) m) (.varN (.const c) n)
```

The major-premise position of every registered ι/quotient pattern is
`.varN (.const c) n` — it demands a **constructor application, syntactically**.
`Params.pat_simple` says every registered pattern is a `SimplePattern.toPattern`, i.e.
`.const c` (δ) or the above. So no rule can fire on a major premise that is a variable.

That is machine-checked here as `VEnv.whnf_app_bvar`
(`Theory/Typing/HeadRedStuck.lean`): for **any** `Params` instance,
`WHNF Γ f → (f is not a .lam) → WHNF Γ (.app f (.bvar i))`. All four `WHRed` rules are
eliminated, the `extra` case by the pattern argument above. **[machine-checked]**

### 5.2 Everything else has one **[read]**

* **Carneiro**, `~/lean-type-theory/unique.tex:103`, rule `K⁺`:
  `P` SS inductive, `Γ ⊢ intro inv[p,h] : α  ⟹  Γ ⊢ rec_P C e p h ↝_κ e inv[p,h] v`
  — fires at an **arbitrary** major premise `h`. `unique.tex:66`: "The standard formulation
  of the Church-Rosser theorem, when applied to the ↝ reduction relation, is not true; …
  Lean will not have unique normal forms, **because of proof irrelevance**." The whole
  κ/`≡_p` split, `K⁺` included, exists to answer exactly the objection that refutes
  `descend`.
* **The C++ kernel**: `~/lean4/src/kernel/inductive.cpp:595` `init_K_target` (single
  non-mutual inductive, `Prop`-valued, one constructor, no fields beyond parameters — i.e.
  `Eq`, `HEq`), consumed at `inductive.h:90,135`.
* **This repository's implementation**: `Lean4Lean/Inductive/Reduce.lean`, `toCtorWhenK`.

So `Theory/`'s rule set is **strictly weaker than both the specification it is mirroring and
the implementation it is specifying**. That is a divergence in its own right and belongs in
`divergences.md` (orchestrator's call; not written by this stream).

### 5.3 What this does to `docs/handoff-descend.md` §4

`handoff-descend.md` §4 argues, as **[analysis]**, that restricting `descend`'s `q` to
*registered* patterns does not save it, because at an ι-rule for a large-eliminating `Prop`
inductive the major premise is a proof, so witness A reappears at a registered pattern; and
it concludes "**The same argument reaches `IsDefEq.church_rosser` itself** … There is no
right guard: the guard would have to exclude `Eq`, and `Eq`'s ι-rule is in every real
environment."

**That conclusion is wrong as stated.** The guard is not on the pattern — it is a *missing
rule*. With `K⁺` in the rule set, `Eq.rec C m h` for a variable `h` **reduces to `m`**, the
diamond closes, and witness A's shape at a registered ι-pattern is repaired. The thesis
anticipated precisely this case and added the rule; this tree omitted it. **[read + analysis]**

What survives of `handoff-descend.md` unchanged:
* the three machine-checked refutations at `refEnv` — those are about `descend`'s
  **under-constrained `q`**, not about ι-rules, and are unaffected;
* the recommendation to restate `descend` with a `Pat`/`Subpattern` hypothesis on `q`;
* `appDF_proof_escape` closing E3.

What changes: **the reason E5 fails at a registered ι-pattern is a missing K⁺ rule, and it
is fixable.** "No normalisation argument can work" was already withdrawn once in this tree
(commit `ed036f8`); this is the second time an impossibility claim in this corner turns out
to be a claim about the tree's own definitions.

### 5.4 One residual that `K⁺` does **not** cover — flagged, not claimed **[analysis]**

`Quot` at a `Prop` carrier. With `α : Sort 0`, `Quot r : Prop`, so a variable `q : Quot r`
is a proof and `q ≡ Quot.mk r a` by proof irrelevance; `Quot.lift f h : Quot r → β` with
`β : Sort v`, `v > 0`, is a large elimination, so `Quot.lift f h q ≡ f a` while
`Quot.lift f h q` is reduction-normal (no `Quot.mk`) and is not a proof.

* Carneiro's `K⁺` is stated for **SS inductives**; `Quot` is a primitive, not an inductive,
  and `unique.tex` gives only `(ι_q) lift R f h (mk_R a) ↝_κ f a`. So the thesis's κ appears
  to have the same gap.
* The C++ kernel likewise requires `Quot.mk` (`~/lean4/src/kernel/quot.cpp`).

If this is right, it is a genuine hole in `unique.tex` §§3–4 rather than in this tree, and it
would mean `≡_κ = ≡` (`thm:ckappa`) fails for environments with `Quot` over a `Prop`. **This
is analysis, from reading the rules; it is not machine-checked and it has not been checked
against `unique.tex`'s later sections. Check it before relying on it.** If it holds, it is a
reference bug worth reporting upstream (the user decides whether and when).

---

## 6. What this stream landed: `Theory/Typing/HeadRedStuck.lean` **[machine-checked]**

New file, no `sorry`, ~150 lines, imports only `HeadReduction.lean`.

| declaration | statement | `sorry`-free? |
|---|---|---|
| `VEnv.whnf_app_bvar` | `WHNF Γ f → (∀ A e, f ≠ .lam A e) → WHNF Γ (.app f (.bvar i))` | **yes** |
| `VEnv.whRedS_app_bvar_eq` | the same under `⤳*` | **yes** |
| `VEnv.ReduceSortStmt` / `ReduceForallEStmt` | `IsDefEq.reduce_sort`'s / `reduce_forallE`'s types, packaged as `Prop`s (binders made explicit -- forced, a `Prop`-valued `def` cannot be introduced by `fun` past an implicit binder) | (defs) |
| `VEnv.reduceSortStmt_holds` / `reduceForallEStmt_holds` | each proved **by** the corresponding theorem — the anti-strawman check | no, tainted **deliberately** |
| `VEnv.not_reduceSortStmt_of_stuck` | a weak-head-normal `.app f (.bvar i)` definitionally equal to a sort refutes `ReduceSortStmt` | **yes** |
| `VEnv.not_reduceForallEStmt_of_stuck` | ditto for a Π | **yes** |
| `VEnv.reduceSortStmt_forbids_stuck` | contrapositive: `ReduceSortStmt` forbids such a term existing | **yes** |

`reduceSortStmt_holds` is the anti-strawman guard `docs/handoff-descend.md` §2.2 asks for:
`ReduceSortStmt` is `IsDefEq.reduce_sort`'s type verbatim, not a paraphrase, because the
theorem itself proves it.

**The one remaining obligation, isolated:**

> **(K)** Exhibit a `Params` instance, a context `Γ`, and terms with `f` weak-head normal,
> `f` not a `.lam`, and `Γ ⊢ .app f (.bvar i) ≡ .sort u : A` (or `≡ .forallE A B : V`).

Given (K), both `reduce_sort` and `reduce_forallE` are refuted outright, with no hypothesis
beyond what (K) supplies. **Everything else is done.**

### 6.1 Pricing (K) **[analysis]**

*It cannot be done on the δ fragment.* Checked by hand: with only δ-rules, a stuck
application is never definitionally a sort or a Π. Proof irrelevance would need
`Sort (u+1) ≡ Sort 0`; η never produces a sort or a Π on the right; δ-rules key on a bare
constant, so they never inspect an argument and never fire on a proof. So (K) genuinely
requires an ι or quotient rule — the δ fragment is not adversarial enough.
`CycleConv.propLoopEnv` (non-terminating head reduction, `Params` instance, `VEnv.WF`) was
tried as the adversarial witness and does **not** discharge (K): its cycle never reaches a
sort or a Π, so `reduce_sort`'s hypothesis is never satisfied there.

*The cheapest route is `VEnv.empty.addQuot` at a `Prop` carrier* (§5.4's shape), which is
also what `docs/handoff-descend.md` §4 recommends for its own unfinished half. Its cost:

| step | est. |
|---|---|
| `addQuot` environment + `VEnv.WF` | ~120 lines |
| `Γ ⊢ Quot.lift f h q ≡ f a` (proof irrelevance + the quot rule) | ~80 |
| the `Params` instance — **blocked**: needs `PatWF`'s quot case, which needs `forallE_inv` | carry `PatWF` as a hypothesis, ~30 |
| `WHNF` of the head `Quot.lift f h` (5-ary partial application) | ~60 |
| assembly | ~40 |

≈ 330 lines, **one session**, and the result is conditional on `PatWF` — an honest
hypothesis (it is a true statement of the type theory) but a hypothesis, exactly as
`DescendRefute.lean` carries `SortUniq`. **Not attempted this session.**

**Whether it is worth doing.** It refutes two theorems that §1 already shows are unusable for
the alignment step. Its real value would be as evidence for §5 — that the rule set, not the
theorem, is what is wrong. If §5.4's `Quot` analysis is confirmed first (cheaper, on paper),
(K) becomes the machine-checked form of it and is worth the session; if §5.4 is refuted,
(K) should be built with `Eq`'s ι-rule instead and will show only what `K⁺` already fixes.

---

## 7. Corrections this document makes

| document | claim | correction |
|---|---|---|
| `docs/handoff-descend.md` §4 | "There is no right guard: the guard would have to exclude `Eq`" | The guard is not on the pattern. The missing thing is the `K⁺` rule, which Carneiro's κ, the C++ kernel and this repo's own implementation all have and `Theory/` does not. **[read, §5]** |
| `docs/handoff-descend.md` §4 | "The same argument reaches `IsDefEq.church_rosser` itself … `church_rosser` is false for environments with an `Eq`-like ι-rule" | False *of this tree's rule set*, which is the honest scope. Not established for a rule set with `K⁺`. |
| `docs/handoff-descend.md` §5 | "the tree now has **no** candidate reduction relation. `HeadReduction.lean` … is the only remaining one" | Priced here: it is not a candidate, and the reason is not confluence but §1's measured circularity plus §4's structural one. |
| `docs/handoff-injectivity.md` §8 / `docs/handoff-weakn.md` §8 | "price `HeadReduction.lean` — it is the only untried one" | Priced. Verdict §0. |
| the task brief | "the *same* defect that killed `descend`" | Not the same defect. `descend`'s is an under-constrained `q`; `HeadReduction`'s is circularity, and its ι-flavoured trouble is a missing rule. |
| the task brief | "`ChurchRosser.lean` is compromised … do not build on it" | Correct as guidance, but the diagnosis needs §5: `descend` as *stated* is false; `descend` at a rule set with `K⁺` has not been refuted. |

Nothing in `docs/handoff-injectivity.md` §§1–3 was contradicted; §1's numbers were
independently re-measured this session and agree.

---

## 8. What to pick up first

1. **Settle §5.4 on paper (cheapest thing in this document).** Read `unique.tex` §§3–4 and
   `~/lean4/src/kernel/quot.cpp` for the `Quot`-over-`Prop` case. If the gap is real, it
   changes what "a correct reduction relation for Lean" even is, and it changes it for
   `ChurchRosser.lean`, `HeadReduction.lean` and any replacement equally. If it is not real,
   the fix in `unique.tex` is the template.
2. **Add `K⁺` to `Theory/`'s rule set** — `Pat`, `Pattern`, `VEnv.addInduct`'s emitted
   rules — and record the divergence. This is a prerequisite for *any* confluence argument
   in this tree and is independent of the injectivity corner. It also closes a genuine
   spec/implementation gap: `Lean4Lean/Inductive/Reduce.lean` does K-like reduction and
   `Theory/` does not specify it, so the implementation is currently *outside* its own
   specification on those inputs. Sizeable, and it belongs to whoever owns
   `Theory/Inductive/`, not to this stream.
3. **Do not attack `forallE_inv`'s `trans` through `HeadReduction.lean`.** §§1, 3, 4.
4. **The one unpriced idea worth a session** is the one §4 ends on and `docs/` has never
   proposed: a parallel-reduction relation **indexed by `IsDefEqStrong` derivations**, whose
   β rule carries the annotation typing as a premise (as `IsDefEqStrong.beta` already does),
   so that "reduction implies conversion" is definitional rather than derived. `IsDefEq.strong`
   is clean, so the entry point is free. The question that decides it — and that should be
   answered before any code — is whether the `trans` case of `forallE_inv`'s induction, which
   already runs **over `IsDefEqStrong`**, can consume such a relation without needing to
   bridge back to plain `IsDefEq`. If it can, the circle in §4 never has to be crossed.
   `docs/handoff-sortuniq.md` §5 records one negative structural fact about `IsDefEqStrong`
   that this idea must answer: composing `defeq` links needs a shared type index, and
   different links carry different levels.
5. Keep §1.1's 182 clean declarations. `WHRed.determ`, `WHRedS.determ` and
   `InferType.determ` are what a verified checker needs, and they are free of all of this.

---

## 9. Files

* `Lean4Lean/Theory/Typing/HeadRedStuck.lean` — **new**, no `sorry`. §6.
* `Lean4Lean/Theory/Typing/HeadReduction.lean` — **unchanged**.
* `Lean4Lean/Theory/Typing/ChurchRosser.lean`, `RawDefEq.lean` — **unchanged**. Nothing in
  `ChurchRosser.lean` was re-derived; its results remain suspect per the brief, and §5 says
  *why* they fail, which is not the same as saying they can be repaired without work.
* `docs/handoff-headreduction.md` — this document.

**Verification run at the end of this session [measured].**

```
lake build Lean4Lean.Theory.Typing.HeadRedStuck   -> Build completed successfully (57 jobs)
lake env lean scripts/sorry-census.lean           -> TOTAL ... containing sorryAx: 20
#print axioms whnf_app_bvar                       -> [propext, Quot.sound]
#print axioms whRedS_app_bvar_eq                  -> [propext, Quot.sound]
#print axioms not_reduceSortStmt_of_stuck         -> [propext, Quot.sound]
#print axioms not_reduceForallEStmt_of_stuck      -> [propext, Quot.sound]
#print axioms reduceSortStmt_forbids_stuck        -> [propext, Quot.sound]
#print axioms reduceSortStmt_holds                -> [propext, sorryAx, Classical.choice, Quot.sound]
#print axioms reduceForallEStmt_holds             -> [propext, sorryAx, Classical.choice, Quot.sound]
```

The census total is **20**, unchanged from the brief. This stream added no `sorry` and
removed none. Auto-bound-implicit audit of the new statements: `whnf_app_bvar`'s `#check`
shows `{Γ f i}` each used where intended and the `∀ (A e)` inside `hlam` genuinely bound by
that hypothesis -- no stray section variable, no under-constrained quantifier.

Mid-session, `Lean4Lean/Theory/Inductive/Lemmas.lean` was briefly red from another stream's
in-flight edit (`(kernel) invalid projection` at `:568,:574,:581`); it went green again on
its own and the numbers above are from after that.
