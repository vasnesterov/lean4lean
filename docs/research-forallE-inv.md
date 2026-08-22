# How do we reach `IsDefEqU.forallE_inv`?

Scouting pass, read-only. Claims are tagged **[verified]** (read from source, mechanical
reasoning) or **[inferred]** (my analysis, not machine-checked). Every file claim cites
`file:line`.

Tree state at the time of this pass, checked first
(`git status --short`, `git log --oneline`):

```
HEAD 3128f64  feat: recApp_hasType''; pat_wf restated; pat_app_l removed
 M Lean4Lean/Theory/Inductive/Structure.lean
 M Lean4Lean/Theory/Inductive/TelescopeLift.lean
 M Lean4Lean/Verify/Typing/Lemmas.lean          (TrProj.weak' sorry closed)
?? Lean4Lean/Theory/Typing/PatternDecode.lean
```

*Calibration note.* My previous report said Option 4 of `docs/design-shape-lattice.md` was
"already applied in your tree". That was a transient read during another stream's
termination check, reported as settled state. I have checked `git status` and `git diff`
before every working-tree claim below, and I flag anything I read from a file that a live
stream owns.

---

> ## UPDATE — spike on obstacle (iii), at `6065f46`
>
> **Obstacle (iii) is refuted as an obstacle. Machine-checked.** I tried to build the
> counterexample and failed, and the failure is not "I ran out of ideas" — the positive
> statement that dissolves it is now proved, sorry-free, from mainline lemmas only, and its
> axiom cone is `[propext, Quot.sound]`. Details and the Lean text: **§9**, scratch file at
> `<scratchpad>/Descent.lean`.
>
> The one-line reason: substituting `VLevel.params U` for the levels of a derivation
> (a) makes *any* level `U`-well-formed (`VLevel.WF.inst` + `VLevel.params_wf`),
> (b) is the identity on `U`-well-formed terms (`VExpr.LevelWF.instL_id`),
> (c) preserves `≈` (`VLevel.inst_congr_l`), and
> (d) is admissible on derivations (`IsDefEq.instL`).
> So reflect at any `U'` you like and substitute back down; the conclusion, whose levels are
> already `U`-well-formed, is untouched.
>
> Consequences for the ranking below: route 1 loses its dominant unknown and keeps only the
> `trans'` obstacle, which is **half-proved and shares its blocker with `sort_inv`**. Route 3
> is retired — **neither** of the two fixes I costed is needed, so the migration keeps
> `SExpr.lean` byte-for-byte. Route 2's relative case is correspondingly weaker: I would now
> stay on the shape route. The revised recommendation is §10.

---

## Bottom line

**The narrowed reflection really is the shortest route.** *(As first written: "…and it is
not as narrow as hoped." The spike in §9 removed the reason for that caveat.)*

Ranked, risk-adjusted (revised after the spike):

| # | Route | Verdict |
|---|---|---|
| 1 | **Reflection `SExpr → VExpr`, narrowed at the conclusion** | The route. Of the three obstacles I named, (ii) was never real, **(iii) is now refuted (§9)**, and (i) `trans'` is half-proved with its blocker shared with `sort_inv`. The *fixup* the narrowing was supposed to buy is already proved (`IsDefEq.eqUpToLevels`, `Strong.lean:694`). |
| 2 | Full Carneiro conversion-alternation stratification | Still the fallback, and still delivers all three statements where the shape route delivers two. But ~2300 lines of churn against a route whose only remaining obstacle is shared with work already scheduled. Do not switch. |
| 3 | ~~Add level-WF side conditions to `SExpr.IsDefEq`~~ | **Retired by §9.** Not needed. Costing it was the third deliverable of the spike; the answer is that both fixes are unnecessary and the migration pays nothing. |
| 4 | Re-base the logical relation on `VExpr` | Prohibitive (8479 lines written against `SExpr`). Name it, don't take it. |
| 5 | Weaken/restate the three consumers | **Impossible.** All three genuinely need Pi-injectivity; §6 gives the failure point in each. |
| 6 | Read it off the set model | **Impossible.** `forallE_inv`'s conclusion is a derivation, and the interpretation is not injective. Witness in §5. |
| 7 | Confluence, given `sort_inv` for free | **Still circular**, and for a *different* reason than `sort_inv` was. §4. |

The one piece of unambiguously good news: `IsDefEq.eqUpToLevels` (`Theory/Typing/Strong.lean:694–698`)
is proved and sorry-free, and it is exactly the lemma the representative-choice
induction needs. **[verified]**

---

## 1. Does the already-proved `forallE_inv` family suffice? — No, for zero of three

**[verified]** `Theory/Typing/Lemmas.lean:740–795` proves three lemmas:

```lean
theorem IsDefEq.forallE_inv' (H : env.IsDefEq U Γ e1 e2 V) (eq : e1 = A.forallE B ∨ e2 = A.forallE B) :
    env.IsType U Γ A ∧ env.IsType U (A::Γ) B                          -- :740
theorem HasType.forallE_inv (henv) (H : env.HasType U Γ (A.forallE B) V) : … -- :786
theorem IsType.forallE_inv (henv) (H : env.IsType U Γ (A.forallE B)) : …     -- :794
```

Their conclusion is **`IsType`-ness of the components of one `∀`**. The injectivity lemma's
conclusion is **`IsDefEq` between the components of two `∀`s** (`Injectivity.lean:23–31`).
These are different statements; the proved family says nothing about a second Pi. So no
consumer can be served by it, and no restatement of a consumer can bridge the gap by
itself — a consumer that needs `A ≡ A'` cannot be handed `IsType A ∧ IsType A'`.

The three consumers, with what each actually uses. (Line numbers moved since your message:
`Verify/Typing/Lemmas.lean:2033` is now `:2095`, the file having grown.)

### Consumer A — `TrExpr.beta`, `Verify/Typing/Lemmas.lean:2094–2105`

```lean
| beta =>
    let ⟨_, .app hf ha tf ta, _, df⟩ := H
    let .lam hA tA tb := tf
    have ⟨⟨_, hA⟩, _, hb⟩ := hf.lam_inv henv hΓ
    have ht := hf.uniqU henv hΓ (hA.lam hb)
    have ⟨⟨_, Ae⟩, _, be⟩ := ht.forallE_inv henv hΓ
```

**Uses the domain half only.** `Ae` is used three times (`:2100` `.vlam Ae.symm`, `:2102`
`Ae.defeq ha`, `:2104` `.defeq Ae ha`); **`be` is never used again** — I grepped the whole
`have` block and `be` does not occur (the later `be'` at `:2103` is a different binder).
**[verified]**

The two Pis are: the one *stored* in `TrExprS.app` (`Verify/Typing/Expr.lean:110–113`,
`env.HasType … f' (.forallE A B)`), and the lambda's own, from
`HasType.lam_inv` (`Strong.lean:784`). `TrExprS.app` stores an arbitrary Pi — whichever the
caller's derivation happened to use — so nothing pins `A` to the lambda's domain.

> **So consumer A is unblocked by *domain-only* injectivity.** If a route delivers only the
> first conjunct of `forallE_inv`, that is one of the three consumers done. Worth knowing;
> I found no route that delivers the domain half more cheaply than both.

### Consumers B, C — `inferApp.loop.WF`, `Verify/TypeChecker/InferType.lean:276` and `:286`

```lean
have uf := hf'.uniqU henv hΔ hety                          -- :271
…
let ⟨_, .forallE _ _ hty hbody, h3⟩ := hfty                -- :275
have ⟨⟨_, uA⟩, _, uB⟩ := h3.trans henv hΔ uf.symm |>.forallE_inv henv hΔ
…
exact .inst henv hΔ (ha'.defeqU_r henv hΔ ⟨_, uA.symm⟩) ⟨_, hbody, _, uB⟩ …   -- :281
```

**Both halves are used**: `uA` retypes the argument, `uB` supplies the codomain's typing.
**[verified]** The two Pis here come from genuinely different places: `A₂,B₂` from
`AppStack.app` (`Verify/Typing/Lemmas.lean:2206–2212`), and `A₁,B₁` from the *syntactic*
`fType` the algorithm peeled.

**Verdict on Task 1: 0 of 3.** Cheapest-possible outcome ruled out.

---

## 2. The one thing that is already done: `eqUpToLevels`

Before the routes, the fact that changes their pricing. **[verified]**

```lean
inductive EqUpToLevels (U : Nat) : VExpr → VExpr → Prop     -- Strong.lean:228–235
  | bvar    : EqUpToLevels U (.bvar i) (.bvar i)
  | const   : (∀ l ∈ ls, l.WF U) → (∀ l ∈ ls', l.WF U) → List.Forall₂ (· ≈ ·) ls ls' → …
  | sort    : l.WF U → l'.WF U → l ≈ l' → EqUpToLevels U (.sort l) (.sort l')
  | app | lam | forallE : congruences

variable! (henv : Ordered env) (hΓ : OnCtx Γ (env.IsType U)) in
theorem IsDefEq.eqUpToLevels (H : env.IsDefEq U Γ e1 e2 A)
    (H1 : EqUpToLevels U e2 e2') : env.IsDefEq U Γ e1 e2' A     -- Strong.lean:694–698
```

`SExpr.mk` (`Experimental/SExpr.lean:166–172`) replaces each `VLevel` by `SLevel.mk`, and
`SLevel.mk u = SLevel.mk v ↔ u ≈ v` (`Bridge.lean:64`). So for `U`-level-WF `VExpr`s,
**`mk e = mk e'` is exactly `EqUpToLevels U e e'`**, and `eqUpToLevels` converts a
derivation about a chosen representative into one about the term you actually wanted.

That is the whole content of "the narrowing at the conclusion", and it costs nothing: it is
proved, in the mainline, sorry-free. Which means the narrowing does **not** need to be
argued for — but also that it buys less than hoped, because it touches neither named
obstacle (§3).

Also worth stating: **`mk : VExpr → SExpr` is surjective.**
`SLevel := { f : List Nat → Nat // ∃ l : VLevel, l.eval = f }` (`SExpr.lean:63`) carries its
own representative, and `SExpr` (`:101–107`) has exactly `VExpr`'s constructors with
`SLevel` in place of `VLevel`. So representative choice needs only `Exists.choose`, and
"general" reflection is stateable without knowing `A`, `A'`. **[verified]** The narrowing's
value is entirely in the fixup, not in the invertibility.

---

## 3. Route 1 — the narrowed reflection, and its three obstacles

The statement needed, twice (once per component):

```
SExpr.IsDefEq (Γ.map mk) (mk A) (mk A') (.sort u)  →  env.IsDefEqU U Γ A A'
```

The SExpr side delivers exactly the right shape. **[verified]**

```lean
theorem forallE_inv (hΓ : Ctx.WF Γ)
    (H : Γ ⊢ SExpr.forallE A₀ B₀ ≡ SExpr.forallE A₁ B₁ : .sort s) :
    ∃ u v, Γ ⊢ A₀ ≡ A₁ : .sort u ∧ A₀::Γ ⊢ B₀ ≡ B₁ : .sort v
```
(`ShapeLogRelAdequacy.lean:462–466`; the codomain is stated in `A₀::Γ`, matching
`Injectivity.lean:19`.) The forward bridge `VEnv.IsDefEq.toSExpr` (`Bridge.lean:176`) and
`OnCtx.toSExpr` (`:203`) are sorry-free, and the retype-at-a-sort step is already written
twice in `BridgeInjectivity.lean:56–66`.

### Obstacle (i): `trans'` — half-solved, and it shares `sort_inv`'s blocker

`SExpr.IsDefEq.trans'` (`SExpr.lean:662`) has no `VExpr` counterpart:

```lean
| trans' : Γ ⊢ A ≡ B : .sort u → Γ ⊢ B ≡ C : .sort v → Γ ⊢ A ≡ C : .sort u
```

**But its elimination is already proved, modulo one hypothesis.**
`Experimental/UniqueTyping.lean:207–231` defines `IsDefEq'`, the `trans'`-free variant, and
`:260–278` proves

```lean
theorem IsDefEq.toIsDefEq' (huniq : ∀ …, Γ ⊢ e₁ ≡ e₂ : .sort u → Γ ⊢ e₂ ≡ e₃ : .sort v → u = v)
    (h : Γ ⊢ e₁ ≡ e₂ : A) : Γ ⊢' e₁ ≡ e₂ : A
```

with `iff_isDefEq'` at `:281`. **[verified]** `huniq` is `IsDefEq.uniq_sort` (`:186`), which
needs `Ctx.WF Γ`; the docstring at `:252–259` explains the induction cannot maintain it in
the `beta` case and that the fix runs through `SExpr.IsDefEq.subst`.

`subst` now exists — `SExpr.lean:1270–1272` — but it is proved *via* `IsDefEq.strong`
(`:878–879`), which is still a `sorry` and still carries the `hu0` defect note
(`:764`, `:789`, `:867`). **[verified]**

> So obstacle (i) is not independent work: **`trans'`-elimination and `sort_inv` are blocked
> on the same keystone, `SExpr.IsDefEq.strong`.** Whatever pays for one pays for the other.
> That is a genuine reduction in the marginal cost of `forallE_inv`.

**The narrowing does not help here. [verified]** `toIsDefEq'` is an induction over the whole
derivation; `trans'` occurs at arbitrary depth. Knowing the conclusion's endpoints is
irrelevant.

### Obstacle (ii): `const` — *not* an obstacle, on the plain judgment

Your message named "the `CtorBundle`-carrying `const`". **That constructor is in
`IsDefEqStrong`, not in the judgment the reflection would consume.** **[verified]**

* `SExpr.IsDefEq.const` (`SExpr.lean:664–665`):
  `env.constants c = some ci → ls.length = ci.uvars → Γ ⊢ .const c ls : (SExpr.mk ci.type).instL ls`
  — no bundle. `IsDefEq'.const` (`Experimental/UniqueTyping.lean:212–213`) is identical.
* The `CtorBundle` version is `IsDefEqStrong.const` (`SExpr.lean:808–813`).

`SExpr.forallE_inv`'s conclusion is stated in plain `IsDefEq` (`ShapeLogRelAdequacy.lean:464`),
so the reflection's source is the plain judgment. The `CtorBundle` obstacle is real but it
lives on the `IsDefEq.strong` path (shared with `sort_inv`), not on the reflection path.

That is one obstacle fewer than you were carrying.

### Obstacle (iii): level well-formedness — new, with a witness

**This one is not in either of our lists, and it is the reason I do not think the narrowing
makes route 1 short. [verified witness, [inferred] severity]**

`VLevel.WF` is **syntactic** (`Theory/VLevel.lean:20–25`):

```lean
def WF : VLevel → Prop
  | .zero => True | .succ l => l.WF | .max l₁ l₂ => l₁.WF ∧ l₂.WF
  | .imax l₁ l₂ => l₁.WF ∧ l₂.WF | .param i => i < n
```

`SLevel` records only the *evaluation* (`SExpr.lean:63`), and the `SExpr` judgment
deliberately imposes no level conditions —
`Bridge.lean:18–20`: *"`SLevel` records only 'is the evaluation of some `VLevel`', so the
`SExpr` judgment imposes no level well-formedness conditions and no hypothesis relating `U`
to `Params.univs` is needed."*

**Witness that representative choice can produce a syntactically ill-formed level.** Take
`l := .imax (.param 7) .zero`. `VLevel.eval` (`VLevel.lean:33–39`) sends `.imax` to
`Lean.Nat.imax`, and `Lean.Nat.imax n 0 = 0`, so `l.eval ls = 0 = VLevel.zero.eval ls` for
every `ls`. Hence `SLevel.mk l = SLevel.mk .zero`. But at `U = 0`,
`VLevel.WF 0 l = (7 < 0) ∧ True = False`, while `VLevel.WF 0 .zero = True`.

So a chosen representative of a perfectly good `SLevel` need not be `WF`. This bites in two
places at once:

1. The `VExpr` constructors that check levels — `sortDF`, `constDF`, `extra`
   (`Theory/Typing/Basic.lean:22–31, 54–56`) — cannot be applied with an ill-formed
   representative.
2. `EqUpToLevels.sort`/`.const` (`Strong.lean:229–232`) require **both** sides WF, so the
   fixup lemma of §2 does not apply either.

Can the invariant be threaded instead of fixed? **No, not as the judgment stands.**
`SExpr.IsDefEq.const` (`:664`) admits *any* `ls : List SLevel` of the right length, so
"every level in this derivation has a `U`-WF representative" is not preserved by the rules.
**[verified]**

Two fixes, both real work:

* **(iii-a)** Add the WF side conditions to `SExpr.IsDefEq.const` and `.extra`, mirroring
  `VExpr`. `Bridge.lean`'s forward direction can supply them (the `VExpr` rules carry them),
  but every `.const`/`.extra` construction site in `ShapeLogRel.lean` (6122 lines) must be
  re-checked, and `Params.univs` — deliberately absent from the judgment — comes back.
  **Cost unmeasured.**
* **(iii-b)** Strengthen `SExpr.forallE_inv`'s *conclusion* to carry the invariant, which
  means strengthening the logical relation's `DefEq` payload. Larger.

I would price obstacle (iii) as the dominant unknown of route 1, and I would **check it
before anything else**: write the narrowed reflection statement, try to prove the `const`
case, and see whether the WF gap is real in practice or whether the derivations the LR
actually emits happen to stay inside the WF fragment. On this development that check has
repeatedly been the whole story.

> **↑ Everything from "So a chosen representative…" to here was written before the spike and
> is superseded by §9.** The witness above is correct and is now machine-checked; the
> *inference drawn from it* — that it obstructs the reflection — is wrong. The threading
> question ("can the invariant be threaded instead of fixed?") had the right answer, **no**,
> and the wrong conclusion: the invariant does not need to be threaded, because the levels
> can be repaired at the end instead of maintained throughout. Neither (iii-a) nor (iii-b)
> is needed.

### Summary of route 1 *(revised after §9)*

| Piece | Status |
|---|---|
| `mk` surjective; representative choice | **free** (`SExpr.lean:63`) |
| fixup `rep(mk A) → A` | **proved** (`Strong.lean:694`) |
| `trans'`-elimination | **half-proved**, blocked on `SExpr.IsDefEq.strong` — *shared with `sort_inv`* |
| `const`/`CtorBundle` | **not an obstacle** on the plain judgment |
| level well-formedness | **not an obstacle** — refuted in §9, machine-checked |
| `∃ U'` threading (monotonicity, finiteness) | **proved** in §9 |
| context well-formedness through the induction | **available** on the `VExpr` side (§9.4) — the step `toIsDefEq'` cannot take |
| congruence cases of the induction | mechanical, unwritten — the remaining bulk |

---

## 4. Route 7 — confluence, given `sort_inv`: still circular, and worse

You asked whether handing `sort_inv` to the confluence route breaks the cycle. **It does
not, and the reason is structurally deeper than last time. [verified]**

`IsDefEq.uniq` (`Theory/Typing/UniqueTyping.lean:13–111`) consumes
`IsDefEqU.forallE_inv_stratified` **directly**, at `:43`, in its `app` case:

```lean
  | app _ a2 a3 a4 _ a6 a7 _ _ ih3 =>
    intro (.app _ _ b3 b4 b5 _ b7)
    have ⟨_, c1, _, _, c3, c4⟩ := ih3 n IH hΓ … b5
    have ⟨_, _, d3, d4, d5⟩ := IsDefEqU.forallE_inv_stratified henv hΓ ⟨_, c1⟩ c3 c4
```

Handing it `sort_inv` removes the nine `sort_inv` calls (`:50, :54, :65, :69, :71, :80, :83,
:98, :108`) but not this one. And `IsDefEq.church_rosser` (`ChurchRosser.lean:1430`) is built
on `uniq` throughout — the `uniqU` / `trans_l` / `defeqU_*` family, all defined in
`UniqueTyping.lean:113–169`.

This is not an artefact of the repo's factoring; it is Carneiro's architecture.
`~/lean-type-theory/unique.tex`:

* `thm:utype` (`:40–42`) — unique typing **assumes** definitional inversion, whose clause 2
  (`:33`) *is* Pi-injectivity; the `app` case (`:51`) is line-for-line `UniqueTyping.lean:43`.
* `thm:1dinv` (`:258–278`) — inversion at `n+1` from κ-completeness at `n+1`, which needs
  Church–Rosser at `n+1`, which assumes unique typing at `n`.

So {inversion at n} → {unique typing at n} → {CR at n+1} → {inversion at n+1} is a genuine
cycle, and **the conversion-alternation index is the only known device that cuts it.**
Clause 1 (`sort_inv`) being available unstratified does not help, because clause 2 is on the
cycle independently.

Confirming again that the repo's index is the wrong one: `HasTypeStratified.defeq`
(`Strong.lean:856–857`) carries an **unstratified** `Γ ⊢ A ≡ B : .sort u` premise, so
"definitional inversion at `n`" is not stateable against it. **[verified]**

One nuance worth having, since it is the only good news here: `uniq`'s call at `:43` is at a
*strictly smaller* index (`c3`, `c4` at `n-1`; the surrounding induction is
`WellFounded.induction Nat.lt_wfRel.2` at `:25–26`). So `uniq` and `forallE_inv_stratified`
could in principle be a single mutual induction — which is exactly what Carneiro does — but
the CR step inside it must then be available at bounded index, and that is the re-indexing.

---

## 5. Route 6 — the set model: impossible, with a witness

**[verified reasoning]** Two independent reasons, either sufficient.

**(a) The conclusion is positive; the interpretation is not injective.** `forallE_inv` must
*produce* a derivation `env.IsDefEqU U Γ A A'`. A model can refute derivability
(`sort_inv`'s `u ≈ v`, `sort_forallE_inv`'s `False`); it cannot manufacture a derivation
without a completeness theorem, and there is none — the interpretation identifies strictly
more than defeq does. Witness: every *true* proposition is sent to the same set.
`Universe.lean:75` gives `p ∈ UProp → p = ∅ ∨ p = {pt}`, so two provable but definitionally
distinct props both interpret to `{pt}`. Injectivity of `⟦·⟧` therefore fails outright, and
with it any extraction of a derivation.

**(b) The soundness ledger already says the model does not need it, and the gating is the
wrong way round.** `InterpSound.lean:1062, 1108` and `Interp.lean:32` record
`IsDefEqU.forallE_inv` as **not needed** by soundness; and the interpretation is gated on
`sort_inv` through `LevelAssign` — which my previous pass showed is *equivalent* to
`sort_inv` (`Interp.lean:272–274`, `lvl_uniq`). So the model both cannot supply
`forallE_inv` and does not want it.

The growth in `SetModel/` since my last pass (`Quot`'s value layer, `cnstOf`, the prelude
specs) does not change either point: it is all downstream of `LevelAssign`.

---

## 6. Route 5 — restating the consumers: impossible in all three

**[inferred, but each failure point is concrete.]**

### Consumer A

The obligation is `IsDefEq.beta` (`Theory/Typing/Basic.lean:45–47`):

```lean
| beta : A::Γ ⊢ e : B → Γ ⊢ e' : A → Γ ⊢ .app (.lam A e) e' ≡ e.inst e' : B.inst e'
```

It is stated at **the lambda's own domain**. `TrExpr.beta` has `ha : HasType Γ a' A` for the
*stored* Pi's domain, so it must convert. Two escapes fail:

* *Prove `HasType Γ (.lam A'' b) (.forallE A B) → IsDefEqU Γ A A''` directly.* The induction
  dies at `defeqDF` (`Basic.lean:44`): the intermediate type `X` in
  `IsDefEq Γ X (.forallE A B) (.sort u)` need not be syntactically a `.forallE`, so the IH
  does not apply. Same failure at `trans`, `symm`, `proofIrrel`, `extra`. This statement is
  Pi-injectivity, not a weakening of it.
* *η-expand first.* `IsDefEq.eta` (`:48–50`) gives
  `.lam A (.app e.lift (.bvar 0)) ≡ e : .forallE A B` at the **stored** domain `A`, which is
  what we want — but then β-reducing the body returns `.app e a'` unchanged. η then β is the
  identity; it moves nothing.

* *Redesign `TrExprS.app`* (`Verify/Typing/Expr.lean:110–113`) so the stored Pi is canonical:
  not statable — "canonical" is not a property of the syntax, and `TrExprS` must stay closed
  under weakening and context conversion.

### Consumers B, C

The loop's invariant already shares one type: `hfty : c.TrExpr (fType.instantiateList lm) fty'`
and `hety : c.HasType e' fty'` name the same `fty'` (`InferType.lean:254`). The second Pi
comes from `AppStack.app` (`Verify/Typing/Lemmas.lean:2206–2212`).

Note that half the work is already injectivity-free: from `h3 : IsDefEqU Γ (.forallE A₁ B₁) fty'`
and `hety`, `IsDefEq.defeqDF` gives `HasType Γ e' (.forallE A₁ B₁)` with no inversion. What
remains is `HasType Γ a'' A₁`, and the only source of `a''`'s typing is the AppStack's `A₂`.

* *Drop the Pi from `AppStack.app`.* Then recover it with `HasType.app_inv`
  (`Strong.lean:769–776`) — which returns `∃ A B, …`, an arbitrary Pi again. No gain.
* *Weaken `inferType.WF` to "the returned type is **a** type of the term".* Does not help:
  the returned type is the translation of `fType.bindingBody!.instantiate1 a`, i.e.
  `B₁.inst a''`, and building `HasType Γ (.app f' a'') (B₁.inst a'')` via `IsDefEq.appDF`
  still needs `a'' : A₁`.
* *Use the simple recursive `inferType` app case instead of the `inferApp` spine.* Same
  shape, same need.

> **This is not a repo artefact either.** Every verified kernel I know of needs Pi-injectivity
> (MetaCoq's `cumul_Prod_inv`) for exactly this step. The content of `inferType.WF` *is*
> "the Pi the algorithm peeled is the Pi the typing rule wants".

### One thing that *is* restatable

`Params.pat_wf` (`ChurchRosser.lean:36–39`) — the field you have parked. Its docstring
(`:21–33`) says both available routes go through a well-formed context; what it does not
say is that the `IsDefEq.uniq` route additionally needs Pi-injectivity, and so does the
`HasType.app_inv` route, since `app_inv` returns an arbitrary Pi and the rule's arguments
must be typed at Δ's *declared* domains. **[inferred]** Parking it as an interface
obligation is the right call; it is downstream of `forallE_inv`, not parallel to it.

---

## 7. Route 2 — the Carneiro stratification, re-priced upward

My last report ranked this second and said "only if 1 stalls". **The finding that the shape
route structurally cannot reach `forallE_inv` changes the comparison, and I want to state
that plainly.**

* The shape route delivers `sort_inv` and `sort_forallE_inv`. Both have conclusions outside
  `VExpr` (`u ≈ v`; `False`), which is exactly why they need only the forward bridge —
  `BridgeInjectivity.lean:7–11` says so.
* The Carneiro stratification delivers **all three**, unstratified, by taking `n` large, and
  its destination is published and known true (`unique.tex:282–288`).
* Both need the same `VEnv.Params` instance, which is now much closer than at my last pass:
  `addInduct_WF` is proved (commit `dd994a4`), and `Theory/Typing/PatternDecode.lean`
  (untracked, in flight) is building the `Pat` decoder — its module docstring `:11–33`
  explains why it must be syntactic rather than an environment traversal.
* Cost, unchanged from my last estimate: a `⊢_n`/`≡_n` pair with basics (300–500 lines);
  `IsDefEq.uniq` re-proved on that index (`UniqueTyping.lean:13–111`, 150–250 lines); and
  `ChurchRosser.lean` re-indexed (1475 lines, ~90 calls into the `uniq` family, 22 lemma
  statements). Call it 2000–3000 lines of churn on finished proof, plus the `extra` case at
  `ChurchRosser.lean:1295` and the two missing `Params` fields (`PLAN.md:194–200`).

**The comparison I would actually make:** route 1's remaining cost is
`SExpr.IsDefEq.strong` (shared with `sort_inv`, so already paid for) **plus** obstacle (iii),
which is unpriced and could be anywhere from a hundred lines to an `SExpr.lean` refactor,
**plus** the reflection induction itself. Route 2's cost is large but *known*. If obstacle
(iii) turns out to require fix (iii-a) or (iii-b), the two routes are close enough that I
would not bet on route 1.

> **Superseded by §9.** Obstacle (iii) requires neither fix. Route 1's remaining cost is
> `SExpr.IsDefEq.strong` — already on the `sort_inv` bill — plus the reflection induction.
> Route 2 loses the comparison and I would not switch. Revised recommendation: §10.

---

## 8. Recommendation *(as written before the spike — see §10 for the revision)*

1. **Spend one session on obstacle (iii) before anything else.** Write the narrowed
   reflection statement for a single component, and attempt only the `const` case. The
   question is whether an `SExpr.IsDefEq` derivation between images of level-WF `VExpr`s can
   traverse ill-formed levels. If it cannot — i.e. if the invariant *is* maintained on the
   derivations the LR emits — route 1 is short and clearly right. If it can, you are choosing
   between (iii-a), (iii-b) and route 2, and you should make that choice deliberately.
   Consider also trying to *refute* the narrowed reflection outright: `SExpr.IsDefEq` is
   strictly more permissive on levels than `VExpr.IsDefEq`, and this development's record on
   "statements that resist proof" is four for four.
2. **Do not re-open the confluence route, and do not spend on `ChurchRosser.lean:1295` for
   this purpose.** §4 is decisive: `UniqueTyping.lean:43` is on the cycle independently of
   `sort_inv`.
3. **Do not look to the set model.** §5, witness in hand.
4. **Do not attempt to restate the consumers.** §6; all three fail, and consumer A fails at
   `IsDefEq.beta`'s statement itself.
5. **Record now that consumer A needs only the domain half** (`be` unused at
   `Verify/Typing/Lemmas.lean:2099`). If any partial result lands, that is one of three
   consumers closed, and it is the one in the file a live stream is already editing.
6. **Keep `Params.pat_wf` parked.** It is downstream of `forallE_inv` by both available
   routes, and unparking it will not be cheap until this lands.

### Corrections to your framing, for the record

* The `CtorBundle`-carrying `const` is **not** an obstacle to reflection — it is in
  `IsDefEqStrong` (`SExpr.lean:808`), not in the plain judgment the reflection consumes
  (`:664`).
* `trans'` is **half-solved already** (`Experimental/UniqueTyping.lean:260–281`) and shares
  its blocker with `sort_inv`, so its marginal cost is near zero.
* The narrowing buys the *fixup*, and the fixup is **already proved** (`Strong.lean:694`).
  It buys nothing else.
* ~~There is a **third** obstacle, level well-formedness, and it is the one I would plan
  around.~~ **Withdrawn: §9.** The witness was right, the inference from it was wrong.

---

# 9. Spike: obstacle (iii), refuted

Executed at `6065f46` (`M Theory/Inductive/{Structure,StructureClosed,TelescopeLift}.lean`,
`M Theory/Typing/PatternDecode.lean`, `M Verify/Typing/{Expr,Lemmas}.lean`). Nothing under
`Lean4Lean/Experimental/` was touched — it could not even be imported, since its `.olean`s
are stale against the modified `Theory/Inductive` and `Theory/Typing` sources. Everything
below therefore imports **only** `Lean4Lean.Theory.Typing.Strong`, which is a stronger
result than I set out to get: the resolution needs nothing from the migrating files.

Full text: `<scratchpad>/Descent.lean`, 170 lines. Every declaration below is
machine-checked, `sorry`-free, and `#print axioms` reports `[propext, Quot.sound]`.

## 9.1 The refutation attempt, and where it fails

The counterexample I was hunting had to be: `A`, `A'` level-well-formed at `U`, `Γ`
well-formed, with `SExpr.IsDefEq (Γ.map mk) (mk A) (mk A') X` derivable and
`env.IsDefEqU U Γ A A'` not — the SExpr derivation forced through levels no `U`-well-formed
`VExpr` can express.

**It cannot exist, because the ill-formed levels can be repaired at the end rather than
avoided throughout.** The repair is substitution of `VLevel.params U`, and the mainline
already has every property it needs:

| Property | Lemma | Cite |
|---|---|---|
| makes **any** level `U`-WF | `VLevel.WF.inst` + `VLevel.params_wf` | `VLevel.lean:143`, `:130` |
| identity on `U`-WF levels/terms | `VLevel.inst_id`, `VExpr.LevelWF.instL_id` | `VLevel.lean:132`, `VExpr.lean:175` |
| preserves `≈` | `VLevel.inst_congr_l` | `VLevel.lean:164` |
| admissible on derivations | `IsDefEq.instL` | `Lemmas.lean:593–595` |
| discharges the residual slack | `IsDefEq.eqUpToLevels` | `Strong.lean:694–698` |

The first three are exactly the properties I had failed to look for when I wrote §3. The
crucial one is the **first**: `VLevel.inst` sends `.param i ↦ ls.getD i .zero`
(`VLevel.lean:113–118`), so out-of-range parameters go to `.zero` *by definition of the
substitution*, and `WF.inst` then makes the result `U`-WF unconditionally. There is no
invariant to maintain.

## 9.2 Reflecting *up*: the level side conditions cost nothing

The three `SExpr` rules with no level premise reflect at a large enough `U'`, each in two
lines. `VLevel.exists_wf`/`exists_wf_list` supply the bound; `IsDefEq.mono_uvars` combines
the branches of an induction by taking the max. All proved in the spike file.

```lean
theorem const_case_reflects {env : VEnv} {Γ : List VExpr} {c ci} {lsᵥ : List VLevel}
    (h1 : env.constants c = some ci) (h2 : lsᵥ.length = ci.uvars) :
    ∃ U', env.IsDefEq U' Γ (.const c lsᵥ) (.const c lsᵥ) (ci.type.instL lsᵥ) := by
  obtain ⟨U', hU'⟩ := VLevel.exists_wf_list lsᵥ
  exact ⟨U', .constDF h1 hU' hU' h2 (Lean4Lean.List.Forall₂.rfl fun _ _ => rfl)⟩
```

`sort_case_reflects` and `extra_case_reflects` are the same three lines against
`SExpr.lean:663` and `:679`. **That is the whole of the `const` case this spike was scoped
to.** It is not hard; it was only ever hard if you insisted on reflecting at the ambient `U`.

The type also lands on the nose, with no `≈`-slack: `SExpr.mk_instL` (`Bridge.lean:107–110`)
gives `mk (ci.type.instL lsᵥ) = (mk ci.type).instL (lsᵥ.map mk)`, and a representative
function is a genuine section of `SLevel.mk` (`SExpr.lean:63` carries the witness), so
`lsᵥ.map mk = ls` exactly.

## 9.3 Descending back down

```lean
/-- Same skeleton, `≈`-equivalent levels, no well-formedness demanded — i.e. `mk e = mk e'`. -/
inductive SameLevels : VExpr → VExpr → Prop | bvar | const | sort | app | lam | forallE

theorem descent {env : VEnv} {Γ : List VExpr} {U U' : Nat}
    (henv : Ordered env) (hΓ : OnCtx Γ (env.IsType U))
    (H : env.IsDefEq U' Γ e₁ e₂ A)
    (h1 : SameLevels e₁ a₁) (h2 : SameLevels e₂ a₂)
    (w1 : a₁.LevelWF U) (w2 : a₂.LevelWF U) :
    env.IsDefEqU U Γ a₁ a₂
```

A derivation at **any** universe-parameter count, between terms that agree up to level
equivalence with `U`-level-well-formed terms, descends to `U`. The proof is eleven lines:
`instL (params U)` the whole derivation, note the context is unchanged
(`CtxStrong.strong … |>.levelWF` plus `LevelWF.instL_id` pointwise), and discharge the two
endpoints with `eqUpToLevels`.

`SameLevels` is definitionally the relation `SExpr.mk e = SExpr.mk e'` — same skeleton,
componentwise `≈` levels — by `SLevel.mk_inj` (`Bridge.lean:64`). I state it natively rather
than as `mk e = mk e'` only so the file need not import `Experimental/`.

## 9.4 A second thing the spike settled

`toIsDefEq'` cannot maintain `Ctx.WF` through its induction, because neither
`SExpr.IsDefEq.beta` nor `IsDefEqStrong.beta` carries a premise typing the binder — the
docstring at `Experimental/UniqueTyping.lean:252–259` records this, and it is why
`uniq_sort`'s hypothesis is not dischargeable there.

**The reflection induction does not inherit that problem**, because the `VExpr` side has
`IsDefEq.isType` (`Lemmas.lean:872–873`) and the `SExpr` side has no analogue:

```lean
example (henv : Ordered env) (hΓ : OnCtx Γ (env.IsType U)) (h : env.HasType U Γ e' A) :
    OnCtx (A :: Γ) (env.IsType U) := ⟨hΓ, h.isType henv hΓ⟩
```

`beta`'s second premise types `e'` at `A`, which already makes `A` a type. So the context
well-formedness that `eqUpToLevels` needs at every node is available. Machine-checked.

## 9.5 The witness, machine-checked

```lean
example : ¬ VLevel.WF 0 (.imax (.param 7) .zero) := by decide
example : VLevel.WF 0 .zero := by decide
example : (VLevel.imax (.param 7) .zero) ≈ (VLevel.zero) := by
  simp [VLevel.equiv_def, VLevel.eval, Lean.Nat.imax]
```

The witness from §3 is real: these two `VLevel`s share an `SLevel` and only one is
well-formed at `U = 0`. What §3 got wrong was the inference — a representative *can* be
ill-formed, and it does not matter.

## 9.6 Costing the two fixes — the spike's third deliverable

* **(iii-a)** WF side conditions on `SExpr.IsDefEq.const` and `.extra`: **not needed.**
* **(iii-b)** Strengthened LR payload: **not needed.**

So the answer to "which one preserves what the migration has already built" is: **neither is
required, and `SExpr.lean` is untouched.** The migration in flight — 101 error sites — keeps
every line. That is the strongest form the answer could have taken, and it is the reason I
would not now switch routes.

## 9.7 What I could *not* settle, and what would still refute route 1

The residual risk is entirely obstacle (i), and it is worth stating sharply because it is
where a refutation would now have to come from.

`trans'` (`SExpr.lean:662`) is the only rule of `SExpr.IsDefEq` with no `VExpr` counterpart,
and its admissibility rests on `SExpr`-side sort uniqueness. Tracing that:
`toIsDefEq'` ← `uniq_sort` (`Experimental/UniqueTyping.lean:186`) ← `HasTypeS.uniq` (`:92`),
and `HasTypeS.uniq` consumes `SExpr.forallE_inv` and `SExpr.sort_inv` from the shape model
plus `IsDefEq.subst` (`SExpr.lean:1270`), which is proved *through* `IsDefEq.strong`
(`:878`) — still a `sorry`, still carrying the `hu0` defect (`:764`, `:789`, `:867`).
**[verified]**

So: **if `SExpr.IsDefEq.strong` turns out to be irreparably false rather than repairable,
`trans'` loses its justification and both `sort_inv` and `forallE_inv` fall with it.** That
is a single point of failure for the whole shape route, and it is not new — it is the item I
flagged in the previous pass. It is also the thing I would attack next.

I also did not attempt the reflection induction itself. Its congruence cases are mechanical
(`IsDefEq'`'s constructors are `VEnv.IsDefEq`'s, one for one, modulo the level conditions
now handled), but "mechanical" on this development has meant a few hundred lines more than
once.

---

# 10. Revised recommendation

1. **Stay on the shape route.** Obstacle (iii) is gone at no cost to `SExpr.lean`, so the
   argument for switching to the Carneiro stratification — which rested on route 1 having an
   unpriced dominant unknown — no longer holds. The migration's 101 sites keep their value.
2. **Attack `SExpr.IsDefEq.strong` next, and interrogate it before proving it.** It is now
   the single point of failure for `sort_inv`, `forallE_inv`, `trans'`-elimination and
   `IsDefEq.subst` at once (§9.7). Its docstring already calls it false as stated for the
   `hu0` reason; the question worth answering first is whether the *repaired* statement is
   true.
3. **Then write the reflection.** In this order: `∃ U'`-threading (proved, §9.2), the
   congruence cases (unwritten), `trans'` via `toIsDefEq'` (needs 2), the descent (proved,
   §9.3). The pieces at the two ends are done; the middle is the work.
4. Items 2–6 of §8 stand unchanged: no confluence, no set model, no consumer restatement,
   consumer A needs only the domain half, keep `Params.pat_wf` parked.
5. ~~Consider promoting the §9 lemmas out of the scratchpad.~~ **Done** — see §11.

---

# 11. Landed

`Theory/Typing/Strong.lean`, +120 lines, immediately after `IsDefEq.eqUpToLevels`
(`:694`), under a section note `### Descending a derivation to a smaller universe-parameter
count` (`:701`) that states the repair-at-the-end argument, names the four supporting
lemmas, and records the `.imax (.param 7) .zero` witness together with the inference that
does *not* follow from it. Provenance points back to §9.

| Declaration | Cite | Note |
|---|---|---|
| `VLevel.WF.mono` | `:733` | monotone in the parameter count |
| `VLevel.exists_wf` | `:737` | every level is WF at *some* count |
| `VLevel.exists_wf_list` | `:745` | list version — the `∃ U'` an induction produces |
| `IsDefEq.mono_uvars` | `:757` | combine the `U'`s of an induction's branches |
| `EqUpToLevels.instL'` | `:779` | substituting WF levels lands `EqUpToLevels` at the substituted count |
| `OnCtx.instL_id` | `:794` | the context survives the substitution untouched |
| `IsDefEq.descend` | `:805` | the descent itself |

Two changes from the scratch version, both simplifications:

* **No new inductive.** The scratch proof used a bespoke `SameLevels` (skeleton + `≈`
  levels, no well-formedness). It is unnecessary: state the hypotheses as
  `EqUpToLevels U' e a`, at the *reflection's* count rather than the ambient one, and the
  existing datatype does the job. A caller with `mk e = mk a` and `a.LevelWF U ≤ U'` gets
  there via `VLevel.WF.mono`.
* `EqUpToLevels.instL'` is the reusable half of what `SameLevels.instL` was, and is named
  against the existing `EqUpToLevels.instL` (`:239`), which is a different statement — one
  term at two `≈`-equivalent level lists, rather than two terms at one list.

Checked: `lake build` of `Theory.Typing.Injectivity`, `Theory.Typing.ChurchRosser`,
`Theory.SetModel.SoundInduction`, `Verify.Typing.Lemmas`, `Verify.Primitive` — all clean,
the only `sorry` warning being the pre-existing `ChurchRosser.lean:1266`. Every new
declaration reports `depends on axioms: [propext, Quot.sound]`.

The reflection induction itself was **not** attempted; it is scoped as its own task — §12.

---

# 12. Scoping the reflection induction

Scoping only; nothing built. Tree at `b63575b` (`M Experimental/ShapeLogRel.lean`, the
migration). Estimates are ranges with a confidence tag; anything I would otherwise have
called "assembly" is broken out with its own line, per the two streams that were burned by
not doing that.

**Headline: the `trans'` partition is clean, and cleaner than expected — but not in the way
the question assumed.** `trans'` need not be eliminated before the induction at all. Doing
it *inside* the induction is strictly better and leaves nothing open. §12.2.

**Second headline, deflationary: delivering `forallE_inv` does not unblock `IsDefEq.uniq`.**
`uniq` consumes `forallE_inv_stratified` (`UniqueTyping.lean:43`), not `forallE_inv`. That
is item **C4**, it has the lowest confidence in the whole estimate, and it needs a
`HasTypeStratified` inversion lemma that does not exist. Scheduling that as "assembly"
is exactly the trap. §12.5.

## 12.1 The statement, and why it must quantify over `Γ` and `U`

```lean
theorem reflect (henv : Ordered env) :
    ∀ {Γ' e₁' e₂' A'}, SExpr.IsDefEq Γ' e₁' e₂' A' →
      ∀ (Γ : List VExpr) (U : Nat), Γ.map SExpr.mk = Γ' → OnCtx Γ (env.IsType U) →
        ∃ U' e₁ e₂ A, U ≤ U' ∧
          SExpr.mk e₁ = e₁' ∧ SExpr.mk e₂ = e₂' ∧ SExpr.mk A = A' ∧
          env.IsDefEq U' Γ e₁ e₂ A
```

Three design points, each forced:

* **Preimages are existential, not computed.** A global structural `rep : SExpr → VExpr`
  looks tidier but does not commute with `SExpr.instL` on the nose, so `const` and `extra`
  would need `≈`-slack in their *types* and hence a `defeqDF` each. With existentials those
  two cases land exactly, via `SExpr.mk_instL` (`Bridge.lean:109`) and the fact that a
  representative function is a genuine section of `SLevel.mk`. The slack moves to the cases
  that need alignment anyway.
* **`Γ` is universally quantified** (over `VExpr` contexts whose `mk`-image is `Γ'`), because
  the binder cases must instantiate it at `Aᵥ :: Γ` where `Aᵥ` is produced by a *sibling*
  premise's IH. In `beta` the binder's preimage comes from premise 2 and is needed for
  premise 1 — impossible if `Γ` is fixed.
* **`U` is universally quantified and `U ≤ U'` is in the conclusion**, so `hΓ` can be lifted
  to whatever count a sibling branch produced. Lifting is one line: `OnCtx.mono`
  (`Lemmas.lean:163`) composed with `IsDefEq.mono_uvars` (`Strong.lean:757`).

*Fallback if the `∃ U'` bookkeeping gets noisy in practice:* state `U'` universally with a
"every level occurring has a `U'`-well-formed representative" side condition instead. I do
not recommend starting there — the max-taking is three tokens per case — but it is the
escape hatch if `mono_uvars` applications start dominating.

## 12.2 The `trans'` partition

**Of the 14 constructors of `SExpr.IsDefEq` (`SExpr.lean:656–680`), exactly one is
`trans'`, and it is *not* blocked.**

The assumption behind the question was that `trans'` must be eliminated first, by
`IsDefEq.toIsDefEq'` (`Experimental/UniqueTyping.lean:260`), whose `huniq` hypothesis is
sort-uniqueness stated **with no `Ctx.WF`** — and that is genuinely open, because
`uniq_sort` (`:186`) requires `Ctx.WF Γ` and the docstring at `:252–259` explains that the
`toIsDefEq'` induction cannot maintain it (neither `IsDefEq.beta` nor `IsDefEqStrong.beta`
types its binder).

**Do the elimination inside the reflection instead.** The reflection's motive already
carries `OnCtx Γ (env.IsType U)` on the `VExpr` side, and §9.4 established that the `VExpr`
side *can* maintain context well-formedness through `beta`, because `IsDefEq.isType`
(`Lemmas.lean:872`) exists and `SExpr` has no analogue. `OnCtx.toSExpr` (`Bridge.lean:203`)
turns that invariant into the `Ctx.WF Γ'` that `uniq_sort` wants. So the `trans'` case reads:

1. `uniq_sort h1 h2 (hΓ.toSExpr) : u = v` — applied to `trans'`'s own two SExpr premises,
   at the same context, with `Ctx.WF` supplied by the invariant we are already carrying;
2. `SLevel.mk_inj` (`Bridge.lean:64`) turns `mk uᵥ = mk vᵥ` into `uᵥ ≈ vᵥ`;
3. `sortDF` + `defeqDF` retypes the second IH from `.sort vᵥ` to `.sort uᵥ`;
4. proceed exactly as the `trans` case.

`uniq_sort` is a *proved theorem* (sorry-tainted through `IsDefEq.strong`, like everything
else here), not an open hypothesis. So:

| | Cases | Status |
|---|---|---|
| Independent of `trans'`-elimination | 13 — `bvar symm trans sort const appDF lamDF forallEDF defeqDF beta eta proofIrrel extra` | buildable now |
| Depends on it | 1 — `trans'` | **also buildable now**, via `uniq_sort` with `Ctx.WF` in hand |

**Nothing is left open, and nothing is serialised behind the migration.** The whole chain
compiles today and becomes sorry-free the moment `SExpr.IsDefEq.strong` lands. That is a
better answer than "mostly unblocked with a blocked tail": there is no tail.

*The instruction that follows from this:* **reflect `SExpr.IsDefEq`, not `IsDefEq'`.** If
someone reflects `IsDefEq'` instead, they inherit `huniq` as an open hypothesis for no gain;
and if they reflect `IsDefEq` but try to justify `trans'` on the `VExpr` side, that *is*
circular — it needs `VExpr`-side `uniq`. The partition is clean only for one of the three
designs, so it should be written down as a decision, not rediscovered.

This is the third time in this task that an obstacle was a choice of vantage rather than a
fact about the objects — after "reflect at `U'`, not at `U`" (§9) and "state the hypothesis
at the reflection's count, not the ambient one" (§11). The prompt is worth keeping: **when a
case looks like it needs new machinery, check first whether it needs a different `U` or a
different place to stand.**

## 12.3 The induction, itemised

Reference points for calibration, all in-tree: `VEnv.IsDefEq.toSExpr` (`Bridge.lean:176–201`)
is the *forward* direction — 26 lines for 13 cases, trivial because `mk` is a homomorphism
and `SExpr` has no side conditions to discharge. The reverse is asymmetric precisely because
side conditions must be *produced* and preimages *aligned*. The closest same-shape analogues
are `IsDefEqStrong.instL` (`Strong.lean:300–339`, ~40 lines, no alignment) and
`EqUpToLevels.defeq` (`Strong.lean:533–610`, ~78 lines, with alignment).

| # | Group | Cases | Est. lines | Confidence |
|---|---|---|---|---|
| B1 | free | `bvar`, `symm` | 15 | high |
| B2 | level side conditions only | `sort`, `const`, `extra` | 30 | high — spiked, §9.2 |
| B3 | congruence + alignment | `appDF`, `defeqDF`, `proofIrrel` | 90–120 | medium |
| B4 | binder cases (context extension + alignment) | `lamDF`, `forallEDF`, `beta` | 100–140 | medium |
| B5 | η | `eta` | 20–30 | medium |
| B6 | `trans` (align middle term *and* type) | `trans` | 40–50 | medium |
| B7 | `trans'` (B6 + `uniq_sort` + `mk_inj`) | `trans'` | 30–40 | medium |
| | **Induction total** | **14** | **325–425** | |

Notes on the harder groups:

* **B3/B4/B6 all do the same thing** — two sibling IHs produce two preimages of the same
  `SExpr` term, and they must be made one. That is item A6 below; build it first and these
  become short. If A6 is not factored out, expect these three groups to double.
* **B4's ordering subtlety.** In `beta`, premise 1 lives at `A::Γ` but the binder's preimage
  `Aᵥ` comes from premise 2. The universally-quantified `Γ` in the motive is what makes this
  legal; `OnCtx (Aᵥ::Γ)` then comes from `IsDefEq.isType` on premise 2's IH (§9.4).
* **B5** needs `SExpr.mk_lift` (`Bridge.lean:106`); `VExpr.inst_liftN_bvar0`
  (`Bridge.lean:32`) exists for the forward direction and may or may not be needed here.

## 12.4 Infrastructure, itemised (before any case)

| # | Item | Est. lines | Confidence |
|---|---|---|---|
| A1 | `repL : SLevel → VLevel`, a section of `SLevel.mk` (`SExpr.lean:63` carries the witness; `Exists.choose`) | 8 | high |
| A2 | `mk`-skeleton inversion, six constructors + list case; equivalently `mk` surjectivity | 50 | **medium-low** |
| A3 | `mk e = mk e' → e.LevelWF U → e'.LevelWF U → EqUpToLevels U e e'` | 30 | high — proved in the spike as `SameLevels.toEqUpToLevels` |
| A4 | `Lookup (Γ.map mk) i A' → ∃ A, Lookup Γ i A ∧ mk A = A'` (inverse of `Bridge.lean:163`) | 12 | high |
| A5 | `OnCtx` lifted in `U` — `OnCtx.mono` ∘ `IsDefEq.mono_uvars` | 4 | high |
| A6 | **the alignment combinator**: `mk x = mk y → IsType Γ x → IsDefEq Γ x y (.sort w)`, from A3 + `IsDefEq.eqUpToLevels` | 15 | high |
| | **Infrastructure total** | **~120** | |

A2 is the one to watch: six constructors, and the `const` case needs surjectivity at the
list level. It is the sort of item that has come in at twice its estimate here before.

**A3 is the piece of the spike that did *not* land**, and deliberately: it mentions `mk`, so
it belongs in `Experimental/Bridge.lean` (or a new `Experimental/Reflect.lean`), not in the
mainline. A6 is its only consumer and pays for itself across six cases.

## 12.5 Assembly, itemised — including the trap

| # | Item | Est. lines | Confidence |
|---|---|---|---|
| C1 | `SExpr.forallE_inv` (`ShapeLogRelAdequacy.lean:462`) → the two component defeqs, retyped at a sort — the `HasTypeS.uniq` move already written twice at `BridgeInjectivity.lean:56–66` | 20 | high |
| C2 | reflect each component, then `IsDefEq.descend` each to `U` | 30 | high |
| C3 | state `IsDefEqU.forallE_inv` in `Injectivity.lean`'s shape, relative to `[Params] [ParamsExtra]` | 15 | high |
| C4 | **`forallE_inv_stratified` from `forallE_inv` + `sort_inv`** | **80–150** | **low** |
| C5 | rewire `Injectivity.lean`: today `forallE_inv` (`:23–31`) is *derived from* `forallE_inv_stratified`; the arrow reverses | 10 | high |
| | **Assembly total** | **155–225** | |

**C4 is the trap and it should be scheduled as its own task, not as a tail.** Three facts:

1. `IsDefEq.uniq` (`UniqueTyping.lean:13`) consumes `forallE_inv_stratified` at `:43`, not
   `forallE_inv`. So C1–C3 unblock only the three direct consumers
   (`Verify/Typing/Lemmas.lean:2095`, `Verify/TypeChecker/InferType.lean:276, 286`) — **not**
   the ~80 `uniq` sites across eight `Verify/` files.
2. The stratified conclusion carries `HasTypeStratified` derivations at specific indices
   (`Injectivity.lean:18–21`). Recovering them from `h2`/`h3` needs a **`forallE` inversion
   lemma for `HasTypeStratified` that does not exist**: `Strong.lean` has `hasType` (`:980`),
   `mono` (`:992`), `to_core` (`:1030`) and `isType` (`:1037`), and nothing that inverts a
   `.forallE` subject.
3. The level mismatch — the stratified derivation sits at some `u₀`, the defeq at the `u`
   `forallE_inv` produced — is bridged by `HasTypeStratified.defeq` (`:947`ff) *given*
   `u₀ ≈ u`, i.e. **given `sort_inv`**. So C4 additionally consumes the other injectivity
   statement. Fine, since `sort_inv` is the shape route's other deliverable — but it means
   C4 cannot start before `sort_inv` lands, whereas B and C1–C3 can.

My analysis says C4 goes through. It is **[inferred]**, not machine-checked, and it is the
item I would expect to be wrong about.

## 12.6 What the landed lemmas are actually used for

Asked directly, and the answer is partly deflationary. Of the seven declarations in
`Strong.lean:733–819`:

| Landed lemma | Used by |
|---|---|
| `VLevel.exists_wf` (`:737`) | case `sort` |
| `VLevel.exists_wf_list` (`:745`) | cases `const`, `extra` |
| `IsDefEq.mono_uvars` (`:757`) | every case with ≥2 premises — 8 of 14 — and A5 |
| `VLevel.WF.mono` (`:733`) | A5, and wherever a `WF` is lifted |
| `IsDefEq.descend` (`:805`) | **once, in C2** — not in any case |
| `EqUpToLevels.instL'` (`:779`) | internal to `descend` |
| `OnCtx.instL_id` (`:794`) | internal to `descend` |

So: **four of the seven are induction machinery, three are the exit ramp.** What the
induction actually leans on most heavily is the *alignment* machinery — A3 and A6 — and that
did not land, because it mentions `mk` and therefore cannot live in the mainline. The right
reading is that what landed is correctly shaped for the two ends (`∃ U'` threading in, the
descent out) and says nothing either way about the middle. That was the honest expectation
going in and it survived contact.

## 12.7 Total, and how I would schedule it

| | Lines | |
|---|---|---|
| A — infrastructure | ~120 | A2 is the risk |
| B — the induction, 14 cases | 325–425 | build A6 first |
| C1–C3, C5 — assembly to `forallE_inv` | ~75 | |
| C4 — `forallE_inv_stratified` | 80–150 | **own task; low confidence; needs `sort_inv`** |
| **Total** | **~600–770** | |

Compare: my last pass priced the Carneiro stratification at 2000–3000 lines of churn on
*finished* proof. This is 600–770 lines of new proof with no churn. The comparison still
favours the shape route, and by more than it did.

Schedule:

1. **A1–A6 and B1–B2 now** — no dependencies, and B2 is already spiked.
2. **A6, then B3/B4/B6/B7** — all four collapse onto the alignment combinator.
3. **C1–C3, C5** — gives `forallE_inv` and unblocks the three direct consumers.
4. **C4 separately, after `sort_inv`** — and re-scope it once the `HasTypeStratified`
   inversion lemma has been attempted, because that is where the estimate will move.

Nothing in 1–3 waits on the `indTy` migration. All of it inherits the `SExpr.IsDefEq.strong`
taint and clears when the migration does.

## 12.8 On LSP staleness — asked for, and yes, warn the other streams

I saw two distinct behaviours this session and only one of them is safe:

* **Source changed, not rebuilt** → `lean_run_code` returns an **error**, *"Imports are out
  of date and must be rebuilt"*, and refuses. Safe: it declines rather than guessing. This
  is what blocked me from importing `Experimental/Bridge.lean` during the spike.
* **Module rebuilt after the worker started** → `lean_run_code` returns an **info**,
  *"Imports are out of date and should be rebuilt"*, and then **answers from the stale
  environment**. I asked for `#print axioms` on seven freshly-built declarations and got
  seven `Unknown constant` errors, with the `.olean` on disk 19 seconds *newer* than the
  source and containing all seven. A negative result from that state is worthless and does
  not look it.

Practical rules worth passing on:

* `lean_diagnostic_messages` **on the file you are editing** is reliable — it elaborates
  live against built imports, and it correctly reported my `Strong.lean` edit as clean.
* After a `lake build`, verify new declarations with `lake env lean` on a temp file, **not**
  `lean_run_code`.
* Treat the *info*-severity "should be rebuilt" as invalidating any negative result in that
  response. The error-severity "must be rebuilt" is fine — it refuses.

Two environment notes while I am here: `lake` is not on `PATH` for the Bash tool
(`~/.elan/bin/lake`), and `ripgrep` is absent, so `lean_local_search` fails outright with an
installation message — use `grep -rn --include=*.lean` instead.

---

# 13. A6 landed, and the collapse measured

`Lean4Lean/Reflect/Align.lean`, 147 lines, no errors, no warnings, no `sorry`. Axiom cones
are `[propext, Quot.sound]` throughout, except `SLevel.mk_rep`, which adds
`Classical.choice` (it is `Exists.choose`); all three are on `Verify/Guard.lean`'s
whitelist. Verified with `lake env lean`, not `lean_run_code` — see §12.8, which bit twice
during this session.

## 13.1 What is in it

The A-group, minus A4:

| Item | Contents |
|---|---|
| A2 | `SExpr.mk_eq_{bvar,sort,const,app,lam,forallE}` — six skeleton inversions |
| A1 | `SLevel.rep` and `SLevel.mk_rep` — a section of `SLevel.mk` |
| A5 | `OnCtx.mono_uvars` |
| A3 | `EqUpToLevels.of_mk` — `mk x = mk y` plus level-well-formedness is `EqUpToLevels` |
| A6 | `IsDefEq.align{T,R,L}` — retype / retarget-right / retarget-left |

A4 (`Lookup` inversion through `mk`, ~12 lines) is not written; it is needed only by the
`bvar` case.

`[Params]` turns out to be needed only for `SLevel.mk_inj`'s sake, so the file is split:
the six skeleton inversions, `SLevel.rep` and `OnCtx.mono_uvars` are `Params`-free, and only
the alignment half carries the instance.

## 13.2 The collapse: measured, and larger than estimated

Three cases probed in scratch against the landed file, one from each group that was supposed
to depend on A6. **Proof bodies, excluding the `example` signature:**

| Group | Case | Estimated (§12.3) | Measured | |
|---|---|---|---|---|
| B6 | `trans` | 40–50 | **10** | one `alignL` + one `alignT` |
| B3 | `appDF` | 90–120 *(for three cases)* | **12** | one `alignT` |
| B4 | `lamDF` | 100–140 *(for three cases)* | **9** | **no alignment at all** |

The collapse happened. Revised B:

| Group | Cases | Was | Now |
|---|---|---|---|
| B1 | `bvar`, `symm` | 15 | ~12 |
| B2 | `sort`, `const`, `extra` | 30 | ~30 |
| B3 | `appDF`, `defeqDF`, `proofIrrel` | 90–120 | ~40 |
| B4 | `lamDF`, `forallEDF`, `beta` | 100–140 | ~40 |
| B5 | `eta` | 20–30 | ~15 |
| B6 | `trans` | 40–50 | 10 |
| B7 | `trans'` | 30–40 | ~20 |
| | **case bodies** | **325–425** | **~170** |
| | motive plumbing + `induction` scaffolding | not costed | **60–100** |
| | **B total** | **325–425** | **230–270** |

I am costing the scaffolding separately rather than folding it in, because it is the part I
have *not* measured: the probes hand the induction hypotheses over in exactly the shape the
case wants, and Lean's `induction ... with` will not. That is the same "assembly" error the
itemisation exists to prevent, so it gets its own line.

Revised total: **A ~160 + B 230–270 + C1–C3/C5 ~75 = 465–505 lines**, against 600–770 before
C4 is excluded. C4 remains out of scope and unestimated here.

## 13.3 A structural finding: the binder cases need no alignment

`lamDF` came in at 9 lines and used none of A6. The reason generalises, and it changes which
cases are "hard":

**Alignment is needed exactly where two *sibling* premises independently produce a preimage
of the same object.** In the binder cases they do not — the context preimage is *chosen* by
the first premise's induction hypothesis and *threaded into* the second:

```lean
  obtain ⟨U₁, Av, A'v, S, le₁, hA, hA', hS, d1⟩ := ih1 U (Nat.le_refl _) hΓ
  obtain ⟨uv, rfl, huv⟩ := SExpr.mk_eq_sort hS
  obtain ⟨U₂, bv, b'v, Bv, le₂, hb, hb', hB, d2⟩ :=
    ih2 (Av::Γ) U₁ (by simp [hA, hΓm]) ⟨hΓ.mono_uvars le₁, _, d1.hasType.1⟩
```

The universally-quantified `Γ` in the motive (§12.1) is what makes this legal, and it is
what makes the binder cases cheap rather than expensive. So the split is:

* **needs alignment (6):** `trans`, `trans'`, `appDF`, `defeqDF`, `proofIrrel`, and `beta`
  (for the binder type shared between its two premises);
* **needs none (8):** `bvar`, `symm`, `sort`, `const`, `extra`, `lamDF`, `forallEDF`, `eta`.

§12.3 implied ten cases leaning on A6. It is six.

## 13.4 Coupling: the answer to the question asked

**No, the reflection body does not need `ShapeLogRel.lean` — with one exception, and the
exception is separable.**

* `Reflect/Align.lean` imports `Experimental.Bridge` (which is `SExpr.lean` plus the `mk`
  homomorphism lemmas) and `Theory.Typing.Strong`. **No `ShapeLogRel`.** Confirmed by its
  building.
* 13 of the 14 cases need only `SExpr.IsDefEq`, i.e. `SExpr.lean`. **No `ShapeLogRel`.**
* The `trans'` case needs `SExpr.IsDefEq.uniq_sort`, which lives in
  `Experimental/UniqueTyping.lean` → `ShapeLogRelAdequacy.lean` → `ShapeLogRel.lean`. **That
  one case couples.**

**The separation is cheap and I would take it.** State the reflection with `trans'`'s
sort-uniqueness as an explicit hypothesis in exactly `uniq_sort`'s shape — crucially *with*
`Ctx.WF Γ`, which is what distinguishes it from `toIsDefEq'`'s open `huniq`:

```lean
(huniq : ∀ {Γ : List SExpr} {e₁ e₂ e₃ : SExpr} {u v : SLevel},
   Γ ⊢ e₁ ≡ e₂ : .sort u → Γ ⊢ e₂ ≡ e₃ : .sort v → Ctx.WF Γ → u = v)
```

That is dischargeable **today** by `uniq_sort` (`Experimental/UniqueTyping.lean:186`). So the
~250-line body imports only `Bridge`, and a ~10-line capstone importing `UniqueTyping`
discharges the hypothesis. The bulk is then immune to the migration.

Two further coupling facts the coordinator should have:

* **`Reflect/Align.lean` is in no default build target.** `defaultTargets` are `Lean4Lean`,
  `lean4lean`, `Lean4Lean.Theory`, `Lean4Lean.Verify`; the lib globs are
  `Lean4Lean.{Theory,Verify,Tests}.*` and `Lean4Lean.Experimental.+`, none of which covers
  `Lean4Lean.Reflect.*`. `lake build Lean4Lean.Reflect.Align` works on demand, but a bare
  `lake build` will not touch it and it will rot silently. Fixing that is a `lakefile.toml`
  change, which is a controlled file — **your call, not mine.**
* **Rebuild churn is real.** `SExpr.lean` imports `Theory/Inductive/Lemmas.lean`, which the
  keystone stream is editing; I hit a hard "imports out of date" mid-session and had to
  rebuild `Experimental.Bridge` to continue. Expect that repeatedly. It is not a blocker —
  the rebuild took seconds — but it means this stream cannot be fully insulated from the
  other two no matter where the file lives.

## 13.5 Next

A4, then B in the order B2 → B1 → B4/B5 → B3 → B6 → B7, then C1–C3/C5. The motive plumbing
(§13.2's separately-costed line) is the first thing to write, since every case depends on its
exact shape; I would write it and prove `bvar` and `symm` against it before doing any other
case, precisely to find out whether 60–100 is right.

---

# 14. A4 and the motive plumbing: 60–100 did not hold, it was 15

Two files, both building, under `Lean4Lean/Experimental/Reflect/` (moved there from
`Lean4Lean/Reflect/`, which no lib glob covered and which could not be given one — Lake
refuses a lib whose modules import another lib's).

| File | Lines | State |
|---|---|---|
| `Align.lean` | 177 | complete, no `sorry` |
| `Induction.lean` | 126 | 5 of 14 cases proved, 9 `sorry` |

## 14.1 A4

`Lookup.of_map_mk` — `SExpr.Lookup (Γ.map mk) i A' → ∃ A, Lookup Γ i A ∧ mk A = A'`, the
inverse of `Bridge.lean`'s `Lookup.toSExpr`. **11 lines**, estimated 12. The A-group is now
complete.

## 14.2 The measurement asked for

Scaffolding, counted as the parts that exist *only* to support the induction — the
`Reflects` definition, the `SortUniq` hypothesis, and the theorem signature with its `intro`
and `induction`:

| Piece | Lines |
|---|---|
| `Reflects` | 4 |
| `SortUniq` | 5 |
| signature + `intro` + `induction ... with` | 6 |
| **total** | **15** |

**Estimated 60–100. Actual 15.** The estimate was wrong in the safe direction, and the
reason is worth recording because it is checkable: I had budgeted for `induction ... with`
producing induction hypotheses in a shape the cases would have to massage. It does not.
Stating the theorem as

```lean
∀ {Γ'} {e₁' e₂' A'}, SExpr.IsDefEq Γ' e₁' e₂' A' →
  ∀ (Γ : List VExpr) (U : Nat), Γ.map SExpr.mk = Γ' →
    OnCtx Γ (Params.env.IsType U) → Reflects Params.env Γ U e₁' e₂' A'
```

and then `intro …; induction H with` leaves the trailing `∀ Γ U, …` in the goal, so each
`ih` arrives as `∀ Γ U, Γ.map mk = Γ' → OnCtx Γ … → Reflects …` — exactly the shape §13.2's
probes assumed. **The transfer cost from probe to real induction was one line per case**
(the `intro Γ U hΓm hΓ`).

## 14.3 Five cases proved against the real motive

Rather than stop at `bvar`/`symm`, I ported the three §13.2 probes in, because "the motive
elaborates" and "the motive supports the measured cases" are different claims and only the
second is worth anything.

| Case | Group | Probe | In file |
|---|---|---|---|
| `bvar` | B1 | — | 6 |
| `symm` | B1 | — | 4 |
| `trans` | B6 | 10 | 11 |
| `appDF` | B3 | 12 | 13 |
| `lamDF` | B4 | 9 | 9 |
| | | | **43** |

So the motive is not merely well-formed; the two cases that need alignment and the one that
needs context threading all go through it unchanged.

## 14.4 Revised estimate

| | Lines |
|---|---|
| A — `Align.lean`, complete | 177 |
| B — 5 cases done | 43 |
| B — 9 cases remaining *(B2 ~30, `forallEDF` ~9, `beta` ~20, `eta` ~15, `defeqDF` ~12, `proofIrrel` ~15, `trans'` ~20)* | ~121 |
| B — scaffolding, measured | 15 |
| C1–C3, C5 + capstone | ~85 |
| **Total** | **~440** |

Against 600–770 at §12 and 465–505 at §13. The remaining uncertainty is concentrated in
three cases and I would not defend the numbers on the others:

* **`beta`** — the only case with *both* sibling-preimage alignment and context extension.
* **`eta`** — `lift` / `.bvar 0` bookkeeping through `mk`; `SExpr.mk_lift` exists, but the
  shape `.lam A (.app e.lift (.bvar 0))` has to be matched on both sides.
* **`const` / `extra`** — the level side conditions are spiked (§9.2), but at the `VExpr`
  level; composing `SLevel.rep` with `SExpr.mk_instL` so the type lands on the nose has not
  been done.

## 14.5 The capstone seam, as approved

`Induction.lean` takes `SortUniq` — `SExpr.IsDefEq.uniq_sort`'s exact statement, **with**
`Ctx.WF Γ` — as a hypothesis, and imports only `Align.lean`. So neither file imports
`Experimental/UniqueTyping.lean`, and neither depends on `ShapeLogRelAdequacy.lean` or
`ShapeLogRel.lean`. Confirmed by their building while `ShapeLogRel.lean` is dirty in the
working tree.

Only the `trans'` case will use `huniq`, and the capstone that discharges it is the only
file that will import the shape model.

---

# 15. B is complete: all 14 cases, no `sorry`

`Lean4Lean.reflect` builds with **zero `sorry`** and axiom cone
`[propext, Classical.choice, Quot.sound]` — `Classical.choice` entering through
`SLevel.rep`, which is `Exists.choose`. All three within `Verify/Guard.lean`'s whitelist.

| File | Lines | State |
|---|---|---|
| `Experimental/Reflect/Align.lean` | 200 | complete |
| `Experimental/Reflect/Induction.lean` | 204 | complete |

## 15.1 B2 first, as scoped — and the risky composition works

`const`/`extra`/`sort` were taken first because their §9.2 spike was at the `VExpr` level
and composing `SLevel.rep` with `SExpr.mk_instL` so the type lands on the nose was untried.

**It works, and `by simp` closes it outright.** With `SLevel.rep` a section of `SLevel.mk`
(`SLevel.mk_rep`), `SExpr.mk_instL` gives

```
mk (ci.type.instL (ls.map SLevel.rep)) = (mk ci.type).instL ((ls.map rep).map mk)
                                       = (mk ci.type).instL ls
```

exactly — no `≈`-slack, so no `align` call in any of the three. `sort` 5 lines, `const` 6,
`extra` 6: **17 against an estimate of 30.**

**One snag worth recording, because it is a repeat of a documented one.** The obvious lemma
`(ls.map rep).map mk = ls` never fires: `List.map_map` is itself `simp` and rewrites the goal
to `ls.map (mk ∘ rep) = ls` first, at which point nothing matches. Fixed by also stating the
simp-normal form, `SLevel.mk_comp_rep : mk ∘ rep = id`. This is exactly the
"`@[simp]` lemma that has already fired changes what `rw` can see" note at
`Theory/Inductive/Lemmas.lean:47–51` — same phenomenon, different file, and it cost one
round here too.

## 15.2 The other two named risks, also retired

§14.4 named `beta`, `eta` and `const`/`extra` as the three places I would not defend the
numbers. Having retired the third, I took the other two rather than the cheap cases, on the
same reasoning as §14.3: the brief's stopping point retired B2's risk but left two named
risks open, and finding them wrong after three routine cases is worse than finding them now.

Both went through **first try**, and both for a reason that corrects §13.3:

* **`beta` needs no alignment** (10 lines). The binder type `Av` is produced by premise 2's
  induction hypothesis and *threaded into* premise 1's context, exactly as in `lamDF`. I had
  listed it as needing alignment "for the binder type shared between its two premises";
  that sharing is what makes it *not* need alignment, because the same `Av` is used twice
  rather than produced twice.
* **`eta` needs no alignment** (6 lines). Its single premise `Γ ⊢ e : .forallE A B` is a
  `HasType`, so `d.hasType.1` is about one endpoint only and the second preimage `ev'` is
  simply discarded.

**Corrected split — alignment is needed in 4 cases, not 6:** `trans`, `trans'`, `appDF`,
`defeqDF`, `proofIrrel` use `align*`; the other nine do not. (`proofIrrel` uses it twice.)

## 15.3 Final measurements

| Case | Group | Est. | Actual |
|---|---|---|---|
| `bvar` | B1 | — | 5 |
| `symm` | B1 | — | 4 |
| `sort` | B2 | ~10 | 5 |
| `const` | B2 | ~10 | 6 |
| `extra` | B2 | ~10 | 6 |
| `eta` | B5 | ~15 | 6 |
| `lamDF` | B4 | — | 9 |
| `forallEDF` | B4 | ~9 | 10 |
| `beta` | B4 | ~20 | 10 |
| `trans` | B6 | — | 11 |
| `defeqDF` | B3 | ~12 | 11 |
| `appDF` | B3 | — | 13 |
| `trans'` | B7 | ~20 | 13 |
| `proofIrrel` | B3 | ~15 | 20 |
| **`reflect`, signature to end** | | **179** | **136** |

`proofIrrel` is the only case that overran, and only because it is the sole three-premise
rule: three universe counts to reconcile rather than two, and a retype of the proposition's
sort from the chosen representative `zv` to a literal `VLevel.zero` (via `mk_zero` and
`mk_inj`, since `SLevel.mk zv = SLevel.zero` gives only `zv ≈ .zero`, not equality).

Running totals against the three estimates: **§12 600–770 → §13 465–505 → §14 ~440 →
actual 404 for A+B, with C remaining.**

## 15.4 What remains

Only C. The capstone (`SortUniq` discharged by `SExpr.IsDefEq.uniq_sort`, ~10 lines) and
C1–C3/C5 (`SExpr.forallE_inv` → retype at a sort → reflect twice → `IsDefEq.descend` →
`IsDefEqU.forallE_inv`, ~75 lines). C4 remains out of scope.

The seam held: neither `Align.lean` nor `Induction.lean` imports
`Experimental/UniqueTyping.lean`, so neither depends on `ShapeLogRelAdequacy.lean` or
`ShapeLogRel.lean`, and both built clean throughout while `ShapeLogRel.lean` was dirty.
