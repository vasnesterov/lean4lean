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

## Bottom line

**The narrowed reflection really is the shortest route, and it is not as narrow as hoped.**

Ranked, risk-adjusted:

| # | Route | Verdict |
|---|---|---|
| 1 | **Reflection `SExpr → VExpr`, narrowed at the conclusion** | The only route whose destination is reachable. Three obstacles, not two — the third (level well-formedness) is new and I give a witness. One of the three is already half-proved, and the *fixup* the narrowing was supposed to buy is **already proved** (`IsDefEq.eqUpToLevels`, `Strong.lean:694`). |
| 2 | **Full Carneiro conversion-alternation stratification** | Its value has gone *up* since my last report, because it delivers all three injectivity statements and the shape route delivers only two. ~2300 lines of churn, known-true destination. The honest fallback, and possibly the honest primary — see §7. |
| 3 | Add level-WF side conditions to `SExpr.IsDefEq` | Not a route on its own; the cheapest known fix for obstacle (iii) of route 1. Undoes a deliberate simplification (`Bridge.lean:18–20`). |
| 4 | Re-base the logical relation on `VExpr` | Removes the reflection problem at the root. Prohibitive (8479 lines written against `SExpr`), but *less* prohibitive than it looks, because `eqUpToLevels` supplies the level congruences `SLevel` exists to avoid. Name it, don't take it. |
| 5 | Weaken/restate the three consumers | **Impossible.** All three genuinely need Pi-injectivity; §6 gives the failure point in each. |
| 6 | Read it off the set model | **Impossible.** `forallE_inv`'s conclusion is a derivation, and the interpretation is not injective. Witness in §5. |
| 7 | Confluence, given `sort_inv` for free | **Still circular**, and for a *different* reason than `sort_inv` was. §4. This is the most decision-relevant finding. |

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

### Summary of route 1

| Piece | Status |
|---|---|
| `mk` surjective; representative choice | **free** (`SExpr.lean:63`) |
| fixup `rep(mk A) → A` | **proved** (`Strong.lean:694`) |
| `trans'`-elimination | **half-proved**, blocked on `SExpr.IsDefEq.strong` — *shared with `sort_inv`* |
| `const`/`CtorBundle` | **not an obstacle** on the plain judgment |
| level well-formedness | **new, unpriced, dominant** |
| congruence/`extra` cases of the induction | mechanical, unwritten |

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

---

## 8. Recommendation

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
* There is a **third** obstacle, level well-formedness, and it is the one I would plan
  around.
