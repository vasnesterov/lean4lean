# Research: the three `sorry`s in `Lean4Lean/Theory/Typing/Injectivity.lean`

Read-only investigation. No repo file was modified.

---

## 0. Executive summary

1. **The circularity is real and is exactly Carneiro's.** `Injectivity` → `UniqueTyping`
   → `ChurchRosser` → `HeadReduction`. Church–Rosser in this repo is developed at the
   *unstratified* level and calls unique typing / Π-injectivity **~40 times**
   (`IsDefEqU.forallE_inv` ×11, `IsDefEqU.sort_inv` ×1, `IsDefEq.uniq`/`uniqU` ×23 in
   `ChurchRosser.lean`; ×4/×2/×2/×11 in `HeadReduction.lean`). So the "prove injectivity
   from Church–Rosser" move is genuinely blocked.

2. **`HasTypeStratified` is *not* Carneiro's `⊢_n`, and it does not break this
   circularity.** It stratifies the *typing* judgment by derivation height while its
   conversion premise stays a full, unstratified `IsDefEq`. It exists to make
   `IsDefEq.uniq`'s own induction well-founded (because `forallE_inv_stratified` hands
   back derivations that are not sub-derivations), not to layer conversion. Carneiro's
   index counts alternations on the **conversion** judgment; the repo has no counterpart
   of `⊢_0 α ≡ β ⟺ α = β`, hence no `thm:0dinv` and no `thm:1dinv`.

3. **A prior attempt exists and got very far, but in a parallel universe.** Commit
   `84f2b04 "Finished injectivity! 🎉"` (Mario Carneiro, 2026-05-13) proves
   `SExpr.sort_inv`, `SExpr.forallE_inv`, `SExpr.sort_forallE_inv` and full unique typing
   — for `SExpr`, a *copy* of `VExpr` with semantically-quotiented levels, via a
   6100-line shape logical relation. **There is no bridge from `SExpr` back to `VExpr`**,
   and the chain still depends on `sorryAx` (39 sorries + 1 axiom in the substrate).

4. **Recommendation (§6):** finish the SExpr shape-logical-relation track and add the
   two translation lemmas, in the order given there. Do *not* attempt a faithful
   Carneiro re-stratification of `ChurchRosser.lean` — it means re-indexing ~2300 lines
   of finished proof. Two of the three targets (`sort_inv`, `sort_forallE_inv`) need
   only the **easy** direction of the bridge, so they can land first.

---

## 1. The three statements and their consumers

`Lean4Lean/Theory/Typing/Injectivity.lean` (34 lines, docstring *"A bunch of important
structural theorems which we can't prove :("*):

```lean
theorem IsDefEqU.sort_inv (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (h1 : env.IsDefEqU U Γ (.sort u) (.sort v)) : u ≈ v := sorry            -- line 11

theorem IsDefEqU.forallE_inv_stratified (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (h1 : env.IsDefEqU U Γ (.forallE A B) (.forallE A' B'))
    (h2 : env.HasTypeStratified U Γ (.forallE A B) V true n)
    (h3 : env.HasTypeStratified U Γ (.forallE A' B') V' true n') :
    (∃ u, env.IsDefEq U Γ A A' (.sort u) ∧ env.HasTypeStratified U Γ A (.sort u) true n) ∧
    ∃ u, env.IsDefEq U (A::Γ) B B' (.sort u) ∧
      env.HasTypeStratified U (A::Γ) B (.sort u) true n ∧
      env.HasTypeStratified U (A'::Γ) B' (.sort u) true n' := sorry          -- line 14

theorem IsDefEqU.forallE_inv (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (h1 : env.IsDefEqU U Γ (.forallE A B) (.forallE A' B')) :
    (∃ u, env.IsDefEq U Γ A A' (.sort u)) ∧ ∃ u, env.IsDefEq U (A::Γ) B B' (.sort u) :=
  … -- PROVED, one-liner from forallE_inv_stratified via HasTypeStrong.stratify

theorem IsDefEqU.sort_forallE_inv (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U)) :
    ¬env.IsDefEqU U Γ (.sort u) (.forallE A B) := sorry                      -- line 33
```

Note the sorted `A` in `forallE_inv_stratified`'s conclusion carries *the same numeric
index* `n`/`n'` as the hypotheses. That is deliberate: it is what makes the well-founded
recursion in `IsDefEq.uniq` decrease. See §2.2.

**Consumers.** `Injectivity.lean` is imported only by `UniqueTyping.lean`, but its
downstream reach is the whole metatheory:

| Consumer | Uses |
|---|---|
| `Theory/Typing/UniqueTyping.lean` | `forallE_inv_stratified` ×1 (line 43), `sort_inv` ×7 (lines 50, 54, 65, 69, 71, 80, 83, 98, 108) — inside `IsDefEq.uniq` |
| `Theory/Typing/ChurchRosser.lean` | `IsDefEqU.forallE_inv` ×11, `IsDefEqU.sort_inv` ×1, `IsDefEq.uniq`/`uniqU` ×23 |
| `Theory/Typing/HeadReduction.lean` | `forallE_inv` ×4, `sort_inv` ×2, `sort_forallE_inv` ×2, `uniq`/`uniqU` ×11 |
| `Verify/Typing/Lemmas.lean` | `forallE_inv` (1743, 2033), `uniqU` (2032) |
| `Verify/TypeChecker/InferType.lean` | `forallE_inv` (255, 265), `uniqU` (251) |
| `Verify/TypeChecker/Basic.lean` | `uniqU` (876) |

Everything in `Lean4Lean.Theory` beyond `Strong.lean` and everything in `Verify` that
reasons about `isDefEq`/`inferType` is `sorryAx`-tainted through these three.

Beware of name collisions when grepping: `Theory/Typing/Lemmas.lean` also defines
`HasType.forallE_inv`, `IsType.forallE_inv`, `HasType.sort_inv`, `IsDefEq.sort_inv_l/_r`
(lines 786–836). Those are **different, already-proved** lemmas — "the subterms of a
well-typed Π are well-typed", "the level of a well-typed sort is `WF`". They take only
`henv`; the injectivity ones take `henv hΓ`. In `ChurchRosser.lean` 26 of the 37
textual `forallE_inv` hits are the harmless `HasType.forallE_inv`.

---

## 2. What the circularity is, precisely

### 2.1 The import cycle that would exist

`Injectivity.lean` imports `EnvLemmas` + `Strong`. `UniqueTyping` imports `Injectivity`.
`ChurchRosser` imports `Pattern`, `Strong`, `UniqueTyping`. `HeadReduction` imports
`ChurchRosser`.

The natural proof of all three targets is Carneiro `thm:1dinv`: take
`Γ ⊢ e₁ ≡ e₂`, apply completeness of κ-reduction (`IsDefEq.church_rosser`,
`ChurchRosser.lean:1344`) to get `e₁ ≫* e₁' ≡ₚ e₂' ≪* e₂`, observe that sorts and Πs
are `ParRed`-rigid, and inspect the `NormalEq` (`≡ₚ`) constructor. All the work is
already there — `NormalEq`, `ParRed`, `CParRed`, `ParRed.triangle`,
`ParRedS.church_rosser`, `CRDefEq`, `IsDefEq.church_rosser`. But `ChurchRosser.lean` is
proved *using* `IsDefEq.uniq` (23 sites) and `IsDefEqU.forallE_inv`/`sort_inv` (12
sites), and `IsDefEq.uniq` is proved *using* `forallE_inv_stratified` and `sort_inv`.
So the injectivity statements sit strictly below the machinery that would prove them.

Concretely, the three would fall out of the *existing* code in ~30 lines each if
`IsDefEq.church_rosser` were available:

* `sort_inv`: sorts are `ParRed`-rigid, so CR yields `NormalEq Γ (.sort u) (.sort v)`.
  Constructors that can match: `refl` (⇒ `u = v`), `sortDF` (⇒ `u ≈ v` ✔), `proofIrrel`
  (⇒ `Γ ⊢ p : .sort .zero` and `Γ ⊢ .sort u : p`; unique typing then gives
  `p ≡ .sort (.succ u)`, and typing those two gives `.sort .zero ≡ .sort (.succ (.succ u))`,
  so `sort_inv` again ⇒ `0 ≈ succ (succ u)`, contradiction). This is Carneiro
  `unique.tex:264-266` verbatim.
* `sort_forallE_inv`: same, `NormalEq (.sort u) (.forallE A' B')` has only `proofIrrel`
  available, contradiction as above (`unique.tex:274-276`).
* `forallE_inv`: `NormalEq (.forallE A₁ B₁) (.forallE A₁' B₁')` — only `refl`,
  `forallEDF` (✔), and `proofIrrel` (contradiction) apply; `etaL`/`etaR` need a `.lam`
  on one side (`unique.tex:268-272`).

The `proofIrrel` branch is exactly where Carneiro writes *"(Note: we are using that
`⊢_n` has unique typing here.)"* (`unique.tex:180`) — the reason the whole thing must be
stratified.

### 2.2 What `HasTypeStratified` actually does, and why it is *not* `⊢_n`

`Theory/Typing/Strong.lean:826-858`:

```lean
variable (env : VEnv) (U : Nat) in
inductive HasTypeStratified : List VExpr → VExpr → VExpr → Bool → Nat → Prop where
  | bvar    : Lookup Γ i A → Γ ⊢ A : .sort u !! n → Γ ⊢ .bvar i :! A !! n+1
  | sort'   : l.WF U → l'.WF U → l ≈ l' → Γ ⊢ .sort l :! .sort (.succ l') !! n
  | const   : … → Γ ⊢ ci.type.instL ls : .sort u !! n → Γ ⊢ .const c ls :! … !! n+1
  | app     : … five premises at !! n … → Γ ⊢ .app f a :! B.inst a !! n+1
  | lam     : … four premises at !! n … → Γ ⊢ .lam A body :! .forallE A B !! n+1
  | forallE : … two premises at !! n … → Γ ⊢ .forallE A body :! .sort (.imax u v) !! n+1
  | base    : Γ ⊢ e :! A !! n → Γ ⊢ e : A !! n
  | defeq   : u.WF U → Γ ⊢ A ≡ B : .sort u →          -- ← unstratified `IsDefEq env U`!
              Γ ⊢ A : .sort u !! n → Γ ⊢ B : .sort u !! n →
              Γ ⊢ e : A !! n → Γ ⊢ e : B !! n+1
```

The notation in scope (`Strong.lean:819-821`) is
`local notation Γ " ⊢ " e1 " ≡ " e2 " : " A => IsDefEq env U Γ e1 e2 A`, i.e. the
conversion premise of `defeq` is the **full, un-indexed** `VEnv.IsDefEq`. `n` therefore
measures only the height of the *typing skeleton*; conversions are unrestricted.

Carneiro's index is the opposite (`unique.tex:10-15`):

> * `Γ ⊢₀ α ≡ β` iff `α = β`.
> * `Γ ⊢_{n+1} α ≡ β` iff there is a proof of `Γ ⊢ α ≡ β` using only `Γ ⊢_n e : α` typing judgments.
> * `Γ ⊢_n e : α` means there is a proof of `Γ ⊢ e : α` in which all appeals to the conversion rule use `Γ ⊢_m α ≡ β` for `m ≤ n`.

That is an **alternation** count between the two mutually-recursive judgments, and its
whole purpose is that `⊢₀` has definitional inversion for free (`thm:0dinv`) and that
the Church–Rosser development at level `n+1` may assume unique typing at level `n`
(`unique.tex:64`: *"we will assume that `⊢_n` has unique typing, which will prevent the
appearance of certain pathologies"*).

The repo's index solves a different, purely local problem. Look at `IsDefEq.uniq`
(`UniqueTyping.lean:13-111`). Its `suffices` states a *stronger* claim than `thm:utype`:

```lean
∀ {e A B b n₁ n₂ n}, n₁ ≤ n → n₂ ≤ n →
  env.HasTypeStratified U Γ e A b n₁ → env.HasTypeStratified U Γ e B b n₂ →
  ∃ u, Γ ⊢ A ≡ B : .sort u ∧ ∃ v, u ≈ v ∧
    env.HasTypeStratified U Γ A (.sort u) true (n-1) ∧
    env.HasTypeStratified U Γ B (.sort v) true (n-1)
```

and proceeds by `WellFounded.induction Nat.lt_wfRel.2` on `n`, then induction on the
first derivation. In the `app` case (lines 40-56) it obtains from the IH a defeq of the
two Π types, feeds it to `forallE_inv_stratified`, and receives
`d4 : HasTypeStratified (A::Γ) B (.sort u) true n`, `d5 : … B' … n'`. **`d4`/`d5` are
not sub-derivations of anything** — they are freshly manufactured. The only reason the
subsequent `IH _ (Nat.lt_succ_self _) hΓ₁ le₁ (Nat.le_refl _) a4 d4` is legal is the
numeric bound. So `HasTypeStratified` is a *substitute measure for `thm:utype`'s
structural induction*, forced by the fact that the repo's `uniq` also has to produce
sort witnesses.

**Consequence.** The stratification is already load-bearing and correctly designed for
what it does — but it gives no traction on the three sorries, because their hypothesis
`h1 : env.IsDefEqU U Γ (.forallE A B) (.forallE A' B')` is an *unstratified* defeq and
their conclusion is unstratified defeq too. There is no `n` to induct on for them.

### 2.3 Could one instead index by height of the whole `IsDefEq`?

No. A plain derivation-height index on the combined `IsDefEq` judgment fails because the
Church–Rosser development manufactures new derivations of unbounded height (β-reduction,
`ParRed.defeq`, `NormalEq.defeq`) and calls `uniq` on them. Carneiro's alternation count
survives that: a level-`(n+1)` conversion derivation only ever contains level-`n` typing
judgments, and the κ-reduction/`≡ₚ` machinery is *defined* over level-`n` typing, so
every `uniq` appeal inside it is at level `n`. Reproducing that in this repo means
re-indexing `ParRed`, `CParRed`, `NormalEq`, `CRDefEq` and all ~2300 lines of
`ChurchRosser.lean` + `HeadReduction.lean`.

---

## 3. Mapping `unique.tex` onto the repo

| `unique.tex` | Repo | Status |
|---|---|---|
| `Γ ⊢ e : α` | `VEnv.HasType env U Γ e A` := `IsDefEq env U Γ e e A` (`Typing/Basic.lean:60`) | ✔ |
| `Γ ⊢ α ≡ β` (untyped) | `VEnv.IsDefEqU env U Γ A B` := `∃ A', IsDefEq … A B A'` (`Basic.lean:66`) | ✔ (typed, `∃`-erased) |
| `⊢_n` stratified judgments (`unique.tex:10-15`) | **absent** | ✗ |
| `n`-provability basics lemma (18-25) | `HasTypeStratified.mono`, `HasTypeStrong.stratify` (`Strong.lean:872, 885`) — but for the *wrong* index | partial/mismatched |
| Definitional inversion (1)(2)(3) (`unique.tex:29-37`) | `IsDefEqU.sort_inv`, `IsDefEqU.forallE_inv`, `IsDefEqU.sort_forallE_inv` | **the 3 sorries** |
| `thm:utype` unique typing at `n` (40-53) | `IsDefEq.uniq` (`UniqueTyping.lean:13`) | ✔ modulo the sorries |
| `thm:0dinv` `⊢₀` has def. inversion (56-61) | **absent** (no `⊢₀`) | ✗ |
| `rec`-normal form / η-expansion preprocessing (74-89) | `Params.Pat` + `pat_simple`/`pat_uniq`/`pat_app_*` discipline (`ChurchRosser.lean:12-31`) | different but equivalent device |
| κ-reduction `⇝_κ` (91-103) | folded into `ParRed` | ✔ |
| proof-irrelevance relation `≡_p` (112-119) | `NormalEq` (`ChurchRosser.lean:81-116`) — has `refl, sortDF, constDF, appDF, lamDF, forallEDF, etaL, etaR, proofIrrel` | ✔ |
| Regularity of reductions (121-131) | `NormalEq.defeq`, `NormalEq.symm/.trans/.weakN/.instN`, `ParRed.defeq` | ✔ |
| parallel reduction `≫_κ` (138-150) | `ParRed` (`ChurchRosser.lean:470`) | ✔ |
| complete reduction `⋙_κ` (154) | `CParRed` (`ChurchRosser.lean:485`), `CParRed.exists` (714) | ✔ |
| `thm:gg_prop` (157-166) | `ParRed.weakN/.instN/.defeq/.hasType`, `CParRed.toParRed` | ✔ |
| `thm:gg_compat` (168-183) | `NormalEq.parRed` (`ChurchRosser.lean:1178`) | **2 `sorry`s** at 1190, 1209 (both the `extra`/ι case) |
| `thm:tri` triangle lemma (184-221) | `ParRed.triangle` (`ChurchRosser.lean:763`) | ✔ |
| `thm:church_rosser` (135-137, 223-238) | `ParRed.church_rosser` (913), `ParRedS.church_rosser` (1299) | ✔ |
| `≡_κ` (240) | `CRDefEq` (`ChurchRosser.lean:1294`) | ✔ |
| `thm:ckappa` completeness of κ (242-254) | `IsDefEq.church_rosser` (`ChurchRosser.lean:1344`) | ✔ |
| `thm:1dinv` `⊢_{n+1}` has def. inversion (258-278) | **absent** | ✗ |
| `thm:unique` final induction on `n` (282-288) | **absent** | ✗ |

**Where the repo diverges, and why that is exactly why the three are stuck.** The repo
implemented §4 (the κ-reduction / Church–Rosser half of `unique.tex`) *at the top level*,
un-indexed, and simply assumed §3's definitional inversion as three axioms. It never
implemented the `⊢_n` scaffolding (§1-2) that makes the induction close. So the repo has
everything Carneiro has except the one device — the alternation index — whose sole job
is to break this circle.

Secondary divergences worth noting:

* Carneiro's defeq is a 2-place judgment `Γ ⊢ α ≡ β`; the repo's is 4-place
  `IsDefEq Γ e₁ e₂ A`, with typing defined as `IsDefEq Γ e e A`. The typing and
  conversion judgments are literally the same relation. That makes Carneiro's
  "alternation between the two judgments" harder to define, and is probably why the
  repo's author reached for a typing-height index instead.
* Carneiro's `thm:utype` proof needs no numeric measure at all; the repo's `IsDefEq.uniq`
  does, because it simultaneously produces the stratified sort witnesses used by the
  `app`/`lam` cases.
* `IsDefEq.uniq`'s conclusion `∃ u, Γ ⊢ A ≡ B : .sort u` matches `thm:unique` exactly.

---

## 4. Survey of `Lean4Lean/Experimental/`

### 4.0 Build status

`lakefile.toml:36-38` declares `[[lean_lib]] name = "Lean4Lean.Experimental"`,
`globs = ["Lean4Lean.Experimental.+"]`. It is **not** in `defaultTargets`, there is no
`Lean4Lean/Experimental.lean` aggregator, and `Lean4Lean.lean` does not import it — but
`.github/workflows/ci.yml:35-36` builds it explicitly, so everything here compiles.
Nothing in `Theory/` or `Verify/` depends on it.

### 4.1 The live track: `SExpr → ShapeLogRel → ShapeLogRelAdequacy → UniqueTyping`

| File | Lines | `sorry`-using decls | `axiom` |
|---|---|---|---|
| `SExpr.lean` | 1324 | **25** | 1 (`Params.extra_pat`, line 614) |
| `ShapeLogRel.lean` | 6100 | **0** (the 8 grep hits are all inside a dead `/- … -/` block at 1665-1732) | 0 |
| `ShapeLogRelAdequacy.lean` | 473 | **1** (`LR.adequacy`, the `const` case) | 0 |
| `UniqueTyping.lean` | 266 | **0** | 0 |

**`SExpr` is `VExpr` with semantically-quotiented levels.** `SExpr.lean:87-94` is
structurally identical to `VExpr` (`Theory/VExpr.lean:7-13`); the only difference is that
`sort`/`const` carry `SLevel` instead of `VLevel`, where (`SExpr.lean:48-49`)

```lean
/-- A semantically quotiented version of `VLevel`. This avoids the need for some congruences. -/
def SLevel := { f : List Nat → Nat // ∃ l : VLevel, l.WF univs ∧ l.eval = f }
```

Two `VLevel`s that are `≈` collapse to one `SLevel`, which is exactly why
`SExpr.sort_inv` can conclude `u = v` rather than `u ≈ v`. Note that `SLevel.mk` is
**surjective** onto `SLevel` by the subtype's own defining property — this matters for
the bridge (§6).

`SExpr.IsDefEq` (`SExpr.lean:588-612`) is a near-copy of `VEnv.IsDefEq` with three
changes: (i) level-`WF` side conditions vanish (SLevels are WF by construction);
(ii) `sortDF`/`constDF` become plain `sort`/`const` (the `≈`-congruences become
`rfl`); (iii) it **adds** a heterogeneous transitivity

```lean
  /-- Heterogeneous transitivity: middle term may be at a different sort. -/
  | trans' : Γ ⊢ A ≡ B : .sort u → Γ ⊢ B ≡ C : .sort v → Γ ⊢ A ≡ C : .sort u
```

`trans'` is the device that makes the whole thing non-circular: it lets you build a
derivation *without knowing* that the two sorts agree, so translating into `SExpr` never
requires unique typing. `Experimental/UniqueTyping.lean` then closes the loop —
`IsDefEq.uniq_sort` (line 174) proves the sorts do agree, and `IsDefEq.iff_isDefEq'`
(line 261) shows the `trans'`-free system `IsDefEq'` is equivalent.

**All three targets are proved in SExpr form** (`ShapeLogRelAdequacy.lean`, bodies
`sorry`-free):

```lean
theorem forallE_whRed_l (d : Γ ⊢ A₀ ≡ SExpr.forallE B₁ F₁ : .sort s) :        -- line 434
    ∃ B₀ F₀, Γ ⊢ A₀ ⤳* .forallE B₀ F₀ ∧ ∃ u v,
      Γ ⊢ B₀ ≡ B₁ : .sort u ∧ B₀::Γ ⊢ F₀ ≡ F₁ : .sort v

theorem forallE_inv (H : Γ ⊢ SExpr.forallE A₀ B₀ ≡ SExpr.forallE A₁ B₁ : .sort s) :  -- 448
    ∃ u v, Γ ⊢ A₀ ≡ A₁ : .sort u ∧ A₀::Γ ⊢ B₀ ≡ B₁ : .sort v

theorem sort_forallE_inv : ¬Γ ⊢ .sort u ≡ SExpr.forallE A₁ B₁ : .sort s        -- 455

theorem sort_inv (d : Γ ⊢ SExpr.sort u ≡ SExpr.sort v : V) : u = v              -- 459
```

Note `sort_inv` takes an **arbitrary** ambient type `V`, matching `IsDefEqU` exactly;
`forallE_inv` and `sort_forallE_inv` currently require the ambient type to be `.sort s`
(a small generalisation to close, see §6).

They all rest on the fundamental theorem `LR.adequacy` (`ShapeLogRelAdequacy.lean:106`),
which has **one** `sorry`, at line 154, in the `const` case:

```lean
  | @const c ci Γ ls _ h1 h2 h3 =>
    …
    intro σ; rw [(Params.henv.closedC h1).mkS.instL.subst_eq .zero]; clear σ
    sorry
```

The remaining goal is reflexivity of the logical relation at a bare constant. It is the
case that needs `CtorBundle`/`Params.ctor_ty` — i.e. "a constructor's type is a
Π-telescope ending in an application of its inductive type". Every other case (`bvar`,
`symm`, `trans`, `trans'`, `sort`, `appDF`, `lamDF`, `forallEDF`, `defeqDF`, `beta`,
`eta`, `proofIrrel`, `extra`) is discharged.

**How `ShapeLogRel.lean` works** (6100 lines, fully proved). It builds a
*shape-indexed, finitely-approximated logical relation*:

* `Shape n` (line 53) — an `n`-fold iterate of `ShapeS` over `Shape0`; level 0 has only
  `bot` and `sort rel`, each successor adds `forallE`, `lam`, `ctor`, `indTy`. A
  dependent function's shape is a **finite table** `ShapeFun n := List (Shape n × Shape n)`
  (57), so shape application is a decidable finite lookup. This finiteness is what makes
  the relation definable by ordinary recursion on `n`.
* `WShape n` (928) = well-formed shapes; `TShape := Σ n, WShape n` (1819) = level-erased.
* `Shape.HasType`/`HasTypePi`/`HasTypeLam` (2486-2513) — a kinding judgment on shapes.
* `LE_Interp ρ m M` (3333) — *"shape `m` is a lower bound on the shape of expression `M`"*,
  with `| bot : LE_Interp ρ .bot M` always available. **This is the crucial design choice:
  the shape assignment is a *relation with a bottom element*, not a function.** It makes
  the assignment free to construct, so no unique-typing input is required (contrast
  `Stronger.lean`, §4.2).
* `LE_Interp.strongSound` (5054) — first fundamental lemma: defeq preserves
  shape-interpretation. **Complete, all 14 cases.** Corollary `LE_Interp.sound` (5261).
* `LogRel Γ n` (5265-5291) — a record bundling `DefEq`/`TyDefEq` together with *all*
  their structural closure properties as fields (`sort_iff`, `bot`, `symm`, `trans`,
  `trans'`, `conv`, `whr`, …). `sort_iff` is where sort-injectivity is baked in.
* `LR0` (5307) / `LRS` (5657) / `LR` (5896) — the relation by recursion on `n`. The
  disjointness engine is `LRS.DefEq` (5612): at type-shape `forallE` the relation is
  `False` unless the element shape is `bot` or `lam`, so
  `LRS.DefEq.sort_forallE : … ↔ False := .rfl` (5640).
* `LR.SubstWF` (6070) — semantic substitutions, consumed by the adequacy proof.

**`SExpr.lean`'s 25 open declarations** (the real debt), grouped:

| Group | Declarations (line) |
|---|---|
| **defeq ↔ strong bridge** (most load-bearing; both fundamental lemmas start `replace H := H.strong`) | `IsDefEq.strong` (679), `IsDefEqStrong.defeq` (680) |
| **inductive/ctor shape** | `Params.ctor_ty` (682) |
| **stratified typing** (exact copies of lemmas already proved in `Theory/Typing/Strong.lean:910,917`) | `HasTypeStratifiedS.to_core` (734), `.isType` (737) |
| **substitution** (used pervasively by Adequacy via `W.toSubstEq`) | `Ctx.Subst.lift_r` (760), `Ctx.Subst.id` (770), `IsDefEq.subst` (786), `Ctx.SubstEq.lookup` (794), `Ctx.SubstEq.lift` (797), `IsDefEq.defeqDF_l'` (823), `IsDefEqLift.subst` (885) |
| **weak-head reduction — all holes are the `extra`/pattern case** | `WHRed.subst` (953), `.weak'` (959), `.weakU_inv` (965), `.determ` (981, ×5), `WHRedS.defeq` (1008), `ParRed.weak'` (1060), `WHRedS.parRedS` (1182) |
| **type inference** | `InferType.hasType` (1091), `InferTypeS.hasType` (1167), `InferType.whRed` (1316, ×2) |
| **a second, in-file Church-Rosser development** (probably *not* on the injectivity path) | `NormalEq.symm` (1248), `NormalEq.weak'` (1259), `CRDefEq.trans` (1294) |

Measured axiom footprints today:

```
Lean4Lean.SExpr.sort_inv            → [propext, sorryAx, Classical.choice, Quot.sound, Params.extra_pat]
Lean4Lean.SExpr.forallE_inv         → same
Lean4Lean.SExpr.HasTypeS.uniq       → same
Lean4Lean.SExpr.IsDefEq.iff_isDefEq'→ same
```

Finally: **no instance of `SExpr.Params` exists anywhere**, and `SExpr.Params` requires
a `classify : Name → Option Classification` tagging every constant as
`ctor`/`etaCtor`/`symb`/`indTy`. This is the same debt the mainline already carries —
`PLAN.md:108` records *"nothing instantiates `VEnv.Params`"* for `ChurchRosser.lean:12` —
but the two `Params` classes are **different** (SExpr's adds `classify` and
`pat_wf : Pat p r → p.WF classify`; the mainline's adds `pat_wf`-as-soundness,
`pat_app_l`, `pat_app_l_uniq`, `pat_app_uniq`, `extra_pat`). A single environment would
have to satisfy both.

### 4.2 `Stronger.lean` (627 lines) — the one other real asset

Approach: annotate the judgment with **the level of the type**. `VEnv'.VConstant`/`VDefEq`
carry a `level : VLevel` (lines 7, 10); `VCtx := List (VExpr × VLevel)` (49); and
`IsDefEqStrong : VCtx → VExpr → VExpr → VExpr → VLevel → Prop` (57), written
`Γ ⊢ e₁ ≡ e₂ : A : u`.

**`IsDefEqStrong.sort_invL` (lines 547-551) is a complete, `sorry`-free proof of sort
injectivity in this calculus** (I re-read the proof; it is a 20-line induction with no
holes):

```lean
theorem IsDefEqStrong.sort_invL {env : VEnv'}
    (H : env.IsDefEqStrong U Γ e1 e2 A u) :
    (.sort v = e1 → u ≈ v.succ.succ) ∧
    (.sort v = e2 → u ≈ v.succ.succ) ∧
    (.sort v = A → u ≈ v.succ)
```

From `Γ ⊢ .sort u ≡ .sort v : A : l` the first two conjuncts give
`l ≈ u.succ.succ` and `l ≈ v.succ.succ`, hence `u ≈ v` by `VLevel.succ_congr_iff`. There
is also a partial Π-inversion, `IsDefEqStrong.forallE_inv'` (477-480), proved.

**Why it does not close the gap.** The only bridge to the ordinary judgment is the *easy*
direction, `IsDefEqStrong.out` (line 193): `IsDefEqStrong env U Γ e₁ e₂ A u →
env.out.IsDefEq U Γ.out e₁ e₂ A`. There is no reflection `IsDefEq → IsDefEqStrong`, and
there cannot be a cheap one: `trans`/`defeqDF` demand the **same** level index on both
premises, so building the annotation requires level-uniqueness. That is the file's own
headline `IsDefEqStrong.uniqL'` (574-580), which is essentially unstarted — 4 `sorry`s at
lines 623, 625, 626, 627, with the author's comment at 625:

```lean
    -- looks like it needs unique typing :(
```

And it genuinely does: in the `appDF` case, two typings of `f a` at levels `v`, `v'`
come from `f : forallE A B` at `imax u v` and `f : forallE A' B'` at `imax u' v'`;
`imax u v ≈ imax u' v'` does **not** imply `v ≈ v'`, so you need Π-injectivity to get
`B ≡ B'`. Circular.

**The lesson worth carrying forward:** `Stronger.lean` assigns each judgment a *function*
(the level), which must be chosen and therefore requires uniqueness up front.
`ShapeLogRel` assigns a *lower-bound relation with a `bot`* (`LE_Interp`), which is free
to construct and only becomes informative where the derivation forces it. That is
precisely why one route stalls and the other does not.

### 4.3 The other ten files — all dead ends

| File | Approach | Live `sorry`s | Verdict |
|---|---|---|---|
| `Stratified.lean` (332) | stratified `HasType1`/`IsDefEq1` over an external defeq | 1 (line 91, `IsDefEq.induction1`'s `constDF`); 2 more inside `/- depends on church-rosser -/` | Dead as code — `unique_typing'` (211, 260) is **inside a block comment**. **But `DefInv` (lines 9-14) is the cleanest single statement of all three goals and is worth lifting verbatim** (see below). |
| `StratifiedUntyped.lean` (317) | same, with an untyped 3-place `IsDefEqU1` | 1 live (72) | Dead — near-duplicate of the above, ~65 % commented out, headline commented out. |
| `NormalEq.lean` (512) | `structure Typing` bundling ~50 fields, then `NormalEq` + `NormalEq.trans` | **0** | Dead *for this purpose*: it **assumes** the answers as fields `univ_defInv` and `forallE_defInv` (lines 87-88). Header says `-- TODO: remove, this is now part of ChurchRosser.lean`. |
| `ParallelReduction.lean` (905) | Takahashi/Tait–Martin-Löf over the same `Typing` record | 2 (699, 718 — the `extra`/pattern cases) | Dead: proves `church_rosser` (858) **using** `TY.forallE_defInv` at 10 sites. Superseded by `Theory/Typing/ChurchRosser.lean`, which has literally the same two sorries at 1190/1209. |
| `LogRel.lean` (379) | Kripke reducibility candidates over `SExpr`, `Type`-valued `LogRel` | 7 + 5 `stop` (= `repeat sorry`) | Dead: `fundamental` (353) handles only `symm` and part of `bvar`; `| _ => sorry` at 379. Superseded by `ShapeLogRel`. |
| `StepIndexed.lean` (88) | coinductive step-indexed sketch | 0, but 3 real `axiom`s (59, 60, 62) | Dead: a scratch note; the one ambition (`IsTy.uniq`) is commented out at 87-88. |
| `MoreStepIndexed.lean` (489) | **origin of the shape lattice** — `Shape n`, `ble/LE`, `lift`, `Join`, shape-indexed `LogRel` | 1 live (310, `ShapeFun.app_mono_l`) | Dead: `#exit` at **line 420**; the headline `TypeEq` (443) is never elaborated. Superseded by `ShapeLogRel.lean`, which is the finished version of this idea. |
| `DomainTheory.lean` (242) | inverse-limit domain `Dom` for `SExpr` | 0 explicit, but `stop` at 223 | Dead: no typing judgment at all; `Dom.out` (211), the projection out of the limit, is `stop`ped. |
| `CoinductiveLogRel.lean` (61) | `VExpr`-side coinductive LR over `HeadReduction` | 0 | Dead: lines 20-61 are one block comment; the live 19 lines prove nothing. |
| `Thierry.lean` (363) | *"Partial formalization of Coquand & Huber… I just wanted to make sure I understood the monotonicity theorem right"* | 14 (incl. `def subst` at 148 and the termination measure at 190) | Dead: foreign, universe-free calculus with its own `Expr`; no imports; `axiom mySorry`; assumes `WHRedTS.uniq_pi` as an **axiom** (181). |
| `Thierry2.lean` (831) | same paper, `D` rebuilt as an ideal completion of the shape lattice | 26, incl. `D.pi` (472 — **the Π former is `sorry`**) and `def subst` (571); plus ~9 more axioms | Dead: same foreign calculus. Its shape-lattice ideas were absorbed into `MoreStepIndexed` → `ShapeLogRel`. |

Worth lifting verbatim — `Experimental/Stratified.lean:9-14` states all three goals as a
single predicate, and the name `DefInv` appears **nowhere else in the repo**:

```lean
def DefInv (env : VEnv) (U : Nat) (Γ : List VExpr) : VExpr → VExpr → Prop
  | .forallE A B, .forallE A' B' =>
    ∃ u v, env.IsDefEq U Γ A A' (.sort u) ∧ env.IsDefEq U (A::Γ) B B' (.sort v)
  | .forallE .., .sort .. | .sort .., .forallE .. => False
  | .sort u, .sort v => u ≈ v
  | _, _ => True
```

---

## 5. Git archaeology

| Commit | Date | What it did |
|---|---|---|
| `2f4b1b2` *corollaries of unique typing* | 2023-12-16 | creates `Theory/Typing/UniqueTyping.lean` |
| `690cf91` *unique typing proved 🎉 (modulo injectivity)* | 2026-01-31 | **creates `Theory/Typing/Injectivity.lean` with the sorries** and proves `IsDefEq.uniq` from them; +464 lines to `Strong.lean` (this is where `HasTypeStratified` lands) |
| `3865842` *clean up Church-Rosser proof* | 2026-02-01 | proves `IsDefEqU.forallE_inv` from `forallE_inv_stratified` (the only later edit to `Injectivity.lean`) |
| `5049520` *standardization theorem* | 2026-02-02 | creates `HeadReduction.lean` (480 lines), which consumes `sort_forallE_inv` |
| `7232477` *corollary: injectivity of pi types* | 2026-04-08 | `ShapeLogRel.lean` + `ShapeLogRelAdequacy.lean` — Π-injectivity **in SExpr** |
| `da2ed76` *sort injectivity* | 2026-04-08 | same two files — sort injectivity **in SExpr** (+185 lines to `ShapeLogRel`) |
| `84f2b04` **"Finished injectivity! 🎉 / Resolved unique typing circularity using trans' auxiliary"** | 2026-05-13 | creates `Experimental/UniqueTyping.lean` (266 lines); +60 `ShapeLogRel`, +35 `ShapeLogRelAdequacy`, +68 `SExpr`; **+16 lines to `Theory/Typing/Strong.lean`** (`HasTypeStratified.to_core`, `HasTypeStratified.isType`) |

**Answer to "why is it no longer in place":** it never was. `84f2b04` never touched
`Theory/Typing/Injectivity.lean`. It "finished injectivity" **for `SExpr`**, an
`Experimental/` copy of the calculus, and the only thing it contributed to the mainline
was two 5-line helper lemmas in `Strong.lean`. The three `sorry`s have been untouched
since `690cf91` (2026-01-31) / `3865842` (2026-02-01). Nothing regressed; the bridge was
simply never built. Subsequent commits touching `Experimental/` (`1090ad7`, `4b9984e`,
`1772f58`, `97addd5`, `ef849df`, toolchain bumps) are LogRel cleanup and CI repair, not
injectivity work.

---

## 6. Recommendation

### 6.1 Ruled out

* **Prove them from `IsDefEq.church_rosser`.** Impossible as the code stands: 12 direct
  and 23 indirect (via `uniq`) uses of the very statements inside `ChurchRosser.lean`.
* **Carneiro-faithful re-stratification** (define `⊢_n` for the *conversion* judgment and
  re-run §4 of `unique.tex` at each level). This is the mathematically canonical fix and
  it is what `unique.tex:282-288` does. But in this repo typing and conversion are the
  *same* 4-place relation (`HasType e A := IsDefEq e e A`), so the alternation index has
  to be introduced by hand, and `ParRed`, `CParRed`, `NormalEq`, `CRDefEq` and every
  `uniq`/`forallE_inv` appeal in ~2300 lines of `ChurchRosser.lean` + `HeadReduction.lean`
  must be re-indexed and each call's level re-checked. Weeks of mechanical but
  error-prone work on finished proofs. Keep as fallback only.
* **Re-do the shape logical relation over `VExpr` instead of `SExpr`.** The 6100-line
  `ShapeLogRel.lean` is written against `SExpr`'s `Subst`/`WHRed`/`ParRed` API and, more
  importantly, against `SLevel` — whose entire purpose is to make level congruences
  disappear. Porting to `VExpr` would reintroduce a `≈`-congruence obligation at every
  `sort`/`const` in 6100 lines. Build the bridge instead.
* **`Stronger.lean`.** `sort_invL` is real and free, but the annotation cannot be
  constructed without Π-injectivity (§4.2). Salvage the *insight*, not the code.

### 6.2 The recommended route: finish the SExpr shape-model track and bridge it

This is the only route with a complete design, a proved 6100-line core, and all three
targets already stated and proved on the far side.

**Phase 0 — logistics and measurement.**
`Theory/` may not import `Experimental/` (`Lean4Lean.Theory` is a default build target and
gates `Verify/Guard.lean`'s axiom whitelist, `Lean4Lean.Experimental` is not). Plan to
promote `SExpr.lean`, `ShapeLogRel.lean`, `ShapeLogRelAdequacy.lean` and a new
`Bridge.lean` into e.g. `Lean4Lean/Theory/ShapeModel/`. No import cycle results: `SExpr`
imports only `Theory/Typing/{Lemmas,Pattern}`, while `Injectivity` imports
`Theory/Typing/{EnvLemmas,Strong}`. Track progress with `#print axioms` on
`Lean4Lean.SExpr.sort_inv` / `.forallE_inv` (today: `sorryAx` + `Params.extra_pat`).

**Phase 1 — close the `SExpr.lean` substrate (25 declarations).** Order by how much of
the adequacy proof each unblocks:

1. `Ctx.SubstEq.lookup` (794), `Ctx.SubstEq.lift` (797), `IsDefEq.subst` (786),
   `Ctx.Subst.id` (770), `Ctx.Subst.lift_r` (760), `IsDefEqLift.subst` (885),
   `IsDefEq.defeqDF_l'` (823). Used pervasively by `ShapeLogRelAdequacy` via
   `W.toSubstEq` / `.subst W.toSubstEq`. The VExpr analogues exist and can be ported:
   `IsDefEqStrong.instN` (`Theory/Typing/Strong.lean:353`), `IsDefEqStrong.weakN` (144),
   and the `weakN`/`instN` block in `Theory/Typing/Lemmas.lean`.
2. `IsDefEq.strong` (679) and `IsDefEqStrong.defeq` (680) — *the* load-bearing pair;
   both fundamental lemmas open with `replace H := H.strong`. The VExpr analogue is the
   whole of `Theory/Typing/Strong.lean` (924 lines) culminating in `IsDefEq.strong`
   (line 689). **Design decision to take early:** `SExpr.IsDefEqStrong.const` carries a
   `CtorBundle` payload, which is what forces `Params.ctor_ty` (682). Move `ctor_ty`
   into `Params` as a well-formedness *field* rather than trying to prove it — it is
   exactly the kind of fact `VInductDecl.WF` (PLAN.md Phase B) will eventually supply,
   and pretending otherwise blocks Phase 1 on the keystone.
3. `HasTypeStratifiedS.to_core` (734), `.isType` (737) — verbatim ports of
   `HasTypeStratified.to_core`/`.isType` (`Theory/Typing/Strong.lean:910, 917`), ~5 lines
   each. Free.
4. `WHRed.determ` (981, five `extra`-overlap cases), `WHRed.subst` (953), `.weak'` (959),
   `.weakU_inv` (965), `ParRed.weak'` (1060). This is where `Params.pat_uniq` /
   `pat_app_*` earn their keep; `sort_inv`/`forallE_inv` route through
   `WHNF.sort.whRedS` / `WHNF.forallE.whRedS`, i.e. through `WHRedS.determ`, so these
   *are* on the critical path.
5. `WHRedS.defeq` (1008), `WHRedS.parRedS` (1182), `InferType.hasType` (1091),
   `InferTypeS.hasType` (1167), `InferType.whRed` (1316). **Check first** whether the
   injectivity chain uses them; `NormalEq.symm` (1248), `NormalEq.weak'` (1259) and
   `CRDefEq.trans` (1294) look like a *separate* in-file Church-Rosser development that
   injectivity does not need — if so, `#exit`-fence or delete them rather than proving
   them.
6. Convert `axiom Params.extra_pat` (614) into a `Params` field; the commented-out lines
   42-44 show the intended form.

**Phase 2 — close `LR.adequacy`'s `const` case** (`ShapeLogRelAdequacy.lean:154`), using
`Params.ctor_ty` as a field from Phase 1.2. At that point `SExpr.sort_inv`,
`SExpr.forallE_inv`, `SExpr.sort_forallE_inv`, `SExpr.HasTypeS.uniq` and
`SExpr.IsDefEq.iff_isDefEq'` are `sorryAx`-free.

**Phase 3 — the bridge (new code; none of this exists today).**

3.1 `mk`-commutation lemmas: `mk (e.liftN n k) = (mk e).liftN n k`,
    `mk (e.inst a k) = (mk e).inst (mk a) k`,
    `mk (e.instL ls) = (mk e).instL (ls.map SLevel.mk)`, and `Lookup` transfer. Partial
    coverage exists (`VExpr.ClosedN.mkS` at `SExpr.lean:160`, and `.mkS.instL.subst_eq`
    is used inside Adequacy).

3.2 Level dictionary: `SLevel.mk u = SLevel.mk v ↔ u ≈ v` for `WF` levels (both
    directions are `VLevel.eval` extensionality), and **surjectivity** of `SLevel.mk`
    onto `SLevel` (immediate from the subtype's `∃ l, l.WF univs ∧ l.eval = f`).

3.3 **Forward translation**
    `VEnv.IsDefEq U Γ e₁ e₂ A → SExpr.IsDefEq (Γ.map mk) (mk e₁) (mk e₂) (mk A)`,
    given a `Params` instance with `Params.env = env`, `Params.univs = U`. Routine, one
    case per rule: `sortDF`'s `l ≈ l'` and `constDF`'s `Forall₂ (·≈·) ls ls'` collapse to
    syntactic equality under `mk`, so both become reflexivity instances of `SExpr.sort` /
    `SExpr.const`; `extra` maps directly because `SExpr.IsDefEq.extra` is *already*
    stated in terms of `mk df.lhs`/`mk df.rhs`/`mk df.type`. Estimate 150-300 lines.

3.4 **`IsDefEqU.sort_inv` and `IsDefEqU.sort_forallE_inv` fall out here.** Their
    conclusions (`u ≈ v` and `False`) live entirely on the `SLevel`/`Prop` side, so
    **neither needs the reverse translation.** One small gap to close first:
    `SExpr.sort_forallE_inv` (`ShapeLogRelAdequacy.lean:455`) and `forallE_whRed_l` (434)
    require the ambient type to be `.sort s`, whereas `IsDefEqU` supplies an arbitrary
    type. `SExpr.sort_inv` (459) is already stated with an arbitrary `V`, so generalise
    `forallE_whRed_l` the same way (its `hmem : WShape.HasType … (.sort …)` obligation is
    where the constraint enters).

3.5 **Backward reflection** — needed *only* for `forallE_inv_stratified`:
    `SExpr.IsDefEq (Γ.map mk) (mk e₁) (mk e₂) (mk A) → ∃ A', VEnv.IsDefEq U Γ e₁ e₂ A'`.
    Two steps:
    * (a) eliminate `trans'` via `SExpr.IsDefEq.iff_isDefEq'`
      (`Experimental/UniqueTyping.lean:261`) — **already proved**, so the target becomes
      the `trans'`-free `IsDefEq'` (lines 195-216), whose constructors are in 1-1
      correspondence with `VEnv.IsDefEq`'s;
    * (b) induct on `IsDefEq'`, choosing a `VLevel` representative for each `SLevel`
      (surjectivity, 3.2). Different preimages of the same `SExpr` are exactly
      `EqUpToLevels`-related, and `IsDefEq.eqUpToLevels`
      (`Theory/Typing/Strong.lean:694`, with `EqUpToLevels` at 228) already says
      `IsDefEq` is closed under that relation — so the representative mismatches at
      `trans`/`defeqDF` are repairable. Expect to need a two-sided strengthening of
      `eqUpToLevels` (it currently rewrites only the right-hand term). **This is the one
      genuinely new metatheorem; budget it as the largest single item after Phase 1
      (order 400-800 lines).**

3.6 **The stratified bookkeeping in `forallE_inv_stratified`.** From
    `h2 : HasTypeStratified U Γ (.forallE A B) V true n`, peel the `base`/`defeq` chain
    down to the `forallE` node — giving `Γ ⊢ A : .sort u₀ !! m` and
    `A::Γ ⊢ B : .sort v₀ !! m` with `m + 1 ≤ n` — then retarget to the common sort `u`
    delivered by 3.5 with **one** `HasTypeStratified.defeq` step (index `m+1 ≤ n`) and
    `HasTypeStratified.mono` (`Strong.lean:872`). Purely mechanical; the inversion
    helper is the analogue of the already-proved `HasTypeStratified.to_core`/`.isType`
    (`Strong.lean:910, 917`). *This step is what makes `IsDefEq.uniq`'s well-founded
    recursion on `n` close* — see §2.2, and do not weaken the index in the statement.

**Phase 4 — delete the three `sorry`s.** `UniqueTyping`, `ChurchRosser`,
`HeadReduction`, `Verify/Typing/Lemmas.lean`, `Verify/TypeChecker/{InferType,Basic}.lean`
all light up with no further edits.

### 6.3 Induction measure and dependency order, in one line each

* **Injectivity itself:** no induction on the repo side. The induction lives inside
  `ShapeLogRel`'s recursion on the shape index `n` (`LR0`/`LRS`/`LR`,
  `ShapeLogRel.lean:5307/5657/5896`), which is well-founded because `Shape n` uses
  *finite* function tables. That is the measure that replaces Carneiro's alternation
  count.
* **`IsDefEq.uniq`:** unchanged — well-founded recursion on the `HasTypeStratified`
  height `n` (`UniqueTyping.lean:25`), which needs `forallE_inv_stratified` to be
  **index-preserving**.
* **Order:** Phase 1.1 → 1.2/1.3 → 1.4 → Phase 2 → 3.1/3.2 → 3.3 → **3.4 lands two of the
  three sorries** → 3.5 → 3.6 → **3.6 lands the third**.

### 6.4 Two caveats to raise before starting

1. **`Params` is uninstantiated on both sides.** Neither `SExpr.Params`
   (`SExpr.lean:23`) nor `VEnv.Params` (`ChurchRosser.lean:12`) has an instance anywhere,
   so `ChurchRosser`/`HeadReduction` are already vacuous today (`PLAN.md:108`). Adding
   `SExpr.Params` is therefore not new debt in kind, but the two classes differ
   (`classify`, `pat_wf : p.WF classify` on one side; `pat_wf`-as-soundness,
   `pat_app_l`, `pat_app_l_uniq`, `pat_app_uniq`, `extra_pat` on the other) and a real
   environment must eventually satisfy **both**. Consider unifying them into one class
   before Phase 1, so the eventual instance is built once.
2. **`Params.ctor_ty` / the `const` case is entangled with the inductive keystone.**
   `LR.adequacy`'s open case needs "a constructor's type is a Π-telescope ending in an
   application of its inductive type" — which is content of `VInductDecl.WF`
   (`Theory/Inductive.lean:5`, a `sorry` *definition*). Making it a `Params` field defers
   the entanglement cleanly, but it means Injectivity's final discharge in a real
   environment still waits on PLAN.md Phase B. Worth stating explicitly in `PLAN.md`:
   *Injectivity is not independent of the inductive spec.*


---

## 7. Implementation addendum (this session)

### 7.1 Answer to the dependency question

**Yes — gated.** `SExpr.sort_inv` (`ShapeLogRelAdequacy.lean:459`) calls `LR.adequacy`
directly, and `LR.adequacy` is one theorem whose `const` case is `sorry`. Machine-checked
`sorry` frontier of the two conditional results (7 declarations, not 25):

| # | Declaration | Location |
|---|---|---|
| 1 | `SExpr.IsDefEq.strong` | `SExpr.lean:687` |
| 2 | `SExpr.IsDefEqStrong.defeq` | `SExpr.lean:688` |
| 3 | `SExpr.IsDefEq.subst` | `SExpr.lean:794` |
| 4 | `SExpr.Ctx.SubstEq.lift` | `SExpr.lean:805` |
| 5 | `SExpr.IsDefEq.defeqDF_l'` | `SExpr.lean:831` |
| 6 | `SExpr.WHRed.determ` | `SExpr.lean:989` |
| 7 | `SExpr.LR.adequacy` | `ShapeLogRelAdequacy.lean:106` (the `const` case, line 162) |

plus the axiom `SExpr.Params.extra_pat` (`SExpr.lean:622`).

The inductive-spec entanglement enters through **#1**, not through `LR.adequacy` directly:
`SExpr.IsDefEqStrong.const` carries a `CtorBundle` payload, so `IsDefEq.strong` must
manufacture one, which is `Params.ctor_ty` (`SExpr.lean:690`, also `sorry`).

### 7.2 A third gate, found while implementing: `SExpr.mk` was lossy (now fixed)

`SLevel` was `{ f // ∃ l : VLevel, l.WF univs ∧ l.eval = f }` and
`SLevel.mk l = if l.WF univs then ⟨l.eval, …⟩ else .zero`. A constant's type `ci.type` has
levels well-formed at `ci.uvars`, unrelated to `univs`, so `mk` sent `.param i` (`i ≥ univs`)
to `zero`. Concretely with `univs = 0`, `ci.type = .sort (.param 0)`, `ls = [.succ .zero]`:
`mk (ci.type.instL ls) = .sort ⟨fun _ => 1⟩` but `(mk ci.type).instL (ls.map mk) = .sort ⟨fun _ => 0⟩`.
So `SExpr.IsDefEq.const` was **not** the image of `VEnv.IsDefEq.constDF` and no forward
simulation could exist.

Fixed by relaxing the subtype to `{ f // ∃ l : VLevel, l.eval = f }`, making
`SLevel.mk l = ⟨l.eval, l, rfl⟩` total and faithful. All `SExpr.IsDefEq` rules are unchanged.
Every downstream theorem is universally quantified over `SExpr`/`SLevel`, so a larger
`SLevel` makes them *stronger*, never vacuous. `ShapeLogRel.lean`, `ShapeLogRelAdequacy.lean`
and `Experimental/UniqueTyping.lean` rebuilt unmodified.

Caveat to record: level well-formedness is no longer tracked inside `SExpr`. Harmless for
the forward direction (`VEnv.IsDefEq` tracks it itself), but the eventual **reverse**
reflection (§6.2 step 3.5) must carry `VLevel.WF` as a side condition rather than reading it
off `SLevel`.

### 7.3 A safety landmine: do not fake the `Params` instance

`Params` is instantiable — `Pat := fun _ _ => False`, `classify := fun _ => none` satisfies
`pat_simple`/`pat_wf`/`pat_uniq` vacuously. But `SExpr.Params.extra_pat` is a standalone
`axiom`, not a class field, and it then proves `False`. Verified in a scratch buffer (not
committed): with `env := (∅ : VEnv).addDefEq ⟨0, .sort .zero, .sort .zero, .sort (.succ .zero)⟩`,
which is `Ordered`, `Params.extra_pat` yields `∃ …, False ∧ …`.

**Consequence:** `extra_pat` must become a `Params` field before any instance is built.

### 7.4 What was built

* `Lean4Lean/Experimental/Bridge.lean` (new, 160 lines, sorry-free, axioms `propext`,
  `Quot.sound` only): `SLevel.mk_inj/mk_congr/mk_succ/mk_max/mk_imax/mk_inst/mk_list_congr`,
  `SExpr.mk_lift'/mk_lift/mk_instL/mk_inst_of/mk_inst`, `Lookup.toSExpr`, and the
  **forward simulation** `VEnv.IsDefEq.toSExpr`, with `HasType`/`IsDefEqU` corollaries.
* `Lean4Lean/Experimental/BridgeInjectivity.lean` (new, 65 lines, sorry-free):
  `VEnv.IsDefEqU.sort_inv_params` and `VEnv.IsDefEqU.sort_forallE_inv_params` — the two
  target statements, relative to `[Params]` with `Params.env = env`.

`Theory/Typing/Injectivity.lean` was **not** modified: its statements quantify over every
`env` with `VEnv.WF env`, and no honest `Params` instance exists yet.

Confirmed en route: the forward direction really does suffice for both targets, and the
`.sort s` restriction on `SExpr.sort_forallE_inv` is *not* a blocker — it is removed on the
`SExpr` side using `SExpr.HasTypeS.uniq` (`Experimental/UniqueTyping.lean`), which retypes
the derivation at `.sort (mk u).succ`. Correcting §6.2 step 3.4.
