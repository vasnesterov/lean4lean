# Is there a shorter route to `IsDefEqU.sort_inv`?

Scouting pass, read-only. Every claim about file contents carries a `file:line`.
Claims are tagged **[verified]** (I read the source and the reasoning is
mechanical) or **[inferred]** (my analysis, not machine-checked).

Working tree at the time of the pass: `bdf7a41`, plus uncommitted edits to
`Experimental/ShapeLogRel.lean`, `Theory/Inductive/Lemmas.lean`,
`Theory/SetModel/{Consts,Interp,InterpSound,SoundInduction}.lean`,
`docs/soundness-ledger.md`, and two untracked files
(`Theory/MutualDefUnsound.lean`, `docs/design-shape-lattice.md`). Three of those
directories are being edited live; line numbers there may drift.

---

## Answer, up front

**No. There is no shorter route, and the two candidate shortcuts are both closed
— one by a circularity that is visible in the source, one by an equivalence that
is proved in the source.**

But the framing that prompted the question is wrong in a way that matters:

* The Church–Rosser route is **not** blocked by the `extra` case at
  `ChurchRosser.lean:1295`. It is blocked because the whole file rests on
  `IsDefEq.uniq`, which rests on `sort_inv`. Finishing `:1295` buys nothing
  towards `sort_inv`. **[verified]**
* The `ShapeLogRel` "datatype change to a 6100-line file" is **not** what stands
  in the way. The fix is already in your working tree: an 8-line change to two
  clauses of `Shape.hasType`, no datatype change, no lattice change
  (`git diff Lean4Lean/Experimental/ShapeLogRel.lean`; the reasoning is
  `docs/design-shape-lattice.md`, Option 4). **[verified]**
* What *does* stand in the way, and is not named in `PLAN.md`, is
  **`SExpr.IsDefEq.strong` (`Experimental/SExpr.lean:848`)** — a `sorry` on the
  direct path from `SExpr.sort_inv`, which the file's own docstring
  (`:756–772`) records as **false as stated**, for a reason independent of the
  one already fixed. Its `VExpr` analogue is ~700 lines. **[verified]**

So the honest outside view is: the current route really is the shortest, and it
is further from done than "one datatype fix". The remaining `ShapeLogRel` cone
holds **21 live `sorry`s, one statement known false as stated, and two
uninstantiated classes** — not one item.

### Ranked recommendation

| # | Route | Risk-adjusted verdict |
|---|---|---|
| 1 | **Finish `ShapeLogRel` adequacy** | Still the shortest. Re-plan against the real frontier below; start with `SExpr.IsDefEq.strong`, not with `Shape.hasType`. |
| 2 | Carneiro's conversion-alternation stratification | Real fallback, known-true destination, ~2300 lines of churn on 1475 lines of finished proof, and it needs the same keystone. Only if 1 stalls. |
| 3 | Rework the set model to split proofs *semantically* | Interesting, and I could not kill it outright — but its payoff is smaller than it looks (§2.4). Not worth starting. |
| 4 | Complete `ChurchRosser.lean:1295` | **Does not yield `sort_inv`.** Circular. Also: nothing on the `kernel_sound` path imports `ChurchRosser` or `HeadReduction` any more. Deprioritise entirely. |
| 5 | Purpose-built "small model" on `Option VLevel` | **Impossible as described.** Witness in §2.1. |

---

## Task 1 — the Church–Rosser route

### 1a. What `ChurchRosser.lean` proves, and where the `sorry` sits

**[verified]** The file is 1475 lines with exactly one `sorry`, at `:1295`.

Everything in it lives under `variable [Params]` (`:49`), where `Params`
(`:12–47`) is a class bundling:

```lean
class Params where
  env : VEnv
  henv : env.WF
  univs : Nat
  Pat : (p : Pattern) → p.RHS × p.Check → Prop
  pat_simple  : Pat p r → ∃ sp : SimplePattern, p = sp.toPattern
  pat_uniq    : …          -- non-overlap
  pat_wf      : …          -- each rule is semantically valid
  pat_app_l, pat_app_l_uniq, pat_app_uniq : …   -- orthogonality
  extra_pat   : env.defeqs df → … →
    ∃ Δ L R p r m1 m2, df.lhs.instL ls = VExpr.mkLams Δ L ∧ … ∧ Pat p r ∧ p.Matches L m1 m2 ∧ …
```

The top-level theorem is `IsDefEq.church_rosser` (`:1430–1475`):

```lean
variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem IsDefEq.church_rosser (H : Γ ⊢ e₁ ≡ e₂ : A) : Γ ⊢ e₁ ≫≪ e₂
```

with `CRDefEq` (`:1380–1382`)

```lean
def CRDefEq (Γ : List VExpr) (e₁ e₂ : VExpr) : Prop :=
  (∃ A, Γ ⊢ e₁ : A) ∧ (∃ A, Γ ⊢ e₂ : A) ∧
  ∃ e₁' e₂', Γ ⊢ e₁ ≫* e₁' ∧ Γ ⊢ e₂ ≫* e₂' ∧ Γ ⊢ e₁' ≡ₚ e₂'
```

`≡ₚ` is `NormalEq` (`:99–132`), Carneiro's `≡_p`: reflexivity, `sortDF`,
`constDF`, the congruences, `etaL`/`etaR`, and **`proofIrrel`** (`:130–132`).

The `sorry` is in `NormalEq.parRed` (`:1249–1366`):

```lean
variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem NormalEq.parRed (H1 : Γ ⊢ e₁ ≡ₚ e₂) (H2 : Γ ⊢ e₂ ≫ e₂') :
    ∃ e₁', Γ ⊢ e₁ ≫* e₁' ∧ Γ ⊢ e₁' ≡ₚ e₂'
```

specifically the `appDF` × `extra` case (`:1294–1295`). This is exactly
Carneiro's `thm:gg_compat` (`~/lean-type-theory/unique.tex:168–183`), whose two
last bullets (`:180`, `:181`) are the quotient case and the recursor case.

### 1b. Would completing it yield `sort_inv`? — No. The derivation already exists, and it is circular.

**[verified]** The derivation you asked me to write is already in the repo, at
`HeadReduction.lean:470–485`:

```lean
theorem IsDefEq.reduce_sort (H : Γ ⊢ e ≡ .sort u : A) :
    ∃ u', Γ ⊢ e ⤳* .sort u' ∧ u' ≈ u := by
  have ⟨_, _, e', _, h1, h2, h3⟩ := H.church_rosser hΓ
  …
  obtain ⟨v, rfl, a1⟩ : ∃ v, e' = sort v ∧ v ≈ u := by
    cases h3 with
    | refl => exact ⟨_, rfl, rfl⟩
    | sortDF _ _ h => exact ⟨_, rfl, h⟩
    | etaL h => cases ((HasType.sort hu).uniqU henv hΓ h).sort_forallE_inv henv hΓ
    | proofIrrel h1 _ h3 =>
      have := h1.defeqU_l henv hΓ ((HasType.sort hu).uniqU henv hΓ h3).symm
      have := ((HasType.sort (by exact hu)).uniqU henv hΓ this).sort_inv henv hΓ
      cases congrFun this []
```

The chain of names is therefore:

1. `IsDefEq.church_rosser` (`ChurchRosser.lean:1430`) → `CRDefEq`;
2. sorts are `ParRed`-normal, so both reducts are sorts — see 1d, this part is
   free;
3. case on `NormalEq` between two sorts: `refl`, `sortDF`, `proofIrrel`;
4. `refl`/`sortDF` give `u ≈ v` immediately;
5. **`proofIrrel` is killed with `IsDefEqU.sort_inv` itself** — line `:482`.

And step 5 is not an accident of this proof. `proofIrrel` says: there is a `p`
with `Γ ⊢ p : .sort .zero`, `Γ ⊢ .sort u : p`, `Γ ⊢ .sort v : p`. Refuting it
means showing `Sort u` is not a proof, i.e. that `.sort (u.succ)` and
`.sort .zero` cannot be definitionally equal — which is `sort_inv`.
Carneiro hits the identical wall and breaks it by stratification
(`unique.tex:266`, the `⊢_n` index: *"by unique typing at n, `Γ ⊢_n P ≡ U_{SS ℓ}`,
so by definitional inversion `0 ≡ SS ℓ`"*).

Worse, the circularity is not confined to one case. `ChurchRosser.lean` calls
`IsDefEq.uniq`/`uniqU` 22 times, `trans_l`/`trans_r`/`transU_*` 19 times and
`of_l`/`of_r`/`defeqU_*` 49 times; **every one of those is defined in
`UniqueTyping.lean` on top of `IsDefEq.uniq`** (`UniqueTyping.lean:113–169`),
and `IsDefEq.uniq` (`:13–111`) invokes `IsDefEqU.sort_inv` at nine sites
(`:50, :54, :65, :69, :71, :80, :83, :98, :108`) and
`IsDefEqU.forallE_inv_stratified` at `:43`. **[verified]**

> **Verdict (1b): the Church–Rosser route is circular, at the level of the whole
> file, not of one case.** `PLAN.md:209–211` already says this; I confirm it and
> can now point at the exact line (`HeadReduction.lean:482`) where the
> circularity is realised in code.

### 1c. How hard is the `extra` case, and is confluence false in this generality?

**[verified] `VDefEq.WF` requires essentially nothing** (`Theory/Typing/Basic.lean:75–76`):

```lean
def VDefEq.WF (env : VEnv) (df : VDefEq) : Prop :=
  env.HasType df.uvars [] df.lhs df.type ∧ env.HasType df.uvars [] df.rhs df.type
```

No orthogonality, no left-linearity, no non-overlap, no constraint on the shape
of `lhs`, and — worth naming — **no requirement that `lhs` and `rhs` be
semantically equal**. Under `VDefEq.WF` alone, confluence is plainly false: two
rules `c ⟶ a` and `c ⟶ b` with `a`, `b` distinct normal forms of the same type
satisfy it and diverge.

**But `sort_inv`'s hypothesis is `VEnv.WF env`, which is much stronger.**
`VEnv.WF` (`Theory/Typing/Env.lean:51`) is `∃ ds, VEnv.WF' ds env`, built from
`VDecl.WF` (`:17–45`), and the *only* ways a `VDefEq` enters are:

| Source | `lhs` shape | Cite |
|---|---|---|
| `.def` / `.mutualDef` (δ) | `.const name (VLevel.params n)` | `VDecl.lean:11–12` |
| `.quot` | `fun α r β f c a => Quot.lift α r β f c (Quot.mk r a)` | `Theory/Quot.lean:11` |
| `.induct` (ι) | `mkLams Γ' (D.iotaLhs j C)` | `Theory/Inductive/Decl.lean:520–525` |

So under `VEnv.WF` the rules are δ/quot/ι and the orthogonality `Params` demands
is, in principle, derivable. **[verified for the shapes; [inferred] that
orthogonality follows]**

The honest answer to "is confluence false here" is therefore: **false in the
generality of `VDefEq.WF`, and not-known-either-way in the generality of
`VEnv.WF`, because nothing instantiates `Params`** (`PLAN.md:173, 241`; the
class is at `ChurchRosser.lean:12` and I found no instance anywhere in the
repo). The `Params` class *is* the statement of what has to be true, and it is
missing two fields, per `PLAN.md:194–200`: the major premise of a recursor
pattern must have a type not defeq to a `.forallE` (to exclude `etaL`), and
small elimination (a recursor whose major premise is a proof is itself a proof).
Both are Carneiro's `unique.tex:180–181`, one of which he flags explicitly and
one silently.

**Cost of `:1295`, if you wanted it for its own sake: [inferred]** two new
`Params` fields, their discharge by `addInduct'` (i.e. the keystone), and a case
analysis mirroring `unique.tex:178–181`. Perhaps 200–400 lines *after* the
keystone. But see the next paragraph before spending it.

**`ChurchRosser.lean` is currently off the critical path entirely. [verified]**
`ChurchRosser` is imported only by `HeadReduction.lean:1` and `Theory.lean:4`;
`HeadReduction` only by `Theory.lean:5` and `Experimental/CoinductiveLogRel.lean:1`;
and **nothing imports `Lean4Lean.Theory`**. Meanwhile the set model's soundness
ledger now records that soundness consumes no injectivity beyond `sort_inv`
(`InterpSound.lean:1056–1105`, `docs/soundness-ledger.md`). So the marginal
value of `:1295` to `kernel_sound` is currently zero.

### 1d. The weaker statement — confirmed true, confirmed cheap, and confirmed insufficient

Your main hypothesis was: *no extra rule can rewrite a `.sort`, so `sort_inv`
may follow with no confluence theorem at all.*

**The first half is true and nearly free. [verified]**
`Pattern.Matches` (`Theory/Typing/Pattern.lean:97–102`) has three constructors:

```lean
inductive Pattern.Matches : (p : Pattern) → VExpr → (p.LPath → List VLevel) → (p.Path → VExpr) → Prop
  | const : Matches (.const c) (.const c ls) (fun _ => ls) nofun
  | var   : Matches f f' f1 g1 → Matches (.var f) (.app f' a') f1 (·.elim a' g1)
  | app   : Matches f f' f1 g1 → Matches a a' f2 g2 → Matches (.app f a) (.app f' a') …
```

Every constructor forces the matched expression to be a `.const` or an `.app`.
`ParRed.extra` (`ChurchRosser.lean:542–543`) is gated on `p.Matches e m1 m2`, so
`Γ ⊢ .sort u ≫ e` forces `e = .sort u`. The proof is literally
`cases H2 with | sort => … | extra r1 r2 => cases r2`, and the file already
writes it four times (`:1256–1257`, `:1305`, `:1318`, `:1365`). Likewise
`df.lhs` is never a `.sort` in a `VEnv.WF` environment (table in 1c), which is
provable by an `Ordered`-style induction over `VEnv.WF'` in ~60 lines with no
`Params`.

**The second half is false. [verified]** The obstacle to `sort_inv` is not the
`extra` rules; it is `proofIrrel` plus `IsDefEq.trans`/`symm`. Getting from
`IsDefEqU Γ (.sort u) (.sort v)` to *any* statement about reduction requires
`IsDefEq.church_rosser`, and that requires `IsDefEq.uniq` (90+ call sites),
which requires `sort_inv`. And even after reduction, the `NormalEq.proofIrrel`
case needs `sort_inv` again (`HeadReduction.lean:482`).

> **Hypothesis (1d): killed.** The observation is correct and cheap; it removes
> a case that was never the difficulty. I would not spend the 60 lines unless
> some other route asks for it.

---

## Task 2 — the purpose-built route

### 2.1 A syntactic invariant on `Option VLevel` is impossible — witness

**[verified]** Suppose `D : VExpr → Option VLevel` is any function of the
syntax with `D (.sort u) = some u`, and suppose `IsDefEq Γ e₁ e₂ A → D e₁ = D e₂`.
Take the `beta` rule (`Theory/Typing/Basic.lean:45–47`):

```
Γ ⊢ .app (.lam A e) e' ≡ e.inst e' : B.inst e'
```

with `A := .sort .zero`, `e := .sort (.succ .zero)` (weakened), `e' :=` any
inhabitant. Then `D (.app (.lam A e) e')` must equal `D (.sort (.succ .zero)) =
some 1`. Since a `.app` node carries no level, `D` must *evaluate*. So `D` is a
normalisation function, not a syntactic reading, and the argument is a
normalisation proof.

Independently, `proofIrrel` (`Basic.lean:51–53`) forces `D` to identify all
proofs — so `D` must know whether its argument is a proof, which is typing
information not present in the syntax. That is precisely the
`LevelAssign.srt`/`IsProof` split (`Interp.lean:254`, `:297`).

Both obstructions are constructor-level, so no choice of target domain avoids
them. The `extra` constructor is *not* what breaks this route.

### 2.2 Can `sort_inv` be read off the existing set model? — No, and the gating is essential, not incidental

**[verified]** The interpretation does send `.sort u` to a set determined by `u`
and by nothing else:

```lean
lemma interp_sort (Γ) (u) (ρ) : (interp M L Γ (.sort u)).toFun ρ = U M.κ (u.eval M.ls)
```
(`Theory/SetModel/Interp.lean:369–370`), and `U` is injective in its index below
the chain length: `U_mem_of_lt : i < j → j ≤ n → U κ i ∈ U κ j`
(`Universe.lean:215–217`), so `U κ i = U κ j` contradicts ∈-irreflexivity.
Soundness is assembled: `SoundInduction.lean:337–339` gives
`IsDefEq nv Γ e₁ e₂ A → SoundAbove M L Γ e₁ e₂ A`, i.e. above a threshold of
inaccessibles the two interpretations are *equal*. `M.ls : List ℕ`
(`Interp.lean:231`) is a free field, so quantifying over it turns
`u.eval M.ls = v.eval M.ls` into `u ≈ v`.

So the corollary is real — **and it is circular.** `interp` takes `L :
LevelAssign env nv` (`Interp.lean:313`), whose fields are

```lean
  lvl_sound : env.HasType nv Γ A (.sort u) → lvl Γ A ≈ u
  srt_sound : env.HasType nv Γ e A       → srt Γ e ≈ lvl Γ A
```
(`Interp.lean:259–263`), and the file itself proves the converse:

```lean
theorem lvl_uniq (hu : env.HasType nv Γ A (.sort u)) (hv : env.HasType nv Γ A (.sort v)) : u ≈ v :=
  (L.lvl_sound hu).symm.trans (L.lvl_sound hv)
```
(`Interp.lean:272–274`).

> **`LevelAssign` is *equivalent* to `sort_inv`-for-types (plus choice), by
> `lvl_sound` in one direction and `lvl_uniq` in the other. [verified]** The
> gating at `Interp.lean:22` is therefore **essential, not incidental**. No
> fragment of the interpretation as written is unconditional in the relevant
> sense: `interp` mentions `L` in exactly three clauses (`:325` `app`,
> `:331` `lam`, `:337` `forallE`) but is parameterised on it throughout, and
> soundness needs all three.

### 2.3 The one thing I could not kill: semantic proof splitting

**[inferred throughout this subsection — no code, no proof.]**

`L` is used only to answer three yes/no questions (`Interp.lean:234–243`):
is `f` a proof (`app`), is `b` a proof (`lam`), is `B` a proposition
(`forallE`). Each is a `Decidable` `if` (`Interp.lean:300–304`). One could try
to answer them *semantically* instead:

* `forallE A B`: test `∀ v ∈ ⟦A⟧ρ, ⟦B⟧(ρ,v) ∈ UProp`. `UProp = ℘{pt}`
  (`Universe.lean:58`) is `ℒₛₑₜ`-definable, and the test is a function of the
  interpretations of `A` and `B`, hence stable under the congruence IHs.
* `app f a`: test `⟦f⟧ρ = pt`. Function of `⟦f⟧`, stable under the IH.
* `proofIrrel` needs no test at all: from the *typing* half of soundness,
  `Γ ⊢ p : .sort .zero` gives `⟦p⟧ρ ∈ U κ 0 = UProp`, hence `⟦p⟧ρ ⊆ {pt}`
  (`Universe.lean:61`), hence `⟦h⟧ρ = ⟦h'⟧ρ` outright.

**Where it breaks:** the `lam A b` clause. Its split must agree with the
`forallE A B` split for the *same* `B` — otherwise `⟦λx:A.b⟧ ∉ ⟦∀x:A.B⟧`. But
`B` does not occur in the syntax `lam A b`, and a test on `⟦b⟧` is not the same
test: take `pt = ∅` (`Universe.lean:53`) and a `b` whose value happens to be `∅`
under a non-propositional `B`; the `lam` test fires, the `forallE` test does
not, and the membership obligation fails. This is exactly why Carneiro splits on
`sort (A::Γ) b` — a fact about the *type* of `b`.

The only repair I can see is a **type-directed** interpretation `interp Γ A e`
carrying the expected type as a parameter, splitting `lam` on
`⟦A⟧ρ ⊆ {pt}` (a function of `⟦A⟧` alone, hence stable). That is a real design
and I could not refute it in this pass.

### 2.4 …but it would not help, and here is why

Even if §2.3 worked perfectly, **`sort_inv` would still be required**, because
the *refinement* layer needs it independently of the model. **[verified]**

`IsDefEq.uniq`/`uniqU` is used **80 times across eight files in
`Lean4Lean/Verify/`** (`Verify/Typing/Lemmas.lean`, `Typing/ConditionallyTyped.lean`,
`EquivManager.lean`, `TypeChecker/{WHNF,IsDefEq,Basic,InferType}.lean`,
`Primitive.lean`), plus 44 uses of the `trans_l`/`defeqU_*` family built on it.
`Verify/Typing/Lemmas.lean:5` and `Verify/Primitive.lean:3` import
`Theory.Typing.UniqueTyping` directly. And `IsDefEqU.forallE_inv` — which is
derived from `forallE_inv_stratified`, another of the three `sorry`s — is used
at `Verify/Typing/Lemmas.lean:2033` and `Verify/TypeChecker/InferType.lean:276, 286`.

Additionally, a model-based `sort_inv` is only ever available **relative to a
`V ⊧ 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰`**. `kernel_sound`'s proof does have such a `V` (that is the
shape of `SetTheory.provable_of_models`, `PLAN.md:31–32`), so it is not
*useless* — but threading that hypothesis through 124 call sites and every
downstream statement of the refinement layer is an architectural change far
larger than proving `sort_inv`. The repo has no Mathlib dependency
(`lakefile.toml`: `batteries`, `Foundation`, `lean4export`), so the alternative
— building the needed finite fragment of the cumulative hierarchy inside Lean's
own universes to get it unconditionally — is a from-scratch project.

> **Verdict (Task 2): the model route is closed.** §2.2 is circular by an
> equivalence proved in the source; §2.3 is speculative and, per §2.4, would not
> retire `sort_inv` even if it succeeded.

---

## Task 3 — are the other two statements dead?

**Answer: one is emphatically alive; the other is dead only by accident, and is
2 lines. Delete neither. [verified]**

`Theory/Typing/UniqueTyping.lean:1` is indeed the only importer of
`Injectivity.lean`, but the trace does not stop there.

**`IsDefEqU.forallE_inv_stratified` (`Injectivity.lean:14–21`) — ALIVE.**
Two consumers:

1. `IsDefEqU.forallE_inv` (`Injectivity.lean:23–31`) is proved *from* it — it is
   not an independent lemma;
2. `IsDefEq.uniq` uses it directly at `UniqueTyping.lean:43`.

And `IsDefEqU.forallE_inv` is consumed in:

| Site | Cite |
|---|---|
| `IsDefEq.uniq`'s app case | — (via `forallE_inv_stratified`) |
| refinement layer | `Verify/Typing/Lemmas.lean:2033`; `Verify/TypeChecker/InferType.lean:276, 286` |
| `ChurchRosser.lean` | `:330, :634, :885, :1128, :1137, :1142, :1154, :1198, :1223, :1288, :1361` |
| `HeadReduction.lean` | `:429, :645` |

The earlier name-level grep missed these because `Theory/Typing/Lemmas.lean:786–795`
defines a *different* `forallE_inv` family — `IsDefEq.forallE_inv'`,
`HasType.forallE_inv`, `IsType.forallE_inv` — which takes **one** argument
(`henv`) and says "a Π-type that is a type has component types". The injectivity
one takes **two** (`henv hΓ`) and is about `IsDefEqU`. Both names appear
throughout `ChurchRosser.lean`; the arity distinguishes them.

**`IsDefEqU.sort_forallE_inv` (`Injectivity.lean:33–34`) — dead *today*, but only
because its consumers are.** Its only two uses are
`HeadReduction.lean:479` (in `IsDefEq.reduce_sort`) and `:499` (in
`IsDefEq.reduce_forallE`). `HeadReduction.lean` is imported only by
`Theory.lean:5` and `Experimental/CoinductiveLogRel.lean:1`, and **nothing
imports `Lean4Lean.Theory`** — so it is off the `kernel_sound` path. It is also
confirmed unneeded by soundness (`InterpSound.lean:1105`,
`docs/soundness-ledger.md`).

Recommendation: **do not delete either.** `forallE_inv_stratified` is load-bearing
for the refinement layer. `sort_forallE_inv` is two lines and deleting it breaks
`HeadReduction.lean`, which is where you will look first if the CR route is ever
revived. If you want the file smaller, the honest edit is to record in its
docstring which of the three is on the critical path.

---

## What the `ShapeLogRel` route actually still needs

This is the part I would most want you to see, because it is where the five
optimistic estimates came from.

### The `Shape.hasType` item is already essentially done

**[verified]** `docs/design-shape-lattice.md` (untracked, 176 lines) lays out
four options and recommends Option 4 — quantify the sort by disjunction outside
`hasType.core`. **That change is already applied in your working tree**, and it
is 8 lines across two clauses, with no datatype change, no lattice change and no
`Prop`/`Bool` change:

```
-  | _+1, .bot, .forallE a b => hasType.core hasType b a fun _ => .type
+  | _+1, .bot, .forallE a b =>
+    hasType.core hasType b a (fun _ => .sort false) ||
+    hasType.core hasType b a (fun _ => .sort true)
```

The lemma layer has not caught up yet — `Shape.HasTypeLam`
(`ShapeLogRel.lean:2509`) still reads `HasTypePi b a true`, which no longer
matches the new clause, so `Shape.HasType.unfold` (`:2524`) cannot hold as
stated. That is the live edit in flight, and the memo names the six sites
(`HasTypeU.bot`, `HasType.toType`, `HasType.isType`, `HasTypePi.toType`, the
four `LogRel` fields, the `WShape.HasDom` family).

**Cost: [inferred] tens to low hundreds of lines. This is not the blocker.**

### The blocker nobody has priced: `SExpr.IsDefEq.strong`

**[verified]** `SExpr.sort_inv` (`ShapeLogRelAdequacy.lean:472`) → `LR.adequacy`
(`:441–443`) → `adequacyS (H.strong hΓ)` → `SExpr.IsDefEq.strong`
(`Experimental/SExpr.lean:848`), which is

```lean
theorem IsDefEq.strong (hΓ : Ctx.WF Γ) : Γ ⊢ e1 ≡ e2 : A → IsDefEqStrong Γ e1 e2 A := sorry
```

Its own docstring at `SExpr.lean:756–772` records:

> **KNOWN DEFECT — `hu0` is false.** `Eq.refl : ∀ {α : Sort u} (a : α), a = a`
> has sort `imax (u+1) (imax u 0) = 0`, so `u = .zero` for it; yet `Eq.refl`
> must be `classify`-ed as a constructor … So `CtorBundle Eq.refl` is
> uninhabited while `IsDefEqStrong.const` demands `∀ cl, CtorBundle c cl` — i.e.
> this is a *second*, independent reason that `IsDefEq.strong` is false as
> stated.

The named fix touches `CtorBundle` (`SExpr.lean:776–789`, the `hu0` field at
`:783`), the `mkPi`/`mkApp` ordering of `rhs`, and `LE_Interp.build_spine` in
`ShapeLogRel.lean` (a `.bot` branch for `Prop`-valued inductives). The `VExpr`
analogue of this theorem, `VEnv.IsDefEq.strong`, is
`Theory/Typing/Strong.lean:689`, standing on roughly 680 lines (`:12–692`) — and
the `SExpr` judgment (`SExpr.lean:801–826`) is *not* a copy: it adds `trans'`
(heterogeneous transitivity, `:806`) and a `const` rule carrying a `CtorBundle`
(`:808–813`).

**Cost: [inferred] 500–1000 lines plus a datatype repair. This is the largest
single open item on the route and `PLAN.md` does not list it.**

### Full frontier of the route, as I found it

| Item | Cite | Note |
|---|---|---|
| `Shape.hasType` lemma layer | `ShapeLogRel.lean:2486–2511` | in flight; Option 4 applied, ~6 sites to follow |
| `SExpr.IsDefEq.strong` | `SExpr.lean:848` | `sorry`, **false as stated** (`:758`) |
| `LR.adequacy` `const` case | `ShapeLogRelAdequacy.lean:150–156` | needs `Params.ctor_ty` |
| 19 further `SExpr.lean` `sorry`s | `:960, :963, :1066, :1075, :1361, :1432, :1438, :1448, :1555, :1616, :1638, :1714, :1729, :1798, :1810, :1842, :1870, :1871` | **[not verified]** which lie in `sort_inv`'s cone |
| `Params` + `ParamsExtra` instances | `BridgeInjectivity.lean:15–22` | the keystone tie-in; `Params` alone is satisfiable trivially, `ParamsExtra.extra_pat` is the real content |

Two facts that put this in perspective:

* `ShapeLogRel.lean` (6122 lines) really is `sorry`-free in live code — its five
  remaining `sorry`s (`:1702, :1710, :1711, :1719, :1721`) sit inside the block
  comment opened at `:1666` and closed at `:1735`. `PLAN.md:220` is accurate.
  **[verified]**
* `Bridge.lean` (218 lines) really is `sorry`-free, and
  `VEnv.IsDefEqU.sort_inv_params` (`BridgeInjectivity.lean:44–47`) is a
  three-line consequence. The forward bridge is genuinely done. **[verified]**

So the route is: **`SExpr.lean`'s decorated judgment is the frontier, not the
shape lattice.**

---

## The fallback, priced

**Carneiro's conversion-alternation stratification.** `unique.tex:10–15` indexes
by alternations between `⊢ e : α` and `⊢ α ≡ β`; `thm:1dinv` (`:258–278`) then
derives definitional inversion at `n+1` from unique typing at `n`, killing the
`proofIrrel` case at `:266` with a *stratified* `sort_inv`. This is the only
published proof of the statement and it is known to work.

The repo's `HasTypeStratified` (`Strong.lean:827–857`) is **not** that index: its
`defeq` constructor

```lean
  | defeq : u.WF U → Γ ⊢ A ≡ B : .sort u →
    Γ ⊢ A : .sort u !! n → Γ ⊢ B : .sort u !! n → Γ ⊢ e : A !! n → Γ ⊢ e : B !! n+1
```
(`:856–857`) carries a **full, unstratified `IsDefEq`** as its second premise. So
"definitional inversion at `n`" is not stateable against it, and `PLAN.md:213–217`
is right that adopting Carneiro's index means re-indexing the finished work.

**Cost [inferred]:** a new `⊢_n`/`≡_n` pair with its basics (300–500 lines); a
re-proof of `IsDefEq.uniq` on that index (`UniqueTyping.lean:13–111`, ~150–250
lines); and re-indexing `ChurchRosser.lean` (1475 lines, ~90 call sites into the
`uniq` family, 22 lemma statements). Call it 2000–3000 lines of churn on 1475
lines of finished proof. **And it still needs the same `Params` instance and the
same two missing `Params` axioms** — so it is not independent of the keystone
either.

Its one virtue over `ShapeLogRel`: the destination is *known true* and the proof
is *published*. If `SExpr.IsDefEq.strong` turns out to be a second false
statement rather than a repairable one, this is where to go.

---

## Two things worth knowing that I found on the way

1. **Both surviving routes need the inductive keystone.** `ShapeLogRel` needs
   `Params` + `ParamsExtra` (`BridgeInjectivity.lean:15–22`); Carneiro's route
   needs `VEnv.Params` (`ChurchRosser.lean:12`) plus two fields it does not yet
   have. So `sort_inv` is downstream of the keystone on every route, and
   `PLAN.md:236–237`'s "injectivity is not independent of the inductive-spec
   keystone" is if anything understated.
2. **`Theory/MutualDefUnsound.lean`** (untracked, another stream's work) exhibits
   a machine-checked refutation of `leanTTConsistent` via `VDecl.WF.mutualDef`
   (`Theory/Typing/Env.lean:26–30`, the `env'` in the third premise). I checked
   whether it also refutes `sort_inv`: it does not. δ-rules always have a
   `.const` left-hand side, so a self-referential definition gives you inhabited
   propositions, not new definitional equalities between sorts.

---

## Bottom line

The current `ShapeLogRel` route really is the shortest, and I am saying so
having tried to break it. What has changed is *where* its remaining work is:
not in the `Shape` datatype (already fixed, 8 lines, in your tree), but in
`SExpr.lean`'s decorated judgment — `IsDefEq.strong`, a `sorry` whose own
docstring calls it false as stated, standing on a ~680-line analogue.

If you want one decision out of this memo: **authorise the `Shape.hasType`
lemma-layer follow-through (it is already half-applied and cheap), and
immediately re-point the stream at `SExpr.IsDefEq.strong` — including a
deliberate check, before any proof effort, of whether the repaired statement is
true.** On this project that check has paid off four times
(`PLAN.md:375–388`).
