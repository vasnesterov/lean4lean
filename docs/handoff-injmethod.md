# handoff-injmethod — a method for the two Injectivity holes

Target: `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified` and `Lean4Lean.VEnv.WF.rigidShapeUniqNS`
(both `Lean4Lean/Theory/Typing/Injectivity.lean`, both `[propext, sorryAx, Quot.sound]`).
Owned files: `Lean4Lean/Theory/Typing/InjMethod.lean`, this doc. `Injectivity.lean` is read-only
for this stream; any discharge is proved in `InjMethod.lean` and the exact edit is *stated*, not made.

Opened 2026-09-04.

---

## §1 — Weighing the three method classes, and the priors (written before any Lean measurement; NEVER EDITED)

### §1.0 What the two statements actually say

`RigidShapeUniqNS env U` (Injectivity.lean:1002) is, unfolded:

    ∀ Γ e T s₁ s₂, OnCtx Γ (env.IsType U) → ¬ env.IsProof U Γ e →
      s₁.RuleFree env → s₂.RuleFree env → ¬ s₁.BothSort s₂ →
      env.IsDefEq U Γ e s₁.toExpr T → env.IsDefEq U Γ e s₂.toExpr T →
      s₁.Compat env U Γ s₂

`RigidShape` has three constructors (`sort`, `pi`, `app`), so `Compat` is a 3×3 table. Its
`app`/`app` entry is visible at Injectivity.lean:960 and is *positive* (`c = c' → levels and
args agree`); the `sort`/`sort` entry has been factored out by `¬ BothSort`. **The
crucial structural observation, which drives everything below: the table's six remaining
entries split into two kinds.**

* **Positive entries** — `pi`/`pi` and `app`/`app`. Their conclusion asserts that certain
  conversions *hold* (`IsDefEq U Γ A A' (.sort u)`, `List.Forall₂ (env.IsDefEqU U Γ)`). To
  prove one you must **produce a conversion derivation**.
* **Negative (disjointness) entries** — `sort`/`pi`, `pi`/`sort`, `sort`/`app`, `app`/`sort`,
  `pi`/`app`, `app`/`pi`. I predict these are literally `False`, i.e. the claim is that a
  well-typed non-proof is never convertible with two *differently shaped* rigid terms. To
  prove one you must **refute a conversion**.

That split is the axis along which I weigh the classes, because the three classes have
opposite competences on the two kinds. **This axis has not appeared in any previous round's
framing**, which is my reason for thinking there is something left to measure.

### §1.1 THREE SHAPE PRIORS (before any cost prior)

**S1 — does the target exist? (judged on the CONCLUSION HEAD, not the obligation's name.)**
The conclusion head of `WF.rigidShapeUniqNS` is `RigidShapeUniqNS env U`, i.e. ultimately
`RigidShape.Compat env U Γ s₂`, under the hypothesis `VEnv.WF env` and *the shape-level side
condition `s₁.RuleFree env`, `s₂.RuleFree env`*.

`RuleFree` exists because of `RuleFreeHead` (Injectivity.lean:165): *no `defeq` of the
environment has a left-hand side headed by `c`*. The file is explicit (§"Why (B) carries two
side conditions") that without it "a constant whose value is a constant function identifies
all its arguments", and that this is machine-checked in `ConstInvWitness.lean` as a
regression test. **So the file already knows that rogue environment `defeqs` break injectivity,
and guards against them — for the `app` shape.**

`RuleFree` is a predicate on a `RigidShape`. `RigidShape.app c ls as` carries a constant name,
so its `RuleFree` clause has something to say. **`RigidShape.sort u` and `RigidShape.pi A B`
carry no constant name, so their `RuleFree` clause has nothing to say and is almost certainly
`True`.** But `VEnv`'s `defeqs` field is a set of `VDefEq`s, and if `VEnv.WF` /
`Ordered` constrains a `defeq` only by *"both sides are well-typed at a common type"* — with no
requirement that `lhs` be headed by a constant — then nothing stops a well-formed environment
from declaring

    lhs = .sort .zero,  rhs = .forallE (.sort .zero) (.sort .zero),  type = .sort (.succ .zero)

both sides being types at `Sort 1`. That environment makes `Sort 0` convertible with a Π, and
the `sort`/`pi` entry of `Compat` — which I predict is `False` — then makes
`RigidShapeUniqNS` **outright false**, with `VEnv.WF` satisfied. No independence argument, no
model: just build the env and derive `False`.

This is *exactly* the failure mode the method rules name — "a decisive claim graded 'unproved,
not false' was actually **unprovable as stated** because it omitted a hypothesis every neighbour
carried". Every neighbour in this family (`const_app_inv`, `const_forallE_inv`,
`const_sort_inv`) carries a `RuleFreeHead`-flavoured guard. `rigidShapeUniqNS` carries one only
*through the shapes*, and two of its three shapes cannot express it.

> **Prior S1.** P(`Ordered`/`VEnv.WF` constrains `defeqs` only by "both sides typecheck at a
> common type", with no constant-head condition on `lhs`) = **0.60**.
> P(`RigidShape.RuleFree` is `True` on both `.sort` and `.pi`) = **0.70**.
> P(the heterogeneous entries of `Compat` are `False`) = **0.85**.
> Joint ⇒ P(a rogue-`defeq` refutation of `WF.rigidShapeUniqNS` is available) ≈ **0.36**.
> P(the same attack refutes `forallE_inv_stratified`) = **0.15** — much lower, because there the
> conclusion is *positive* (`∃ u, IsDefEq Γ A A' (.sort u)`), so refuting it needs an
> independence/model argument on top of the rogue env, not just `False`.

**S2 — is the work in the direction I think?** My direction is: *attack, not prove.* Prior work
(four rounds) pushed on producing the positive entries. If S1 holds, the correct direction is
the opposite one and the deliverable is a refutation plus a *statement repair* (the hypothesis
`rigidShapeUniqNS` should have carried).
Risk: the tree may already have measured this. `Theory/Typing/InjPiRogue.lean` exists, and its
name reads as exactly "rogue environment vs Π-injectivity". Also present:
`DefInvRefute.lean`, `AppUniqRefute.lean`, `DescendRefute.lean`, `ParRedPropRefute.lean`,
`SubstCRefute.lean`, `SubstTRefute.lean` — refutation is an established local genre.

> **Prior S2.** P(`InjPiRogue.lean` already runs a rogue-`defeq` attack on this family) = **0.75**.
> P(it concludes the attack *fails* against `rigidShapeUniqNS` specifically, e.g. because
> `Ordered` does constrain `lhs`) = **0.45**. If it concludes failure, prior S1 is dead and I
> fall to §1.2(b). **This is the first thing I measure.**

**S3 — measurement, or docstring?** Two decisive-sounding claims in the target file are, I
predict, prose:
* `RigidShapeUniq`'s docstring: "See the section docstring for what discharges this
  (confluence, via `IsDefEq.church_rosser`)". Given the orchestrator's point 3 (`KStep.defeq`
  is itself tainted by `forallE_inv_stratified`), this citation is either non-existent or
  circular. **P(prose or circular) = 0.80.**
* `forallE_inv_stratified`'s docstring bullets are *self-flagged* as prose ("analysis of the
  induction, not a machine-checked impossibility") — good practice, and it means its claim
  "not provable by induction on the conversion derivation in isolation" is **not** measured and
  must not be quoted as if it were.
* Third: the docstring of `RigidShapeUniqNS`'s section asserts the eight non-`sort`/`sort`
  entries "do **not** follow from `SortUniq`", citing `UnivDiscrim.lean` "machine-checked
  there". **P(that one is genuinely machine-checked) = 0.7** — it is the one claim in the
  neighbourhood that names a witness file and a specific witness.

**S4 — what does the implementation compare with?** **Moot.** There are no `@[extern]`,
`opaque` or `partial` functions anywhere in `Theory/`; this layer is abstract `VExpr`/`VLevel`
mathematics and a hole-free neighbour in the same file has axiom set `[propext]` alone. The
2026-09-04 `CLAUDE.md` corollary about restating obligations around upstream opacity therefore
has no purchase here, and there is nothing to restate *around*.

### §1.2 The three classes, weighed

**(a) A normalisation / standardisation argument built from scratch.**
The honest obstruction is not cost, it is *contention plus circularity*. Circularity: every
K⁺ step in the tree consumes `forallE_inv_stratified` through `KStep.defeq`, so the existing
relation is unusable. The escape that would work in principle is well known — do confluence on
**untyped** `VExpr` (Tait–Martin-Löf parallel reduction; no typing premises, hence no
inversion, hence no circle), then bridge `IsDefEq → untyped conversion`. The bridge is where
all the content is, and it *cannot* be clean, because `IsDefEq` contains `proofIrrel`: two
distinct proofs of one Prop are convertible and are not untyped-convertible. That is precisely
why the target carries `¬ IsProof`. Contention: three streams are live on
`CParRedK.lean`/`TrianglePort.lean` right now (`git status`), i.e. on this very bridge.
Duplicating them is the worst available use of this round.
*Abandon if:* nothing — I am not starting here.

**(b) A model-theoretic argument.** I claim, and will prove, that this class has a **hard
competence boundary that exactly matches the split in §1.0**, and that the boundary explains
the one failure already on record.

A model is a soundness statement: an interpretation `I` with
`env.IsDefEq U Γ e₁ e₂ T → I Γ e₁ = I Γ e₂`. Contrapositively it yields
`I Γ e₁ ≠ I Γ e₂ → ¬ env.IsDefEq U Γ e₁ e₂ T`. So a soundness-only argument
**decides negative conversion facts and cannot decide a single positive one.** To get a
positive conversion out of a model you need *completeness* — `I Γ e₁ = I Γ e₂ → IsDefEq …` —
which is not a property of the ZFC/inaccessibles model at all (its Π is set-theoretic function
space, which is *not* injective: `∀ x : Empty, B` is the one-element set of empty functions for
every `B`, so `⟦∀x:Empty,B⟧ = ⟦∀x:Empty,B'⟧` while `B ≢ B'`), and which in general is the
decidability-of-conversion problem, i.e. strictly harder than the target.

Consequences, which is why I rate this class high *as a source of a negative result*:
1. Class (b) can, in principle, deliver the **six disjointness entries** of `Compat` and
   **none** of the positive ones. That is a genuine split of one hole into a theorem plus a
   narrower hole.
2. It **retro-explains the round-2 failure**: `PropAgreeOn`'s conclusion "cannot deliver
   `SortUniq`" (`SortInvIndep.lean`:493), and `SortUniq`'s conclusion `u ≈ v` is *positive*.
   The prop-agreement ingredient was not unluckily weak — it was on the wrong side of this
   boundary, and so is every other soundness-only ingredient. **P(this reading is right) = 0.8.**
   If right, "the prop-agreement route was model-flavoured and failed" stops being a caution
   about class (b) and becomes an *instance of a theorem about* class (b) — and the caution in
   my instructions is answered rather than ignored.
*Abandon if:* the tree already contains this boundary result (check `PropAgreeWall.lean`,
`NotProofNoModel.lean`), or `Interp`'s soundness turns out to be an `Iff`.

**(c) A refutation.** Cheap, decisive, and §1.1/S1 hands me a *specific named candidate* rather
than a search. Note that (b) and (c) are the **same technique aimed in opposite directions**:
(b) proves a disjointness entry by exhibiting a model that separates the shapes; (c) refutes one
by exhibiting a `VEnv.WF` environment that identifies them. Exactly one of the two can succeed
on the `sort`/`pi` entry, and *which one* is decided by a single question — does `Ordered`
constrain a `defeq`'s left-hand side? So the first measurement discriminates both classes at
once. That is the cheapest informative experiment available, and it is why I order it first.

### §1.3 Decision

**Primary: (c), with (b)'s competence boundary as the guaranteed deliverable.** Reason: the two
share their first measurement, the measurement is cheap and decisive for both, and each has a
publishable outcome whichever way it falls — if `Ordered` is permissive, `rigidShapeUniqNS` is
*false as stated* and the deliverable is a refutation plus the exact hypothesis repair; if
`Ordered` is restrictive, the deliverable is the class-(b) boundary theorem, which converts the
one recorded ingredient-failure into a theorem about a whole method class and splits the hole
along the §1.0 axis.

**Explicitly not attempted: (a).** Stated so it cannot be read as an oversight.

**I abandon (c) the moment** `Ordered`'s `defeqs` clause is shown to require a constant-headed
`lhs`, or `InjPiRogue.lean` is shown to have run and failed this attack. **I abandon (b) the
moment** `Interp`'s soundness is found to be an equivalence, or `PropAgreeWall.lean` is found to
contain the boundary result already.

---

## §2 — Measurements (append-only; each entry appended the moment it lands, before the next tool call)

### M1 (2026-09-04) — `Ordered` does **not** constrain a `defeq`'s left-hand side. Prior S1a scores TRUE.

`Lemmas.lean:258`: `| defeq : Ordered env → df.WF env → Ordered (env.addDefEq df)`. `df.WF env`
asks only that both sides be typed at `df.type` in the **empty context**. There is no
constant-head condition, no `RuleFreeHead`, nothing. So a well-formed environment may declare
a definitional equation between *any* two closed terms that share a type.

**Prior S1a (P = 0.60): TRUE.** Prior S2a (P = 0.75, that `InjPiRogue.lean` already runs a
rogue-`defeq` attack): **TRUE**, and better than predicted — it does not merely run the attack,
it *leaves the environment behind*, `Ordered`-proved and `sorryAx`-free:

    roguePiEnv : one constant C : Sort 1, plus TWO defeqs
      rogueDf1 : C ≡ ∀ (_ : Prop), Prop                 at Sort 1
      rogueDf2 : C ≡ ∀ (_ : Prop), ∀ (_ : Prop), Prop   at Sort 1
    ordered_roguePiEnv : Ordered roguePiEnv   -- sorryAx-free

Prior S2b (P = 0.45, that it concludes the attack *fails*): **FALSE** — it concludes the
opposite, that `InjChainLower.lean`'s `[analysis]` claim of "no rogue-environment refutation …
is available by this idiom" **does not hold up on the Π-side entries**, and refutes
`ConvPiFromEntry` at `roguePiEnv`. So the idiom is live, and the recorded barrier against it was
prose that was *wrong*. (S3's genre-level prediction, that decisive claims here are prose,
scores on a claim I had not even nominated.)

**But its target was `ConvPiFromEntry`, not either of my two.** So the environment is available
and the two targets are unmeasured against it. The remaining questions for a refutation of
`WF.rigidShapeUniqNS` are exactly S1b and S1c: is `RigidShape.RuleFree` vacuous on `.sort`/`.pi`,
and is the heterogeneous entry of `Compat` `False`.

### M2 (2026-09-04) — S1b and S1c both score TRUE. The refutation is available in principle, and collapses to ONE question.

`Injectivity.lean:932` — `RigidShape.RuleFree`:

    | .sort _ => True
    | .pi _ _ => True
    | .app c _ _ => env.RuleFreeHead c

**Prior S1b (P = 0.70): TRUE.** The guard is vacuous on two of the three shapes, exactly as
predicted. The docstring even says so out loud — "Only the application spine has one" — and
treats that as a *feature* ("the `RuleFreeHead` the const-family already takes"), where in fact
it is the gap: the const family needs the guard because a rogue δ-rule reduces a spine to
anything; a rogue δ-rule reduces a *constant* to anything too, and then the `sort` and `pi`
shapes on the **other** side of `Compat` are reached with no guard in force at all.

`Injectivity.lean:949` — `RigidShape.Compat`: all **six** off-diagonal entries are literally
`False`. **Prior S1c (P = 0.85): TRUE.**

So `WF.rigidShapeUniqNS`, instantiated at any environment carrying one constant `C` with two
definitional equations

    C ≡ .sort .zero                                    at .sort (.succ .zero)
    C ≡ .forallE (.sort .zero) (.sort .zero)           at .sort (.succ .zero)

at `Γ = []`, `e = C`, `T = .sort (.succ .zero)`, `s₁ = .sort .zero`,
`s₂ = .pi (.sort .zero) (.sort .zero)`, concludes `False`. Its five side conditions are all free:
`OnCtx [] _` is `trivial`; both `RuleFree`s are `trivial`; `¬ BothSort` is `not_false`; and
`¬ IsProof` is `not_isProof_of_defeqU_sort` (Injectivity.lean:1030), a `sorryAx`-free theorem of
the target file itself, applied to the first link. **Nothing is left but one question:**

> **Is such an environment `VEnv.WF`?** `InjPiRogue.lean` proves its cousin only `Ordered`, and
> says so pointedly — "Every reduction … carries `Ordered env` **and nothing stronger**. At that
> strength the statement is false". `WF.rigidShapeUniqNS` takes `VEnv.WF env`. If `VEnv.WF` is
> `Ordered` plus nothing that excludes a non-constant-headed or duplicated `defeq`, the hole is
> **false as stated**. If `VEnv.WF` excludes it, class (c) dies here and I fall to (b).

### M3 (2026-09-04) — `VEnv.WF` is *declaration-history* strength, and that kills the outright refutation while handing me a sharper target.

`Env.lean:136`: `def VEnv.WF (env : VEnv) : Prop := ∃ ds, VEnv.WF' ds env`, with `VEnv.WF'`
(`Env.lean:132`) an inductive over a list of `VDecl` steps. So `VEnv.WF env` means **"env was
built by a legal declaration sequence"** — strictly stronger than `Ordered env`
(`VEnv.WF.ordered`, `EnvLemmas.lean:134`, is the one-way implication and there is no converse).

Consequence for class (c). Every `VDecl.WF` rule that adds a `defeq` adds **one defeq per new
constant name**:

* `| def : ci.WF env → env.addConst ci.name ci.toVConstant = some env' → VDecl.WF env (.def ci) (env'.addDefEq ci.toDefEq)`
* `| unsafeDef : … → env.addConsts cis = some env' → … → VDecl.WF env (.unsafeDef cis) (env'.addDefEqs cis)`
  with `addConsts = cis.foldlM (·.addConst ·)` and `addDefEqs = cis.foldl (·.addDefEq ·)`.

`addConst` is `Option`-valued and (to be confirmed, M4) fails on a name already present, so the
names in a block are distinct and **the δ-rule set of a `VEnv.WF` environment is left-linear and
non-overlapping: at most one rule per constant head.** ι-rules likewise (distinct constructors),
and β/η are the standard confluent pair. So the rogue idiom — *two* rules on *one* constant,
which is what `roguePiEnv` uses and what `Ordered` permits — **is not reachable inside
`VEnv.WF`**, and I now expect `WF.rigidShapeUniqNS` to be **true**.

**Prior S1's joint prediction (P ≈ 0.36 that an outright refutation is available): FALSE, and
for a reason none of its three components saw.** All three components scored TRUE and the
conjunction still fails, because I had not asked the fourth question — *is `VEnv.WF` `Ordered`?*
Recording that as the round's methodological miss: I priced the three hypotheses the statement
displays and not the one it inherits.

**The pivot, and it is worth more than the refutation would have been.** The gap between
`Ordered` and `VEnv.WF` is now the whole content of the target, and it is *measurable*:

> **Claim R (to prove).** `¬ ∀ env U, Ordered env → env.RigidShapeUniqNS U`.

If Claim R holds, then **every proof attempt that carries only `Ordered env` is provably doomed**,
no matter how much confluence machinery it builds — and `InjPiRogue.lean` states that the
neighbouring reduction files carry exactly that: "Every reduction in `InjMidLocal.lean`,
`InjChainLower.lean` and `InjPiInhab.lean` carries `Ordered env` **and nothing stronger**." That
makes Claim R a **negative result about the method class four rounds have been inside**, plus a
positive instruction for the next round: the proof must consume `WF'`'s declaration history,
specifically δ-rule non-overlap, and no amount of `Ordered`-level rewriting theory can substitute.
Claim R needs the `sort`/`pi` entry (conclusion literally `False`), so unlike `InjPiRogue`'s
`pi`/`pi` refutation it needs **no independence argument** — only an `Ordered` env with
`C ≡ .sort .zero` and `C ≡ .forallE (.sort .zero) (.sort .zero)`, plus `¬ IsProof [] C`.

### M4 (2026-09-04) — M3's mechanism confirmed; and Claim R hits a wall that is itself informative.

`VEnv.addConst` (`VEnv.lean:27`) is `match env.constants name with | some _ => none | none => …`
— it **does** fail on a name already present. So M3's reasoning stands: a `VEnv.WF` environment
has at most one δ-rule per constant head. The tree already names that property —
`VEnv.DefEqHeadsUnique`, extracted from the history by `WF'.defEqHeads`
(`Theory/Typing/DeltaUnique.lean`) — and `InjPiRogue.lean` §8 already proves both
`not_defEqHeadsUnique_roguePiEnv` and `not_wf_roguePiEnv : ¬ VEnv.WF roguePiEnv`, machine-checked.
So the `Ordered`/`VEnv.WF` gap is known *in this exact form*; what is not done is drawing the
consequence for the two target holes.

**And Claim R does not come free.** `IsProof` (Injectivity.lean:699) is
`∃ p, HasType U Γ p (.sort .zero) ∧ HasType U Γ e p`, and the target's `¬ IsProof` premise must
be *supplied* by a refuter. The only routes in the tree to `¬ IsProof` at a sort or a Π —
`sort_not_proof`, `forallE_not_proof` (`NotProof.lean:63`), `not_isProof_of_sort'`,
`IsType.not_isProof` — every one of them takes `env.SortUniq U`, i.e. **universe uniqueness**,
which is the *other* face of the very hole being attacked. Discharging `¬ IsProof` at a rogue
environment therefore needs `SortUniq` *at that environment*, and `SortUniq` is a statement about
all of conversion, not a finite check.

Note the pleasing symmetry, and it is the §1.0 axis again: `¬ IsProof` is a **negative**
statement (`¬∃`). A model can decide it. `SortUniq` is a **positive** one (`u ≈ v`). A model
cannot. So the honest cheapest route to Claim R is a bespoke model of the rogue environment —
which is class (b) used *within* class (c), at exactly the boundary §1.2(b) predicted.

Simplification worth recording for whoever picks Claim R up: **no constant is needed.**
`Ordered.defeq` asks only `df.WF env`, and

    df := ⟨0, .sort .zero, .forallE (.sort .zero) (.sort .zero), .sort (.succ .zero)⟩

satisfies it over `VEnv.empty` — `Prop : Sort 1` by `HasType.sort`, and
`∀ (_ : Prop), Prop : Sort (imax 1 1) = Sort 1`. So `VEnv.empty.addDefEq df` is `Ordered`,
makes `Prop` convertible with a Π, and needs neither `rogueC` nor `InjPiRogue`'s two-rule idiom.
That is a smaller witness than `roguePiEnv` and it targets the `sort`/`pi` entry, whose `Compat`
value is literally `False`. Everything but `¬ IsProof env 0 [] (.sort .zero)` is then `trivial`.

### M5 (2026-09-04) — `InjPiRogue.lean` has already walked most of Claim R, and it reports the wall I just hit, plus one I had not priced.

Read in full. Its Round-2 section retires its own `[analysis]` flag with two machine-checked
theorems (`not_defEqHeadsUnique_roguePiEnv`, `not_wf_roguePiEnv`) and states the operational
conclusion I was about to re-derive:

> "**Stop pointing proof attempts at `ConvPiFromEntry` over `Ordered env`.** Any proof must
> consume `VEnv.WF`, and §7 names exactly which clause of it."

**So Claim R's *conclusion* is already on record for the neighbouring statement, and my M3 pivot
is not new.** Class (c) is now dead on both aims: outright refutation blocked by `VEnv.WF`
(M3/M4), `Ordered`-strength refutation already delivered next door. **Abandoning (c)** on the
condition §1.3 set out ("the moment `InjPiRogue.lean` is shown to have run this attack").

Three further facts from it that reprice class (b) — and one of them is against me:

1. **`RigidNodeCircle.rigidShapeUniqNS_iff_family` decomposes `WF.rigidShapeUniqNS` into five
   conjuncts, and they split exactly three-negative / two-positive**: `RigidSortPiDisj`,
   `RigidConstPiDisj`, `RigidConstSortDisj` (negative) against Π-injectivity and const-app
   injectivity (positive). **§1.0's axis is real and is already the tree's own decomposition.**
   That is the one prediction of mine that was structurally right and independently confirmed.
2. **`InjSortPiModel.interp_sort_ne_interp_forallE` proves the *semantic* residual of
   `RigidSortPiDisj` outright** — "the packaging is what collapses there, not the content". So
   class (b) *does* reach a negative conjunct semantically, exactly as §1.2(b) predicted…
3. **…but `InjSortPiModel.lean` items 2–3 record that the model route to those conjuncts is
   *circular* (`RigidSortPiDisj`) or *refuted* (`RigidConstPiDisj`, `RigidConstSortDisj`), and
   `Theory/SetModel/` carries `sorry` in nine files including `Interp.lean` and
   `InterpSound.lean`.** This is the fact §1.2(b) did not price: I predicted the class's
   *competence* boundary correctly and ignored whether the class's *machinery* is available.
   `sorry` in `InterpSound.lean` means the soundness arrow itself is not in hand.

Also recorded there, and it is the sharpest single sentence in the neighbourhood: any syntactic
separation "must survive `IsDefEqStrong.beta`, which can turn an application into a Π
(`.app (.lam _ (.bvar 0)) (∀ (_ : Prop), Prop) ≡ ∀ (_ : Prop), Prop`), so a head- or
occurrence-counting invariant cannot be β-stable: separating two terms here is a normalisation
or model obligation, not a syntactic one."

**Prior S3 scores TRUE but on the wrong claim.** I nominated `RigidShapeUniq`'s "confluence, via
`IsDefEq.church_rosser`" docstring (P = 0.80 prose-or-circular). Not yet checked. What actually
fell to the prose test was `InjChainLower.lean`'s `[analysis]` — "no rogue-environment refutation
… is available by this idiom" — which `InjPiRogue.lean` shows is **false**, and
`InjPiRogue.lean`'s own first-round `[analysis]` flag, which was **true but redundant**. Two for
two on the genre; zero for one on the specific nomination.

### M6 (2026-09-04) — class (b) is measured-dead, and §1.2(b)'s "new" principle was already the tree's, written 2026-08-31.

`Theory/Typing/InjSortPiModel.lean` (582 lines) opens with **exactly** the argument §1.2(b) sets
out as my contribution:

> "The faithfulness gap is what kills `PiInv`, and it kills every *positive* conjunct: soundness
> maps derivations to denotational facts, never back. But a **disjointness** conjunct is
> negative: it says a conversion does *not* exist. For those, soundness alone is the right tool
> … No faithfulness is involved, because the derivation is a *hypothesis*, not a conclusion."

**So §1.2(b)'s competence boundary — my primary intended deliverable, and the thing I rated
P = 0.8 and thought would "answer rather than ignore" the caution in my instructions — is
prior art, five days old.** It is also *better* than my version: it is applied conjunct by
conjunct and it produces a verdict I did not predict. The measured table:

| conjunct | polarity | semantic status |
|---|---|---|
| `PiInv` | positive | dead (faithfulness; domain half separately refuted, `not_forallPropDomInj`) |
| `RigidConstAppInv` | positive | dead (faithfulness) |
| `RigidSortPiDisj` | negative | residual **proved** (`interp_sort_ne_interp_forallE`); packaging collapses |
| `RigidConstPiDisj` | negative | **dead** (`not_coherentConstNotPi`) |
| `RigidConstSortDisj` | negative | **dead** (`not_coherentConstNotUniv`) |

"**The semantic tally for the second hole is therefore 1 usable conjunct of 5, permanently.**"
So the polarity split does *not* buy the three negative conjuncts as §1.2(b) hoped — two of the
three die because `CoherentOn.const_type` constrains `M.cnst c us` **by membership in
`⟦ci.type⟧` and by nothing else**, and both target shapes live inside a declared type; and the
refuted guard is *stronger* than what the conjuncts supply, so no weakening rescues them.

**Abandoning (b)** on §1.3's stated condition, which fires twice over: the boundary result is
already in the tree, and `Theory/SetModel/` carries `sorry` in nine files including
`InterpSound.lean`, so the soundness arrow is not even in hand.

Two live details worth carrying forward, because they are the only things in this file that are
*not* verdicts:

* **The `Above` threshold.** `SetModel.sound`'s chain threshold "is produced *by the derivation*,
  so a chain long enough to use it can only be picked after the derivation is in hand." That is a
  quantifier-order problem, not a falsity — and quantifier-order problems are sometimes repairable.
* **The empty-context valuation obligation (item 4).** `interpCtx_vFalse`: for
  `Γ = [∀ p : Prop, p]` — legitimate over every environment — `interpCtx M L Γ` is **empty**, in
  every model and on both branches. `Sound.eq` quantifies over `ρ ∈ interpCtx M L Γ`, so in a
  context containing an empty type the model says **nothing at all**, and that is why even the
  proved residual cannot be packaged. This is a real limitation of every soundness model and not
  an artefact: it is why "1 of 5, permanently" is permanent.

**Score for §1's decision.** Both classes I chose in §1.3 are closed by prior work that §1 did
not know about, and my abandonment conditions fired as written rather than being argued around.
The three shape priors S1a/S1b/S1c all scored TRUE and the decision built on them was still
wrong, because §1 priced the hypotheses the statement *displays* and not the one it *inherits*
(`VEnv.WF` vs `Ordered`, M3) nor whether the chosen class's *machinery* exists (M6). Those are
the two questions a fifth round should add to the prior list.

### M7 (2026-09-04) — **The circularity is not vicious. The reference builds it deliberately and breaks it with the alternation index. My instructions' point 3 has it wrong.**

`~/lean-type-theory/unique.tex`, read in full down to §church_rosser. Its §1 says, in as many
words:

> "Unfortunately, we cannot yet prove this theorem. The critical step is the Church-Rosser
> theorem … **However, we can set up the induction, which is necessary now since the
> Church-Rosser theorem will require that this theorem is true, and we will be caught in a
> circularity unless we are careful about the claims.**"

So the dependency "confluence needs unique typing needs Π-inversion" is **known to the
reference, designed for, and defeated** — by stratifying on *the number of alternations between
the typing and the conversion judgment*. Define `⊢_n` (unique.tex §1):

* `Γ ⊢₀ α ≡ β` iff `α = β`;
* `Γ ⊢_{n+1} α ≡ β` iff `Γ ⊢ α ≡ β` has a proof using only `⊢_n` typing judgements;
* `Γ ⊢_n e : α` iff `Γ ⊢ e : α` has a proof whose every conversion appeal is `⊢_m` for `m ≤ n`.

"**Definitional inversion** for `⊢_n`" is then exactly our two holes, indexed: (1) sort levels
agree, (2) Π domains and codomains convert, (3) `Γ ⊢_n U_ℓ ≢ ∀x:α.β`. The four arrows are:

    (i)   DInv 0                        -- unique.tex thm:0dinv. TRIVIAL: ⊢₀ is syntactic equality.
    (ii)  DInv n  →  UType n            -- unique.tex thm:utype.
    (iii) UType n →  CR (n+1)           -- unique.tex §kappa + §church_rosser.
    (iv)  CR (n+1) →  DInv (n+1)        -- unique.tex thm:1dinv.
    then  (∀ n, DInv n) → DInv           -- unique.tex "n-provability basics" (3),(4).

Induction on `n` closes it: `DInv 0 → UType 0 → CR 1 → DInv 1 → UType 1 → CR 2 → …`. **Every
step of the confluence development is licensed to consume inversion — one index down.** §kappa's
own note says so: "*we will assume that `⊢_n` has unique typing, which will prevent the
appearance of certain pathologies*."

**Consequence for my instructions.** Point 3 says `CRShape.lean` "measured" that
`VEnv.KStep.defeq` is already tainted by `forallE_inv_stratified`, "so **every K⁺ step consumes
it**", and concludes "**you may not use confluence, Church–Rosser, or anything downstream of
them.**" The measurement is presumably right and the conclusion does not follow. A K⁺ step
consuming Π-inversion is not a circle — it is arrow (iii), exactly as designed. It is a circle
only if the inversion it consumes is at the **same or unbounded** index as the one being proved.
The taint is a symptom of the tree consuming the *global* `sorry`-backed
`forallE_inv_stratified` where it should consume a *hypothesis* `PiInvStrat`-at-`n`, and
`Injectivity.lean` already prescribes that discipline for a neighbour: "Anything that wants to
state a result about the `RigidShapeBridge` family without inheriting that taint has to take this
as a hypothesis instead — the same discipline `PiLevelPin.lean` uses for `SortUniq`."

**And the tree is already built for this.** The target's own statement is *already indexed* —
`h2 : HasTypeStratified U Γ (.forallE A B) V true n`, `h3 : … n'` — which is why it is called
`forallE_inv_**stratified**` and why the `sorry` was narrowed onto it rather than onto plain
`forallE_inv`. `Injectivity.lean`'s `UniqAux` section is arrow (ii) already built
(`piInvStrat_of`, `uniqQ`, `WF.sortUniq'`), and it names its own blocker in the language of the
index: "**Inside `uniqQ` only bounded instances of `SortUniq` are available, so the circle does
not close.**" That sentence is the diagnosis and the cure at once — the circle does not close
*because the conclusion is not one index up*. Arrow (iii)'s conclusion must be at `n+1`.

**Prior S3 scores TRUE on its actual nomination after all**, and harder than predicted. The
docstring claim under test was "See the section docstring for what discharges this (confluence,
via `IsDefEq.church_rosser`)". It is not merely prose-or-circular: the *citation* is right and
the *reason it was disbelieved* is wrong. Confluence does discharge this; what nobody wrote down
is the index at which it is allowed to.

**Method class chosen from here (call it (a′), and it is not §1.2(a)):** not "build
standardisation from scratch" and not "borrow the tainted confluence", but **build the
index-stratified induction skeleton** — state the four arrows over `n`, prove the closure
induction and the (i)/(ii) arrows from what the tree has, and leave exactly one named residual,
arrow (iii) at a *bounded* hypothesis. That is a reduction and not a restatement, because the
hypothesis it needs (inversion at `n`) is available exactly where the current one (inversion,
unbounded) is not.

### M8 (2026-09-04) — M7's architecture is **already in the tree**, three of its four arrows sorry-free. The residual is one arrow, and it is `DefInv n → DefInv (n+1)`.

`Theory/Typing/UniqueTypingN.lean` is unique.tex §1 transcribed, and its own header cites the
theorem numbers:

* `def DefInv env U n` with projections `.sort`, `.forallE`, `.sort_forallE`, and the three
  standalone forms `SortInvN` (180), `SortForallEDisjN` (185), `ForallEInvN` (196), plus
  `SubstC` (219) — **this is unique.tex's "definitional inversion for `⊢_n`", all three clauses.**
* **Arrow (i)** — `theorem DefInv.zero : env.DefInv U 0` (229), with `SortInvN.zero` (237),
  `SortForallEDisjN.zero` (240), `ForallEInvN.zero` (244), `SubstC.zero` (247). unique.tex
  thm:0dinv. **Done, and trivial as the reference says.**
* **Arrow (ii)** — `theorem HasTypeN.uniq (dinv : env.DefInv U n) (hs : env.SubstC U n)` (467)
  and `Stratified.uniq` (434). Header line 15: "`VEnv.Stratified.uniq` — **thm:utype**
  (`unique.tex:40`), **sorry-free** from those two." **Done.**
* **The closure to the unstratified holes** — `IsDefEqU.sort_inv_of_sortInvN` (519),
  `IsDefEqU.sort_forallE_inv_of_sortForallEDisjN` (533), and line 500 states the general shape:
  the statements "still `sorry` there — follow from definitional inversion **at every index** and
  nothing else". **Done, or at least stated.**

So (i), (ii) and the closure exist. **Arrow (iii)+(iv) — `DefInv n → DefInv (n+1)`, the
stratified Church–Rosser step, unique.tex §kappa/§church_rosser/thm:1dinv — is the whole
residual, and it is the *only* residual.** That is a materially different picture from the one my
instructions gave me ("you may not use confluence"): confluence is not forbidden, it is *the
single named remaining arrow*, and it is licensed to consume `DefInv n` while proving `DefInv (n+1)`.

This also re-reads the census honestly. Two holes in `Injectivity.lean` are not two independent
mathematical facts; they are the *unstratified shadows* of one inductive step that nobody has
been able to take. Which is exactly why every cheap producer turned out to be a restatement
(instruction point 1): restatements of the shadow cannot move the step.

### M9 (2026-09-04) — **CORRECTION TO M7. The reference's stratified induction is machine-checked BROKEN. My instructions' point 3 reaches the right conclusion by wrong reasoning; I reached the wrong conclusion by right reasoning.**

M7 claimed the index licenses arrow (iii) and therefore "confluence is not forbidden, it is the
single named remaining arrow". `UniqueTypingN.lean`'s own header refutes that, and it is the most
important thing in this round's reading. Quoting it:

* **`SubstC` is false.** unique.tex thm:utype's application case (`unique.tex:51`) ends "…so
  `Γ ⊢ₙ β[e₂/x] ≡ β'[e₂/x]`": it substitutes into a conversion and *keeps the index*.
  "**That step is false.**" `Theory/Typing/SubstCRefute.lean` machine-checks a counterexample at
  `n = 1` over the empty environment, and "every rule it relies on is one the reference states
  with the same premises". `SubstC` "**is not in the reference; it is a step the reference takes
  without justification**".
* **The counting argument says why it is structural, not accidental.** Substituting a `⊢ₘ`
  derivation into a `⊢ₙ` conversion splices the alternations, so the index is `m + n`
  (`Stratified.instN` proves exactly this bound). In thm:utype's application case `m = n`, so
  "the reference's step lands at `2n`, while its consumer thm:1dinv needs it at `n`". And
  "`DefInv` is neither monotone nor antitone in `n` … so a conclusion at `2n` cannot be repaired
  downstream."
* **Verdict, in the file's words: "The induction cannot pass `n = 1`."** `DefInv 0` → `uniq 0`
  (since `SubstC 0` holds) → `DefInv 1`; the next step needs `uniq 1`, and `SubstC 1` is false.
* **The goal is false too, not merely the step.** `Theory/Typing/DefInvRefute.lean`'s
  `defInv_all_false` refutes `∀ n, DefInv env U n` **over the empty environment**. That is why
  the surviving reductions were narrowed to clauses **(1) and (3)** of `DefInv` only.
* **§§3–4 fare no better.** The three further fixed-index substitutions there need `VEnv.SubstT`,
  "**and it is false as well** — at `n = 1`, at substitution depth 1, which is the depth
  `p_subst`'s and `gg_subst`'s inductions actually use". So "the plan 'restate §§3–4 over
  `IsDefEqN`' is not expensive transcription — **it has no proof at the index at all**."
* **The obvious repair is measured and rejected.** Adding `instC` as a `Stratified` rule costs
  exactly four cases and keeps `Stratified.lean` sorry-free — but "it does not survive
  downstream": thm:1dinv's induction gains a case needing `≡ᵏ` closed under instantiation by
  `⊢ₙ₊₁`-typed terms while `≡ₚ`/`↝ᵏ`'s side conditions sit at `⊢ₙ`, and pushing the rule down
  breaks thm:gg_compat and thm:tri, which are proved by *inversion*.

**So class (a′) — port the reference's index-stratified induction — is refuted in-tree, and this
is one of the "machine-checked refutations of results in the published reference" `CLAUDE.md`
mentions.** M7's architecture claim stands as a description of what the reference *intends*; its
claim that the residual is "one arrow, licensed by the index" is **withdrawn**. The index does
license the dependency in principle; what fails is that the index cannot be *preserved through
substitution*, which every arrow of the induction needs.

**Net on instruction point 3.** Its ban on confluence is *correct*, and my M7 objection to it was
wrong. But its stated reason — "the dependency is circular" — is not the reason, and the
distinction matters for the next round: the dependency is *stratifiable in principle and the
reference stratifies it*; what kills the route is that `SubstC`/`SubstT` are **false**, so the
stratification cannot be carried through substitution. A round told "the dependency is circular"
will go looking for a cleverer way to break the circle — which is what I did, and it is a dead
half-day. A round told "`SubstC` is false at `n = 1` and `∀ n, DefInv n` is false over `∅`" will
not. **Recommend point 3 be restated that way.**

**Score.** Four method classes, four measured verdicts, none of them mine:
(a) confluence — banned, and the only circle-breaking version is refuted (`SubstCRefute`,
`SubstTRefute`); (a′) port the reference — refuted, the reference has a false step;
(b) model — 1 usable conjunct of 5, permanently; (c) refutation — done next door at `Ordered`
strength, blocked at `VEnv.WF` strength.

### M10 (2026-09-04) — one live, explicitly-unrefuted target found, and it is on my hole. This is what I will build.

`UniqueTypingN.lean:180/185` and `DefInvRefute.lean:320/325` both mark clauses (1) and (3) of
`DefInv` as **open — "neither proved nor refuted"**, "Also not refuted", "Not refuted by anything
known". They are the two clauses the surviving reductions consume:

    SortInvN         env U n  :  IsDefEqN U n Γ (.sort u) (.sort v) → u ≈ v
    SortForallEDisjN env U n  :  ¬ IsDefEqN U n Γ (.sort u) (.forallE A B)

and `sort_inv_of_sortInvN` / `sort_forallE_inv_of_sortForallEDisjN` (`DefInvRefute.lean:340,348`)
carry them to the unstratified holes. `SortForallEDisjN` **is** `RigidSortPiDisj`, conjunct 3 of
the 5 that `RigidNodeCircle.rigidShapeUniqNS_iff_family` splits my second target into. Note it
carries **no `¬ IsProof` premise** — so the wall M4 hit does not apply to it.

Every refutation in `DefInvRefute.lean` is over the **empty** environment (`defInv_one_false`,
`defInv_all_false`, `defInv_forallE_right_false` — all `(∅ : VEnv)`, `U = 1`, `n = 1`), and over
`∅` clause (3) survives. So the environment axis has never been run against clause (3).

**What I will prove.** `SortForallEDisjN` is **not provable from `Ordered env` at any `n ≥ 1`**,
witnessed by a one-rule environment, together with the fact that the witness is not `VEnv.WF`.
Predicted shape:

    injEnv := VEnv.empty.addDefEq ⟨0, .sort .zero, .forallE (.sort .zero) (.sort .zero), .sort (.succ .zero)⟩
    ordered_injEnv            : Ordered injEnv
    not_sortForallEDisjN_one  : ¬ injEnv.SortForallEDisjN 0 1
    not_wf_injEnv             : ¬ VEnv.WF injEnv

**Why this is not `InjPiRogue.lean` again, and why it is sharper.** `roguePiEnv` needs **two**
δ-rules on **one constant**, so the `VEnv.WF` clause it pins is `DefEqHeadsUnique`
(rule-count uniqueness, `DeltaUnique.lean`). My witness has **one** rule and no constant at all:
its lhs is `.sort .zero`. So the clause it pins is `VEnv.RuleShape.delta` — *a δ-rule's lhs is
`.const ci.name _`* — which is **logically prior** to rule-count uniqueness. Consequence, if it
lands: the received summary "any proof must consume `VEnv.WF`, and the clause is that a
`VEnv.WF` environment cannot carry two δ-rules for one constant" is *one clause too weak*. **One
rule is enough to break clause (3), if its head is not a constant.** And it lands on conjunct 3
of the target hole rather than on a neighbour.

Expected value if it lands: no census movement (it is a negative result, not a discharge), one
named `VEnv.WF` clause that every future attempt on `RigidSortPiDisj` must consume, and the
first refutation in the tree that is about clause (3) at all.


---

## §3 — What landed (2026-09-04)

`Lean4Lean/Theory/Typing/InjMethod.lean`, new, 150 lines, builds clean with **no warnings**.
Full bare `lake build`: **1667 jobs, "Build completed successfully"**. Guards on the same build:
`guard 1: Axioms.lean declares exactly the 24 frozen axioms ✓`,
`guard 2: kernel_sound axioms within whitelist ✓ (proof INCOMPLETE: sorryAx present)`,
`guard 3: checker cone implementation gaps within frozen list (2/2 remaining) ✓`.
**Census unchanged at 13** — this round discharges nothing, by design; it is a negative result.
`Injectivity.lean` was not edited, and I request no edit to it or to any frozen file.

### The theorem

**Clause (3) of definitional inversion is not provable from `Ordered env`, and one rule is
enough to break it.** All statements `sorryAx`-free.

| name | arity | axioms |
|---|---|---|
| `InjMethod.ordered_injEnv` | 0 | `[propext, Quot.sound]` |
| `InjMethod.rogue_link` | 0 | `[propext, Quot.sound]` |
| `InjMethod.not_sortForallEDisjN` | 1 (`1 ≤ n`) | `[propext, Quot.sound]` |
| `InjMethod.not_sortForallEDisjN_one` | 0 | `[propext, Quot.sound]` |
| `InjMethod.not_sortForallEDisjN_of_ordered` | 0 | `[propext, Quot.sound]` |
| `InjMethod.not_defInv` | 1 (`1 ≤ n`) | `[propext, Quot.sound]` |
| `InjMethod.ruleShape_lhs_ne_sort` | 2, **both load-bearing** (`lean_minimal_hypotheses`) | `[propext, Quot.sound]` |
| `InjMethod.not_wf_injEnv` | 0 | `[propext, Classical.choice, Quot.sound]` |

**Cone figures are deliberately omitted.** I wrote two independent transitive-dependency counters
and both returned the *same internally inconsistent* readings — `not_sortForallEDisjN_one` (which
is literally `not_sortForallEDisjN (Nat.le_refl 1)`) measured **smaller** than
`not_sortForallEDisjN`, which is impossible. Rather than quote numbers I cannot validate, I
report none and flag the tooling gap: **this tree has no trustworthy cone counter that I could
find, and several docs quote cone figures (3529, 588, 47) whose provenance a fifth round should
check before relying on them.**

### The witness

    rogueDf := ⟨0, .sort .zero, .forallE (.sort .zero) (.sort .zero), .sort (.succ .zero)⟩
    injEnv  := (∅ : VEnv).addDefEq rogueDf          -- one rule, ZERO constants

`Ordered.defeq` asks only `df.WF env` = both sides typed at `df.type` in the empty context.
`Prop : Sort 1` by `HasType.sort`; `∀ (_ : Prop), Prop : Sort (imax 1 1)`, converted to `Sort 1`
by `imax_equiv`. `Stratified.extra` at `n = 0` yields a `⊢₁` conversion `Prop ≡ ∀ (_ : Prop), Prop`
in **every** context, which is exactly what clause (3) forbids; `IsDefEqN.mono` lifts it to every
`n ≥ 1`. And `not_wf_injEnv` closes the door: `RuleShape.delta` needs a `.const`-headed lhs while
`rogueDf.lhs` is `.sort .zero`, and `quot`/`iota` need declared constants while `injEnv` has none.

### Why this is not `InjPiRogue.lean` again

| | `InjPiRogue.roguePiEnv` | `InjMethod.injEnv` |
|---|---|---|
| rules | **two** δ-rules on **one constant** | **one** rule, **no constant** |
| `VEnv.WF` clause pinned | `DefEqHeadsUnique` (rule-count uniqueness) | `RuleShape.delta` (lhs is `.const`-headed) |
| target | `ConvPiFromEntry` (a *neighbour* of the hole) | `SortForallEDisjN` = `RigidSortPiDisj`, **conjunct 3 of 5 of the hole** |
| independence needed | **yes** — `ConvSortPiDisj roguePiEnv 0`, and the file says it "cannot be" proved there | **no** — clause (3) is a bare `¬ IsDefEqN`, refuted by exhibiting the conversion |

`RuleShape.delta` is logically prior to rule-count uniqueness: a rule can fail to be
`const`-headed at all, and then there is nothing for uniqueness to be about. So the received
summary — "a `VEnv.WF` environment cannot carry **two** δ-rules for one constant, and that is the
only thing `roguePiEnv` needs" — is **one clause too weak** as a statement of what the proof must
consume. **Recommended correction to `InjPiRogue.lean` §7's "Stop pointing proof attempts at …"
box** (I do not own that file, so this is a statement, not an edit): the clause of `VEnv.WF` that
must be consumed is `VEnv.RuleShape`, of which `DefEqHeadsUnique` is a consequence, not the
converse.

### Limits of this result, proved where provable

1. **It does not refute either target hole, and cannot.** Both take `VEnv.WF env`;
   `not_wf_injEnv` is the machine-checked proof that my witness is outside that hypothesis. This
   limit is *proved*, not asserted.
2. **It says nothing about whether clause (3) is true over a `VEnv.WF` environment.** It is a
   statement about a *hypothesis*, not about the mathematics.
3. **It does not touch clause (1) (`SortInvN`), the other live clause.** `injEnv` relates a sort
   to a Π, not a sort to a sort, so `SortInvN injEnv 0 1` is untouched — plausibly still true
   there. Whether an analogous one-rule witness breaks clause (1) is **open and cheap**: take
   `rogueDf' := ⟨0, .sort .zero, .sort (.succ .zero), .sort (.succ (.succ .zero))⟩`; `Ordered`
   should hold by the same two lines, and it would refute `SortInvN` at `n = 1` since
   `.zero ≉ .succ .zero`. **I did not build it** — flagged rather than claimed.
4. **The `¬ IsProof` wall (M4) is untouched.** It is why `RigidShapeUniqNS` itself, rather than
   its conjunct 3, cannot be attacked this way even at `Ordered` strength.

### Where a fifth round should go, given all nine measurements

Ranked, with the reason:

1. **Clause (1), one rule, `Ordered`** — limit 3 above. Hours, not days, and it completes the
   environment-axis picture for both live clauses.
2. **`RuleShape`-guarded clause (3).** State `SortForallEDisjN` over
   `Ordered env ∧ (∀ df, env.defeqs df → env.RuleShape df)` — the exact strength this round shows
   is necessary — and see whether it is provable. That is the first formulation of clause (3) that
   is not already refuted by an environment, and nobody has written it.
3. **Do not** reopen the index route (`SubstC`, `SubstT` both false, M9), the model route
   (1 of 5 permanently, M6), or a `VEnv.WF`-strength refutation (M3/M4).
4. **Restate instruction/handoff point 3.** "The dependency is circular" sends rounds hunting for
   a way to break the circle; the truth is that the circle *is* breakable in principle by the
   alternation index and the reference does break it, and what kills the route is that `SubstC`
   is **false at `n = 1`** and `∀ n, DefInv n` is **false over `∅`**. The second framing closes
   the route; the first one advertises it.

### §3.1 CORRECTION to limit 3, same day, before publishing the recommendation

I checked limit 3's "open and cheap" witness before recommending it, and **it does not exist.**
`VDefEq.WF env df` requires *both* sides typed at the **same** `df.type`. A rule between two sorts
would need `HasType 0 [] (.sort u) df.type` and `HasType 0 [] (.sort v) df.type`, while
`.sort u : .sort (.succ u)` and `.sort v : .sort (.succ v)` — the level bookkeeping forces the two
declared types apart unless `u ≈ v`, in which case the rule is harmless and clause (1) survives it.
So `rogueDf'` as I wrote it is **not** a legal `VDefEq` at all.

This is exactly the argument `InjPiRogue.lean` already records for `rogueSortEnv` — "*That argument
is sound **for sort chains only**, where the level bookkeeping (`.sort l : .sort (.succ l)`) forces
the mismatch. It says nothing about Π chains*" — and I had read that sentence and still wrote the
recommendation. **The asymmetry it describes is the real content:** the rogue idiom reaches the
Π-side entries and **provably cannot reach the sort-side one**, because a Π's type
`.sort (.imax u v)` is free enough to be shared while a sort's type `.sort (.succ u)` is not.

So the corrected picture of the two live clauses is a genuine split, and it is the most useful
single sentence this round produced:

> **Clause (3) (`SortForallEDisjN`) is not provable from `Ordered env` — one non-`const`-headed
> rule refutes it (§3). Clause (1) (`SortInvN`) is immune to that idiom, because no legal
> `VDefEq` relates two sorts at distinct levels.** The two live clauses therefore need *different*
> environment hypotheses, and only clause (3) needs `RuleShape`.

**Recommendation 1 is withdrawn and recommendation 2 is promoted to first.** What remains open on
clause (1) is not a cheap witness but the opposite: upgrading "no one-rule witness exists" to
"provably immune at `Ordered` strength" needs typing inversion over `∅` (that `HasType ∅ 0 [] (.sort u) T`
forces `T ≈ .sort (.succ u)`), which is itself a small inversion lemma nobody has stated. That is a
better second target than the one I first wrote, and it is *positive* work rather than a refutation.

### §3.2 Build receipt (2026-09-04, final)

Bare `lake build`: **Build completed successfully (1667 jobs)**.
`guard 1 ✓ (24 frozen axioms)` / `guard 2 ✓ (INCOMPLETE: sorryAx present)` / `guard 3 ✓ (2/2)`.
Census **13**, unchanged — nothing discharged, by design.
`Lean4Lean.Theory.Typing.InjMethod` builds in ~1.2 s with **zero warnings**.
One transient red during the round in `Verify/Inductive/InductMap.lean`, a file owned by another
live stream; re-polled and green. Nothing in this round touched `Injectivity.lean`, any frozen
file, or any file this stream does not own, and no git state was changed.
