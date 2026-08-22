# How do we reach const-application injectivity?

Scouting pass, read-only. **[verified]** = read from source; **[inferred]** = my analysis.
Tree at `0eb8c55`. Estimates classify arithmetic as **positional** (de Bruijn offsets/index
shifting — under-priced ×2 by default) or **structural** (induction over term or derivation
shape).

---

## Bottom line

**The statement as posed is false, twice over, and one of the two falsifications is not
repaired by the narrowing the ledger already applies.** Beyond that, three different facts
are being called "I13", and the five consumers do not all want the same one.

| # | Route | Verdict |
|---|---|---|
| 1 | **Church–Rosser** | **The answer.** No longer circular — the cycle ran through `uniq` needing `forallE_inv_stratified`, and `forallE_inv` now arrives independently. Conditional on C4 + `Params` + `ChurchRosser`'s `extra` case, none of which this item has to pay for. §5. |
| 2 | Extend the reflection | **Blocked, and not where you expected.** `SExpr.mk` preserves const heads and spines exactly — it is *not* the quotient that loses information. `Shape.indTy` is argument-free (`ShapeLogRel.lean:360`), so the shape model cannot tell `Quot α r` from `Quot α' r'`. §4. |
| 3 | Make the checker check | Real, cheap, and only fixes two of the five sites. A `divergences.md` entry. §7. |
| 4 | Restate the consumers | **Impossible for the quot sites.** §7 gives the wall. |

---

## 1. First: "I13" names a different statement than the one wanted

The ledger entry (`docs/design-inductive.md:1052–1054`) is **[verified]**:

```lean
theorem IsDefEqU.const_forallE_inv (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (hrigid : RuleFreeHead env c) :
    ¬ env.IsDefEqU U Γ ((VExpr.const c ls).mkApp args) (.forallE A B)
```

That is **disjointness** — a rule-free const application is not a Π — in the shape of
`sort_forallE_inv`. It is what `pat_major_not_pi` (I14) consumes. It is **not** injectivity,
and it does not imply it.

Three distinct facts are in play, and the five consumers split across them:

| | Fact | Wanted by |
|---|---|---|
| **(A)** | *disjointness* — const-app ≢ Π. This is I13 as recorded. | `pat_major_not_pi` (I14) |
| **(B)** | *injectivity* — `c ls as ≡ c ls' as' → ls ≈ ls' ∧ as ≡ as'` | `reduceRecursor.WF` quot branch, `Quot.ind` arm, `TrProj.uniq`, `TrProj.defeqDFC` |
| **(C)** | *rigidity* — `X ≡ const-app → X` whnf-reduces to a const-app with that head | `TrProj.weak'_inv` |

`TrProj.weak'_inv`'s own note (`Verify/Typing/Lemmas.lean:671–678`) traces its route to
*"concluding that `B₀` has the form `(.const S us).mkApp (ps' ++ ιs')`"* — that is (C), not
(B). **[verified]** `TrProj.uniq`'s note (`:929–933`) says *"recover `ls ≈ ls'` and
`ps ≡ ps'`"* — that is (B). **[verified]**

So **the five consumers need two facts, not one**, and neither is the one the ledger
records. `RuleFreeHead` appears nowhere in the tree — only in that design-doc line.
**[verified]**

## 2. (B) is false as posed — witness W1

Take a constant function. `VDefVal.toDefEq` (`Theory/VDecl.lean:11–12`) makes a `def` into
the `VDefEq` `⟨uvars, .const name (VLevel.params uvars), value, type⟩`, so declaring

```
f : Type 0 → Type 0 := fun _ => Prop        -- value = .lam (.sort 1) (.sort 0)
```

puts `.const f [] ≡ .lam (.sort 1) (.sort 0)` into `env.defeqs`. Then by `extra` + `beta`,

```
f Prop  ≡  Prop  ≡  f (Prop → Prop)
```

so `(.const f []).mkApp [.sort 0] ≡ (.const f []).mkApp [.forallE (.sort 0) (.sort 0)]`,
while general injectivity would give `.sort 0 ≡ .forallE (.sort 0) (.sort 0)` — which is
exactly what `IsDefEqU.sort_forallE_inv` (`Theory/Typing/Injectivity.lean:33`) denies, and
which is already proved on the `SExpr` side
(`Experimental/BridgeInjectivity.lean:56–66`). **[verified for the construction; the
contradiction is airtight relative to a statement the project already holds]**

Both arguments have type `Type 0` (`.sort 0 : .sort 1`, and
`.forallE (.sort 0) (.sort 0) : .sort (imax 1 1) = .sort 1`), so the application is
well-typed at both. **W1 is why `RuleFreeHead` is in the ledger's statement at all**, and it
is load-bearing rather than decorative.

## 3. (B) is false *again* — witness W2, which `RuleFreeHead` does not repair

This one is not in the ledger and I think it is new.

```
axiom P  : Prop
axiom mkP : Type 0 → P
```

Both are axioms, so `mkP` heads no rule: `Pat` has exactly three constructors —
`delta` (a `def`'s `.const c`), `iota` (a recursor), `quot` (`Quot.lift`)
(`Theory/Typing/PatternRules.lean:270, 273, 286`) — and an axiom matches none.
**[verified]** So `RuleFreeHead env mkP` holds.

But `mkP A : P` and `P : Prop`, so `IsDefEq.proofIrrel` (`Theory/Typing/Basic.lean:51–53`)
gives

```
mkP Prop  ≡  mkP (Prop → Prop)
```

directly, with no reduction at all. Injectivity would again yield
`.sort 0 ≡ .forallE (.sort 0) (.sort 0)`, contradicting `sort_forallE_inv`.

**So (B) needs a second side condition beyond `RuleFreeHead`: the application must not be a
proof.** The clean form is `env.IsType U Γ ((.const c ls).mkApp as)` — the application is a
*type*. Then `proofIrrel` is excluded, because it would need the application's type
(a sort) to itself be `.sort .zero`, i.e. `succ u ≈ 0`, which `sort_inv` refutes.
**[inferred, but the exclusion is the same two-line argument already written at
`Theory/Typing/HeadReduction.lean:479–483`]**

**All five consumers satisfy it.** The quot sites use it at `Quot α r`, which is `e`'s type;
the `TrProj` sites use it at `(.const S us).mkApp (ps ++ ιs)`, which is `e`'s type
(`Verify/Typing/Expr.lean:85`). So the narrowing costs the consumers nothing — but a
statement written without it would be false, and W2 is the witness. **[verified that both
sites use it at a type]**

> **The statement to put in `Injectivity.lean` is therefore:**
> ```lean
> theorem IsDefEqU.const_app_inv (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
>     (hrigid : RuleFreeHead env c) (hty : env.IsType U Γ ((.const c ls).mkApp as))
>     (h : env.IsDefEqU U Γ ((.const c ls).mkApp as) ((.const c ls').mkApp as')) :
>     List.Forall₂ (· ≈ ·) ls ls' ∧ List.Forall₂ (env.IsDefEqU U Γ) as as'
> ```
> — same head on both sides, which is all the consumers need. Different heads additionally
> needs *no-confusion between rule-free constants*, a fourth fact nobody has asked for.

## 4. Q1 — the reflection route: `mk` is fine, the shape lattice is not

I built the reflection, so this is the part I can answer from the inside.

**`SExpr.mk` does not quotient anything relevant.** `mk_const : mk (.const c us) = .const c (us.map .mk)` and `mk_app : mk (.app f a) = .app (mk f) (mk a)` (`Experimental/Bridge.lean:97–99`) — the head *name* and the spine survive exactly; only the levels are quotiented, and `SLevel.mk_inj` recovers `≈` from that. So the worry that `mk` loses what is needed is **unfounded**. **[verified]**

**The loss is in the `Shape` lattice.** `ShapeS` (`Experimental/ShapeLogRel.lean:354–360`) is

```lean
  | bot | sort (rel : Bool)
  | forallE : Shape → List (Shape × Shape) → ShapeS Shape
  | lam : List (Shape × Shape) → ShapeS Shape
  | ctor : Name → List Shape → ShapeS Shape
  | indTy (rel : Bool) : ShapeS Shape
```

`forallE` carries its domain and codomain shapes, and `ctor` carries its name and argument
shapes — which is exactly why `forallE_whRed_l` (`ShapeLogRelAdequacy.lean:445`) can extract
component defeqs and deliver `forallE_inv` (`:462`). **`indTy` carries a `Bool` and nothing
else.** `Quot α r` and `Quot α' r'` therefore have the *same shape*, and the model has
nothing to say about their arguments. **[verified]**

Corroboration: the adequacy file's whnf inversions are exactly `WHNF.sort` and
`WHNF.forallE` (`Experimental/SExpr.lean:1766–1767`), both `nofun`. There is no
`WHNF.const`, no `WHNF.indTy`, and no `const_whRed_l`. **[verified]**

Extending it needs two changes, not one **[inferred]**:

* **datatype** — `indTy` gains a `List Shape`. That is a second migration of exactly the kind
  in flight (which is adding the `Bool`), and strictly larger: `Compat`, `LE`, `join`,
  `lift`, `plift`, `WF` and `app` each gain a clause, and `plift`/`lift` are where the
  `Shape n → Shape m` index arithmetic lives.
* **semantics** — the LR must stop treating an inductive type application as neutral and
  start relating its arguments, so that `DefEq` at an `indTy` shape says something. The
  datatype change alone buys nothing.

The second is the reason I would not take this route even at zero datatype cost: it changes
what the model *means*, and the model's soundness argument is the thing the whole shape
stream rests on.

## 5. Q3 — Church–Rosser: **not circular any more**

This is the finding that changes the plan.

The cycle I established twice ran through `IsDefEq.uniq` consuming
`IsDefEqU.forallE_inv_stratified` at `Theory/Typing/UniqueTyping.lean:43`. That is still
there — but `forallE_inv` now exists independently, by reflection
(`Experimental/Reflect/Capstone.lean`), and `docs/research-forallE-inv.md` §12.5 (item C4)
costs the conversion to the stratified form at 80–150 lines. **Once C4 lands, `uniq` is
unblocked, and with it the whole of `ChurchRosser.lean`.** **[inferred, but the dependency
chain is verified at each link]**

Given CR, (B) and (C) are the classical corollaries:

* `X := (const c ls).mkApp as`, `Y := (const c ls').mkApp as'`, `X ≡ Y`. CR gives reducts
  related by `NormalEq`.
* `ParRed` on a const-headed spine with a rule-free head can only use `app` congruence: the
  `extra` step needs `Pat p r` with a matching head, and `Pat`'s three constructors
  (`PatternRules.lean:270, 273, 286`) put no rule at `c`. **[verified]**
* `NormalEq` between two const-headed spines: `refl` ✓, `appDF` peels arguments ✓,
  `constDF` at the bottom gives `ls ≈ ls'` ✓, `etaL`/`etaR` need a `.lam` on one side ✗,
  and `proofIrrel` is excluded by §3's `IsType` side condition + `sort_inv`.
* (C) falls out of the same reduction analysis — it is `IsDefEq.reduce_forallE`
  (`HeadReduction.lean:490`) with `.forallE` replaced by a const head.

**Prerequisites, none of which this item pays for:** C4; a `Params` instance (five of six
fields done); and `ChurchRosser.lean`'s remaining `extra` case. All three are already on the
board for other reasons.

## 6. Q2 — is a narrower fact enough? Yes, and it is *the same* narrower fact

Per §3 the needed statement is already narrow: same head, rule-free, applied at a type.
Checking it against each consumer **[verified for the site, [inferred] for sufficiency]**:

| Consumer | Needs | Head | Satisfies `IsType`? |
|---|---|---|---|
| `reduceRecursor.WF` quot branch | (B) | `Quot` | yes — it is `e`'s type |
| `Quot.ind` arm | (B) | `Quot` | yes |
| `TrProj.uniq` | (B) | the structure `S` | yes — `TrProj`'s `HasType` premise |
| `TrProj.defeqDFC` | (B) | `S` | yes |
| `TrProj.weak'_inv` | **(C)**, not (B) | `S` | yes |

Restricting further to *declared inductive type formers* buys nothing over `RuleFreeHead`:
the proof-relevant content is "no rule fires at this head", and M2
(`design-inductive.md:1040–1046`) is how you get it for inductives. `Quot` needs it too and
is not inductive — which the design doc already notes at `:1063–1065`. **[verified]**

## 7. Q4 — restating the consumers

**The quot sites cannot be restated.** The kernel returns `f a` built from `f` in the
*eliminator* spine and `a` in the *constructor* spine (`Lean4Lean/Quot.lean:112`). The
abstract rule `quotDefEq` (`Theory/Quot.lean:11`) is stated at one set of `α, r`. Connecting
`Quot.lift α r β f c q` to the instance at `α', r'` needs `appDF`, which needs `α ≡ α'` —
which is (B). Going the other way round (instantiate the rule at `α, r` and move the
constructor) needs `Quot.mk α' r' a ≡ Quot.mk α r a`, which is (B) again. **[inferred; I
checked both directions]**

`PatternRules.lean:255–262`'s resolution — make the matcher *refuse* unless the two `defeq`
clauses hold — is genuinely unavailable here, because the checker does not refuse.
**[verified]** But there is a third option the Pattern note does not have:

> **Make `Lean4Lean`'s `quotReduceRec` check it.** Add `isDefEq α α'` and `isDefEq r r'` to
> `Quot.lean:110–112`. The WF proof then *receives* what it currently has to derive. This is
> a deliberate divergence from the C++ kernel (`quot_reduce_rec`,
> `~/lean4/src/kernel/quot.h:39–69`, tests head and arity only), so it needs a
> `divergences.md` entry and an arena run — but it is sound and complete, since in a
> well-typed application the two agree and `isDefEq` will say so. It is the same shape as
> `bugs-found.md` item 10's option 2.

**Cost: ~30 lines in `Quot.lean` + ~60 in the WF proof + one arena run. Structural.** It
fixes the two quot sites and **neither** `TrProj` site — those need (B) and (C) at an
arbitrary structure head, where no analogous check exists to add.

## 8. Ranked recommendation

1. **Wait for Church–Rosser; do not build this separately.** §5. The corollary is
   **120–200 lines, structural** — induction over `ParRed`/`NormalEq` with no de Bruijn
   arithmetic — and it delivers (A), (B) and (C) together. Everything it waits on is already
   scheduled. This is the first time in this campaign that CR has *not* been circular for an
   injectivity item, and it is worth acting on.
2. **Fix the statement first, in the ledger and in `Injectivity.lean`.** §1 and §3. The
   ledger's I13 is (A); the consumers need (B) and (C); and (B) needs the `IsType` side
   condition or it is false by W2. Cost: documentation. Doing this before anyone starts is
   what stops the third false-statement round.
3. **Take the divergence only if the quot sites are urgent.** §7, ~90 lines structural + an
   arena run, fixes two of five.
4. **Do not extend the shape model.** §4. Estimate, if anyone insists:
   **1500–3000 lines**, of which the `lift`/`plift` clauses are **positional** — so price
   that portion at ×2 — and the semantic change to the LR is unpriced because I do not know
   how to price a change to what the model asserts.

## 9. What I did not do

I did not machine-check W1 or W2; both are constructions in the abstract theory that reduce
to `sort_forallE_inv`, which is itself only proved relative to `Params`. If either is to be
relied on, the cheap confirmation is to build the two-declaration environment and
`#print axioms` the resulting `IsDefEqU` — the same way `MutualDefUnsound.lean` is built.
I also did not verify that C4 is achievable; it is the one link in §5's chain that
`docs/research-forallE-inv.md` marks low-confidence, and if it fails the whole of route 1
reverts to being circular.

---

# 10. Follow-up: the witnesses, the statements, and C4

## 10.1 W1 and W2 are machine-checked

`Lean4Lean/Theory/Typing/ConstInvWitness.lean`, building clean. Axiom cones:

| | |
|---|---|
| `w1`, `w2`, `w1_forces`, `w2_forces` | `[propext, Quot.sound]` — **no `sorryAx`** |
| `absurd_of_prop_eq_propArrow` | `+ sorryAx`, via `sort_forallE_inv` |

So the *derivations* — that `f Prop ≡ f (Prop → Prop)` and that `mkP A ≡ mkP B` — are
sorry-free. Only the final step, "and that conclusion is impossible", leans on
`sort_forallE_inv`. That taint is unavoidable rather than incidental: refuting a definitional
equality is precisely what `Injectivity.lean` exists to do, so any witness of this class must
bottom out in one of its statements. I checked whether a different choice of arguments could
avoid it and it cannot — two *sorts* inhabiting the same type necessarily have the same
level, so no instance of W1/W2 lands on a disequality that is provable today.

`w2` is the one that matters: `env.defeqs` is not mentioned in its statement, so the witness
stands in an environment with **no rules at all**, and `IsDefEq.proofIrrel` closes it with no
reduction whatever. `RuleFreeHead` cannot exclude it under any reading.

They are landed as **regression tests**, not prose: `drop_ruleFreeHead_inconsistent` and
`drop_isType_inconsistent` each take the injectivity statement with one side condition
removed and derive `False`. Removing a condition from `const_app_inv` later turns one of
these into a proof of `False` from a provable hypothesis, and the file stops compiling.

## 10.2 Statements fixed

`Theory/Typing/Injectivity.lean` now carries `VExpr.headConst?`, `VEnv.RuleFreeHead`,
`IsDefEqU.const_app_inv` (B, both side conditions) and `IsDefEqU.const_forallE_inv` (A), with
a module docstring separating the three facts and naming each consumer. **(C) rigidity is
deliberately not stated there**: its faithful form mentions weak-head reduction, which lives
downstream in `HeadReduction.lean`, and writing a reduction-free approximation is exactly how
one gets a fourth wrong statement. It is recorded as ledger item I13b instead, to be stated
where the reduction relation is in scope.

`docs/design-inductive.md` gains rows I13a/I13b and a correction note; the old recommendation
to pick I13 up "in the `SExpr` bridge, where `Shape.ctor'` already exists" is **withdrawn**
there, since `Shape.ctor'` classifies *constructor* applications and the type formers in
question fall under the argument-free `indTy`.

## 10.3 C4 is achievable — and I had the difficulty in the wrong place

**Verdict: achievable. Route 1 survives.**

I previously marked C4 low-confidence because I expected the `HasTypeStratified` inversion to
be the hard part. It is not: **13 lines, first try**, structurally identical to the existing
`HasTypeStratified.to_core` and `.isType`, with the only new content a `.mono` in the `defeq`
case. Machine-checked in the scratchpad.

The real difficulty is one step further on, and it is a *level alignment*.
`forallE_inv_stratified`'s conclusion pins the **same** `u` in the `IsDefEq` and in the
`HasTypeStratified` — and `uniq` genuinely uses that pinning (`UniqueTyping.lean:55`, where
`.sortDF … e3.symm` and `d3.instN` must meet at one level). But `forallE_inv` hands back a
level unrelated to the one the stratified hypothesis carries, and reconciling two types of
the same term on the `VExpr` side **is** `uniq`. Circular.

**It is not circular on the `SExpr` side, and that is what rescues it.** SExpr-side unique
typing is already proved: `SExpr.HasTypeS.uniq` (`Experimental/UniqueTyping.lean:92`). So the
alignment is available there for free:

1. `VEnv.HasType.toSExpr` (`Bridge.lean:208`) pushes the stratified hypothesis' typing
   `Γ ⊢ A : .sort u` forward;
2. `SExpr.forallE_inv` (`ShapeLogRelAdequacy.lean:462`) gives the component defeq at some
   `u'`, and `IsDefEq.toHasTypeS` (`Experimental/UniqueTyping.lean:179`) a second typing of
   `mk A`;
3. `HasTypeS.uniq` then `SExpr.sort_inv` (`:472`) give `SLevel.mk u = u'`;
4. `SLevel.mk_inj` (`Bridge.lean:64`) turns that into `u ≈ u'`, and `sortDF`/`defeqDF` retype
   on the `VExpr` side.

So the fix is a strengthened capstone lemma — `forallE_inv` *at a specified level* — rather
than anything in `Injectivity.lean`. **[inferred, but every link is a named proved lemma]**

Revised C4 estimate, all **structural** (no de Bruijn arithmetic anywhere in it):

| Item | Est. |
|---|---|
| `HasTypeStratified.forallE_inv'` | **13, machine-checked** |
| `forallE_inv_at` in `Experimental/Reflect/Capstone.lean` | 30–50 |
| assembly of `forallE_inv_stratified` | 40–60 |
| **total** | **85–125** |

Against the earlier 80–150 with low confidence — same range, now with the risk located and
one third of it already checked. The dependency chain for route 1 therefore holds: C4 →
`uniq` → `ChurchRosser` → (A), (B), (C) together.

## 10.4 C4 landed

Built, and **under estimate**: ~65 lines of proof against 85–125, all structural, no
positional arithmetic. Every piece went through first try.

| Piece | Where | Lines | Verified |
|---|---|---|---|
| `HasTypeStratified.forallE_inv'` | `Theory/Typing/Strong.lean` | 13 | **yes** — built, `[propext, Quot.sound]`, sorry-free |
| `sort_uniq_of_hasType` | `Experimental/Reflect/Capstone.lean` | 9 | elaborated clean; see caveat |
| `forallE_inv_at` | same | 15 | elaborated clean; see caveat |
| `forallE_inv_stratified_params` | same | 28 | elaborated clean; see caveat |

The shape of the proof is what §10.3 predicted. The domain half needs no alignment at all —
`hA₀`'s level is exactly the one `forallE_inv_at` is asked for. The codomain half does, and
asymmetrically: `h3` types `B'` in `A'::Γ` while the equality lives in `A::Γ`, so the two are
brought together by `HasType.defeqDFC` along `A ≡ A'` and then compared with
`sort_uniq_of_hasType`. The final `HasTypeStratified.defeq` retype consumes the `1 ≤ n'`
conjunct that `forallE_inv'` was strengthened to carry, since it lands at `(n'-1)+1`.

**Verification caveat, and it is the §16.4 hazard of `docs/research-forallE-inv.md` again.**
The three `Capstone.lean` pieces elaborated clean under `lake env lean` against the
`ShapeLogRel.olean` present at that moment. The shape stream then pushed an edit,
`ShapeLogRel.lean` went red, and `lake` discarded that olean — so the axiom cones cannot
currently be re-checked, and by the rule established there **this is not yet a verified
result**. It should be re-checked the moment that stream is green; the expected cone is
`[propext, Classical.choice, Quot.sound, sorryAx]`, matching `forallE_inv_params`, with the
`sorryAx` entering through `SExpr.IsDefEq.strong` exactly as before.

The mainline half is unaffected and fully verified, since it depends on nothing in
`Experimental/`.

*(Separately: `lake build Lean4Lean.Theory` is currently red at
`Theory/Typing/PatternRules.lean:1359`, the keystone stream's file. `EnvLemmas` — its only
route toward this work — does not import `Strong.lean`, and `Strong`, `Injectivity` and
`ConstInvWitness` each build clean on their own, so that failure is unrelated to C4.)*
