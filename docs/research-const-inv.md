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
