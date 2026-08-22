# Scoping the three projection/reduction sorries

`WHNF.lean:8` (`reduceRecursor.WF`), `Reduce.lean:145` (`reduceProjCore.WF`),
`InferType.lean:421` (`inferProj.WF`). Scoping only; no `.lean` written. Tagged
**[verified]** (read from source) / **[inferred]**. Tree at `d04adda`.

---

## Bottom line

The three are in three different states, and only one of them should be built now.

| # | Sorry | Truth | Vacuous today? | Gated on `TrProj.uniq`/`defeqDFC`? |
|---|---|---|---|---|
| 1 | `reduceRecursor.WF` | **true** | **No — half of it is live** | No |
| 2 | `reduceProjCore.WF` | **true** | Yes, twice over | Probably not — §4 |
| 3 | `inferProj.WF` | **wrongly stated; false once live** | Yes | Yes |

* **`reduceRecursor.WF` is the one to build.** It is the only one of the three that is not
  vacuous: its `quotReduceRec` branch is reachable today and provable from `quotDefEq`.
  Its `inductiveReduceRec` branch is vacuous and, when it stops being so, needs `structEta`
  — the same missing rule as the two struct-eta sorries (`docs/research-structeta.md`).
  So it splits cleanly into a buildable half and a blocked half.
* **`inferProj.WF` is false as stated, for a shallow reason nobody has noticed**, on top of
  the deep one already in `bugs-found.md` item 10. §3. It should be *restated* before it is
  ever proved, and even restated it stays false until item 10 is resolved.
* **`reduceProjCore.WF` is true but doubly vacuous** and I would not spend on it yet. §4.

---

## 1. `reduceRecursor.WF` — half live, half blocked

```lean
def reduceRecursor (e : Expr) : RecM (Option Expr) := do
  if env.quotInit then
    if let some r ← quotReduceRec e whnf then return r
  if let some r ← inductiveReduceRec env e whnf inferType isDefEq then return r
  return none
```
(`TypeChecker.lean:334–341`) **[verified]**

### 1a. The `quotReduceRec` branch is reachable **[verified]**

I expected this to be vacuous like everything else downstream of `AddInduct`, and checked:
it is not.

`TrEnv'.quot` (`Verify/Environment/Basic.lean:191–195`) fires on `AddQuot`
(`:90–94`), which is four `AddQuot1` steps inserting `.quotInfo` for `Quot`, `Quot.mk`,
`Quot.lift`, `Quot.ind`, each needing only `TrConstant .safe`, freshness and `addConst`.
**`AddQuot` never inspects `Eq`** — the `QuotReady` premise is on the *`VEnv`* side
(`VEnv.QuotReady env := env.constants ``Eq = some eqConst`), and an `axiomDecl` named `Eq`
at the right type satisfies it. So a `VContext` with `quotInit = true` and `Quot.lift` in
its map exists, and `quotReduceRec` (`Quot.lean:105–120`) can return `some`.

That is a real difference from `checkEqType.WF`/`addQuot.WF`, whose vacuity
(`Verify/Environment.lean:118–133`) comes from the *kernel-side* `checkEqType` needing
`Eq` as `.inductInfo`. `TrEnv'` is a relation, not a reachability claim, and
`reduceRecursor.WF` quantifies over `VContext`s, not over environments reachable from
`Environment.empty`. **[verified]** — worth stating, because it is the reason this branch
is not covered by the standing vacuity argument.

The abstract counterpart is `quotDefEq` (`Theory/Quot.lean:11`),
`fun α r β f c a => Quot.lift α r β f c (Quot.mk r a) ≡ f a`, which `AddQuot` puts into the
`VEnv` as a `VDefEq` — so `VEnv.IsDefEq.extra` applies directly. No `TrProj`, no
`IsStructure`, no `structEta`. **[inferred]**

### 1b. The `inductiveReduceRec` branch is vacuous, then blocked

It needs `.recInfo` in the constant map. The only `TrEnv'` rule that would introduce one is
`induct`, whose `AddInduct` premise (`Verify/Environment/Basic.lean:106–108`) is an
inductive with **no constructors** (`-- TODO`). **[verified]**

When that lands, this branch needs three things, only one of which exists:

* the ι-rule for recursors — supplied by `addInduct'`'s `VDefEq`s;
* **K-like reduction** — per `design-inductive.md:618–637` this needs no new rule (it is
  `proofIrrel` + ι), but the abstract counterpart is *stronger* than the checker's
  `isKTarget`, so it does not follow mechanically; it is lemma M3;
* **structure eta**, via `toCtorWhenStruct` (`Inductive/Reduce.lean:58–65`), which converts
  a struct-typed major premise into a constructor application. That is the missing
  `VEnv.IsDefEq` constructor from `docs/research-structeta.md`. **[verified that
  `toCtorWhenStruct` is on this path; [inferred] that no derivation exists without it]**

### Itemisation — the buildable half only

| # | Item | Est. | Confidence |
|---|---|---|---|
| R1 | split `reduceRecursor.WF` on `env.quotInit` and the two `if let some` guards; the `none` fall-through is `nofun` | 15 | high |
| R2 | `quotReduceRec` returns `some` ⇒ head is `Quot.lift`/`Quot.ind` at the right arity, major reduces to `Quot.mk _ a` | 40 | medium |
| R3 | translate that to the `VEnv` side and apply `IsDefEq.extra` at `quotDefEq`, instantiated at the term's levels | 50–80 | **medium-low** — `quotDefEq.lhs` is λ-wrapped (six binders), so this needs β-reduction of the applied rule, the same peeling `Params.extra_pat` does |
| R4 | the `mkAppRange` tail (`Quot.lean:114–115`) — extra arguments re-applied after the redex | 25 | medium |
| R5 | `FVarsBelow` for the result | 15 | high |
| R6 | `inductiveReduceRec` branch: vacuity from the absence of `.recInfo` | 30–40 | medium — needs the safety-uniform lemma of §5 |
| | **total** | **175–215** | |

R3 is the risk. `quotDefEq`'s left-hand side is a closed λ-abstraction, and the checker's
redex is that abstraction *applied*; relating them is exactly the λ-peeling that
`Params.extra_pat`'s docstring (`ChurchRosser.lean:27–42`) says is forced. Nothing here
needs `Params` — but the same β-peeling work reappears. **[inferred]**

## 2. Why `reduceProjCore.WF` is true

I scrutinised this one first, as asked. It is the reduction fast-path shape, and
`reduceProjCore` (`TypeChecker.lean:351–359`) does have the tell — **it never checks that
the head constructor belongs to the projected structure**:

```lean
  c.withApp fun mk args => do
  let .const mkC _ := mk | return none
  let .ctorInfo mkInfo ← env.get mkC | return none
  return args[mkInfo.numParams + idx]?
```

It reads `numParams` off whatever constructor it finds and indexes blindly. But the
postcondition is **not** false, because the hypothesis carries the missing check:
`he : c.TrExprS (.proj n i e) e'` forces a `TrProj Γ n i · ·` (`TrExprS.proj`,
`Verify/Typing/Expr.lean:182`), whose `IsStructure S D T C` pins the block, and the same
`TrExprS` derivation types the struct at `(.const S us).mkApp (ps ++ ιs)`. So a
constructor of a *different* type cannot appear under a well-translated projection.
**[verified for the shape of the hypothesis; [inferred] that the inversion goes through]**

Two further paths, both benign: `args[…]?` out of range returns `none` (postcondition
vacuous on that branch), and the `.lit (.strVal s)` pre-step (`:353–354`) expands a string
literal, which `TrExprS.lit`/`TrExprS.listChar` already cover.

**So this is the good case: a fast-path whose postcondition is saved by its hypothesis
rather than by its check.** Worth recording, since the last three times this shape appeared
the hypothesis did *not* save it.

## 3. `inferProj.WF` is wrongly stated — and false twice

### 3a. The shallow reason, not previously recorded **[verified]**

```lean
theorem inferProj.WF
    (he : c.TrExprS e e') (hty : c.TrExprS ety ety') (hasty : c.HasType e' ty') :
    (inferProj st i e ety).WF c s fun ty _ =>
      ∃ ty', c.TrTyping (.proj st i e) ty e' ty' := sorry
```

`TrTyping env Us Δ e A e' A'` unfolds (`Verify/Typing/Lemmas.lean:1968–1970`) to
`FVarsBelow Δ e A ∧ TrExprS Δ e e' ∧ TrExprS Δ A A' ∧ HasType e' A'`. So the conclusion
asserts

```
TrExprS (.proj st i e) e'
```

with `e'` bound by the *hypothesis* `he : c.TrExprS e e'` — the translation of the
**struct**, not of the projection. By `TrExprS.proj` that requires
`TrProj Γ st i e' e'`, i.e. `D.projTerm T C us ps ιs i e' = e'`: the recursor application
`S.rec … e'` equal to `e'`. Impossible. **The `e'` in the conclusion needs to be a fresh
existential** — every sibling in the file has it that way (`inferLet.WF`,
`inferType'.WF`: `∃ e' ty', c.TrTyping e ty e' ty'`).

The call site (`InferType.lean:490`) does not force the error — it passes the result into
`hF`, whose goal has `e'` existentially quantified, so the over-specific form still
elaborates. The bug is invisible from there.

**Fix: `∃ e'' ty', c.TrTyping (.proj st i e) ty e'' ty'`.** That is a one-line restatement,
and it must happen before anyone proves this — but the file belongs to the `TrProj` stream,
so it is theirs to make.

### 3b. The deep reason — `bugs-found.md` item 10 **[verified]**

Even restated, it is false. `inferProj` (`TypeChecker.lean:233–260`) checks the type's head
is `.const I_name` with `typeName == I_name`, that `I_val` is `.inductInfo` with a single
constructor, the argument count, and the F17 `Prop` side conditions. **It never checks
recursiveness.** `VEnv.IsStructure.noRec : C.recFields = []`
(`Theory/Inductive/Structure.lean:485–487`) does. Item 10 measured this: hand-built
`.proj` on `inductive R | mk : R → Nat → R` is accepted by both kernels *and ι-reduces*, and
`TrProj` has no derivation for it.

So: `inferProj` succeeds, `TrProj` does not exist, `TrExprS (.proj …)` does not exist, and
the conclusion is unprovable — for a term the checker accepted. Item 10 already costs the
two ways out (generalise the minor premise over `D.ihTypes`, or make `addDecl` reject it as
a `divergences.md` entry); this scope adds only that **`inferProj.WF` is precisely where
that debt is paid**, and that it cannot be proved before the choice is made.

### 3c. It is vacuously true today

`inferProj` throws unless `env.get I_name` is `.inductInfo`, which no `TrEnv'` supplies
(§5). So the statement is *currently* vacuously true and *becomes* false when `AddInduct`
lands — the worst combination for scheduling, because proving it today would look like
progress and would have to be deleted. **Do not close this one.**

## 4. Which are gated on `TrProj.uniq` / `defeqDFC`

Both are `sorry` and blocked on const-application injectivity
(`Verify/Typing/Lemmas.lean:697–710`, `:929–935`), i.e. on the `Params` instance.

* **`reduceRecursor.WF` — not gated.** Neither branch constructs or compares a `TrProj`.
  The quot branch touches no inductive machinery at all. **[verified]**
* **`reduceProjCore.WF` — probably not gated. [inferred]** It *consumes* a `TrProj` rather
  than producing or reconciling two, and the ι law applies to the same `projTerm` the
  hypothesis supplies. The residual risk is the step "the kernel constructor `mkC` is
  `C.name`": that needs `TrEnv` uniqueness for constructor entries plus `HasInduct`
  uniqueness (ledger G4), which is what `TrProj.uniq`'s note says it needs. If that step
  cannot be done from `TrEnv.find?_uniq` alone, this one is gated after all — **that is the
  first thing to check** if it is scheduled.
* **`inferProj.WF` — gated.** It must *construct* an `IsStructure` from the kernel's checks,
  which is the kernel→abstract structure bridge (G1/G4), the same family.

## 5. The vacuity mechanism, and its one wrinkle

Identical to `docs/research-structeta.md` §4, and it applies to all three: `AddInduct` has
no constructors, so `TrEnv'.induct` never fires and no `.inductInfo`, `.ctorInfo` or
`.recInfo` reaches the constant map. **[verified]**

The wrinkle is the same too: `TrEnv'.no_inductInfo` (`Verify/Environment/Extension.lean:17`)
is proved only at `safety = .unsafe`, because `TrEnv'.ignore` (`Basic.lean:137–140`) admits
a hidden constant when `¬ safety ≤ ci.safety`. `Verify/Environment.lean:133` dodges this by
instantiating the `VEnvs` bundle at `.unsafe`; `VContext` carries a single
`trenv : TrEnv safety env venv` and cannot. A safety-uniform disjointness lemma
(~20–30 lines, `TrEnv.find?_iff` plus the absence of an `.inductInfo` shape in
`TrConstant`) unblocks all of it. **[inferred]**

`reduceProjCore.WF` is additionally vacuous on the *hypothesis* side, which is stronger and
cheaper: `TrProj` requires `IsStructure`, whose `decl` field
(`Structure.lean:488–489`) demands `∃ env₀ env₁, D.WF env₀ ∧ env₀.addInduct' D = some env₁
∧ env₁ ≤ env`. No `TrEnv'`-built `VEnv` contains a block's constants, so `env₁ ≤ c.venv`
fails and `c.TrExprS (.proj …) e'` is uninhabited. **[inferred]** That makes it closeable
by `nomatch`-style inversion with no environment reasoning at all — but see the
recommendation.

## 6. Recommendation

1. **Build `reduceRecursor.WF`'s `quotReduceRec` half** (§1a, items R1–R5, 145–175 lines).
   It is genuinely non-vacuous, needs nothing that is blocked, and is the only real content
   available in this group. Leave R6 — the `inductiveReduceRec` vacuity — until the
   safety-uniform lemma exists, or state it as an explicit hypothesis so the file compiles.
2. **Do not touch `inferProj.WF`.** It needs a restatement (§3a) in a file this stream does
   not own, and it is false until item 10 is decided. Both are other people's calls. The
   restatement is worth flagging to the `TrProj` stream now, since they are about to edit
   that file anyway for the `TrProj.wf` signature change.
3. **Leave `reduceProjCore.WF`.** True, doubly vacuous, and the same argument as
   `docs/research-structeta.md` §5 applies: closing a vacuous sorry removes a marker,
   contributes nothing, and is discarded on landing. If it *is* scheduled, check the
   `mkC = C.name` step first (§4) — that is what decides whether it is gated.

## 7. What I did not do

I did not verify R3's λ-peeling against `quotDefEq` in Lean; it is the largest single
uncertainty in the buildable half and I would attempt it first rather than last. I did not
confirm that `RecM.WF` treats a `throw` as vacuously satisfying its postcondition — the
precedent is `Verify/Environment.lean:147` (`fun _ h => nomatch h`), and §3c depends on it.
