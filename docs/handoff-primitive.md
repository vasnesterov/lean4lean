# `checkPrimitiveDef.WF.rest` — `Reflection.checkITE.WF` is closed, and the two halves were not two halves

Stream scope: `Lean4Lean/Verify/Typing/Expr.lean`, `Lean4Lean/Primitive.lean`,
`Lean4Lean/Verify/Primitive.lean`, `Lean4Lean/Verify/Environment/Boundaries.lean`
(`checkPrimitiveDef.WF.rest` only), and new files under `Lean4Lean/Verify/`.

Everything below is marked **[machine-checked]** (a `lake build`, the sorry census, the guards,
`scripts/dup-names.lean`, or a Kernel Arena run produced it) or **[source]** (read off the code,
or argued).

| gate | before | after |
| --- | --- | --- |
| sorry census (`lake env lean scripts/sorry-census.lean`) | **19** | **19** **[machine-checked, both runs]** |
| `lake build` of `Verify.Primitive`, `Verify.Environment.Boundaries`, `.Extension`, `Verify.Bridge` | green | green **[machine-checked]** |
| `Verify/Guard.lean` guards 1–3 | ✓ | ✓ **[machine-checked: 25 frozen axioms ✓; `kernel_sound` within whitelist ✓ (proof INCOMPLETE); cone gaps 54/54 ✓]** |
| `scripts/dup-names.lean` | — | no duplicates **[machine-checked]** |
| Kernel Arena (`lean4lean-local`) | **185 / 6 / 0** | **185 / 6 / 0** **[machine-checked; three full runs: baseline, after both executable changes, and a confirmation run]** |
| axiom set of `Reflection.checkITE.WF` | — | **identical, element for element, to `Reflection.check.WF`'s** **[machine-checked]** |

`Lean4Lean/Primitive.lean` changed: two executable changes, both recorded in `divergences.md`
(the primitives bullet, "Seventh (b)" amended and "Ninth" added).

---

## 0. Bottom line

1. **`Reflection.checkITE.WF` is proved**, together with the half-lemma it is built from and
   the acceptance test that composes it with `VEnv.reflects_condApp`. Its axiom set is
   **identical** to the already-landed `Reflection.check.WF`'s — same 25 entries including the
   inherited `sorryAx` — so it adds no taint of any kind, and the census is unmoved at 19.
   See §1.
2. **A defect was found in the recognizer that the previous handoff had exactly backwards.**
   §5 of that handoff said the `true` and `false` halves of `checkITE` are "separate binder
   blocks, so their contexts differ in the `H` domain only". They were **not separate blocks**:
   Lean's `do` layout put the `false` half *inside* the `true` half's `p`, `H`, `t` binders, so
   the two conclusions lived three binders apart. Same defect in `Reflection.checkNatDITE` and
   in `Condition.check`'s `.bool` arm. Repaired by factoring each half into its own definition.
   §2.
3. **The prescribed remedy for that non-problem — `TrExprS.unique'` + `IsUniqueCtx` — is not
   needed and was not used.** The two halves are proved independently and combined by a
   `fun v : Bool => …`; nothing is ever compared across them. §2.3.
4. **The `@ite.{1}` type check from last round was in a shape the proof cannot use.** It pinned
   `∀ (α : Type) (c : Prop), Decidable c → α → α → α`; `VEnv.condApp_typed` needs the head's
   type *after* the result type is supplied, and bridging that gap needs `HasType α (.sort 1)`
   at the base context, which `checkIsType α` does not give. Now checked applied, as
   `checkNatDITE` already did. §3.
5. Everything `Condition.check.WF` still owes `VEnv.reflects_condApp` is exactly three facts:
   `hdec`, `hB`, `hPR`. That is machine-checked, not argued — see
   `VEnv.reflects_condApp_of_checkITE`. §1.3.

---

## 1. `Reflection.checkITE.WF` **[machine-checked]**

### 1.1 What is in `Lean4Lean/Verify/Primitive.lean`

| name | content |
| --- | --- |
| `trExprS_app_inv'` | application inversion in the `_inv'` family's raw form. Needed because `let .app _ _ h3 h4 := h` does **not** reduce a `mkApp2`/`mkApp5` under a `VContext.TrExprS` abbrev — that failure is the first thing a newcomer will hit |
| `trExprS_iteHeadType_inv'` | inverts `∀ (c : Prop), Decidable c → α → α → α` for an *arbitrary* `α : Expr`, identifying its three occurrences under the binders with the base translation by `trExprS_weakBV0` + `TrExprS.unique`. Same device as `trExprS_reflProofType_inv'` |
| `TypeChecker.Reflection.checkITEHalf.WF` | one half of the check, parametrised by the boolean `v`, the constant name `bn` the recognizer writes for it, and the branch selector `sel`. Delivers the `IsDefEqU` in the four-entry context `[Aα, Aα, RT (bvar 0) (boolLit v), .sort .zero]` |
| `TypeChecker.Reflection.checkITE.WF` | the whole check: `∃ Aα F`, with `TrExprS α Aα`, `Aα.ClosedN 0`, `F.ClosedN 0`, `TrExprS (@ite.{1} α) F`, `HasType F (∀ (c : Prop), Decidable c → Aα → Aα → Aα)`, and the selection `IsDefEqU` **for both booleans** |
| `VEnv.reflects_condApp_of_checkITE` | the acceptance test: `checkITE.WF`'s two outputs plus `hdec`/`hB`/`hPR` give `VEnv.ReflectsCondApp` |
| `Reflection.defn₁_type_isUnique` … `defn₂_toDec_closed` (8 lemmas) | the non-vacuity discharge: the `IsUnique` / `looseBVarRange' = 0` side conditions hold at both shipped `Reflection`s |

### 1.2 Hypotheses, and why each is suppliable **[machine-checked where marked]**

`checkITE.WF` takes: `hfail` (generalised over the `VContext` — see the trap in §4),
`hnil : c.vlctx = []`, `hlp : c.lparams = []`, `α`'s `FVarsIn` / `IsUnique` /
`looseBVarRange' = 0`, and for `r.type` and `r.toDec` a base-context `TrExprS` together with
`IsUnique` and *some* typing (used only for `ClosedN 0` via `closedN_of_nil`).

* `hnil`, `hlp` — the recognizer's branches run at `VContext.mk' wf .safe [] fuel`, and the
  `Nat.bitwise` branch's `Condition.check` calls were hoisted above its binders last round for
  exactly this reason. **[source]**
* the `r.type` / `r.toDec` translations and typings — `Reflection.check.WF`'s output verbatim,
  including the `∃ TD TDA` clause added last round. **[source]**
* `IsUnique` is `False` at a `.proj`, so it is a real vacuity risk, not bookkeeping. All four
  instances (`defn₁`/`defn₂` × `type`/`toDec`) are proved, as are the four
  `looseBVarRange' = 0`. **[machine-checked]**
* `IsUnique α` and `α.looseBVarRange' = 0` for `α ∈ iteTypes` — `q(Nat)`, `q(Bool)`; `.const`,
  so both are `trivial`/`rfl`. **[source]**

### 1.3 What is left, exactly **[machine-checked]**

`VEnv.reflects_condApp_of_checkITE` type-checks, and its remaining hypotheses are `hdec`, `hB`,
`hPR` and nothing else. So for the `ite` side of `Condition.check.WF` the whole residue is:

* `hdec` — from `isDefEq e cond.dec`, β-reduced through `e = fun x y => toDec (prop x y)
  (asBool x y) (proof x y)` at a pair of numerals (`IsDefEqU.instNat2` then two `beta'`);
* `hB` — `VEnv.HasPrimitives.natBLE` / `natBEq` for the two shipped conditions;
* `hPR` — `trExprS_reflProofType_inv'` → `VEnv.reflProof_inst`, both already built and
  `sorryAx`-free.

---

## 2. The defect: the two halves were one nested block **[machine-checked by `#print`; repair machine-checked]**

`#print Lean4Lean.Environment.Reflection.checkITE` on the pre-repair source shows

```
withCheckedLocalDecl `t … fun t => do
  withCheckedLocalDecl `e … fun e => do
      let b ← checkedIsDefEq (… Bool.true …) t
      if b then pure () else fail
  withCheckedLocalDecl `p … fun p => …          -- the `false` half, HERE
```

`fun t => do` opens its `do` block at the column of the next token, which is the same column as
the following `withCheckedLocalDecl`, so the second half became a *statement of the first half's
`t` block*. It therefore ran under `p`, `H`, `t` — binder depth 3, not 0.

Identical in `Reflection.checkNatDITE` (`false` half under `p`, `H`, `a`) and in
`Condition.check`'s `.bool` arm (under `t`).

### 2.1 Why it is inert executably and fatal for the proof

Executably: the three stale declarations are checked, are mentioned by neither side of the
`false` comparison, and are unused, so the accepted set is unchanged. **[source]** The Arena is
unchanged. **[machine-checked]**

For the proof: `VEnv.hsel_of_checkITE` needs *both* equations in the same four-entry context
`[Aα, Aα, RT (bvar 0) (boolLit v), .sort .zero]`. The `false` half's conclusion sat in a
seven-entry context, and dropping three unused entries is a **strengthening** step —
`IsDefEqU.weakN_iff`, one of the 19.

### 2.2 The repair

`Reflection.checkITEHalf`, `Reflection.checkNatDITEHalf` and `Condition.checkBoolITEHalf` are
now separate definitions taking the boolean literal and a branch selector; `checkITE` etc. call
each twice. The two calls are siblings by construction, so the layout cannot silently regress.
Recorded in `divergences.md` as "Ninth".

### 2.3 The correction to the previous handoff

Its §5 said the halves "differ in the `H` domain only: compare across them with
`TrExprS.unique'` + `IsUniqueCtx`, not `TrExprS.unique`". Both clauses are wrong:

* they differed by **three binders**, not by the `H` domain;
* **no cross-half comparison is needed at all.** `checkITE.WF`'s conclusion is
  `∀ v : Bool, …`; each half is proved on its own and the two are combined by `cases v`.
  `TrExprS.unique'` and `IsUniqueCtx` appear nowhere in the proof.

This is the round's most valuable output: a prescribed technique that was solving a problem that
did not exist, guarding a layout that was itself broken.

---

## 3. The `@ite` type check had to be re-shaped **[machine-checked: Arena; source: the argument]**

Last round added `checkedTypeIs q(@ite.{1}) q(∀ (α : Type) (c : Prop), Decidable c → α → α → α)`.
That shape is not usable. `VEnv.condApp_typed` consumes
`HasType F (∀ (c : Prop), Dc c → Aα → Aα → Aα)` where `F` is the head **already applied to the
result type**, because that is what `VExpr.condApp` puts in head position. Getting there from
`HasType ite (∀ (α : Type) …)` needs `HasType Aα (.sort 1)` at the base context. What
`checkIsType α` gives is `IsType Aα`, i.e. `HasType Aα (.sort u)` for an *existential* `u`; the
only route from there is (i) recover `Aα : Sort 1` inside the recognizer's binders by `piUniq`
on the application spine, (ii) `HasType.uniqU` against the weakened `Sort u`, (iii)
`IsDefEqU.sort_inv` to get `u ≈ 1` — and `sort_inv`'s cone bottoms out at
`forallE_inv_stratified`, another of the 19. **[source]**

So the recognizer now checks `@ite.{1} α` against `∀ (c : Prop), Decidable c → α → α → α`, once
per element of `iteTypes` — the same shape `Reflection.checkNatDITE` already used for
`@dite Nat`. `checkedTypeIs.WF` then hands the typing over directly and
`trExprS_iteHeadType_inv'` pins the type.

Accept-set: neither form is a superset of the other in the abstract (the applied one also forces
`α : Type`; the unapplied one also constrains `ite` at result types never used), but each is
implied by the selection equations the same branch goes on to check, so both are neutral
relative to the rest of the branch. Arena 185/6/0 for both. **[machine-checked]**

---

## 4. Traps, for whoever picks this up

1. **`hfail` must be generalised over the `VContext`.** `Reflection.check.WF` states it at `c`;
   any lemma that uses `fail` *under* a `withCheckedLocalDecl` needs
   `∀ {c' : VContext} …, M.WF c' s' fail Q`. The call sites supply `fail = throw …`, for which
   `M.WF.throw` holds at every context, so this costs nothing — but the un-generalised form
   fails with a page-long context mismatch and looks like a deeper problem than it is.
2. **`let .app _ _ h3 h4 := h` does not see through `mkApp2`/`mkApp5` when the goal is stated
   with `VContext.TrExprS`.** Use `trExprS_app_inv'` and `obtain`.
3. **`simp only [VExpr.lift, VExpr.liftN, liftVar]` leaves `if 0 < 0 then …` unevaluated.** The
   `.bvar 0 → .bvar 3` chain needs the comparisons discharged too (see the `simp only` list in
   `checkITEHalf.WF`).
4. **The final context reconciliation** — `c4.vlctx.toCtx` down to `[Aα, Aα, HT, .sort .zero]` —
   is `simpa [VContext.IsDefEqU, VContext.withMLC, VLCtx.toCtx, hlp, hnil, VExpr.condApp]`.
   `VContext.IsDefEqU` is an abbrev and must be named explicitly.
5. `Verify/Environment/Extension.lean:118` consumes `ReflectsNatBitwise` **positionally**. Not
   touched this round; `Extension.lean` and `Bridge.lean` both still build. **[machine-checked]**

---

## 5. Pick up first

1. **`Condition.check.WF`.** With §1.3 above, the `ite` side is discharged by
   `VEnv.reflects_condApp_of_checkITE` and the residue is `hdec`, `hB`, `hPR`. The arm's own
   shape: `checkType cond.dec`, `checkedTypeIs cond.prop q(Nat → Nat → Prop)`,
   `Reflection.check.WF` (done), `Reflection.checkITE.WF` per `iteTypes` element (done),
   `Reflection.checkNatDITE.WF` (open, §2), `checkType e`, `checkedTypeIs asBool`,
   `checkedTypeIs proof …` (→ `trExprS_reflProofType_inv'` → `reflProof_inst` → `hPR`), and
   `isDefEq e cond.dec` (→ `hdec`).
2. **`Reflection.checkNatDITE.WF`**, feeding `reflects_condAppD`. Now genuinely the same shape
   as `checkITE.WF`: `checkNatDITEHalf` is a sibling pair, `@dite Nat`'s type is already checked
   applied, and `condApp_typed'` takes the dependent branch domains. The differences from
   `checkITE.WF` are (i) the branch domains `p → Nat` and `¬p → Nat` are not closed, so the two
   inner binders' translations need `trExprS_app_inv'` on `Not p` rather than
   `TrExprS.unique` against a closed `Aα`, and (ii) `reflects_condAppD`'s `hsel` keeps a
   `VExpr.WF` premise instead of the four typings.
3. **`Condition.check`'s `.bool` arm** — `ReflectsCondApp1`. Its `@ite` check was changed to the
   applied form at the same time as `checkITE`'s, so `trExprS_iteHeadType_inv'` applies verbatim;
   `checkBoolITEHalf` is the sibling-pair form.
4. Then the `Nat.mod` / `Nat.div` assembly: `trExprS_app5`, `reflects_fuel_mod` / `_div` in
   their **new** (`RHS` + `hsel`) form, `preserves_glue`, `VEnv.primField_Nat_mod` / `_div`.
5. `unfoldNatWellFounded` last, and **not** by a checked conversion: the
   `WellFounded.Nat.fix` fixpoint equation is propositional, not definitional, so a
   `checkedIsDefEq` there returns `false` and the recognizer would *reject* `Nat.gcd` and
   `Nat.bitwise`. This has now survived four handoffs unchanged.

---

## 6. Carried over, still correct **[machine-checked unless noted]**

* Π-injectivity here is **inherited taint, not a new hole**: `VEnv.IsDefEqU.forallE_inv` and
  `VEnv.HasType.piUniq` are inside `checkPrimitiveDef.WF`'s 17594-constant forward cone, measured
  by a reachability scan over `ConstantInfo.value?`, not argued.
* `reflects_fuel_go`'s repair stands: `ReflectsCondApp` is the `ite` rule only, the `go`
  equations are `dite`s, and `ReflectsCondAppD` / `reflects_condAppD` are the `dite` statements.
  `ReflectsCondApp`'s live consumer is `reflects_natBitwise_go`, whose equation really is an
  `ite`.
* `trExprS_goType_inv'` and its nine supporting inversions: sorry-free, used in situ in the
  `Nat.mod` branch.
* The C++ kernel has **no primitive-definition recognizer at all** (measured), so every
  discrepancy here is a divergence by construction and the Arena's accepted set is the only
  external constraint.
* The general principle, now paid for twice: **the verification can never recover a subterm's
  type from the fact that an application containing it type-checks.** `TrExprS.app` and
  `VExpr.WF.app_inv` both hand back the domain the application *invented*. If the abstract
  statement needs a declared type, the recognizer has to check it — and it has to check it in
  the *shape* the abstract statement consumes (§3).

## 7. Method note

Last round's instrument — *write the supplier's side and see what it holds at the moment it must
produce the hypothesis* — found the defect in §2 as well, but only after `#print`ing the
recognizer. **Read the elaborated program, not the source layout.** Three `do` blocks in this
file did not mean what they looked like, and no amount of reasoning about the source would have
shown it; one `#print` did.
