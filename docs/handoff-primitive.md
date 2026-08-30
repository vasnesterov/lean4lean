# `checkPrimitiveDef.WF.rest` — the statement is now true; what closed, what is open

Stream scope: `Lean4Lean/Verify/Typing/Expr.lean`, `Lean4Lean/Primitive.lean`,
`Lean4Lean/Verify/Primitive.lean`, `Lean4Lean/Verify/Environment/Boundaries.lean`, and new
files under `Lean4Lean/Verify/`.

Everything below is separated into **[machine-checked]** (a `lake build`, an `#print axioms`, a
`lean_minimal_hypotheses` run, or a Kernel Arena run produced it) and **[source]** (read off the
code or argued, not proved).

| gate | before | after |
| --- | --- | --- |
| sorry census (`lake env lean scripts/sorry-census.lean`) | **19** | **19** **[machine-checked, both runs]** |
| Kernel Arena (`lean4lean-local`) | **185 correct / 6 either / 0 incorrect** | **185 / 6 / 0** **[machine-checked, both runs]** |
| `Verify/Guard.lean` guards 1–3 | ✓ | ✓ **[machine-checked]** |

---

## 0. Bottom line

**The four-part fix landed.**  `VEnv.ReflectsNatBitwise` was *false* as stated (§3 of the
previous handoff, unchanged and still correct); it is now true, the recognizer supplies the
missing information, and the three closed `Nat.land` / `Nat.lor` / `Nat.xor` branches consume
it.  `checkPrimitiveDef.WF.rest` is therefore **open rather than false** for the first time.

Two corrections to the brief this stream was given:

1. **It was a five-touch-point fix, not four.**  `Lean4Lean/Verify/Environment/Extension.lean`
   — a file this stream does not own — also consumes `ReflectsNatBitwise` *positionally*, and
   the obvious placement of the new `env'.WF` hypothesis breaks it.  §1.3 records the placement
   that keeps it green and why that placement is load-bearing.
2. **§6.1's "identify by `trExprS_uniq`" understates the available tool.**  `TrExprS.unique`
   (`Verify/Typing/Lemmas.lean:2338`) gives *syntactic* equality of translations, not merely
   `IsDefEqU`, for any `e` satisfying `TrExprS.IsUnique` — which is every projection-free
   expression, so every type and right-hand side the recognizer builds.  That matters because
   the `Nat.mod` / `Nat.div` telescope inversion needs `T = VExpr.goType P` on the nose. §5.2.

New machinery, all sorry-free and building:

| declaration | file | content |
| --- | --- | --- |
| `TypeChecker.trExprS_appD` | `Verify/Primitive.lean` | one application step at an **arbitrary** domain (`trExprS_app1` generalised off `Nat`) |
| **`TypeChecker.trExprS_app5`** | `Verify/Primitive.lean` | **the length-5 spine at a fully dependent telescope** — the tool §6.1 named as missing |
| `TypeChecker.checkedTypeIs.WF'` | `Verify/Primitive.lean` | `checkedTypeIs` when the caller already holds the subject's translation: hands back the typing *at that* translation |
| `TypeChecker.trExprS_boolArrow2_inv` | `Verify/Primitive.lean` | `Bool → Bool → Bool` translates to `.forallE .bool (.forallE .bool .bool)` |

Deleted as now redundant: `VEnv.ReflectsBoolBoolBoolT`, `VEnv.ReflectsNatBitwiseT`,
`ReflectsNatBitwiseT.toWeak` (their content is the definition now).

---

## 1. The four-part fix, as landed

### 1.1 `Lean4Lean/Verify/Typing/Expr.lean` — the two statement edits

```lean
def VEnv.ReflectsBoolBoolBool (env : VEnv) (f : VExpr) (g : Bool → Bool → Bool) :=
  env.HasType 0 [] f (.forallE .bool (.forallE .bool .bool)) ∧
  ∀ a b, env.IsDefEqU 0 [] (.app (.app f (.boolLit a)) (.boolLit b)) (.boolLit (g a b))

def VEnv.ReflectsNatBitwise (env : VEnv) :=
  env.contains ``Nat.bitwise →
  ∀ (env' : VEnv), env ≤ env' → ∀ (f : VExpr) (g : Bool → Bool → Bool),
    env'.WF → env'.ReflectsBoolBoolBool f g → ∀ a b, env'.IsDefEqU 0 [] …
```

`import Lean4Lean.Theory.Typing.Env` was added: `VEnv.WF` lives there and the file previously
reached only `Theory.Typing.Basic` / `Lemmas`.  No import cycle — `Theory/` imports nothing from
`Verify/` **[machine-checked: builds]**.

The reasoning for both conjuncts is now a docstring on the definitions themselves, so the next
reader does not have to find this file.  It is the previous handoff's §3 verbatim in substance:
`IsDefEqU` entails well-typedness, so the conclusion *asserts* `f`'s typing, and the truth table
does not imply it (`f : (x : Bool) → Q x` with `Q Bool.true ≡ Q Bool.false ≡ Bool → Bool`);
`env'.WF` is needed because the proof chains `IsDefEqU` and `IsDefEqU.trans` requires it, while
`env ≤ env'` transfers nothing to an `f` that is new in `env'`.

### 1.2 `Lean4Lean/Primitive.lean` — the recognizer check

In each of the `Nat.land` / `Nat.lor` / `Nat.xor` branches, immediately after
`let .app (.const ``Nat.bitwise []) and := v.value | fail`:

```lean
unless ← checkedTypeIs and q(Bool → Bool → Bool) do fail
```

**[machine-checked: `lake build Lean4Lean.Primitive` green, which runs the `run_meta` self-test
at the foot of the file — all eighteen primitives of the real prelude still check.]**  Recorded
in `divergences.md` as the *sixth* way the recognizer is stricter than "declared at a
definitionally equal type".

### 1.3 `Verify/Primitive.lean` and `Verify/Environment/Boundaries.lean` — the follow-through

* `reflectsBoolBoolBool_and` / `_or` / `_bne` take the typing as a new first explicit argument
  and return `⟨hty, fun …⟩`.
* `reflects_natBitwiseApp`, `reflects_natLAnd`, `reflects_natLOr`, `reflects_natXor` take
  `henv : env.WF`.
* `reflects_natBitwise_go`'s uses of `hf` become `hf.2` (three sites); its statement is
  unchanged.
* `ReflectsNatBitwise.mono` threads the extra binder.
* Each of the three `Boundaries.lean` branches gains, right after
  `obtain ⟨G, hFeq, hG⟩ := trExprS_bitwiseApp_inv hFv; subst hFeq`:

  ```lean
  refine M.WF.bind (checkedTypeIs.WF' hG ?hfvB) fun _ _ _ hbt => ?_
  case hfvB => simp [FVarsIn]
  split
  case isFalse => exact M.WF.bindThrow .throw
  rename_i hbty
  obtain ⟨tyB, htyB, hGtyF⟩ := hbt
  cases trExprS_boolArrow2_inv htyB
  have hGty := hGtyF (by simpa using hbty)
  ```

  and passes `henv₂` to `hprim3.natBitwise` and `hGty.mono hle3` to `reflectsBoolBoolBool_*`.

**[machine-checked: `lake build Lean4Lean.Verify.Environment.Boundaries` green.]**

### 1.4 The fifth touch point, and why `env'.WF` sits where it sits

`Verify/Environment/Extension.lean:118–120` (`VEnv.HasPrimitives.addConst`) reads

```lean
· intro h env'' le' f g hfg
  exact H.natBitwise (oldContains (hprims (by simp)) h) env'' (le.trans le') f g hfg
```

The binders are positional.  Inserting `env'.WF →` immediately after `env ≤ env' →` — the
natural place, and the one the brief specified — shifts every name by one: `f` would be bound to
the `WF` proof and the `exact` would be a type error.  This stream does not own that file and
may not fix it, so the hypothesis was placed **after `f` and `g` instead**, where the same
`intro` line binds `hfg` to the `WF` proof and the partial application
`H.natBitwise … env'' (le.trans le') f g hfg` has exactly the residual type
`ReflectsBoolBoolBool f g → ∀ a b, …` that the goal then is.  `Extension.lean:144`
(`HasPrimitives.addDefEq`) is a partial application and is insensitive to the placement either
way.

* Chosen placement keeps `Extension.lean` and `Bridge.lean` compiling: **[machine-checked]**.
* The natural placement breaking `Extension.lean:118`: **[source, argued from the quoted
  binder list — not run, because running it would have left a file this stream does not own
  red for other streams to trip over]**.

The ordering is therefore load-bearing for a file outside this stream's scope, and is flagged in
the definition's own docstring.  **If a later stream wants the natural order, it must edit
`Extension.lean:118` in the same commit.**

---

## 2. What is now proved about `Nat.bitwise`

Unchanged from the previous session and still sorry-free: `VEnv.reflects_natBitwise_go` (the
recursion, by `Nat.strongRecOn` on the first argument), `ReflectsCondApp1` and its `ofDefeq`,
`VExpr.bitParity` / `.bitwiseRec` / `.bitwiseRhs`, `reflects_natOp`, `bif_boolLit`,
`natBeq_eq_decide`, `reflects_bitParity`.  `lean_minimal_hypotheses` previously reported all
thirteen explicit hypotheses of `reflects_natBitwise_go` load-bearing; the statement did not
change this session (only `hf`'s *uses* did, `hf` → `hf.2`), so that audit still applies.
`#print axioms Lean4Lean.VEnv.reflects_natBitwise_go` is identical to `reflects_natAdd`'s
**[machine-checked]**.

What still blocks the `Nat.bitwise` *branch* is §5 — `unfoldNatWellFounded` — not §3 any more.

---

## 3. The new tool: length-5 application spines

`Verify/Primitive.lean`, `namespace TypeChecker` **[machine-checked: builds]**.

```lean
theorem trExprS_appD (hF : c.TrExprS value F) (hFty : c.HasType F (.forallE A B))
    (ha : c.TrExprS a a') (haty : c.HasType a' A) :
    c.TrExprS (.app value a) (.app F a') ∧ c.HasType (.app F a') (B.inst a')

theorem trExprS_app5 (hF …) (hFty : c.HasType F (.forallE A₁ B₁))
    (h₁ …) (t₁ : c.HasType a₁' A₁) (e₁ : B₁.inst a₁' = .forallE A₂ B₂)
    … (h₅ …) (t₅ : c.HasType a₅' A₅) (e₅ : B₅.inst a₅' = R) :
    c.TrExprS (mkApp5 value a₁ a₂ a₃ a₄ a₅) (VExpr.app5 F a₁' a₂' a₃' a₄' a₅') ∧
      c.HasType (VExpr.app5 F a₁' a₂' a₃' a₄' a₅') R
```

Why the general `A`: `Nat.modCore.go` and `Nat.div.go` have type
`∀ b, 1 ≤ b → ∀ fuel x, x + 1 ≤ fuel → Nat`.  Arguments 2 and 5 are *proofs* whose types mention
earlier arguments, so no `Nat`-domain lemma (`trExprS_app1`, `trExprS_app2`) applies, and the
codomain after each instantiation is not a constant.  Each `eᵢ` is the caller's obligation to
compute one instantiation; they are `simp` lemmas away once the abstract `≤` symbol is known to
be closed.

**Audit.**  `lean_minimal_hypotheses` reports **all seventeen explicit hypotheses load-bearing,
none droppable** **[machine-checked]**.  `#print axioms trExprS_app5` = `[propext,
Classical.choice, Quot.sound]` — no `sorryAx` **[machine-checked]**.  Non-vacuity is by
construction: `trExprS_appD` is `TrExprS.app` plus `HasType.app`, and `trExprS_app5` is five
compositions of it, so any five-argument application at a well-typed head instantiates it
**[source]**.

---

## 4. `Nat.mod` / `Nat.div` — the revised remaining steps

All the *mathematics* is already in `Verify/Primitive.lean` (`reflects_condApp`,
`reflects_condApp_natLE`, `ReflectsCondApp.natLE_le`, `reflects_fuel_go`, `reflects_fuel_mod`,
`reflects_fuel_div`, `IsDefEqU.inst4`, `.inst2`).  What is left, per branch:

1. **`checkedTypeIs.WF` on `q(@LE.le Nat _)`** → `P` with
   `HasType P (.forallE .nat (.forallE .nat (.sort .zero)))`.  Use the new
   `checkedTypeIs.WF'` — it delivers the typing at *the caller's* translation, which is what
   every downstream step needs.
2. **`checkedTypeIs.WF'` on `q(Nat.modCore.go)` / `q(Nat.div.go)` against
   `q(∀ n, Nat.succ Nat.zero ≤ n → ∀ fuel x : Nat, Nat.succ x ≤ fuel → Nat)`** → `GO` with its
   telescope.  **This is the one piece that does not yet exist**, and §5.2 below is what it
   costs; it is *not* just a fifth `trExprS_arrow_inv`.
3. `Condition.check.WF` for `Condition.natLE`, as in the previous handoff: `checkType cond.dec`
   → `D`; `checkedTypeIs cond.prop` → `P` again (identify with step 1 by `TrExprS.unique`, not
   `trExprS_uniq` — see §5.2); `Reflection.check` → `TY`; `checkedTypeIs asBool` → the
   translation of `Nat.ble` is `.const ``Nat.ble`` []` by `trExprS_const_nil_inv`; the final
   `isDefEq e cond.dec` β-reduced at two numerals is `reflects_condApp_natLE`'s `hdec`.
4. `Reflection.checkITE` / `checkNatDITE` → `hsel`: one app-spine inversion plus
   `IsDefEqU.inst4`, since the executable reshaping of the previous session.
5. The two big `checkedIsDefEq`s of the branch, instantiated at numerals
   (`IsDefEqU.instNat` / `instNat2` for the `Nat` binders, `inst0` for `hy`, `fuel`, `h`), give
   `reflects_fuel_mod`'s `hgo` with `Ok b hy f x h := HasType hy (P·1·b) ∧ HasType h (P·(x+1)·f)`;
   `hK` is the well-typedness of the checked right-hand side, using `hprim.natSub` to turn
   `Nat.sub x y` into `natLit (x-b)` — which is why the branch requires `Nat.sub` present.
   **The left-hand sides here are the length-5 spines: this is where `trExprS_app5` is used.**
6. `preserves_glue` + `VEnv.primField_Nat_mod` / `_div`, exactly as the fifteen closed branches.

`Nat.div` is the same proof with `Nat.succ` as the wrapper.

Note that `.rest` is currently a bare `sorry` with **no branch skeleton at all** — the four
names are not yet dispatched.  Splitting it (previous handoff §6.3) is now worth doing *first*,
since the statement is true: the split keeps the census at 19 while turning `.rest` into a proof
with a single `sorry` under `Nat.gcd` / `Nat.bitwise`.

---

## 5. Two things the previous handoff got slightly wrong about the plumbing

### 5.1 (c) `unfoldNatWellFounded` — unchanged, and still the hard one

The previous session's §5 stands in full and is not repeated: the fixpoint equation of
`WellFounded.Nat.fix` is *propositional, not definitional* (`Nat.eager` exists precisely to make
it so), a `checkedIsDefEq` at it returns `false`, and the "produce it by a checked conversion"
recommendation would make the recognizer reject `Nat.gcd` and `Nat.bitwise`.  Machine-checked
there by a failing `rfl`.  The re-priced route is a fuel induction on the `Nat.rec` skeleton *at
numerals*, whose prerequisite is a `whnfCore.WF` / `unfoldDefinition.WF` returning a defeq
witness for the whole application alongside the syntactic result.  Nothing this session changed
that.  **Do not attempt it before `Nat.mod` / `Nat.div` land.**

### 5.2 Identifying translations: `TrExprS.unique`, not `trExprS_uniq`

`trExprS_uniq` (`Verify/Primitive.lean`) gives `c.IsDefEqU e₁ e₂`.  That is too weak for step 2
above, which has to conclude that `GO`'s type *is* a specific `VExpr` telescope so that
`trExprS_app5`'s `eᵢ` obligations can be discharged by `simp`.

The stronger tool exists: `TrExprS.unique` (`Verify/Typing/Lemmas.lean:2338`)

```lean
theorem TrExprS.unique (H : IsUnique e) (H1 : TrExprS env Us Δ e e₁)
    (H2 : TrExprS env Us Δ e e₂) : e₁ = e₂
```

`TrExprS.IsUnique` fails only at `.proj` (see the `unique'` proof: every other constructor
recurses, and `.lit` goes through `toConstructor`).  Every type and right-hand side the
recognizer builds is projection-free, so it always applies.  **[source, read off
`Verify/Typing/Lemmas.lean:2323–2340`]**

**The obstacle step 2 actually faces**, which no previous handoff named: the two `≤`
applications in the `go` telescope sit at *different binder depths* (`Nat.succ Nat.zero ≤ n`
under one binder, `Nat.succ x ≤ fuel` under four), while `checkedTypeIs` hands back the
translation `P` of `q(@LE.le Nat _)` at the *base* context.  So the inversion must first weaken
`P` under one and under four binders before `TrExprS.unique` can identify the occurrences.  For
`q(@LE.le Nat _)`, which is built from constants only, the weakening is the identity on the
abstract side, and `TrExprS.weakLam0` (used four times already in the `Nat.land` / `Nat.lor`
branches of `Boundaries.lean`) is the tool.  **That iterated weakening is the next concrete
piece of work**, and it is what makes step 2 more than a fifth `trExprS_arrow_inv`.
**[source]**

---

## 6. Unchanged

* The C++ comparison: **the C++ kernel has no primitive-definition recognizer at all**
  (measured), so every discrepancy here is a divergence by construction and there is no C++
  behaviour to match — only the accepted set, which the Arena measures.  §1.2's new check is
  therefore recorded in `divergences.md` and gated on the Arena, and nothing else.
* The executable reshaping of `Reflection.checkITE` / `checkNatDITE` / `Condition.check`
  (previous session §4), and its own divergence entry, are untouched.
* `reflects_fuel_go`'s `Ok : Nat → VExpr → Nat → Nat → VExpr → Prop` arity repair (previous
  session §1) is untouched.
* The `Nat.pow` / `Nat.shiftLeft` numeral-size divergence (`Lean4Lean/TypeChecker.lean`, not
  this stream's file) is recorded in `divergences.md` and unchanged.

## 7. Pick up first

1. Split `.rest` into its four named branches so `Nat.mod` / `Nat.div` can be proved
   independently and only `Nat.gcd` / `Nat.bitwise` reach a `sorry` (census stays 19).
2. §5.2's iterated weakening, then step 2 of §4 — the `go` telescope inversion.  Everything
   after it is assembly with `trExprS_app5` and the fuel lemmas that already exist.
3. (c) as re-priced in §5.1 — **do not** attempt the `checkedIsDefEq` route.

### Note for whoever touches `Verify/Typing/Expr.lean` next

`ReflectsNatBitwise`'s binder order (`∀ f g, env'.WF → …`, not `env ≤ env' → env'.WF → ∀ f g`)
is load-bearing for `Verify/Environment/Extension.lean:118`.  §1.3.
