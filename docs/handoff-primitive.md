# `checkPrimitiveDef.WF.rest` — the `Condition.check` interface, closed at both ends

Stream scope: `Lean4Lean/Verify/Typing/Expr.lean`, `Lean4Lean/Primitive.lean`,
`Lean4Lean/Verify/Primitive.lean`, `Lean4Lean/Verify/Environment/Boundaries.lean`
(`checkPrimitiveDef.WF.rest` only), and new files under `Lean4Lean/Verify/`.

Everything below is marked **[machine-checked]** (a `lake build`, a reachability scan, the sorry
census, the guards, or a Kernel Arena run produced it) or **[source]** (read off the code, or
argued).

| gate | before | after |
| --- | --- | --- |
| sorry census (`lake env lean scripts/sorry-census.lean`) | **19** | **19** **[machine-checked, both runs]** |
| `lake build` of `Verify.Primitive`, `Verify.Environment.Boundaries`, `Verify.Environment.Extension`, `Verify.Bridge` | green | green **[machine-checked]** |
| `Verify/Guard.lean` guards 1–3 | ✓ | ✓ **[machine-checked: 25 frozen axioms ✓; `kernel_sound` within whitelist ✓ (proof INCOMPLETE); cone gaps 54/54 ✓]** |
| Kernel Arena (`lean4lean-local`) | **185 / 6 / 0** | **185 / 6 / 0** **[machine-checked; three full runs: baseline, after the `Condition.check`/`Reflection.check`/`Nat.bitwise` changes, after the `@ite`/`@dite` head-type checks]** |

`Lean4Lean/Primitive.lean` **did** change this session — five additions, all recorded in
`divergences.md` (the primitives bullet, "Seventh" and "Eighth").

---

## 0. Bottom line

1. **Finding 1 (`reflects_condApp`'s `hsel` may be undischargeable) is resolved, and it was
   worse than reported**: *three* of its inputs were unsuppliable, not one. All three are now
   closed, two of them by checks the recognizer was not making.
2. **Finding 2 (`Nat.bitwise` runs `Condition.check` under three binders) is resolved** by
   hoisting those two checks above the binders — accept-set neutral, no `weakN_iff`, no
   instantiation argument.
3. **A third, unreported defect was found and repaired: `VEnv.ReflectsCondApp` is the `ite`
   rule and only the `ite` rule, but `reflects_fuel_go` used it for a `dite`.** Its `hgo`/`hdite`
   pair could not have been supplied by the `Nat.mod` / `Nat.div` `go` equations. Both lemmas
   were restated and a `dite` counterpart added.
4. `Reflection.checkITE.WF` was **not** attempted. Everything it consumes and everything it must
   produce is now named and, where provable in isolation, proved — see §5.

---

## 1. Finding 1: the verdict, and the two hypotheses nobody had counted

### 1.1 The measurement that settled the route **[machine-checked]**

The previous handoff offered Route 1 (accept a dependency on `IsDefEqU.forallE_inv`, one of the
19) or Route 2 (strengthen `ReflectsCondApp`, re-checking three proved consumers). **Route 1, at
zero cost.** A forward-reachability scan over `ConstantInfo.value? (allowOpaque := true)` from
seed `Lean4Lean.checkPrimitiveDef.WF` (cone size 17594) reports:

```
YES  Lean4Lean.VEnv.IsDefEqU.forallE_inv
YES  Lean4Lean.VEnv.HasType.piUniq
YES  Lean4Lean.VEnv.IsDefEqU.weakN_iff
YES  Lean4Lean.TrProj.uniq / .weak'_inv
no   Lean4Lean.VEnv.NormalEq.descend, .const_forallE_inv, .sort_forallE_inv, .const_sort_inv, .const_app_inv
```

Same for `Lean4Lean.addDecl.WF`. So Π-injectivity is **already** in this branch's cone, via
`VEnv.HasType.piUniq` (`Verify/Typing/Lemmas.lean:26`). Using it here is inherited taint, not a
new hole, and the census stays at 19. Route 2 would have had to be re-checked against
`reflects_fuel_go`, `ReflectsCondApp.ofDefeq` and `reflects_natBitwise_go`; Route 1 changes
nothing downstream.

### 1.2 What was built **[machine-checked: builds; taint as marked]**

`Lean4Lean/Verify/Primitive.lean`:

| name | content | axioms |
| --- | --- | --- |
| `VExpr.WF.app_arg_typed` | one application step **with the head's Π-type known**: returns the *declared* domain, where `VExpr.WF.app_inv` returns an existential one | inherited `sorryAx` (via `piUniq`) |
| `VEnv.condApp_typed'` | the general four-argument version: `HasType F (∀ A₀ A₁ A₂ A₃, R)` + `WF (condApp F c i t e)` ⟹ all four arguments typed at the declared domains, each instantiated by its predecessors. **No closedness, no shape assumption** — `dite`, whose branch domains `c → Nat` / `¬c → Nat` depend on `c`, needs this | inherited |
| `VEnv.condApp_typed` | the `ite` specialisation, branch domains a closed `Aα` | inherited |
| `VEnv.reflects_condApp` | restated: `hsel` now takes **four typing hypotheses instead of a `VExpr.WF`**, and they are *exactly* `IsDefEqU.inst4`'s four | inherited |
| **`VEnv.hsel_of_checkITE`** | **the acceptance test**: builds the new `hsel` from the shape `Reflection.checkITE` actually leaves — an `IsDefEqU` in context `[Aα, Aα, RT (bvar 0) (boolLit v), .sort .zero]` — by `IsDefEqU.inst4`, with every closedness side condition derived from the typings (`VExpr.WF.closedN` at the empty context) | **`sorryAx`-free** |

Why this closes the finding and the old statement did not: `hsel`'s four typings are `inst4`'s
four *on the nose* (`p : .sort .zero`; `H : (RT·p)·(boolLit v)`, i.e. `A.inst p 0`; `t`, `e : Aα`,
i.e. `B.inst p 1` and `C.inst p 2`). `hsel_of_checkITE` is what turns "the shape looks right"
into a proof.

### 1.3 **The correction: `hsel` was one of three, not one** **[source, then closed by construction]**

Auditing `reflects_condApp`'s *own* hypotheses the same way turned up two more that nothing in
the recognizer could supply.

* **`hF` — the conditional head's type.** `condApp_typed` needs `HasType F (∀ (c : Prop), Dc c →
  Aα → Aα → Aα)`. `F` is the translation of `q(@ite.{1}) α`, and the recognizer only ever put
  `@ite` inside a `checkedIsDefEq`, which type-checks the *application* and so yields existential
  domains again. **Fix: `Reflection.checkITE` (and the `.bool` arm of `Condition.check`) now
  `checkedTypeIs q(@_root_.ite.{1}) q(∀ (α : Type) (c : Prop), Decidable c → α → α → α)`, and
  `Reflection.checkNatDITE` now checks `@dite Nat` likewise.**
* **`hPR` — the reflection proof's type.** `reflects_condApp` instantiates the selection equation
  at `H := proof a b`, which needs `HasType (PR·a·b) ((RT·(P·a·b))·(boolLit (g a b)))`. The
  recognizer checked only `isProp (← checkType proof)`. The typing is **not recoverable**:
  `checkType e` (on `fun x y => toDec (prop x y) (asBool x y) (proof x y)`) gives a `TrExprS`
  whose `.app` rule hands back the domain the application invented; pinning it needs `toDec`'s
  declared telescope, which nothing checks; and `toDec`'s telescope readable off `checkITE` lives
  under different binders, so relating the two needs `IsDefEqU.weakN_iff` (open). **Fix:
  `Condition.check`'s `.reflectNatNat` arm now `checkedTypeIs proof (∀ n m : Nat, reflect.type
  (cond.prop n m) (asBool n m))`.**

Both are strictly stricter checks; both leave the Arena at 185/6/0 **[machine-checked]**.

The verification side of `hPR` is built and `sorryAx`-free **[machine-checked]**:

| name | content |
| --- | --- |
| `trExprS_weakBV0` | a *closed* term's translation is unchanged under a `(none, .vlam A)` entry — `TrExprS.weakBV` + `Expr.liftLooseBVars_eq_self` + `ClosedN.liftN_eq`. The `_inv'` family above it all invert constant-only terms; this is the general fact, and it is what lets `Reflection.type` / `Condition.prop` / `asBool` be recognised inside a `∀ n m : Nat, …` |
| `trExprS_reflProofType_inv'` | inverts the translation of `∀ n m : Nat, rty (prp n m) (asB n m)` to `.forallE .nat (.forallE .nat ((RT·((P·bvar1)·bvar0))·((B·bvar1)·bvar0)))`, given `IsUnique` + closedness of the three abstract sub-terms |
| `VEnv.reflProof_inst` | reads that at a pair of numerals: `HasType (PR·a·b) ((RT·(P·a·b))·(B·a·b))` |

`Reflection.check.WF` was extended to also return `∃ TD TDA, TrExprS r.toDec TD ∧ HasType TD TDA`
at the **base** context, matching the new `_ ← checkType r.toDec`.

---

## 2. Finding 2, resolved by moving the check rather than the fact

`Nat.bitwise` ran `Condition.natEq.check` and `Condition.bool.check` *inside* the `f` / `n` / `m`
binders, so their facts arrived at `toCtx = [Nat, Nat, Bool → Bool → Bool]` while
`ReflectsCondApp` lives at `0 []`. Both conditions and both `iteTypes` lists are **closed**, so
neither check reads or binds those variables: the two calls now run above the binders.
Accept-set neutral (only the error ordering changes); Arena unchanged **[machine-checked]**.

The previously recommended workaround — instantiating at closed inhabitants `HasPrimitives`
supplies — is no longer needed and should not be built.

---

## 3. **New finding: `ReflectsCondApp` is the `ite` rule, and `reflects_fuel_go` used it for a `dite`** **[source; the repair is machine-checked]**

`Condition.dite` (`Lean4Lean/Primitive.lean`) builds

```
mkApp4 q(@dite Nat) (prop args) (dec args) (.lam0 (prop args) t) (.lam0 (Not (prop args)) e)
```

— both branches are **λs over the decision's proof** — and `@dite`'s reduction *applies* the
selected λ to that proof: `Reflection.checkNatDITE` checks `dite p (toDec p true H) a b ≡
a (ofTrue p H)`, **not** `≡ a`.

`VEnv.ReflectsCondApp F P D g` asserts `condApp F … t e ≡ bif g a b then t else e`. That is the
`ite` rule. `reflects_fuel_go` took it as `hdite` and stated `hgo`'s right-hand side as a
`condApp` whose branch slots were `wrap (VExpr.app5 GO …)` and `base x` — with `hbase` forcing
the `e` slot to be **syntactically** `.natLit (sem x b)`. The `Nat.mod` and `Nat.div` `go`
equations are `c.dite #[y, x] … x` (`Lean4Lean/Primitive.lean`), so the slots are λs. **`hgo`
could not have been supplied.** The lemma is true; its hypothesis was unreachable — the same
failure mode as finding 1, one level up, and the reason to audit suppliers as well as consumers.

Repair, all **[machine-checked: builds]**:

* `reflects_fuel_go` now takes an abstract right-hand side `RHS : Nat → Nat → Nat → VExpr →
  VExpr → VExpr` and a separate `hsel` saying *that* term selects
  (`if b ≤ x then wrap (app5 GO …) else base x`). The conditional is gone from the induction.
  `reflects_fuel_mod` / `_div` follow suit; their `hdite` argument is dropped.
* `VEnv.ReflectsCondAppD F P D OT OF PR g` — the `dite` rule, with the selected branch **applied**
  to `OT·(P·a·b)·(PR·a·b)` (resp. `OF`).
* `VEnv.reflects_condAppD` — the `reflects_condApp` proof for it; its `hsel` keeps the `VExpr.WF`
  premise plus `H`'s typing, because the branch domains depend on `c` and its supplier will
  recover them with `condApp_typed'` from `@dite Nat`'s (now checked) type.
* `VEnv.ReflectsCondAppD.natLE_le` — the `b ≤ x` reading, the form `reflects_fuel_go`'s `hsel`
  wants.

`ReflectsCondApp` keeps a live consumer: `reflects_natBitwise_go`, whose equation really is an
`ite` **[machine-checked: still builds]**.

---

## 4. Executable changes, and why each one is not decoration

All five are in `divergences.md`. Arena **185 / 6 / 0** before and after **[machine-checked]**.

| # | change | accept set |
| --- | --- | --- |
| 1 | `Reflection.check`: `_ ← checkType r.toDec` | **neutral** — `toDec` is a subterm of every term already handed to `checkType` |
| 2 | `Reflection.checkITE` + `Condition.check`'s `.bool` arm: `checkedTypeIs q(@ite.{1}) …` | **stricter** |
| 3 | `Reflection.checkNatDITE`: `checkedTypeIs q(@dite Nat) …` | **stricter** |
| 4 | `Condition.check` `.reflectNatNat`: `checkedTypeIs proof (∀ n m : Nat, r.type (prop n m) (asBool n m))` | **stricter** |
| 5 | `Nat.bitwise`: the two `Condition.check` calls hoisted above `f`/`n`/`m` | **neutral** (reorder) |

The general principle, worth keeping: **the verification can never recover a subterm's type from
the fact that an application containing it type-checks.** `TrExprS.app` and `VExpr.WF.app_inv`
both hand back the domain the application *invented*, existentially quantified. If the abstract
statement needs a declared type, the recognizer has to check it.

---

## 5. Pick up first

1. **`Reflection.checkITE.WF`.** Everything it consumes now exists. Its shape:
   four `M.WF.withCheckedLocalDecl`s (`p : Prop`, `H : r.type p true`, `t e : α`), then
   `checkedIsDefEq.WF`, then a five-fold app-spine inversion of
   `mkApp5 q(@ite.{1}) α p (mkApp3 r.toDec p q(true) H) t e`.
   * `@ite.{1}` is pinned by `trExprS_const_inv'` — no uniqueness needed.
   * the `p`, `H`, `t`, `e` positions are pinned outright (`TrExprS.fvar` reads a deterministic
     `VLCtx.find?`; `trExprS_lastFVar0` / `hasType_fvar1` are the existing tools).
   * `α` and `r.toDec` are abstract `Expr`s: identify their in-context translations with the
     base ones by `TrExprS.weakLam0` (needs `ClosedN 0`, from `closedN_of_nil`) plus
     `TrExprS.unique` (needs `IsUnique`, structural and `simp`-dischargeable at a concrete
     `q(…)`). Take `Aα`, `TD`, `IsUnique α`, `IsUnique r.toDec` as **hypotheses** — the base
     `TD` now comes from `Reflection.check.WF`, which is why `checkType r.toDec` was added.
   * the **`true` and `false` halves are separate binder blocks**, so their contexts differ in
     the `H` domain only: compare across them with `TrExprS.unique'` + `IsUniqueCtx`, not
     `TrExprS.unique`.
   * the output feeds `hsel_of_checkITE` directly. Do not re-derive the instantiation.
   * add the `@ite` type check's own reading (`hF`) to the postcondition — `checkedTypeIs.WF'`
     plus an inversion of `∀ (α : Type) (c : Prop), Decidable c → α → α → α`.
2. **`Reflection.checkNatDITE.WF`**, same shape, feeding `reflects_condAppD`; the branch domains
   come from `condApp_typed'` and `@dite Nat`'s checked type.
3. **`Condition.check.WF`** on top: `checkType cond.dec`, `checkedTypeIs cond.prop (Nat→Nat→Prop)`,
   `Reflection.check.WF` (done), the two above, `checkType e`, `checkedTypeIs asBool`, the new
   `checkedTypeIs proof …` (→ `trExprS_reflProofType_inv'` → `reflProof_inst` → `hPR`), and
   `isDefEq e cond.dec` (→ `hdec`, after `IsDefEqU.instNat2` at the two numerals).
4. Then the `Nat.mod` / `Nat.div` assembly: `trExprS_app5`, `reflects_fuel_mod` / `_div` in their
   **new** form, `preserves_glue`, `VEnv.primField_Nat_mod` / `_div`.
5. `unfoldNatWellFounded` last, and **not** by a checked conversion — §5.1 of the previous
   handoff stands verbatim: the `WellFounded.Nat.fix` fixpoint equation is propositional, not
   definitional, so a `checkedIsDefEq` there returns `false` and the recognizer would *reject*
   `Nat.gcd` and `Nat.bitwise`.

---

## 6. Carried over, still correct

* `trExprS_goType_inv'` and its nine supporting inversions: sorry-free, used in situ in the
  `Nat.mod` branch **[machine-checked]**. The "iterated weakening under one and four binders"
  that an older handoff prescribed remains dead work — `@LE.le Nat instLENat` is closed and
  constant-only.
* `VEnv.ReflectsNatBitwise` / `ReflectsBoolBoolBool` binder order is load-bearing for
  `Verify/Environment/Extension.lean:118`, which consumes it **positionally**. Not touched;
  `Extension.lean` and `Bridge.lean` both still build **[machine-checked]**.
* The C++ kernel has **no primitive-definition recognizer at all**, so every discrepancy here is
  a divergence by construction and the Arena's accepted set is the only external constraint.
* `reflects_condApp` still has **no consumer** in the tree; `Condition.check.WF` will be the
  first. Its hypotheses are now all *demonstrably* suppliable (§1.2, §1.3), which is the thing
  that was missing.

## 7. Method note

Two of this session's three findings were "a proved lemma whose hypothesis cannot be produced".
Neither is visible from the statement, and neither is caught by a non-vacuity check — the
hypotheses are all satisfiable in the abstract, just not by the recognizer. The instrument that
found both was the same: **write the supplier's side and see what it holds at the moment it must
produce the hypothesis.** `hsel_of_checkITE` exists for exactly that reason and should be the
template — every hypothesis of a `Reflects*` lemma deserves one.
