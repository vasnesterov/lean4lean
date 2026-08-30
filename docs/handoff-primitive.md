# `checkPrimitiveDef.WF.rest` — `Nat.mod` and `Nat.div` are closed

Stream scope: `Lean4Lean/Verify/Typing/Expr.lean`, `Lean4Lean/Primitive.lean`,
`Lean4Lean/Verify/Primitive.lean`, `Lean4Lean/Verify/Environment/Boundaries.lean`
(`checkPrimitiveDef.WF.rest` only), and new files under `Lean4Lean/Verify/`.

Everything below is marked **[machine-checked]** (a `lake build`, the sorry census, the guards,
`scripts/dup-names.lean`, `#print axioms`, or a Kernel Arena run produced it) or **[source]**
(read off the code, or argued).

| gate | before | after |
| --- | --- | --- |
| sorry census (`lake env lean scripts/sorry-census.lean`) | **19** | **19** **[machine-checked, both runs]** |
| `checkPrimitiveDef.WF.rest`'s open branches | 4 (`mod`, `div`, `gcd`, `bitwise`) | **2** (`gcd`, `bitwise`) **[machine-checked]** |
| `lake build` (whole tree) | green | green **[machine-checked]** |
| `Verify/Guard.lean` guards 1–3 | ✓ | ✓ **[machine-checked: 25 frozen axioms ✓; `kernel_sound` within whitelist ✓ (proof INCOMPLETE); cone gaps 54/54 ✓; `stdPrelude accepted by addDecl ✓`]** |
| `scripts/dup-names.lean` | — | no duplicates **[machine-checked]** |
| Kernel Arena (`lean4lean-local`) | **185 / 6 / 0** *(carried; `Primitive.lean` unchanged, so before = after by construction)* | **185 / 6 / 0** **[machine-checked, two full runs]** |

**`Lean4Lean/Primitive.lean` is byte-for-byte unchanged this round.** No executable change, so
no new entry in `divergences.md`.

---

## 0. Bottom line

1. **The `Nat.mod` branch of `checkPrimitiveDef.WF.rest` is proved.** §1.
2. **The `Nat.div` branch is proved.** §2.
3. **A hypothesis of an already-proved lemma was *not suppliable* and had to be repaired**:
   `VEnv.reflects_fuel_go`'s `hK`. §3. This is the same failure family as the `Ok`-indexing
   defect the previous handoff recorded, found the same way (write the supplier's side).
4. `Nat.gcd` and `Nat.bitwise` are untouched and still blocked at `unfoldNatWellFounded`. §6.
   Kernel Arena is **185 correct / 6 either / 0 incorrect**, twice. Since `Lean4Lean/Primitive.lean`
   is byte-for-byte unchanged this round, the executable is unchanged and the accepted set could
   not have moved; the runs are a check on that reasoning, not a measurement of a change.
5. The census does **not** move: `checkPrimitiveDef.WF.rest` is one declaration, and two of its
   four branches still carry `sorry`. It will read 18 only when all four close.

---

## 1. The `Nat.mod` branch **[machine-checked]**

The whole chain, in `Lean4Lean/Verify/Primitive.lean` unless noted.

### 1.1 Reading the two equations back

The recognizer compares
```
mod (succ x) y   ≡  c.ite Nat #[y, succ x] (c.dite #[1, y] (go y _ (succ (succ x)) (succ x) _) (succ x)) (succ x)
go y hy (succ fuel) x h  ≡  c.dite #[y, x] (go y hy fuel (sub x y) (div_rec_fuel_lemma …)) x
```
under `withCheckedLocalDecl` binders.  Both right-hand sides mention constants whose types
`VEnv.HasPrimitives` does not pin — `Not`, `Nat.lt_succ_self`, `Nat.div_rec_fuel_lemma` — so
neither translation can be *built*; it is read off `checkedIsDefEq.WFr` and inverted.

| name | content |
| --- | --- |
| `VExpr.iteNat`, `VExpr.diteNat` | `@ite.{1} Nat`, `@dite.{1} Nat` |
| `trExprS_iteNat_inv'`, `trExprS_diteNat_inv'` | both heads pinned **syntactically**, by `trExprS_const_inv'`.  No `TrExprS.unique` and therefore **no `IsUnique` side condition** for them — one fewer vacuity surface than `Reflection.checkITE`'s `α` |
| `trExprS_fvar_uniq` | `IsUnique (.fvar _)` is `True`, so `TrExprS.unique` pins a free variable's translation outright.  This is what makes the whole inversion possible without `IsDefEqU.weakN_iff` |
| `trExprS_liftBV0` | the **lifting** counterpart of `trExprS_weakBV0`: weakening past one anonymous `.vlam` while *lifting* the abstract term.  `trExprS_weakBV0` needs `e'.ClosedN 0`, which a bound variable does not have; this is what carries `x`, `y`, `hy`, `fuel` under the λ that `Condition.dite` wraps its branches in |
| `trExprS_succFvar_inv'` | `Nat.succ` applied to a free variable |
| `trExprS_modEq1_inv'` | the first equation's RHS, leaving exactly `EA1` (the `Not`-typed binder domain) and `LT1` (the `Nat.lt_succ_self` witness) abstract |
| `trExprS_modEq2_inv'` | the `go` equation's RHS, parametrised by the recursion's constant name so `Nat.div` reuses it; leaves `EA2`, `K2` abstract |

### 1.2 Building the equation's left-hand side

`TypeChecker.trExprS_goApp` builds `TrExprS (mkApp5 go y hy fuel x h)` from the declared
telescope `checkedTypeIs q(Nat.modCore.go)` pins.  Its five `B.inst` side conditions are `simp`
identities; the only interesting one is the fifth, which needs `VExpr.inst_lift` because
`go`'s last domain mentions the *fuel* argument.  `VExpr.closedN_goType` is the closedness
`HasType.weakLam0` needs to carry `HasType go .goType` under the five binders.

### 1.3 Instantiating at numerals

* `VEnv.goCtx` — the five-binder context `[h, fuel, hy, y, x]` the `go` equation is checked in.
* `VEnv.IsDefEqU.instGo5` — substitutes `x := natLit x`, `y := natLit b`, `hy`, `fuel := natLit f`,
  `h`, in that order (outermost first, exactly as `IsDefEqU.inst4` does).  The two *proof*
  binders are substituted by terms the caller supplies with their typings; **nothing about their
  types is needed beyond that**, which is what keeps the induction independent of the branch's
  plumbing.
* `VEnv.mod_step1` (via `IsDefEqU.instNat2`) and `VEnv.mod_step2` (via `instGo5`) deliver the two
  equations at numerals in exactly the shape the fuel induction consumes.

### 1.4 Getting past the two λs

`VEnv.diteNat_reduce` is the new step: `ReflectsCondAppD` delivers the selected λ **applied** to
the decision proof, and this reduces it.  It needs no typing from the caller —
`VEnv.IsDefEqU.beta_wf` recovers the argument's declared domain from the redex's own
well-typedness via `VExpr.WF.app_arg_typed`.

### 1.5 The `Nat.sub` congruence

The recognizer's recursive call carries `Nat.sub x y`, while `reflects_fuel_mod`'s induction
hypothesis is at the numeral `x - y`.  `VEnv.IsDefEqU.app2_congr_arg1'` makes the swap in a
position whose *successor* argument's type depends on it (the fuel proof `h : x+1 ≤ f`), which
is why the plain `app_congr_arg` family does not suffice.  The typings it needs come from
`VEnv.goApp3_typed` / `VEnv.goApp5_typed`; `hprim.natSub` supplies the defeq, and the branch's
`env.contains ``Nat.sub` guard reaches `c.venv.contains` through `contains_primConst` and the
new `TypeChecker.primitives_natSub`.

### 1.6 Assembly

`VEnv.reflects_mod_of_equations` takes exactly what the branch produces — `h0`, the two
equations, `ReflectsCondApp` / `ReflectsCondAppD` at `.iteNat` / `.diteNat`, and `HasType go
.goType` — and returns `∀ a b, F a b ≡ natLit (a % b)`.  Everything happens at `c.venv`; the
transport to the extension `env₂` is one `IsDefEqU.mono` at the end.  **That ordering is
forced**: `ReflectsCondApp` has a `VExpr.WF` premise in a *negative* position, so it is not
monotone, and any attempt to carry it into `env₂` first is dead.

The `Ok` predicate the induction runs under is
```
Ok b hy f x h  :=  HasType hy (1 ≤ b)  ∧  HasType h (x+1 ≤ f)
```
— the fuel/numerator indexing the previous handoff established, with the two typings that
`goApp_typed` extracts from the applications' own well-typedness.

## 2. The `Nat.div` branch **[machine-checked]**

Same chain, three structural differences, all forced by the recognizer:

* `iteTypes := []`, so only the `ReflectsCondAppD` half of `Condition.check.WF_natLE_pinned` is
  used and `hitefv` is discharged by `absurd hα (by simp)`;
* `Condition.natLE.check` runs **before** the two `checkedTypeIs`, so the proof meets them in
  the opposite order to `Nat.mod`'s;
* there is **no outer `ite` and no `div 0 x` base case**: `Nat.div.go` at fuel `x+1` already
  returns `0` when the divisor exceeds the numerator, so the single equation
  `div x y ≡ dite (1 ≤ y) (go y _ (succ x) x _) 0` covers every numerator.  `Nat.succ` is the
  fuel recursion's wrapper and `0` its exhausted branch.

New: `trExprS_divEq1_inv'`, `trExprS_divEq2_inv'`, `VEnv.div_step1`, `VEnv.div_step2`,
`VEnv.reflects_div_of_equations`.

## 3. Correction: `reflects_fuel_go`'s `hK` was not suppliable **[machine-checked, by construction]**

The lemma was proved last round with

```
(hK : ∀ b f x hy h, Ok b hy (f+1) x h → Ok b hy f (x - b) (K b f x hy h))
```

**This cannot be supplied.**  `Ok b hy f (x-b) K`'s second conjunct is
`HasType K (natLEApp (natLit (x-b+1)) (natLit f))`.  The only source of that typing is the
well-typedness of the recursive application `go b hy f (x-b) K`, and that application occurs in
the recognizer's term **only inside the `b ≤ x` branch of the `dite`**.  When `¬ b ≤ x` the
recognizer's right-hand side is the fuel-exhausted branch (`x` for `mod`, `0` for `div`); there
is no `go` application at all, and the type `x-b+1 ≤ f` is in general uninhabited.  So the
un-guarded `hK` is empty at every real call site, and any proof depending on it would be
consuming a vacuous obligation.

The repair is free: `reflects_fuel_go`'s own proof uses `hK` **only** inside its `by_cases
hbx : b ≤ x` positive branch.  `hK` now reads

```
(hK : ∀ b f x hy h, Ok b hy (f+1) x h → b ≤ x → Ok b hy f (x - b) (K b f x hy h))
```

in `reflects_fuel_go`, `reflects_fuel_mod` and `reflects_fuel_div`.  Adding a hypothesis to a
hypothesis makes the lemma **stronger**, so nothing downstream is weakened; all three still
build.  **The refutation dies at its own witness**: with `b ≤ x` in hand, `hsel`'s output in the
positive branch gives `VExpr.WF (go b hy f (x-b) K)` and `goApp5_typed` reads the typing off it.

This is the third statement in this development found unsuppliable by *writing the supplier's
side* rather than by reasoning about the statement.  Put that instrument in every brief.

## 4. Method notes that cost time

1. **`rw [if_pos h]` rewrites only the first matching `if`.**  Both sides of an `IsDefEqU` carry
   one after `ReflectsCondAppD.natLE_le`; use `simp only [if_pos h]`.
2. **`ClosedN.liftN_eq (Nat.zero_le 0)` pins the depth to `0`.**  Where the instantiation depth
   varies (under a λ it is `k+1`), it must be `(Nat.zero_le _)`.  Two `simpa`s failed on exactly
   this and the error looks like a shape mismatch, not like a depth mismatch.
3. **`mkAppB` is not reached by unfolding `mkApp2`.**  `FVarsIn` goals over
   `Condition.natLE.dite …` need `Lean.mkAppB` in the simp set as well as `Lean.mkApp2`,
   `Lean.mkApp4`, `Lean.mkApp5`, `Lean.mkApp6`, `Lean.mkAppN` and `Lean.Expr.lam0`.
4. **The `FVarsIn` side conditions are best discharged structurally**, not by feeding
   `h.fvarsIn` to `simp` (it is stated as `Expr.FVarsIn`, and `simp` unfolds that first, so the
   fact never fires).  `repeat' apply And.intro` then
   `all_goals first | exact hxv5.fvarsIn | … | trivial | simp [FVarsIn, Lean.Level.hasMVar']`.
5. **The last `unless … do fail` inside the binder block has no continuation**, so its `isFalse`
   case is `.throw`, not `M.WF.bindThrow .throw`.  Every earlier one is `bindThrow`.
6. **`return true` sits outside all five `withCheckedLocalDecl`s.**  The reflection fact has to
   leave the binders through the *outermost* `withCheckedLocalDecl`'s postcondition
   (`Q := fun _ _ => ∀ a b, …`), which is context-free and so passes through unchanged.
7. **`hasType_lastFVar`, not `hasType_lastFVar0`**, when the binder's domain is not closed
   (`1 ≤ y`, `x+1 ≤ fuel+1`).  The `0` variant demands `ty'.ClosedN 0`.
8. **`set_option … in` goes before the doc comment**, not between the doc comment and the
   theorem.  `checkPrimitiveDef.WF.rest` now needs `maxHeartbeats 4000000` (45 s to elaborate).

## 5. Non-vacuity

* The `Nat.mod` and `Nat.div` branches now *produce* `PrimitiveResult`'s `preserves` field, i.e.
  `VEnv.PrimField ``Nat.mod` / ``Nat.div``, at the accepting path.  `Verify/Soundness.lean`'s
  `stdPrelude accepted by addDecl ✓` witnesses that this path is reached at the real
  declarations. **[machine-checked]**
* Every hypothesis of `reflects_mod_of_equations` / `reflects_div_of_equations` is discharged in
  `Boundaries.lean` from the recognizer's own checks; none is assumed. **[machine-checked]**
* `IsUnique` never appears for the two conditional heads (§1.1), so the `IsUnique`-at-a-`.proj`
  vacuity risk the previous handoff flagged is *narrower* than before, not wider.

## 6. Pick up first

1. **`Nat.gcd`**, blocked at `unfoldNatWellFounded`, unchanged.
2. **`Nat.bitwise`**, blocked at `unfoldNatWellFounded`, and additionally consuming
   `Condition.check.WF_natEq` (at `Nat` and `Bool`) and `WF_boolCond` (at `Nat`), both of which
   are already proved.
3. `unfoldNatWellFounded` **not** by a checked conversion: the `WellFounded.Nat.fix` fixpoint
   equation is propositional, not definitional, so a `checkedIsDefEq` there returns `false` and
   the recognizer would *reject* `Nat.gcd` and `Nat.bitwise`.  This has now survived six
   handoffs unchanged. **[source]**
4. The two `Nat.mod` / `Nat.div` chains are close to a template.  If a third fuel recursion
   ever appears, `trExprS_modEq2_inv'` is already parametrised by the `go` constant's name and
   `reflects_fuel_go` by the wrapper, base and recurrence.

## 7. Carried over, still correct **[machine-checked unless noted]**

* `TypeChecker.Condition.check.WF` (both arms), `Reflection.check.WF`, `checkITE.WF`,
  `checkNatDITE.WF`, `Condition.check.WF_bool`, and the acceptance instances
  `WF_natLE` / `WF_natEq` / `WF_boolCond` / `WF_natLE_pinned` are unchanged and still used.
* Π-injectivity here is **inherited taint, not a new hole**: `VEnv.IsDefEqU.forallE_inv` and
  `VEnv.HasType.piUniq` are inside `checkPrimitiveDef.WF`'s forward cone.  Every new lemma's
  axiom set is a subset of `{propext, sorryAx, Classical.choice, Quot.sound}`; the four
  inversion lemmas and the four `…_step` lemmas carry **no `sorryAx` at all**. **[machine-checked]**
* `ReflectsCondApp` is the `ite` rule only; the `go` equations are `dite`s and use
  `ReflectsCondAppD`.  `ReflectsCondApp`'s live consumers are now `reflects_natBitwise_go` and
  the `Nat.mod` branch.
* **No cross-half comparison is ever needed.**  `TrExprS.unique'` and `IsUniqueCtx` appear
  nowhere in this development.
* The C++ kernel has **no primitive-definition recognizer at all** (measured), so every
  discrepancy here is a divergence by construction and the Arena's accepted set is the only
  external constraint.
* **The verification can never recover a subterm's type from the fact that an application
  containing it type-checks.**  `TrExprS.app` and `VExpr.WF.app_inv` hand back the domain the
  application *invented*.  If the abstract statement needs a declared type, the recognizer has
  to check it, in the *shape* the abstract statement consumes.  `trExprS_goApp` is this round's
  instance: it exists only because `checkedTypeIs q(Nat.modCore.go)` pins the telescope.
* `Verify/Environment/Extension.lean:118` consumes `ReflectsNatBitwise` **positionally**.  Not
  touched this round; `Extension.lean` and `Bridge.lean` both still build. **[machine-checked]**
