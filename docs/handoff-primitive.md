# `checkPrimitiveDef.WF.rest` — state, two statement defects, and the (c) correction

Stream scope: `Lean4Lean/Primitive.lean`, `Lean4Lean/Verify/Primitive.lean`,
`Lean4Lean/Verify/Environment/Boundaries.lean`, new files under `Lean4Lean/Verify/`.
Everything below is separated into **[machine-checked]** (a `lake build`, an `#print axioms`,
a `lean_minimal_hypotheses` run, or a Kernel Arena run produced it) and **[source]** (read off
the code or argued, not proved).

Census: **19 before, 19 after** **[machine-checked, both runs]**.  Kernel Arena: **185 correct
/ 6 either / 0 incorrect before and after** **[machine-checked, both runs]**.

---

## 0. Bottom line

Three things this session found that the previous handoffs got wrong, and one thing that
closed:

1. **`VEnv.reflects_fuel_go`'s `Ok` had the wrong arity** and the lemma was therefore *true but
   unusable*: any `Ok` making its `hgo` provable is empty.  Fixed in place; §1.
2. **`VEnv.ReflectsNatBitwise` (`Verify/Typing/Expr.lean`) is not provable as stated**, so
   `checkPrimitiveDef.WF.rest` is **false at its `Nat.bitwise` branch**, not merely open.  Two
   hypotheses are missing, both of them things the conclusion itself needs.  §3.
3. **The standing recommendation for (c) cannot work.**  "Change `unfoldNatWellFounded` to
   produce its equation by a checked conversion" is impossible: the fixpoint equation of
   `WellFounded.Nat.fix` is *propositional, not definitional*, deliberately so.  §5.
   Machine-checked by a failing `rfl`.
4. **(d) is closed as metatheory**: `VEnv.reflects_natBitwise_go`, the `Nat.bitwise` recursion,
   is proved, together with the conditional machinery it needs.  §2.

Plus one executable change that removes the largest single piece of the remaining plumbing,
Arena-gated at 185/6/0: §4.

---

## 1. `reflects_fuel_go`'s `Ok` — a statement that carried less than its conclusion needed

`Verify/Primitive.lean` **[machine-checked: builds]**.  The previous session stated

```
{Ok : Nat → VExpr → VExpr → Prop}
(hgo : ∀ (b f x : Nat) (hy h : VExpr), Ok b hy h → IsDefEqU (app5 GO b hy (f+1) x h) …)
(hK  : ∀ b f x hy h, Ok b hy h → Ok b hy (K b f x hy h))
```

`hgo`'s left-hand side is `Nat.modCore.go b hy (f+1) x h`, and `IsDefEqU` entails
well-typedness, so `h` must have type `x+1 ≤ f+1` **for these particular `f` and `x`**.  A
three-argument `Ok` cannot say that: it is carried unchanged across the recursive call, where
the fuel is `f` and the numerator `x - b`, and a proof of `x+1 ≤ f+1` is not a proof of
`x-b+1 ≤ f`.  So every `Ok` strong enough to make `hgo` provable is empty, and the conclusion
is vacuous at every call site.  **[source, argued; the fix is machine-checked]**

Repaired to `Ok : Nat → VExpr → Nat → Nat → VExpr → Prop` (`Ok b hy f x h`), with
`hgo … (Ok b hy (f+1) x h)` and `hK … → Ok b hy f (x - b) (K b f x hy h)`.  The induction is
unchanged — `hK` steps the indices down exactly as the recursive call does — and the shape the
`Nat.mod` / `Nat.div` branches can actually supply is
`Ok b hy f x h := HasType hy (1 ≤ b) ∧ HasType h (x+1 ≤ f)`.  `reflects_fuel_mod` and
`reflects_fuel_div` inherit the change.  The reasoning is recorded in the section docstring.

---

## 2. (d) `Nat.bitwise` — closed as metatheory

New in `Verify/Primitive.lean`, all sorry-free modulo the standing `IsDefEqU.trans` /
`weakN_iff` taint that every existing `reflects_*` lemma in the file already carries
(`#print axioms` identical to `reflects_natAdd`'s) **[machine-checked]**:

| declaration | content |
| --- | --- |
| `VExpr.app2'`, `VExpr.natOp` | the two application shapes the equation is built from |
| `VExpr.WF.app2_fn/arg1/arg2`, `.condApp_cond/_inst/_t/_e` | well-typedness peeling |
| `IsDefEqU.app2_congr_args`, `.condApp_congr_cond` | the congruences |
| `ReflectsCondApp.ofDefeq` | a `ReflectsCondApp` read at arguments that merely *reflect* numerals (`Nat.mod n 2`, not a literal) |
| `VEnv.ReflectsCondApp1`, `.ofDefeq` | **conditionals with one boolean scrutinee** — `Condition.bool`, used three times in the equation; no `Reflection` layer |
| `VExpr.bitParity`, `.bitwiseRec`, `.bitwiseRhs` | the checked right-hand side, at a pair of numerals |
| `VEnv.reflects_natOp`, `bif_boolLit`, `natBeq_eq_decide`, `reflects_bitParity` | supporting |
| **`VEnv.reflects_natBitwise_go`** | **the recursion** |

The induction is `Nat.strongRecOn` on the first argument (`n ≠ 0` in the recursive branch, so
`n / 2 < n`), not on `n + m` as the earlier note guessed; `m` stays universally quantified.
Every hypothesis is monotone under `env ≤ env'` (`NatLits`, three `ReflectsNatNatNat`s and
their `contains`) rather than a whole `HasPrimitives`, which is what the second-order field
needs, since the field gives no `HasPrimitives` for the extension.

**Non-vacuity / information-flow audit.**  `lean_minimal_hypotheses` reports **all thirteen
explicit hypotheses load-bearing**, none droppable **[machine-checked]**.  The conclusion is
therefore not derivable from any proper subset, and in particular not without `heq` — the one
equation the recognizer actually checks.

---

## 3. `ReflectsNatBitwise` is not provable as stated — so `.rest` is **false**, not open

**[source, argued; the repaired statements are machine-checked]**

`Verify/Typing/Expr.lean:241`:

```lean
def VEnv.ReflectsNatBitwise (env : VEnv) :=
  env.contains ``Nat.bitwise →
  ∀ (env' : VEnv), env ≤ env' → ∀ (f : VExpr) (g : Bool → Bool → Bool),
    env'.ReflectsBoolBoolBool f g → ∀ a b, env'.IsDefEqU 0 []
      (.app (.app (.app (.const ``Nat.bitwise []) f) (.natLit a)) (.natLit b))
      (.natLit (Nat.bitwise g a b))
```

Two hypotheses are missing.

### 3.1 The combinator's type — and this one makes the conclusion **false**

`IsDefEqU` entails well-typedness, so the conclusion *asserts* that `f` may be applied at
`Nat.bitwise`'s domain, i.e. `env'.HasType 0 [] f (Bool → Bool → Bool)`.  (Formally:
`HasType (Nat.bitwise · f) T` forces `HasType (.const ``Nat.bitwise`` []) (.forallE A B)` with
`HasType f A`, and the constant rule plus `IsDefEqU.forallE_inv` give
`A ≡ Bool → Bool → Bool` once `Nat.bitwise`'s own type is pinned, which the branch's
`checkPrimValue` does.)

The only hypothesis about `f` is `ReflectsBoolBoolBool f g`, which says `f` applied to two
boolean *literals* reduces to a literal.  That does not give the typing.  Take `f : (x : Bool)
→ Q x` in an environment carrying `Q Bool.true ≡ Bool → Bool` and `Q Bool.false ≡ Bool → Bool`
and nothing about `Q` at a variable: `ReflectsBoolBoolBool f g` holds and `Nat.bitwise · f` is
ill-typed.  `env'` ranges over **arbitrary** extensions — no `VEnv.WF`, no restriction — so
nothing rules that environment out.

The repair loses no content: at any `f` without the typing the conclusion is already false, so
the strengthened statement covers every `f` at which the old one was not already false.

### 3.2 The extension's well-formedness

The proof of the field chains `IsDefEqU` steps, and `IsDefEqU.trans` requires `env.WF`.
`ReflectsNatBitwise` supplies `env ≤ env'` and nothing else, so no transitivity is available in
`env'` at all, and `f` is new in `env'` so nothing transfers from `env`.  This one is
*unprovable* rather than demonstrably false — the repo has no tool for chaining defeqs in a
non-well-formed environment — but it is equally blocking.

### 3.3 The exact edits, and what they cost elsewhere

Proved in this stream's file as `VEnv.ReflectsBoolBoolBoolT` and `VEnv.ReflectsNatBitwiseT`,
with `ReflectsNatBitwiseT.toWeak` showing the strengthened field still delivers the old one at
every `f` that carries the typing **[machine-checked]**.

**Edit 1 — `Lean4Lean/Verify/Typing/Expr.lean:232` (not this stream's file):**

```lean
def VEnv.ReflectsBoolBoolBool (env : VEnv) (f : VExpr) (g : Bool → Bool → Bool) :=
  env.HasType 0 [] f (.forallE .bool (.forallE .bool .bool)) ∧
  ∀ a b, env.IsDefEqU 0 [] (.app (.app f (.boolLit a)) (.boolLit b)) (.boolLit (g a b))
```

**Edit 2 — `Lean4Lean/Verify/Typing/Expr.lean:241`:** insert `env'.WF →` after `env ≤ env' →`
in `ReflectsNatBitwise`.

**Follow-through 1 — `Lean4Lean/Primitive.lean` (this stream's file, *not* made):** the
`Nat.land` / `Nat.lor` / `Nat.xor` branches must supply the new conjunct, and cannot: they know
only `HasType (Nat.bitwise · G) (Nat → Nat → Nat)`, and `HasPrimitives` does not pin
`Nat.bitwise`'s type.  Add to each of the three branches

```lean
unless ← checkedTypeIs and q(Bool → Bool → Bool) do fail
```

(`and` / `or` / `xor` being the destructured combinator).  It passes on the real prelude —
`Nat.land = Nat.bitwise and` with `and = Bool.and : Bool → Bool → Bool`.

**Follow-through 2 — `Verify/Primitive.lean` and `Verify/Environment/Boundaries.lean`:**
`reflectsBoolBoolBool_and` / `_or` / `_bne` gain the typing argument;
`reflects_natBitwiseApp` passes `henv` and the typing to `hbw`; the three closed branches in
`Boundaries.lean` thread the new check and pass `hGty.mono hle3` and `henv₂`, both of which are
already in scope there **[source, read against `Boundaries.lean:689–777`]**.

**These four must land in one commit.**  Making the recognizer change alone adds a check whose
information nothing consumes; making the `Expr.lean` change alone breaks the three closed
branches.  That is why this stream made none of them: the first is in a file it owns but is
useless without the second, which is in a file it does not.

---

## 4. Executable change: the conditional checks are now in the shape the proof consumes

`Lean4Lean/Primitive.lean` **[machine-checked: `lake build` green, the `run_meta` self-test
still accepts all eighteen primitives, Kernel Arena 185/6/0 before and after]**.

`Reflection.ite` and `Reflection.natDITE` are **deleted**.  `Reflection.checkITE` now takes the
result type `α` as a parameter and checks, under binders `p : Prop`, `H : r.type p b`,
`t e : α`,

```
@ite.{1} α p (r.toDec p b H) t e  ≡  t   (b = true)      and   ≡  e   (b = false)
```

`Reflection.checkNatDITE` likewise checks `@dite Nat p (r.toDec p b H) a b'` directly, under
`p`, `H`, `a`, `b'`.  `Condition.check`'s `ite : Bool` flag becomes `iteTypes : List Expr`
(`Nat.mod` passes `[Nat]`, `Nat.bitwise` passes `[Nat, Bool]` for `Condition.natEq` because it
needs both `Condition.ite Nat` and `Condition.decide`, `[Nat]` for `Condition.bool`), and the
`.bool` arm checks the same applied shape at each result type.

**Why.**  `VEnv.ReflectsCondApp` is stated over the applied form.  With the old check the
verification first had to invert the translation of `Reflection.ite` — a four-fold λ with an
`@ite` spine in its body — to learn that the translated `ITE'` really *is* that λ, then β-reduce
four times, then re-apply.  With the new one the checked term is an application spine and the
hypothesis is read off by app-inversion, which the file already does everywhere.  That was the
single largest item in the remaining plumbing.

**Zero proof churn**: `Condition` / `Reflection` are reachable only from `Nat.mod`, `Nat.div`,
`Nat.gcd` and `Nat.bitwise` — all four inside `.rest` **[machine-checked: `lake build` of
`Verify/Environment/Boundaries.lean` is unchanged, census 19]**.

**Behavioural difference**, recorded in `divergences.md`: the old form additionally forced
`r.toDec p b H : Decidable p` at a *variable* `b`; the new one forces it at `b = Bool.true` and
`b = Bool.false` only, which is all the abstract statement uses.  The recognizer is therefore
marginally more permissive on `Reflection` records ill-typed at a variable boolean and
well-typed at both literals; neither shipped record is such a thing, and the accepted set on
the Arena is unchanged.

Also added, ready for the instantiation step: `IsDefEqU.inst4` (four nested binders whose only
dependency is on the outermost — one `IsDefEqU.instN` at depth 3 then three `inst0`s; this is
why the recognizer binds `p` outermost) and `IsDefEqU.inst2` (two independent binders of
arbitrary closed domain) **[machine-checked]**.

---

## 5. (c) — the standing recommendation is impossible, and here is what (c) actually is

**The recommendation was: make `unfoldNatWellFounded` produce its fixpoint equation by
`checkedIsDefEq` instead of by structural matching.  It cannot work.**

`WellFounded.Nat.fix` (`~/lean4/src/Init/WF.lean:494`) is

```lean
def Nat.fix : (x : α) → motive x :=
  let rec go : ∀ (fuel : Nat) (x : α), (h x < fuel) → motive x :=
    Nat.rec (fun _ hfuel => …) (fun _ ih x hfuel => F x (fun y hy => ih y …))
  fun x => go (Nat.eager (h x + 1)) x (Nat.eager_eq _ ▸ Nat.lt_add_one _)
```

with

```lean
/-- Helper gadget that prevents reduction of `Nat.eager n` unless `n` evaluates to a ground term. -/
def Nat.eager (n : Nat) : Nat := if Nat.beq n n = true then n else n
theorem Nat.eager_eq (n : Nat) : Nat.eager n = n := ite_self n
```

`Nat.fix_eq` — `Nat.fix h F x = F x (fun y _ => Nat.fix h F y)` — is proved from
`Nat.eager_eq` (`ite_self`, propositional) and `Nat.fix.go_congr` (an induction on the fuel,
propositional).  It is **not** a definitional equality, and `Nat.eager` exists precisely to
make sure it is not: at a free variable `x`, `Nat.beq (h x + 1) (h x + 1)` is stuck, so the
`ite` is stuck, so `Nat.rec` is stuck.

Machine-checked **[machine-checked]**:

```lean
example (h : Nat → Nat) (F : ∀ x : Nat, (∀ y, InvImage (·<·) h y x → Nat) → Nat) (x : Nat) :
    WellFounded.Nat.fix h F x = F x (fun y _ => WellFounded.Nat.fix h F y) := rfl
-- error: type mismatch, rfl has type ?m = ?m
```

A `checkedIsDefEq` at that equation would simply return `false` and the recognizer would reject
`Nat.gcd` and `Nat.bitwise` outright — the Arena would catch it on the first run.  The
structural matching is not a shortcut somebody took; it is the only way to establish, inside a
kernel, a fact the kernel's conversion deliberately does not decide.

### 5.1 What (c) actually costs

Price it as a *fuel induction on the `Nat.rec` skeleton*, not as a reconstruction of
`Nat.fix_eq`:

* the abstract `IsDefEqU` is the same conversion, so `fix α motive f F a ≡ F a (fun y _ => fix …
  y)` is **not** an `IsDefEqU` at an open `a` either.  Any spec that states it in that form is
  false;
* but at a **numeral** it is, because everything computes: `h a` is a numeral, `Nat.eager`
  reduces, `Nat.rec` reduces.  And numerals are all `HasPrimitives` ever asks about;
* so the spec to prove is: from the structural facts the recognizer checks — that `go` is
  `Nat.rec base step` with `step = fun _ ih x hfuel => F x (fun y hy => ih y _)`, which is where
  `lambdaTelescope` + the four `==` comparisons land — derive
  `IsDefEqU (go (natLit (t+1)) x h) (F x (fun y hy => go (natLit t) y _))` by ι (**a real
  definitional step**, because the fuel is a numeral), and then run exactly the induction
  `VEnv.reflects_fuel_go` already runs, with `F` in place of the `Condition` layer.

The prerequisite that does not exist is a `whnfCore.WF` / `unfoldDefinition.WF` returning a
defeq witness for the **whole** application together with the *syntactic* result, so that the
`==` comparisons can be turned into equalities of translations.  That is the real cost of (c),
and it is unchanged by anything in this session except that its shape is now known.

Ranking after this session: **(a)+(b) plumbing < (c)**, with (d) closed and the `Nat.bitwise`
branch additionally blocked on §3.

---

## 6. What is open, with the exact failing step

### 6.1 `Nat.mod` / `Nat.div` — plumbing, no new mathematics

All the mathematics is in `Verify/Primitive.lean` (`reflects_condApp`,
`reflects_condApp_natLE`, `ReflectsCondApp.natLE_le`, `reflects_fuel_go`, `reflects_fuel_mod`,
`reflects_fuel_div`, `IsDefEqU.inst4`, `.inst2`).  What is left is, per branch:

1. `checkedTypeIs.WF` on `q(@LE.le Nat _)` and on `q(Nat.modCore.go)` / `q(Nat.div.go)` →
   the translations `P` and `GO` with their types;
2. `Condition.check.WF` for `Condition.natLE`: `checkType cond.dec` → `D`;
   `checkedTypeIs cond.prop` → `P` again (identify by `trExprS_uniq`); `Reflection.check` →
   `TY`; `checkedTypeIs asBool` → the translation of `Nat.ble` is `.const ``Nat.ble`` []` by
   `trExprS_const_nil_inv`; the final `isDefEq e cond.dec` β-reduced at two numerals is
   `reflects_condApp_natLE`'s `hdec`;
3. `Reflection.checkITE`/`checkNatDITE` → `hsel`: **now one app-spine inversion plus
   `IsDefEqU.inst4`**, since §4;
4. the two big `checkedIsDefEq`s of the branch, instantiated at numerals
   (`IsDefEqU.instNat`/`instNat2` for the `Nat` binders, `inst0` for `hy`, `fuel`, `h`), give
   `reflects_fuel_mod`'s `hgo` with
   `Ok b hy f x h := HasType hy (P·1·b) ∧ HasType h (P·(x+1)·f)`; `hK` is the well-typedness of
   the checked right-hand side, using `hprim.natSub` to turn `Nat.sub x y` into `natLit (x-b)`
   — which is why the branch requires `Nat.sub` present;
5. `preserves_glue` + `VEnv.primField_Nat_mod` / `_div`, exactly as the fifteen closed branches.

The single missing tool is a `TrExprS` inversion for application spines of length 5 at a
`VContext` (the file has `trExprS_app2`/`app2_uniq` for length 2).  **[source]**

### 6.2 `Nat.gcd` — §5.  `Nat.bitwise` — §5 **and** §3.

### 6.3 Restructuring `.rest`

Once `Nat.mod` and `Nat.div` close, `.rest` should be split so the proved names dispatch to
proofs and only `Nat.gcd`/`Nat.bitwise` reach a `sorry`.  That keeps the census at 19 (one
`sorry` before, one after) while `.rest` itself becomes a proof.  Note that until §3's edits
land, `.rest` is **false**, so no split can make it disappear.

---

## 7. Unchanged from the previous handoff

* The statement audit of `.rest`'s own signature (no auto-bound implicits, no under-constrained
  quantifier, non-vacuous — the `run_meta` self-test and `stdPrelude accepted by addDecl ✓`
  drive all four branches to `.ok`) stands and was not repeated.  Note that "not vacuous" and
  "true" are different claims: §3 refutes the second for the `Nat.bitwise` branch.
* The C++ comparison: **the C++ kernel has no primitive-definition recognizer at all**, so
  every discrepancy here is a divergence by construction and there is no C++ behaviour to
  match — only the accepted set, which the Arena measures.
* The `Nat.pow` / `Nat.shiftLeft` numeral-size divergence (`Lean4Lean/TypeChecker.lean`, not
  this stream's file) is recorded in `divergences.md` and unchanged.

## 8. Pick up first

1. §3's four edits, in one commit, with the Arena as the gate.  Without them the
   `Nat.bitwise` branch cannot be closed and `.rest` cannot be true.
2. The `Nat.mod` plumbing of §6.1, starting with the length-5 `TrExprS` app-spine inversion.
   `Nat.div` is the same proof with `Nat.succ` as the wrapper.
3. (c) as re-priced in §5.1 — **do not** attempt the `checkedIsDefEq` route.
