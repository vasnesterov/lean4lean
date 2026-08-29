# Handoff: the `Eq` safety gap in quotient initialization

Scope: `Verify/SafeFragment.lean` §3's live gap — `quotInit` forces `Eq` into the model, but
neither kernel checked that `Eq` is a *safe* declaration. This document separates what is
**machine-checked** from what is **read off source**, and says where the remaining work is.

---

## 1. The gap is real. Confirmed independently, with executable witnesses.

### 1.1 Read off source

* `Lean4Lean.checkEqType` (`Lean4Lean/Quot.lean`, pre-change) destructured
  `let .inductInfo info ← env.get ``Eq` and then checked, in order: exactly one universe
  parameter, exactly one constructor, `info.type` structurally equal to
  `∀ {α : Sort u}, α → α → Prop`, and the constructor's type structurally equal to
  `∀ {α : Sort u} (a : α), @Eq α a a`. **No safety check anywhere.**
* `check_eq_type` (`~/lean4/src/kernel/quot.cpp:19-44`) is the same four checks in the same
  order. `constant_info::is_unsafe()` is never called.
* `Eq ∉ Lean.Kernel.Environment.primitives` (`Lean4Lean/Environment/Basic.lean:34-42`), so
  `checkName` raises nothing; `checkPrimitiveInductive` (`Lean4Lean/Primitive.lean:545-546`)
  returns `false` immediately when `isUnsafe`, so `allowPrimitive` plays no part.
* Positivity is skipped for an unsafe block: `Lean4Lean/Inductive/Add.lean:381`, `if !isUnsafe
  then checkPositivity …`.
* `add_quot`/`addQuot` install the four quotient constants with `add_core`/`Environment.add`,
  which bypasses the type checker, and a `quotInfo` is unconditionally safe
  (`ConstantInfo.isUnsafe` for `.quotInfo` is the literal `false`, `Lean/Declaration.lean:454`).
  `Quot.lift`'s stored type mentions `Eq`.

### 1.2 Machine-checked witness, lean4lean

Building `Eq`'s real `InductiveVal`/`ConstructorVal` types out of a live `Lean` environment and
replaying them into `Kernel.Environment.empty` through `Lean4Lean.addDecl`, then calling
`Lean4Lean.Environment.addQuot`:

```
== safe Eq ==    added Eq: isUnsafe=false … addQuot SUCCEEDED: quotInit=true
== unsafe Eq ==  added Eq: isUnsafe=true  … addQuot SUCCEEDED: quotInit=true    <-- the gap
```

After the fix the second line reads
`addQuot FAILED: (kernel) failed to initialize quot module, 'Eq' is not a safe declaration`.

### 1.3 Machine-checked witness, C++ kernel

```lean
prelude
universe u
unsafe inductive Eq : {α : Sort u} → α → α → Prop where
  | refl : ∀ {α : Sort u} (a : α), Eq a a
init_quot
```

elaborates with **no error** on the pinned toolchain. `#print Eq` reports
`unsafe inductive Eq.{u} : {α : Sort u} → α → α → Prop`; `#print Quot.lift` reports
`Quotient primitive Quot.lift.{u, v} : … → (∀ (a b : α), r a b → Eq (f a) (f b)) → Quot r → β`.

Appending to the *same* file

```lean
axiom bad : ∀ {α : Sort u} (a : α), Eq a a
axiom useLift : ∀ {α : Sort u} {r : α → α → Prop} {β : Sort v} (f : α → β),
  (∀ (a b : α), r a b → Eq (f a) (f b)) → Quot r → β
```

gives, twice, `error: (kernel) invalid declaration, it uses unsafe declaration 'Eq'`. The second
of those axioms is `Quot.lift`'s own stored type. So the C++ kernel installs a safe constant it
would itself refuse to accept.

### 1.4 The check that would have to reject it, and does not

`check_eq_type` / `checkEqType`. Nothing else in either `addQuot` path inspects `Eq` at all, and
`Quot*` are added without type checking, so no later check can catch it either.

### 1.5 Corrections to the brief

Two, both minor, one substantive:

* The brief says the gap is masked because `checkEqType.WF`'s conclusion is `False`. That is
  right, but the *reason* `TrEnv'.no_inductInfo` proves `False` is not only that `AddInduct` has
  no constructors — it is also that `TrEnv'.ignore` at `.unsafe` is unusable, because
  `¬ .unsafe ≤ ci.safety` is false for every `ci` (`no_inductInfo`'s `ignore` case is discharged
  by `cases ci.safety <;> rfl`). Both facts are needed; the crutch dies when either goes.
* The C++ consequence is **not** a route to `False`, as far as this stream could establish.
  `check_eq_type` pins `Eq`'s type and its single constructor's type *exactly*, and that
  constructor type is positive, so the skipped positivity check buys nothing. What breaks is the
  safe/unsafe stratification invariant (§1.3). `bugs-found.md` entry 15 states it that way.
* The brief's "`Eq` is not in `Environment.primitives` so `checkName` admits it" is accurate but
  `checkName` is never called on `Eq` by `addQuot` in the first place — only on the four `Quot*`
  names. `Eq` reaches the environment through `addInductive`, whose `checkName ind.name` is the
  relevant one, and `allowPrimitive` there is `false` for exactly the reason given.

---

## 2. What was changed

### 2.1 Executable (`Lean4Lean/Quot.lean`, owned)

One check, immediately after the `.inductInfo` destructuring, in the position where the C++
kernel would put it:

```lean
if info.isUnsafe then fail "'Eq' is not a safe declaration"
```

Nothing else about `checkEqType` or `addQuot` changed. This is a deliberate divergence — we
reject an input the C++ kernel accepts — recorded in `divergences.md`.

### 2.2 Kernel Arena

Both runs on the same machine, same tests, `uv run lka.py run --checker lean4lean-local`:

| | correct | either | incorrect |
|---|---|---|---|
| baseline (binary built before the change) | 185 | 6 | 0 |
| after the change | 185 | 6 | 0 |

No regression, nothing new incorrect. Expected: every real prelude declares `Eq` safe.

### 2.3 Proof side (`Lean4Lean/Verify/EqSafety.lean`, new, owned)

All four are `sorry`-free (`#print axioms`: `propext`, `Classical.choice`, `Quot.sound`, plus the
three `PersistentHashMap` axioms already in Guard's whitelist, reached through
`SafeFragment`'s `eq_safe_of_quotInit`).

* `ConstantInfo.safety_inductInfo` — `(ConstantInfo.inductInfo info).safety = if info.isUnsafe
  then .unsafe else .safe`.
* `TrEnv.eq_isUnsafe_false_of_quotInit` — **necessity**. If a `.safe` model exists for a
  quotient-initialized environment whose `Eq` is inductive, that inductive is not unsafe. This
  is the machine-checked statement that the new check is exactly what the model demands, not a
  convenience.
* `checkEqType.WF_safe` — **sufficiency, and the honest non-vacuous postcondition**:
  ```lean
  (checkEqType env).WF fun _ => ∃ info : InductiveVal,
    env.find? ``Eq = some (.inductInfo info) ∧ info.isUnsafe = false ∧
    (ConstantInfo.inductInfo info).safety = .safe
  ```
  No `VEnvs.WF` hypothesis; read straight off the executable checker.
* `checkEqType.WF_visible` — the same fact in the shape `TrEnv.eq_visible_of_quotInit` consumes:
  `Eq` is visible at *every* safety level.
* `checkEqType.WF_quotReady` — the full replacement for `checkEqType.WF`, i.e. exactly what
  `addQuot.WF` needs (`∀ safety, (ves.venv safety).QuotReady`), reduced to one premise.

---

## 3. What is stated but open, and precisely where it fails

`addQuot.WF`'s non-initialized branch must build `TrEnv'.quot`, whose first premise is
`VEnv.QuotReady (ves.venv safety)`, i.e.

```
(ves.venv safety).constants ``Eq = some eqConst
```

with `eqConst := vconst(type_of% @Eq)` (`Theory/Quot.lean:6`). The checker establishes that `Eq`
is *present* and *safe*, hence *visible at every level* (§2.3). It does **not** establish that
`Eq`'s image in the model is `eqConst`, and that is the entire remaining gap.

`checkEqType.WF_quotReady` isolates it as its single hypothesis:

```lean
(htr : ∀ (safety : DefinitionSafety) (info : InductiveVal),
   env.find? ``Eq = some (.inductInfo info) → info.isUnsafe = false →
   (ves.venv safety).constants ``Eq = some eqConst)
```

**Where it fails today, exactly.** `htr` is not derivable from `wf : ves.WF env`. The only
`TrEnv'` constructor that could put an `.inductInfo` into the constant map is `TrEnv'.induct`,
whose second premise is `AddInduct C env decl C' env'` — and `AddInduct` has **no constructors**
(`Theory/Inductive/Decl.lean`; `SafeFragment.lean`'s `AddInduct.le` is proved by `nomatch H`).
So `TrEnv'` today cannot place *any* inductive in any model, which is what
`TrEnv'.no_inductInfo` says and what the current vacuity crutch exploits. Attempting to prove
`htr` from `TrEnv.find?` gets `∃ ci', venv.constants ``Eq = some ci' ∧ TrConstant safety venv
(.inductInfo info) ci'` only *after* an inductive constructor exists to supply the `ci'`; there
is no route from `wf` to the *identity* `ci' = eqConst` without it, because nothing in `TrEnv'`
currently relates a kernel `InductiveVal`'s stored type to a `VConstant`.

**What `htr` will need when `AddInduct` lands.** Two things, in this order:
1. `TrEnv'.induct` must add `Eq` to the model at `.safe` (it will, once gated to safe blocks —
   which is why the executable check in §2.1 is a precondition of this work, not an aside).
2. The translation of `info.type` must be shown to be `eqConst.type`. `checkEqType` checks
   `info.type` structurally against `(← read).mkForall #[α] (α.arrow (α.arrow .prop))` under a
   `withLocalDecl`-bound `α`. Extracting that equation from `checkEqType`'s success is
   mechanical but was **not attempted here** (see §4).

---

## 4. What was tried and did not work, with the failing step

* **Extracting the type equations from `checkEqType`.** Wanted: `info.type = <closed literal>`
  as an extra conjunct of `checkEqType.WF_safe`, so that `htr` could be stated in terms of
  `info.type` rather than as "translates to `eqConst`". Not attempted to completion: the check
  runs inside `ExprBuildT.run` (`ReaderT LocalContext <| ReaderT NameGenerator`) and compares
  against `LocalContext.mkForall #[α] …` where `α` is a `withLocalDecl`-bound fvar whose id
  comes from the `NameGenerator`. Reducing that to a closed `Expr` needs `withLocalDecl`'s and
  `mkForall`'s computational behaviour on a one-entry context, which is a self-contained but
  non-trivial lemma. **Deliberately deferred** — it buys nothing until `AddInduct` exists, since
  the conclusion it feeds (`= eqConst`) has no other half.
* **`rw [hu] at h` followed by `simp` to kill the unsafe branch** in `checkEqType.WF_safe`.
  Fails: `rw` cannot find `info.isUnsafe` because after `cases ci` the hypothesis still has the
  un-reduced `do let __x ← pure (ConstantInfo.inductInfo info); match __x with …` wrapper, so
  the occurrence is under a `match` motive. Working form is
  `cases hu : info.isUnsafe with | false => rfl | true => simp [hu, …] at h`, which does the
  case split *before* looking at `h` and lets `simp` reduce the `pure`-bind and the `if`
  together.

---

## 5. The frozen/unowned edit this stream did not make

`checkEqType.WF` and `addQuot.WF` live in `Lean4Lean/Verify/Environment.lean`, which this stream
does not own. **No edit was made there, and none is needed today**: the file still compiles
unchanged against the new `checkEqType` (verified — full `Lean4Lean.Verify` build is green), and
its `False` postcondition is still true, still vacuously.

The edit to make *when `AddInduct` gains constructors* — not before, since it cannot be proved
before — is to replace, in `Lean4Lean/Verify/Environment.lean`:

```lean
theorem checkEqType.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env) :
    (checkEqType env).WF fun _ => False := …

theorem addQuot.WF … :=
  … | · exact (checkEqType.WF wf).bind fun _ h => False.elim h
```

with

```lean
theorem checkEqType.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env) :
    (checkEqType env).WF fun _ => ∀ safety, (ves.venv safety).QuotReady :=
  checkEqType.WF_quotReady (htr := …)   -- `htr` from `TrEnv'.induct`
```

and to discharge `addQuot.WF`'s second branch by `TrEnv'.quot` with that `QuotReady` and
`AddQuot.to_addQuot`. `checkEqType.WF_quotReady` in `Verify/EqSafety.lean` is that theorem
already, waiting only for `htr`. Note `checkEqType.WF`'s `wf` argument becomes genuinely used at
that point; today it is used only to reach `no_inductInfo`.

---

## 6. What to pick up first

1. **The `htr` premise of `checkEqType.WF_quotReady`.** It is now the *only* thing between the
   checker and a non-vacuous `addQuot.WF`, and it is a pure `AddInduct` obligation. Whoever
   builds `TrEnv'.induct` should state it in a shape that hands `htr` over directly: from
   `env.find? n = some (.inductInfo info)` and the block's safety, the model's constant at `n`.
2. **Then** the type-equation extraction of §4, which is what turns `htr`'s abstract "translates
   to `eqConst`" into something derivable from what `checkEqType` literally compares.
3. **Audit the other `add_core` sites for the same shape of bug.** The defect's real form is
   "a constant installed without type checking, whose stored type names a constant whose safety
   was never constrained". `addQuot` is the only such site in this kernel today, but
   `addInductive`'s recursor/constructor installation is structurally similar and worth the same
   read. Nothing was checked there by this stream.
