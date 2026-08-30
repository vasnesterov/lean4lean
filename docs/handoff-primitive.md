# `checkPrimitiveDef.WF.rest` — split into four branches; the telescope inversion is closed

Stream scope: `Lean4Lean/Verify/Typing/Expr.lean`, `Lean4Lean/Primitive.lean`,
`Lean4Lean/Verify/Primitive.lean`, `Lean4Lean/Verify/Environment/Boundaries.lean`
(`checkPrimitiveDef.WF.rest` only), and new files under `Lean4Lean/Verify/`.

Everything below is separated into **[machine-checked]** (a `lake build`, a `#print axioms`, the
sorry census, the guards, or a Kernel Arena run produced it) and **[source]** (read off the code
or argued, not proved).

| gate | before | after |
| --- | --- | --- |
| sorry census (`lake env lean scripts/sorry-census.lean`) | **19** | **19** **[machine-checked, both runs]** |
| `lake build Lean4Lean.Verify.Environment.Boundaries` | green | green **[machine-checked]** |
| `Verify/Guard.lean` guards 1–3 | ✓ | ✓ **[machine-checked: 25 frozen axioms ✓; kernel_sound within whitelist ✓ (proof INCOMPLETE); cone gaps 54/54 ✓]** |
| Kernel Arena (`lean4lean-local`) | **185 correct / 6 either / 0 incorrect** | **185 / 6 / 0** **[machine-checked, after run]** |

No executable file changed this session (`Lean4Lean/Primitive.lean` untouched), so there is
nothing new for `divergences.md`.

---

## 0. Bottom line

1. **`.rest` is split.**  It is no longer a bare `sorry`: it is a 19-way `split` on the
   recognizer's `match v.name`, with the fifteen non-target branches discharged from `hrest` and
   the four target branches named.  Each of the four is peeled down to its own first genuinely
   missing lemma.  Census stays at **19** because all four `sorry`s live inside the one
   declaration.

2. **The `Nat.mod` / `Nat.div` `go` telescope inversion is done** — and the route the previous
   handoff prescribed for it was **unnecessary**.  See §2; this is the session's main
   correction.

3. **The real remaining blocker for `Nat.mod` and `Nat.div` is `Condition.check.WF`**, not the
   telescope.  `Nat.div` hits it *before* the telescope, `Nat.mod` immediately *after*.  §4
   prices it and records two obstacles in its interface that no previous handoff named.

---

## 1. What `.rest` now looks like

`Lean4Lean/Verify/Environment/Boundaries.lean:107`.  Structure:

```
obtain ⟨⟨name, lparams, type, …⟩⟩ := v; unfold Environment.checkPrimitiveDef; split …
split                                   -- the 19-way match on the name
· rename_i hname; subst hname; simp at hrest      -- ×15, the non-target branches
· -- ``Nat.mod   … peeled to line 189
· -- ``Nat.div   … peeled to line 209
· -- ``Nat.gcd   … peeled to line 229
· -- ``Nat.bitwise … peeled to line 245
· exact .pure ⟨nofun, nofun, nofun⟩     -- the match's catch-all: returns false
```

`exact absurd hrest (by decide)` does **not** work for the fifteen dismissals: after the
`obtain` the name sits under a `DefinitionVal` projection with free variables in it and `decide`
refuses (`Expected type must not contain free variables`).  `simp at hrest` does
**[machine-checked]**.

### 1.1 How far each branch is peeled, and what stops it

| branch | peeled through | stops at |
| --- | --- | --- |
| `Nat.mod` | guard, `checkPrimValue`, `mod 0 x ≡ 0`, `checkedTypeIs q(@LE.le Nat _) q(Nat → Nat → Prop)`, `checkedTypeIs q(Nat.modCore.go) q(∀ n, 1 ≤ n → ∀ fuel x, x+1 ≤ fuel → Nat)` | `Condition.natLE.check` |
| `Nat.div` | guard, `checkPrimValue` | `Condition.natLE.check` — `Nat.div` runs it **before** its two `checkedTypeIs` |
| `Nat.gcd` | guard, `checkPrimValue` | `unfoldNatWellFounded` (no spec) |
| `Nat.bitwise` | guard, `checkPrimValue` | `unfoldNatWellFounded`, then `Condition.natEq.check` / `Condition.bool.check` |

At the `Nat.mod` stopping point the following are in hand **[machine-checked: the branch
compiles]**:

* `hFty : HasType F (.forallE .nat (.forallE .nat .nat))`, `hFc : F.ClosedN 0`;
* `h0 : IsDefEqU 0 [VExpr.nat] (.app (.app F .natZero) (.bvar 0)) .natZero` — the `mod 0 x ≡ 0`
  equation, ready for `IsDefEqU.instNat`;
* `hPty : HasType 0 [] VExpr.natLE (.forallE .nat (.forallE .nat (.sort .zero)))` — note the
  translation `P` of `@LE.le Nat instLENat` is **identically `VExpr.natLE`**, not an
  existential;
* `hGOty : HasType 0 [] (.const ``Nat.modCore.go []) VExpr.goType`.

---

## 2. **Correction: the iterated weakening the brief called "the concrete next piece" is not needed at all**

The previous handoff (§5.2) said the `go` telescope inversion is *not* a fifth
`trExprS_arrow_inv` because the two `≤` occurrences sit at binder depths 1 and 4 while
`checkedTypeIs` hands its type back at the base context, so `P` must be weakened under one and
under four binders (`TrExprS.weakLam0`) before `TrExprS.unique` can identify the occurrences.

**That is wrong, and the work it prescribes is dead work.**

`@LE.le Nat instLENat` is a *closed term built from constants only*
(`.app (.app (.const ``LE.le [.zero]) (.const ``Nat [])) (.const ``instLENat [])`).  `TrExprS`'s
`.const` and `.app` rules are context-independent on such a term, so its translation is the same
`VExpr` at **every** `VLCtx` — with no weakening step and no appeal to `TrExprS.unique`.  The
inversion is therefore exactly a plain iterated `trExprS_arrow_inv'`, and it is done:

```lean
theorem trExprS_goType_inv' {env : VEnv} {Us Δ} … (h : TrExprS env Us Δ <the checked type> e') :
    e' = .goType
```

`Lean4Lean/Verify/Primitive.lean:2378`.  `#print axioms` = `[propext, Classical.choice,
Quot.sound]`, no `sorryAx` **[machine-checked]**.  Non-vacuity is not merely by construction: it
is **used in situ**, in the `Nat.mod` branch, against the type the recognizer actually builds,
and that branch compiles **[machine-checked]** — which is also the only real check that the
`Expr` shape in the statement matches `q(∀ n, Nat.succ Nat.zero ≤ n → ∀ fuel x : Nat,
Nat.succ x ≤ fuel → Nat)`.

The same argument kills the `TrExprS.unique` note (previous handoff §5.2's "stronger than an
earlier note claimed"): `TrExprS.unique` is indeed stronger than `trExprS_uniq`, and it will
still be wanted in §4, but *not here*.

### 2.1 New definitions and inversions

`Lean4Lean/Verify/Typing/Expr.lean`:

| name | line | content |
| --- | --- | --- |
| `VExpr.natLE` | 210 | `@LE.le Nat instLENat` in the abstract syntax |
| `VExpr.natLEApp` | 213 | `a ≤ b` at `Nat` |
| `VExpr.goType` | 220 | `∀ n, 1 ≤ n → ∀ fuel x, x+1 ≤ fuel → Nat` |

`Lean4Lean/Verify/Primitive.lean` (all sorry-free, all `[propext, Classical.choice, Quot.sound]`
**[machine-checked]**):

| name | line | content |
| --- | --- | --- |
| `trExprS_bvar0_inv'` | 2318 | `.bvar 0` under one `vlam` translates to `.bvar 0` |
| `trExprS_bvar1_inv'` | 2325 | `.bvar 1` under two `vlam`s translates to `.bvar 1` |
| `trExprS_natLE_inv'` | 2333 | `@LE.le Nat instLENat` ↦ `VExpr.natLE`, at any context |
| `trExprS_natLEApp_inv'` | 2344 | `a ≤ b` spine inversion |
| `trExprS_one_inv'` | 2355 | `Nat.succ Nat.zero` ↦ `VExpr.natLit 1` |
| `trExprS_natArrowProp_inv'` | 2364 | `Nat → Nat → Prop` |
| **`trExprS_goType_inv'`** | **2378** | **the telescope** |
| `trExprS_const_inv'` | 2413 | `.const n us` at an arbitrary explicit level list — subsumes `trExprS_const_nil_inv'` and `trExprS_const_zero_inv'` |
| `trExprS_prop_inv'` | 2420 | `Prop` |
| `trExprS_propBoolProp_inv'` | 2427 | `Prop → Bool → Prop` |
| `TypeChecker.Reflection.check.WF` | 2448 | what `Reflection.check` establishes (§4.1) |

---

## 3. Unchanged and still correct from the previous session

* `VEnv.ReflectsNatBitwise` / `ReflectsBoolBoolBool` carry the typing and the `env'.WF` they
  need; the binder order (`∀ f g, env'.WF → …`) is load-bearing for
  `Verify/Environment/Extension.lean:118`, which consumes it positionally.  Not touched.
* `trExprS_app5`, `trExprS_appD`, `checkedTypeIs.WF'`, `trExprS_boolArrow2_inv`,
  `reflects_condApp`, `reflects_fuel_go` / `_mod` / `_div`, `reflects_natBitwise_go`,
  `IsDefEqU.inst4` / `.inst2` / `.inst0` — all still there and sorry-free.  `trExprS_app5` was
  **not** needed yet: it is used in step 5 of the assembly, past `Condition.check.WF`.
* §5.1's verdict on `unfoldNatWellFounded` stands verbatim: the `WellFounded.Nat.fix` fixpoint
  equation is *propositional, not definitional*, a `checkedIsDefEq` there returns `false`, and
  the "checked conversion" recommendation would make the recognizer **reject** `Nat.gcd` and
  `Nat.bitwise`.  Do not attempt it before `Nat.mod` / `Nat.div` land.
* The C++ kernel has **no primitive-definition recognizer at all**, so every discrepancy here is
  a divergence by construction and the Arena's accepted set is the only external constraint.

---

## 4. The real blocker: `Condition.check.WF`

`Lean4Lean/Primitive.lean:205`.  `Condition.check` is an `M Unit` that, in its
`.reflectNatNat` case, performs: `checkType cond.dec`; `checkedTypeIs cond.prop (Nat→Nat→Prop)`;
`Reflection.check`; `Reflection.checkITE α` for each `α` in `iteTypes`;
`Reflection.checkNatDITE` if `dite`; `checkType e` for the λ-abstracted decision term;
`checkedTypeIs asBool (Nat→Nat→Bool)`; `isProp (← checkType proof)`; and finally
`isDefEq e cond.dec`.

Its output must be `env.ReflectsCondApp F P D Nat.ble` (`Verify/Primitive.lean:708`), which is
what `reflects_fuel_mod` / `_div` consume.

### 4.1 What exists now

`TypeChecker.Reflection.check.WF` (`Verify/Primitive.lean:2448`) — the first and smallest of
the pieces:

```lean
theorem Reflection.check.WF … :
    M.WF c s (r.check fail) fun _ _ =>
      ∃ RT, c.TrExprS r.type RT ∧
        c.HasType RT (.forallE (.sort .zero) (.forallE .bool (.sort .zero)))
```

**[machine-checked: builds; `#print axioms` shows `sorryAx` only as inherited taint from
`checkedTypeIs.WF`'s cone, which every branch in this file already depends on — the census still
reports 19, i.e. this declaration does not itself contain `sorryAx`.]**

### 4.2 Obstacle A — `reflects_condApp`'s `hsel` may not be suppliable as stated **[source]**

`reflects_condApp` (`Verify/Primitive.lean:731`) takes

```lean
(hsel : ∀ (p H t e : VExpr) (v : Bool),
  VExpr.WF env 0 [] (VExpr.condApp F p (.app (.app (.app TD p) (.boolLit v)) H) t e) →
  env.IsDefEqU 0 [] (…) (bif v then t else e))
```

quantified over **arbitrary** `p H t e`, with only well-typedness of the whole application as a
hypothesis.  The supplier gets its equation from `Reflection.checkITE`, under four binders
(`p : Prop`, `H : r.type p true`, `t e : α`), and turns it into a base-context statement with
`IsDefEqU.inst4`.  `inst4` demands `HasType p (.sort .zero)`, `HasType H (RT.inst p 0)`,
`HasType t Aα`, `HasType e Aα` — **none of which follows from `VExpr.WF … (condApp F p i t e)`
alone**: `VExpr.WF.app_inv` hands back an *existential* domain, and pinning it to `.sort .zero`
needs `HasType F (.forallE (.sort .zero) …)`, which nothing in scope provides for the abstract
`F`.

`reflects_condApp` is a *proved* theorem, so this does not make anything false; it makes `hsel`
possibly **unusable**, which is the failure mode ORCHESTRATOR.md's "audit against consumers"
rule is about.  `reflects_condApp` has **no consumer anywhere in the tree** today
**[machine-checked: `grep` over `Lean4Lean/`, the only occurrences are its own definition site
and doc comments]**, so its hypotheses have never been discharged.

Two ways out, both untried:

* **Route 1 (no interface change).**  Recover the domains after all: `checkedIsDefEq`
  type-checks the left-hand side, so in the four-binder context `HasType F (.forallE (.sort
  .zero) X)` holds; `F` is closed, so strengthen it to the base context, then combine with the
  existential domain from `VExpr.WF.app_inv` via `HasType.uniqU` and `IsDefEqU.forallE_inv`.
  **`IsDefEqU.forallE_inv` is one of the 19 open sorries** (`Theory/Typing/Injectivity`).  Using
  it adds inherited taint, not a new hole — the checker cone already depends on it — but it does
  mean this route is not self-contained.
* **Route 2 (interface change).**  Add the four typings to `hsel` as hypotheses and have
  `reflects_condApp` discharge them at its own call site (`p := P·a·b` from `hPty`,
  `H := PR·a·b` from `Condition.check`'s `checkType e`).  The `t`/`e` typings then have to be
  pushed one level further out, into `ReflectsCondApp` itself, whose consumers are
  `reflects_fuel_go`, `ReflectsCondApp.ofDefeq` and `reflects_natBitwise_go` — **all three are
  proved today, so any such strengthening must be re-checked against them before it is made.**

### 4.3 Obstacle B — `Nat.bitwise` runs `Condition.check` under three binders **[source]**

`Nat.mod` and `Nat.div` call `Condition.check` at the **base** context
(`c.vlctx = []`), so their `Condition.check` facts are already where `ReflectsCondApp`'s
`0 []` wants them.  `Nat.bitwise` does not: it binds `f`, `n`, `m` with
`withCheckedLocalDecl` *first* and only then runs `Condition.natEq.check` and
`Condition.bool.check` (`Lean4Lean/Primitive.lean:466–473`).  Its facts therefore arrive in a
context whose `toCtx` is `[Nat, Nat, Bool → Bool → Bool]`.

* Moving them to `0 []` by **strengthening** goes through `IsDefEqU.weakN_iff`
  (`Theory/Typing/UniqueTyping.lean:172`) — **another of the 19 open sorries**.
* It can be avoided by **instantiating** instead: all three domains are inhabited by closed
  terms `HasPrimitives` supplies (`.natZero` twice, `.lam .bool (.lam .bool .boolTrue)` for the
  combinator), and the `Condition.check` facts do not mention `f`, `n`, `m`, so instantiating
  them at any closed inhabitants returns the same statement at base.  This is the route to take.

Neither observation appears in any previous handoff.

### 4.4 Interface sketch for `Reflection.checkITE.WF` **[source]**

What the next stream should aim at, and the traps found while sizing it:

```lean
theorem Reflection.checkITE.WF {s} {r} {α} {fail} {RT Aα : VExpr}
    (hfail …) (hnil : c.vlctx = [])
    (hRT : c.TrExprS r.type RT) (hRTc : RT.ClosedN 0) (huRT : TrExprS.IsUnique r.type)
    (hAα : c.TrExprS α Aα) (hAαc : Aα.ClosedN 0) (huα : TrExprS.IsUnique α) :
    M.WF c s (r.checkITE α fail) fun _ _ =>
      ∃ ITE TD, ∀ v : Bool,
        (c.venv).IsDefEqU 0 [Aα, Aα, (RT.app (.bvar 0)).app (.boolLit v), .sort .zero]
          (VExpr.condApp (ITE.app Aα) (.bvar 3)
            (((TD.app (.bvar 3)).app (.boolLit v)).app (.bvar 2)) (.bvar 1) (.bvar 0))
          (bif v then .bvar 1 else .bvar 0)
```

* `RT` and `Aα` must be **hypotheses at the base context, with closedness**, not existentials
  produced inside: `withCheckedLocalDecl` hands back its domain's translation existentially in
  the *extended* context, and identifying that with the base-context one is what
  `TrExprS.weakLam0` (needs `ClosedN 0`) plus `TrExprS.unique` (needs `IsUnique`) is for.  The
  caller has both: `Reflection.check.WF` gives `RT`, `closedN_of_nil` gives `RT.ClosedN 0`, and
  `IsUnique` of a concrete `q(…)` literal is a structural `Prop` (`Lemmas.lean:2275`) that
  `simp` should discharge.
* `ITE` and `TD` are fine as existentials — the LHS translation is recovered by five `TrExprS`
  **app-spine inversions**, which need no `IsUnique` at all.  `.fvar` positions are pinned
  outright, because `TrExprS.fvar` reads a deterministic `VLCtx.find?`.
* The `true` half and the `false` half are **separate `withCheckedLocalDecl` blocks**, so their
  `TD`s are a priori different terms in a priori different contexts (the `H` domain differs).
  `TrExprS.unique'` with `IsUniqueCtx` (`Lemmas.lean:2303–2340`) is the tool that compares
  across contexts differing only in declaration *types*; `TrExprS.unique` is not.
* Binder order `p, H, t, e` is already what `IsDefEqU.inst4` wants — do not reorder it.

---

## 5. Method notes

* **Auditing a statement's binders does not audit the statements it depends on** — and it does
  not audit whether its *hypotheses can be supplied*.  §4.2 is an instance of the second: every
  binder of `reflects_condApp` is clean, the theorem is proved, and its `hsel` may still be
  undischargeable.  The instrument that found it was asking "what does the supplier actually
  hold at the moment it must produce this?", not reading the statement.
* The cheapest disproof of a prescribed method is to **do the thing the prescription says is
  impossible**.  §2's inversion took under an hour once the observation ("the source term is
  closed and constant-only") was made; the prescribed weakening machinery was never written.

---

## 6. Pick up first

1. `Reflection.checkITE.WF` and `Reflection.checkNatDITE.WF` to the sketch in §4.4, then
   `Condition.check.WF` for `Condition.natLE` on top.  This unblocks `Nat.mod` *and* `Nat.div`
   simultaneously — `Nat.div`'s branch is otherwise a copy of `Nat.mod`'s, since
   `trExprS_natLE_inv'` and `trExprS_goType_inv'` serve `Nat.div.go` unchanged (the checked
   type is the same up to binder names, which the inversion ignores).
2. Before writing `Condition.check.WF`'s postcondition, settle §4.2: Route 1 (accept the
   `forallE_inv` dependency) or Route 2 (strengthen `ReflectsCondApp`, re-checking
   `reflects_fuel_go`, `ReflectsCondApp.ofDefeq` and `reflects_natBitwise_go` first).
3. Only then the assembly of §4 of the previous handoff (steps 4–6): `trExprS_app5`,
   `IsDefEqU.inst4`, `reflects_fuel_mod` / `_div`, `preserves_glue`,
   `VEnv.primField_Nat_mod` / `_div`.
4. `unfoldNatWellFounded` last, as re-priced — **not** by a checked conversion.

## 7. Kernel Arena

`uv run lka.py run --checker lean4lean-local` in `~/lean-kernel-arena`:
**185 correct / 6 either / 0 incorrect** **[machine-checked]** — identical to the recorded
before-figure.  No executable file changed this session, so this is a regression check, not a
gate on new behaviour.
