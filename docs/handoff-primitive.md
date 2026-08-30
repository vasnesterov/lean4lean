# `checkPrimitiveDef.WF.rest` — `Condition.check.WF` is closed, both arms

Stream scope: `Lean4Lean/Verify/Typing/Expr.lean`, `Lean4Lean/Primitive.lean`,
`Lean4Lean/Verify/Primitive.lean`, `Lean4Lean/Verify/Environment/Boundaries.lean`
(`checkPrimitiveDef.WF.rest` only), and new files under `Lean4Lean/Verify/`.

Everything below is marked **[machine-checked]** (a `lake build`, the sorry census, the guards,
`scripts/dup-names.lean`, `#print axioms`, or a Kernel Arena run produced it) or **[source]**
(read off the code, or argued).

| gate | before | after |
| --- | --- | --- |
| sorry census (`lake env lean scripts/sorry-census.lean`) | **19** | **19** **[machine-checked, both runs]** |
| `lake build` (whole tree) | green | green **[machine-checked]** |
| `Verify/Guard.lean` guards 1–3 | ✓ | ✓ **[machine-checked: 25 frozen axioms ✓; `kernel_sound` within whitelist ✓ (proof INCOMPLETE); cone gaps 54/54 ✓]** |
| `scripts/dup-names.lean` | — | no duplicates **[machine-checked]** |
| Kernel Arena (`lean4lean-local`) | **185 / 6 / 0** | **185 / 6 / 0** **[machine-checked; two full runs after the executable change]** |
| axiom set of every new `…WF` | — | **identical, element for element, to `Reflection.check.WF`'s 25** **[machine-checked]** |

`Lean4Lean/Primitive.lean` changed by **one reordering**, recorded in `divergences.md`
("Tenth"). No other executable change.

---

## 0. Bottom line

1. **`TypeChecker.Condition.check.WF` is proved** — the whole `.reflectNatNat` arm, delivering
   one `VEnv.ReflectsCondApp` per element of `iteTypes` and, when `dite := true`, one
   `VEnv.ReflectsCondAppD`. §1.
2. **`TypeChecker.Reflection.checkNatDITE.WF` is proved**, with `checkNatDITEHalf.WF`,
   `VEnv.hsel_of_checkNatDITE` and the acceptance test
   `VEnv.reflects_condAppD_of_checkNatDITE`. §2.
3. **`TypeChecker.Condition.check.WF_bool` is proved** as well — the `.bool` arm, delivering
   `VEnv.ReflectsCondApp1`. That was item 3 on the last handoff's pick-up list. §3.
4. **Three acceptance instances and one collapse test are machine-checked**:
   `Condition.check.WF_natLE`, `…WF_natEq`, `…WF_boolCond` discharge *every* hypothesis at the
   three shipped `Condition`s, and `Condition.check.WF_natLE_pinned` collapses the existential
   `P`/`D` to the concrete `VExpr.natLE` and `.const ``Nat.decLe []` the `Nat.mod` / `Nat.div`
   branches actually carry. §4.
5. **Correction to the brief that ordered this round.** It listed `Condition.check.WF` as
   target 1 and `Reflection.checkNatDITE.WF` as target 2. Target 2 is a **prerequisite** of
   target 1, not a successor: `Condition.check`'s `dite` clause *is* `checkNatDITE`, and
   `M.WF` is not vacuous for a trivial postcondition (it also asserts state well-formedness and
   monotonicity), so the arm cannot even be *traversed* without it. The order was inverted. §5.
6. **A second `do`-block defect, of a different kind, in the same arm** — and this one was not
   in any handoff. §5.2.

---

## 1. `Condition.check.WF` **[machine-checked]**

`Lean4Lean/Verify/Primitive.lean`, at the end of the file.

```
theorem Condition.check.WF … (himpl : cond.impl = .reflectNatNat asBool r proof) … :
  M.WF c s (cond.check fail iteTypes dite) fun _ _ =>
    ∃ P D, c.TrExprS cond.prop P ∧ c.TrExprS cond.dec D ∧ P.ClosedN 0 ∧ D.ClosedN 0 ∧
      (∀ α ∈ iteTypes, ∃ Aα F, … ∧ c.venv.ReflectsCondApp F P D g) ∧
      (dite = true → ∃ FD OT OF PR, … ∧ c.venv.ReflectsCondAppD FD P D OT OF PR g)
```

The `g : Nat → Nat → Bool` is a parameter, supplied through one hypothesis

```
hg : ∀ {Δ X}, TrExprS c.venv c.lparams Δ asBool X →
       ∀ a b, c.venv.IsDefEqU 0 [] (X (natLit a) (natLit b)) (boolLit (g a b))
```

which is `trExprS_const_nil_inv'` composed with `VEnv.HasPrimitives.natBLE` / `natBEq` at the
two shipped conditions. Stating it this way — a *rule* for reading the recognizer's `asBool`,
not a fixed `B : VExpr` — is what keeps the lemma independent of which primitive is behind
`asBool`.

### 1.1 The pieces that were missing, and are now there

| name | content |
| --- | --- |
| `trExprS_lam_inv'` | λ inversion in the `_inv'` family's raw form |
| `trExprS_decisionTerm_inv'` | pins the translation of `fun x y => toDec (prop x y) (asBool x y) (proof x y)` to `.lam .nat (.lam .nat (TD (P bv1 bv0) (B bv1 bv0) (PR bv1 bv0)))`, identifying all four abstract subterms with their base-context translations by `trExprS_weakBV0` + `TrExprS.unique` |
| `VEnv.IsDefEqU.lam2_beta` | the two congruences and the two βs from `E ≈ D` (what `isDefEq e cond.dec` leaves) to `D (natLit a) (natLit b) ≈ body[a,b]`. The body's typing is **not** recovered by inverting `HasType E EA` blindly: it is `HasType.lam_inv` twice, at `[]` and at `[.nat]` |
| `M.WF.forIn` invariant for `iteTypes` | `∃ pre, iteTypes = pre ++ vs ∧ ∀ α ∈ pre, <checkITE.WF's output>`. The accumulator is `PUnit`, so the processed prefix has to live in the invariant, not in the accumulator |

`hdec`, `hB`, `hPR` — the three residues the last handoff identified — are all discharged
inside this lemma. `hPR` needs one extra step over `VEnv.reflProof_inst`: that lemma delivers
`HasType (PR a b) (RT (P a b) (B a b))` while `reflects_condApp` wants `(boolLit (g a b))` in
the last slot, so `hg` is applied through `IsDefEqU.app_congr_arg'` and `HasType.defeqU_r`.

---

## 2. `Reflection.checkNatDITE.WF` **[machine-checked]**

| name | content |
| --- | --- |
| `trExprS_bvar2_inv'` | the bound variable two `vlam`s out |
| `trExprS_diteHeadType_inv'` | pins `@dite.{1} Nat`'s declared type. Needs **no** uniqueness side condition, unlike `trExprS_iteHeadType_inv'`: every leaf is a constant or a bound variable because the result type is fixed at `Nat` |
| `VEnv.hsel_of_checkNatDITE` | the `dite` counterpart of `hsel_of_checkITE`. The four binder domains are `Prop`, `RT p (boolLit v)`, `p → Nat`, `¬p → Nat`; only the first two are closed, so this is where `IsDefEqU.inst4`'s dependence on the outermost binder is actually used, and the three typings it needs come from `VEnv.condApp_typed'` |
| `Reflection.checkNatDITEHalf.WF` | one half, parametrised by the literal `v` and by `ob` (`r.ofTrue` or `r.ofFalse`) |
| `Reflection.checkNatDITE.WF` | the whole check |
| `VEnv.reflects_condAppD_of_checkNatDITE` | the acceptance test: its two outputs plus `hdec`/`hB`/`hPR` give `ReflectsCondAppD`. Axiom set identical to `reflects_condApp_of_checkITE`'s **[machine-checked]** |

**What `checkNatDITE.WF` deliberately does not export**, and why it is not a gap: the declared
types of `r.ofTrue` / `r.ofFalse`. The recognizer checks them (`ofTrue : ∀ p : Prop,
r.type p true → p`), but the abstract statement does not use them, and the consumer's β-step
does not need them either — `ReflectsCondAppD`'s conclusion is an `IsDefEqU`, which entails
`VExpr.WF` of `.app t (OT p PR)`, and `VExpr.WF.app_arg_typed` against
`HasType t (.forallE p .nat)` (from `condApp_typed'`) recovers `HasType (OT p PR) p` without
them. **[source]** If a future step turns out to want them anyway, the check is already made;
only an inversion lemma for its type is missing.

---

## 3. `Condition.check.WF_bool` **[machine-checked]**

`VEnv.reflectsCondApp1_of_checkBoolITE`, `Condition.checkBoolITEHalf.WF`,
`Condition.check.WF_bool`, `Condition.check.WF_boolCond`.

Two structural differences from the `.reflectNatNat` arm, both forced:

* there are only **two** binders (`t`, `e`), so `IsDefEqU.inst2` replaces `inst4`;
* everything `ReflectsCondApp1` needs is established *before* the `iteTypes` loop, so the
  reflection fact is assembled **inside** the loop body rather than after it.

The arm ends in `if dite then throw …`, so the `dite = true` case is `M.WF.throw` and the
conclusion carries no `dite` clause at all.

---

## 4. Non-vacuity and the collapse test **[machine-checked]**

* `Condition.check.WF_natLE` and `Condition.check.WF_natEq` discharge **every** hypothesis of
  `Condition.check.WF` at `Condition.natLE` / `Condition.natEq` — including the `IsUnique` side
  conditions, which are `False` at a `.proj` and so are a real vacuity risk, and the `hg`
  reading of `asBool`.
* `Condition.check.WF_boolCond` does the same for `Condition.bool`.
* `Condition.check.WF_natLE_pinned` is the **collapse test**: it runs the general lemma's
  existential `P` and `D` through `trExprS_natLE_inv'` and `trExprS_const_nil_inv'` and comes
  out with `ReflectsCondApp F VExpr.natLE (.const ``Nat.decLe []) Nat.ble` and
  `ReflectsCondAppD FD VExpr.natLE (.const ``Nat.decLe []) OT OF PR Nat.ble` — the exact slots
  `Condition.ite` / `Condition.dite` put `cond.prop` and `cond.dec` in, hence the form
  `VEnv.reflects_fuel_mod` / `_div` consume. It also shows `c.venv.contains ``Nat.ble` is
  reachable from the branch's `env.contains ``Nat.ble` guard, via `contains_primConst` and the
  new `primitives_natBLE`.
* The *call site's* side is checked too: at `VContext.mk' wf .safe [] fuel` the three structural
  hypotheses `hnil`, `hlp`, `hsafe` are `rfl`; `hfail` in the context-generic form is
  `M.WF.throw`; `hnat` is `NatFacts.contains` and `hnatty` is the new
  `TypeChecker.NatFacts.isType0`; and `hitefv` at `[q(Nat)]` / `[q(Nat), q(Bool)]` is
  `⟨by simp [FVarsIn], trivial, rfl⟩`. **[machine-checked, in a scratch file — the four
  `example`s are not committed, but `NatFacts.isType0` is]**

---

## 5. Corrections and new findings

### 5.1 The two targets were in the wrong order **[machine-checked, by construction]**

`Condition.check`'s `.reflectNatNat` arm contains `if dite then reflect.checkNatDITE fail`.
`M.WF c s x Q` is not implied by `Q = fun _ _ => True`: it also asserts that `x` preserves
`VState.WF` and is monotone in the state. So the arm cannot be traversed at all without
`checkNatDITE.WF`, whatever postcondition is wanted. Target 2 had to be proved first.

### 5.2 A second `do`-block defect, of a different kind **[machine-checked by `#print`]**

Last round's finding was that `fun t => do` swallowed the following statement. That one is
fixed and stays fixed: `#print` of `Reflection.checkNatDITE` and of `Condition.check` confirms
the two halves are siblings in all three places. **[machine-checked]**

The new one is not about columns. `Lean`'s `do` elaborator turns

```
    for α in iteTypes do reflect.checkITE α fail
    if dite then reflect.checkNatDITE fail      -- ← mid-block `if` with no `else`
    …twelve more lines…
```

into a **join point**: `have __do_jp := fun __r => <the whole rest of the arm>;
if dite = true then (checkNatDITE >>= __do_jp) else __do_jp ()`. The rest of the arm is
therefore reached along two paths, and a proof has to traverse it twice or invent an
abstraction over an anonymous `letFun`-bound continuation.

There was a second, independent order problem in the same arm: `_ ← checkType e` ran **above**
`checkedTypeIs proof …`. `checkType e`'s output is a translation of the decision term, and
reading it (`trExprS_decisionTerm_inv'`) requires `proof`'s own base-context translation to
already exist — which is exactly what the later `checkedTypeIs proof` produces. In the old
order the translation of `proof` inside `e` was an existential nothing later could be
identified with.

Both are fixed by **moving two statements**, recorded in `divergences.md` as "Tenth":
`checkType e` now sits immediately before `isDefEq e cond.dec`, and the `dite` check is the
arm's **last** statement, where a trailing `if` needs no join point. Every statement in the arm
must succeed for the recognizer to accept and none reads state produced by the ones it moved
past, so the accepted set is unchanged; only the error message on a malformed `Condition`
changes. Arena 185/6/0 after. **[machine-checked]**

The generalisable rule, and the reason this belongs in the next brief: **a mid-block `if` with
no `else` duplicates everything after it.** Put such a check last, or factor the tail into its
own definition.

### 5.3 `simp only []` is what removes a `do` block's `have`s

`unfold`ing a recognizer leaves `have y := …; have x := …; have e := …` as `letFun` nodes,
which block `split` (its `isFalse` branch keeps the whole `letFun` wrapper) and block `refine
M.WF.bind`. `simp only []` zeta-reduces them and nothing else. This cost an hour; it is one
token in the script.

---

## 6. Traps, for whoever picks this up

1. **`hfail` must be generalised over the `VContext`** — `∀ {c'} {β} {s'} {Q}, M.WF c' s' fail Q`
   — because `fail` is used under `withCheckedLocalDecl` binders. `Boundaries.lean`'s local
   `hfail` is stated at the fixed `c`; the caller supplies `fun {_ _ _ _} => .throw` instead.
   Costs nothing, but the un-generalised form fails with a page-long context mismatch.
2. **`let .app _ _ h3 h4 := h` does not see through `mkApp2`/`mkApp5`** under a
   `VContext.TrExprS` abbrev. Use `trExprS_app_inv'` / `trExprS_lam_inv'` and `obtain`.
3. **`c.HasType` / `c.IsDefEqU` are abbrevs over `c.lparams.length` and `c.vlctx.toCtx`.** With
   an abstract `c` and only *propositional* `hnil`/`hlp`, converting to the raw
   `c.venv.HasType 0 []` needs `rwa [VContext.HasType, hctx, hUs]`, where
   `hctx : c.vlctx.toCtx = []` is `by rw [hnil]; rfl`. The `raw` helper at the top of
   `Condition.check.WF` is the pattern.
4. **`OnCtx` is a `def`, not an inductive**, so `⟨trivial, hnatty⟩ : OnCtx [.nat] …` needs a
   `show` with `Γ` given explicitly.
5. **`FVarsIn (.const n us)` is `∀ u ∈ us, u.hasMVar' = false`**, so `simp [FVarsIn]` leaves
   `Level.zero.succ.hasMVar' = false` on any term mentioning `ite.{1}` / `Eq.{1}`. Add
   `Lean.Level.hasMVar'` to the simp set (`<;> rfl` also works but the linter prefers the
   former).
6. `Verify/Environment/Extension.lean:118` consumes `ReflectsNatBitwise` **positionally**. Not
   touched this round; `Extension.lean` and `Bridge.lean` both still build. **[machine-checked]**

---

## 7. Pick up first

1. **The `Nat.mod` branch of `checkPrimitiveDef.WF.rest`.** It is now blocked on nothing that
   is missing — `Condition.check.WF_natLE_pinned` supplies both conditional facts at the base
   context, and `trExprS_natLE_inv'` / `trExprS_goType_inv'` already pin `@LE.le Nat _` and the
   `Nat.modCore.go` telescope. What is left is: the two `checkedIsDefEq`s under the `x`/`y` and
   `hy`/`fuel`/`h` telescopes, read back with `trExprS_app5`; the β-step through
   `Condition.dite`'s two `.lam0`s (see §2's last paragraph — `VExpr.WF.app_arg_typed` against
   `condApp_typed'`'s `HasType t (.forallE p .nat)`, then `IsDefEqU.beta'`); and the assembly
   through `VEnv.reflects_fuel_mod`, `preserves_glue`, `VEnv.primField_Nat_mod`. **[source]**
2. **`Nat.div`** is the same, one step shorter (`iteTypes := []`, so only the
   `ReflectsCondAppD` half is used) and with `.app .natSucc` as `reflects_fuel_div`'s wrapper.
3. **`Nat.bitwise`** now has all three of its `Condition.check` facts
   (`WF_natEq` at `Nat` and `Bool`, `WF_boolCond` at `Nat`), but is still blocked at
   `unfoldNatWellFounded`.
4. `unfoldNatWellFounded` last, and **not** by a checked conversion: the
   `WellFounded.Nat.fix` fixpoint equation is propositional, not definitional, so a
   `checkedIsDefEq` there returns `false` and the recognizer would *reject* `Nat.gcd` and
   `Nat.bitwise`. This has now survived five handoffs unchanged. **[source]**

---

## 8. Carried over, still correct **[machine-checked unless noted]**

* Π-injectivity here is **inherited taint, not a new hole**: `VEnv.IsDefEqU.forallE_inv` and
  `VEnv.HasType.piUniq` are inside `checkPrimitiveDef.WF`'s 17594-constant forward cone.
* `ReflectsCondApp` is the `ite` rule only; the `go` equations are `dite`s and use
  `ReflectsCondAppD`. `ReflectsCondApp`'s live consumer is `reflects_natBitwise_go`.
* **No cross-half comparison is ever needed.** Every `…Half.WF` conclusion is proved
  independently and the two are combined by `cases v`. `TrExprS.unique'` and `IsUniqueCtx`
  appear nowhere in this development.
* The C++ kernel has **no primitive-definition recognizer at all** (measured), so every
  discrepancy here is a divergence by construction and the Arena's accepted set is the only
  external constraint.
* **The verification can never recover a subterm's type from the fact that an application
  containing it type-checks.** `TrExprS.app` and `VExpr.WF.app_inv` hand back the domain the
  application *invented*. If the abstract statement needs a declared type, the recognizer has
  to check it, in the *shape* the abstract statement consumes.

## 9. Method note

Two instruments earned their place again this round.

* **Write the supplier's side and see what it holds when it must produce the hypothesis.**
  That is what found §5.2's second defect: the `hPR`-shaped hypothesis
  `trExprS_decisionTerm_inv'` needs simply did not exist yet at the point `checkType e` ran.
* **`#print` the elaborated declaration, not the source.** Three `do` blocks in
  `Lean4Lean/Primitive.lean` did not mean what they looked like last round; a fourth shape —
  the mid-block `if`'s join point — did not either, and is invisible in the source.
