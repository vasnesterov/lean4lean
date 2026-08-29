# Handoff: the `Eq` safety gap, and `addQuot.WF`

Scope: `Verify/SafeFragment.lean` §3's gap — `quotInit` forces `Eq` into the model, but neither
kernel checked that `Eq` is a *safe* declaration — and the chain of obligations that hung off it,
ending at `addQuot.WF`. This document separates what is **machine-checked** from what is **read
off source**, and marks every claim an earlier revision got wrong.

---

## 0. Correction notice (read this first)

Two claims in the previous revision of this document were **false**, and were relayed to other
streams as established. They are marked in place below and corrected here:

1. **§3/§6.1 (old): "`htr` — a safe inductive `Eq` translates to `eqConst` — is the `AddInduct` /
   `TrEnv'.induct` obligation and nothing else, and cannot be discharged because `AddInduct` has
   no constructors."**
   **False.** `htr` needs no inductive machinery at all. `TrEnv.find?` returns the model's
   constant together with its `TrConstant` for *any* `TrEnv'` step, indifferent to which step
   introduced the name; the only missing piece was the *identity* of the translated type, which
   `TrExprS.unique` supplies once `checkEqType`'s `mkForall` comparison is computed. That
   computation is exactly the item §4 of the old revision had **deferred** as "buys nothing until
   `AddInduct` exists" — it was in fact the whole remaining step.
   `checkEqType.WF_quotReady_closed` (`Verify/InductFlip.lean`, master `092c0f8`) now proves the
   conclusion outright, `sorry`-free. A cone check over its 7327-declaration closure finds no
   `AddInduct` lemma in it.

2. **§4 (old): "extracting the type equations from `checkEqType` … buys nothing until `AddInduct`
   exists."** False for the same reason; it was the critical path.

The corresponding docstrings in `Verify/EqSafety.lean` (module header and
`checkEqType.WF_quotReady`) now carry the correction rather than a silent rewrite.

A third false claim, in a *different* file, is also corrected: `Verify/Environment/Induct.lean`'s
`TrIndDecl.safe` said an unsafe inductive block "is taken by `TrEnv'.ignore` instead". It is not.
`ignore`'s premise is `¬ safety ≤ ci.safety`, and `.unsafe` is the bottom of `DefinitionSafety`,
so `.unsafe ≤ ci.safety` holds for every `ci` (`ignore_unavailable_at_unsafe`,
`Verify/TypeChecker/Reduce.lean`). `TrEnv' .unsafe` therefore has **no rule at all** for an
unsafe inductive: they are currently *unhandled*, not handled-by-ignoring. The `safe` field
excludes them; it does not route them anywhere. (The twin claim at `Theory/Inductive/Decl.lean:703`
and the one in `Verify/Environment/Basic.lean`'s `AddInduct` section belong to other streams.)

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
* `Eq ∉ Lean.Kernel.Environment.primitives` (`Lean4Lean/Environment/Basic.lean`), so
  `checkName` raises nothing; `checkPrimitiveInductive` (`Lean4Lean/Primitive.lean`) returns
  `false` immediately when `isUnsafe`, so `allowPrimitive` plays no part.
* Positivity is skipped for an unsafe block: `Lean4Lean/Inductive/Add.lean:381`.
* `add_quot`/`addQuot` install the four quotient constants with `add_core`/`Environment.add`,
  which bypasses the type checker, and a `quotInfo` is unconditionally safe. `Quot.lift`'s stored
  type mentions `Eq`.

### 1.2 Machine-checked witness, lean4lean

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

elaborates with **no error** on the pinned toolchain. Appending `axiom useLift : …` (which is
`Quot.lift`'s own stored type) gives `error: (kernel) invalid declaration, it uses unsafe
declaration 'Eq'`. So the C++ kernel installs a safe constant it would itself refuse to accept.
`bugs-found.md` entry 15.

---

## 2. What was changed on the executable side

One check in `Lean4Lean/Quot.lean`, immediately after the `.inductInfo` destructuring:

```lean
if info.isUnsafe then fail "'Eq' is not a safe declaration"
```

Deliberate divergence from the C++ kernel; recorded in `divergences.md`. Kernel Arena: 185
correct / 6 either / 0 incorrect before and after.

---

## 3. Machine-checked, `sorry`-free (current state)

### 3.1 `Verify/EqSafety.lean` (owned)

* `TrEnv.eq_isUnsafe_false_of_quotInit` — **necessity**: if a `.safe` model exists for a
  quotient-initialized environment whose `Eq` is inductive, that inductive is not unsafe.
* `checkEqType.WF_safe` — **sufficiency**, read straight off the executable checker.
* `checkEqType.WF_visible` — `Eq` visible at every safety level.
* `checkEqType.WF_quotReady` — the reduction to `htr`. **Superseded** (see §0.1); kept as the
  record of how the premise was isolated.

### 3.2 `Verify/InductFlip.lean` (not owned; master `092c0f8`)

* `checkEqType.WF_quotReady_closed` —
  `(checkEqType env).WF fun _ => ∀ safety, (ves.venv safety).QuotReady`, with no premise beyond
  `wf`. This is `htr`, discharged.

### 3.3 `Verify/QuotConsts.lean` (new, owned, 794 lines, no `sorry`)

The whole `AddQuot` construction, which §6.1 of the old revision mis-stated as an afterthought
and which was in fact the *only* remaining blocker:

| § | content |
|---|---|
| 1 | `quotTypeE`, `quotMkTypeE`, `quotLiftTypeE`, `quotIndTypeE` — the four stored types as closed `Expr` literals; `quotCI`…`quotIndCI` the four `ConstantInfo`s. |
| 2 | `trExprS_quotType`, `trExprS_quotMkType`, `trExprS_quotLiftType`, `trExprS_quotIndType` — `TrExprS` against `quotConst.type`…`quotIndConst.type` (`Theory/Quot.lean`), each in the *staged* `VEnv` its predecessors produced. `Quot.lift`'s needs `Eq` in the model — that is where `QuotReady` is consumed. Proved by a `tr_tac` macro over `Theory/Typing/Meta.lean`'s `type_tac`. |
| 3 | `LocalContext.mkForall_list` (`mkBinding_eq` ∘ `mkBindingList_eq_fold`), `LocalContext.find?_mkLocalDecl`, `ofDecls`/`find?_ofDecls`/`mkForall_ofDecls`, then the four concrete `mkForall_quot*Type` computations. |
| 4 | `addQuot_unfold : Environment.addQuot env = … := rfl` — the whole `ExprBuildT`/`ReaderT`/`NameGenerator`/`Except` computation carried out **definitionally**; then `addQuot_eq`, which replaces the raw `mkForall`s by the §1 literals. |
| 5 | `trEnv_addQuot` — `TrEnv'.quot` fires: `AddQuot` built from `QuotReady` plus four `checkName` freshness facts. Plus `QuotFresh`, `le_quotVEnv`, `quotVEnv_mono`, `hasPrimitives_quotVEnv`, `safePrimitives_quotEnv`. |
| 6 | **`addQuot.WF'`** — the statement of `Verify/Environment.lean`'s `addQuot.WF`, proved with no vacuity crutch. |
| 7 | `QuotWit` — the non-vacuity witness (§5 below). |

Axioms of `addQuot.WF'` at master `961871b`: `propext`, `Classical.choice`, `Quot.sound`,
`Lean.Expr.{abstractRange_eq, abstract_eq, eqv_eq, hasLooseBVar_eq, lowerLooseBVars_eq}`,
`Lean.Level.instLawfulBEqLevel`, `Lean.Syntax.structEq_eq`. All in `Guard.lean`'s whitelist; no
new axiom. The `QuotWit` witness uses only the three standard axioms.

---

## 4. The edit this stream did **not** make (unowned file)

`Verify/Environment.lean` is not owned by this stream. The edit, **verified to compile** in a
sandbox copy of master together with the whole `Lean4Lean.Verify` library (all three guards
pass, `sorryAx` count unchanged):

```diff
-import Lean4Lean.Verify.Environment.Extension
+import Lean4Lean.Verify.Environment.Extension
+import Lean4Lean.Verify.QuotConsts
```

and, replacing the current `checkEqType.WF` (conclusion `False`) and `addQuot.WF` (discharged by
`False.elim`) in their entirety:

```lean
/-- The honest postcondition: on success `checkEqType` establishes `VEnv.QuotReady` at every
safety level.  Proved by `checkEqType.WF_quotReady_closed` (`Verify/InductFlip.lean`). -/
theorem checkEqType.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env) :
    (checkEqType env).WF fun _ => ∀ safety, (ves.venv safety).QuotReady :=
  checkEqType.WF_quotReady_closed wf

/-- Non-vacuous: see `addQuot.WF'` (`Verify/QuotConsts.lean`). -/
theorem addQuot.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env) :
    (Environment.addQuot env).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧ ∀ safety, ves.venv safety ≤ ves'.venv safety :=
  addQuot.WF' wf
```

No import cycle: `Verify/Environment.lean` is imported only by `Verify.lean` and
`Verify/Bridge.lean`, neither of which is in `QuotConsts.lean`'s cone.

`checkEqType.WF`'s `wf` argument becomes genuinely used at that point; today it is used only to
reach `no_inductInfo`.

---

## 5. Non-vacuity, and the honest limit

`addQuot.WF'` is proved **without** any vacuity crutch: it constructs the model rather than
deriving `False`. But its hypotheses are, today, jointly unsatisfiable on the non-initialized
branch, and this must be said plainly:

> `wf : ves.WF env` together with `checkEqType env = .ok ()` forces `Eq` to be an `.inductInfo` in
> a kernel environment that has a `VEnvs` model, and `VEnvs.WF.no_inductInfo`
> (`Verify/InductFlip.lean`) refutes that for as long as `AddInduct` has no constructors.

So `addQuot.WF'` is *live* today only on the `quotInit = true` branch. What §7 of
`Verify/QuotConsts.lean` machine-checks is that nothing in the construction is vacuous on its own
terms, at a concrete witness:

* `QuotWit.envEq` — `Kernel.Environment.empty `main` with `Eq` added as an **axiom** of exactly
  the type `eqConst` models (`eqStoredType `u`).
* `QuotWit.trEnv_envEq` — `TrEnv safety envEq venvEq` at every safety level, via `TrEnv'.axiom`.
* `QuotWit.trEnv_addQuot_wit` — `trEnv_addQuot` fires: `TrEnv'.quot` is reachable and `AddQuot` is
  inhabited at a concrete environment, at every safety level.
* `QuotWit.quotVEnv_venvEq_contents` — the resulting model really holds `quotConst`,
  `quotMkConst`, `quotLiftConst`, `quotIndConst`, `eqConst` and the ι-rule `quotDefEq`. The step
  is not a no-op.

None of §7 is used by §6, and nothing in §6 depends on how `Eq` got into the environment. When
the `AddInduct` flip lands and `Eq` arrives as an inductive, §6 applies verbatim — no further
work on the quotient side.

**This is the whole remaining dependency**: `addQuot.WF` is now blocked on `AddInduct`'s
emptiness alone, exactly like `addDecl.WF`'s `inductDecl` branch, and on nothing specific to
quotients.

---

## 6. Master is red (`961871b`), and the fix

`961871b` ("pure containers replace the persistent HAMT and trie") introduced a new
`Lean4Lean.LocalContext` type replacing `Lean.LocalContext`, and **broke
`Verify/InductFlip.lean`** — which is not owned by this stream, so the fix below was verified in
a sandbox and **not applied**. Four errors, all in §3.1 of that file, all namespace/API drift:

```diff
-open Lean.LocalContext in
-theorem _root_.Lean.LocalContext.mkForall_single {lctx : LocalContext} {fv : FVarId}
+open Lean4Lean.LocalContext in
+theorem _root_.Lean4Lean.LocalContext.mkForall_single {lctx : LocalContext} {fv : FVarId}
@@
-theorem _root_.Lean.LocalContext.wf_empty : ({} : LocalContext).WF := .nil
+theorem _root_.Lean4Lean.LocalContext.wf_empty : ({} : LocalContext).WF := .nil

-theorem _root_.Lean.LocalContext.toList_empty : ({} : LocalContext).toList = [] := by
-  show List.filterMap id (PersistentArray.toList' _).reverse = []
-  rw [show (({} : LocalContext).decls) = .empty from rfl, PersistentArray.toList'_empty]
-  rfl
+theorem _root_.Lean4Lean.LocalContext.toList_empty : ({} : LocalContext).toList = [] := rfl

-theorem _root_.Lean.LocalContext.find?_empty {fv} : ({} : LocalContext).find? fv = none := by
+theorem _root_.Lean4Lean.LocalContext.find?_empty {fv} : ({} : LocalContext).find? fv = none := by
   rw [LocalContext.wf_empty.find?_eq_find?_toList, LocalContext.toList_empty]; rfl

-theorem _root_.Lean.LocalContext.find?_mkLocalDecl_empty {fv n ty bi kind} :
+theorem _root_.Lean4Lean.LocalContext.find?_mkLocalDecl_empty {fv n ty bi kind} :
     (({} : LocalContext).mkLocalDecl fv n ty bi kind).find? fv =
       some (.cdecl 0 fv n ty bi kind) := by
   rw [(LocalContext.wf_empty.mkLocalDecl LocalContext.find?_empty).find?_eq_find?_toList,
-    LocalContext.mkLocalDecl_toList LocalContext.wf_empty.decls_wf,
-    LocalContext.toList_empty]
+    LocalContext.mkLocalDecl_toList, LocalContext.toList_empty]
   simp [Lean.LocalDecl.fvarId]
@@
-  rw [LocalContext.mkForall_single LocalContext.find?_mkLocalDecl_empty rfl rfl]
+  rw [Lean4Lean.LocalContext.mkForall_single LocalContext.find?_mkLocalDecl_empty rfl rfl]
```

`Verify/QuotConsts.lean` as delivered is already ported to the new API and **will not compile
until the above lands**, because it imports `InductFlip.lean`. With the patch applied, the whole
`Lean4Lean.Verify` library builds green.

---

## 7. What to pick up first

1. **Apply §6's `InductFlip.lean` patch.** Master does not build without it.
2. **Apply §4's `Verify/Environment.lean` edit.** Verified to compile; it removes the last
   vacuity crutch from that file.
3. **`AddInduct`'s constructors** (`Verify/Environment/Basic.lean`, another stream's
   `AddInductStages` flip). After that, `addQuot.WF` is live end-to-end with no further quotient
   work, and `addDecl.WF`'s `inductDecl` `sorry` stops being a *false* statement.
4. **Unsafe inductives at `safety = .unsafe`** (§0.3). Not a proof obligation on
   `Verify/Environment/Induct.lean` — a design question: `TrEnv'` needs a rule that admits an
   unsafe block at `.unsafe` without a positivity witness, or `VEnvs.WF` must be weakened there.
   Nothing routes them today.
5. **Audit the other `add_core` sites for the same shape of bug.** The defect's real form is "a
   constant installed without type checking, whose stored type names a constant whose safety was
   never constrained". `addQuot` is the only such site today, but `addInductive`'s
   recursor/constructor installation is structurally similar. Nothing was checked there.

---

## 8. Technique notes (for whoever writes the next `TrExprS`-heavy file)

* **`tr_tac`.** `Verify/QuotConsts.lean` §2 defines a four-line `first`-combinator macro that
  discharges a `TrExprS` goal structurally, delegating the `IsType`/`HasType` side conditions to
  `Theory/Typing/Meta.lean`'s `type_tac`. All four quotient types, `Quot.lift`'s seven binders
  included, go through in 3.6 s. Watch the `;` precedence inside `first | … | …`: write
  `exact TrExprS.bvar rfl`, **not** `refine TrExprS.bvar ?_; rfl` — the latter parses so that the
  alternative silently fails and `first` falls through to a wrong constructor.
* **`mkForall` over a `withLocalDecl` chain.** Do not compute `mkBinding` by hand. `ofDecls`
  (a list of binder data) plus `mkForall_ofDecls` reduces every such goal to
  `xs.foldr (fun d e => .forallE d.2.1 d.2.2.1 (e.abstract1 d.1) d.2.2.2) b`, which `simp` with
  the pairwise `≠`s finishes.
* **Unfolding a monadic checker.** `addQuot_unfold` is `rfl`. Stating the right-hand side with the
  *raw* `mkForall` applications (as `def`s over `qfv 1 … qfv 6`) and letting the kernel do the
  `ExprBuildT`/`ReaderT`/`NameGenerator`/`Except` reduction is far cheaper than driving `simp`
  through it, and it is a stronger check: it is the kernel, not a simp set, that certifies the
  four stored types.
* **The `NameGenerator` ids.** `ExprBuildT.run` starts at `{ namePrefix := `_uniq, idx := 1 }` and
  `withFreshId` is a *reader*, not state: ids are reused across sibling blocks
  (`α,r,a = 1,2,3`; then `r,a,β,f,b = 2,3,4,5,6`; then `β,q = 4,5`). Harmless, because each
  `mkForall` reads the context in force at its own point — but a hand computation that assumes
  monotone ids gets `Quot.ind` wrong.
