# `checkPrimitiveDef.WF.rest` is **closed**

Stream scope: `Lean4Lean/Verify/Typing/Expr.lean`, `Lean4Lean/Primitive.lean`,
`Lean4Lean/Verify/Primitive.lean`, `Lean4Lean/Verify/Environment/Boundaries.lean`, and new
files under `Lean4Lean/Verify/` (this round added `Lean4Lean/Verify/PrimitiveWF.lean`).

Everything below is marked **[machine-checked]** (a `lake build`, a census run, a Kernel Arena
run, `Verify/Guard.lean`, or `scripts/primitive-wf-refutation.lean` produced it) or **[argued]**.
The central claim is machine-checked.

| gate | before | after |
| --- | --- | --- |
| sorry census | **19** **[machine-checked, canonical instrument]** | **18** **[machine-checked, reduced cone — see §7]** |
| `checkPrimitiveDef.WF.rest` | `sorry` (2 of 4 branches open) | **proved, no `sorry`** **[machine-checked]** |
| `lake build Lean4Lean.Verify.Environment.Boundaries` | green | green, **no `declaration uses sorry`** **[machine-checked]** |
| Kernel Arena (`lean4lean-local`) | 185 / 6 / 0 | **185 / 6 / 0** **[machine-checked, three runs across the round]** |
| `scripts/primitive-wf-refutation.lean` | both witnesses REJECTED | **both still REJECTED, both real primitives still accepted** **[machine-checked, four runs]** |
| `Verify/Guard.lean` guards 1–3 | 25 axioms ✓, whitelist ✓, gaps 54/54 ✓ | 25 axioms ✓, whitelist ✓, **gaps 52/54 ✓** **[machine-checked]** |
| `run_meta` self-test (all 18 primitives) | accepted | accepted **[machine-checked, every build]** |

`Lean4Lean/Primitive.lean` **is changed**; `divergences.md`'s `checkPrimitiveDef` bullet gains
clause *Twelfth*.

---

## 0. Bottom line

1. **`Nat.gcd` and `Nat.bitwise` are proved.** `checkPrimitiveDef.WF.rest` no longer contains a
   `sorry`; the census drops 19 → 18.
2. The route was **not** the one the previous handoff and the brief described. What made the two
   branches provable was not "the fuel induction, everything else is in place" but four further
   things the recognizer did not check. Each was found by *writing the supplier's side* — the
   `M.WF` specification of `unfoldNatWellFounded` and of the branch — and each was
   undischargeable at the call site as it stood. §1.
3. `Lean4Lean/Verify/PrimitiveWF.lean` (new, ~2000 lines) holds all of it. `Verify/Primitive.lean`
   gained one genuinely new *concept*: `VEnv.ReflectsCondAppAll` — the conditional-selection
   predicates are **not monotone**, and `Nat.bitwise`'s field is relativized to an arbitrary later
   environment. §3.
4. Two measuring instruments (`scripts/sorry-census.lean`, `scripts/dup-names.lean`) are
   **currently broken by a name collision that is not this stream's**. §7.

---

## 1. The four blockers, and how each was found

None of these is visible from the proof side; all four were found by writing the *specification*
of the code that was supposed to supply the hypothesis.

**(a) `Condition.check.WF_bool` demands `c.vlctx = []`, and the recognizer called
`Condition.bool.check` under three binders.** So the `ReflectsCondApp1` the `Nat.eager` step needs
could not be obtained at all: its supplier's hypothesis was unsatisfiable at the call site.
*Fix (implementation):* hoist `Condition.bool`'s check out of `unfoldNatWellFounded` into the two
branches, where the local context is empty. Accept-set neutral (`Condition.bool` and its
`iteTypes` are closed).

**(b) Nothing constrained `fix.go`'s *type*.** The fuel induction's step hypothesis is "the
recursive call's fuel bound is a proof of `x' < fuel'`", and there is no way to get it: the only
source is the well-typedness of the call, and `VExpr.WF.app_inv` hands back an *existential*
domain. The proved `Nat.mod` / `Nat.div` branches do not have this problem because their `go` is
a **constant** whose type they pin with `checkedTypeIs q(Nat.modCore.go) q(…)`.
*Fix (implementation):* `NatWFUnfold.goType` — the caller now checks
`fix.go α motive h F : ∀ (fuel : Nat) (x : α), Nat.succ (h x) ≤ fuel → motive x`, at the base
context. `VEnv.goAppWF_typed` is the resulting extraction lemma, `VEnv.ok_of_goApp` its packaging.

**(c) Nothing forced `go`, `pack` and the measure to be independent of the recursion
variables.** The induction steps `go` and `pack` to *different* arguments (`gcd m n → gcd (n%m) m`),
so `GO` and `PACK` must be the **same closed terms** at every level; if they mentioned `m` or `n`
the recursive call would be about `GO[n%m, m]` while the induction hypothesis is about `GO[m,n]`,
and the induction cannot even be stated. `whnfCore` of `e m n` may perfectly well return a
`fix α motive h F a₀` whose components mention the binders.
*Fix (implementation):* `checkNoMVarNoFVar` on all of them, and the base-context `checkedTypeIs`
for `go`/`measure`/`pack` (which is what makes the *translations* closed, via `closedN_of_nil`).
**[argued]** that no witness was constructed for this one: constructing a definition whose
unfolding produces an fvar-dependent `go` *and* passes the remaining checks is real work, and
"no witness" is not evidence of truth — the point is derivability, and the induction was
unstateable.

**(d) `VEnv.ReflectsCondApp` / `ReflectsCondApp1` / `ReflectsCondAppD` are not monotone.** Their
premise `VExpr.WF env 0 [] (condApp …)` is in **negative** position. `VEnv.ReflectsNatBitwise` is
relativized to an arbitrary extension `env'` and to a combinator `f` that exists only there, and
every conditional in `Nat.bitwise`'s body scrutinises `f`. So the conditional facts were needed at
`env'` and could not be transported.
*Fix (verification):* `VEnv.ReflectsCondAppAll` (and `…1All`, `…DAll`) —
`∀ env', env ≤ env' → env'.WF → env'.ReflectsCondApp …`. Every *ingredient* of
`reflects_condApp_of_checkITE` is an `IsDefEqU`, a `HasType` or a closedness fact, and all three
are monotone; only the assembled predicate is not. `Condition.check.WF` now produces the
relativized form and its four consumers instantiate it with `.self` at their own environment.

**Also corrected, from the previous handoff:** `TypeChecker.Inner.whnfCore.WF` and
`unfoldDefinition.WF` **exist and are proved** (`Verify/TypeChecker/Basic.lean`); the "missing
`whnfCore.WF`" that was relayed for several rounds was never missing. What was missing at the `M`
level were the wrappers, added here as `TypeChecker.whnfCore.WF` / `TypeChecker.unfoldDefinition.WF`.

## 2. Two side conditions, derived rather than checked

`trExprS_weakBV0` — the step that carries a closed term's translation under a `.forallE` binder —
needs `TrExprS.IsUnique e` and `e.looseBVarRange' = 0`.

* `IsUnique` (no `Expr.proj`) is **checked**: `Lean4Lean.Environment.noProj`, a
  `Lean4Lean.anySubterm` scan. It is *not* a fresh recursion, deliberately: every recursive
  definition gets an `f._unsafe_rec` companion and `Verify/Guard.lean`'s check 3 counts those, so
  a new walk would enlarge the frozen implementation-gap list. The first version of this round
  *did* violate guard 3 for exactly that reason; `anySubterm`/`replaceNoCacheT` is the repo's own
  total walk and is already whitelisted.
* `looseBVarRange' = 0` is **not checked** — it is *derived*: `TrExprS.looseBVarRange_le` says
  `TrExprS env Us Δ e e' → e.looseBVarRange' ≤ Δ.length`, because `TrExprS.bvar` reads
  `VLCtx.find?`, which returns `none` on the empty context. At the base context that gives `= 0`.
  This is strictly better than a check and it removed a second guard-3 entry.

## 3. What is where

`Lean4Lean/Verify/PrimitiveWF.lean`, in dependency order:

* `TypeChecker.whnfCore.WF`, `TypeChecker.unfoldDefinition.WF` — `M`-level wrappers.
* `TrExprS.isUnique_of_noProj`, `VLCtx.find?_inl_lt`, `TrExprS.looseBVarRange_le`,
  `trExprS_looseBVarRange_nil` — §2.
* `NatWFUnfold.Good`, `TypeChecker.unfoldNatWellFounded.WF` — the unfolder's specification. Its
  postcondition is *only* the six `FVarsIn`s and the four `IsUnique`s: search is not trusted.
* `VExpr.goTypeWF`, `VEnv.goAppWF_typed`, `trExprS_goTypeWF_inv'`, `TypeChecker.trExprS_goAppWF`,
  `trExprS_packApp`, `trExprS_packApp3`, `trExprS_measApp`, `hasType_goApply`.
* `VExpr.natEq`, `trExprS_natEq_inv'`, `trExprS_natEqApp_inv'`,
  `VEnv.ReflectsCondAppD.natEq_eq`, `TypeChecker.Condition.check.WF_natEq_pinned`.
* **`Nat.gcd`:** `VEnv.reflects_fuel_gcd`, `VExpr.gcdCtx`, `IsDefEqU.instGcd`, `gcd_step`,
  `VExpr.eagerFuelAt`/`eagerITEAt`, `gcd_entry`, `eagerITE_reduce`,
  `trExprS_gcdEntry_inv'`, `trExprS_gcdGo_inv'`, **`VEnv.reflects_gcd_of_equations`**.
* **`Nat.bitwise`:** `VExpr.bitSel`/`bitParityG`/`bitwiseFuelThen`/`bitwiseFuelElse`/
  `bitwiseFuelRhs`, `VEnv.reflects_fuel_bitwise`, `VExpr.bitwiseCtx`, `IsDefEqU.instBitwise`,
  `bitwise_step`, `IsDefEqU.instBw3`, `bitwise_entry`, `trExprS_bitSel_inv'`,
  `trExprS_natEqIte_inv'`, `trExprS_bitParity_inv'`, `trExprS_bitwiseEntry_inv'`,
  `trExprS_bitwiseGo_inv'`, **`VEnv.reflects_bitwise_of_equations`**,
  `reflectsNatBitwise_of_open`.

`Lean4Lean/Verify/Primitive.lean` gained `ReflectsCondAppAll` / `ReflectsCondApp1All` /
`ReflectsCondAppDAll` with their `.self` accessors and the three `_all_of_check*` producers, and
`Condition.check.WF` / `WF_bool` / the pinned forms now produce the relativized versions.

`Lean4Lean/Verify/Environment/Boundaries.lean` — the two branches, ~620 lines. They are the same
shape as the `Nat.mod` branch: collect the checks, invert the right-hand sides, hand the
equations to `reflects_*_of_equations`, and close `preserves` with `preserves_glue` plus
`reflectsNNN_of_open` (`gcd`) / `reflectsNatBitwise_of_open` (`bitwise`).

## 4. Traps that cost time, worth not re-deriving

* **Declaring `structure Lean4Lean.Foo.Bar` while inside `namespace Lean4Lean` creates a
  `Lean4Lean.Lean4Lean` namespace**, and from then on *every importing file* that says
  `open Lean4Lean` inside `namespace Lean4Lean` opens that near-empty namespace instead of the
  real one. The visible symptom is nowhere near the cause: `Verify/Environment/Extension.lean`
  started reporting `The environment does not contain 'List.Forall₂.and_mem'`, because
  `Lean4Lean/Std/Basic.lean` keeps the `List` API inside `namespace Lean4Lean` and dot notation
  could no longer reach it. Bisected by importing one module at a time into a six-line file.
  Write `namespace Environment.NatWFUnfold` … `end`, never a dotted declaration name.
  Corollary: **`lake build` with no target is the only thing that catches this** — every
  narrowed target stayed green.
* **`open Lean4Lean.Environment` inside `namespace Lean4Lean` silently opens nothing** (Lean
  reads it as `_root_.Lean4Lean.Lean4Lean.Environment` and warns). That warning is the *same*
  bug as the previous bullet, seen a step earlier. Fully qualify.
* `ClosedN.instN_eq (Nat.zero_le 0)` pins the depth to 0 and then fails to fire at depth 2 or 3.
  Always `(Nat.zero_le _)`.
* `simp only [Lean.mkAppN]` leaves `Array.foldl mkApp f #[a,b]`; the whole family
  `Lean.mkApp, mkApp2, mkApp3, mkApp4, mkApp5, mkAppN` has to be in the set together.
* A `have x := …` in a `do` block is a `letFun`; `simp only []` before `split`, or the `split`
  finds no `if`.
* An `IsUnique` argument placed *before* the `TrExprS` hypothesis cannot be elaborated (the term
  it is about is not determined yet). Put it last.
* `VExpr.natLit 0` and `VExpr.natZero` are `rfl`-equal but `rw` will not match across them:
  normalise with `VExpr.natLit_zero` first.
* A `.lam`'s domain from `trExprS_lam_inv'` must be *named* (`obtain ⟨EAd, …⟩`), or every later
  `trExprS_weakBV0 (A := _)` has an unsolvable placeholder.
* Passing a `HasType`/`TrExprS` through `by simpa using h` at a five-binder context usually fails
  where passing `h` **raw** succeeds: `.lift` on a closed term is definitional, and unification
  reduces it while `simp` does not.

## 5. Corrections to the brief

* *"`reflects_natBitwise_go` is already proved; all 13 hypotheses confirmed load-bearing."*
  Correct that it is proved, but it is **not usable** for this branch: it recurses through
  `Nat.bitwise` itself at a *smaller argument*, while the recognizer's equation recurses through
  `fix.go` at a *smaller fuel*, and fuel-invariance is not derivable (the previous handoff §2 is
  right about that). `VEnv.reflects_fuel_bitwise` is the fuel-indexed replacement; it reuses
  `reflects_natBitwise_go`'s conditional argument almost verbatim but not its statement.
* *"Point 3 eliminates the `whnfCore.WF`/`unfoldDefinition.WF` prerequisite entirely."* True, but
  the prerequisite was never missing (§1, last paragraph).
* *"`.rest` … drops only when all four branches close."* Correct, and it did.
* *"`.rest` needs `set_option maxHeartbeats 4000000`."* Still true; the file also needs it for
  the new `Verify/PrimitiveWF.lean` lemmas (`1000000` there, `2000000` for
  `trExprS_bitwiseGo_inv'`).

## 6. What is *not* claimed

* The proof rests on the tree's standing sorry-backed lemmas — `IsDefEqU.forallE_inv`
  (via `VEnv.HasType.piUniq`, used by `VExpr.WF.app_arg_typed`), `TrProj.uniq`, `weakN_iff`.
  That is **inherited taint**, unchanged by this round: those lemmas were already in
  `checkPrimitiveDef.WF`'s forward cone through the `Nat.mod` branch.
* `checkPrimitiveDef.WF.rest` being proved does not move `kernel_sound`; guard 2 still prints
  *proof INCOMPLETE*. The remaining 18 are listed in §7.

## 7. Measuring, and an instrument that is currently broken **[machine-checked]**

`scripts/sorry-census.lean` and `scripts/dup-names.lean` both fail to *import*:

```
import Lean4Lean.Verify.Typing.DefEqCtx failed, environment already contains
'Lean4Lean.VEnv.HasArgs.defeqDFC.match_1_1' from Lean4Lean.Theory.Typing.PatternRules
```

`Lean4Lean/Theory/Typing/PatternRules.lean` and `Lean4Lean/Verify/Typing/DefEqCtx.lean` declare
the same auxiliary and **cannot be imported together**; both are reachable from
`Experimental/ConeJoin.lean`, which both scripts import. Neither file is this stream's — the
working tree's only modifications are `Lean4Lean/Primitive.lean`,
`Lean4Lean/Verify/Primitive.lean`, `Lean4Lean/Verify/Environment/Boundaries.lean` and the new
`Lean4Lean/Verify/PrimitiveWF.lean`. This is exactly the failure mode `dup-names.lean` exists to
catch, and it is live.

The `18` above was therefore measured with the census script over a **reduced cone** —
`Verify.Guard` plus `Verify.Environment`, `Theory.Typing.ChurchRosser`, and the
`Verify.*` leaves of `ConeJoin` that do not pull `PatternRules`. That cone reproduces the
canonical run's module list exactly, minus `checkPrimitiveDef.WF.rest`:

```
Theory.Inductive.Decl 1, Theory.Typing.ChurchRosser 1, Theory.Typing.Injectivity 6,
Theory.Typing.UniqueTyping 1, Verify.Environment 1, Verify.Soundness 2,
Verify.TypeChecker.InferType 1, Verify.TypeChecker.IsDefEq 2, Verify.TypeChecker.WHNF 1,
Verify.Typing.Lemmas 2   — TOTAL 18
```

`dup-names.lean` over the same reduced cone reports **no duplicates**, so nothing this round
added collides; it says nothing about the `PatternRules` side.

Independently checked and *not* the same thing: `Verify/Environment/Extension.lean` went red
mid-round with `The environment does not contain 'List.Forall₂.and_mem'`. That one **was** this
stream's — see §4, first bullet — and is fixed; `lake build` with no target is green.

## 8. Pick up first

1. **Restore the instruments** — split the duplicated auxiliary out of
   `Theory/Typing/PatternRules.lean` or `Verify/Typing/DefEqCtx.lean` (whichever owns it), then
   re-run the canonical census and `dup-names`. Until then no one can measure the whole tree.
2. The remaining 18 are unchanged in character: `TrProj.uniq` (89 users) and
   `IsDefEqU.forallE_inv_stratified` (250) dominate.
3. Nothing in `Verify/PrimitiveWF.lean` is provisional; it has no `sorry` of its own.
