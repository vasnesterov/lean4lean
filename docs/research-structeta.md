# Scoping `Verify/TypeChecker/IsDefEq.lean`'s two sorries

`tryEtaStructCore.WF` (`:183`) and `isDefEqUnitLike.WF` (`:444`). Scoping only; no lines
written. Claims tagged **[verified]** (read from source) or **[inferred]**. Tree at
`ab62157`.

---

## Bottom line

**Neither statement is false. Both are *currently vacuous*, and both would need a spec rule
that does not exist the moment they stop being vacuous.** That is two findings, and they
point in opposite directions, so the decision is not "prove them" or "don't" — it is which
of two different things to do.

1. **The abstract spec cannot express either fact.** Both rest on surjective pairing —
   `e ≡ mk p (proj 0 e) … (proj (n-1) e)` — which is not derivable from ι and cannot be a
   `VDefEq`. This is **already documented**: `docs/design-inductive.md:724–765` names
   `tryEtaStructCore` and `isDefEqUnitLike` explicitly and proposes a new `VEnv.IsDefEq`
   constructor `structEta`, calling it *"the single largest unplanned item this design
   uncovers"*. My independent analysis reached the same place; §2 records the one thing
   the design note does not cover.
2. **But neither postcondition is reachable today.** `AddInduct`
   (`Verify/Environment/Basic.lean:106–108`) is still an inductive with **no constructors**
   (`-- TODO`), so no `TrEnv'` can contain an `.inductInfo`. Both checks are gated behind an
   `.inductInfo` lookup, so both functions provably return `false`, and both `sorry`s are
   **closeable today by a vacuity argument** — with no `structEta`, no `TrProj`, and no
   spec change.

**Recommendation: do not close them vacuously.** §5. The sorry is currently the only marker
in `Verify/` that `structEta` is missing; a vacuity proof removes the marker, contributes no
soundness content, and is discarded wholesale when `AddInduct` lands. If the goal is to make
these two lines mean something, the work is `structEta` in the spec — a different, larger,
and separately schedulable task.

---

## 1. What the two checks actually do **[verified]**

`tryEtaStructCore` (`TypeChecker.lean:656–668`): `s` must be a *saturated constructor
application* `C.mk ps fs` of a non-recursive structure; then `inferType t ≡ inferType s`;
then `proj i t ≡ fs[i]` for every field. Concludes `t ≡ s`.

`isDefEqUnitLike` (`TypeChecker.lean:849–857`): `whnf (inferType t)` has head `.const I`,
where `I` is `isRec := false`, one constructor, `numIndices := 0`, and that constructor has
`numFields := 0`; then `tType ≡ inferType s`. Concludes `t ≡ s`.

Worth noting the two conditions coincide: `isNonRecStructure`
(`Environment/Basic.lean:49–52`) is exactly `isRec := false ∧ ctors = [_] ∧ numIndices = 0`,
byte-identical to Lean's own (`~/lean4/src/Lean/Structure.lean:361–364`). So
**`isDefEqUnitLike` is the zero-field special case of `tryEtaStructCore`'s structure
condition**, and the two sorries want the same abstract rule at different arities.

They differ in one way that matters for cost: with zero fields there are **no projections**,
so `isDefEqUnitLike` needs none of the `TrProj` machinery that `tryEtaStructCore` does.

## 2. The spec gap, and the part the design note does not cover

`VEnv.IsDefEq` (`Theory/Typing/Basic.lean:18–56`) has 13 constructors — `bvar symm trans
sortDF constDF appDF lamDF forallEDF defeqDF beta eta proofIrrel extra`. None is struct-eta,
unit-like, or K. **[verified]** `Expr.proj` has no `VExpr` counterpart either; the abstract
projection is a recursor application (`Theory/Inductive/Structure.lean`, `projTerm`), and ι
fires only on constructor applications — so `t ≡ mk (proj t)` for a *variable* `t` is
unreachable. `design-inductive.md:726–730` states this and rules out encoding it as a
`VDefEq`: the left-hand side is a variable, and `Pattern` only matches `const`-headed spines.

**The part not covered there.** `design-inductive.md`'s proposed `structEta` carries
`(D.lvl.inst ls).IsNeverZero` — F16's condition, taken from `toCtorWhenStruct`. But **neither
of these two checks tests the level**: `tryEtaStructCore` tests `isNonRecStructure`, and
`isDefEqUnitLike` tests only `isRec`/`ctors`/`numIndices`/`numFields`. Both therefore fire on
`Prop` structures — `And`, `True` — where the proposed `structEta` would not apply.
**[verified]**

That is not a hole; it is a case split, and the `Prop` half is already free:

| | `Prop` case (`D.lvl ≈ 0`) | non-`Prop` case |
|---|---|---|
| `tryEtaStructCore` | `IsDefEq.proofIrrel` — both sides inhabit the same proposition, and the check establishes `inferType t ≡ inferType s` | `structEta` + field congruence |
| `isDefEqUnitLike` | `proofIrrel` | `structEta` at zero fields, twice, then `trans` |

The `Prop` half is the same argument `design-inductive.md:618–637` uses to show K-like
reduction needs no new rule. So a correct `structEta` plan must either drop `IsNeverZero`
or pair the rule with a `proofIrrel` branch at each of these three call sites. **[inferred]**
Worth fixing in the design note before anyone implements against it.

## 3. Neither statement is false **[inferred, with the reasoning]**

The instruction was to check truth before proving, `isDefEqUnitLike` being the shape that has
been false three times here — a fast-path whose postcondition claims more than the check
establishes. I looked for that and did not find it:

* `isDefEqUnitLike` reads its constructor out of `I`'s own `ctors` list, so `c` cannot belong
  to another type; parameters are pinned by `tType ≡ inferType s`; `numIndices = 0` and
  `numFields = 0` leave `I ps` with exactly one closed inhabitant.
* `tryEtaStructCore` never compares the constructor's *parameter* arguments directly, only
  its fields — but the parameters are pinned by `inferType t ≡ inferType s = S ps`, and
  applying `structEta` at that same `ps` needs no injectivity of `S`.
* `tryEtaStructCore` does not check that `t` is a non-constructor, despite its comment. Sound
  anyway: if `t = C.mk ps bs` then `proj i t` reduces to `bs[i]` and the check compares the
  fields, which is what `isDefEqApp` would have done.

Both are true in the intended semantics — `SetModel/Inductive.lean` builds inductives as
least fixed points with injective constructors and no junk, which is exactly surjective
pairing. They are **underivable, not false**. Note the asymmetry with `sort_inv`: a rigorous
*refutation* of derivability would need a countermodel, which the set model does not supply
because the set model validates struct-eta.

## 4. The vacuity, and how it would be proved **[verified for the gate; [inferred] for the route]**

`AddInduct` (`Verify/Environment/Basic.lean:106–108`) has no constructors. It is the only
premise of `TrEnv'.induct` (`:196–199`), the only rule that introduces an inductive. Hence
`TrEnv'.no_inductInfo` (`Verify/Environment/Extension.lean:17`): a `TrEnv'` constant map
contains no `.inductInfo`. This is the same gate that already makes `addQuot.WF` and
`checkEqType.WF` vacuous — see the comment at `Verify/Environment.lean:118–122` and its use
of `no_inductInfo` at `:133`.

Both checks are gated on it. `isDefEqUnitLike` matches `.inductInfo` directly.
`tryEtaStructCore` matches `.ctorInfo` and then calls `env.isNonRecStructure fInfo.induct`,
which needs an `.inductInfo` — so it too can never reach `return true`.

**The one wrinkle.** `no_inductInfo` is proved only for `safety = .unsafe`
(`Extension.lean:17`), because the `TrEnv'.ignore` rule (`Basic.lean:137–140`) admits an
arbitrary hidden constant when `¬ safety ≤ ci.safety`, which is unsatisfiable at `.unsafe`
and satisfiable at `.safe`. `Verify/Environment.lean:133` works around this by instantiating
the `VEnvs` bundle at `.unsafe` (`wf.tr (safety := .unsafe)`) — but `VContext` carries a
single `trenv : TrEnv safety env venv` (`Verify/TypeChecker/Basic.lean:195`), **not** the
bundle, so that workaround is unavailable here. **[verified]**

Two ways out, both small:

* **(V1)** a safety-uniform disjointness lemma —
  `TrEnv' safety C Q venv → C.find? n = some (.inductInfo i) → venv.constants n = none`.
  The `ignore` case is the new one and should go through `TrEnv.find?_iff` plus the fact
  that `TrConstant`/`TrDefVal` have no `.inductInfo` shape. ~20–30 lines. **[inferred]**
* **(V2)** give `VContext` access to the `.unsafe` translation, mirroring `VEnvs`. Larger and
  touches a structure other proofs depend on.

Then each sorry is: run `inferType.WF`/`whnf.WF` to get a `TrExprS` for the inferred type,
use `AppStack.build` (`Verify/Typing/Lemmas.lean:2214`) to reach the head, invert
`TrExprS.const` to get `venv.constants I = some _`, and contradict. ~30–40 lines each.

**Total for the vacuous close: ~90–110 lines.** **[inferred]**

## 5. Recommendation

**Do not close them vacuously.** Three reasons:

1. **It contributes nothing and costs the marker.** These two `sorry`s are the only place in
   `Verify/` that records the absence of `structEta`. `design-inductive.md` records it too,
   but a `sorry` is what a build surfaces. Closing them makes the refinement layer look
   complete on structure-eta when it is not.
2. **It is discarded on landing.** The moment `AddInduct` gains constructors, the vacuity
   proof stops compiling and the real proof — `structEta`, `TrProj` functionality, an
   `IsStructure` bridge — has to be written from scratch. Nothing carries over.
3. **The precedent is already flagged as a problem, not a pattern to follow.**
   `PLAN.md:86–88` records that `AddInduct` being empty makes `addQuot.WF` and
   `checkEqType.WF` vacuous and that "the refinement layer currently says nothing about
   `stdPrelude`". Adding two more to that list is motion, not progress.

**If the sorry count matters more than the marker**, V1 + the two proofs is ~100 lines and
carries no risk — but it should be labelled in-file as vacuous, the way
`Verify/Environment.lean:136` labels `addQuot.WF`.

**What I would actually schedule instead**, in order:

| Item | Est. | Note |
|---|---|---|
| Fix `design-inductive.md`'s `structEta` for the `Prop` case (§2) | doc only | do before anyone implements against it |
| `structEta` constructor in `Theory/Typing/Basic.lean` | 10 | the statement |
| `structEta` case in every induction over `IsDefEq` | **200–400** | `Lemmas.lean`, `Strong.lean`, `UniqueTyping.lean`, `ChurchRosser.lean`, `Verify/` — mostly one-liners, as `eta`'s are, but the count is large and several files have other owners |
| `NormalEq.structEtaL`/`structEtaR` + `ChurchRosser` cases | 100–200 | mirrors `etaL`/`etaR` (`ChurchRosser.lean:104–111`) |
| `isDefEqUnitLike.WF` for real | 60–100 | needs `structEta` + a kernel→abstract `IsStructure` bridge; **no `TrProj`** |
| `tryEtaStructCore.WF` for real | 150–250 | additionally needs `TrProj` functionality — `TrProj.uniq` (`Verify/Typing/Lemmas.lean:929–935`) is `sorry` and blocked on const-application injectivity (ledger I1/I13) |

Two scheduling facts fall out of that table:

* **`isDefEqUnitLike` is much cheaper than `tryEtaStructCore`** and is not blocked on
  `TrProj` at all — zero fields means no projections. If only one is done, it is that one.
* **`tryEtaStructCore` is blocked twice over**: on `structEta` *and* on `TrProj.uniq`, whose
  own note (`Verify/Typing/Lemmas.lean:929–933`) says it needs injectivity of a constant
  application, i.e. a Church–Rosser consequence. It should not be scheduled until both clear.

## 6. What I did not do

I did not attempt a rigorous non-derivability proof for either statement (§3 explains why
the set model cannot supply one), and I did not verify V1 — the safety-uniform disjointness
lemma — beyond identifying `TrEnv.find?_iff` as the intended ingredient. If the decision is
to close them vacuously, V1 is the thing to check first, because it is the only step whose
shape I have not confirmed against the source.
