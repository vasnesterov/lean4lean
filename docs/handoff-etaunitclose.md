# handoff-etaunitclose — the two eta holes: true today (vacuously), **false after the flip**

Round of 2026-09-03.  Targets: `TypeChecker.Inner.tryEtaStructCore.WF`
(`Verify/TypeChecker/IsDefEq.lean:556-558`) and `TypeChecker.Inner.isDefEqUnitLike.WF`
(`:1052-1054`).  My files: `Lean4Lean/Verify/TypeChecker/EtaUnitClose.lean` (new) and this doc.
`IsDefEq.lean` was **not** edited; the frozen files were not touched; no git commands were run.

## Status: COMPLETE. Both holes verdicted; see §3.

## 1. What each hole claims

```lean
-- IsDefEq.lean:556
theorem tryEtaStructCore.WF {c : VContext} {s : VState}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
    RecM.WF c s (tryEtaStructCore e₁ e₂) fun b _ => b → c.IsDefEqU e₁' e₂' := sorry
-- IsDefEq.lean:1052
theorem isDefEqUnitLike.WF {c : VContext} {s : VState}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
    RecM.WF c s (isDefEqUnitLike e₁ e₂) fun b _ => b = .true → c.IsDefEqU e₁' e₂' := sorry
```

Unfolding `RecM.WF`/`M.WF` (`Verify/TypeChecker/Basic.lean:278,325`), each says: for every
recursion bundle `m` with `m.WF`, every `s` with `s.WF c`, if running the function on
`c.toContext`/`s.toState` succeeds with the answer `true`, then the two *abstract* terms
`e₁'`/`e₂'` that `he₁`/`he₂` translate to are related by `c.venv.IsDefEqU` — the 13-constructor
`VEnv.IsDefEq` of `Theory/Typing/Basic.lean`.

## 2. Consumers (`lean_references`, run this round)

| hole | direct references | consuming declarations | transitive users |
|---|---|---|---|
| `tryEtaStructCore.WF` | 3 (self + 2) | **1** — `tryEtaStruct.WF` (`IsDefEq.lean:564,566`, both argument orders) | 71 |
| `isDefEqUnitLike.WF` | 2 (self + 1) | **1** — `isDefEqCore'.WF` (`IsDefEq.lean:1170`) | 70 |

Both funnel into `isDefEqCore'.WF`, so both are load-bearing for checker soundness; but the
work item is *one* item, and closing either alone frees nothing (reproducing
`docs/handoff-etaunit.md` §1: sole-user counts 1 and 0).

## 3. Verdict: **both holes are true today, vacuously, and refutable at a post-flip context**

Not "unproved".  Three theorems in `EtaUnitClose.lean`:

| theorem | says |
|---|---|
| `TypeChecker.tryEtaStructCore.WF_today` | the hole at `:558`, **proved**, one line, `sorryAx`-free |
| `TypeChecker.isDefEqUnitLike.WF_today` | the hole at `:1054`, **proved**, one line, `sorryAx`-free |
| `TypeChecker.tryEtaStructCore_WF_false_of_flip` / `…isDefEqUnitLike_WF_false_of_flip` | each hole's *universally quantified* statement is **false** given (i) a `VEnvAt env safety MutField.unitEnv` and (ii) the checker answering `true` at the pair `(foo, A.mk)` |
| `TypeChecker.etaHoles_true_today_false_of_flip` | all four, as one statement |

Read the pair: `WF_today` shows the hole is a true statement *now*; `_WF_false_of_flip` shows
the same statement is *false* as soon as `AddInduct` gains constructors, unless `VEnv.IsDefEq`
gains a rule.  That is precisely the profile of a `sorry` that must not be closed by its
available one-liner, and it is why the docstrings at `:534` and `:1041` refuse it.  This round
turns that refusal from a policy into a theorem.

**Both `WF_today` proofs show the hole's own hypotheses are half dead.**
`tryEtaStructCore.WF_today` does not use `he₁`; `isDefEqUnitLike.WF_today` does not use `he₂`
(hence the `_he₁`/`_he₂` binders in my file — the statements are otherwise the holes verbatim).

### What `_WF_false_of_flip` takes, and how small it is

```lean
theorem isDefEqUnitLike_WF_false_of_flip
    {env : Environment} {safety : DefinitionSafety}
    (hva : VEnvAt env safety MutField.unitEnv)
    {m : Methods} (hm : m.WF) {st : State}
    (hfire : Inner.isDefEqUnitLike (.const `MutField.foo []) (.const `MutField.A.mk []) m
        (VContext.mk1 hva).toContext {} = .ok (true, st))
    (H : ∀ {e₁ e₂ : Expr} {e₁' e₂' : VExpr} {c : VContext} {s : VState},
      c.TrExprS e₁ e₁' → c.TrExprS e₂ e₂' →
      RecM.WF c s (Inner.isDefEqUnitLike e₁ e₂) fun b _ => b = .true → c.IsDefEqU e₁' e₂') :
    False
```

`H` is the hole's statement **verbatim** (copy the `theorem` line at `IsDefEq.lean:1052`).
Everything else that a refutation normally has to build is discharged inside the proof and is
*not* a hypothesis:

* the `VContext` — `TypeChecker.VContext.mk1 hva`, whose `mlctx` is `.nil`, so
  `vlctx.toCtx = []` and `lparams = []` by `rfl`;
* the `VState` and its `VState.WF` — `{}` and `VState.WF.empty1`, free;
* both `TrExprS` premises — `TrExprS.const MutField.unitEnv_foo rfl rfl` and
  `… unitEnv_Amk rfl rfl`, free, because `unitEnv`'s constant map is known;
* the abstract contradiction — `MutField.unitEnv_foo_ne_Amk` (§1 of my file).

So exactly **three** things stand between this and an unconditional refutation of both holes:

1. `TrEnv safety env MutField.unitEnv` for some real kernel `Environment` — the `AddInduct`
   flip, and nothing else.  (`VEnvAt`'s other two fields are `HasPrimitives`, which is
   *conditional on containment* in every one of its 24 fields and so should be free at
   `unitEnv`, and `safePrimitives`, a condition on `env` rather than on `venv`.)
2. `hfire` — that the checker answers `true` there.  Measured at the same shape in §4 below;
   not derivable abstractly because `env` is a variable.
3. `hm : m.WF` — see the circularity note in §5.

### The honest reading: §2 is itself vacuous **today**, and that is the point

`VEnvAt env safety MutField.unitEnv` is currently **unsatisfiable** (`TrEnv` cannot translate an
inductive while `AddInduct` is empty), so `_WF_false_of_flip` is, right now, a true implication
with an uninhabited premise.  Stated flatly: I did **not** refute either hole.  What the theorem
buys is that the refutation is now *assembled* — every ingredient but one is discharged, the
witness pair is fixed (`foo` vs `A.mk`), and the abstract contradiction is a named lemma — so at
the flip the two `sorry`s do not need re-investigation; they need deleting.  The pair
{`WF_today`, `_WF_false_of_flip`} is a satisfiability seesaw: exactly one of the two is vacuous
at any time, and the flip swaps which.  Before this round neither end of that seesaw existed as
a theorem.

## 4. Against the C++ kernel: re-read line by line, **nothing new**

Read on current master: `try_eta_struct_core` at `~/lean4/src/kernel/type_checker.cpp:856-872`;
`try_eta_struct` **inline in the header**, `type_checker.h:98-100`, as
`try_eta_struct_core(t,s) || try_eta_struct_core(s,t)`; `is_def_eq_unit_like` at
`type_checker.cpp:1120-1130`; `is_non_rec_structure` at `inductive.cpp:28-33`; the call order in
`is_def_eq_core` at `type_checker.cpp:1190-1205`.

Control flow is identical in both functions, step for step, including the order of the four
guards in `try_eta_struct_core` (constant head → `is_constructor` → arity → `is_non_rec_structure`
→ type equality → per-field projections), the two-argument-order wrapper, and the tail of
`is_def_eq_core` (`is_def_eq_app`, `try_eta_expansion`, `try_eta_struct`,
`try_string_lit_expansion`, `is_def_eq_unit_like`).  `is_def_eq_unit_like` uses
`is_def_eq_core`, not `is_def_eq`, so it skips the success cache; lean4lean's `isDefEqUnitLike`
likewise calls `isDefEqCore`, skipping the `eqvManager.addEquiv` that `Inner.isDefEq`
(`TypeChecker.lean:183-187`) performs.  `Kernel.Environment.isNonRecStructure`
(`Lean4Lean/Environment/Basic.lean:49`) is character-for-character Lean core's
`Lean.isNonRecStructure` (`~/lean4/src/Lean/Structure.lean:361`), which is the same three
conjuncts as C++.

**The two divergences here are already recorded, and are still exactly right.**
`divergences.md:203-217` has both:

* `isDefEqUnitLike`: C++ `env().get(ctor_name).to_constructor_val()` raises where lean4lean
  returns `false`.  Verified: still `type_checker.cpp:1126`, with the function at `:1120` — no
  further line drift since that entry was written.
* `tryEtaStructCore`: C++ `is_non_rec_structure` calls `env.get`, which throws on an unknown
  name; lean4lean's `isNonRecStructure` uses `find?` and returns `false`.  Verified: still
  `inductive.cpp:28`.  Worth adding to that entry if anyone touches it: **Lean core's own
  Lean-side `isNonRecStructure` has the same `find?`-vs-`get` difference**, and its docstring
  says "This must be in sync with `is_non_rec_structure()`" — so lean4lean matches Lean core
  here and it is the C++/Lean pair upstream that differs.

**Nothing for `divergences.md` and nothing for `bugs-found.md` from these two paths.**  In
particular the "no singleton-block test" observation (both kernels run eta and unit-like defeq at
members of *mutual* non-recursive blocks) is already recorded three times —
`FiringWitness.lean` item 5, `VEnv.IsStructure.types`' docstring, and
`MutNonRec.kernelProjChecks` — and `divergences.md:218-221` already records that **neither C++
function tests the structure's universe**.  I found no third difference and no unsoundness in
either C++ function: at zero fields the unit-like rule is exactly η-expansion of both sides to
`I.mk ps`, and at positive fields `try_eta_struct_core` checks every projection.

## 5. Vacuity, both directions, measured

**Direction 1 — is the premise satisfiable?**  `RecM.WF`'s own premises are *not* the problem:
`Methods.WF` is inhabited (`Methods.withFuel.WF`), `VState.WF` is inhabited at `{}`
(`VState.WF.empty1`), and `VContext` is inhabited (`VContext.mk1` at any `VEnvAt`).  What is
empty is the set of `VContext`s whose `venv` has an inductive: `TrEnv.not_inductInfo` /
`.not_ctorInfo` hold *because* `Lean4Lean.AddInduct` has no constructors, and that is the whole
reason both holes are provable today.

**A circularity worth knowing.**  The only inhabitant of `Methods.WF` in the tree is
`Methods.withFuel.WF`, whose cone contains **both of these very holes** (measured:
`scripts/exists.lean` on `Lean4Lean.TypeChecker.Methods.withFuel.WF` lists
`isDefEqUnitLike.WF`, `tryEtaStructCore.WF`, `inferProj.WF`, `TrProj.weak'_inv` and the four
census holes).  §2's theorems therefore take `hm : m.WF` as a *hypothesis* rather than using
`withFuel.WF`, which keeps their cones free of the holes they refute; the consequence for a
successor is that when these two statements fall, `Methods.withFuel.WF` and `isDefEqCore'.WF`
fall with them, not after them.

**Direction 2 — does the guard ever fire?**  Yes, and at the refutation's own shape.
`FiringWitness.lean` already fires both gates at *free variables* of a zero-field structure.
That is not enough for §2: the abstract contradiction needs no-confusion, and no-confusion in
this tree exists only at a **constant** head (`VEnv.constNoConf_of_notIsProof`; there is no
bvar-vs-constructor no-confusion anywhere — `docs/handoff-etaunit.md` §2).  §4 of my file
therefore fires them at an **axiom** inhabitant, which is what `MutField.foo` abstracts:

```
structure Z : Type where                     -- zero fields, Type, so not proof irrelevance
axiom fooAx : Z                              -- added to a *kernel environment value* by
                                             -- Lean4Lean.addDecl; this module declares no axiom
isDefEqUnitLike  fooAx Z.mk  =  true         -- M.run … (RecM.run …), the call §2's `hfire` names
tryEtaStructCore fooAx Z.mk  =  true
Lean4Lean.addDecl accepts  theorem : fooAx = Z.mk := rfl
```

All five checks pass, as a build-time `#eval` that fails the build if any verdict changes.
**The instrument discriminates** (probed separately, not assumed): `isDefEqUnitLike` answers
`false` at a *one*-field structure, and `tryEtaStructCore` answers `false` in the reversed
argument order `(Z.mk, fooAx)`.  So the `true`s are real answers, not a `matches` pattern that
always succeeds.

This is the first firing witness in the tree at a *constant* inhabitant, and it is what makes
§2's `hfire` a hypothesis about something known to happen rather than a hypothesis about
something imagined.

## 6. Cones and taint (`scripts/exists.lean`, after `lake build`)

| declaration | arity | cone | reaches `sorryAx` | holes in cone |
|---|---|---|---|---|
| `MutField.unitEnv_constants_eq_none` | 3 | 1027 | no | — |
| `MutField.unitEnv_hasPrimitives` | 0 | 1092 | no | — |
| `TypeChecker.MutField.venvAt_of_trEnv` | 4 | 4756 | no | — |
| `TypeChecker.tryEtaStructCore.WF_today` | 8 | 6832 | **no** | — |
| `TypeChecker.isDefEqUnitLike.WF_today` | 8 | 6557 | **no** | — |
| `MutField.unitEnv_foo_ne_Amk` | 0 | 7554 | yes | the four census holes |
| `TypeChecker.tryEtaStructCore_WF_false_of_flip` | 8 | 10951 | yes | the four census holes |
| `TypeChecker.isDefEqUnitLike_WF_false_of_flip` | 8 | 10766 | yes | the four census holes |
| `TypeChecker.etaHoles_true_today_false_of_flip` | 17 | 11938 | yes | the four census holes |

"the four census holes" = `IsDefEqU.weakN_iff`, `IsDefEqU.forallE_inv_stratified`,
`WF.rigidShapeUniqNS`, `NormalEq.descend` — the same four `EtaUnitRefute.lean` and
`isDefEqUnitLike.WF_of_unitEta` already borrow.  **No new hole, and no dependence on the two
holes being refuted.**

Axioms (`#print axioms`, at the foot of the file): `[propext, Classical.choice, Quot.sound]` for
the five hole-free declarations, the same plus `sorryAx` for the four tainted ones.  `after ⊆
before` holds: no axiom outside what the tree already uses.

The module was built (`lake build Lean4Lean.Verify.TypeChecker.EtaUnitClose`) **before**
measuring, because `lake env lean file.lean` leaves no `.olean` and the previous round recorded
a stale-olean probe that inverted its own conclusion.

## 7. What I could not do, with reasons

1. **Refute either hole unconditionally.**  Blocked on `TrEnv safety env MutField.unitEnv`, i.e.
   on `AddInduct` having constructors.  Everything else `VEnvAt` needs is now discharged
   (`MutField.venvAt_of_trEnv` takes `TrEnv` plus the `env`-only `safePrimitives` side
   condition and returns the `VEnvAt`).  This is not a research problem, it is the flip.
2. **Discharge `hfire` as a theorem.**  It quantifies over an abstract `env`; the checker's
   answer depends on `env.find?`, and the facts that would pin those lookups
   (`IndShape`/`CtorShape`, `Verify/Environment/Basic.lean:278ff`) are supplied only by the
   `AddInduct` constructors that do not exist.  Measured at the shape instead (§5).
3. **Generalise `unitEnv_foo_ne_Amk` off `U = 0`, `Γ = []`.**  `unitEnv_not_isProof_foo`
   (EtaUnitRefute, not mine) is stated at `0 []`, and moving it needs `instL`/weakening steps I
   did not need, since `VContext.mk1`'s context *is* `0 []`.  Not a gap for §2.
4. **Anything in `IsDefEq.lean`.**  Not mine; §5 of my file states both candidate edits exactly
   and recommends against both.  `divergences.md` and `bugs-found.md` untouched — §4 says why
   there is nothing to add.

## 8. Pick up first

1. **Do not close these two `sorry`s.**  `etaHoles_true_today_false_of_flip` is the one-line
   citation for that: it proves both statements *and* refutes both statements' universal
   closures at a post-flip context, in one theorem.
2. **The eta corner is one work item and its content is entirely abstract-side.**  The route is
   the 14th `VEnv.IsDefEq` constructor (price already measured in `docs/handoff-etaunit.md` §3:
   25 direct eliminations, 2643-declaration blast radius), plus model validation from
   `Theory/SetModel/UnitEtaPairing.lean`.  Once `StructEtaG` is a theorem,
   `EtaResidual.lean` closes both holes with no further checker-side work.
3. **`MutField.unitEnv_hasPrimitives` is reusable.**  Any refutation or witness that needs a
   `VEnvAt`/`VContext` at a small hand-built `VEnv` needs `HasPrimitives` there, and the
   `unitEnv_absurd` / `unitEnv_absurd'` pair (autoParam side conditions, so callers write
   `unitEnv_absurd h`) makes it 24 one-line fields.  The same three lemmas transfer verbatim to
   `declEnv`, `barEnv`, `MutNonRec.decl2Env`.
4. **`EtaUnitClose.lean` is an ORPHAN**, like `EtaUnitRefute.lean`: nothing imports it, so
   `hole-rank`, `cone-measure` and `sorry-census` do not see it.  One `import` line in
   `Experimental/ConeJoin.lean` (not mine) fixes both.

## 9. A duplication found on the way: `constNoConf_of_notIsProof`

`EtaUnitRefute.lean` (08:47 today) introduces
`VEnv.constNoConf_of_notIsProof` — `constApp_inv_of_patWF` with the `IsType` premise replaced by
`¬ IsProof` — as the trick that makes its refutation work.  `Verify/Typing/NoConfGuard.lean`
(14:17 today, so *later*, and independently) contains the same content twice over:

* `VEnv.ConstNoConfNP` (`:205`) is that statement as a named predicate;
* `VEnv.constNoConfNP_of_patWF` (`:214`) is the **same proof term**, line for line;
* `VEnv.constNoConfNP_of_wf` (`:224`) is strictly better — it discharges `PatWF` by
  `patWF_of_wf` internally, so callers pass only `env.WF` and `U`.

Same taint in both (the four census holes; cone 7491 vs 7328).  So `constNoConf_of_notIsProof`
should be **deleted** in favour of `VEnv.constNoConfNP_of_wf`, and `MutField.unitEnv_not_unitEta`
and my `MutField.unitEnv_foo_ne_Amk` re-pointed at it (each loses one argument).  Neither file is
mine, so this is a note, not an edit.  Two agents proved the same lemma seven hours apart on the
same day; `NoConfGuard.lean` §2 even opens by correcting a handoff that claimed "nothing in the
tree has the `¬ IsProof` form of constant no-confusion".

`Verify/Typing/QuotKEta.lean` was read and does **not** bear on these two holes: its `EtaK` is
the ι/δ *pattern-rule* eta of `ParRedK`, not structure eta, and no statement in it mentions
`StructEta`/`StructEtaG`/`UnitEta` or either hole.
