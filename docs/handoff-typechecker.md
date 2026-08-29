# Handoff — the `Verify/TypeChecker` stream

Ownership this round: `Verify/TypeChecker/{IsDefEq,WHNF,Reduce,Basic}.lean`,
`Verify/Environment/Boundaries.lean`, `Verify/EqSafety.lean`, `Verify/QuotConsts.lean`,
new files under `Verify/`.  (`Verify/Typing/*` and `Verify/TypeChecker/InferType.lean` moved
to other streams; the previous edition of this file covered them and is superseded below.
Its §3 and §4 results — `TrProj.defeqDFC` closed, `TrProj.wf`'s subgoal refuted by
`ProjLevelWitness.lean` — still stand and are not repeated.)

Everything below is marked **[checked]** (a Lean declaration compiles, or an `#print axioms`
output was produced) or **[source]** (read off code/docstrings, not compiled).

---

## 0. Measurements, and a correction to the brief

**[checked]** `lake env lean scripts/sorry-census.lean` reports **21** declarations whose
*value* contains `sorryAx`, both before and after this session's work.  My four are

| site | file |
|---|---|
| `TypeChecker.Inner.quotReduceRec.WF` | `Verify/TypeChecker/WHNF.lean` |
| `TypeChecker.Inner.tryEtaStructCore.WF` | `Verify/TypeChecker/IsDefEq.lean` |
| `TypeChecker.Inner.isDefEqUnitLike.WF` | `Verify/TypeChecker/IsDefEq.lean` |
| `checkPrimitiveDef.WF.rest` | `Verify/Environment/Boundaries.lean` |

**[checked] The brief's two opening leads both came back negative, and that is worth
recording so nobody re-runs them.**

* *Auto-bound-implicit defect* (the `Params.extra_pat` / `Aligned.addInduct` failure mode).
  All four signatures were printed with `#check @…`.  Every binder is used: `quotReduceRec.WF`
  relates `e` to `e'` and its `whnf` argument really is `TypeChecker.Inner.whnf`, not a free
  variable; both `IsDefEq.lean` statements bind `e₁ e₁' e₂ e₂'` and use all four;
  `checkPrimitiveDef.WF.rest` binds `env`/`ves` through `wf` and `VContext.mk' wf`.
  **No defect in any of the four.**
* *The `TrProj.defeqDFC` existential trick* ("the conclusion is an `∃`, so nothing has to be
  recovered").  `TrExpr` is `∃ e₂, TrExprS … e e₂ ∧ IsDefEqU e₂ e'` (`Verify/Typing/Expr.lean:185`,
  read directly, not from a docstring).  The existential is over the *reduct's own*
  translation; the target `e'` is fixed as the input's translation, and `TrExprS` is
  functional up to `TrExprS.uniq`, so there is no freedom to exploit.  The other three
  conclusions (`b = true → c.IsDefEqU e₁' e₂'`, `PrimitiveResult`) contain no existential at
  all.  **The trick applies to none of the four.**

---

## 1. Closed this session: the rule-free-head obligation at `Quot`, without `VEnv.Sig`

This is the session's result.  `quotReduceRec.WF` was blocked on *two* open statements; it is
now blocked on **one**.

**Label correction first, because three files and the previous handoff get it slightly
wrong.**  "Ledger item M2" is **Lemma M2 of `docs/design-inductive.md:1040`** — *"inductive
heads are rule-free"* — carried in that document's ledger as row **I12**, *"M2 (inductive
heads are rule-free), from I1 | easy | 80"*.  It is **not** in `docs/soundness-ledger.md` (grep
finds no `M2` there at all), and as stated it is about *inductive* heads, so `RuleFreeHead env
``Quot`` is not literally an instance of it.  The `Quot` case is called out separately, three
paragraphs below M2 in the same section: *"Note this axiom is **also** required by the
quotient rule (`Quot.mk r a : Quot α r`, and `Quot` is a primitive constant with no rules), so
it is not inductive-specific and should not be paid for by this design."*  **That sibling
obligation — unnumbered, and owned by nobody — is what is now closed.**

### 1.1 What the obligation was, and why the `VEnv.Sig` price was avoidable

`VEnv.RuleFreeHead env c` (`Theory/Typing/Injectivity.lean:116`) says `c` heads no
definitional-equality rule of `env`.  It is a side condition of fact **(B)**,
`IsDefEqU.const_app_inv`, which `quotReduceRec.WF` needs at `c = ``Quot``.
`Theory/Typing/DeclRules.lean` proves the first half (a rule of a `VEnv.WF` environment has
one of three shapes) and says of the second half: *"needs a signature invariant relating names
to their declaring step, and is deliberately not attempted here."*  `design-inductive.md`
prices the whole thing at *"easy | 80, **from I1**"* — I1 being the `VEnv.Sig` invariant.

**That invariant is not needed at the `Verify` layer.**  A `TrEnv'`-built environment already
carries the name information, and the argument is **temporal rather than typal**:
`VEnv.addConst` refuses a name already present, a `TrEnv'` chain only ever grows `constants`,
and `Q = true` (i.e. `Kernel.Environment.quotInit = true`) forces the `quot` step to have
fired.  A δ-rule named `Quot` would have to be added while `Quot` is absent, and `AddQuot`
demands `Quot` absent later.  The two cannot both happen.

### 1.2 What is now in the tree

All in `Verify/TypeChecker/Reduce.lean`, immediately after `TrEnv'.defeqs_shape`, all
**[checked]** and all `#print axioms` → `[propext, Classical.choice, Quot.sound]`, no `sorryAx`:

| declaration | statement |
|---|---|
| `VEnv.addConsts_constants_none` | a block's names are fresh before the block is added |
| `VDefVal.toDefEq_name` | `v.toDefEq = w.toDefEq → v.name = w.name` |
| `VDefVal.headConst?_toDefEq` | `v.toDefEq.lhs.headConst? = some v.name` (`rfl`) |
| `VDefVal.toDefEq_ne_quotDefEq` | a δ-rule is never `quotDefEq` |
| `TrEnv'.defeq_contains` | every δ-rule's constant is declared |
| `TrEnv'.quotInit_contains` | `Q = true → venv.contains ``Quot`` |
| `TrEnv'.not_quotDefEq` | `Q = false → ¬ venv.defeqs quotDefEq` |
| **`TrEnv'.ruleFreeHead_quot`** | `TrEnv' safety C true venv → venv.RuleFreeHead ``Quot`` |
| `TrEnv.not_quotDefEq`, **`TrEnv.ruleFreeHead_quot`** | the same on a `Kernel.Environment`, guarded by `env.quotInit` |

`TrEnv.ruleFreeHead_quot` has exactly the shape `IsDefEqU.const_app_inv`'s `hrigid` binder
wants (checked against `Injectivity.lean:402-407`).

### 1.3 Non-vacuity — fired at a witness, not left as a lemma

**[checked]** In `Verify/QuotConsts.lean` §7, reusing that section's existing `trEnv_addQuot_wit`:

* `QuotWit.quotInit_wit` — the witness environment really has `quotInit = true` (`rfl`);
* `QuotWit.ruleFreeHead_quot_wit` — `(quotVEnv venvEq).RuleFreeHead ``Quot``, discharged;
* `QuotWit.ruleFreeHead_quot_wit_nonvacuous` — and the model it is discharged at *has a rule*
  (`defeqs quotDefEq`), whose head is `Quot.lift`, so the `∀ df` is not quantifying over an
  empty `defeqs`.

`#print axioms` on all three: no `sorryAx`.

### 1.4 Pricing, since the brief asked for it

**Measured, not estimated: ~150 lines of routine `TrEnv'` induction, one afternoon, and — the
part that matters — *zero* dependency on I1/`VEnv.Sig`.**  The whole cost is three inductions
over `TrEnv'` (nine constructors each, `induct` vacuous, `quot` needing the four-`AddQuot1`
`obtain` pattern already written out in `defeqs_shape`) plus four one-line algebra lemmas.  No
import was added to `Reduce.lean`: `Theory/Typing/Injectivity` is already in its cone.

**The pricing correction is the reusable part.**  `design-inductive.md` charges row I12 to I1
because it reasons at the `VEnv.WF` layer, where the only handle on names is a signature
invariant.  At the `TrEnv'` layer there is a second handle — `addConst`'s freshness check plus
the monotonicity of `constants` along the chain — and it is enough.  **When I12 itself is
attempted after the `AddInduct` flip, try this route before building `VEnv.Sig`.**

**And it was indeed the cheaper half.**  The other half, `const_app_inv`, is a `sorry` in
another stream's file whose own `trans` and `proofIrrel` cases are open and route through
Church–Rosser.  Anyone pricing the two should not have treated them as comparable.

**Recipe for generalising**, if a later consumer wants `RuleFreeHead` at another name: the
only thing `Quot`-specific is `quotInit_contains`.  For the other three quotient constants
(`Quot.mk`, `Quot.ind`; **not** `Quot.lift`, which genuinely heads `quotDefEq`) it is the same
proof with `ha₂`/`ha₄` in place of `ha₁` plus one `≤`-transport.  For an *inductive* type
former `S` — which is what `TrProj.uniq` needs — the same shape works, but only once
`AddInduct` gains constructors, because today `TrEnv'.induct` is vacuous and there is no step
that declares `S`.  **Do not attempt the inductive case before the flip; there is nothing to
induct on.**

---

## 2. `quotReduceRec.WF` — statement corrected, residual halved

### 2.1 The statement gained a hypothesis, and this is a correction, not a weakening

`quotReduceRec.WF` now reads

```lean
theorem quotReduceRec.WF {c : VContext} {s : VState} (hq : c.env.quotInit = true)
    (he : c.TrExprS e e') : RecM.WF c s (quotReduceRec e whnf) …
```

**[checked]** `reduceRecursor.WF` supplies `hq` from its own `split` and still compiles
unchanged otherwise: the implementation calls `quotReduceRec` only under `if env.quotInit`
(`Lean4Lean/TypeChecker.lean:334-337`), so nothing downstream loses anything.

**Why it is needed.**  **[checked]** `quotReduceRec` (`Lean4Lean/Quot.lean:113`) dispatches on
the head constant's *name* alone and never consults `quotInit`; `TrEnv'.axiom` never consults
names either.  So `TrEnv` admits an environment with `quotInit = false` holding an axiom
*named* `Quot.lift` of a type with nothing to do with quotients, whose model contains **no
quotient rule at all**.  Both halves are machine-checked in `Verify/QuotConsts.lean`:

* `QuotWit.trEnv_envLift : TrEnv safety envLift venvLift` — the axiom is admitted;
* `QuotWit.envLift_find? : envLift.find? ``Quot.lift = some (.axiomInfo liftAx)` — it really is
  in the kernel map under that name;
* `QuotWit.envLift_quotInit : envLift.quotInit = false` (`rfl`);
* `QuotWit.venvLift_no_quotDefEq : ¬ venvLift.defeqs quotDefEq`, via `TrEnv.not_quotDefEq`.

(The axiom's type is `eqStoredType`, reused verbatim from the neighbouring `Eq` witness —
`TrConstant` never inspects the name, so the same `TrExprS` derivation serves.  That is the
whole reason this witness was cheap.)

**[source]** On that environment the branch would fire and the postcondition would have no
rule to appeal to, so the theorem **is false without `hq`**.  This last step is *not*
machine-checked: completing it means showing the reduct is ill-typed, i.e. `.app` at a
non-function, i.e. sort/Π disjointness — fact **(A)**, itself `sorry`
(`Injectivity.lean:373`).  **So: strong, half-mechanised, not a proved refutation.**  I have
recorded it that way in the theorem's docstring and I recommend the next stream not upgrade
the claim without the missing half.

### 2.2 The residual, exactly

One open statement: **`VEnv.IsDefEqU.const_app_inv`** (`Theory/Typing/Injectivity.lean:402`,
fact (B), `sorry`).  Its two side conditions are settled:

* `hrigid : RuleFreeHead env ``Quot`` — **proved**, §1;
* `hty : IsType U Γ ((.const ``Quot ls).mkApp as)` — **[source]** free, because the fact is
  applied at the *type* of the major premise.

The underlying mathematical obligation is unchanged and worth restating: `quotDefEq` binds one
`α` and one `r` and uses each in **both** the `Quot.lift` head and the `Quot.mk` argument
(`bvar 5`/`bvar 4` in both positions — visible in `#print quotDefEq`), while `quotReduceRec`
checks only the head name and `isAppOfArity ``Quot.mk 3`, exactly as the C++ kernel does
(`~/lean4/src/kernel/quot.h:39-69`).  So `Quot α r ≡ Quot α' r' → α ≡ α'` must be *derived*
where `Theory/Typing/PatternRules.lean`'s `quotCheck` *assumes* it by making the matcher refuse.

**[checked]** The second, independent gap is confirmed by `TrEnv'.defeqs_shape`'s `quot` case
compiling with a single `rcases` alternative: `VEnv.addQuot` adds **exactly one** `VDefEq`, the
`Quot.lift` rule, while `quotReduceRec` reduces `Quot.ind` too.  **[source]** That half is
still derivable by `IsDefEq.proofIrrel` (`Quot.ind`'s motive lands in `Prop`), but it is a
different argument from `extra` and needs the same spine inversion.

---

## 3. `tryEtaStructCore.WF` and `isDefEqUnitLike.WF` — untouched, and why

Both remain `sorry`, per the standing ruling.  I did **not** conflate them with
`tryEtaStructCore_never_true` / `isDefEqUnitLike_never_true`; those two markers still compile
(**[checked]**, the census still lists exactly two `sorry`s in `IsDefEq.lean`).

**[checked] against `~/lean4/src/kernel/type_checker.cpp`:** our `isDefEqUnitLike` mirrors
`is_def_eq_unit_like` gate for gate — `!isRec`, one constructor, `numIndices = 0`,
`numFields = 0`, then `isDefEqCore tType (inferType s)`.  No divergence to record.

**What they need, restated precisely so it is not re-derived:**

* `tryEtaStructCore.WF` — the residual is one statement the abstract spec does not have:
  `env.IsStructure S D T C → HasType Γ t ((.const S us).mkApp ps) →
  IsDefEqU Γ t (ctor.mkApp (ps ++ [t.1, …, t.n]))`.  Plus the kernel→abstract bridge from
  `ConstantInfo.ctorInfo` + `isNonRecStructure` to `VEnv.IsStructure`, and `TrProj`
  functionality (which is `TrProj.uniq`, another stream's, itself blocked on (B) **and** on
  ledger G4, `VEnv.IsStructure.unique`, which **still has no statement anywhere in the tree**).
* `isDefEqUnitLike.WF` — the same rule at *zero* fields, applied twice, plus the same bridge,
  but **no** `TrProj`: a zero-field structure has no projections.  Note it is **not** derivable
  from `proofIrrel`: a unit-like structure may live in `Type` (`Unit`, `PUnit`), so the two
  elements need not be proofs.

**I deliberately did not write a `StructEtaRule : Prop` and reduce these to it.**  Applying
`docs/handoff-stratified.md` §5's criterion: the honest form of that rule is close enough to
the conclusion that the "reduction" would be a rename, and the real content — the bridge and
the projection bookkeeping — would sit on the wrong side of it.  A reduction that moves the
difficulty rather than the statement is worse than the `sorry`.

---

## 4. `checkPrimitiveDef.WF.rest` — priced, and it is **not** the cheap one

The brief's instinct ("an unexamined hole is often the cheapest") does not survive contact
here.  **[source]**, from `Lean4Lean/Primitive.lean` and `Verify/Environment/Boundaries.lean`:

1. **The first step is not in a file this stream owns.**  The four remaining branches
   (`Nat.mod`, `Nat.div`, `Nat.gcd`, `Nat.bitwise`) still hand *unchecked* terms to `isDefEq`
   and `inferType`, which is `bugs-found.md` item 4 — the bug that was fixed for the other
   fifteen branches by `checkPrimValue`/`checkIsType`/`checkedIsDefEq`/`checkedTypeIs`.  I
   re-read the code and confirm the diagnosis, and can sharpen it: in `Condition.check`
   (`Primitive.lean:125`) the very first `inferType cond.prop` runs on a term nothing has
   checked — `checkType cond.dec` precedes it, but for `natLE`/`natEq` the `dec` (`Nat.decLe`,
   `Nat.beq`) does not mention `prop` (`@LE.le Nat _`, `@Eq Nat`), so no earlier check covers
   it.  By contrast `asBool` and `proof` *are* covered, because the later `checkType e`
   type-checks a term containing both.  The fix is therefore narrower than the docstring
   implies but it is still an edit to `Primitive.lean`, which this stream does not own.
2. **Then it needs genuinely new reflection arguments** that the fifteen closed branches did
   not: fuel recursion for `mod`/`div`, `WellFounded.Nat.fix` through
   `unfoldWellFounded`/`unfoldNatWellFounded` for `gcd`/`bitwise`, each threading `Acc.rec`
   and `Acc.intro` through `M.WF`.
3. **It may be false rather than open.**  `M.WF` demands `VState.WF` preservation, and an
   untyped `isDefEq` records its verdict in the `EquivManager`, whose invariant demands both
   sides be translatable.  Whether a declaration exists that *exploits* the gap is still
   established neither way — the fifteen were each closed without needing such a witness.
   **If someone wants a decisive result here, build that witness before attempting a proof.**

Ranking of the four by cost: `quotReduceRec.WF` (one open theory statement) <
`isDefEqUnitLike.WF` < `tryEtaStructCore.WF` (a missing spec rule, then a bridge) <
`checkPrimitiveDef.WF.rest` (an implementation fix in another stream's file, then new
metatheory, and possibly false).

---

## 5. Non-vacuity audit

Applying the stated test to everything §1–§2 claims:

* `TrEnv'.ruleFreeHead_quot` — not a reduction, an outright proof, and fired at a witness
  whose environment carries a real rule (§1.3).  Its `quotInit = true` hypothesis is *not*
  degenerate: `TrEnv'.not_quotDefEq` shows the `quotInit = false` side is genuinely different,
  and `QuotWit.trEnv_envLift` shows that side is inhabited.
* `TrEnv'.defeq_contains`, `TrEnv'.quotInit_contains`, `TrEnv'.not_quotDefEq` — used only as
  steps of the above; each is separately non-vacuous because `trEnv_addQuot_wit` and
  `trEnv_envLift` inhabit both settings.
* The `hq` added to `quotReduceRec.WF` does **not** make the theorem vacuous: §2.1's witness
  is on the *excluded* side, and `QuotWit.trEnv_addQuot_wit` inhabits the *admitted* side.
  A hypothesis that both sides of are inhabited cannot be hiding an empty premise.

---

## 6. Pick up first

1. **`const_app_inv` is now the whole of `quotReduceRec.WF`.**  Nothing else in this stream is
   one theorem away from closing.  If the injectivity stream lands (B), this branch should be
   attempted immediately — the side conditions are already discharged in the form its binders
   want.
2. **Generalise `ruleFreeHead_quot` only when it has a consumer**, per §1.4's recipe; the
   inductive case is blocked on the `AddInduct` flip, not on effort.
3. **Do not** re-run the auto-bound-implicit check or the existential trick on these four
   (§0), and do not re-derive `quotReduceRec.WF`'s dependency labels: it is fact **(B)**, not
   I13, and (B)'s `RuleFreeHead` condition is **no longer open**.
4. For `checkPrimitiveDef.WF.rest`, the *first* useful artefact is a counterexample
   declaration, not a proof attempt (§4.3).

## 7. For the orchestrator — statements in files this stream does not own

Not edited; reported.

* `Theory/Typing/DeclRules.lean` module docstring: *"This is also the first half of
  soundness-ledger item **M2** … The second half … needs a signature invariant relating names
  to their declaring step, and is deliberately not attempted here."*  Still true of the
  `VEnv.WF` layer, but the second half is now **done at the `TrEnv'` layer** for `Quot`
  (`TrEnv.ruleFreeHead_quot`), and the note should point at it so the next reader does not
  price `VEnv.Sig` again.
* `Theory/Typing/Injectivity.lean:116`, `RuleFreeHead`'s docstring: *"Deriving it from
  `VEnv.WF` is ledger item M2 and needs the `VEnv.Sig` invariant."*  True for `VEnv.WF`;
  should note that consumers inside `Verify/` do not need it, and cite
  `TrEnv.ruleFreeHead_quot`.
* **The label "ledger item M2" points at the wrong document.**  There is no `M2` anywhere in
  `docs/soundness-ledger.md`; the lemma is `docs/design-inductive.md:1040` and its ledger row
  is **I12** in that file's table (`design-inductive.md:1311`).  Three sources use the
  soundness-ledger phrasing: `Theory/Typing/DeclRules.lean:26`,
  `Theory/Typing/Injectivity.lean:115`, and `docs/handoff-weakn.md:255`.  Either fix the
  citations or move the row.
* `docs/design-inductive.md:1311`, row **I12**: its *"easy | 80, from I1"* pricing is now
  known to overcharge — see §1.4.  The `Quot` sibling, which the same section explicitly says
  *"should not be paid for by this design"*, is done and cost no I1 at all.
