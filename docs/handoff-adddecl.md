# `addDecl.WF` and `checkPrimitiveDef.WF.rest` — the restatement, and what closed

Everything below is separated into **[machine-checked]** (a `lake build` / `#print axioms` /
`lake env lean scripts/sorry-census.lean` produced it) and **[source]** (read off the code,
not proved).

Census: **19 before, 19 after** **[machine-checked, both runs]**.  Full `lake build` is green
**[machine-checked]**.  No executable code was touched — the three modified files are
`Verify/Environment.lean`, `Verify/Inductive/AddDeclWF.lean`, `Verify/Primitive.lean`, all
proof-side — so the Kernel Arena gate is not engaged and was **not** run.

---

## 1. Bottom line

* The honest restatement of `addDecl.WF` is written, elaborates, and is **proved with no
  `sorry` of its own**: `addDecl.WF_honest` (`Verify/Inductive/AddDeclWF.lean` §5)
  **[machine-checked]**.
* It is **non-vacuous, and separated from the refuted statement at a single witness**:
  `addDeclPost_separation` exhibits one constant map at which the honest arm's three conjuncts
  hold *and* the map carries an `.inductInfo` — the exact hypothesis from which
  `addDecl_inductDecl_post_false` derives `¬ ves.WF env'`.  Sorry-free
  (`[propext, Classical.choice, Quot.sound]`) **[machine-checked]**.
* `addDecl.WF` itself keeps its statement and its `sorry`, **because the statement is pinned
  from outside this stream** — see §4.  This is a correction to the brief, which expected the
  restatement to land at `addDecl.WF`.
* On the primitive side, §5(a) and §5(b) of `docs/handoff-primitive.md` are **both closed as
  metatheory**: the `Condition` reflection lemma and the fuel induction for `Nat.mod` /
  `Nat.div` are proved at the `VExpr` level (§5 below).  What is left of those two items is
  plumbing, not mathematics, and §5.3 says exactly what.

---

## 2. The restatement

`Verify/Inductive/AddDeclWF.lean` §5.

```lean
def AddInductPost (env env' : Environment) (ves : VEnvs)
    (lp : List Name) (np : Nat) (types : List InductiveType) : Prop :=
  ∃ (ves' : VEnvs) (numNested : Nat), ∀ safety,
    InductStepNested env.constants env'.constants
      (ves.venv safety) (ves'.venv safety) lp np types numNested

def AddDeclPost (env : Environment) (decl : Declaration) (ves : VEnvs)
    (env' : Environment) : Prop :=
  match decl with
  | .inductDecl lp np types iu => iu = false → AddInductPost env env' ves lp np types
  | _ => ∃ ves' : VEnvs, ves'.WF env' ∧ ∀ safety, ves.venv safety ≤ ves'.venv safety
```

### 2.1 Why this shape and not another

Three constraints, each already established and each re-checked here:

1. **The old conclusion must go, at `inductDecl` only.**  `VEnvs.WF.no_inductInfo` refutes
   `∃ ves', ves'.WF env'` at every environment whose map holds an `.inductInfo`, and the
   checker produces such environments (`AddDeclWF.lean` §4, check A, a build-time `#eval`).
   Outside `inductDecl` nothing is weakened — `AddDeclPost.eq_old` proves the two are the same
   proposition there, by `rfl` per constructor **[machine-checked]**.

2. **The change is to a definition the statement quantifies over.**  The earlier finding —
   "no branch-local restatement, the conclusion is uniform across `Declaration`" — is right
   about `addDecl.WF` as written, and the way out is that the postcondition becomes a
   *definition* (`AddDeclPost`) that may case on `decl`, which the theorem's own binder
   supplies.  That is a change of definition, not a per-branch weakening of a fixed predicate.

3. **`InductStepNested`, with the two corrections, not `InductStepSafe`.**  Confirmed against
   `Verify/Environment/InductR.lean`: `InductStepNested` already uses `VInductDecl'.WF` rather
   than the re-staged `WFC`, and already carries `∃ et, venv.addIndTypes D = some et` as an
   explicit conjunct with `ctors_nonvacuous` reading it back.  Both corrections in the brief
   were already applied there; nothing needed changing **[source, read against InductR.lean]**.

### 2.2 The one place the restatement is honestly silent

`iu = true`.  `AddDeclPost` at an unsafe inductive is `true = false → …`, i.e. vacuous, and
that is deliberate and labelled in the docstring.  The reason is §1.1's, unchanged and not
repaired here: `TrEnv'` has **no rule at all** for an unsafe inductive at `safety = .unsafe`
— `ignore`'s premise `¬ safety ≤ ci.safety` fails for every constant there, and
`AddInductStages`/`AddInductStagesR` force `isUnsafe = false` on everything they introduce
(`unsafe_induct_unreachable`).  Closing it is a **new `TrEnv'` constructor** in
`Verify/Environment/Basic.lean` — a file this stream does not own — the inductive analogue of
`TrEnv'.unsafeDef`.  It is a design decision, not a proof obligation, and it is independent of
`AddInduct`.

---

## 3. What closed

All sorry-free (`#print axioms` = `[propext, Classical.choice, Quot.sound]`)
**[machine-checked]**, in `Verify/Inductive/AddDeclWF.lean`:

| declaration | content |
| --- | --- |
| `AddInductPost`, `AddDeclPost` | the restatement; elaborates |
| `AddDeclPost.eq_old` | outside `inductDecl` the restatement *is* the old statement |
| `AddInductPost.exists_le` | the monotonicity half survives the weakening |
| `AddInductPost.find?_of_not_mem` | the map is determined outside `indDeclNamesN` |
| `AddInductiveStepWF` | the single remaining checker-side obligation |
| `addDecl.WF_honest` | **the restatement, proved** from that obligation |
| `AddInductFlip`, `InductStepNested.trEnv'` | what the flip buys, exactly |
| `AddIndConsts.find?_mono`, `.find?_head` | a stage's insertions survive the later stages |
| `AddInductStages.find?_type_head`, `AddInductStagesR.find?_type_head` | the block's first type constant reaches the output map as an `.inductInfo` |
| `R10.Wit.inductStepSafe_wit_inductInfo` | the honest arm at a map that holds an `.inductInfo` |
| `addDeclPost_separation` | that fact and `addDecl_inductDecl_post_false`, side by side |
| `addInductPost_nested_nonvacuous` | the nested half, from `inductStepNested_wit_closed` |

`addDecl.WF_honest`'s own axiom print carries `sorryAx` — **inherited taint only**, from the
six non-inductive branch lemmas it re-uses (`addAxiom.WF`, `addDefinition.WF`, …), which are
already tainted through the type-checker stream.  It contributes no declaration to the census
**[machine-checked: census unchanged at 19, and `addDecl.WF_honest` does not appear in it]**.

### 3.1 The separation, spelled out

`addDeclPost_separation` proves, at one and the same `m`:

* `∃ m' venv', InductStepSafe m m' VEnv.empty venv' [] 0 [R10.Wit.uIndType] ∧
   ∃ v, m'.find? \`R10.Wit.U = some (.inductInfo v)` — the honest arm's three conjuncts hold,
  and the map carries an `.inductInfo`;
* `∀ env' ves n v, env'.constants.find? n = some (.inductInfo v) → ¬ ves.WF env'` — the old
  arm's refutation, triggered by exactly that.

The `.inductInfo` half is new: it needed `AddIndConsts.find?_mono`/`.find?_head`, which say
that a stage's insertion survives the two later stages because each `cons` demands freshness
in the map it inserts into.  The earlier witnesses (`addInductStages_wit`,
`inductStepNested_wit`) exposed a `.ctorInfo`/`.recInfo` but not the `.inductInfo` the
refutation keys on, so the separation had never actually been made at the refuting constant.

---

## 4. What is open, with the exact failing step

### 4.1 `AddInductiveStepWF` — the obligation the restatement leaves

```lean
def AddInductiveStepWF : Prop :=
  ∀ {env : Environment} {ves : VEnvs}, ves.WF env →
    ∀ lp np types ap fuel,
      (Environment.addInductive env lp np types false ap fuel).WF fun env' =>
        AddInductPost env env' ves lp np types
```

This is the whole remaining content of the inductive branch under the honest postcondition:
turn the checker's `addInductive` run into a `VInductDecl'`, a `K`, an `R`, the syntactic
translation `TrIndDeclN`, the declaration's `VInductDecl'.WF`, and the constant-map step
`AddInductStagesR`.  It is **not** refuted by `VEnvs.WF.no_inductInfo` — its conclusion never
mentions `ves'.WF env'` — and its consequent is satisfiable (§3.1) **[machine-checked]**.

### 4.2 Why the restatement did not land *at* `addDecl.WF` — correction to the brief

The brief says the restatement "does not require the `AddInduct` flip".  That is true of the
*statement*.  It is not true of *installing* it, and the obstruction is not inside
`Verify/Environment.lean`:

`Verify/Bridge.lean` — not this stream's file — repeats `addDecl.WF`'s conclusion verbatim as
`def AddDeclWF (fuel)` and discharges it by `theorem addDeclWF fuel := fun wf decl =>
addDecl.WF wf decl fuel` (line 138) **[source]**.  Weakening `addDecl.WF`'s conclusion breaks
that line, and there is no way to keep both: `AddDeclWF fuel` is precisely the false
statement, so it cannot be re-derived from anything true, and re-proving it would need a
second `sorry` (census 20, which the brief forbids).

The three changes `Verify/Bridge.lean` would need, in order:

1. `AddDeclWF fuel`'s body becomes `… .WF (AddDeclPost env decl ves)`.
2. `foldlM_addDecl_WF` needs a fold-level invariant instead of `∃ ves', ves'.WF env' ∧ …`.
   **This is the real content**, and it is where the honest postcondition stops composing:
   the *next* iteration's premise is `ves.WF env`, which `AddInductPost` does not supply.
3. `foldAddDecl_tr` becomes a hypothesis of
   `not_leanTTConsistent_of_kernel_proves_false`, alongside `PreludeBridge`, since
   `TrEnv .safe env venv` is exactly what the honest arm stops delivering.

Item 2 is blocked on the same `AddInduct` emptiness as everything else: `Bridge`'s chain is
already false from `stdPrelude`'s **first** declaration, `eqDecl`, which is an `.inductDecl`
**[source, `Verify/Soundness.lean`]**.  So making the Bridge changes piecemeal buys nothing;
they should land in the same commit as the flip.

**Recommended:** when the flip lands (`AddInduct := fun m env D m' env' => ∃ K R,
AddInductStagesR m env D K R m' env'`, `Verify/Environment/Basic.lean`'s docstring carries the
exact text), `InductStepNested.trEnv'` gives the `TrEnv'` step immediately, with no extra
hypothesis.  The three `VEnvs.WF` fields it does not supply are named in the file:
`hasPrimitives` and `safePrimitives` from `VEnv.HasPrimitives.extend` plus
`AddInductStagesR.find?_shape`'s safety gate, and `mono` from `AddInductStagesR.le`.

### 4.3 A note on ownership, for the orchestrator

The one-line decision this stream could not take: **may `Verify/Bridge.lean` be edited?**  It
is not frozen and no stream in this session's brief claims it, but it is not in this stream's
file list either, and the edit weakens
`not_leanTTConsistent_of_kernel_proves_false` by adding a hypothesis — an architectural
change, not a mechanical one.  The content is proved where this stream owns it; the edit is
stated above and not made.

---

## 5. `checkPrimitiveDef.WF.rest`

`docs/handoff-primitive.md` §5 ranks the remaining work (a) ≪ (b) < (d) ≪ (c).  **(a) and (b)
are now proved**, in `Verify/Primitive.lean`.

### 5.1 (a) The `Condition` reflection lemma — closed

There was **nothing** about `ite`/`dite`/`Decidable` anywhere in `Theory/` or `Verify/`
**[machine-checked: exhaustive grep]** — this is built from scratch.

```lean
def VExpr.condApp (F c inst t e : VExpr) : VExpr := ((((F.app c).app inst).app t).app e)

def VEnv.ReflectsCondApp (env : VEnv) (F P D : VExpr) (g : Nat → Nat → Bool) : Prop :=
  ∀ (a b : Nat) (t e : VExpr),
    VExpr.WF env 0 [] (VExpr.condApp F (P·a·b) (D·a·b) t e) →
    env.IsDefEqU 0 [] (VExpr.condApp F (P·a·b) (D·a·b) t e) (bif g a b then t else e)
```

`F` is left abstract — the conditional's head already applied to its result type, `@ite α` or
`@dite Nat` — so the constant name and the universe come from whatever `TrExprS` returns for
the recognizer's `q(@ite.{1})` / `q(@dite Nat)`, and **one shape serves both `Condition.ite`
and `Condition.dite`**.  This was the single design choice that halved the work.

Proved, all sorry-free modulo the standing `IsDefEqU.trans` taint from
`Theory/Typing/UniqueTyping.lean`'s `weakN_iff` — the *same* taint every existing
`reflects_*` lemma in the file already carries **[machine-checked, compared against
`reflects_natAdd`]**:

* `VExpr.WF.app_fn'`, `.app_arg'`, `IsDefEqU.app_congr_arg'`, `.app_congr_fn'`, `.wf_r`,
  `.app2_congr_fn` — general application congruences that chain onto a well-typedness proof
  rather than demanding the operator's Π-type, in the style the file already uses;
* `IsDefEqU.condApp_congr_inst` — replace a conditional's `Decidable` instance;
* `IsDefEqU.inst0` — instantiate a defeq under a binder of *arbitrary* domain (the existing
  `instNat`/`instBool` only cover `Nat`/`Bool`, and `checkITE`'s binders are `Prop` and
  `r.type p b`);
* `IsDefEqU.beta'` — β at `IsDefEqU`;
* **`VEnv.reflects_condApp`** — the lemma itself;
* `VEnv.reflects_condApp_natLE` — its `Condition.natLE` instance, whose boolean side is the
  `HasPrimitives` field `natBLE`, so the caller supplies nothing for it;
* `VEnv.ReflectsCondApp.natLE_le` — read back as `if a ≤ b then t else e`.

Nothing is assumed about `r.toDec` beyond the selector equations: the decision procedure is a
black box whose only property is that at a **literal** boolean it selects.  That is exactly
what `Reflection.checkITE` establishes and no more.

### 5.2 (b) The fuel induction — closed

```lean
theorem VEnv.reflects_fuel_go (henv : env.WF) … :
    ∀ (f x b : Nat), 1 ≤ b → x < f → ∀ hy h, Ok b hy h →
      env.IsDefEqU 0 [] (VExpr.app5 GO (.natLit b) hy (.natLit f) (.natLit x) h)
        (.natLit (sem x b))
```

Parametrised by the wrapper (`id` for `mod`, `Nat.succ` for `div`), the fuel-exhausted branch
(`x` for `mod`, `0` for `div`), and the arithmetic recurrence — so it is literally the same
induction twice, and the two corollaries `reflects_fuel_mod` / `reflects_fuel_div` are
three-line applications **[machine-checked]**.

The point the previous handoff flagged — that `Nat.modCore.go` is constrained *only* at
`Nat.succ fuel`, so the `fuel = 0` case is unreachable and staying inside that must be carried
— is the `x < f` invariant; the `f = 0` case discharges by `omega`.

The two proof arguments `go` carries (`1 ≤ y`, `Nat.succ x ≤ fuel`) are opaque `VExpr`s here,
handled by a caller-chosen predicate `Ok` and a proof-builder `K` (the shape
`Nat.div_rec_fuel_lemma` has in the recognizer) with the single requirement that `K` preserves
`Ok`.  **Nothing about their types is needed**, which is what makes the induction independent
of the branch's plumbing — and what let it be proved before the plumbing exists.

`reflects_succ` (a term reflecting `n` gives `Nat.succ ·` reflecting `n+1`) is proved on the
way, from `HasPrimitives.natSucc_hasType`.

### 5.3 What is left of (a)+(b): plumbing, and exactly which

The gap between the recognizer's *checked* equations and `reflects_condApp`'s `hsel` /
`reflects_fuel_go`'s `hgo` is **instantiation and β-reduction, no new mathematics**:

* `Reflection.ite` is a four-fold λ, so `r.ite p b H α` needs **four** `IsDefEqU.beta'`s to
  reach `condApp (I·α) p (toDec p b H)`;
* `Reflection.checkITE` compares under **two** `withCheckedLocalDecl` binders (`p : Prop`,
  `H : r.type p b`), so **two** `IsDefEqU.inst0`s;
* the checked equation is at the *function* level (`mkApp3 r.ite p true H`), so **two**
  `IsDefEqU.app_congr_fn'`s to apply it to `t` and `e`;
* the right-hand sides `fun α a _ => a` / `fun α _ a => a` need **three** more β steps.

All of those tools are now in the file.  This is the next task, and it is the only thing
between §5.1/§5.2 and a closed `Nat.mod` / `Nat.div` branch.

### 5.4 (d) and (c) — untouched, and what (c) would take

**(d)** `Nat.bitwise`'s second-order field was not attempted; §5(d) of `handoff-primitive.md`
stands unchanged.  Note that `reflects_condApp` is one of its three prerequisites and is now
available, so (d) is strictly cheaper than it was.

**(c)** `unfoldNatWellFounded`, deliberately left.  What it would take, restated after this
session's reading **[source]**: the fixpoint equation is read off *structural matches* against
a `Nat.rec` skeleton (`let .const \`\`WellFounded.Nat.fix [_,_] := fix`,
`unless (α, motive, f, F, a) == (α', motive', f', F', a')`,
`unless ih == .app (.app natRec t) y`) on the results of `whnfCore` and `unfoldDefinition`.  A
spec must therefore *reconstruct* `fix α motive f F a ≡ F a (fun y _ => fix α motive f F y)`
from syntactic equality checks, which needs `whnfCore.WF` / `unfoldDefinition.WF` in a form
that returns a defeq witness for the **whole application** — neither exists — plus an argument
that the matched `Nat.rec` skeleton really computes the fixpoint.  The previous handoff's
recommendation stands and this session did not find a cheaper route: **change
`unfoldNatWellFounded` to produce its equation by `checkedIsDefEq` instead of by structural
matching**, so the spec reads it off rather than reconstructing it.  That is an
implementation change and costs a Kernel Arena run.

---

## 6. Corrections to the brief

1. **"Land the honest restatement of `addDecl.WF`"** — the restatement is landed as a proved
   theorem; installing it *as* `addDecl.WF` is blocked by `Verify/Bridge.lean`, not by
   anything in this stream's files (§4.2).  The brief's premise that the branch could be made
   true-and-open in place did not survive contact with the consumer.
2. **"The obligation must use `VInductDecl'.WF`, not the re-staged `WFC`"** and **"`∃ et,
   venv.addIndTypes D = some et` must be an explicit conjunct"** — both were **already**
   applied to `InductStepNested` in `Verify/Environment/InductR.lean` before this session.
   Nothing needed correcting; the draft the brief refers to (`InductStepSafe` /
   `AddInductiveObligation`) is the older non-nested one, which §3 of that file already marks
   superseded.
3. **"(a) ≪ (b)"** — accurate as a ranking, but (b) turned out to be *cheaper in absolute
   terms* than (a), because the fuel induction can be stated over opaque proof arguments and
   so needs none of the conditional machinery, whereas (a) had to introduce the conditional
   layer from nothing.  Doing (a) first was still right: (b) consumes `ReflectsCondApp`.
4. **`bugs-found.md` / `divergences.md`** — no new entries.  No executable code was touched,
   so the `Nat.pow` / `Nat.shiftLeft` numeral-size divergence recorded by the previous stream
   is unchanged and no behaviour moved.
