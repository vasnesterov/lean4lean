# Handoff: `TrProj.weak'_inv` — the residual split, and why the route is closed rather than expensive

Round of 2026-09-02.  Scope: `Lean4Lean.TrProj.weak'_inv` (`Verify/Typing/Lemmas.lean`), the
`Verify/`-side census hole with **90** transitive users.  Everything below is marked **[measured]**
(a command was run in this tree, this round) or **[read off source]** (an argument from reading
definitions).  Nothing marked measured was inferred.

## 0. Bottom line

* **The hole is not closed, and the `sorry` is untouched.**  Census 13 → 13, byte-identical.
* **It is now split**, in `Lean4Lean/Verify/Typing/ProjWeakInvSplit.lean` (new, owned), into
  the **typing half of the `weakN_iff` hole** — an existing named statement — plus **one
  conversion statement**, and `TrProj.weak'_inv`'s exact statement is derived from those two with
  `IsDefEqU.weakN_iff` **absent from the cone**.  **[measured]**
* **The remaining half is bounded above by rigidity (C) together with const-app injectivity (B)**,
  now as a theorem rather than as the prose the `sorry`'s docstring carried.  **[measured]**
* **Verdict: the route is closed, not merely expensive.**  Every route to the remaining half is
  one of three, and all three are shut — (C) rigidity (only producer needs the refuted
  `VEnv.WeakNorm`), confluence-with-lift-preservation (`NormalEq.descend`, refuted), or
  inhabitation of the stripped binder (refuted at every consistent environment, `ProjInhab.lean`
  §1).  What is *new* is that the first of those is now the measured upper bound for exactly the
  part that the strengthening hole cannot pay for, so no future round need re-open the question of
  whether some fourth route might be cheaper *within the strengthening family*: it cannot be,
  because the remaining half is not an instance of that family at all (§3).

## 1. Correction: "both residuals bounded" is not about this hole twice

The brief said a recent commit "reduced it and left both residuals bounded".  Established in the
tree: commit `06e1b07` is a **two-stream** commit, and "both residuals" are **two different
streams'** residuals — `ParRedKStatement` (the confluence layer) and `ConstAppTypeStrengthen`
(this one).  For `TrProj.weak'_inv` the commit bounded **one** residual, three ways (not false /
not vacuous / not trivially true).  **[measured — `git log -1 --format=%B 06e1b07`]**

The state of this hole on entry, all of it landed by earlier rounds and all of it verified here:

| fact | where | status on entry |
|---|---|---|
| `weak'_inv` ⇐ `VEnv.ConstAppTypeStrengthen`, statement verbatim | `ProjWeakInv.lean` | proved, cone 3661, holes `{weakN_iff, forallE_inv_stratified, rigidShapeUniqNS}` **[measured]** |
| residual holds at depth 0, over inhabited lifts at every depth | same | proved, hole-free **[measured]** |
| residual ⇐ `ConstAppSkipUninhab` (one binder, uninhabited) | same | proved, hole-free |
| "uninhabited type exists" **is** `VEnv.Consistent`, as an iff | `ProjInhab.lean` §1 | proved |
| `AllTypesInhabited` closes the residual; satisfied at one `VEnv.WF` env | `ProjInhab.lean` §2 | proved, hole-free |
| `ConstAppSkipUninhab` is *stronger* than the residual needs | `ProjInhab.lean` §3 | proved |

So the entry state was: the residual is one opaque `Prop`, bounded from below (inhabited lifts) and
localised to one uninhabited binder, with the uninhabited case pinned to consistency.

## 2. What this round adds  **[measured]**

One new file, `Lean4Lean/Verify/Typing/ProjWeakInvSplit.lean` (owned; 29 declarations), plus an
`Update 8` paragraph on `TrProj.weak'_inv`'s own docstring (`Verify/Typing/Lemmas.lean`, owned —
the `sorry` and its statement are unchanged).

### 2.1 The split

    VEnv.TypingStrengthening env U        -- the TYPING half of the weakN_iff hole
    VEnv.ConstAppDefeqStrengthen env U    -- NEW: a c-spine defeq to a lift is defeq to a
                                          -- c-spine one context down (IsDefEqU only)
    ───────────────────────────────────────
    VEnv.ConstAppTypeStrengthen env U     -- the ProjWeakInv residual
    ⟹  TrProj.weak'_inv's exact statement

| theorem | cone | holes |
|---|---|---|
| `constAppTypeStrengthen_of_typing_head` | 3628 | `forallE_inv_stratified`, `rigidShapeUniqNS` |
| `TrProj.weak'_inv_of_typing_head` | 3679 | `forallE_inv_stratified`, `rigidShapeUniqNS` |
| `TrProj.weak'_inv_of_strengthen` (the entry state, for comparison) | 3661 | + `weakN_iff` |

`weakN_iff` leaves the cone because `OnCtx Γ` is recovered by `TypingStrengthening.onCtx_weak'_inv`
instead of `OnCtx.weak'_inv`.  **This is not the 3628 artefact `ProjWeakInv.lean` warns about**:
`weak'_inv_of_typing_head` takes the same `OnCtx Γ'`-only premise as the `sorry`, and the
consumer-shaped variant is unaffected.

### 2.2 The split is exact enough to name what is left, and tightened twice

* `VEnv.ConstAppDefeqStrengthenInh` — the same statement with `B` additionally **inhabited in the
  smaller context**, which is what the call site has (the projection's own subject).
  `ConstAppDefeqStrengthen.inh` is the (trivial) implication, so every bound transfers;
  `constAppTypeStrengthen_of_typing_head_inh` / `TrProj.weak'_inv_of_typing_head_inh` are the split
  at the tighter form.
* `VEnv.ConstAppDefeqStrengthenRF` — tighter again: only **rule-free** heads, plus `IsType` of the
  spine and both contexts' well-formedness.  Every one of those premises is discharged at the call
  site (§2.4).

### 2.3 The remaining half is bounded above by (C) + (B)

`constAppDefeqStrengthenInh_of_constRigid`: **(C) `VEnv.ConstRigid` together with (B)
`ConstAppInvStmt` proves the head statement, pointwise.**  Route, one step per ingredient:

1. (C) at `Γ'` (`VEnv.ConstRigid.at_lift`, already in `Rigidity.lean` for this consumer) — the
   lifted subject weak-head reduces to a `c`-spine.
2. `WHRedS.defeq` makes that a `Γ'`-conversion.
3. (B) reads off `us ≈ us₁` **and the arity** (`List.Forall₂.length_eq`) — neither of which (C)
   supplies; this is the docstring's "(B)'s level half", plus a fact nobody had recorded: **(B) is
   also what supplies `as'.length = as.length`**, which the consumer needs to split the spine at
   the parameter/index boundary.
4. `WHRedS.weakU_inv` moves the reduction into `Γ`; `VExpr.lift'_eq_constApp_inv` (new, 12 lines)
   reads the pre-image spine off the reduct.
5. `WHRedS.defeq` again in `Γ`, at the type of `B` given by the inhabitant.
6. Level well-formedness from the reduct's own typing (`IsDefEq.levelWF`, `levelWF_mkApp`) — **not**
   from `us ≈ us₁`, which does not transport it (`≈` is equality of evaluations; a level with an
   out-of-range parameter can be `≈` a well-formed one).

### 2.4 …and the loop closes at a structure head

(C) is stated only for rule-free heads.  The head `TrProj` needs is a **structure** name, and
`VEnv.IsStructure.ruleFreeHead` (`Theory/Typing/StructureRuleFree.lean`, cone 4091, **hole-free**
**[measured]**) supplies exactly that.  Threading it needs the residual to carry `hS`, so:

* `VEnv.ConstAppTypeStrengthenStruct` — the residual with the structure hypothesis;
  `ConstAppTypeStrengthen.struct` shows nothing is conceded.
* `TrProj.weak'_inv_of_structStrengthen` — `weak'_inv`'s statement from it.  **Its proof is
  `TrProj.weak'_inv_of_strengthen_onCtx`'s (`ProjWeakInv.lean:150`) verbatim** with `hS` passed to
  the residual, duplicated because the residual there is universally quantified over the head and
  cannot see that the head is a structure.  Recorded as a duplication, not a new proof.
* `TrProj.weak'_inv_of_constRigid` — **`TrProj.weak'_inv`'s exact statement from the typing half,
  (C) and (B)** at a `VEnv.Params` environment, every other side condition discharged inside.
  Cone 5767, holes `{weakN_iff, forallE_inv_stratified, rigidShapeUniqNS}`.

### 2.5 The rigidity route costs *more* than the split, and by a measured step  **[measured]**

`constAppDefeqStrengthenInh_of_constRigid` has cone 3813 and **re-imports `weakN_iff` in full**.
The step is `WHRed.weakU_inv` (cone 3611, holes `{weakN_iff, forallE_inv_stratified}`) — moving the
reduction into the smaller context.  So:

* the **split** needs the *typing half* of `weakN_iff` (43 of its 296 users' gate) and no more;
* the **rigidity route to the split's residual** needs the *whole* `weakN_iff` plus (C) plus (B).

That ordering was not on the record and it changes what a next round should attack.

## 3. Why the route is closed, stated sharply

The residual that resists is `VEnv.ConstAppDefeqStrengthen` (equivalently its `Inh`/`RF`
tightenings): **from `Γ' ⊢ B.lift' l ≡ (const c us).mkApp as`, conclude `Γ ⊢ B ≡ (const c us').mkApp as'`.**

1. **It is not an instance of the strengthening hole, and this is machine-checked, not read off
   the shape.**  `Strengthening`, `StrengtheningTarget` and `IsDefEqU.weakN_iff` all require *both*
   endpoints to be lifts (`.Skips n k`).  `constAppDefeqStrengthen_rhs_not_skips` exhibits an
   instance — one constant `c : Sort 1 → Sort 1`, one β-redex — where the hypothesis **holds** and
   the right-hand side **does not skip** the stripped binder.  So however `weakN_iff` is
   discharged, `TrProj.weak'_inv` is not a corollary of it.  **[measured]**
2. **What is left is a head-preservation (rigidity) fact.**  §2.3 proves rigidity + injectivity
   *suffice*.  Necessity is not proved and is not claimed — but every route anyone has written down
   goes through one of: (C), whose only producer `constRigidPat_of_weakNorm` needs the sorry-free
   **refuted** `VEnv.WeakNorm`; Church–Rosser plus `ParRed.weakN_inv`, which re-imports the
   **refuted** `NormalEq.descend`; or inhabitation, which `ProjInhab.lean` §1 shows fails at every
   consistent environment.  **[read off source, from the three refutation files; the sufficiency
   direction is measured]**
3. **Narrowing to structure heads does not help.**  It discharges (C)'s *side* condition
   (`RuleFreeHead`, via `IsStructure.ruleFreeHead`) and nothing else; (C)'s gate is `WeakNorm`, i.e.
   weak-head-normal-form **existence**, which the structure hypothesis says nothing about.
   **[read off source]**

So: **expensive is the wrong word.**  Closing this hole needs either a proof of (C) that does not
go through whnf existence, or `KDescend.lean`'s repair of `NormalEq.descend`, or a consistency
assumption threaded through `TrProj` and `addDecl.WF`.  All three are other files' business, and
two of the three are known-refuted as stated.

## 4. Anti-vacuity  **[measured]**

The instruments read conclusions; none asks whether a hypothesis is inhabited.  So:

* **Both hypotheses of the split are simultaneously satisfiable at a `VEnv.WF` environment.**
  `exists_univInhabEnv_typing_and_head`, cone 3274, `#print axioms` = `[propext,
  Classical.choice, Quot.sound]` — **hole-free**.  `exists_univInhabEnv_trProj_weak'_inv_split`
  fires the composite there (and is `sorryAx`-tainted, from `HasArgs.of_mkApp`, exactly as
  `ProjInhab.lean`'s counterpart is).
* **Scope of that witness, stated rather than implied:** that environment is *inconsistent*
  (`AllTypesInhabited.not_consistent`) and has no uninhabited binder at any well-formed context, so
  it witnesses satisfiability and **nothing** about the obstruction.
* **The degenerate instance.**  `constAppDefeqStrengthen_fires_degenerate`: `Γ = []`, empty spine,
  depth-one lift — hypotheses satisfiable, conclusion discharged, in every environment declaring a
  `Sort 0`-valued constant.
* **The head statement is not trivially true.**  Its `∃ as'` is load-bearing:
  `constAppDefeqStrengthen_moves` shows that at §3.1's witness the produced spine **differs** from
  the given one (the β-redex has to be converted away, not renamed).
* **The tightened form's premise is not vacuous where it matters.**
  `constAppDefeqStrengthenInh_rhs_not_skips` re-runs §3.1's witness with one further constant
  `d : c (Sort 0)`, so the *inhabited* form has the same non-skipping instance.  Without this the
  §2.2 narrowing could have been vacuous at exactly the instances carrying its content.
* **No conclusion was weakened.**  `TrProj.weak'_inv_of_typing_head`,
  `_of_typing_head_inh`, `_of_structStrengthen` and `_of_constRigid` all prove the `sorry`'s
  statement verbatim, at its own premises (`OnCtx Γ'`, `Ctx.Lift'`, the `TrProj`).

## 5. What I tried that failed, and the step it failed at

1. **Deriving the residual from the existing strengthening hole.**  Failed at *application*: the
   right-hand side of the equation is a `c`-spine whose arguments live in `Γ'` and need not be
   lifts, so `IsDefEqU.weak'_iff`/`weakN_iff` has no instance with that hypothesis.  Turned into
   §3.1's witness rather than left as prose.
2. **`HasType.skips` + uniqueness as a route to the head.**  It gives that the `c`-spine *is* defeq
   to a lift — which the hypothesis already says — and stops exactly where the docstring's original
   trace stops: reading the **head** off the pre-image.  No progress; recorded so it is not
   retried.
3. **An exact (two-directional) split.**  Not achieved: `ConstAppTypeStrengthen` does **not**
   visibly imply the head statement, because the head statement's hypothesis supplies no inhabitant
   of the `c`-spine *type*, which the residual needs as its subject.  Consequence, stated honestly:
   the split's two hypotheses may be *jointly stronger* than the residual.  The `Inh` and `RF`
   tightenings (§2.2) narrow that gap to premises the call site actually has; they do not close it.
4. **Taking `IsStructure` into the head statement itself** (rather than only its `RuleFreeHead`
   consequence).  Not done: it repairs nothing (§3.3) and its non-vacuity would need an
   `IsStructure` witness, i.e. a full `addInduct'` staging.  The premise is there for the taking —
   `TrProj.mk` carries it — and §8 of the new file records that.

## 6. Measurements, verbatim

* `lake build`: **Build completed successfully (1499 jobs)**, exit 0.  **No errors in any file**,
  hence none in the files this stream owns.  (The 1499th job is the new module.)
* `lake build Lean4Lean.Experimental.ConeJoin Lean4Lean.Verify.Guard`:

      guard 1: Axioms.lean declares exactly the 24 frozen axioms ✓
      guard 2: kernel_sound axioms within whitelist ✓ (proof INCOMPLETE: sorryAx present)
      guard 3: checker cone implementation gaps within frozen list (2/2 remaining) ✓

  24 and 2/2 as required; guard 2's `INCOMPLETE` is its standing state.  No guard number moved.
* `scripts/sorry-census.lean`, start and end of round: **TOTAL 13**, outputs **byte-identical**
  (`diff` reports nothing).  The row for this hole, at both ends:

      Lean4Lean.Verify.Typing.Lemmas: 1
          Lean4Lean.TrProj.weak'_inv   [90 transitive users]

  So the brief's "90 transitive users" is confirmed, and no hole was closed, moved or added.
* `#print axioms` for all **29** new declarations: 19 are `[propext]` / `[propext, Quot.sound]` /
  `[propext, Classical.choice, Quot.sound]`, i.e. **hole-free**; 10 carry `sorryAx`, all of it
  inherited from three pre-existing Theory-side holes — `forallE_inv_stratified` and
  `rigidShapeUniqNS` (through `IsDefEq.uniqU` and `HasArgs.of_mkApp`) and, in the three
  ConstRigid-route theorems, `weakN_iff` (through `WHRed.weakU_inv`).  **No new `sorry` was
  written**, and no `sorryAx` was replaced by another.
* **No frozen-axiom dependency**: a cone scan for `.axiomInfo` constants over all seven composite
  theorems finds only `propext`, `Classical.choice`, `Quot.sound`, `sorryAx` — no `Lean4Lean.*`
  axiom.  **[measured]**
* No duplicate names: each of the 29 identifiers occurs in no other `.lean` file.  **[measured]**
* No implementation file was touched, so goal 1 (Kernel Arena) is unaffected and was not re-run.

## 7. Relay to the orchestrator — two caveats you need

1. **`Experimental/ConeJoin.lean` was NOT edited** (this brief forbade it), so
   `scripts/sorry-census.lean` and `scripts/dup-names.lean` are **blind to the new module**.  The
   census's unchanged figures are therefore unchanged *for that reason too*, not only because the
   module adds no hole.  If the module is added to `ConeJoin`, the counts that move are:
   `forallE_inv_stratified` and `rigidShapeUniqNS` **+10 users each**, `weakN_iff` **+3**
   (`constAppDefeqStrengthenInh_of_constRigid`, `constAppDefeqStrengthenRF_of_constRigid`,
   `TrProj.weak'_inv_of_constRigid`).  Measured per-declaration, not estimated.
2. **`TrProj` was not widened**, and no route here asks for it.  The ruling is respected: the
   split, the tightenings and the rigidity route all live outside `TrProj`, and
   `TrProj.weak'_inv_of_structStrengthen` rebuilds `TrProj.mk` from the same fields.

## 8. What I would pick up first

1. **Do not attack `ConstAppDefeqStrengthen` through the strengthening family.**  §3.1 is a
   machine-checked reason it cannot work.  Anyone who reports "closing `weakN_iff` closes
   `weak'_inv`" is wrong, and the witness that says so is two lines to re-run.
2. **If this hole is to be closed, the cheapest *named* prerequisite is now `KDescend.lean`'s
   repair of `NormalEq.descend`**, because that is what unlocks the confluence route to the head
   statement (common reduct, `ParRed.constApp_inv` keeps the head, `ParRed.weakN_inv` keeps the
   lift).  The rigidity route is strictly more expensive (§2.5) *and* dead at its gate.
3. **The `ParRedKWeakN`/`ParRed.weakN_inv` cycle is the one thing not measured here.**  It is the
   step the confluence route needs and the reason the previous round did not take it; whether the
   `ParRedK` restatement (`KSite7Rows.lean`, same commit `06e1b07`) makes it available is the
   question I would ask next, and it belongs to the confluence stream, not this one.
4. **Do not re-derive §2.3 step 3.**  (B) supplies the arity as well as the levels; a round that
   budgets a separate arity argument is budgeting twice.
