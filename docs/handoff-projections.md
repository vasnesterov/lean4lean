# Handoff: the projection cluster

**Census: 19 → 19.**  No hole closed and none added.  What moved is *what the three open holes
in this cluster are blocked on*: facts (A), (B) and (D) of `Theory/Typing/Injectivity.lean`'s
constant-application taxonomy are now **proved** modulo one hypothesis, and (C) is **proved
from weak-head normalisation and nothing else**.  Full `lake build` green; all three of
`Verify/Guard.lean`'s checks pass (guard 2 still reports `proof INCOMPLETE: sorryAx present`,
as it must while 19 holes remain).

Everything below is separated into **machine-checked** (a named, `sorry`-free-or-explicitly-
tainted declaration in the tree, with its cone measured) and **read off source** (an argument
from reading definitions, not checked).

---

## 0. Pick this up first

1. **`VEnv.PatWF`** (`Theory/Typing/ParamsBuild.lean`).  It is now the single hypothesis
   standing between this tree and (A), (B) and (D) *unconditionally*.  It is one field of
   `VEnv.Params`; `VEnv.paramsOfWF` derives the other nine from `VEnv.WF`.  It is proved
   outright on the δ fragment (`patWF_of_deltaFragment`); the ι and quotient cases need
   `IsDefEqU.forallE_inv`, which is an **existing census hole**, not a new one.  Discharging
   `PatWF` closes `quotReduceRec.WF`'s mathematical content and two of `TrProj.uniq`'s four
   obligations at once.  This is the highest-leverage single item in the cluster.
2. **`RecTypeResidual`** (§3.4 of the previous edition, unchanged) — ledger G4's remainder.
3. **Weak-head normalisation** (`VEnv.WeakNorm`, `Verify/Typing/ConstSpine.lean`) — (C)'s
   only residual, and `TrProj.weak'_inv`'s last mathematical one.

---

## 1. Status of the four

| | status | blocked on |
|---|---|---|
| `TrProj.wf` | **PROVED** (previous edition) | — (cone: `IsDefEqU.weakN_iff`, `forallE_inv_stratified`) |
| `TrProj.weak'_inv` | open | (C) ⇐ `WeakNorm`; (B) ⇐ `PatWF`; `IsDefEqU.weak'_iff` |
| `TrProj.uniq` | open | `PatWF`; `RecTypeResidual`; a `projTerm` congruence |
| `inferProj.WF` | open **by deliberate choice** | see the previous edition §6; unchanged |

---

## 2. What landed this round: `Verify/Typing/ConstSpine.lean` (new, 707 lines)

### 2.1 The correction that unlocked it

`Theory/Typing/Injectivity.lean` attaches the same residual to all six of its statements: the
**`trans`** case of an induction on `IsDefEqStrong` — "a term convertible with a rule-free
constant application reduces to one".  Last round's note that `const_app_inv` had been
"reduced to `trans` as its only residual" was correct about that induction.

**But the `trans` case is an artefact of the induction, not of the statements.**
`VEnv.NormalEq` (`Theory/Typing/ChurchRosser.lean`) has **no `trans` constructor** —
transitivity there is `NormalEq.trans`, a *theorem*, and `VEnv.IsDefEq.church_rosser` has
already paid for it.  An argument routed through Church–Rosser never meets that case.

Machine-checked, all in `Verify/Typing/ConstSpine.lean`:

| name | content |
|---|---|
| `VEnv.ParRed.constApp_inv`, `.ParRedS.constApp_inv` | a parallel reduct of `(const c ls).mkApp as` is `(const c ls).mkApp as'` with `as ≫ as'` pointwise.  `beta` is impossible (the spine head is not a λ), `extra` is impossible under `PatFreeHead` |
| `VEnv.NormalEq.constApp_inv` | `NormalEq` between two constant spines is head-, level- and argument-wise.  Only `refl`, `constDF`, `appDF` are reachable; `proofIrrel` is blocked by `¬IsProof` threaded down the spine by `IsProof.app'`; `etaL`/`etaR` by shape |
| `VEnv.IsDefEq.constApp_inv` | the two joined by `church_rosser`.  **(B) and (D) in one statement** |
| `VEnv.NormalEq.constApp_forallE`, `.constApp_sort`, `IsDefEqU.constApp_forallE_false`, `.constApp_sort_false` | **(A)**, by the same route and more cheaply — with the right-hand side a Π or a sort, `proofIrrel` is `NormalEq`'s only live constructor, and the right-hand side's being a type refutes it |

### 2.2 The `VEnv`-level results, and the anti-strawman checks

`VEnv.paramsOfWF` turns each of these into a statement about an arbitrary well-formed
environment, conditional on `VEnv.PatWF`:

* `VEnv.const_forallE_inv_of_patWF`, `VEnv.const_sort_inv_of_patWF` — **(A)**
* `VEnv.const_app_inv_of_patWF` — **(B)**
* `VEnv.constApp_inv_of_patWF` — (B) and (D) together
* `VEnv.constNoConf_of_patWF` (`Verify/Typing/Rigidity.lean`) — **(D)**, as the stated
  `VEnv.ConstNoConf`, so it is its own anti-strawman check

For (A) and (B) the anti-strawman check is explicit and in the house style of
`Theory/Typing/HeadRedStuck.lean`: `ConstAppInvStmt`, `ConstForallEInvStmt`,
`ConstSortInvStmt` are the three `Injectivity.lean` theorems' types with every binder made
explicit and nothing else changed; `…_holds` proves each **by** that theorem (deliberately
`sorryAx`-tainted) and `…_of_patWF` proves the same `Prop` from `PatWF`.  The two sit side by
side, so no statement can have been narrowed unnoticed.

### 2.3 The measured cone — this is the point

Machine-measured (forward reachability from the declaration, `sorryAx`-containing
declarations only):

```
Lean4Lean.VEnv.constApp_inv_of_patWF        -- (B)+(D)
Lean4Lean.VEnv.const_forallE_inv_of_patWF   -- (A), Π half
Lean4Lean.VEnv.const_sort_inv_of_patWF      -- (A), sort half
    IsDefEqU.weakN_iff
    IsDefEqU.forallE_inv_stratified
    NormalEq.descend
    IsDefEqU.forallE_inv
```

Four existing census holes, **none of them a constant-application fact**.  In particular
`const_app_inv`, `const_forallE_inv`, `const_sort_inv` and `sort_forallE_inv` are *not* in the
cone, so this is not circular.

**Consequence for the ledger.**  The constant-application family is not an independent
obligation.  It is downstream of the sort/Π family, of `NormalEq.descend`, and of `PatWF`.

### 2.4 A second correction: (B)'s side condition is not the one that blocks the step

`RuleFreeHead` is a fact about `env.defeqs`.  The reduction step it has to block is
`WHRed.extra` / `ParRed.extra`, which fires on a `Params.Pat`-registered pattern.  The
`Params` class relates `Pat` and `defeqs` in **one direction only** (`extra_pat`: every rule
is a registered pattern under leading λs); nothing forbids an instance whose `Pat` registers a
pattern headed by a `RuleFreeHead` constant.

So `VEnv.PatFreeHead` is the honest condition, and:

* `Lean4Lean.Pat.headConst_defeqs` (machine-checked) — every pattern the **canonical** table
  `Lean4Lean.Pat env` registers has the head constant of a rule's left-hand side, in all three
  constructors (δ, ι, quot);
* `VEnv.RuleFreeHead.patFreeHead` (machine-checked) — hence `RuleFreeHead → PatFreeHead` at
  `paramsOfWF`'s instance, which is the only one any consumer meets.

This matters for `VEnv.ConstRigid` as it was stated in `Verify/Typing/Rigidity.lean`: it is
`[Params]`-gated and carries `RuleFreeHead`, so **as stated it is under-hypothesised** — the
hypothesis cannot reach the step it is meant to block.  The statement is kept verbatim (so the
correction is legible) and `VEnv.ConstRigidPat` is the repaired form.  This is the same defect
class as `RecTypeInj` (§3.3 of the previous edition): a hypothesis set carrying strictly less
information than its conclusion needs, invisible to an auto-bound-implicit audit.  (The
running count of such statements in this development is kept elsewhere and is not asserted
here; what is asserted is the defect and its repair.)  Note the difference from the earlier
finds: `ConstRigid` is not shown **false** — it is shown *unreachable from its own
hypotheses*.  No instance refuting it is exhibited, and none is claimed.

Machine-checked necessity, at the tree's one concrete `Params` instance
(`Theory/Typing/ParamsWitness.lean`'s `propLoopParams`, where a `ParRed.extra` step really
fires) — all three `sorry`-free:

* `propLoop_not_patFreeHead_A` — `PatFreeHead` fails at `A` there;
* `propLoop_patFreeHead_other` — and holds at every other name;
* `parRed_constApp_inv_needs_patFreeHead` — **dropping `PatFreeHead` from
  `ParRed.constApp_inv` makes that lemma false**, because `A ≫ B` and `B` is not an
  application of `A`.

### 2.5 Non-vacuity: (A), (B) and (D) fired end to end, with `PatWF` **discharged**

`Theory/Typing/CycleConv.lean`'s `propLoopEnv2` is `propLoopEnv` *before* its two δ-rules are
added: two constants `A B : Prop` and no definitional-equality rules at all.  It is in the δ
fragment vacuously, so `VEnv.patWF_of_deltaFragment` discharges `PatWF` outright.  Added to
`Verify/Typing/Rigidity.lean`, all machine-checked:

* `propLoopEnv2_wf`, `propLoopEnv2_patWF` — **`sorry`-free**.  Two `VDecl.axiom` steps from the
  empty environment, then `PatWF` from the δ fragment.
* `propLoopEnv2_A_ne_B` — **(D) with content**: two distinct propositions of a rule-free
  environment are not definitionally equal.
* `propLoopEnv2_A_ne_sort`, `propLoopEnv2_A_ne_forallE` — **(A) with content**.

These are the first end-to-end firings of the constant-application family in this tree:
`VEnv.WF` → `paramsOfWF` → `IsDefEq.church_rosser` → the spine analysis, with **no hypothesis
carried**.  Their only taint is the four inherited holes of §2.3.  So the results are not
vacuous, and `PatWF` is not an unsatisfiable ask — it is discharged here.

---

## 3. (C) rigidity: why Church–Rosser does not settle it, and what does

### 3.1 The obstruction, exactly

The spine recursion that proves (B) and (D) works because *both* endpoints are constant
spines, so `NormalEq.etaL` is excluded by shape at every level.  For (C) only the right
endpoint is known, and `etaL` relates a **λ** to a constant application.

* At the **top** of the spine that is excluded by (C)'s `IsType` side condition: an
  η-expansion has a Π type, and a Π is not a sort.  Machine-checked as
  `VEnv.isType_lam_false`.
* At a **proper sub-spine** it is not excluded, because a sub-spine legitimately has a Π type.
  And the induction hypothesis one would need there is **false**: `.lam A b` is a weak-head
  normal form (`WHNF.lam`) that η-relates to a constant application and is not one.
  Machine-checked as `VEnv.whnf_lam_not_constApp` (`sorry`-free).

This is why (C) is genuinely a different statement from (B), and it is a *sharper* reason than
the one `Injectivity.lean` gives ("its formulation mentions weak-head reduction").

### 3.2 The repair, machine-checked

A `WHNF` application has a `WHNF`, non-λ function (`VEnv.WHNF.app_fn`,
`VEnv.WHNF.app_not_lam`), so along a `WHNF` spine `etaL` is excluded at every level after all.

| name | content |
|---|---|
| `VEnv.StRed.constApp_whnf` | a weak-head normal form that standard-reduces to a constant spine *is* one |
| `VEnv.NormalEq.constApp_whnf` | the spine analysis under a `WHNF`, non-λ subject |
| `VEnv.WeakNorm` | `∀ Γ e A, OnCtx Γ → Γ ⊢ e : A → ∃ e', Γ ⊢ e ⤳* e' ∧ WHNF Γ e'` |
| **`VEnv.constRigid_of_weakNorm`** | **(C), from `WeakNorm` and nothing else** |
| `VEnv.constRigidPat_of_weakNorm` | the same, packaged as the stated `VEnv.ConstRigidPat` |

Cone of `constRigid_of_weakNorm`: `weakN_iff`, `forallE_inv_stratified`, `NormalEq.descend`,
`forallE_inv`, `sort_forallE_inv` — one more than (A)/(B)/(D), all existing census holes.

Read off source (not checked): `WeakNorm` is not in the tree in any form, and
`Theory/Typing/HeadRedStuck.lean` is the relevant warning — it shows that a `Params` instance
hosting a *stuck* K-redex that is definitionally a sort would refute `IsDefEq.reduce_sort`.
Any route to `WeakNorm` has to rule such instances out.

---

## 4. `TrProj.weak'_inv`: the swap does **not** transfer, and there is a cheaper entry point

**Asked and answered.**  `ProjSkip.lean`'s swap (the move that unblocked `TrProj.wf`) replaces
an unused entry of the *projection's own field telescope*, so that `projMotiveTerm` stays
saturated while being typed.  Every clause `TrProj.mk` asks for in `weak'_inv`'s conclusion —
`IsStructure`, one `HasType`, three length equations, `hus`, two `HasArgs`, F17 — is a
statement in the ambient context `Γ`, and **none of them mentions that telescope**.  So the
swap has nothing to act on here.  (Read off source: the clause list is `TrProj`'s definition,
`Verify/Typing/Expr.lean:81–145`.)

Machine-measured: the two lemmas' *shared* residual is `IsDefEqU.weakN_iff` and
`forallE_inv_stratified` — `TrProj.wf`'s whole cone — and nothing else.  The previous
edition's claim that they "share a blocker" is right about `weakN_iff` and was never about the
swap.

**Cheaper entry point, not yet tried** (read off source): `VEnv.InferTypeS.weakU_inv`
(`Theory/Typing/HeadReduction.lean:691`) inverts a lift on a whole *inferred typing* and hands
back a type living in `Γ`.  That is steps 1 and 3 of the traced route (`HasType.skips` at
`Ctx.Lift'`, then `IsDefEqU.weak'_iff`) in one already-proved lemma, at the cost of being
`Params`-gated — which (C) already is.  `VEnv.InferType.exists` supplies its input from
`VEnv.WF` alone.

What `weak'_inv` still needs after that, read off source: (C) at `Γ'`; `WHRedS.weakU_inv` to
move the reduction into `Γ` (already proved, already in `Ctx.Lift'` form); (B)'s level half to
reconcile the recovered `us'` with the use site's `us` (**now available**,
`const_app_inv_of_patWF`); a `HasArgs` congruence along argument-wise `IsDefEqU`; and a
`HasArgs` strengthening across the lift.  The last two are plumbing that does not exist yet
and has not been costed.

---

## 5. `TrProj.uniq`: two of four obligations discharged

Unchanged in statement.  Its four obligations were: (1) ledger G4, (2) fact (B), (3) fact (D)
via the independence of `s₁`, `s₂`, (4) a `projTerm` congruence lemma.

* (2) and (3) are **proved**, modulo `PatWF` — `const_app_inv_of_patWF`,
  `constNoConf_of_patWF`.
* (1) is `RecTypeResidual`, unchanged from the previous edition §3.4.
* (4) is unchanged: mechanical, real work, still uncosted.

Note (D) is now proved *without* ledger G4: no-confusion between distinct rule-free constants
does not go through structure uniqueness at all.  G4 is still needed for (1).

Non-vacuity of (D) at a rule-free environment is §2.5, with `PatWF` discharged.  At the
two-field *structure* witness it is machine-checked
(`Verify/Typing/Rigidity.lean`) as: `barEnv_ruleFreeHead'` generalises the previous
`barEnv_ruleFreeHead` to every name but `Bar.rec`, and `barEnv_bar_ne_ctorApp` derives from
(D) that `Bar` is **not** definitionally equal to any application of `Bar.mk` — a negative
statement with content, at the environment where `RuleFreeHead` is proved rather than assumed.
Two hypotheses are carried rather than discharged there, and neither is about `barDecl`:
`barEnv.WF` (because `VInductDecl'` is not yet wired into `VDecl.induct` — the same gap
`ProjWfWitness.lean` §2.5 records) and `PatWF` (the open `Params` field itself).

---

## 6. Corrections to earlier editions of this file and to docstrings

1. **"(B) is reduced to `trans` as its only residual"** — true of the `IsDefEqStrong`
   induction, and *not* a fact about the statement.  Church–Rosser proves (B) outright modulo
   `PatWF`; the `trans` case never arises because `NormalEq` has no `trans` constructor.
2. **"(C) needs (B) plus rigidity"** and **"`TrProj.weak'_inv` needs (C), (B)'s level half and
   `weak'_iff`"** — the list is right, and (C)'s own residual is now named: `WeakNorm`.
3. **`VEnv.ConstRigid`'s `RuleFreeHead` side condition** is the wrong condition under an
   abstract `Params`.  Use `VEnv.ConstRigidPat`.  §2.4.
4. **"`TrProj.wf`'s swap may help `weak'_inv`"** — it cannot.  §4.
5. `Theory/Typing/Injectivity.lean`'s module docstring says a fourth fact (no-confusion) "is
   not stated because no consumer has asked for it".  It is now stated *and proved*
   (`VEnv.ConstNoConf`, `VEnv.constNoConf_of_patWF`).  Both it and the (A)/(B) proofs belong
   in that file rather than under `Verify/`; they are here only because that file is another
   stream's.  Nothing in `ConstSpine.lean` depends on `Verify/`, so it moves verbatim.

---

## 7. Files

New:

* `Lean4Lean/Verify/Typing/ConstSpine.lean` — §2, §3.  Imports `Theory/Typing/HeadReduction`,
  `Theory/Typing/Injectivity`, `Theory/Typing/ParamsBuild`.  Depends on nothing in `Verify/`.

Edited (all owned by this stream):

* `Lean4Lean/Verify/Typing/Rigidity.lean` — (D) proved; (C) repaired and reduced;
  `PatFreeHead` necessity witnesses; the `propLoopEnv2` end-to-end firings (§2.5); `barEnv`
  non-vacuity; header rewritten.  Now imports `Theory/Typing/ParamsWitness` and
  `Verify/Typing/ConstSpine`.
* `Lean4Lean/Verify/Typing/Lemmas.lean` — docstrings of `TrProj.weak'_inv` and `TrProj.uniq`
  updated (§4, §5).  No proof changed; census unchanged.
* `Lean4Lean/Verify/TypeChecker/WHNF.lean` — `quotReduceRec.WF`'s docstring updated: its
  residual is now *forward* (discharge `PatWF`), not *sideways* (state a new inversion
  principle).

Unchanged: `Theory/Inductive/StructureClosed.lean`, `Verify/Typing/ProjLevelWitness.lean`,
`Verify/Typing/ProjSkip.lean`, `Verify/Typing/ProjWfWitness.lean`,
`Verify/Typing/StructureUniq.lean`, `Verify/TypeChecker/InferType.lean`.

**Auto-bound-implicit audit.**  Every new statement is a `def … : Prop` with explicit binders,
or a theorem whose binders were read back from the elaborated type.  The defect that bit this
round was again a different one — §2.4.
