# Handoff: `inferProj.WF` — closeable today, and that is exactly why it must not be closed

Round of **2026-09-02**.  Scope: `Lean4Lean.TypeChecker.Inner.inferProj.WF`
(`Lean4Lean/Verify/TypeChecker/InferType.lean:468`), the `Verify/`-side census hole with **70**
transitive users and one of `kernel_sound`'s nine.  Split as elsewhere in this repo into
**[measured]** (a command was run in this tree, this round) and **[read off source]** (an argument
from reading definitions).  Nothing marked measured was inferred.

## 0. Bottom line

* **The hole is not closed and the `sorry` is untouched.**  Census **13 → 13**, byte-identical.
  **[measured]**
* **It is nevertheless provable today, hole-free, in one line** — `inferProj_always_throws hty`,
  a theorem 20 lines below it in the same file, is general in the postcondition and has exactly
  this type.  Axioms `[propext, Classical.choice, Quot.sound]`, no `sorryAx`, no frozen axiom;
  cone 6973 with an **empty** hole set.  **[measured]**
* **So this hole is not hard and not blocked; it is a bookkeeping decision, and it is the only one
  of the nine in that state.**  The decision is the orchestrator's, and my recommendation is
  **do not take it**, for a reason that is a measurement rather than a preference: the tripwire
  people usually pay a vacuity close for **already exists as a landed theorem**, so closing buys
  nothing and costs the census row.  §2.
* **No split of this hole can carry information** — provably, not as an opinion.  §3.  So the
  `TrProj.weak'_inv` treatment (`docs/handoff-trproj-weakinv.md`) **cannot** be borrowed here, and
  the brief's question about that shape has a definite negative answer with a reason.
* **What resists, once the vacuity lifts, is two unchecked fields of `VEnv.IsStructure`** in
  **positive** position, and reaching them needs the `TrProj` widening the standing ruling reserves
  to the orchestrator.  **Route status: closed to me, not merely expensive.**  §4.
* **The statement is not FALSE today** and cannot be refuted today — I tried, and §5 names the step
  each of three refutation attempts failed at.  Its falsity is *conditional on the `AddInduct`
  flip*, and that conditionality is not something any instrument in this tree can see.

## 1. The one-line proof, verbatim  **[measured]**

`inferProj_always_throws` (`InferType.lean:508`, landed by an earlier round) is

```lean
theorem inferProj_always_throws {c : VContext} {s : VState} (hty : c.TrExprS ety ety')
    {Q : Expr → VState → Prop} : (inferProj st i e ety).WF c s Q
```

— **universally quantified over `Q`**.  `inferProj.WF`'s conclusion is an instance of it, so

```lean
theorem inferProj.WF
    (he : c.TrExprS e e') (hty : c.TrExprS ety ety') (hasty : c.HasType e' ty') :
    (inferProj st i e ety).WF c s fun ty _ =>
      ∃ e'' ty'', c.TrTyping (.proj st i e) ty e'' ty'' :=
  inferProj_always_throws hty
```

is the whole proof.  **That is the exact edit**, and it was compiled in scratch
(`lake env lean` on a file importing `Verify.TypeChecker.InferType`; `he` and `hasty` become
unused-variable warnings).  Measurements:

| name | axioms | forward cone | holes in cone |
|---|---|---|---|
| the one-line `inferProj.WF` (scratch) | `[propext, Classical.choice, Quot.sound]` | — | — |
| `inferProj_always_throws` | `[propext, Classical.choice, Quot.sound]` | 6973 | **∅** |
| `inferProj.WF` (as it stands, `sorry`) | — | 4399 | itself only |
| `TrEnv.not_inductInfo` | — | 6103 | **∅** |
| `TrProj.isStructure` | — | 690 | **∅** |
| `TrProj.wf` | — | 5076 | `weakN_iff`, `forallE_inv_stratified` |
| `projTerm_hasType` | — | 5067 | `weakN_iff`, `forallE_inv_stratified` |

**The brief's caution about `weakN_iff` is answered, by measurement rather than analogy:**
`inferProj.WF` is **not** downstream of `IsDefEqU.weakN_iff`.  Its own cone's only hole is itself,
and the route that would close it today is hole-free.  `weakN_iff` enters only on the *live* route,
through the target-typing obligation (`projTerm_hasType`, `TrProj.wf`), i.e. after the flip.

**One correction to `docs/research-proj-reduction.md` §5.**  That scope said the vacuity mechanism
has a wrinkle — `TrEnv'.no_inductInfo` "is proved only at `safety = .unsafe`" — and costed a
safety-uniform lemma at 20–30 lines.  It exists and is landed: `TrEnv.not_inductInfo`
(`Verify/TypeChecker/Reduce.lean:116`) takes **no** safety hypothesis, proved by induction over
`TrEnv'` with `ignore` discharged by the `∃ ci', venv.constants name = some ci'` guard.  The
docstring there records that the mechanism the scope predicted ("no `.inductInfo` shape in
`TrConstant`") is *not* the one that works.  **[measured — `inferProj_always_throws` compiles at
arbitrary `c.safety`]**

## 2. Why closing it is information-destroying rather than merely vacuous  **[measured]**

The usual argument *for* discharging a vacuously-true hole is that a `sorry` is silent forever
while a vacuity proof **breaks the build** the moment the vacuity lifts.  Here that argument does
not apply, and the reason is a fact about the tree, not a judgement:

* `inferProj_always_throws` is **already landed**, its only substantive step is
  `c.trenv.not_inductInfo`, and `not_inductInfo` holds **only** while `AddInduct`
  (`Verify/Environment/Basic.lean`) has no constructors.  So the tripwire is in place today, with
  or without the `sorry`.  Its own docstring says exactly this: *"when it becomes
  `AddInductStages` this theorem goes red, and that is the point of keeping it."*
* Therefore closing `inferProj.WF` by that route adds **no** tripwire and removes **one** census
  row: `scripts/sorry-census.lean` would read TOTAL 12 and guard 2's hole set would read 8.

And the cost is not only bookkeeping.  Closing it makes the **emptiness of `AddInduct`
load-bearing for goal 2**.  `CLAUDE.md` forbids narrowing `kernel_sound`'s statement to make a
proof go through; a vacuity close narrows nothing in the *statement* and everything in the
*hypothesis* — which is precisely the blindness the brief's anti-vacuity clause is about
("every instrument here reads conclusions… none asks whether a hypothesis is inhabited").  Nine
such closes in a row would print `proof COMPLETE` for a kernel whose verification says nothing
about any inductive declaration.

This also agrees with the in-tree ruling already on the `sorry`'s docstring (*"closing it
vacuously today would hide that"*), which I did not override.

## 3. Why the `weak'_inv` split shape cannot be borrowed — and this is a proof, not a preference

`docs/handoff-trproj-weakinv.md` made real progress by splitting one opaque residual into
`VEnv.TypingStrengthening` + `VEnv.ConstAppDefeqStrengthen`, then bounding what was left.  The
brief asked whether `inferProj.WF` can borrow that.  **It cannot, and the obstruction is
structural.**

For **any** proposition `R` whatever,

```lean
theorem inferProj_WF_of_any (R : Prop) (_hR : R) (he …) (hty …) (hasty …) :
    (inferProj st i e ety).WF c s fun ty _ => ∃ e'' ty'', c.TrTyping (.proj st i e) ty e'' ty'' :=
  inferProj_always_throws hty
```

compiles — **without using `_hR`** (checked in scratch, at an abstract `R : Prop`; the unused
binder is what the linter reports).  **[measured]**  So every "reduction of `inferProj.WF` to a
named residual" is a theorem regardless of what the residual says, including residuals that are
false, vacuous, or nonsense.  A split therefore conveys no information about the hole, and no
instrument in the tree (census, hole cone, `#print axioms`) can tell a good residual from a bad one
here.

**Why `weak'_inv` is different, in one sentence:** its statement quantifies over a bare `VEnv` and
a `List VExpr` context and mentions no `VContext`, so its residuals are constrained by concrete
`VEnv`s that the tree can build (`ProjInhab.lean` does exactly that); `inferProj.WF` quantifies
over a `VContext`, which carries `trenv : TrEnv safety env venv`, and that field is what makes
every residual unconstrained today.

**Consequence for scheduling:** partial credit is unavailable on this hole. It goes from
"vacuous" to "false" to "provable" in one step — the `AddInduct` flip plus the widening — with no
intermediate state that any instrument can register.

## 4. What resists once the branch is live, stated as fields  **[measured against source]**

`inferProj` (`Lean4Lean/TypeChecker.lean:233–260`) checks, in order: the whnf'd struct type's head
is `.const I_name I_levels`; `typeName == I_name`; `env.get I_name` is `.inductInfo I_val`;
`I_val.ctors` is a **singleton** `[c]`; `args.size == I_val.numParams + I_val.numIndices`; then it
walks the constructor's telescope instantiating parameters and earlier *used* fields, checking
`isProp dom` on each used binder and on the projected one when `maybePropType`.

`VEnv.IsStructure S D T C` has ten fields.  **Two of them correspond to nothing `inferProj`
checks:**

1. **`types : D.types = [T]`** — the block is a singleton.  `inferProj` reads `I_val.ctors`,
   `numParams`, `numIndices`; it **never reads `I_val.all`**.  So it accepts `.proj` on a member of
   a mutual block.  (Already machine-checked elsewhere for both kernels:
   `MutNonRec.kernelProjChecks`, `Verify/StructureBridge.lean`.)
2. **`noRec : C.recFields = []`** — the projected constructor is non-recursive.  `inferProj`
   **never reads `I_val.isRec`**, and neither does C++ `infer_proj` (`~/lean4/src/kernel/type_checker.cpp`;
   audited, ledger row 99e).  This is `bugs-found.md` item 10, and the executable's acceptance is a
   landed build-time check: `FiringWitness.recProjTest` plus `gateChecks`' two direct calls at
   `inductive FRec where | mk : Nat → FRec → FRec`, which assert `inferProj FRec 0` returns `Nat`
   and `inferProj FRec 1` returns `FRec` and fail the build otherwise.  (These are `#eval`s, not
   theorems — ledger row 104e's caveat applies; `Expr.mkData` is `opaque`.)

Both fields sit in **positive** position from this lemma's point of view: the conclusion asserts
`c.TrTyping (.proj st i e) ty e'' ty''`, which contains `TrExprS (.proj st i e) e''`, whose
`.proj` constructor carries `TrProj`, whose single constructor `TrProj.mk` carries
`env.IsStructure S D T C` (`TrProj.isStructure`, cone 690, hole-free).  **So no restatement of
`inferProj.WF` itself can avoid them** — the existential `∃ e'' ty''` that an earlier round
correctly repaired does not help, because it existentialises the *target*, not the predicate.

Dropping them is the `IsStructureG` widening plus the `TrProj` widening — ledger rows 105a
(wall 3), 107b (wall 2 **gates** wall 3), 107c (it reopens `TrProj.uniq`), 107d (option (d): an
extra field of `TrProj.mk` carrying the target's typing, which relocates wall 2 **onto this
lemma**).  Two things follow that are worth stating plainly:

* **My brief forbids the widening** (`TrProj` must not be widened; if a route needs it, stop and
  report).  This route needs it.  **Reporting and stopping.**
* Even *with* option (d) this lemma does not become provable, it becomes *differently* blocked: the
  eleventh field would be `ProjTermGHasType`, which `inferProj.WF` must then **produce**, and that
  is wall 2 (`projTermG_hasType`) — which does not exist.  Per the top banner of
  `docs/handoff-projections.md`, wall 2's two named prerequisites (`iota_law_gen`, `realMinor_app`)
  are now **closed**, and what is left is one `Nat.strongRecOn` on the field index carrying
  `ProjHasTypeG` and the minor-block spine together (ledger rows 114–114g).  So the honest ordering
  is **wall 2 → widening → flip → this lemma**, and this lemma is *last*, not first.

## 5. Three refutation attempts, and the step each failed at

The brief asks for a machine-checked counterexample if the statement is false.  **It is not false
today** — §1 proves it — so the question is whether its post-flip falsity can be witnessed now.
Three routes, all tried, all dead, with the failing step named:

1. **Direct counterexample.**  Build a `c : VContext` and `ety` with `c.TrExprS ety ety'` whose
   whnf'd head `I_name` has `c.env.find? I_name = some (.inductInfo v)` at a recursive one-ctor
   `v`.  **Failed at the second conjunct**: `TrEnv.not_inductInfo` makes that state of affairs
   contradictory for *every* `VContext`, at every safety level.  There is no counterexample, and
   there cannot be one until `AddInduct` gains constructors.  So the statement is *true*, and its
   falsity is a conditional whose antecedent is another stream's deliverable.
2. **Refute the abstract bridge instead**, over a bare `VEnv` so no `TrEnv` is in the way: state
   "kernel-shaped checks on `S` ⟹ `∃ D T C, env.IsStructure S D T C`" and refute it at an `env`
   containing a recursive single-constructor block.  **Failed at the step "no *other* WF block
   names `S`"**: `IsStructure` existentially quantifies `D T C`, and the predicate deliberately
   carries **no** claim that `S` belongs to at most one block — that is ledger **G4**, and
   `IsStructure`'s own docstring says leaving it out is the point.  Refuting the existential
   therefore needs G4, which has no statement in the tree.  A weaker, *provable* form ("the block
   `addInduct'` actually built for `S` does not satisfy `IsStructure`") is available in principle,
   but needs a `D.WF env₀` witness for a **recursive** block, and no such witness exists in this
   cluster (`decl2`, `decl1r`, `Rich`, `RecDep`, `MutField` all make no `WF` claim by design).
   Not attempted further; costed at a round on its own, and it would establish a *conditional*
   refutation, not a refutation.
3. **Refute a residual.**  §3 kills this outright: any residual is unconstrained, so there is
   nothing to refute — a false residual and a true one are equally sufficient.

**Stated plainly, because it is the sort of thing that gets misquoted:** nothing in this round is
evidence that `inferProj.WF` is true in any useful sense, and nothing in it is evidence it is
false.  What is established is that its *present* truth is unconditional and cheap, that its
*future* falsity is unwitnessable from inside the tree today, and that the gap between the two is
invisible to every instrument this repo has.

## 6. Anti-vacuity, applied to this round's own output

Required by the brief, and it is short because the round adds no statement:

* **No hypothesis was strengthened and no conclusion weakened.**  The only edit to a `.lean` file
  is a docstring paragraph on `inferProj.WF` in `Verify/TypeChecker/InferType.lean` (owned).  No
  declaration was added, changed, or removed; no `#print axioms` output can move, and none did.
* **The census is byte-comparable and unmoved**: TOTAL **13**, `inferProj.WF [70 transitive
  users]`, at both ends of the round.  **[measured]**
* **`TrProj` was not widened**, `Verify/Typing/Lemmas.lean` and `ProjWeakInvSplit.lean` were not
  touched, `Experimental/ConeJoin.lean` was not touched (no new module, so no instrument went
  blind), and no frozen file was read for editing.
* The one-line proof and the arbitrary-residual theorem live **in scratch only** (`/tmp`), by
  choice: landing a second copy of the `sorry`'s statement, proved, would invite exactly the
  deletion §2 argues against, and would make the census row look like an oversight.  The exact
  text of both is in §1 and §3, and re-checking either is a two-minute `lake env lean`.

## 7. What I would pick up first

1. **Nothing on this hole.**  It is last in its own dependency order (§4) and partial credit is
   provably unavailable (§3).  Any round spent here before wall 2 lands produces text, not proof.
2. **Wall 2** (`projTermG_hasType`) — the `Nat.strongRecOn` on the field index carrying
   `ProjHasTypeG` and the minor-block spine together, ledger rows 114–114g.  It is the gate on
   the widening, the widening is the gate on this lemma, and its two named prerequisites are now
   closed, so it is the first thing in the chain that is actually available.
3. **A decision I cannot make and should not pre-empt:** whether `addDecl` should *reject* `.proj`
   at a recursive constructor (item 10's second exit).  If it should, this lemma becomes provable
   without any widening at all — the `noRec` field would then be checked — and the `types` field
   remains, which `IsStructureG` already handles.  That trade is a `divergences.md` entry plus an
   arena run, and it is the only route to this hole that does **not** pass through wall 2.  Worth
   pricing against wall 2 rather than assuming the generalisation is the cheaper exit; nobody has
   priced the two against each other.
4. **Do not re-derive §1.**  The one-line proof is not a discovery to be re-made; it is the reason
   this hole is *not* a proof problem.  A future round that "finds" it and closes it will have
   undone §2 without reading it.

## 8. Relay to the orchestrator

* **The only file edited is `Lean4Lean/Verify/TypeChecker/InferType.lean`** (owned), docstring
  only.  `lake build` 1499 jobs green before and after; the only diagnostic in the file is the
  expected *"declaration uses `sorry`"* at the hole.
* **The decision is yours, and it is a real one**: `sorry`-census 13 → 12 and guard 2's hole set
  9 → 8 are available for the price of one line and one blind spot.  §2 is my argument against;
  the counter-argument (a red build at the flip) is measurably already covered by
  `inferProj_always_throws`.
* **Two of the nine holes are now known to be in qualitatively different states than the census
  suggests.**  `TrProj.weak'_inv` is *hard and split*; `inferProj.WF` is *easy and deliberately
  open*.  A census row is the same width for both, and `docs/critical-path.md` does not
  distinguish them.  If you want one line added to the vacuity ledger from this round, it is that:
  **the census cannot distinguish a hole that resists from a hole that is being held open on
  purpose**, and this round is the second instance (row 99b was the first, for the reverse case —
  a hole reading 0 where the work is).
* `docs/research-proj-reduction.md` §5's safety-uniform lemma is **done and landed** (§1's
  correction); that document's §6.2 recommendation ("do not touch `inferProj.WF`") is otherwise
  confirmed, including its §3a restatement, which a later round applied.
