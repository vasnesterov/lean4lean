# Handoff: `SpineVar` — the variable-headed **spine** entry, and its §7

Round 11 of the `PiDescend` line, finished.  Input: `Theory/Typing/ShapeVar.lean` (the
bare-variable entry) and `docs/handoff-shapevar.md` §9.1, which named the next target — the entry
`varApp i as`, covering the **variable slice of the `.app` row** — and measured one missing
ingredient for it, a `ClosedN`-of-`spineHead` lemma.

Three files:

| file | what it is | status |
| --- | --- | --- |
| `Theory/Typing/SpineVarClosed.lean` | the missing ingredient (`VExpr.ClosedN.spineHead`, `WF.instL_lhs_spineHead_ne_bvar`, `instL_rhs_…`) | hole-free |
| `Theory/Typing/SpineVar.lean` | the entry `RigidShapeVS`, the collapse, the firing test, the row deletion, the price `iff`, §7.1-§7.4 | four theorems carry one hole |
| `Theory/Typing/SpineVarVacuity.lean` | **§7.5-§7.12**, this round's deliverable | four of 29 declarations carry one hole |

`lake build Lean4Lean.Theory.Typing.SpineVar Lean4Lean.Theory.Typing.SpineVarClosed
Lean4Lean.Theory.Typing.SpineVarVacuity` → **109 jobs**, green.

## 0. Why §7 was the deliverable

One day before this round, in this same corner, a draft shape entry was **vacuous** while printing
a clean `[propext]` and measuring an empty hole cone; it was caught only because its author tried
to *refute* his own row instead of proving it.  `SpineVar.lean`'s own §7 (§7.1-§7.4) refutes two
naive readings of the new rows but does **not** contain the check that would have caught that
draft: a witness showing the guarded row's guard leaves anything behind.  §7.5 supplies it.

## 1. Verdict, per requirement

### 1.1 Refutation attempt, per row

The entry adds **four** things: three `Compat` rows and the `RuleFree` entry.

| row | refutation attempt | outcome |
| --- | --- | --- |
| `varApp i as` / `varApp j as'` (diagonal) | naive reading `i = j` | **REFUTED** — `spineVarNoConf_false` (`SpineVar.lean` §7.3), at `VEnv.empty`, spine length 1, hole-free.  Entry is therefore `True`, and `rigidShapeVS_compat_varApp_diag` records that value. |
| `varApp` / `pi` (`SpineVarPiDisj`) | proof irrelevance, δ, β/η | **all three blocked, as theorems** (`forallE_not_isProof`, `spineVar_delta_blocked`, `spineHead_bvar_ne_beta`/`_lam`, assembled as `spineVar_mechanisms_blocked`).  Not refuted.  Residual: `trans` only, and §7.8 says what it is. |
| `varApp` / `sort` (`SpineVarSortDisj`) | same three | **all three blocked** (`sort_not_isProof` + the shared two).  Not refuted.  Residual: `trans`; `spineVarSort_midpoint_aux` spells it out rather than claiming "same proof". |
| `varApp` / `app` (`SpineVarAppDisj`) | proof irrelevance | **REFUTED unguarded** — `spineVarAppDisjNaive_false` (`SpineVar.lean` §7.4), at `svEnv`, spine length 1.  The `¬ IsProof` guard is exactly what buys the row; δ and β/η blocked as above.  Residual: `trans` **plus** the `appDF` spine recursion (see 1.5). |
| `RuleFree (varApp _ _) = True` | is the `True` hiding an assumption about the rule table? | **justified, not assumed**: `rigidShapeVS_varApp_ruleFree_justified` — no rule's instantiated side, lhs or rhs, is a term a `varApp` shape denotes. |

So: **two of the four naive readings fell; none of the four rows as stated did.**

### 1.2 Firing test

Two halves, both machine-checked.

* *The old vocabulary cannot express it.*  `RigidShapeV.toExpr_ne_bvar_app` and
  `RigidShape.toExpr_ne_bvar_app` (`SpineVar.lean` §1): no shape of either older vocabulary denotes
  a variable-headed spine with a non-empty argument list.  Instantiated at the witness in
  `spineVar_row_unexpressible`.
* *The consumer fires.*  `spineVar_row_premises` discharges **six of the seven** premises of the
  row §5 deletes, at `T = .app (.bvar 2) (.bvar 1)` (a **non-empty** variable spine) over
  `VEnv.empty`: the lift `Ctx.LiftN 1 0`, both `OnCtx`s, `PiDescendNeutral`, `f : T`, `a : S`.  The
  seventh premise is the conversion, and `spineVar_row_fires` shows the deletion killing it for
  **every** codomain `B`, given `SpineVarPiDisj`.  One premise named, as a firing test is allowed.
  The same instance satisfies `PiCodLiftNeutralNV`'s guard, so the previous round's residual still
  carried this row — the deletion is proper, not a rename of the `.bvar` row.

### 1.3 Grade: **localisation**, not new strength

`spineVar_grade`, four conjuncts:

1. `RigidShapeVSUniq ↔ RigidShapeUniq ∧ SpineVarPiDisj ∧ SpineVarSortDisj ∧ SpineVarAppDisj`
   (`SpineVar.lean` §6) — the extension **is** the corner's existing shared node plus exactly three
   rows.  Same grading as `ShapeVar.lean`: a **localisation into the shared node**, not a discharge
   and not new strength.
2. `RigidShapeVSUniq → RigidShapeVUniq` — nothing the previous round said is lost.
3. and 4. no `RigidShapeV`, no `RigidShape` denotes a non-empty variable spine.

**Open, and flagged rather than assumed:** whether the three rows follow from `RigidShapeUniq`
alone.  If they did, the extension would be a **rename**, not a localisation.  Conjuncts 3/4 make
that look unlikely (the rows are not *expressible* downstairs), but expressibility is not
derivability and nothing here settles it.  This is the one grading question I could not close.

Caveat on the `iff`: its `←` direction takes `htr : env.ProofTransport U` as a hypothesis, so the
price tag is exact modulo that node (whose only in-tree inhabitant, `WF.proofTransport`, is
tainted).

### 1.4 Midpoint: **no** — and this time with a term, not a read-off

The mandatory question (ledger rows 94/94a, 100-103; eleven collapses).  `SpineVar.lean` answers it
by reading off the definitions.  Two additions here:

* `spineVar_midpoint_unconstrained`: `spRedex = (λ x : Prop, x) (f a)` is a **β-redex** convertible
  to the `varApp 2 [.bvar 1]` endpoint at `VEnv.empty`, with every premise of the bridge that
  mentions the midpoint satisfied (`OnCtx`, `¬ IsProof`, `RuleFree`, the conversion at a common
  type), and its spine head is a `.lam`.  So the ledger's mechanism is *exhibited*: a midpoint of
  redex shape is available at a `varApp` endpoint, therefore no syntactic condition on the midpoint
  could have survived — and the entry imposes none.  **Not the twelfth collapse.**
* `spineVarPi_midpoint` / `spineVarPi_midpoint_aux` (and the sort sibling) do mention a midpoint,
  and the distinction matters: they **derive** properties of an existentially quantified midpoint
  from a hypothetical counterexample (it is neither variable-spine-headed nor a Π), they do not
  **impose** a condition on one.  The shape they leave open is exactly the redex shape β
  manufactures, which is why they are consistent with the eleven collapses by construction.

### 1.5 Where the app row really is harder

Recorded because "the same induction works" is how an unchecked row gets committed: for the Π and
sort rows every `IsDefEqStrong` case but `trans` closes outright.  For the app row `appDF` does
**not** — both endpoints are applications there — and it closes only by peeling one argument off
each spine and threading `¬ IsProof` down with `IsProof.app'`
(`not_isProof_fun_of_not_isProof_app` isolates that step; `forallE_sort_ne_app` and
`mkApp_cons_eq_app` show why `appDF` is vacuous for the other two rows and reachable for this one).
`ShapeVar.lean`'s bare-variable row escaped `appDF` entirely.

### 1.6 Inhabitation and hole-freeness — stated separately

**Inhabitation.**  Every witness is a typed term in an `OnCtx` context at a `VEnv.WF` environment:
`spineVar_hasType_prop`/`spineVar_isType` (the non-empty variable spine is a type),
`spineVar_row_premises` (six premises of the deleted row), `spRedex_conv` (the redex midpoint),
`spDiagCtx_conv`/`spAppCtx_conv` (the two refutations).  `spineVar_guard_not_vacuous` is the
load-bearing one: without a **non-proof** non-empty variable spine the guard would exclude the
entire slice the entry adds and the entry would be `ShapeVar.lean`'s under a new name.

**Hole-freeness.**  Measured, both by `#print axioms` (audit blocks in all three files) and by cone.
`SpineVarVacuity.lean`: **exactly four** declarations carry `sorryAx`.  That count is from the
compiled environment, not from reading the audit lines — a scan of every constant whose defining
module is `Lean4Lean.Theory.Typing.SpineVarVacuity` (69 public `Lean4Lean.VEnv.*` constants,
36 hand-written `theorem`/`def`) reports exactly these four and no others.  They are
`spineVar_not_isProof` (via `IsType.not_isProof`), `spineVarPi_midpoint` (via `IsDefEq.strong`),
`not_isProof_fun_of_not_isProof_app` (via `IsProof.app'`) and `spineVar_grade` (via §6's `iff`).
All four reach the same single hole, `IsDefEqU.forallE_inv_stratified`; `WF.rigidShapeUniqNS` is in
**none** of them, and `IsDefEqU.weakN_iff` in none either.

Cones (`/tmp/spinevar-cone.lean`, the `hole-cone.lean` instrument re-seeded; `allowOpaque := true`):

| seed | cone | holes in cone |
| --- | --- | --- |
| `spineVar_not_isProof_of_propAgreeOn` | 639 | none |
| `spDiagCtx_isProof_of_conv` | 638 | none |
| `spineVar_row_fires` | 642 | none |
| `spineVar_guard_not_vacuous` | 658 | none |
| `spineVar_midpoint_unconstrained` | 672 | none |
| `spAppCtx_no_bridge_instance` | 800 | none |
| `spineVar_mechanisms_blocked` | 3390 | none |
| `spineVarPi_midpoint_aux`, `spineVarSort_midpoint_aux` | 3468 | **none** |
| `spineVar_not_isProof` | 3464 | `forallE_inv_stratified` |
| `spineVarPi_midpoint` | 3560 | `forallE_inv_stratified` |
| `rigidShapeVSUniq_iff` | 3705 | `forallE_inv_stratified` |
| `spineVar_grade` | 3716 | `forallE_inv_stratified` |
| `piDescend_iff_neutralNVS_sortConv` | 3735 | `forallE_inv_stratified`, `WF.rigidShapeUniqNS` |

**Hole-freeness is not discharge.**  The extended bridge `RigidShapeVSUniq` is a **hypothesis**
wherever it appears, and a hypothesis is invisible to both `#print axioms` and the cone
(`docs/vacuity-ledger.md` §0, third instrument).  Two of the four tainted results have hole-free
doubles here — `spineVar_not_isProof_of_propAgreeOn` and `spineVarPi_midpoint_aux`.  Getting the
second of those hole-free was **not** free: the first draft used `WF.sortUniq' henv` in the
`proofIrrel` case, printed `sorryAx`, and only hypothesising `SortUniq` removed it.  The docstring
that claimed hole-freeness was written *before* the measurement and was wrong; it was corrected
after.  That is the one place in this round where a claim and a measurement disagreed.

### 1.7 Witness environments (requirement 5), machine-checked

`spineVar_witness_envs`: `VEnv.empty` declares no constant and no rule; `svEnv`'s constant table is
the **single** entry `svC ↦ ⟨0, ∀ X : Prop, X⟩` and nothing else, and it has no rules.
`svEnv_every_prop_inhabited` and `svEnv_false_inhabited` prove `svEnv` **inconsistent** (every
proposition of every context is inhabited; the closed proposition `∀ X : Prop, X` is inhabited in
the empty context) — a theorem, not a docstring assertion.  An inconsistent `VEnv.WF` environment is
a legitimate *refutation* witness (the rows quantify over all `VEnv.WF` environments) and is used
here only under `¬` or in a premise-failure statement.

§7.3's refutation lives in a context that assumes `∀ X : Prop, X` twice, but over `VEnv.empty`:
that is a **context hypothesis**, not an axiom, so the *environment* there is consistent.

## 2. Where the brief was wrong

1. **`univInhab` is not used in this corner.**  The brief asks me to disclose that "one witness
   environment used in this corner declares `univInhab : ∀ (α : Sort u), α` and is therefore
   inconsistent".  No witness in `SpineVarVacuity.lean`, `SpineVar.lean` or `ShapeVar.lean` does.
   The two witness environments are `VEnv.empty` and `svEnv`, and `spineVar_witness_envs` pins
   `svEnv`'s constant table to its one **propositional** axiom, so this is a checked absence and not
   a grep (`docs/handoff-shapevar.md` §192 makes the same claim in prose; it is correct).
   `univInhab` belongs to the weakening/strengthening stream (`docs/handoff-weakn.md`,
   `docs/handoff-gatebody.md`, `docs/handoff-trproj-weakinv.md`).  The disclosure that *is* owed
   here is a different one, and it is now a theorem: `svEnv` is inconsistent for a Prop-level
   reason.
2. **"§7 is missing" was half true.**  The crashed stream did write a §7 (§7.1-§7.4) and it builds;
   what was missing was (a) the non-proof witness, without which the entry is a rename, (b) any
   per-row refutation record for the Π and sort rows, (c) a consumer-side firing test with premises
   discharged, and (d) the every-midpoint form of the two hard-constraint checks.  Committing
   §7.1-§7.4 alone would not have committed a vacuous row, but it would have committed an
   **unmeasured guard** — the exact shape of the earlier incident.
3. **The brief's "13 holes, `NOT BUILT`" expectation is met but the `NOT BUILT` list is not empty**:
   `Lean4Lean.Theory.Inductive.CtorBeta` and `Lean4Lean.Theory.Inductive.CtorBetaScan` are on disk,
   in a default target, with **no `.olean`** — a concurrent stream's files (`CtorBeta*`), not mine.
   `lake build` of my modules is green regardless, which is precisely the blindness the census
   exists to catch.  Someone should tell that stream.

## 3. Measurements

* `lake build` (my three modules): **109 jobs**, green.
* `lake env lean --run scripts/sorry-census-all.lean`: **13 holes** over the whole built
  population (pass A 13, pass B 0) — unchanged, this round adds none.  `BUILT: 386; NOT BUILT: 2`
  (`Theory.Inductive.CtorBeta`, `Theory.Inductive.CtorBetaScan`).  `SpineVarVacuity` appears in the
  **ORPHAN** list (32 modules), as a leaf file with no importer should.
* Layering: `grep -rln "^import Lean4Lean.Verify" Lean4Lean/Theory/` → empty.
* Frozen files untouched: `Verify/Soundness.lean`, `Verify/Axioms.lean`, `Verify/Guard.lean` were
  not read for edit, not edited, not `touch`ed.
* `Injectivity.lean` / `InjOneFact.lean` (the files defining `RigidShape` / `SPShape`) untouched;
  the in-place edit is stated and not made — `SpineVar.lean` §9, unchanged by this round.

## 4. What to pick up first

1. **The independence question in 1.3.**  Do `SpineVarPiDisj`/`SortDisj`/`AppDisj` follow from
   `RigidShapeUniq`?  A `VEnv.WF` environment satisfying `RigidShapeUniq` and violating one of the
   three rows would settle it and would downgrade nothing — it would *upgrade* the entry from
   localisation to genuine strength.  Conversely a derivation would show this round is a rename.
   This is the highest-value open item and it is cheap to state.
2. **The app row's `appDF` recursion** is the only place in the family where the induction is not
   structural in the derivation (it recurses on the spine).  Worth a second pair of eyes before the
   in-place edit of `RigidShape` is ever sequenced.
3. **`PropAgreeOn` has no unconditional instance.**  Measured over the compiled environment, not
   grepped: in the import closure of `SortInvIndep` + `PropAgreeGuarded` + `ForallInvPrice` +
   `PiInvResidual` + `AppUniqRefute` + `SortPiDisjPrice` + `SpineVarVacuity`, **exactly two**
   constants have `PropAgreeOn` as their conclusion — `propAgreeOn_of_stratifiedNOn` and
   `propAgreeOn_of_stratifiedN` — and both carry hypotheses (four binders each, none of them a
   `PropAgreeOn`).  So §7.5's hole-free route rests on a node nobody has discharged at *any*
   environment, `VEnv.empty` included.  The nearest unconditional relative, found while checking
   this, is `SetModel/PropAgreeWall.preludeEnv_propTypeAgreeOnCtx` — no hypotheses, but at a
   *specific* environment (`preludeEnv`, not `VEnv.empty`), it is `PropTypeAgreeOnCtx` rather than
   `PropAgreeOn`, and its axioms are `[propext, sorryAx, Classical.choice, Quot.sound]`, i.e. it
   reaches the same hole.  There is therefore **no** hole-free unconditional route to `PropAgreeOn`
   in the tree today.  Discharging it at `VEnv.empty` alone would make this corner's whole
   anti-vacuity apparatus unconditional and looks much easier than the general case.
4. `spineVarSort_midpoint_aux` exists; the **app** row has no midpoint-residual statement, because
   its residual is `trans` + the spine recursion.  If someone wants the full residual map, that is
   the missing third.
