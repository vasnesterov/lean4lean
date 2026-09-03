# Handoff: round 8 on the forward direction of `VEnv.IsDefEqU.weakN_iff`

**Target:** the `sorry` at `Lean4Lean/Theory/Typing/UniqueTyping.lean:193`.
**Verdict: not closed, not refuted.**  Nothing in this round removes a `sorry`.
*"No witness is not evidence of truth."*

Marks as in `docs/handoff-weakn.md`: **[machine-checked]** = a named `sorry`-free declaration in
this tree; **[measured]** = a run reproduced here; **[read]** = read off source;
**[analysis]** = neither.

Files this round owns: `Lean4Lean/Theory/Typing/WeakNForward.lean` (new) and this document.
Nothing else was edited.

## Verdict in five lines

1. The obligation **is** `VEnv.StrengtheningTarget env U`, unfolded and machine-checked (§1).
2. `henv : VEnv.WF env` is **not load-bearing** in the forward half, and is over-strong for the
   reverse half too (`Ordered` suffices) (§2).
3. `IsDefEqU.weakN_iff` has **13 direct / 351 transitive** users, and **all 13 need the forward
   direction**; **0** need only the reverse.  Splitting the `iff` is not a route (§3).
4. **New result:** `StrengthenFamily.lean` §8's informal claim that `Sort (.param i)` has no
   closed inhabitant is **FALSE** — machine-checked refutation, plus the fourth discharge clause
   that closes its residue in any environment declaring a `Sort u`-valued constant (§4).
5. Two edits proposed, both to `Verify/Inductive/StrengthenFamily.lean`; **none** to
   `UniqueTyping.lean:193` (§5).

---

## 0. Routes enumerated as ruled out BEFORE starting (so it is on the record)

From `docs/handoff-weakn.md` §6, §8, §5.5, §6.6, §A.5, §7.8 and
`StrengthenNarrow.lean`'s module docstring.  **None was reattempted.**

| route | why it is closed |
|---|---|
| direct induction on `IsDefEqU` | `trans` **is** the statement (`Strengthening.iff_trans`) |
| the typed form `TypedStrengthening` | inter-derivable (`Strengthening.iff_typed`) |
| a propagated / chain restatement | makes `trans` free, coherence clause's base case is the target |
| Church–Rosser, `NormalEq` | circular through `ParRed.weakN_inv`; `ParRedKWeakN.lean` §1 proves that entry *is* the hole restated |
| `HeadReduction.lean` | its only conversion⟹reduction bridges are `church_rosser` calls |
| set model, **proof** direction | vacuous over an uninhabited entry |
| set model, **refutation** direction | conditional — on `PropDescend` (§A.1), now on `InstDescendUp` (§S) |
| `VExpr.Skips` / `IsDefEq.skips` | downstream of the hole |
| the λ-form | needs `IsDefEqU.forallE_inv`, `sorryAx`-tainted through `rigidShapeUniqNS` |
| `Stratified` (`⊢ₙ`) | still has `trans` with an arbitrary middle term at `n+1` |
| junk **environment** via an open constant type | collapses at its own witness (`constOpenType_collapse`) |
| junk **context** | `Ctx.LiftN` + `OnCtx Γ'` forces the descent to be `SortDescend`, part of the hole |
| any existing `⊬` instrument | all 31 are head-shape facts, all lift-stable, so each kills **both** sides of the `iff` |
| identity-function encoding at term level | `sortConv_encoding_vacuous` |
| re-deriving the nine/ten typing gates | `StrengthenNarrow.lean` §5 has them |
| "reduce it to `TransStrengthening`" | tautology (§9/§5.1) |
| expecting `PiDescend` to unblock the tree | 46 of 296 / 59 of 319 |

---

## 1. The obligation, honestly (task (a))

`Lean4Lean/Theory/Typing/WeakNForward.lean` §1.  Unfolding `IsDefEqU` (an `∃` over `IsDefEq`),
`IsType` (an `∃` over `HasType` at a sort) and `OnCtx` (a `List.rec`) turns the goal at
`UniqueTyping.lean:193` into

```
WeakNForwardRaw env U :=
  ∀ {n k} {Γ Γ' e1 e2 A}, Ctx.LiftN n k Γ Γ' →
    OnCtx Γ' (fun Δ B => ∃ u, env.IsDefEq U Δ B B (.sort u)) →
    env.IsDefEq U Γ' (e1.liftN n k) (e2.liftN n k) A →
    ∃ B, env.IsDefEq U Γ e1 e2 B
```

and `weakNForwardRaw_iff_target` **[machine-checked]** shows this is the tree's
`VEnv.StrengtheningTarget` on the nose — so the unfolding smuggles nothing in and loses nothing.
Note what the unfolding makes visible and the `IsDefEqU` wrapper hides:

* the antecedent's type `A` may be taken as **given** (skolemised out of the `∃`), while the
  conclusion's `B` must be **produced** — the two are unrelated, and the tree's own
  `TypedStrengthening` (where `A`'s lift is the conclusion's type) is a *different* statement
  that happens to be inter-derivable;
* the environment appears **only** through `env.IsDefEq` — there is no `WF`, `Ordered` or
  `Closed` hypothesis anywhere in the obligation. `Ctx.LiftN` is pure syntax.

## 2. Which hypotheses are load-bearing — measured, not guessed (task (a))

The stub is `fun h => have := henv; have := hΓ; sorry`, i.e. nobody had established either.

**`henv : VEnv.WF env` is NOT load-bearing in the forward half.**  `StrengtheningTarget env U`
carries no environment hypothesis and discharges the forward direction verbatim
(`weakN_iff_forward_of_target` **[machine-checked]**).  So the `have := henv` is not a hint: this
half cannot consume an environment hypothesis unless the proof first passes to one of the
*equivalent* forms that carry one (`Strengthening`, `TransStrengthening`, `Strengthening1`,
`AxiomConservativityWF`, …), and `Strengthening.iff_target` shows `henv` is needed there only for
`OnCtx.weakN_inv`.

**`henv` is over-strong for the reverse half too.**  `IsDefEqU.weakN`
(`Theory/Typing/Lemmas.lean:576`) is stated at `Ordered env`, which `VEnv.WF env` strictly
implies.  `weakN_iff_of_target_ordered` **[machine-checked]** is the whole `iff` with `henv`
weakened to `Ordered env`, modulo the open half.  (Not proposed as an edit: the signature change
would touch every one of the 855 syntactic references.)

**`hΓ : OnCtx Γ' (env.IsType U)` is a premise of the obligation, and I could not measure it.**
The honest report: `lean_minimal_hypotheses` cannot answer this, because the theorem's body is
`sorry` and a `sorry` body needs no hypothesis, so the tool reports *everything* unused —
this is a measurement instrument that does not apply to an open theorem, and any claim derived
from running it here would be an artefact.  What can be said:

* deleting `hΓ` gives a strictly stronger statement (`WeakNForwardUnguarded`,
  `StrengtheningTarget.of_unguarded` **[machine-checked]** is the free direction).  The tree
  already names the `Lift'`/`HasType` form of it — `VEnv.UnguardedStrengthen`,
  `SetModel/InstDescendBvar.lean:443` — and records it as **strictly stronger than this hole and
  not one of the four big holes** [read].
* whether `hΓ` is *necessary* (i.e. whether the unguarded form is false) is **itself gated on
  the hole**: a junk `Γ'` separating the two contexts must make some `X` a type upstairs and not
  downstairs, and that is `SortDescend`, a component of the hole (`docs/handoff-weakn.md` §A.5's
  junk-context row, re-derived here **[analysis]**).  So this is not a cheap measurement and I
  did not fake one.

Vacuity control: `weakNForward_vacuous_at_zero` **[machine-checked]** — at `n = 0` the conclusion
*is* the hypothesis, so all content lives at `n ≥ 1`.

---

## 3. Consumer census — which direction each user needs (task (iii))

Instrument: `getUsedConstantsAsSet` over type **and** value with `allowOpaque := true`, internal
names kept as graph nodes (the trap of `handoff-weakn.md` §5.3/§7.1), over the closure
`Verify.Guard` + `Experimental.ConeJoin` + `Theory.Typing.StrengthenNarrow` +
`Verify.Typing.ProjGenTerm` + `Verify.TypeChecker.ProjGenTermWitness` +
`Verify.Typing.ProjWeakInvSplit`.  Script at `/tmp/wnf/direct.lean`, reproduced in §7.

**`IsDefEqU.weakN_iff` has 13 direct users** **[measured, 2026-09-03]** — one more than
`ParRedKWeakN.lean`'s recorded 12 (`typingStrengthening_of_weakN_iff`, `CRPiDescend.lean:352`,
has been added since):

| direct user | module | call sites | direction used |
|---|---|---|---|
| `VEnv.parRedK_weakN_invP` | `Theory.Typing.KMeasure` | `:822` | **forward** (`.1`) |
| `VEnv.parRedK_weakN_invPS` | `Theory.Typing.KMeasure` | `:1077` | **forward** |
| `VEnv.NormalEq.weakN_inv_DFC` | `Theory.Typing.ChurchRosser` | `:492,517,552,570,581` | **forward** |
| `VEnv.ParRedExt.parRed_beta` | `Theory.Typing.ChurchRosser` | `:995` | **forward** |
| `VEnv.hasType_app_bvar0` | `Theory.Typing.ChurchRosser` | `:1347` | **forward** |
| `VEnv.ParRed.weakN_inv` | `Theory.Typing.ChurchRosser` | `:1407,1467` | **forward** |
| `VEnv.KTable.kstep_liftN_inv_stepP` | `Theory.Typing.KCanonical` | `:372,389` | **forward** |
| `ConditionallyWHNF.weakN_inv` | `Verify.Typing.ConditionallyTyped` | `:126` | **forward** |
| `VEnv.typingStrengthening_of_weakN_iff` | `Theory.Typing.CRPiDescend` | `:352` | **forward** |
| `VEnv.IsDefEq.skips` | `Theory.Typing.UniqueTyping` | `:205` | **forward** |
| `VEnv.IsDefEq.weakN_iff'` | `Theory.Typing.UniqueTyping` | `:212,214` | **forward** (twice) |
| `VExpr.WF.weakN_iff` | `Theory.Typing.UniqueTyping` | `:197` | whole `iff` (passthrough) |
| `VEnv.IsDefEqU.weak'_iff` | `Theory.Typing.UniqueTyping` | `:260` | whole `iff` (inside `rw`) |

**Result: 0 of the 13 need only the reverse direction; 11 apply `.1` and nothing else.**
**[measured]**  The two `iff`-consuming rows do not change this:

* the reverse *content* is separately available and hole-free — `IsDefEqU.weakN`
  (`Theory/Typing/Lemmas.lean:576`, cone 1079, no `sorryAx`) and `IsDefEqU.weak'` (cone 1109)
  **[measured]** — so nobody has ever needed to route a weakening through this `iff`;
* a grep over all of `Lean4Lean/` for `.2` / `.mpr` / reverse-`rw` on `weakN_iff` or `weak'_iff`
  finds **no** application in the whole tree outside `Experimental/`, and the two
  `Experimental/` hits (`NormalEq.lean:109,111`, `ParallelReduction.lean:668,671,675,682,899`)
  apply `.2` to a *different* object — the abstract typing-interface field
  `TY.isDefEq_weakN_iff`, not this theorem **[measured]**.

**Consequence, stated plainly: splitting the `iff` into a proved reverse half and an open forward
half buys nothing, because the reverse half is already available elsewhere and nobody consumes it
here.**  So fallback (iii)'s optimistic outcome — "the forward direction is needed at only a few
instances" — is **false at the direct-user level**: it is needed at all 13.

**Fresh totals, re-measured today with `scripts/users.lean`** (a reverse-dependency instrument
another stream added mid-round; population 420 built modules, 25 791 non-internal `Lean4Lean`
declarations) **[measured, 2026-09-03]**:

```
Lean4Lean.VEnv.IsDefEqU.weakN_iff
  DIRECT     13 declarations in 6 modules
  TRANSITIVE 351 declarations in 61 modules
```

The `13` is an independent confirmation of the table above (my own walker and `users.lean` agree).
The transitive figure has moved again — 111 → 124 → 296 → 319 → **351** across rounds — and every
earlier number was measured over a smaller import closure, so treat **351** as the current one and
do not re-quote the older ones as if they were the same measurement.

What *is* true, and is round 5/7's finding rather than mine, is that the **typing** wrappers are
the cheaper half: cutting the ten typing gates leaves 250 of 296 (at `d67375b`) / 260 of 319 (in
round 7's larger closure) transitive users still reaching the hole [read, `handoff-weakn.md`
§5.3, §7.1].  I did **not** re-measure the *split* — `users.lean` has no cut-set mode and my own
per-node walk with cuts did not finish inside this round's budget — so the split is quoted as
**[read]**, and only the 13/351 totals are **[measured]**.

---

## 4. The `Sort (.param i)` residue: the informal claim is FALSE, and the residue closes anyway

This is the round's substantive result.  It is not about the hole itself; it is about the
**bypass** that a sibling stream built around it.

`Verify/Inductive/StrengthenFamily.lean` §8 discharges the nested restriction step without the
hole, conditional on `VInductDecl'.ResultSortInhab` — an inhabitant of `Sort D.lvl` over each
member's telescope — and three clauses discharge that (`resultSortInhab_of_succ`, `_of_zero`,
`_of_lookup`).  The residue it records is a block whose `D.lvl` is neither `≈ .succ _` nor
`≈ .zero` and which has **no binder at that level** — a closed `inductive T : Sort u`, whose
telescope is empty.  For that case the file says, explicitly marked *informal and not
machine-checked* [read, `StrengthenFamily.lean:574-580`]:

> a closed inhabitant of `Sort D.lvl` would have to be a `.sort` (forcing `D.lvl ≈ .succ _`) or a
> `.forallE` (forcing `D.lvl ≈ .imax _ _`), so one expects no closed inhabitant to exist

**That claim is false.**  The case analysis omits `.const` (and `.app`).  `IsDefEq.constDF` types
`.const c ls` at `ci.type.instL ls`, so a constant declared at `Sort (.param 0)` with one universe
parameter is a closed inhabitant of `Sort l` for **every** level `l`, in **every** context, by one
rule application and with no environment hypothesis at all.

Machine-checked, in `Lean4Lean/Theory/Typing/WeakNForward.lean` §4 (all cones `sorryAx`-free and
`weakN_iff`-free **[measured]**):

| name | statement | cone | axioms |
|---|---|---|---|
| `hasType_const_sort` | `env.constants c = some ⟨n, .sort l⟩ → … → Γ ⊢ .const c ls : .sort (l.inst ls)` | 647 | `propext, Quot.sound` |
| `hasType_const_sortParam` | the `⟨1, .sort (.param 0)⟩` case: `Γ ⊢ .const c [l'] : .sort l'` for **every** WF `l'` | 728 | `propext, Quot.sound` |
| `sortInhab_of_const` | **the missing fourth discharge clause**: every WF level's sort is inhabited over every context | 729 | `propext, Quot.sound` |
| `sortWitCV`, `sortWitCV_wf` | `sortWit.{u} : Sort u` as a `VConstVal`, and its `VConstant.WF` | 19 / 595 | — / `propext` |
| `exists_sortWitEnv` | **a `VEnv.WF` environment declaring it** — one `VDecl.WF.axiom` step, no `unsafeDef`, so not inconsistent by construction | 765 | `propext, Quot.sound` |
| `not_forall_sort_param_uninhabited` | **THE REFUTATION**: `¬ ∀ env U i, VEnv.WF env → (VLevel.param i).WF U → ¬ ∃ e, [] ⊢ e : .sort (.param i)` | 888 | `propext, Quot.sound` |
| `sortWit_head_is_const` | negative control (a): the witness is neither a `.sort` nor a `.forallE` — exactly the omitted head shape | 64 | none |
| `param_zero_not_succ_not_zero` | negative control (b): `.param 0` is `≈` no successor and `≉ imax 1 0`, so the instance really is in the residue | 674 | `propext, Quot.sound` |

**Direction of the consequence.**  The residue does not need §8's normal-form argument
machine-checked; it needs the *opposite* fact, and that fact is now proved.  `sortInhab_of_const`
subsumes all three existing clauses: in an environment declaring one `Sort u`-valued constant it
discharges `ResultSortInhab` at **every** well-formed `D.lvl`, successor, zero, `.param i` or
`.imax`, and over every telescope (it is context-uniform, so the same term works at each member).

**The one condition, stated honestly.**  `sortInhab_of_const` needs the environment to declare
such a constant.  The standard prelude has one — `PUnit.{u} : Sort u`, whose `VConstant` is
`⟨1, .sort (.param 0)⟩` **[analysis: read off Lean's own signature, not verified against this
tree's translation of `PUnit`]** — and nested inductive declarations appear far later than
`PUnit` in any real environment.  Whether the specific environment at the restriction step
(`e₂` / `e₁` in `RestrictStepCfg`) declares it is a question inside `Verify/Inductive/`, which is
not this stream's to answer.  Using a *companion* constant of the block itself would be
self-defeating (the junk value must be `NoCSubst σ`), so the witness has to be a
previously-declared constant.

**Anti-vacuity, both ways** (working rule 5):
* the hypothesis is satisfiable at a `VEnv.WF` environment (`exists_sortWitEnv`), and unlike
  `StrengthenVerdict.lean`'s `univInhab` witness the declaration is a plain `.axiom`, not
  `.unsafeDef` — so this witness is *not* inconsistent by construction;
* the conclusion is not trivially true: `param_zero_not_succ_not_zero` shows the level is in the
  residue proper, and `sortWit_head_is_const` shows the inhabitant is the head shape the informal
  argument ruled out, so the refutation is not an artefact of a degenerate instance.

**What this does not claim.**  It does not close the restriction step (that is
`StrengthenFamily.lean`'s theorem, conditional on `ResultSortInhab`); it does not touch the
strengthening hole; and it says nothing about whether `Sort (.param i)` is inhabited in an
environment *without* such a constant — for `VEnv.empty` the question is open here and the
normal-form argument may well be right there.  The refutation is of the claim **as stated**
(quantified over well-formed environments), which is how §8 states it and how the residue would
have to use it.

---

## 5. Edits proposed — and the one that is deliberately *not* proposed

### 5.1 `Theory/Typing/UniqueTyping.lean:193` — **no edit proposed**

Task (c) asks for the exact one-line replacement of the `sorry` *if it is closed*.  It is not
closed, so there is nothing to replace it with, and I am not proposing a cosmetic churn.  Two
things about that line, for whoever does close it:

* the shape the edit will take is
  `refine ⟨fun h => <name> W hΓ h, fun h => h.weakN henv W⟩` where `<name> :
  VEnv.StrengtheningTarget env U` — §1 above proves this is the whole obligation, so no
  reformulation is needed at the call site;
* the `have := henv; have := hΓ` in the current stub is **not** a hint about the proof.  It is
  there because `variable!` expands to `include henv hΓ in`, and without a mention of both the
  `linter.unusedSectionVars` linter fires.  §2 shows `henv` cannot be consumed by this half at
  all.  Do not read it as "both hypotheses are needed here".

### 5.2 `Verify/Inductive/StrengthenFamily.lean` — **edit proposed** (not this stream's file)

Two changes, both consequences of §4.

**(i) Correct §8's informal paragraph.**  The sentence

> a closed inhabitant of `Sort D.lvl` would have to be a `.sort` (forcing `D.lvl ≈ .succ _`) or a
> `.forallE` (forcing `D.lvl ≈ .imax _ _`), so one expects no closed inhabitant to exist

is **false as stated** and should be deleted or replaced by a pointer to
`VEnv.not_forall_sort_param_uninhabited` (`Theory/Typing/WeakNForward.lean` §4.3).  The case
analysis omits `.const`.  Leaving it in place risks a successor spending a round trying to
machine-check a false claim — which is precisely what this round was told to consider doing.

**(ii) Add the fourth discharge clause**, beside `resultSortInhab_of_succ` / `_of_zero` /
`_of_lookup` in §4a.  Verbatim, using `Theory/Typing/WeakNForward.lean`'s
`VEnv.hasType_const_sortParam`:

```lean
/-- **The level-arbitrary case**: any previously declared `Sort u`-valued constant is a witness,
at every `D.lvl`.  This covers the `.param i` residue, closed blocks included. -/
theorem VInductDecl'.resultSortInhab_of_const {env : VEnv} {D : VInductDecl'} {c : Name}
    (hc : env.constants c = some ⟨1, .sort (.param 0)⟩) (hlv : D.lvl.WF D.uvars) :
    D.ResultSortInhab env fun _ => .const c [D.lvl] :=
  fun _ _ => VEnv.hasType_const_sortParam hc hlv
```

That requires `StrengthenFamily.lean` to import `Theory/Typing/WeakNForward.lean` (a `Theory/`
module, so the direction is correct — unlike round 7's `WeakNProjSwap.lean`).  Alternatively
inline the three-line `constDF` proof and drop the import; the content is
`IsDefEq.constDF` plus `simpa [VEnv.HasType, VExpr.instL, VLevel.inst]`.

With (ii) in place, `VIndRestore.argsTypedK_of_resultSortInhab` fires at **every** well-formed
`D.lvl` in any environment declaring such a constant — the residue is gone, subject to the one
condition in §4 (that the environment at the restriction step does declare one).

---

## 6. What I did not do, and the precise reason

* **The hole is not closed.**  I did not attempt a route outside §0's ruled-out list, because
  after seven recorded rounds there is no untried route that fits a single round: the two the
  handoff names as live are (a) `const_app_inv` for a well-typed redex *without* confluence, which
  would break the `ParRed.weakN_inv` cycle and, with round 6's `NormalEqComplete` reduction, leave
  only `PiDescend` — that is an injectivity-stream program, not a strengthening one; and (b) the
  `noUnsafe` restructuring of §A.6.3, which is a flag day across the consumers.
* **The hole is not refuted.**  I did not build a counterexample.  The one shape I priced fresh —
  a non-`VEnv.WF` environment with an **open defeq** (`⟨0, .sort .zero, .bvar 0, .sort 1⟩`), which
  makes `.bvar 0` a proposition upstairs where `Lookup` is available and not downstairs, firing
  `proofIrrel` on two closed constants only in the larger context — is a genuinely *new* shape
  (§1 of `handoff-weakn.md` rules out `extra` for **WF** environments only, and §2's dead witness
  used an open *constant type*, not an open *defeq*).  I did not pursue it because the negative
  half, `[] ⊬ c₁ ≡ c₂` at that environment, needs a non-derivability argument built from scratch:
  the tree's 31 `⊬` instruments all carry `Ordered`/`WF`/rigidity hypotheses that this environment
  fails by construction, and `proofIrrel` blocks the obvious set-valued model.  **[analysis]**
  Recorded as a live lead rather than a result: it would refute the *`henv`-free* statement only,
  i.e. it would show `henv` load-bearing (§2's open question), not refute the hole.
* **`lean_minimal_hypotheses` was not used** on the hole or a restatement of it.  Reason in §2: it
  drops a hypothesis and re-elaborates, and a `sorry` body needs no hypothesis, so on an open
  theorem it reports every hypothesis unused.  Running it here would have produced a
  measurement-shaped artefact, which is worse than saying so.
* **The 296/250/46 and 319/260/59 *splits* were not re-measured.**  The per-node
  reverse-reachability walk *with a cut set* over 25 791 `Lean4Lean` nodes did not finish inside
  this round's budget, and `scripts/users.lean` (which did finish, and gave 13 direct / 351
  transitive) has no cut-set mode.  The direct-user census (§3), which is what the brief asked
  for, did finish.  **If someone wants the split re-measured, add a cut-set option to
  `scripts/users.lean`'s reverse graph** — a single reverse walk is cheap where 25 791 forward
  cones are not, and that is why my instrument was the slow one.
* **`scripts/sorry-census.lean` was not run.**  It walks the whole default target and the tree is
  not fully built (`Verify/Environment/Boundaries.olean` missing, another stream in flight) —
  the same class of failure round 7 recorded.  What is measured instead: the new module contains
  no `sorry` token, and none of its 16 declarations' cones contains `sorryAx` or
  `IsDefEqU.weakN_iff` (§4's table and §7's script).  **Axiom bar: `after ⊆ before` holds
  trivially — the module adds no axiom beyond `propext`/`Quot.sound`, both already in the
  whitelist.**
* `scripts/dup-names.lean` with `Theory.Typing.WeakNForward` added to the joined cone: **no
  duplicate `Lean4Lean` declarations** **[measured]**.
* `lake build Lean4Lean.Theory.Typing.WeakNForward`: green, **zero warnings** **[measured]**.

---

## 7. Instruments (kept here; `scripts/` is not this stream's)

Direct-user census — note `n.isInternal` is filtered only when *reporting*, never when building
the graph (`handoff-weakn.md` §5.3's bug, met in three instruments so far):

```lean
import Lean4Lean.Verify.Guard
import Lean4Lean.Experimental.ConeJoin
import Lean4Lean.Theory.Typing.StrengthenNarrow
import Lean4Lean.Verify.Typing.ProjGenTerm
import Lean4Lean.Verify.TypeChecker.ProjGenTermWitness
import Lean4Lean.Verify.Typing.ProjWeakInvSplit
open Lean Elab Command

private def depsOf (env : Environment) (n : Name) : NameSet :=
  match env.find? n with
  | none => {}
  | some ci =>
    let cs := ci.type.getUsedConstantsAsSet
    match ci with
    | .thmInfo v => cs.union v.value.getUsedConstantsAsSet
    | _ => match ci.value? (allowOpaque := true) with
           | some v => cs.union v.getUsedConstantsAsSet
           | none => cs

private def hole : Name := ``Lean4Lean.VEnv.IsDefEqU.weakN_iff

run_cmd do
  let env ← getEnv
  if (env.find? hole).isNone then logError s!"UNRESOLVED {hole}"
  for (n, _) in env.constants.toList do
    unless (`Lean4Lean).isPrefixOf n do continue
    if n == hole then continue
    if (depsOf env n).contains hole then
      logInfo s!"  {n}   [{((env.getModuleFor? n).getD Name.anonymous)}]"
```

Per-declaration cone / `sorryAx` / axiom check (import only the module under test, so the numbers
are the module's and not the joined cone's) is the `deps`/`cone` walker of `scripts/exists.lean`
with the seed list replaced by the module's own declarations; `scripts/exists.lean` itself could
not be used this round because it walks the whole (incompletely built) default target.

---

## 8. What to pick up first

1. **Apply §5.2(i) immediately** — deleting a false informal claim costs nothing and it is
   currently pointing a successor at a dead end.
2. **Apply §5.2(ii)**, and then answer the one remaining question: does the environment at
   `RestrictStepCfg`'s `e₁`/`e₂` declare a `Sort u`-valued constant?  If yes, the residue is
   closed and the nested restriction step needs neither this hole nor a level side-condition.
3. **Do not** re-run fallback (iii) on `weakN_iff`: §3 settles it.  All 13 direct users need the
   forward direction; the reverse half is available hole-free elsewhere and is consumed by nobody
   through this `iff`.  Splitting the `iff` is not a route.
4. On the hole itself, `docs/handoff-weakn.md` §7.8 and §A.6 still stand.  The one shape this
   round adds to the *refutation* side is §6's open-defeq environment, and what it needs is a
   from-scratch non-derivability argument at a non-`Ordered` environment — the tree has no
   instrument for that, and building one is the whole cost.
