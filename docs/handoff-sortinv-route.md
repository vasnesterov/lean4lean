# Handoff: is there a route to `sort_inv` that avoids `forallE_inv_stratified`?

Written 2026-09-02.  New file rather than a section of `docs/handoff-injectivity.md`, which is
1860 lines / 122 KB and unwieldy.

Claims are marked **[machine]** (a `sorry`-free Lean declaration on this commit, or a
`lake build` / `#print axioms` / cone-script run) or **[analysis]** (read off source).

**One-line answer: NO, and the closing point is machine-checked as an `↔`.**  The lead's
independent `sort_not_proof` pays for the residual that was already free-given-the-target
(`proofIrrel`); the residual that carries the content (`trans` at an arbitrary midpoint) is
provably equivalent to the target.  A *real* gain fell out sideways: unstratified
Π-injectivity comes off the 714-user hole entirely.

Everything below is in one new file, **`/home/vasilii/lean4lean/Lean4Lean/Theory/Typing/SortInvIndep.lean`** (24
declarations — 2 `def`s and 22 theorems — all `sorryAx`-free).  Nothing else was touched.

---

## 0. Where the brief was wrong

The brief asked to be checked.  Three of its assertions need correcting, one materially.

### 0.1 "route A carries `forallE_inv_stratified`" — **CONFIRMED** [machine]

`SetModel/NotProofNoModel.WF.propTypeAgreeOn` runs on `IsDefEqU.uniqU` and
`IsDefEqU.sort_inv`.  I could not measure that declaration directly (see §5: `NotProofNoModel`
does not compile on this commit), but I measured its load-bearing ingredient:
`IsDefEqU.sort_inv` has cone 3409 with holes exactly `[IsDefEqU.forallE_inv_stratified]`.  So
route A is circular for anything that then feeds `sort_inv`, as the brief said, and ledger row
131b's figure is corroborated from the `Theory/Typing` side.

### 0.2 "route B is sorry-free, so leaning on it makes the result non-circular" — **TRUE BUT INCOMPLETE, and this is the material one** [machine + analysis]

`SetModel/PropAgreeWall.propTypeAgreeOnCtx_of_stratifiedN` *is* `sorryAx`-free.  It is **not
hypothesis-free**, and the ledger's own blindness #4 ("an obligation carried as a hypothesis
counts as zero") applies to it:

```
propTypeAgreeOnCtx_of_stratifiedN (henv : VEnv.Ordered env)
    (pta : ∀ n, env.PropTypeAgreeN 0 n) (pun : ∀ n, env.PropUniqN 0 n) :
    env.PropTypeAgreeOnCtx 0
```

* both hypotheses are **open** targets of `Theory/Typing/PropConv.lean` and
  `PropShadow.lean`; only the base index `n = 0` is discharged (`propUniqN_zero`,
  `propTypeAgreeN_zero`, off `HasTypeN.uniq_zero`), and `stratifyN` never produces index 0 —
  the file says so itself;
* `UniqueTypingN.lean`'s own audit of `PropTypeAgreeN` says it is **not self-sufficient**: its
  `eta` case is `SortForallEDisjoint`, a fresh primitive, and its `proofIrrel` case is
  `PropNotProof`, an instance of `PropTypeAgreeN` itself (measure `≤`, not `<`);
* route B is fixed at **`nv = 0`**.  `equivZero_iff_eval_zero` needs `u.WF 0` and the step is
  refuted at `nv ≥ 2` (`propAgree_pointwise_not_from_equivZero`).  `SortUniq`/`sort_inv` are
  wanted at arbitrary `U`.

So route B does not *discharge* the independent source; it **trades** the 714-user node for
`PropTypeAgreeN`/`PropUniqN` at every index, at `U = 0` only.  Read "route B is sorry-free" as
"route B is not circular", never as "route B is paid".

### 0.3 `PiLevelPin.lean`'s own claim — **TRUE-AND-CIRCULAR one way, FALSE the other** [machine]

`PiLevelPin.lean:273–275`: with `sort_not_proof` independent, "`sort_inv` follows from
`WF.rigidShapeUniq` alone".  Two readings, both bad:

1. **`WF.rigidShapeUniq` is a theorem, not a hole.**  Its inhabitant is
   `rigidShapeUniq_of_sortUniq henv (WF.sortUniq' henv) (WF.rigidShapeUniqNS henv)`, and the
   cone measurement gives `WF.rigidShapeUniq`: holes
   `[forallE_inv_stratified, rigidShapeUniqNS]`.  "From `WF.rigidShapeUniq` alone" *is* "from
   `forallE_inv_stratified`".
2. **At the hole level it is false.**  `RigidShapeUniqNS` carries the extra premise
   `¬ s₁.BothSort s₂`, and `RigidShape.BothSort (.sort u) (.sort v)` is `True`
   (`bothSort_sort_sort`, one line, `[propext]`).  The `sort`/`sort` entry — the entry that
   *is* `sort_inv` — was **deleted** from the narrowed hole precisely because
   `sort_inv_of_sortUniq` supplies it from `SortUniq`.  So the narrowed hole says nothing about
   two sorts, and no amount of `sort_not_proof` extracts `sort_inv` from it.

What survives of PiLevelPin's hope is the **Π** half, §4 below — which it did not claim.

---

## 1. The dependency shape, established before anything was proved (work-order item 1)

[machine, cone script — a private copy of `scripts/hole-cone.lean`'s algorithm, forward walk
over **type and value** with `allowOpaque := true`, seeded at **all 24** of my declarations plus 10
controls; run as `lake env lean` over `Lean4Lean.Theory.Typing.SortInvIndep`.]

| declaration | cone | holes in cone |
| --- | --- | --- |
| `IsDefEqU.sort_inv` | 3409 | `forallE_inv_stratified` |
| `WF.sortUniq'` | 3404 | `forallE_inv_stratified` |
| `WF.rigidShapeUniq` | 3434 | `forallE_inv_stratified`, `rigidShapeUniqNS` |
| `IsDefEqU.forallE_inv` | 3537 | `forallE_inv_stratified`, `rigidShapeUniqNS` |
| `piInv_axiom` | 3539 | `forallE_inv_stratified`, `rigidShapeUniqNS` |
| `not_isProof_of_defeqU_sort` | 3426 | `forallE_inv_stratified` |
| `not_isProof_of_defeqU_forallE` | 3426 | `forallE_inv_stratified` |
| `WF.proofTransport` | 3408 | `forallE_inv_stratified` |
| `sort_not_proof` | 2378 | *(none — it takes `SortUniq` as a hypothesis)* |
| `forallE_not_proof` | 2378 | *(none — same)* |

The controls are what make the negatives below trustworthy: the instrument does fire, and it
distinguishes hypothesis-form (`sort_not_proof`, clean) from inhabitant-form
(`not_isProof_of_defeqU_sort`, tainted).  `scripts/hole-rank.lean`'s historic internal-name bug
is not in play here — this walk has no `isInternal` filter at all.

**The shape, then.**  Reading `Injectivity.lean`, `InjPiRogue.lean` §22, `InjOneFact.lean` §4
and `BaseUniqChain.lean`:

```
sort_inv  ⟸  SortUniq                              (sort_inv_of_sortUniq; never opens the conversion)
SortUniq  ⟸  ConvSortInv ∧ ConvPiInv               (sortUniq_of_convInv)
ConvSortInv ⟸ ConvStep2 ∧ SortLinkInv              (convSortInv_of_convStep2_sortLinkInv)
SortLinkInv ⟸ VEnv.WF ∧ SortMidNonSort ∧ SortNotProof     (sortLinkInv_of)
```

and `SortNotProof`/`ShapeNotProof` is the `proofIrrel` residual the lead is about, while
`SortMidNonSort`/`ShapeMidShapeless` is the `trans` residual.

**Circularity verdict** (work-order item 1's crux): `PropTypeAgree` as a *hypothesis* is not
circular — it is not in any hole's cone and no hole is in its cone (`PropAgreeOn`: cone 578,
holes `[]`).  Circularity enters only when it is **instantiated**, and then it depends entirely
on which route is used: route A yes (§0.1), route B no but unpaid (§0.2).  That is the
distinction the brief asked for, and it is the whole answer to "is the result circular": *the
reductions are not, the instantiation of route A would be.*

---

## 2. Proved (work-order item 2)

All in `Lean4Lean/Theory/Typing/SortInvIndep.lean`; all `sorryAx`-free, all with cone-holes
`[]` (measured per declaration, table in §1's instrument run).

**§1 of the file — the independent source, restated and cashed.**
`PropAgreeOn env U` is `SetModel/NotProofNoModel.PropTypeAgreeOnCtx`.  It is *restated* rather
than imported: `Theory/SetModel` imports `Theory/Typing`, so importing it back would invert the
tree's dependency; and on this commit `NotProofNoModel` does not compile anyway.  The unguarded
form was machine-checked definitionally identical to `SetModel/PropSplitAudit.PropTypeAgree`
(`example : PropAgreeAll env U ↔ env.PropTypeAgree U := Iff.rfl`, in a scratch file importing
both — `PropSplitAudit` does build).  **[machine, with the caveat that `PropSplitAudit.lean` is
itself modified in the working tree by another stream, so the identity is against the tree as
of this commit.]**

* `sortNotProof_of_propAgreeOn` — a sort is not a proof, `OnCtx`-guarded.
* `forallENotProof_of_propAgreeOn` — a Π is not a proof.  **Stronger than
  `NotProofNoModel.forallENotProof_of_propTypeAgree`**, which takes the domain and codomain
  typings as extra premises; `HasType.forallE_inv` recovers them, which is what makes it
  usable as a residual-slot inhabitant rather than only at call sites that happen to have them.

**§2 — the corner's `proofIrrel` residual, discharged for all three consumers at once.**
`ShapeNotProofC` (`InjOneFact.ShapeNotProof` guarded by `CtxStrong`), `shapeAgreeC_of_wf`
(`InjOneFact.shapeAgree_of_wf` re-run against the guarded residual — only the `proofIrrel` case
changes), and `shapeLinkAgree_of_propAgreeOn`:

    VEnv.WF ∧ PropAgreeOn ∧ ShapeMidShapeless  →  ShapeLinkAgree

i.e. `InjOneFact.lean`'s **two**-residual bound becomes a **one**-residual bound.  This is the
lead's actual content, and it is real: `InjOneFact.lean` records `ShapeNotProof` as reachable
only through `Injectivity.not_isProof_of_defeqU_sort`, which proves it *from the statement being
reduced*, and therefore deliberately does not import it.  It is now free outright.

**§4 — the gain that is not a collapse: `PiInv` off the 714-user hole.**
Both `SortUniq` uses and the `ProofTransport` use in `Injectivity.lean`'s Π route are the same
fact in disguise ("a Π is not a proof").  Replacing them:

* `not_isProof_of_defeqU_sort_of_propAgreeOn`, `not_isProof_of_defeqU_forallE_of_propAgreeOn` —
  no `SortUniq`, **no `ProofTransport`**.  Proof-ness is not transported along the conversion at
  all: the conversion's own type index is shown to be a proposition, straight off `PropAgreeOn`.
* `rigidPiUniq_of_propAgreeOn : Ordered ∧ PropAgreeOn ∧ RigidShapeUniqNS → RigidPiUniq`
* `IsDefEqU.forallE_inv_of_propAgreeOn` — `forallE_inv_of_rigidPi`'s induction with its one
  `SortUniq` use replaced.
* **`piInv_of_propAgreeOn : VEnv.WF ∧ PropAgreeOn ∧ RigidShapeUniqNS → PiInv`**, cone 3416,
  holes **`[]`** — against `piInv_axiom`'s `[forallE_inv_stratified, rigidShapeUniqNS]`.
* `rigidPiUniq_iff_piInv_of_propAgreeOn` — sharpens `Injectivity.rigidPiUniq_iff_piInv`, which
  takes `SortUniq`.

---

## 3. Refuted / where it closes (work-order item 3)

**`shapeLinkAgree_iff_shapeMidShapeless_of_propAgreeOn`** [machine]:

    VEnv.WF ∧ PropAgreeOn  ⊢  ShapeLinkAgree  ↔  ShapeMidShapeless

`→` is free (`InjOneFact.ShapeLinkAgree.shapeMidShapeless`); `←` is §2.  So with the
`proofIrrel` residual paid from outside, the sort/Π corner's *only* remaining obligation is
**literally equivalent to the corner**.  The mechanism is `InjOneFact.betaMid`: for any
well-typed `X`, `(fun _ : Type 0 => X) Prop` is an `.app`-headed midpoint at every index, so no
syntactic condition on the midpoint localises anything (`InjOneFact.midShapeless_vacuous`).

And the same on the sort side alone, chased all the way to the named hole [machine]:

* `sortLinkInvUC_of_sortUniq : Ordered ∧ SortUniq → SortLinkInvUC` (free, no conversion opened)
* `sortLinkInvUC_iff_sortUniq : VEnv.WF ∧ ConvStep2 ∧ ConvPiInv ⊢ SortLinkInvUC ↔ SortUniq`
* `sortMidNonSortC_iff_sortUniq` — the same with the residual in the shape §2 leaves it,
  composed with `InjOneFact.sortMidNonSortC_iff_sortLinkInvUC`

and `PiLevelPin.piInvStratApp_iff_sortUniq` identifies `SortUniq` with
`forallE_inv_stratified`.  **That is the closing point: the sort-flavoured residual after the
lead is spent is `SortUniq` again.**

This is collapse **eight** in the corner (rows 51, 86, 94 are 5–7), but unlike those it is
reported as the `↔` it is, not as a reduction.

---

## 4. What I tried that failed, and the step it failed at

1. **Import the model side instead of restating it.**  Failed at `lake build`: `Theory/SetModel/`
   `PropSplitUp`, `SoundInduction`, `QuotInterp`, `UnitOracleWitness`, `AboveAudit` do not
   compile on this commit (another stream mid-edit, guarding `PropSplit`'s fields with `OnCtx` —
   ledger row 131g's work item).  Fell back to a restatement plus an `Iff.rfl` identity check
   against `PropSplitAudit`, which does build.
2. **Get `sort_inv`'s `trans` case from `RigidShapeUniqNS`.**  Failed at the definition:
   `RigidShapeUniqNS`'s `¬ s₁.BothSort s₂` premise is `False` at two sorts (§0.3 item 2).
   There is nothing to get.
3. **Get `SortUniq` from `PropAgreeOn` directly.**  Failed at the level layer, and the failure
   is now a theorem: `propAgree_conclusion_not_sortUniq` exhibits `u = 1`, `u' = 2` with
   `∀ ls, (u.eval ls = 0 ↔ u'.eval ls = 0)` and `¬ u ≈ u'`.  `PropAgreeOn`'s conclusion is the
   propositionhood bit and nothing finer — the same wall as
   `PiLevelPin.imax_cod_not_pinned`.
4. **Discharge `ConvPiInv` for the sort chain from §4's `PiInv`.**  Not attempted to completion:
   `BaseUniqChain.convPiInv_of_sortUniq_piInv` takes `SortUniq`, so the chain form of
   Π-injectivity still costs the hole.  `ConvPiInv` therefore stays a hypothesis of
   `sortUniq_of_propAgreeOn` and `sortLinkInvUC_iff_sortUniq`.  **Pick this up first** (§7).

---

## 5. Anti-vacuity, and the grade

The brief's specific trap: seven statements in this corner were green because they were
equivalent to what they claimed to reduce.

* **Hypothesis satisfiability** (ledger §0, blindness 7).  `propAgreeOn_premises_fire`
  [machine]: all seven premise slots of `PropAgreeOn` are satisfied simultaneously at `Γ = []`,
  at **every** environment (no `VEnv.WF`, no constant), with the two types **syntactically
  different** (`.sort (.succ .zero)` vs `.sort (.succ (.imax .zero .zero))`).  So the
  hypothesis is not about an empty class and its conclusion is not trivially reflexive.
  For `ShapeNotProofC` the check **inverts** — it concludes `False`, so an uninhabited premise
  set makes it true and useful, not vacuous; there is no vacuity question to ask of it.
* **Inequivalence of the thing reduced to.**  Stated exactly, because this is where the
  previous seven went wrong:
  - **§3 is not claimed to be a reduction.**  It is the equivalence, in the `↔`.  Graded:
    **collapse, machine-checked.**
  - **§2 and §4 are reductions, and `propAgree_conclusion_not_sortUniq` establishes that they
    are not the target restated *by the route every previous collapse took*** — instantiate the
    "localised" hypothesis at a chosen subject and read the target off its conclusion.  That
    move is impossible here: the conclusion cannot yield `u ≈ u'`.
  - **What is NOT established**, and I am not going to hedge it: that
    `PropAgreeOn → env.SortUniq U` fails at every environment.  That needs a witness
    environment satisfying one and not the other, and **none is exhibited**.  Grade §2/§4
    **probably not a collapse, not proved not to be** — an *indirect* route from `PropAgreeOn`
    to `SortUniq` is not ruled out.  `sortUniq_conclusion_gives_propAgree` shows the converse
    implication of conclusions does hold, so `PropAgreeOn` is on the weak side rather than
    merely incomparable, which is weak evidence in the same direction.

---

## 6. Verification, verbatim

* **`lake build` (full tree)**: fails, with errors **only** in `Lean4Lean/Theory/SetModel/` —
  another stream's in-flight `OnCtx` guarding of `PropSplit`.  **The error set moved between two
  runs in this one session**, which is itself worth recording: the first run (before
  `SortInvIndep.lean` existed) gave 8 errors in `PropSplitUp.lean` + 3 in `SoundInduction.lean`;
  the last run gave 48 in `QuotInterp.lean`, 32 in `UnitOracleWitness.lean`, 2 in
  `AboveAudit.lean` and none in the first two.  Both sets are **entirely inside
  `Theory/SetModel/`**, which I do not own, and the first one predates my file.  No error in any
  file I own, on either run.  No job count is printed on a failing build.
* **`scripts/dup-names.lean`**: also cannot run — same `ConeJoin`/SetModel import failure.  Name
  clashes were instead ruled out by construction: every new declaration is in `Lean4Lean.VEnv`
  with a `_of_propAgreeOn` / `C` suffix and `lake build` of the module (which sees all of
  `InjOneFact`'s and `Injectivity`'s namespace) reports no `already been declared` error.
* **`lake build Lean4Lean.Theory.Typing.SortInvIndep`**: `Build completed successfully (83 jobs).`
* **`lake build Lean4Lean.Experimental.ConeJoin Lean4Lean.Verify.Guard`**: **fails**, in
  `Theory/SetModel/{QuotInterp, UnitOracleWitness, AboveAudit}` — `ConeJoin` imports 20 SetModel
  modules and five of them are red.  `ConeJoin.lean` was not edited (it is the orchestrator's).
* **`lake build Lean4Lean.Verify.Guard`** alone does build (`Guard → Soundness → Environment`,
  no SetModel), and the three guards read:

```
info: Lean4Lean/Verify/Guard.lean:170:0: guard 1: Axioms.lean declares exactly the 24 frozen axioms ✓
info: Lean4Lean/Verify/Guard.lean:195:0: guard 2: kernel_sound axioms within whitelist ✓ (proof INCOMPLETE: sorryAx present)
info: Lean4Lean/Verify/Guard.lean:216:0: guard 3: checker cone implementation gaps within frozen list (2/2 remaining) ✓
Build completed successfully (1144 jobs).
```

  Guard 1 = **24**, guard 3 = **2/2**, guard 2 INCOMPLETE as expected.  Nothing moved.
* **`#print axioms`**: 24 audit lines are in the file itself (§6 of it), checked at build time —
  one per declaration, `def`s included.  All 24 report `[propext, Quot.sound]`, `[propext, Classical.choice, Quot.sound]` or
  `[propext]`.  **No `sorryAx`.  No frozen axiom** (the frozen list lives in
  `Verify/Axioms.lean` and is reached only from the `Verify` cone; nothing here imports it —
  cone measurement shows no `Lean4Lean.*` axiom in any of the 24 cones).
* **Cone measurement, per declaration, over type and value, `allowOpaque := true`**: of 34 seeds
  (my 24 + 10 controls), **26 report `holes []`** — my 24, plus the two hypothesis-form controls
  `sort_not_proof` and `forallE_not_proof` — and the 8 inhabitant-form controls all report
  `forallE_inv_stratified` (§1's table).  So **none** of the 24 contains any of
  `forallE_inv_stratified`, `rigidShapeUniqNS`, `weakN_iff`, `descend`, and the instrument is
  demonstrably not silently returning empty.
* **`scripts/sorry-census.lean` CANNOT BE RUN on this commit**: it imports
  `Experimental.ConeJoin`, which is red (above).  I ran a **reduced-import copy** (roots:
  `Verify.Guard`, `SortInvIndep`, `ChurchRosser`, `UniqSort`, `PatWFIota`, `Inductive.Decl`,
  `Verify.TypeChecker`, `Verify.Environment`, `Verify.Typing.Lemmas`), which reports

```
TOTAL declarations directly containing sorryAx: 12
  Inductive.Decl:            VIndRecArg.exists_indep                  [0 users]
  Typing.ChurchRosser:       NormalEq.descend                         [173 users]
  Typing.Injectivity:        WF.rigidShapeUniqNS                      [251 users]
  Typing.Injectivity:        IsDefEqU.forallE_inv_stratified          [438 users]
  Typing.UniqueTyping:       IsDefEqU.weakN_iff                       [228 users]
  Verify.Environment:        addDecl.WF                               [0 users]
  Verify.Soundness:          kernel_sound, kernel_complete            [0 users]
  Verify.TypeChecker.InferType: Inner.inferProj.WF                    [58 users]
  Verify.TypeChecker.IsDefEq: Inner.isDefEqUnitLike.WF                [58 users]
  Verify.TypeChecker.IsDefEq: Inner.tryEtaStructCore.WF               [59 users]
  Verify.Typing.Lemmas:      TrProj.weak'_inv                         [78 users]
```

  **Every number there is a floor**, not the census figure: the graph is ~110 modules smaller
  than `ConeJoin`'s, which is exactly why `forallE_inv_stratified` reads 438 and not the
  brief's 714.  **12 ≠ the expected 13**, and the missing row is in a module the reduced root
  set does not reach — I did not chase it further.  What the run *does* establish, which is the
  claim that matters: **no row for `Theory.Typing.SortInvIndep` appears at all**, so nothing was
  added and nothing traded.  Independently, all 24 declarations are individually
  `#print axioms`-clean at build time.
* **Tooling caveat, confirmed** (ledger row 131f): `which rg` → nothing.  `lean_local_search`
  and `lean_hammer_premise` are dead in this tree.  Every search claim above is backed by
  **`grep`** (which is `ugrep` here) or by **`lean_run_code` / `lean_diagnostic_messages`**
  (LSP); `lean_references` was not needed.  The cone figures are from the private
  `hole-cone.lean` copy, not from a search tool.

---

## 7. What to pick up first

1. **`ConvPiInv` from `piInv_of_propAgreeOn`.**  This is the one loose end that is pure
   bookkeeping.  `BaseUniqChain.convPiInv_of_sortUniq_piInv` takes `SortUniq`; if the chain form
   can be built from `PiInv` plus `PropAgreeOn` instead, then `sortUniq_of_propAgreeOn` and
   `sortLinkInvUC_iff_sortUniq` shed their `ConvPiInv` hypothesis and the sort side's residual
   becomes **`ConvStep2 ∧ ShapeMidShapeless`** with nothing else — the sharpest possible
   statement of where the corner stands.  Cheap, and it makes §3's negative airtight.
2. **`PropTypeAgreeN` at every index** (`Theory/Typing/PropConv.lean`, `PropShadow.lean`).  §4
   makes this the price of taking `PiInv` off `forallE_inv_stratified`.  Its own audit says the
   missing primitive is **`SortForallEDisjoint`** (`UniqueTypingN.lean`), which has no other
   consumer in the tree and nobody working on it.  That is the concrete funded item this lead
   produces.
3. **Do NOT re-attempt a midpoint localisation** of either `trans` residual.  `betaMid`
   (`InjOneFact.lean`) closes that off for every shape-based side condition, and §3 now closes
   it off for the version with `proofIrrel` already paid.  What is left has to mention a
   reduction relation or a normal-form predicate — `InjOneFact.ShapeCR` is the request.
4. **Ledger rows to write** (I did not edit `docs/vacuity-ledger.md`; it is not mine):
   * a row for collapse **eight** (`shapeLinkAgree_iff_shapeMidShapeless_of_propAgreeOn`,
     `sortMidNonSortC_iff_sortUniq`);
   * a **correction to row 131c**: "route B is sorry-free" is true and misleading — it carries
     two open `∀ n` hypotheses and is fixed at `nv = 0` (§0.2);
   * a **correction to `PiLevelPin.lean`'s** closing section (§0.3), which is currently prose
     recommending a route that is circular in one reading and refuted in the other.  That file
     is mine; I left the docstring alone rather than edit a 714-user file's neighbourhood
     mid-round, and `SortInvIndep.lean` §3.1 carries the correction instead.

---

# Round 2 (2026-09-02, later): `ConvPiInv` discharged; `SortForallEDisjoint` priced

New section, appended rather than editing §0–§7 above (that text is the previous round's record
and its §7 item 1 is what this round executes).  Same conventions: **[machine]** = a `sorry`-free
Lean declaration on this commit plus a `lake build` / `#print axioms` / cone run;
**[analysis]** = read off source.

Task order chosen: **Task 1 first.**  Reason, stated because it was asked for: task 1 is
bounded and its outcome changes how task 2's value must be read.  If the sort side's residual
after §7 item 1 still contains a Π-injectivity conjunct, then even a hole-free
`PropTypeAgreeN`/`PropUniqN` route does not close the corner, and task 2 must be reported as
buying the *model* import and not the *syntactic* one.  Doing task 1 second would have meant
grading task 2 against a residual I had not yet measured.

## 8. Task 1: `ConvPiInv` is free, and it is cheaper than §7 item 1 expected

New file **`/home/vasilii/lean4lean/Lean4Lean/Theory/Typing/PiInvResidual.lean`** (13
declarations, all `sorryAx`-free, all cone-holes `[]`).  Nothing else was touched.

### 8.1 The route §7 item 1 proposed is the *wrong* one, and would have weakened the statement

§7 item 1 says to build `ConvPiInv` "from `PiInv` plus `PropAgreeOn`", i.e. through
`piInv_of_propAgreeOn` and `InjChainStep.convPiInv_of_convStep2`.  That does typecheck
(`convPiInv_of_convStep2 henv.ordered hcs (piInv_of_propAgreeOn henv hT h)`), and it is a
**regression**: `piInv_of_propAgreeOn` takes `env.RigidShapeUniqNS U`, so the composite trades
the hypothesis `ConvPiInv` for the hypothesis `RigidShapeUniqNS`, and `RigidShapeUniqNS` is
*strictly larger* — `RigidNodeCircle.rigidShapeUniqNS_iff_family` decomposes it as `PiInv ∧`
four more conjuncts.  Substituting it in makes `sortUniq_of_propAgreeOn` a **weaker** theorem,
not a sharper one.  **So §7 item 1's own recipe is wrong, and the brief that repeated it
("which may now be nearly free … `PiInv` already conjunct 1 here") inherits the error.**
[machine: the composite builds; analysis: the direction of the trade]

### 8.2 The cheap route was already in `InjOneFact.lean`, one export short

`InjOneFact.shapeLinkAgree_iff` decomposes `ShapeLinkAgree` into `SortLinkInvUC ∧ PiLinkInvUC ∧
SortPiDisjUC`, and **`PiLinkInvUC` already concludes both halves of `ConvPiInv`'s conclusion** —
`ConvC Γ A A' ∧ ConvC (A::Γ) B B'` — for a single link at an arbitrary type index.  The only gap
is chain-to-link, which is exactly `InjChainStep.ConvC.collapseE` from `ConvStep2` alone.  That
file exports only the *codomain* half (`convPiInvCod_of_shapeLinkAgree`), which is why the full
statement was missed for a round.  Four lines:

* `convPiInv_of_convStep2_piLinkInvUC : ConvStep2 ∧ PiLinkInvUC → ConvPiInv` [machine, cone 122]
* `convPiInv_of_shapeLinkAgree : ConvStep2 ∧ ShapeLinkAgree → ConvPiInv` [machine, cone 635]

`collapseE`'s `refl` branch is a *syntactic* equation between two Π's, so `injection` gives the
two chains and no reflexivity witness is needed.

### 8.3 What that buys — proved [machine, per-declaration cones in §8.6]

| target | hypotheses before | hypotheses after |
| --- | --- | --- |
| `SortUniq` | `WF ∧ PropAgreeOn ∧ ConvStep2 ∧ ConvPiInv ∧ ShapeMidShapeless` | `WF ∧ PropAgreeOn ∧ ConvStep2 ∧ ShapeMidShapeless` (`sortUniq_of_propAgreeOn'`) |
| `SortLinkInvUC ↔ SortUniq` | `WF ∧ ConvStep2 ∧ ConvPiInv` | `WF ∧ PropAgreeOn ∧ ConvStep2 ∧ ShapeMidShapeless` (`sortLinkInvUC_iff_sortUniq'`) |
| `PiInv` | `WF ∧ PropAgreeOn ∧ RigidShapeUniqNS` (`piInv_of_propAgreeOn`) | `WF ∧ ConvStep2 ∧ ShapeLinkAgree` — **no `PropAgreeOn`, no `RigidShapeUniqNS`** (`piInv_of_shapeLinkAgree`) |
| `RigidSortPiDisj` | conjunct 2 of `rigidShapeUniqNS_iff_family` | free from `ShapeLinkAgree` (`rigidSortPiDisj_of_shapeLinkAgree`) |
| `RigidShapeUniqNS` (hole B) | five conjuncts `∧ ConvStep2` | **three** const-spine conjuncts `∧ ConvStep2 ∧ ShapeMidShapeless ∧ PropAgreeOn` (`rigidShapeUniqNS_of_propAgreeOn`) |

So **§7 item 1's stated goal is achieved**: the sort side's residual after the independent
source is `ConvStep2 ∧ ShapeMidShapeless` and nothing else.  And `docs/vacuity-ledger.md`'s
corner table line "hole B: the five conjuncts (incl. `PiInv`) `∧ ConvStep2`" should now read
**three** conjuncts, all three of them the constant-spine facts (`RigidConstAppInv`,
`RigidConstPiDisj`, `RigidConstSortDisj`).

### 8.4 The grade: collapse-shaped, consolidating — *not* a strength reduction

Stated up front because this corner has eight collapses in it.  `ShapeMidShapeless` is
equivalent to `ShapeLinkAgree` (`InjOneFact.shapeMidShapeless_iff`, `Ordered env` only) and
`shapeLinkAgree_iff` makes `ShapeLinkAgree` *the conjunction of all three entries of the
corner*.  So every row of §8.3 reduces a target to a hypothesis **containing that target's own
entry**.  Two of the three coordinates are machine-checked equivalences, so the residual is not
strictly stronger either:

* sort entry: `sortLinkInvUC_of_sortUniq'` recovers it from `SortUniq` [machine]
* sort/Π entry: `sortPiDisjUC_of_rigidSortPiDisj` recovers it from `RigidSortPiDisj` [machine]
* Π entry: **not recovered.**  `InjOneFact.lean` §6 records that the converse of
  `PiLinkInvUC → PiLinkInvCod ∧ PiLinkInvDom` "is not available and no claim is made that it
  is", because moving an arbitrary index `T` to a syntactic sort is uniqueness of typing.  So
  §8.3's `PiInv` row is a reduction into something **possibly strictly stronger**, and is graded
  that way rather than as a gain.

Net: **the value is consolidation, not weakening.**  Four hypotheses become two, and the corner
now has one normal form —

    after the independent source, the whole sort/Π corner is  `ConvStep2 ∧ ShapeMidShapeless`

which is what makes §3's negative airtight (§7 item 1's own reason for asking).  It does not
make the corner smaller.

### 8.5 What it unlocks in `RigidNodeCircle.lean`, since the brief asked

`RigidNodeCircle.lean:162–164`'s docstring is **correct on the mechanism and wrong on the
supply**.  Correct: `htr` is used in one of nine branches, at a constant spine, and
`proofTransportSpine_of` supplies that from `ConvPiInv` alone; `baseUniqCAt_of` does need
`ConvSortInv` only for its `.forallE` head, which a spine never presents.  Wrong: it says
`ConvPiInv` comes from `ConvStep2 ∧ PiInv` "with `PiInv` already conjunct 1 here" — which is
circular *as a way of discharging conjunct 1*, since conjunct 1 is what one is trying to prove.
§8.2's route is not circular: `ConvPiInv` comes from `ConvStep2 ∧ ShapeLinkAgree` with no
`PiInv` anywhere, and then §8.3 gets `PiInv` itself out of the same two.  That is what
`rigidShapeUniqNS_of_constSpine` cashes: hole B from the **three** const-spine facts plus
`ConvStep2 ∧ ShapeLinkAgree`, with `ProofTransport`'s spine restriction, `PiInv` and
`RigidSortPiDisj` all supplied internally.  `baseUniqCAt_of`'s `ConvSortInv` half is not needed
anywhere in that chain.

### 8.6 Verification, verbatim [machine]

* `lake build Lean4Lean.Theory.Typing.PiInvResidual`: **`Build completed successfully (84
  jobs).`**  No error in any file I own.
* `#print axioms`, one per declaration, in the file (`section Audit`), checked at build time.
  All 13 report `[propext]`, `[propext, Quot.sound]` or `[propext, Classical.choice,
  Quot.sound]`.  **No `sorryAx`.  No frozen axiom.**
* Cone measurement, forward walk over **type and value**, `allowOpaque := true`, private copy
  of `scripts/hole-cone.lean`'s algorithm, 22 seeds (my 13 + 9 controls):

| declaration | cone | holes |
| --- | --- | --- |
| `convPiInv_of_convStep2_piLinkInvUC` | 122 | `[]` |
| `convPiInv_of_shapeLinkAgree` | 635 | `[]` |
| `convInv_of_shapeLinkAgree` | 643 | `[]` |
| `sortUniq_of_propAgreeOn'` | 3481 | `[]` |
| `sortUniq_of_shapeLinkAgree` | 2396 | `[]` |
| `sortLinkInvUC_iff_sortUniq'` | 3490 | `[]` |
| `piInv_of_shapeLinkAgree` | 3330 | `[]` |
| `rigidSortPiDisj_of_shapeLinkAgree` | 2342 | `[]` |
| `rigidShapeUniqNS_of_constSpine` | 3400 | `[]` |
| `rigidShapeUniqNS_of_propAgreeOn` | 3504 | `[]` |
| `sortLinkInvUC_of_sortUniq'` | 2342 | `[]` |
| `sortPiDisjUC_of_rigidSortPiDisj` | 665 | `[]` |
| `piLinkInvCod_of_shapeLinkAgree` | 604 | `[]` |
| *control* `piInv_axiom` | 3539 | `forallE_inv_stratified`, `rigidShapeUniqNS` |
| *control* `WF.rigidShapeUniq` | 3434 | `forallE_inv_stratified`, `rigidShapeUniqNS` |
| *control* `WF.sortUniq'` | 3404 | `forallE_inv_stratified` |
| *control* `IsDefEqU.sort_inv` | 3409 | `forallE_inv_stratified` |
| *control* `IsDefEqU.forallE_inv` | 3537 | `forallE_inv_stratified`, `rigidShapeUniqNS` |
| *control* `WF.proofTransport` | 3408 | `forallE_inv_stratified` |

  So **none** of the 13 contains any of `forallE_inv_stratified` (725), `rigidShapeUniqNS`
  (460), `weakN_iff` (312), `descend` (200), and the instrument demonstrably fires: all six
  inhabitant-form controls report a hole.

## 9. Task 2: the two `∀ n` statements — and the brief's named primitive is on a dead route

New file **`/home/vasilii/lean4lean/Lean4Lean/Theory/Typing/PropAgreeGuarded.lean`** (19
declarations, all `sorryAx`-free, all cone-holes `[]`).  Nothing else was touched.

### 9.1 The correction, and it is the main result of task 2 [machine]

The brief says: *"The named missing primitive is `SortForallEDisjoint` — a family in
`Theory/Typing/UnivDiscrim.lean`, referenced from `PropShadow.lean:179` and `SortUniq.lean:163`,
described as having no other consumer and nobody working on it."*  **Four things wrong.**

1. **It is not the missing primitive on the live route, and this is measured, not read.**
   `UniqueTypingN.lean`'s audit ("the primitive to route or fund is `SortForallEDisjoint`")
   describes a route that inducts on the **conversion** judgment, where `eta` is a case.
   `PropConv.propTypeAgree_of` inducts on the **typing** judgment, where `eta` — like `trans`,
   `beta`, `proofIrrel`, `extra` — is `nomatch hb`.  Its residuals are `SortInvN`,
   `PropConvInv`, `PropTypeAgreeN.AppCase`; `propTypeAgree_appCase_of` prices the last at
   `SortInvN ∧ RegPi ∧ InstLvl ∧ PropUniqN ∧ PropConvInv`, all at the same index.
   Cone-membership probe over the whole assembly `propTypeAgreeN_and_propUniqN_of`
   (forward walk, type and value, `allowOpaque := true`):

   | probe | in cone of the assembly? |
   | --- | --- |
   | `SortForallEDisjoint` | **out** |
   | `SortForallEDisjoint.AppCase` | **out** |
   | `PropNotProof` | **out** |
   | `SortForallEDisjN` | IN |
   | `SortInvN`, `PropConvInv`, `RegPi`, `InstLvl` | IN |

   So `SortForallEDisjoint` is *not reachable at all* from the route that discharges the two
   targets.  **Funding it would be work on a route the tree has already routed around.**
2. **The brief conflates two predicates with near-identical names.**
   `UniqueTypingN.SortForallEDisjoint` (typing-level: no term has both a sort type and a Π type)
   is not `DefInvRefute.SortForallEDisjN` (conversion-level: no `⊢ₙ` conversion between a sort
   and a Π).  The second *is* in the cone — as half of `SortDisjInvN` — and the first is not.
3. **It is not defined in `UnivDiscrim.lean`.**  `UniqueTypingN.lean:701`.  `UnivDiscrim.lean`
   is one of three files *about* it.
4. **"No other consumer and nobody working on it" is false.**  `Theory/Typing/ShapeSpine.lean`
   (423 lines) is entirely about it and proves the hereditary strengthening *equivalent* to it
   (`SortForallEDisjointH.iff`) and the agreement form **false** (`typeShapeAgree_false`);
   `UnivDiscrim.lean` (340 lines) closes the `common_sort` route to it; `AppCase.lean` (746
   lines) prices its `app` case, which is shared with four other statements, and refutes every
   named route (`appTypeUniq_false`, `piCodConv_false`, `relDisj_instClosed_false`,
   `uniqN_false`).  Consumers in Lean, not prose: `PropTypeAgreeN.eta_case`,
   `sortForallEDisjoint_ofN`, `SortClauses.propLoopEnv_constA_not_forallE_typed`,
   `SortForallEDisjoint.appCase`, `SortForallEDisjoint.univ`.  [grep + `lean_references`-free;
   see §9.6 on tooling]

### 9.2 What the two `∀ n` targets do reduce to [machine]

`propTypeAgreeN_and_propUniqN_of`, at **every** environment and every `U`:

    (∀ n, SortDisjInvN) ∧ (∀ n, PropConvInv) ∧ (∀ n, RegPi) ∧ (∀ n, InstLvl)
      ∧ (∀ n, PropUniqN.AppCase)
    →  (∀ n, PropTypeAgreeN) ∧ (∀ n, PropUniqN)

base index discharged internally.  And **it is a collapse, reported as one**:
`propUniqN_iff_appCase_all` is the `↔` (over `∀ n, SortDisjInvN`) between the fifth hypothesis
and the second conclusion, so the reduction moves no content — it *isolates* it.  The content of
**both** `∀ n` targets is the single statement `∀ n, PropUniqN.AppCase env U n`, which
`AppCase.AppUniqLvl.iff` identifies with `∀ n, AppUniqLvl`.  `propTypeAgreeN_and_propUniqN_iff`
states the whole thing as an `↔`.

Value, stated without inflation: the two `∀ n` statements are **one** obligation and four side
conditions, not two independent obligations — and that one obligation is the `app` case
`AppCase.lean` has already walled on both sides.

**Caveat, flagged rather than buried**: `PropConv.RegPi`'s own docstring says it is *not shown
satisfiable*, not even at the base index (`Stratified.lam` does not ship `A::Γ ⊢ B : .sort v`).
So `propTypeAgreeN_and_propUniqN_iff` is **conditional on `RegPi` being satisfiable**; if it is
not, that `↔` is vacuous (ledger §0, blindness 7).  `propUniqN_iff_appCase_all` carries no such
caveat — it needs only `SortDisjInvN`, whose base index is `SortDisjInvN.zero`.  The two are
stated separately for exactly that reason.

### 9.3 A genuine weakening that fell out: route B can carry the `OnCtx` guard [machine]

`SetModel/PropAgreeWall.propTypeAgreeOnCtx_of_stratifiedN` has `OnCtx Γ (env.IsType 0)` in hand
at the point where it applies `pta` and `pun`, and does not use it.  `propAgreeOn_of_stratifiedNOn`
is that proof with the guard pushed onto the hypotheses:

    Ordered env ∧ (∀ n, PropTypeAgreeNOn env 0 n) ∧ (∀ n, PropUniqNOn env 0 n) → PropAgreeOn env 0

`PropTypeAgreeN.propTypeAgreeNOn` / `PropUniqN.propUniqNOn` are the one-line comparisons, so this
is **strictly less to prove** than route B asks for, with the same conclusion
(`SortInvIndep.PropAgreeOn`, i.e. `NotProofNoModel.PropTypeAgreeOnCtx` restated).
`propAgreeOn_of_stratifiedN` shows the unguarded form still works, so it subsumes route B rather
than replacing it.  `PropTypeAgreeNOn.zero` / `PropUniqNOn.zero` replay the base-index
anti-vacuity check for the guarded forms.

**The exact edit in a file I do not own, stated and not made** (`SetModel/` belongs to another
stream): `PropAgreeWall.propTypeAgreeOnCtx_of_stratifiedN`, `propUniqOnCtx_of_stratifiedN` and
`nonempty_propSplit_of_stratifiedN` should take `PropTypeAgreeNOn` / `PropUniqNOn`.  With the
`Theory/Typing` side proved here the edit is a rename plus threading `hΓ`.

Why it matters beyond tidiness: `RegPi` — §9.2's unsatisfiability caveat — is exactly what an
`OnCtx` hypothesis is expected to buy, per its own docstring ("`Lookup` can hand back a Π-type
whose components were never typed, so it needs a well-formed-context hypothesis").  Guarding the
*target* makes that hypothesis available to whoever attacks `RegPi`.

### 9.4 `SortForallEDisjoint` cannot be proved from `Ordered env` [machine]

`sortPiEnv_sortForallEDisjoint_false : ¬ sortPiEnv.SortForallEDisjoint 0 1`, and the `∀ n` form
with it.  `SortClauses.sortPiEnv` is `Ordered` and not `VEnv.WF`; it carries
`Prop ≡ ∀ (_ : Prop), Prop`, and in the context `[Prop]` the term `.bvar 0` has the *sort* type
`.sort .zero` and, by `conv` along the rule, the *Π* type `.forallE (.sort .zero) (.sort .zero)`.
This is the typing-level statement; `SortClauses.sortPiEnv_sortForallEDisjN_false` is the
conversion-level clause (3) at the same environment (§9.1 item 2).

**And it does not refute the two targets** — said explicitly, because a refutation that came from
a counterexample to the targets themselves would be worthless.  The witness's two types are
`.sort .zero` and a Π, and **neither is a proposition**, so `PropTypeAgreeN`'s hypothesis
`IsPropN Γ A` is never met at it (`sortPiEnv_witness_type_not_prop` is the sort half, from
`not_isPropN_sort`).  I did **not** attempt a refutation of `PropTypeAgreeN sortPiEnv 0 1` and do
not claim one; my sketch says a `VDefEq` rule cannot separate propositionhood because
`VDefEq.WF` forces both sides to be typed at *one* type — that is **[analysis], unproved**.

Consequence for the route, which is the useful part: the *only known* route to
`∀ n, SortDisjInvN` (a side condition of §9.2) runs through `SortForallEDisjN`, and
`SortClauses.sortPiEnv_sortForallEDisjN_all_false` refutes that at an `Ordered` environment.  So
**§9.2's assembly cannot be discharged from `Ordered env` alone**, while
`propTypeAgreeOnCtx_of_stratifiedN` asks only for `Ordered`.  Whoever closes these targets should
state them at `VEnv.WF` (`preludeEnv` is `WF`, so nothing is lost) — or expect to hit this wall.

### 9.5 Answer to "prove `SortForallEDisjoint` or say exactly why it cannot be proved"

**It cannot be proved as stated, and it is the wrong target.**  Precisely:

1. At `Ordered env` it is **false** (§9.4).  Any proof needs `VEnv.WF`.
2. At `VEnv.WF` it is neither proved nor refuted, and it is a **fixpoint**:
   `ShapeSpine.SortForallEDisjoint.appCase` derives its one open case from the statement in one
   line, and `UniqueTypingN.sortForallEDisjoint_ofN` derives the statement from that case, so the
   `app` case is not a smaller sub-problem — it is the whole content.  Nothing equivalent to it
   can break it, and `ShapeSpine.SortForallEDisjointH.iff` shows the natural hereditary
   strengthening *is* equivalent to it while `typeShapeAgree_false` refutes the agreement form.
   Every other named route is refuted in `AppCase.lean`.
3. **And none of that blocks the two `∀ n` targets**, because §9.1's cone probe puts
   `SortForallEDisjoint` outside the assembly's cone entirely.

So the brief's conditional — "if `SortForallEDisjoint` is what unblocks the induction" — has
answer **no**, and the thing that does gate it is `∀ n, AppUniqLvl` (= `∀ n,
PropUniqN.AppCase`), plus `RegPi`, `InstLvl`, `PropConvInv`, `SortDisjInvN`.

### 9.6 Verification, verbatim [machine]

* `lake build Lean4Lean.Theory.Typing.PropAgreeGuarded`: **`Build completed successfully (95
  jobs).`**
* `#print axioms`, one per declaration, in the file (`section Audit`).  All 19 report
  `[propext]`, `[propext, Quot.sound]` or `[propext, Classical.choice, Quot.sound]`.  **No
  `sorryAx`, no frozen axiom.**
* Cone measurement, 19 seeds + 6 controls, same instrument as §8.6.  **All 19 report
  `holes []`**: `eval_indep_of_wf_zero` 572, `equivZero_iff_eval_zero'` 586,
  `propTypeAgreeN_and_propUniqN_of` 1705, `propUniqN_iff_appCase_all` 1652,
  `propTypeAgreeN_and_propUniqN_iff` 1709, `PropTypeAgreeNOn` 35, `PropUniqNOn` 583,
  `PropTypeAgreeN.propTypeAgreeNOn` 37, `PropUniqN.propUniqNOn` 585,
  `propAgreeOn_of_stratifiedNOn` 2410, `propAgreeOn_of_stratifiedN` 2415,
  `PropTypeAgreeNOn.zero` 773, `PropUniqNOn.zero` 774, `sortPiEnv_bvar_sort` 163,
  `sortPiEnv_conv_cons` 605, `sortPiEnv_bvar_pi` 619,
  `sortPiEnv_sortForallEDisjoint_false` 621, `sortPiEnv_sortForallEDisjoint_all_false` 622,
  `sortPiEnv_witness_type_not_prop` 691.  Controls fire: `piInv_axiom` 3539
  `[forallE_inv_stratified, rigidShapeUniqNS]`, `WF.sortUniq'` 3404
  `[forallE_inv_stratified]`.  Upstream ingredients also measured clean: `propUniq_of'` 1649,
  `propTypeAgree_of'` 1661, `propTypeAgree_appCase_of` 1622, `sortForallEDisjoint_ofN` 723 — all
  `holes []`.
* **Tooling, confirmed again**: `which rg` → nothing, so `lean_local_search` and
  `lean_hammer_premise` are dead in this tree, exactly as the brief says.  Every search claim in
  §8–§9 is backed by **`grep`** (a floor, not an exhaustive search) or by `lake build` /
  `lake env lean` (the cone runs and the `#print axioms` lines).  `lean_references` was not
  needed: the two claims that would have wanted it (`SortForallEDisjoint`'s consumers, §9.1 item
  4) are backed by the cone probe instead, which is stronger than a name search.
* **Not run, deliberately, per the brief**: full `lake build`, the three guards,
  `scripts/sorry-census.lean`, `scripts/dup-names.lean`, `MemberRedexScan`.  Two other streams
  are editing `Theory/SetModel/*` and `Theory/Inductive/*` concurrently and all five of those are
  tree-wide.  Evidence offered instead is per-module: two `lake build`s with job counts, 32
  `#print axioms` lines, and 41 cone-seed measurements.  Name clashes were ruled out by
  construction (every new name is in `Lean4Lean.VEnv` or `Lean4Lean.VLevel` with a fresh suffix,
  and both module builds see the full namespaces of `InjOneFact`, `Injectivity`, `PropConv`,
  `AppCase` and `SortClauses`; no `already been declared` error).

## 10. Where the brief and §7 were wrong — one list

1. §7 item 1's recipe for `ConvPiInv` (through `piInv_of_propAgreeOn`) is a **regression**, and
   the brief repeated it (§8.1).  The right route is `PiLinkInvUC` + `collapseE`.
2. The brief: "`baseUniqCAt_of` is named there as needing `ConvSortInv` only for part of its
   job" — true, and **irrelevant to the result**: the route in §8 never calls `baseUniqCAt_of`
   at all.
3. The brief: "`PiInv` already conjunct 1 here", offered as a reason `ConvPiInv` is cheap.
   Circular as written (conjunct 1 is what one is proving) — see §8.5.
4. The brief: `SortForallEDisjoint` is the named missing primitive, in `UnivDiscrim.lean`, with
   no other consumer and nobody working on it.  **Four errors** (§9.1).
5. The brief: the two `∀ n` statements "are now the *entire* remaining syntactic import of the
   model side".  True per ledger row 136d, **but** `PropAgreeWall.nonempty_propSplit_preludeEnv`
   already gives `Nonempty (PropSplit preludeEnv 0)` with **no hypotheses** by route A — so what
   the `∀ n` statements buy is a *hole-free* route, not the only route.  Worth stating precisely
   because it changes the value: they remove `forallE_inv_stratified` from that corner's cone;
   they do not unblock anything that is currently blocked.
6. Correct in the brief, and confirmed here: `PiInv` becoming hole-free last round is real; the
   `rg` tooling is dead; the `∀ n` statements are only discharged at `n = 0`; and separating
   "hole-free" from "discharged" is the right discipline — **§9.2's assembly is hole-free and
   discharges nothing**, because its fifth hypothesis is its own second conclusion.

## 11. What to pick up first

1. **`∀ n, PropUniqN.AppCase` (= `∀ n, AppUniqLvl`).**  §9.2 makes this the single content of
   both `∀ n` targets.  Do **not** re-attempt `SortForallEDisjoint` (§9.5).
2. **`RegPi`, guarded.**  §9.3 makes the `OnCtx` hypothesis available; `PropConv.RegPi`'s
   docstring says that is exactly what it wants.  Until it is satisfiable,
   `propTypeAgreeN_and_propUniqN_iff` is conditional.
3. **The `SetModel/PropAgreeWall.lean` rename** in §9.3 — another stream's file, one-line edits,
   strictly weakens two hypotheses.
4. **`ConvStep2 ∧ ShapeMidShapeless`** is now the whole sort/Π corner (§8.3–§8.4).  Both are
   equivalent to the corner, so the request is still the confluence-layer statement
   `InjOneFact.ShapeCR`; nothing in §8 changes that.
5. **Ledger rows to write** (I did not edit `docs/vacuity-ledger.md`):
   * hole B's row in the corner table: **three** const-spine conjuncts `∧ ConvStep2 ∧
     ShapeMidShapeless`, not five conjuncts `∧ ConvStep2` (§8.3);
   * a row for §9.1 — `SortForallEDisjoint` is outside the cone of the live route, measured;
   * a row for §9.2 — the `∀ n` pair is one obligation, and the reduction to it is an `↔`;
   * a row for §9.4 — `SortForallEDisjoint` false at an `Ordered` environment.

---

# Round 3 (2026-09-02, later still): task 1 was already in HEAD; **`∀ n, AppUniqLvl` is FALSE at an `Ordered` environment**

Appended, not editing §0–§11.  Conventions unchanged: **[machine]** = a `sorry`-free declaration
on this commit plus a `lake build` / `#print axioms` / cone run; **[analysis]** = read off source.

**First thing I did, per the brief's standing advice: `#print axioms` on what already exists.  It
redirected the round.**

## 12. Task 1 needed no work — it was landed last round, in commit `8fa3e6d`

The brief says `InjOneFact.lean` "exports only the codomain half" and asks for the domain half
plus the wiring.  **Both are already in HEAD** [machine]:

* `InjOneFact.lean:396` — `theorem PiLinkInvUC.piLinkInvDom (H : PiLinkInvUC env U) :
  PiLinkInvDom env U := fun hΓ h => (H hΓ h).1`.  The domain half is exported.
* `Theory/Typing/PiInvResidual.lean` (216 lines, 13 declarations) — the whole cheap route,
  including `convPiInv_of_convStep2_piLinkInvUC` and `convPiInv_of_shapeLinkAgree`, plus the
  five rows of §8.3.
* `git log -1 -- Lean4Lean/Theory/Typing/PiInvResidual.lean` → `8fa3e6d feat: ConvPiInv is free,
  hole B needs three conjuncts not five -- and COLLAPSE NINE, self-identified`.
* `lake build Lean4Lean.Theory.Typing.PiInvResidual` → **`Build completed successfully (84
  jobs).`**  All 13 `#print axioms` lines `[propext]` / `[propext, Quot.sound]` /
  `[propext, Classical.choice, Quot.sound]`; no `sorryAx`.

So the brief's task 1 is a restatement of §8, which already executed it.  **Nothing was
reproved and no budget was spent there.**  Consequences for the two questions task 1 asked:

* *"What does the corrected route make free downstream?"* — exactly §8.3's five rows, already
  landed and already graded (§8.4) as consolidating rather than strength-reducing.  Nothing new.
* *"Does the corner table's hole-B line move again?"* — **no.**  It moved once, from five
  conjuncts to three, in §8.3.  `docs/vacuity-ledger.md` row 138 records that; the corner table
  at **ledger line 15** still reads "the five conjuncts (incl. `PiInv`) `∧ ConvStep2`" and is the
  line to fix (I did not edit the ledger).  Nothing this round touches it.

## 13. Task 2: the answer is **NO — and it is a machine-checked refutation, not a difficulty**

New file **`/home/vasilii/lean4lean/Lean4Lean/Theory/Typing/AppUniqRefute.lean`** (38
declarations — 5 `def`s and 33 theorems, all `sorryAx`-free, all cone-holes `[]`).  Nothing else was touched.

> `piLvlEnv_appUniqLvl_all_false : ¬ ∀ n, piLvlEnv.AppUniqLvl 0 n`
> `piLvlEnv_ordered : Ordered piLvlEnv`

**`∀ n, AppUniqLvl` cannot be proved from `Ordered env`** — the hypothesis every current
consumer of it carries.

### 13.1 The witness, and why it is not the one `AppCase.lean` already had

The mechanism is `imax` degeneracy at the *domain*, which the tree had not used:

    C := Type 0        D₀ := Prop          D₁ := Type 0

    C : .sort 2,  D₀ : .sort 1,  D₁ : .sort 2
    (Type 0 → Prop)   : .sort (.imax 2 1) ≈ .sort 2
    (Type 0 → Type 0) : .sort (.imax 2 2) ≈ .sort 2      ← the same sort

So the `VDefEq` `⟨0, Type 0 → Prop, Type 0 → Type 0, .sort 2⟩` has **both sides typed at one
type**, which is all `Ordered.defeq` asks (`piLvlRule_wf`), while relating two Π-types whose
codomains disagree on propositionhood.  Then, in the one-entry context `[Type 0 → Prop]`:

    .bvar 0 : Type 0 → Prop                       (Lookup)
    .bvar 0 : Type 0 → Type 0                     (conv along the rule, one `extra` step)
    Prop    : Type 0                              (one `Stratified.sort`)
    .app (.bvar 0) Prop : Prop   and   : Type 0   (two `Stratified.app`s)

`piLvl_appData` is `AppCase.AppData` at this data, verbatim, and **both conversion premises of
`AppUniqLvl` are discharged by `.rfl`** — the two instantiated codomains are *literally* `Prop`
and `Type 0`, so not even the conversion-free specialisation of the case survives.

This is exactly the gap `AppCase.lean` §4 left open and said so: `witness_shapes` machine-checks
that `AppCaseRefute`'s witness supplies one sort-shaped type and one **stuck** type, hence "is not
a (sort, sort) pair", which is why it refutes `AppTypeUniq` and `UniqN` but leaves `AppUniqLvl`
alone.  This witness supplies two literal sorts. [machine]

### 13.2 What it closes

| statement | verdict at `piLvlEnv` |
| --- | --- |
| `∀ n, AppUniqLvl` (§9.2's single obligation) | **FALSE** (`piLvlEnv_appUniqLvl_all_false`) |
| `∀ n, PropUniqN.AppCase` (the tree's form) | **FALSE** (`piLvlEnv_appCase_all_false`) |
| `∀ n, PropUniqN` (the same by `propUniqN_iff_appCase_all`) | **FALSE** (`piLvlEnv_propUniqN_all_false`) |
| `∀ n, PropUniqNOn` (§9.3's guarded form) | **FALSE** (`piLvlEnv_propUniqNOn_all_false`) |
| `PropUniqZeroN` (the *only* instance route B applies) | **FALSE** (`piLvlEnv_propUniqZeroN_all_false`) |

The guard does not help: the witness context is genuinely well-formed — `piLvlL_isType`
(`OnCtx [piLvlL] (piLvlEnv.IsType 0)`) is `piLvlRule_wf`'s own first component, and
`piLvlL_isTypeN` / `piLvlL_onCtxN` give the indexed form at every `k+1`.  So **§9.3's weakening
and §11 item 3's proposed `SetModel/PropAgreeWall.lean` edit change nothing about
satisfiability** — they are still real weakenings of the *statement*, just not of what is
provable from `Ordered`.

`ordered_not_enough_for_propUniqN`, `..._appUniqLvl`, `..._propUniqNOn` state the negative in
the form a consumer reads: `¬ ∀ env, Ordered env → …`.

### 13.3 The instance route B consumes — named, refuted, and graded as a non-weakening

`propAgreeOn_of_stratifiedNOn` applies `pun` exactly twice, and in both places one universe is
literally `.zero`: `(pun _ hΓ (pta _ hΓ He He' hpA) HA').1 hrefl`.  So route B consumes only

    PropUniqZeroN :  Γ ⊢ₙ A : Prop  →  Γ ⊢ₙ A : .sort v  →  v ≈ 0

`PropUniqN.propUniqZeroN` is free.  **The converse is also free** at any index `k+1`
(`PropUniqZeroN.propUniqN`): `sortDF` turns `A : .sort u` with `u ≈ 0` into `A : Prop`.  The one
extra thing it needs is `u.WF U`, which `SortInvIndep.PropAgreeOn` supplies as `hu`.  So
**naming this instance is not a reduction** — graded as such up front, per the brief's rule —
and its only value is that the refutation reaches it too, which makes the negative stronger.

### 13.4 What it does **not** refute — the part that decides how much this is worth

1. **Not `VEnv.WF`.**  `piLvlEnv_not_wf`: a well-formed environment's rules are declaration
   rules and `DeclRules.IsDeclRule.lhs_ne_forallE` says none rewrites a Π-type.  So
   `∀ n, AppUniqLvl preludeEnv 0 n` is **still open**.  What the refutation establishes is where
   the proof's content has to come from: **any proof must consume `WF.defeq_isDeclRule` /
   `IsDeclRule.lhs_shape`**, and no argument that runs on `Ordered env` can exist.  That is
   §9.4's verdict for a *side condition*, now established for the **obligation itself**.
2. **Not `PropTypeAgreeN`, and provably not by any rule of this shape.**  The witness's two
   types are `Prop` and `Type 0`, neither of which is a *proposition*, so `PropTypeAgreeN`'s
   hypothesis `IsPropN A` is never met.  Stronger, and machine-checked:
   `imax_congr_agree_zero` — if a Π–Π rule sits at one type then `.imax c d₀ ≈ .imax c d₁`,
   and that already forces `d₀ ≈ 0 ↔ d₁ ≈ 0`.  **The `imax` slack that separates two sorts
   cannot separate a proposition from a non-proposition.**  So `∀ n, PropTypeAgreeN` is
   untouched at `piLvlEnv`, and so — as far as this witness goes — is route B's *conclusion*
   `PropAgreeOn`: at the witness the two type-universes are `1` and `2`, and `PropAgreeOn` asks
   only that they agree on being `0`, which they do. [machine for `imax_congr_agree_zero`;
   analysis for the reading of `PropAgreeOn` at the witness]
3. **Not "the corner is closed".**  `PropAgreeWall.nonempty_propSplit_preludeEnv` still gives
   `Nonempty (PropSplit preludeEnv 0)` with no hypotheses by route A (§10 item 5).  What dies is
   the *hole-free* route's `Ordered`-only formulation, not the corner.

### 13.5 A correction the brief and §9.2 both need: `RegPi` is not "unsatisfiable-unknown", it is **FALSE**

The brief carries the caveat "`RegPi` is **not known satisfiable**, so
`propTypeAgreeN_and_propUniqN_iff` is conditional", attributing it to §9.2, which says the same.
**Both understate it.**  `Theory/Typing/RegPiSat.lean:117` has

    theorem regPi_false : ¬ env.RegPi U n

for **every** environment, every `U`, every `n` — the witness is the one-entry context
`[.forallE (.bvar 0) (.bvar 0)]`, where `Lookup` hands back a Π whose components are untypeable.
`regPi_all_false` (this file) is the `∀ n` form.  So `propTypeAgreeN_and_propUniqN_of` and
`propTypeAgreeN_and_propUniqN_iff` are not conditional — they are **vacuous, unconditionally, at
every environment**, and no satisfiability work on `RegPi` is possible.  `RegPiSat.lean` already
supplies the repair (`RegPiOn` / `Regular`, from `EnvReg` + `InstLvl` + `RegConvE`), and §9.2
should be restated against `propTypeAgree_appCase_on_of` rather than
`propTypeAgree_appCase_of`.  `propUniqN_iff_appCase_all` is unaffected, exactly as §9.2 and the
brief both say.  [machine: `regPi_false` is `sorryAx`-free on this commit, cone 682, holes `[]`]

### 13.6 What I tried that failed, and the step it failed at

1. **Prove `∀ n, PropUniqN` from the unstratified `SortUniq`** — which `PiInvResidual.sortUniq_of_shapeLinkAgree`
   now supplies hole-free from `Ordered ∧ ConvStep2 ∧ ShapeLinkAgree`.  **Failed at the bridge**:
   there is no `HasTypeN → HasType`.  `Theory/Typing/Stratified.lean:~322` says so explicitly and
   says why — "the converse `IsDefEqN n → IsDefEqU` is *not* proved here … it needs
   `IsDefEq.uniq`, because `IsDefEqN`'s `conv` rule is three-place while `IsDefEq.defeqDF`
   demands a type."  Worth recording as a *positive*: it means the stratified obligation is **not
   equivalent** to the unstratified corner, so §9.2's target is genuinely separate content and
   the composition I was about to build (which would have been collapse ten) does not exist.
2. **Refute `AppUniqLvl` over the empty environment**, as `AppCaseRefute` does for `AppTypeUniq`.
   **Failed at the shape of the obstruction**: the only device that breaks the index over `∅` is
   an instantiation that blocks a `beta` step (`SubstCRefute.inst_does_not_preserve_index`), and a
   blocked redex is **stuck** — `SubstCRefute.stuck` says it is `⊢₁`-related to nothing but
   itself, so it is not convertible to a sort, and `AppUniqLvl` needs *both* codomains
   sort-convertible.  Every variation I tried collapsed to one of: the redex unblocks (and then
   the two sorts coincide), or it stays stuck (and the premise is unmet).  That is why the
   refutation needs an environment rule, and why it lands at `Ordered` rather than `∅`.
3. **Prove `SortDisjInvN piLvlEnv 0 1`**, to upgrade the refutation to "not implied by
   `Ordered ∧ ∀ n, SortDisjInvN`".  **Failed at the `beta` case** of a `SubstCRefute.stuck`-style
   induction: a sort *is* `⊢₁`-convertible to a β-redex (`symm` of `beta` whose reduct is a
   sort), so no shape-class invariant is preserved and the case is the general weak-head
   confluence problem — the hole itself.  **Not claimed either way.**  See §13.7.

### 13.7 Not established — and it is the first thing to pick up

Whether `piLvlEnv` satisfies **`SortDisjInvN` at index 1** (clause (1) `SortInvN` and clause (3)
`SortForallEDisjN`).  Neither is refuted by the rule: it relates two **Π**-types, so it respects
both shapes — contrast `SortClauses.sortPiEnv`, whose rule relates a sort to a Π and refutes
clause (3) outright (§9.4).  This matters because it decides the strength of §13:

* if they **hold**, then `∀ n, AppUniqLvl` is not implied by `Ordered env ∧ ∀ n, SortDisjInvN`
  either, and §9.2's four side conditions provably do not rescue the obligation;
* if one **fails**, §13 is the weaker statement "`Ordered` alone is not enough", which is still
  what route B needs and still decisive for route B, but no longer separates the obligation from
  its side conditions.

### 13.8 The grade

**This is a refutation, not a reduction**, so the collapse trap that caught rows 51, 86, 94 and
collapses eight and nine does not apply: there is no target here that could turn out equivalent
to what it was reduced from.  What *does* need saying, in the brief's own vocabulary:

* **hole-free ≠ discharged, and this is the third shape of that.**  §9.2's assembly is hole-free
  and discharges nothing because its fifth hypothesis is its own second conclusion.  §13.5 adds:
  it is also *vacuous*, because `∀ n, RegPi` is false at every environment.  And §13 adds: the
  one surviving obligation is *false* at the hypothesis its consumers carry.  Three independent
  reasons the hole-free route pays nothing as currently stated.
* **What is genuinely new**: (i) a (sort, sort) counterexample to the shared `app` case, which
  `AppCase.lean` §4 explicitly did not have; (ii) the `imax`-at-the-domain device, which is what
  makes an `Ordered` rule able to separate two sort levels; (iii) the machine-checked proof that
  the same device *cannot* separate propositionhood (`imax_congr_agree_zero`), which is why
  `PropTypeAgreeN` survives and `PropUniqN` does not; (iv) the localisation of the remaining
  content to `IsDeclRule.lhs_shape`.

### 13.9 Verification, verbatim [machine]

* `lake build Lean4Lean.Theory.Typing.AppUniqRefute`: **`Build completed successfully (96
  jobs).`**  `lake build Lean4Lean.Theory.Typing.PiInvResidual`: **`Build completed successfully
  (84 jobs).`**  No error in any file I own.
* `#print axioms`, one per declaration, in the file (`section Audit`), checked at build time.
  **33 lines**: 32 report `[propext]`, `[propext, Quot.sound]` or `[propext, Classical.choice,
  Quot.sound]`, and one (`piLvlEnv_defeqs`) reports *does not depend on any axioms*.  **No
  `sorryAx`, no frozen axiom, no new `sorry`, none traded.**
* Cone measurement — forward walk over **type and value**, `allowOpaque := true`, private copy of
  `scripts/hole-cone.lean`'s algorithm, 38 seeds (my 33 + 5 upstream ingredients) plus 4
  controls.  **All 33 report `holes []`**: `piLvlRule_wf` 1502, `piLvlEnv_ordered` 1510,
  `piLvlEnv_defeqs` 32, `piLvlEnv_not_wf` 1885, `piLvlEnv_conv` 607, `piLvl_fn₀` 163, `piLvl_fn₁` 620, `piLvl_arg` 63,
  `piLvl_appData` 625, `piLvlEnv_appUniqLvl_false` 654, `piLvlEnv_appUniqLvl_all_false` 655,
  `piLvlEnv_appCase_false` 663, `piLvlEnv_appCase_all_false` 664, `piLvl_witness₀` 208,
  `piLvl_witness₁` 628, `piLvlEnv_propUniqN_false` 653, `piLvlEnv_propUniqN_all_false` 654,
  `piLvl_witness` 1556, `piLvlL_isType` 1556, `piLvlL_onCtx` 1560, `piLvlL_isTypeN` 624,
  `piLvlL_onCtxN` 629, `piLvlEnv_propUniqNOn_false` 1581, `piLvlEnv_propUniqNOn_all_false` 1582,
  `ordered_not_enough_for_propUniqN` 1558, `ordered_not_enough_for_appUniqLvl` 1559,
  `ordered_not_enough_for_propUniqNOn` 1586, `imax_congr_agree_zero` 1514, `regPi_all_false` 683,
  `PropUniqN.propUniqZeroN` 589, `PropUniqZeroN.propUniqN` 583,
  `piLvlEnv_propUniqZeroN_false` 652, `piLvlEnv_propUniqZeroN_all_false` 653.
  Upstream ingredients also clean: `regPi_false` 682, `AppUniqLvl.iff` 682,
  `PropUniqN.appCase_iff` 1651, `propUniqN_iff_appCase_all` 1652,
  `propAgreeOn_of_stratifiedNOn` 2410 — all `holes []`.
* **The instrument fires** on all four controls, so an empty cone here means something:
  `piInv_axiom` 3539 `[forallE_inv_stratified, rigidShapeUniqNS]`; `WF.sortUniq'` 3404
  `[forallE_inv_stratified]`; `IsDefEqU.sort_inv` 3409 `[forallE_inv_stratified]`;
  `WF.proofTransport` 3408 `[forallE_inv_stratified]`.  All four big holes were confirmed
  *present in the environment* before the run (`BIGHOLE … present=true`), so a `[]` is not a
  missing-name artefact.
* **Tooling**: `lean_local_search` / `lean_hammer_premise` remain dead (`rg` absent) —
  confirmed again.  Every search claim in §12–§13 is backed by **`grep`**, by `git log`/`git
  log -S`, or by `lake build` / `lake env lean`.  `lean_references` was not needed.
* **Not run, deliberately, per the brief**: full `lake build`, the three guards,
  `scripts/sorry-census.lean`, `scripts/dup-names.lean`, `MemberRedexScan`.  Two other streams
  are editing `Theory/SetModel/*` and `Theory/Inductive/*` concurrently.  The only pre-existing
  `sorry` warnings my module build surfaces are in `Theory/Inductive/Decl.lean:405` and
  `Theory/Typing/Injectivity.lean:261,1046` — none of them mine, none of them new.

## 14. Where the brief was wrong — one list

1. **Task 1 was already done**, in commit `8fa3e6d`, including the domain export at
   `InjOneFact.lean:396`.  The brief describes it as "the missing export … reportedly one line of
   work"; there is nothing missing.  §12.
2. **`RegPi` is false, not merely "not known satisfiable"** — at every environment, every `U`,
   every `n` (`RegPiSat.regPi_false`).  So `propTypeAgreeN_and_propUniqN_iff` is *vacuous*, not
   *conditional*, and §9.2's own caveat understates it in the same way.  §13.5.
3. **"`∀ n, AppUniqLvl` is now the whole remaining syntactic import of the model side on the
   hole-free route"** — true as a *location* claim, and now known to be **false at the hypothesis
   the route carries**.  The right statement is: it is the whole remaining import *and* it is not
   provable from `Ordered env`, so the hole-free route must be restated at `VEnv.WF` before the
   sentence means anything.  §13.
4. Correct in the brief, and confirmed: `propUniqN_iff_appCase_all` carries no `RegPi` caveat;
   the `rg` tooling is dead; the standing advice to `#print axioms` first was decisive (it saved
   the whole of task 1); and separating "hole-free" from "discharged" is right — §13.8 finds a
   third independent reason the route pays nothing.

## 15. What to pick up first

1. **`SortDisjInvN` at `piLvlEnv`, index 1** (§13.7).  Cheapest thing that changes the meaning of
   §13.  If it holds, §9.2's side conditions are provably no rescue.
2. **Restate the whole `∀ n` family at `VEnv.WF`, not `Ordered`.**  §9.4 said this for a side
   condition; §13 makes it mandatory for the obligation.  Concretely:
   `PropAgreeGuarded.propAgreeOn_of_stratifiedN` / `propAgreeOn_of_stratifiedNOn` and
   `SetModel/PropAgreeWall.propTypeAgreeOnCtx_of_stratifiedN` should take `env.WF`.  `preludeEnv`
   is `WF`, so nothing is lost.  Until then their hypotheses are **refuted**, not merely open.
3. **Attack `∀ n, AppUniqLvl` at `VEnv.WF` through `IsDeclRule.lhs_shape`** (§13.4 item 1).  The
   refutation says exactly what a proof must use, and `DeclRules.lean` already has it. The shape
   of the argument: at a `WF` environment no rule rewrites a Π, so a function's two Π-types are
   related only by `forallEDF`/`trans`/`symm`/`beta`/`appDF`/`eta`/`proofIrrel` and δ-rules on
   constants; §13.6 item 2 is then the reason the two instantiated codomains cannot be two
   *different* sorts.  That is a sketch, **not** a proof, and it is the round's main open item.
4. **Re-price §9.2 against `RegPiSat`** (§13.5): replace `propTypeAgree_appCase_of` with
   `propTypeAgree_appCase_on_of` and `RegPi` with `RegPiOn`/`Regular`, so the assembly stops
   being vacuous.  Pure bookkeeping in `Theory/Typing`, no new mathematics.
5. **Ledger rows to write** (I did not edit `docs/vacuity-ledger.md`):
   * corner table **line 15**: hole B is **three** const-spine conjuncts `∧ ConvStep2 ∧
     ShapeMidShapeless`, not five `∧ ConvStep2` — row 138 already says so, the table was not
     updated;
   * a row for §13 — `∀ n, AppUniqLvl` / `∀ n, PropUniqN` **false at an `Ordered` environment**,
     guard and `u = .zero` instance included, `VEnv.WF` untouched;
   * a row for §13.5 — `RegPi` is **false at every environment**, so
     `propTypeAgreeN_and_propUniqN_of`/`_iff` are vacuous rather than conditional;
   * a row for §13.6 item 1 — there is no `HasTypeN → HasType`, so the stratified obligation is
     **not** equivalent to the unstratified corner (the one place this round a collapse was
     available and turned out not to exist).

# Round 4 (2026-09-02, later still): item (c) is **closed, not expensive** — and §13.6's diagnosis of it was wrong

Appended, not editing §0–§15.  Conventions unchanged: **[machine]** = a `sorry`-free
declaration on this commit plus `lake build` / `#print axioms` / a cone run; **[analysis]** =
read off source.

**One-line answer to §13.5/§13.7 item (c): `SortDisjInvN piLvlEnv 0 1` is neither proved nor
refuted, and it cannot be either cheaply — it is *sandwiched between two open statements*, and
the lower bound is an empty-environment clause the tree has had open since `DefInvRefute`.  The
`beta` case that §13.6 item 3 blamed is FREE.  The obstruction is `appDF`.**

New file **`/home/vasilii/lean4lean/Lean4Lean/Theory/Typing/SortDisjPiLvl.lean`** (39
declarations, all `sorryAx`-free, all cone-holes `[]`).  Nothing else in the tree was touched.

## 16. First, what `#print axioms` said — and the machinery §13.6 did not know about

Per the standing advice, everything the brief named was checked before anything was proved.
All of it is as claimed [machine]: `piLvlEnv_ordered` `[propext, Quot.sound]`,
`piLvlEnv_appUniqLvl_all_false` `[propext]`, `piLvlEnv_propUniqZeroN_false` `[propext]`,
`RegPiSat.regPi_false` `[propext]` (with `RegPiOn`/`Regular` present as the repair, as §13.5
says), `regPi_all_false` `[propext]`.  No `sorryAx` in any of them.  **The brief was right on
every point I could check.**

What the check *did* turn up is that round 3 duplicated existing work:

* **`Theory/Typing/SortClauses.lean` §4 already contains the right predicate for this exact
  job**, and has since before round 3: `SortRed u X` ("`X` weak-head β-reduces to a sort of
  level `≈ u`"), `SortRedInv` (its invariance along a `⊢ₙ` conversion), and
  `sortRedInv_of` — which proves `SortRedInv` at `n+1` from **four** residuals at `n`.  In
  that induction `rfl`, `symm`, **`trans`**, `sortDF`, `constDF`, `lamDF`, `forallEDF` **and
  `beta`** all close outright.  `SortRed.beta_iff` is the `beta` case, one line.
* `Theory/Typing/SortRedApp.lean` (114 declarations) then narrows the surviving residual to one
  branch and names it `SortRedLamExpose`, with `docs/handoff-sortred.md` as its handoff.

So **§13.6 item 3 is wrong in its diagnosis** [machine].  Its report — "failed at the `beta`
case … a sort *is* `⊢₁`-convertible to a β-redex … so no shape-class invariant is preserved and
the case is the general weak-head confluence problem" — has a true premise and a false
conclusion.  The premise is exhibited over `piLvlEnv` itself (`piLvlRedex_conv_sort`:
`fun (_ : Type 0) => Prop` applied to `Prop` is `⊢₁`-convertible to `Prop`), and
`piLvlRedex_sortRed_iff` shows `SortRed` does not care.  What that fact defeats is a *syntactic
shape class*, which is what a `SubstCRefute.stuck`-style induction carries — not the invariant
the tree already uses.  `beta_and_trans_are_free` records both free cases in one statement.

**The brief inherited the wrong diagnosis and asked me to confirm it** ("establish sharply that
the `beta` case genuinely is weak-head confluence").  It is not; the `appDF` case is.

## 17. What is proved [machine]

| statement | declaration |
| --- | --- |
| `piLvlEnv`'s rule is invisible to `SortRed` — the `extra` residual is free | `extraSortRed_piLvlEnv` |
| a Π-type is never `⊢₀`-typed at a Π-type (companion to `forallE_not_prop0`) | `forallE_not_pi0` |
| the rule's two sides are not `⊢₀`-typed at a Π-type, so `extra` cannot be an `appDF`'s `f ≡ f'` | `piLvl_rule_not_pi_typed0` |
| …and their `⊢₀` types differ *syntactically* (`.imax 2 1` vs `.imax 2 2`), so it cannot be its `a ≡ a'` either | `piLvl_rule_sides_not_one_type0` |
| `SortRedAppDF piLvlEnv 0 0 → SortDisjInvN piLvlEnv 0 1` (both clauses) | `piLvlEnv_sortDisjInvN_one_of_appDF` |
| …and from the narrowed form | `piLvlEnv_sortDisjInvN_one_of_lamExpose` |
| the residual **is** the whole reduction here, as over `∅` | `piLvlEnv_sortRedAppDF_iff`, `piLvlEnv_chain` (three `↔`s) |
| `⊢ₙ` conversions transfer up an environment extension (**new**, `Stratified.mono` is index-only) | `Stratified.mono_env` |
| clauses (1)/(3)/both are antitone in the environment | `SortInvN.mono_env`, `SortForallEDisjN.mono_env`, `SortDisjInvN.mono_env` |
| **the lower bound**: `SortDisjInvN piLvlEnv 0 1 → SortDisjInvN ∅ 0 1` | `sortDisjInvN_le` |
| a refutation over `∅` at `U = 0` refutes item (c) outright | `sortInvN_empty_false_imp` |
| `⊢ₙ` conversions transfer up a universe-count extension (**new**) | `VLevel.WF.mono_univs`, `Stratified.mono_univs` |
| the sandwich in one statement, incl. `SortInvN ∅ 1 1 → SortInvN ∅ 0 1` | `sortDisjInvN_sandwich` |
| **§13.7's separation, index-1 form, conditional on the residual** | `piLvlEnv_separates_at_one`, `ordered_and_sortDisjInvN_not_enough_at_one` |
| **§13.7's separation, `∀ n` form** — needs **three** open families, not one | `sortDisjInvN_all_of`, `piLvlEnv_sortDisjInvN_all_of`, `ordered_and_sortDisjInvN_all_not_enough_of` |
| **new refutation**: the spine predicate with each argument `⊢₀`-typed at *some* type is FALSE | `spineInvTyped_one_false` |
| **new necessary sub-obligation**: the residual also demands *argument replacement* | `SortRedArgSwap`, `sortRedArgSwap_of_lamExpose` |

### 17.1 The answer to §13.7's question, stated exactly

§13.7 asks which branch holds, and says the positive branch would show "§9.2's four side
conditions provably do not rescue the obligation".  Both branches are now priced:

* **Positive branch — not reachable today.**  `SortDisjInvN piLvlEnv 0 1` *implies*
  `SortDisjInvN ∅ 0 1` [machine, `sortDisjInvN_le`], which is open: it is the `U = 0` instance
  of the clause `DefInvRefute` left at `U = 1`, and §8 of the new file machine-checks that the
  `U = 1` instance implies the `U = 0` one, so the tree has *nothing* that discharges either.
  The separation is therefore landed as a **conditional theorem** on the residual, in both the
  index-local form (one hypothesis) and the `∀ n` form (three).
* **Negative branch — cannot come from the rule.**  `extraSortRed_piLvlEnv` says the rule is
  invisible to `SortRed`; `piLvl_rule_not_pi_typed0` and `piLvl_rule_sides_not_one_type0` say it
  cannot fire at any of the four typing positions of the residual.  And a refutation that did
  *not* use the rule would refute the `∅` clause, which by `sortInvN_empty_false_imp` settles
  item (c) as a corollary.  So there is no cheap negative either.

**So §15 item 1 — "`SortDisjInvN` at `piLvlEnv`, index 1 … cheapest thing that changes the
meaning of §13" — is wrong.  It is the most expensive item on that list**: it entails the
tree's oldest open index-1 clause.  §15 item 3 (attack `∀ n, AppUniqLvl` at `VEnv.WF` through
`IsDeclRule.lhs_shape`) is the one that does not sit behind that wall.

### 17.2 The grade — where I could be collapsing, said up front

* The route in §3 of the new file is a **sufficient condition, not a reduction**:
  `SortRedInv → SortDisjInvN` is one-way and no converse is known, so `SortRedAppDF piLvlEnv 0 0`
  is **possibly strictly stronger** than item (c).  I have *not* shown item (c) is as hard as
  the residual.  Graded as such in the file's Verdict section.
* The only **real** lower bound is `sortDisjInvN_le` (§4), and what it bounds by is
  `SortDisjInvN ∅ 0 1` — *not* the residual and *not* the `U = 1` goal the tree tracks.  The
  precise relationship is machine-checked in §8 rather than read off, because getting it wrong
  in the optimistic direction is exactly this corner's failure mode.
* **Hole-freeness is reported separately from dischargedness, as always.**  All 39 declarations
  are hole-free (cones below).  **Nothing here is discharged**: every conclusion about
  `SortDisjInvN piLvlEnv 0 1` is under a hypothesis, and that hypothesis is open.  This is a
  *fourth* shape of "hole-free ≠ discharged" to set beside §13.8's three: an assembly all of
  whose conclusions are conditional on a statement that is open, at an environment where the
  hypothesis is at least as strong as a known-open goal.

## 18. What I tried that failed, and the step it failed at

1. **Proving `SortRedLamExpose piLvlEnv 0 0` (equivalently the residual) by induction on the
   conversion `f ≡₁ f'`.**  Failed at the **`trans` case**, and for a reason that is a hard
   constraint rather than a difficulty: `Stratified.trans` carries **no typing premise for its
   middle term**, while the induction hypothesis needs `f` `⊢₀`-typed at `.forallE A (.sort w)`
   — the premise that protects `f` and `f'` from `proofIrrel` (`proofIrrel_not_at_pi`) and from
   `constDF`.  Not abandoned for lack of effort: this is the same wall `docs/handoff-sortred.md`
   §8 item 2 names, and I add one machine-checked step to it (item 2 below).
2. **The intermediate repair — a spine predicate whose arguments are `⊢₀`-typed but not at the
   function's domain.**  This is the natural next design point after
   `SortRedApp.spineInv_one_false` (typing-free) and before §8 item 2's domain-tied spine.
   **Refuted** (`spineInvTyped_one_false`), at `SortRedApp.ArgWitness`'s own witness: the
   separating argument `Prop` *is* `⊢₀`-typed, at `.sort 1`.  So the strengthened predicate has
   to tie the argument's type to the function's **domain**, and a `trans` midpoint has no
   domain — the two horns of the dilemma are now
   `SortRedApp.sortRedAppDF_needs_arg_typing` (arg typing is load-bearing) and this.  **This is
   what "closed rather than expensive" means concretely.**
3. **Refuting `SortDisjInvN piLvlEnv 0 1` using the rule.**  Failed at the shape of the rule:
   both its sides are Π-types, so neither weak-head reduces at all (`extraSortRed_piLvlEnv`),
   and the two `⊢₀`-typing positions where it might have entered are closed by
   `piLvl_rule_not_pi_typed0` / `piLvl_rule_sides_not_one_type0`.  Recorded as a *positive*: it
   is why the environment contributes nothing to this question either way.
4. **Looking for a `Stratified` environment-monotonicity lemma to reuse.**  There is none —
   `Stratified.mono` is monotonicity in the *index* only.  `Stratified.mono_env` and
   `Stratified.mono_univs` are new here; both are 20-line inductions and both are generally
   useful (they are what make §4 and §8 possible at all).  Search backed by **`grep`** and
   `lean_references`; `lean_local_search` / `lean_hammer_premise` remain dead (`rg` absent) —
   confirmed again this round.
5. **Deciding `SortRedArgSwap`** (§9 of the new file, the argument-replacement half).  Not
   attempted beyond establishing necessity: an attempted refutation reduces to finding two
   `⊢₁`-convertible terms at one Π-type of which only one exposes a sort-reaching λ, which *is*
   the residual.  Recorded because it is `SubstC`-shaped and `SubstC` is **false** — so this is
   the most promising place to look for a *refutation* of the residual, and refuting the
   residual would not refute the clauses (`SortRedInv → SortDisjInvN` is one-way).

## 19. Where the brief was wrong — one list

1. **"the `beta` case of a `stuck`-style induction is the general weak-head-confluence
   problem"** (from §13.6 item 3, repeated in the brief as the thing to establish).  **False as
   a statement about this route**: `beta` and `trans` are both free against `SortRed`
   (`SortRed.beta_iff`, `Iff.trans`), and the obstruction is `appDF`.  The brief's *spirit* —
   that the residual is weak-head-confluence-flavoured — is right: the residual is λ-exposure
   invariance plus argument replacement.
2. **"prove it, or establish that this route is closed rather than expensive"** — the right
   answer is neither of the two the brief expected.  The route is **closed against cheap
   attack** (§18 items 2–3) *and* item (c) is **not decidable without an open clause** (§17.1),
   which is stronger than "expensive" and weaker than "impossible".
3. **§13.7's framing that one of the two branches must be reachable.**  Neither is, today.  What
   *is* reachable, and is landed, is the separation **conditional on the residual** — which is
   worth having, because it is exactly the form §9.2's consumers would use.
4. Correct in the brief, and confirmed: `RegPi` is false at every environment; `piLvlEnv`
   appears in exactly one file and nobody had touched `SortDisjInvN` at it; the `rg`-backed
   tools are dead; and the instruction to `#print axioms` first paid again — it is what found
   `SortClauses.lean` §4 and stopped me re-deriving `sortRedInv_of` by hand.

## 20. Verification, verbatim [machine]

* `lake build Lean4Lean.Theory.Typing.SortDisjPiLvl`: **`Build completed successfully (98
  jobs).`**  No error in any file I own.  **Not run, per the brief**: full `lake build`, the
  three guards, `scripts/sorry-census.lean`, `scripts/dup-names.lean`, `MemberRedexScan`.
* `#print axioms`, **39 lines**, one per declaration, checked at build time: 25 `[propext]`,
  11 `[propext, Quot.sound]`, 3 *does not depend on any axioms*
  (`VLevel.WF.mono_univs`, `empty_le_piLvlEnv`, `headBetaS_lam_inv`).  **No `sorryAx`, no frozen
  axiom, no new `sorry`, none traded.**
* **Cone measurement** — forward walk over **type and value**, `allowOpaque := true`, private
  copy of `scripts/hole-cone.lean`'s algorithm; 39 seeds (mine) + 6 upstream ingredients + 4
  controls.  **All 45 non-control seeds report `holes []`.**  Sizes:
  `Stratified.mono_env` 644, `SortInvN.mono_env` 647, `SortForallEDisjN.mono_env` 647,
  `SortDisjInvN.mono_env` 654, `extraSortRed_piLvlEnv` 627, `forallE_not_pi0` 672,
  `piLvlL_type0` 66, `piLvlR_type0` 66, `piLvl_rule_not_pi_typed0` 681,
  `piLvl_rule_sides_not_one_type0` 792, `piLvlEnv_sortRedInv_one_of_appDF` 2002,
  `piLvlEnv_sortRedAppDF_iff` 2004, `piLvlEnv_chain` 2048,
  `piLvlEnv_sortInvN_one_of_appDF` 2005, `piLvlEnv_sortForallEDisjN_one_of_appDF` 2005,
  `piLvlEnv_sortDisjInvN_one_of_appDF` 2011, `piLvlEnv_sortDisjInvN_one_of_lamExpose` 2051,
  `empty_le_piLvlEnv` 43, `sortInvN_le` 661, `sortForallEDisjN_le` 661, `sortDisjInvN_le` 668,
  `piLvlEnv_separates_at_one` 2026, `ordered_and_sortDisjInvN_not_enough_at_one` 2026,
  `sortDisjInvN_all_of` 722, `piLvlEnv_sortDisjInvN_all_of` 730,
  `ordered_and_sortDisjInvN_all_not_enough_of` 1652, `piLvlRedex_conv_sort` 202,
  `piLvlRedex_sortRed_iff` 626, `beta_and_trans_are_free` 629, `spineInvTyped_of_spineInv` 43,
  `spineInvTyped_one_false` 701, `Stratified.mono_univs` 641, `VLevel.WF.mono_univs` 62,
  `SortInvN.mono_univs` 644, `SortForallEDisjN.mono_univs` 644, `sortDisjInvN_sandwich` 673,
  `sortInvN_empty_false_imp` 662, `headBetaS_lam_inv` 179, `sortRedArgSwap_of_lamExpose` 215.
  Upstream ingredients also clean: `sortRedInv_of` 697, `sortRedAppDF_of_sortBranch` 1213,
  `sortRedAppDFSort_iff_lamExpose` 1181, `spineInv_one_false` 667,
  `piLvlEnv_appUniqLvl_false` 654, `piLvlEnv_ordered` 1510.
* **The instrument fires**, so `[]` means something: `piInv_axiom` 3539
  `[forallE_inv_stratified, rigidShapeUniqNS]`; `WF.sortUniq'` 3404
  `[forallE_inv_stratified]`; `IsDefEqU.sort_inv` 3409 `[forallE_inv_stratified]`;
  `WF.rigidShapeUniqNS` 630 `[rigidShapeUniqNS]`.
* **All four big holes were verified *present in the measuring environment*** before the run —
  `forallE_inv_stratified`, `rigidShapeUniqNS`, `IsDefEqU.weakN_iff` and `NormalEq.descend` all
  `present=true` (the last two required importing `UniqueTyping`/`ChurchRosser` into the
  measuring script; my module's own import closure does not reach them, which is a *stronger*
  statement than their absence from a cone).  So no `[]` here is a missing-name artefact.
  Every declaration's cone contains **none of the four**.

## 21. What to pick up first

1. **`SortRedLamExpose ∅ 1 0` — but only with the two horns of §18 item 2 in hand.**  It is
   still the whole of clauses (1) and (3) at index 1, and it is now known to have *two* halves:
   λ-exposure and argument replacement (`SortRedArgSwap`).  Attack the second first: it is the
   `SubstC`-shaped one, `SubstC` is false, and a refutation there kills the residual (though not
   the clauses).
2. **§15 item 3 — `∀ n, AppUniqLvl` at `VEnv.WF` through `IsDeclRule.lhs_shape`.**  This is the
   item that does *not* sit behind the index-1 wall, and §13.4 item 1 already localises the
   content.  It should be re-ranked above item 1 of §15.
3. **Reuse `Stratified.mono_env` / `Stratified.mono_univs`.**  They did not exist; several
   witness files could be shortened by them, and any future "witness environment" argument needs
   the antitonicity direction to know which way its statement transfers.
4. **Ledger rows to write** (I did not edit `docs/vacuity-ledger.md`):
   * a row for §16 — round 3 rediscovered a problem the tree had already reduced, and blamed the
     wrong case (`beta` is free; `appDF` is the residual).  The lesson is the one this project
     keeps relearning: `grep` the tree for the *predicate*, not only for the statement name;
   * a row for §17.1 — item (c) is sandwiched between two open statements, so §15 item 1's
     "cheapest" is wrong; the separation is landed **conditionally**, in both forms;
   * a row for §18 item 2 — `SpineInvTyped` is FALSE, so the argument typing in the residual
     must be **domain-tied**, which `trans` cannot supply;
   * a row for §9 of the new file — `SortRedArgSwap`, a second necessary half of the residual,
     non-trivial already at `f = f'`.
