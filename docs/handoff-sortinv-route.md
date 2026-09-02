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
