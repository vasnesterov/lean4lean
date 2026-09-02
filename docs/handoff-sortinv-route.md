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
