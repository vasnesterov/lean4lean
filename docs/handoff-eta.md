# The two eta holes: residual reduced to **one** abstract rule (round of 2026-09-02)

Stream owning `Lean4Lean/Verify/TypeChecker/IsDefEq.lean` and new files under
`Verify/TypeChecker/`.  Targets: `TypeChecker.Inner.isDefEqUnitLike.WF` (70 transitive users) and
`TypeChecker.Inner.tryEtaStructCore.WF` (71).

Every claim below is tagged **[measured]** (I ran it this round; the command or declaration name is
given) or **[source]** (read off source or a prior document, not re-run).  Nothing is from memory.
Earlier rounds of this corner are in `docs/vacuity-ledger.md` rows 99–110 and
`docs/research-structeta.md`; this file supersedes the previous edition of `handoff-eta.md`,
whose state (census 19, `StructEta` before the `IsStructureG` widening) is two rounds stale.

---

## Bottom line

1. **Neither hole is closed, and neither can be closed honestly in this tree.**  Both are
   *provable today* by a one-line vacuity argument, which I declined; see §4 for the exact lines
   and the measurement that says the close would buy nothing on guard 2.
2. **What did change: the residual is now ONE hypothesis for BOTH holes, where it was two each.**
   New file `Lean4Lean/Verify/TypeChecker/EtaResidual.lean` (mine, 224 lines, `sorry`-free):
   `isDefEqUnitLike.WF` and `tryEtaStructCore.WF` (and `tryEtaStruct.WF`) all follow from
   `c.venv.StructEtaG` **and nothing else** — `etaHoles_of_structEtaG` states all three in one
   theorem.  **[measured]**
3. Three of the four residual hypotheses were removed, each by a named theorem:
   `VEnv.StructEtaG.toUnitEta` (the positive-field rule subsumes the zero-field one),
   `UnitLikeBridgeG.today` (the zero-field bridge is vacuously satisfiable today — the
   counterpart of `EtaStructSpineGC.today`, which had no zero-field twin), and
   `EtaStructSpineGC.today` (pre-existing, applied).  **[measured]**
4. **Both claims I was asked to check are true**, with one qualifier the second needs (§2).
5. **Correction to the brief: neither hole is in `kernel_sound`'s dependency cone today**, so
   closing them cannot move guard 2's axiom set.  `kernel_sound`'s cone is 7914 constants and its
   *only* hole is itself; `addDecl.WF`'s cone is 1 constant — itself.  Both are bare `sorry`s with
   no proof body, so the route from the checker's `.WF` layer to the main theorem is currently
   severed at those two points, not at the eta holes.  **[measured]**  (Consistent with ledger row
   107g, which measured the same thing from the other side.)
6. The only route that discharges `StructEtaG` is a new `VEnv.IsDefEq` constructor.  Re-measured
   price: **65 induction sites** over the `IsDefEq`/`IsDefEqStrong`/`HasTypeStrong`/
   `HasTypeStratified` family, in 15 modules, **none of them in `Verify/`** — reproducing
   `docs/handoff-isdefequ.md` §4's figure exactly.  **[measured]**  All 65 are in files this
   stream does not own, so it is not a job for this stream alone.

**Instruments, run at the end of the round.**  `lake build`: **1499 jobs, completed
successfully, zero errors** (1497 jobs before my file was added; it is picked up by the
`Lean4Lean.Verify.*` glob, so it is in the default build).  Zero errors in files I own.  `lake build
Lean4Lean.Experimental.ConeJoin Lean4Lean.Verify.Guard`: 1423 jobs, verbatim —

```
guard 1: Axioms.lean declares exactly the 24 frozen axioms ✓
guard 2: kernel_sound axioms within whitelist ✓ (proof INCOMPLETE: sorryAx present)
guard 3: checker cone implementation gaps within frozen list (2/2 remaining) ✓
```

`scripts/sorry-census.lean`: **TOTAL 13**, unchanged, with my two rows unchanged —

```
Lean4Lean.Verify.TypeChecker.IsDefEq: 2
    Lean4Lean.TypeChecker.Inner.isDefEqUnitLike.WF   [70 transitive users]
    Lean4Lean.TypeChecker.Inner.tryEtaStructCore.WF  [71 transitive users]
```

No `sorry` added, none removed, no `sorryAx` traded for another.

---

## 1. What I added, and its axioms  **[measured]**

`Lean4Lean/Verify/TypeChecker/EtaResidual.lean`.  `#print axioms` on every declaration:

| declaration | axioms |
|---|---|
| `VEnv.StructEtaG.toUnitEta` | `[propext, Quot.sound]` |
| `TypeChecker.Inner.UnitLikeBridgeG.today` | `[propext, Classical.choice, Quot.sound]` |
| `isDefEqUnitLike.WF_of_structEtaG` | `[propext, sorryAx, Classical.choice, Quot.sound]` |
| `tryEtaStructCore.WF_of_structEtaG'` | `+ Lean.Expr.eqv_eq, Lean.Level.instLawfulBEqLevel, Lean.Syntax.structEq_eq` |
| `etaHoles_of_structEtaG` | same as the row above |
| `MutField.declEnv_IsStructureG_0`, `declEnv_unitEta_premises`, `declEnv_unitEta_of_structEtaG`, `declEnv_unitLike_of_structEtaG`, `declEnv_Amk`, `declEnv_Amk_hasType` | `[propext, Classical.choice, Quot.sound]` |

**No new frozen-axiom dependency.**  The three `Lean.*` axioms are frozen (guard 1's whitelist)
and reach `tryEtaStructCore.WF_of_structEtaG'` only through the pre-existing
`WF_of_structEtaGC`, whose axiom set I re-measured this round and which is **identical, axiom for
axiom**.  Likewise `isDefEqUnitLike.WF_of_structEtaG`'s set is identical to `WF_of_unitEta`'s.
The two new *ingredients* carry no frozen axiom and no `sorryAx` at all.

**Hole cones** (transitive `getUsedConstantsAsSet`, `.thmInfo` values included):

| seed | cone | holes |
|---|---|---|
| `isDefEqUnitLike.WF_of_unitEta` (pre-existing) | 10939 | `descend`, `rigidShapeUniqNS`, `forallE_inv_stratified`, `weakN_iff` |
| `isDefEqUnitLike.WF_of_structEtaG` (new) | 11156 | **the same four** |
| `tryEtaStructCore.WF_of_structEtaGC` (pre-existing) | 12461 | the same four |
| `tryEtaStructCore.WF_of_structEtaG'` (new) | 12579 | **the same four** |
| `UnitLikeBridgeG.today` | 6313 | **none** |
| `VEnv.StructEtaG.toUnitEta` | 819 | **none** |

The four are `inferType.WF`'s, borrowed through its single appeal to `TrExprS.uniq`; the cone
growth (+217, +118) is the two bridge proofs and adds no hole.

### The three steps, one line each

* `StructEtaG.toUnitEta`: at `C.fields = []`, `etaExpansionG_of_no_fields` identifies the two
  right-hand sides, `VIndCtor.recFields_of_fields_nil` supplies `C.recFields = []`, and the F17
  clause is free.  `StructEtaG.unitLike`'s docstring already *claimed* the subsumption ("the two
  widenings are one rule, not two competing ones"); this is the claim as a theorem, and it is what
  lets one rule serve both holes.
* `UnitLikeBridgeG.today`: `head_tr` on the bridge's own first premise puts the head constant in
  `c.venv`, then `TrEnv.not_inductInfo` refutes its third premise.  Five lines,
  `isDefEqUnitLike_never_true`'s route.
* `EtaStructSpineGC.today` (pre-existing) needs exactly the `he₂` that `tryEtaStructCore.WF`
  already has, so the second bridge was already free and nobody had composed it.

---

## 2. The two claims I was told to verify rather than trust

**Claim A — "a lemma along the lines of `isDefEqUnitLike_never_true` was repaired hole-free".
TRUE.**  **[measured]** `#print axioms Lean4Lean.TypeChecker.Inner.isDefEqUnitLike_never_true`
= `[propext, Classical.choice, Quot.sound]`; no `sorryAx`.  Its sibling
`tryEtaStructCore_never_true` is the same.  Ledger rows 39/99a are accurate: the repair is the
swap of `inferType.WF` for `inferType.WF'`, which the statement can afford because its conclusion
is `b = false` and discards the term's translation.

**Claim B — "zero-field eta was widened and the model-side pairing cost was nil, the model having
carried the same singleton assumption".  TRUE, with one qualifier that matters.**  **[measured]**
`Theory/SetModel/UnitEtaPairing.lean` exists (766 lines); `mem_Ind₃_fibre_iff_of_zero_field`,
`interpSig₃_fibre_iff_of_no_fields`, `interpSig₃_resIdxDetAt`,
`IsSubsingletonSignature₃.resIdxDetAt` and `mutUnitSig_not_single` are all
`[propext, Classical.choice, Quot.sound]`, no `sorryAx`.  Reading the statements rather than the
names: `mem_Ind₃_fibre_iff_of_zero_field` has **no hypothesis bounding `S.Q`**, so "no incremental
cost over the singleton case" is right; and `mutUnitSig_not_single` really does refute
`IsSubsingletonSignature₃` at a two-member block **for every carrier**, so "the model carried the
same singleton assumption" is right too.

*The qualifier.*  None of this discharges `UnitEta` (or `StructEtaG`) in the model, and the file
says so itself: `OracleOK` (`SetModel/Cnst.lean`) has **exactly two fields**, `congr` and `type`,
and `type` is a **membership** — verified by reading the structure this round — so
`InductOracleOK` pins no type former's denotation and a model satisfying it may interpret a
zero-field structure as a two-element set.  What is done is the *set-level* pairing step; what is
open is connecting a fibre to `⟦(const S us).mkApp ps⟧`.  So if the plan is "the model discharges
the eta rule", the pairing lemma is a prerequisite that is finished, not the discharge.

---

## 3. Anti-vacuity, for the new content specifically

`toUnitEta` is an implication between two predicates, so it is green whether or not either side is
ever satisfiable — exactly blindness 4/7 of `docs/vacuity-ledger.md` §0.  So:

* **The derived rule fires at the shape the checker fires at.**  `MutField.declEnv` is a two-type
  mutual block in `Type` whose narrow `VEnv.IsStructure` is refuted
  (`MutField.decl_not_isStructure`, pre-existing) and whose *other* member carries a field.  New
  this round: `declEnv_IsStructureG_0` (the shape at the **zero-field** member),
  `declEnv_unitEta_premises` (all eight premises of `VEnv.UnitEta` discharged at once there, plus two shape facts; the
  degenerate instance `Γ = [A]`, `us = []`, `ps = []`), and
  `declEnv_unitEta_of_structEtaG` / `declEnv_unitLike_of_structEtaG`, which fire the derived rule
  from `declEnv.StructEtaG` **alone** and conclude specific `IsDefEq`s between syntactically
  distinct terms (`x ≡ A.mk`, and `x ≡ y` for two inhabitants).  `declEnv_Amk_hasType` types the
  right-hand side, so the fired instance is not satisfied by an ill-typed conclusion.
  **[measured]**  A single `StructEtaG` assumption is therefore used at *both* arities of one
  block, which is what makes `toUnitEta` more than bookkeeping.
* **Where the anti-vacuity guarantee stops, stated rather than glossed.**  `declEnv.StructEtaG`
  itself is an assumption; nothing proves it *holds* at `declEnv` (that needs the model, §2).  And
  `c.venv.StructEtaG` — the residual as its callers use it — is satisfied today only vacuously,
  since a translated `venv` contains no inductive block at all while `AddInduct` is empty.  So the
  honest status of the residual is: **premises satisfiable and non-degenerate at the abstract
  level, conclusion not derivable, and today's call sites are themselves dead.**  The last of those
  is why the reduction is progress in *statement* and not in *content*.
* **Nothing here strengthens a hypothesis.**  `toUnitEta` and the two `today` lemmas all
  *discharge* hypotheses; the surviving hypothesis `c.venv.StructEtaG` is one the tree already had
  (`Verify/TypeChecker/EtaStructG.lean`), unchanged.  No conclusion was weakened.  The
  implementation was not touched — `Lean4Lean/TypeChecker.lean` has no edit this round — so
  nothing was narrowed to make a proof go through, and `kernel_sound`'s statement is untouched
  (frozen files: not opened).

---

## 4. Why I did not close them, and the exact lines that would

Both holes are provable **today**:

```lean
theorem tryEtaStructCore.WF … := (tryEtaStructCore_never_true he₂).mono
  fun _ _ _ h hb => absurd (h ▸ hb) nofun
theorem isDefEqUnitLike.WF … := (isDefEqUnitLike_never_true he₁).mono
  fun _ _ _ h hb => absurd (h ▸ hb) nofun
```

Both witnesses are hole-free (§2, claim A), so this is a genuine close: census 13 → 11, no new
axiom.  Three measurements say it is not worth doing, and the third is new this round:

1. It is discarded at the `AddInduct` flip.  The proof works only because `TrEnv.not_inductInfo`
   holds, and the flip is required for `kernel_sound` to cover nested inductives (CLAUDE.md).
   **[source]**
2. The two census rows are the only place a build surfaces that `structEta` is missing from the
   spec.  `docs/research-structeta.md` §5 and ledger row 39 both already ruled against the
   vacuous close for this reason.  **[source]**
3. **It moves nothing on guard 2.**  Neither hole is in `kernel_sound`'s cone; `kernel_sound` and
   `addDecl.WF` are bare `sorry`s (cones 7914 and 1, each containing itself as its only hole), so
   the eta holes' 70/71 users are the checker-refinement layer and the link to the main theorem
   does not exist yet.  **[measured]**

If the user wants the census number instead of the marker, the two lines above are it, and they
should be labelled in-file as vacuous the way `Verify/Environment.lean` labels `addQuot.WF`.

---

## 5. What I tried that failed, and the step it failed at

* **Restricting the residual to non-`Prop` blocks** (so the eventual spec rule could carry the
  `IsNeverZero` side condition `docs/design-inductive.md` proposes, with `isDefEqUnitLike.WF_prop`
  covering the `Prop` half — the pairing `docs/research-structeta.md` §2 flags as `[inferred]` and
  never machine-checked).  **Abandoned before writing Lean, at a step I can name:** the `Prop`
  branch needs `c.HasType ((VExpr.const S us).mkApp ps) (.sort .zero)` (for `WF_prop`/`WF_proof`),
  and at zero fields the eta branch needs `HasType ((const C.name us).mkApp ps) ((const S us).mkApp
  ps)` (for `structEta_of_prop`).  Neither is derivable from `VEnv.IsStructureG` in a file I own:
  the block constant's and constructor's typings come from the declaration through the
  `Verify/Typing/*` chain, which is why `EtaStructSpineGC` **carries** `hctor` and `hB` as
  conjuncts rather than deriving them.  Adding them as hypotheses would have turned one residual
  into two and moved the hole rather than closing it, so I stopped.  **[source]**  If someone owns
  that chain, the missing lemma is: `IsStructureG S D j T C → HasArgs (D.params.map (instL us)) ps
  → HasType ((const S us).mkApp ps) (.sort (D.lvl.inst us))`, plus the same for `C.name`.
* **Making `c.venv.StructEtaG` provable for a `VContext`** (i.e. the deep vacuity route, V1 of
  `docs/research-structeta.md` §4).  Not attempted: it is the vacuous close in a different
  costume, and it would additionally need "no `VInductDecl'` has `addInduct' D ≤ c.venv`", which
  is a `TrEnv` disjointness fact about `venv.defeqs`, not just `venv.constants`.
* **One instrument error of my own, recorded per ledger §0.**  My first eliminator count returned
  `0` for all four recursors: I had imported only `Lean4Lean.Verify.Guard`, whose closure **does
  not contain the abstract spec** (`Lean4Lean.VEnv.IsDefEq` is not a constant there —
  `#check` fails).  Corrected by importing the Theory modules; the count is then 65.  Anyone
  measuring the spec against Guard's environment will get zeros for everything.  **[measured]**

---

## 6. Proposed ledger row (not added; the ledger is shared)

> **111** | rows 102/105/107/110's residual pairs — "two hypotheses per eta hole" | **now ONE
> hypothesis, and the same one for both holes.** `StructEtaG.toUnitEta` (the positive-field rule
> subsumes the zero-field rule, so `UnitEta` is no longer an independent assumption) and
> `UnitLikeBridgeG.today` (the zero-field bridge, vacuously satisfiable today — the twin
> `EtaStructSpineGC.today` had never been written) reduce `isDefEqUnitLike.WF` and
> `tryEtaStructCore.WF` to `c.venv.StructEtaG` alone; `etaHoles_of_structEtaG` states all three
> `.WF`s from it in one theorem. Axiom sets identical to the predecessors', hole for hole, cones
> +217/+118 with the same four borrowed holes and no new frozen-axiom route. **And the correction
> that reprices the corner: neither hole is in `kernel_sound`'s cone** (7914 constants, only hole
> itself; `addDecl.WF`'s cone is 1) **so no close here can move guard 2 today** |
> `VEnv.StructEtaG.toUnitEta`, `UnitLikeBridgeG.today`, `isDefEqUnitLike.WF_of_structEtaG`,
> `tryEtaStructCore.WF_of_structEtaG'`, `etaHoles_of_structEtaG`,
> `MutField.declEnv_{IsStructureG_0,unitEta_premises,unitEta_of_structEtaG,unitLike_of_structEtaG,Amk_hasType}`
> (`Verify/TypeChecker/EtaResidual.lean`) | the flip kills the two `today` lemmas, by design |

---

## 7. What I would pick up first

1. **`structEta` as a `VEnv.IsDefEq` constructor — and price it against the 65 sites before
   starting.**  It is now the *only* thing between both eta holes and a proof, which was not true
   at the start of this round (there were four hypotheses; three are gone).  The shape to add is
   `StructEtaG`'s, not `StructEta`'s: it is the widest of the three
   (`toStructEta`, `toUnitEta`) and the one satisfiable at the mutual blocks the kernel really
   performs eta on.  Ownership: all 65 sites are in `Theory/`, none in `Verify/`; the one that
   does **not** go through mechanically is `IsDefEq.uniq`'s (`Theory/Typing/UniqueTyping.lean`),
   by the same argument `docs/handoff-isdefequ.md` §3 makes for `retype`.
2. **The model side of the same rule.**  §2's qualifier is the live item: define the `.induct`
   oracle as `IndFiber ∘ interpSig₃` and add the denotation equation to `OracleOK`, which is
   `docs/soundness-ledger.md`'s standing item and is identical for singleton and mutual blocks
   (ledger row 106c).  Until that lands, `StructEtaG` has no discharge route at all, and the
   syntactic work above buys a rule nothing can supply.
3. **`addDecl.WF` and `kernel_sound` are bare `sorry`s with no proof body.**  Finding 5 means the
   eta corner cannot affect guard 2 until the refinement layer is wired to the main theorem.  If
   the goal is guard 2 saying "COMPLETE", that wiring — not this corner — is the critical path,
   and it is measurable: `addDecl.WF`'s cone is a single constant today.
4. **Do not** close either hole vacuously (§4), and do not build on the two `today` lemmas as if
   they were bridges: they are satisfiability certificates that go red at the flip, and
   `WF_of_unitEta` / `WF_of_structEtaGC` are the versions that survive it.
