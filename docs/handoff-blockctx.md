# handoff-blockctx — the two-substitution argument at a *field* context

Owner stream: `blockctx`.  Owned files: `Lean4Lean/Theory/Inductive/BlockCtx.lean`,
`docs/handoff-blockctx.md`.  Everything else in the repo is read-only for this stream.

Task: close the gap `IndepResidual.lean`:302 names — `noBlockType_not_defeqType_blockSpine` needs
`Γ` block-free because it compares *two* constant substitutions, and where the hole lives `Γ` is a
**field context**, which is not block-free — or prove the gap cannot be closed by that method and
say exactly what the obstruction is.

---

## §1 PRIORS (written 2026-09-04, before any Lean in this round; never edited afterwards)

### 1.1 What I was told and intend to verify rather than trust

* **T1** `IndepResidual.noBlockType_not_defeqType_blockSpine` carries `hΓ : ∀ C ∈ Γ, D.NoBlock C`
  and that is the only obstacle to firing it at a field context.  *To verify:* read the statement
  from the compiled environment, not the source; and check that its `Rai` instantiation
  (`rai_noBlockType_not_defeqType_blockSpine`) really cannot be fired at the tree's own field
  context.
* **T2** `RecArgIndep.raiΓ` is a *real* field context of the hole's shape.  Source claims
  `raiΓ_eq : raiΓ = (raiPre.map (·.type)).reverse ++ raiD.params.reverse`.  *To verify* by citing
  that theorem, not by re-deriving it.
* **T3** `blockSpine_defeq_transport_ctx`, `blockSpine_not_defeq_forallE_of_sortVal_ctx`,
  `..._sort_of_piVal_ctx` need **no** hypothesis on `Γ`.  *To verify* from the compiled types.
* **T4** `IndepResidual.blockSubst_WF` has arity 14 and cone 2480; `Rai.raiσ_WF`, `Rai.raiσ'_WF`
  are the two concrete substitutions (sort-valued and Π-valued) into `∅`.  *To verify* with
  `scripts/exists.lean`.
* **T5** `InjCorner.nil_endpoints_typeable` names the target's one open instance as
  `¬ IsDefEqU 0 [] (.sort .zero) (.forallE (.sort .zero) (.sort .zero))`.  *To verify* by reading
  the statement; I intend to *hit that exact instance* with the obstruction, not a cousin of it.

### 1.2 Predictions, written before measuring

* **P1 (the answer).**  The two-substitution argument **does not** reach a field context, and the
  obstruction is *conservation of the mismatch*: every transport available at this layer
  (`substC` on constants, `instN`/axiomize on the context, Π-abstraction of the context,
  instantiating context variables with closed inhabitants) is a homomorphism on syntax, so a
  transport that sends the block to two different values sends *every* block occurrence to two
  different things.  The block occurs in the field context.  So the mismatch moves — context →
  term → environment — and is never annihilated.
* **P2 (the sharp form, and I expect it to be exact rather than approximate).**  At `raiΓ` the
  single context entry **is** the block spine `.const raiI []`, i.e. literally the same term as
  the judgement's right-hand side.  So "the two substituted contexts agree" is *equal to* "the two
  replacement values agree", which the sort/Π shape requirements forbid.  I predict I can prove:
  (a) `raiΓ.substC σ ≠ raiΓ.substC σ'` outright, by `decide`, for the tree's own `raiσ`/`raiσ'`;
  (b) for *arbitrary* σ, σ' with sort- and Π-shaped values, a pointwise **conversion** of the two
  images at `env₁` is exactly `SortPiDisjNil env₁ U`'s open instance — so the side condition needed
  to run the argument holds only if the predicate the argument reduces to is false.  Self-blocking,
  at the same instance §3 of `IndepResidual` targets.
* **P3 (a third reconciliation route, also circular).**  Instantiating the offending context
  variable with a closed inhabitant on each side needs *one* term inhabiting both images; by unique
  typing that again yields `sort ≡ Π`.  I predict this is provable from a `UniqTy env₁ U`
  hypothesis in a few lines.
* **P4 (the positive replacement, and where it goes hole-shaped).**  What *does* work at an
  arbitrary context is a **one**-substitution argument with no composition: for `A` a Π use the
  sort-valued σ, for `A` a sort use the Π-valued σ', for every other `A` use σ and the residual
  "a non-sort is not convertible to a sort" at `env₁`.  I predict: this needs no `SortUniq`, no
  `Ordered env₁`, and **no hypothesis on `Γ`** — the field-context obstruction is bought off by
  strengthening the `env₁`-side predicate from the off-diagonal (sort/Π) to a whole row
  (sort/anything-not-a-sort).
* **P5 (my own method's gap, predicted before measuring).**  That stronger predicate is **false at
  any environment carrying a δ-rule whose right-hand side is a sort** — i.e. at any environment
  that abbreviates a universe (`def MyProp := Prop`).  I predict I can build such an environment
  concretely and refute the predicate there, so the positive theorem is worth only what its target
  is worth, and its target had better be `∅` — the same caveat `IndepResidual` §4 records for
  `RigidSortPiDisj`.  If I cannot build an `Ordered` witness I will say so rather than assert it.
* **P6 (absence claim, to be checked with BOTH scripts).**  No predicate of the form "a non-sort is
  not `IsDefEqU`-convertible to a sort" exists in the tree; the near misses are
  `InjPiRogue.SortMidNonSort` and `InjOneFact.SortMidNonSortC`, which are *`IsDefEqStrong`
  trans-midpoint* statements, and `SortUniqDown.SortInv`, which is level agreement between two
  sorts.  I will not write "does not exist" without `scripts/exists.lean` **and**
  `scripts/shape.lean`.
* **P7 (consumer).**  Zero users, and legitimately so: `IndepResidual` itself has zero users, and
  the hole's own module `Theory/Inductive/Decl.lean` is *upstream* of both, so it cannot cite me.
  To be checked with `scripts/can-cite.py`, not asserted.
* **P8 (build).**  `python3 scripts/layer-check.py` passes; my file imports only `Theory/*`.

### 1.3 What I will *not* do

* Not edit `IndepResidual.lean`, `Decl.lean`, or anything else outside my two files; any implied
  edit is quoted verbatim in §6 and left unapplied.
* Not state a theorem whose hypotheses no field context satisfies.  Every headline gets fired at
  `raiΓ` — the tree's own field context, block-mentioning — or is reported as unfireable.

---

## §2 MEASUREMENTS (appended as made; §1 is never edited)

### 2.1 The priors, checked

* **T1 verified.** `IndepResidual.noBlockType_not_defeqType_blockSpine` (arity 31, cone 2183,
  hole-free; I had guessed 24/861 before measuring -- the guess was wrong, the measured pair is this one) carries `hΓ : ∀ C ∈ Γ, D.NoBlock C`.  And **T1's second half is now a theorem**:
  `BlockCtx.raiΓ_not_noBlock` (`by decide`) refutes that hypothesis at the tree's own field context,
  so `IndepResidual.Rai.rai_noBlockType_not_defeqType_blockSpine` cannot be fired at `raiΓ` at all.
  It is not vacuous — it fires at block-free `Γ` — but at the context the hole hands it, it is
  unusable.  `rai_fieldCtx_is_the_new_part` records both halves as one `∧`.
* **T2 verified**, by citing `RecArgIndep.raiΓ_eq` (arity 0, cone 75, hole-free):
  `raiΓ = (raiPre.map (·.type)).reverse ++ raiD.params.reverse`, the hole's `hΓ` verbatim.
  `raiΓ = [.const raiI []]` — field 0 is recursive with `ξ = []`, `π = []`, so its stored type is
  the block spine on the nose.
* **T3 verified** from the compiled types: the three `_ctx` forms take no hypothesis on `Γ`.
* **T4 verified**: `IndepResidual.blockSubst_WF` arity 14, cone 2480, hole-free;
  `Rai.raiσ_WF` arity 1, cone 2509, hole-free.
* **T5 verified**: `VEnv.nil_endpoints_typeable` (arity 1, cone 582, axioms `[propext]`) names
  `¬ IsDefEqU 0 [] (.sort .zero) (.forallE (.sort .zero) (.sort .zero))`.  `§3`'s
  `rai_side_condition_iff_open_instance` hits that exact proposition, not a cousin.
* **P6 checked with BOTH instruments** — `scripts/exists.lean` on
  `VEnv.SortRigid` / `SortRigid` / `BlockCtx.SortRigid` / `VEnv.SortRigidNS` (all NOT FOUND), and
  `scripts/shape.lean` with `HEADS="VEnv.IsDefEqU VExpr.sort Not OnCtx"` (27 hits, 0 structure
  fields, listed cheapest first).  Nothing in the tree states "a non-sort is not convertible to a
  sort" at the `IsDefEqU` layer.  Nearest: `VEnv.SortMidNonSort` and
  `VEnv.SortMidNonSortC` (both `IsDefEqStrong` *trans-midpoint* statements, not this),
  `VEnv.SortInv` (level agreement between two sorts),
  `VEnv.IsDefEqU.const_sort_inv` (const spines, and downstream).
* **P8 verified**: `python3 scripts/layer-check.py` — `BlockCtx` appears nowhere in either report;
  the 4 direct + 11 transitive `Verify/` entries are pre-existing and none is mine.

### 2.2 The answer

**P1 and P2 hold, and P2 came out exact.**  The two-substitution argument does **not** reach a field
context.  At `raiΓ` the single context entry *is* the judgement's right-hand side, so:

| what | statement |
| --- | --- |
| the side condition, decoded | `substC_ctxEq_iff`: `Γσ = Γσ'` ⟺ `t.instL [] = t'.instL []` |
| syntactic half | `not_substC_ctxEq_of_shapes`: with one value sort-shaped and one Π-shaped, `Γσ ≠ Γσ'`.  **False, not merely unproved** |
| fired | `rai_substC_ctxEq_false`: the two images are `[Prop]` and `[Prop → Prop]` |
| conversion half | `images_conv_refutes_sortPiDisjNil` / `images_conv_refutes_target`: a *conversion* of the two images refutes `SortPiDisjNil env₁ U`, hence `RigidSortPiDisj env₁ U` |
| the two are one | `rai_side_condition_iff_open_instance`: at `Rai.raiσ`/`Rai.raiσ'` the relaxed side condition **is** `Prop ≡ (Prop → Prop)` at `[]` — `nil_endpoints_typeable`'s instance |
| third route | `common_inhabitant_refutes`: a common closed inhabitant of the two images gives the same conversion, under `VEnv.UniqTy` |

So each of the three routes the brief listed for repairing the context is **self-blocking**: its
side condition holds only when the predicate the argument reduces to fails.  The structural reason:
every transport at this layer is a syntax homomorphism, so a transport separating the block into two
values separates *every* block occurrence; the block occurs in the field context; the mismatch moves
(context → term → environment) and is never annihilated.  "Close the context away" is covered by the
same fact — Π-abstracting `Γ` before substituting turns `Γσ.pis A` vs `Γσ'.pis A` into the identical
mismatch, now inside the terms, and axiomising the context (`VEnv.axiomize_step` (`Theory/Typing/ShapeIndepStep.lean`)) moves it into
the environment, since the fresh axiom's type is `Prop` on one side and `Prop → Prop` on the other.

### 2.3 The positive replacement, and P4/P5

`noBlockType_not_defeqType_blockSpine_oneSubst` (arity 29, cone 881) does reach a field context: it
never composes, so the two images of `Γ` are never compared.  Case on `A`'s constructor — sort ⇒ the
Π-valued substitution alone contradicts `RigidSortPiDisj`; anything else ⇒ the sort-valued
substitution alone contradicts `SortRigid`.  **P4 holds**: no `SortUniq`, no `Ordered env₁`, and no
hypothesis on `Γ`.

**P5 holds and is sharper than predicted.**  `SortRigid` implies the old target
(`SortRigid.rigidSortPiDisj`) and is refuted by a *single* δ-rule to a sort
(`not_sortRigid_of_sortAbbrev`) — and that refutation lands at a **`VEnv.WF`** environment
(`wf_sortAbbrevEnv`, `not_sortRigid_wf_sortAbbrevEnv`): `def rogueC : Sort 1 := Prop`, i.e.
`VEnv.rogueEnv1` plus `VEnv.rogueDfSort` taken alone, which is
`rogueSortPiEnv` minus its second rule.  Contrast: `RigidSortPiDisj` is only known false at
`Ordered` environments (a two-rule *hub*, `IndepResidual.not_rigidSortPiDisj_rogueSortPiEnv`) and is
conjectured at `VEnv.WF` ones.  So the field context is bought at the price of a predicate no
universe-abbreviating environment satisfies; what keeps §5 non-vacuous is that its target is `∅`,
which has no δ-rule at all — the same escape `IndepResidual` §3 relies on, and no wider.

### 2.4 The firing (anti-vacuity)

`rai_fieldCtx_noBlockType_not_defeqType_blockSpine` (arity 3, cone 2579): at `RecArgIndep.raiEnv0`,
over `raiΓ` — certified by `raiΓ_eq` to be the hole's own field context and by `raiΓ_not_noBlock` to
be **not** block-free — no block-free type is convertible to the block constant, from the single
hypothesis `SortRigid ∅ 0`.  `OnCtx raiΓ (raiEnv0.IsType 0)` is *discharged* (`onCtx_raiΓ`), not
assumed, so no hypothesis in the statement is one a field context fails.

### 2.5 Table

| name | arity | cone | axioms |
| --- | --- | --- | --- |
| `BlockCtx.blockSpineType_defeq_transport_ctx` | 17 | 858 | propext, Quot.sound |
| `BlockCtx.noBlockType_not_defeqType_blockSpine_ctxEq` | 31 | 2189 | propext, Quot.sound |
| `BlockCtx.ctxEq_of_noBlock` | 7 | 614 | propext |
| `BlockCtx.raiΓ_not_noBlock` | 0 | 409 | propext, Quot.sound |
| `BlockCtx.substC_ctxEq_iff` | 6 | 603 | propext |
| `BlockCtx.not_substC_ctxEq_of_shapes` | 11 | 606 | propext |
| `BlockCtx.rai_substC_ctxEq_false` | 0 | 750 | propext, Quot.sound |
| `BlockCtx.images_conv_refutes_sortPiDisjNil` | 14 | 616 | propext |
| `BlockCtx.images_conv_refutes_target` | 14 | 624 | propext |
| `BlockCtx.rai_side_condition_iff_open_instance` | 2 | 766 | propext, Quot.sound |
| `BlockCtx.common_inhabitant_refutes` | 9 | 37 | propext |
| `BlockCtx.SortRigid` (def) | 2 | 34 | — |
| `BlockCtx.SortRigid.rigidSortPiDisj` | 3 | 81 | propext |
| `BlockCtx.noBlockType_not_defeqType_blockSpine_oneSubst` | 29 | 881 | propext, Quot.sound |
| `BlockCtx.not_sortRigid_of_sortAbbrev` | 10 | 598 | propext |
| `BlockCtx.wf_sortAbbrevEnv` | 0 | 779 | propext, Quot.sound |
| `BlockCtx.not_sortRigid_wf_sortAbbrevEnv` | 0 | 772 | propext, Quot.sound |
| `BlockCtx.onCtx_raiΓ` | 0 | 785 | propext, Quot.sound |
| `BlockCtx.rai_fieldCtx_noBlockType_not_defeqType_blockSpine` | 3 | 2579 | propext, Quot.sound |

Every one: `own value is a hole: false; cone reaches sorryAx: false`.  **No `sorryAx`, and no
`Classical.choice`** — `sort_or_not` is a constructor case split precisely to keep it out.
`lake build Lean4Lean.Theory.Inductive.BlockCtx`: 127/127, zero errors and zero warnings from this
file.

### 2.6 Consumers (P7 checked, not asserted)

`scripts/can-cite.py`: **zero users, and every candidate consumer is upstream of me.**
`Theory/Inductive/Decl.lean` (closure 15 modules) — where the hole is — cannot cite BlockCtx;
neither can `RecArgIndepClose`, `Typing/EnvLemmas`, `Typing/InductiveLemmas` or `Typing/Env` (where
`addInduct_WF` lives).  All five are *inside* BlockCtx's own 118-module import closure, so those are
cycles, not missing imports.  This is inherited: `IndepResidual` has zero users for the same reason,
and `RecArgIndepClose` records that no proof in the tree stands on `exists_indep` at all.

**Actionable, and NOT applied** (I own neither file): §1, §3, §4 and §5 use nothing outside
`IndepResidual`'s own import closure, so `noBlockType_not_defeqType_blockSpine_oneSubst` and its
`Rai` firing could be *migrated into* `Theory/Inductive/IndepResidual.lean` and would then sit one
layer nearer the hole.  Only two declarations need the extra import
(`Lean4Lean.Theory.Typing.InjCorner`, acyclic with `IndepResidual`: union 117 modules):
`images_conv_refutes_sortPiDisjNil` and `images_conv_refutes_target`, which name
`VEnv.SortPiDisjNil` and `RigidSortPiDisj.nil`.  Everything else would move as written.

### 2.7 Gaps inside my own method

1. **The obstruction is proved at one witness, not for all field contexts.**  `raiΓ` is a real
   field context (`raiΓ_eq`) and the tree's only committed one, and the argument is exact there
   because its entry is the spine itself.  A field context whose recursive entry is
   `∀ ξ₀, I p π₀` with `ξ₀ ≠ []` gives images `∀ ξ₀, Prop` and `∀ ξ₀, (Prop → Prop)`, which are
   still non-equal but whose *conversion* would need Π-injectivity to be pushed back to
   `Prop ≡ (Prop → Prop)`.  I did not prove that step; the general claim is "the same, modulo
   `PiInv`", and it is stated here rather than in the file.
2. **The indexed escape I could not close off.**  `substC_ctxEq_iff` is exact because the field
   entry and the target spine carry the *same* arguments.  For an indexed block, entry `I p π₀` and
   target `I p π` with `π₀ ≠ π` could in principle be separated by a replacement value that
   discriminates on its index argument — so a rich `env₁` (one with an eliminator) might admit a
   pair of substitutions agreeing on the context and disagreeing on the target.  I have no witness
   either way; at `env₁ = ∅` no such value exists, but that is not a proof for general `env₁`.
3. **`SortRigid` is a whole row, not a corner.**  The residual for a general `A` could be split
   further by `A`'s shape — `.lam`, a `bvar`-headed spine, a `const`-headed spine (that last one is
   `RigidConstSortDisj` guarded by `RuleFreeHead`, which is exactly what
   `not_sortRigid_wf_sortAbbrevEnv` exploits) — which would trade one strong hypothesis for four
   weaker ones.  I did not do that split; the file takes the single strong predicate and *proves*
   what it costs instead of hiding it.
4. **Nothing here closes the hole and no census number moves.**  `SortRigid ∅ 0` and
   `RigidSortPiDisj ∅ 0` are open, and §4 shows the first is false as soon as the target environment
   can abbreviate a universe.  The claim is only: the *field-context* obstruction named at
   `IndepResidual.lean`:302 is now either refuted (two-substitution route) or removed at a price
   that is measured (one-substitution route).
