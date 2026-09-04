# handoff-b6 — B6, the real restoration (populate `recArg`, re-prove the collapse, witness at `ntreeAux`)

Owned files: `Lean4Lean/Verify/Inductive/B6.lean` (new), `docs/handoff-b6.md` (this).
Predecessor: `docs/handoff-claimb2.md` (B5 + B7 closed, 20 declarations in
`Verify/Inductive/ClaimB.lean`).

## Scoring my predecessor's priors and findings (from `docs/handoff-claimb2.md`)

Written BEFORE any measurement of my own; each score is re-checked at close.

- **Q1** (`OracleSound` has no totality clause; producer is 3 lines) — it measured this by
  reading the definition (M1) and then shipped the producer (M7). Both the prior-raise and the
  delivery are self-consistent and checkable by `#print axioms` on `oracleSound_of_ctorTr`.
  Provisional score **1.0**, pending my own re-measurement of that declaration.
- **Q2** (`CtorStoresTr` the better primary target; both dischargeable) — it discharged both and,
  importantly, noticed the geometry ran the *other* way (`CtorStoresTr` downstream of
  `OracleSound` in `SurfaceMap.lean`). Prior partly right, finding right. Provisional **0.9**.
- **Q3** (B7 tension resolved by "declaration vs restoration") — it **self-refuted** and named the
  real axis, **syntax vs `whnf`**. It scored itself 0.4 for the prior. I agree with 0.4 for the
  prior and give **1.0** to the self-refutation (M5): a machine-checked witness (`ROWit.roRedex`,
  spine head a `.lam`) beats prose, and it produced one.
- **Q4** (completeness is the missing direction) — it found completeness is not merely missing but
  **false at a block the kernel accepts**, and then found the two-stage repair already in the tree
  and already measured (M6, its ninth already-done catch). This is the strongest line in the
  handoff. **1.0**.
- **Q5** (B6 will not close; 0.1) — correct, and it converted the failure into an implementable
  statement with the blocking sub-fact named ("`recArgOf` needs `D`, so `surfIndCtor?` must run in
  two passes"). Prior **1.0** as a prior.
- **Q6/Q7** (Claim A untouched; census 13 / NOT BUILT 0; warning drift attributed to another
  stream's `a554def`) — **1.0** and **0.9**; the warning figure is explicitly flagged as drift,
  not a gate, which is the right framing and matches my brief.
- **Its process discipline**: it logged its own `autoImplicit` near-miss (M9) — an unbound `R` in
  `trCtors_surfInductDecl?_ctorTr` caught by reading the draft against `SurfaceMap.lean:481`
  before elaborating. That is the habit my brief tells me to copy, and it is the reason its round
  has 0 holes. Credited.
- **Aggregate**: the handoff is unusually trustworthy on *measurements* (M1–M8, M10 are all
  reproducible one-liners) and appropriately hedged on *priors*. Its three-part statement of B6 is
  the thing I must verify rather than trust — my brief says so and I agree, because parts 1 and 3
  are claims about code it did not write.

## My own priors (written BEFORE any measurement this round)

- **P1. Part 3 is already done.** `ctorStoresTr_of_ctorTr` stated at arbitrary `R` really is what
  B6's third part needs, so I should not redo it. Confidence **0.75**. Residual risk: "arbitrary
  `R`" may still be *only* the `CtorStoresTr` predicate, whereas the real restoration needs the
  `recArg`-carrying fields too, so part 3 might be done for ctors and open for fields.
  Confidence that a field-side analogue is still missing: **0.5**.
- **P2. The two-pass claim.** `recArgOf` takes `D` (arity 3 = `D`, index, type), and
  `surfIndCtor?` is what builds the ctor types that would feed it, so populating `recArg` inside a
  single pass would be circular in `D`. Prior that the two-pass restructure is genuinely forced:
  **0.7**. Competing prior: only the *type-telescope* part of `D` is needed (the `tyName`/`tyLvls`
  table, i.e. the restoration `R`), not the ctor fields, so the "two passes" may be as cheap as
  "build `R` first, then map" — and `R` is derivable from the surface names alone. Confidence in
  that cheaper shape: **0.45**. These are not exclusive: the restructure is forced *and* may be
  cheap. I will measure `recArgOf`'s actual argument, and whether `surfIndCtor?` already has `D`
  or only `R` in scope.
- **P3. The `.lam`-free lemma.** *`ctorTr?` has no `.lam` case, so its output is `.lam`-free at
  the spine head.* Prior **TRUE as stated about the syntactic clause list**, i.e. `ctorTr?`'s
  `match` has no `.lam` arm and returns `none` there. Confidence **0.8**. But prior that the
  *useful* corollary ("stage 1 always answers on the map's output") follows immediately:
  **0.45** — because the field type the reader sees is a *sub-expression* reached through
  `splitPis`/`spineFn`, and `.lam`-freeness of the whole output does not by itself survive those
  projections unless the fragment is closed under them. What I expect to need: a
  "`ctorTr?`-output is in a `.lam`-free grammar, and that grammar is closed under `splitPis` and
  `spineFn`" invariant. Confidence such an invariant is needed: **0.6**. Confidence it already
  exists in the tree (a `Rigid`/`spine` predicate on `ctorTr?`'s range): **0.4** — the tree has
  had eight already-done catches, and `isUnique_of_ctorTr` suggests range invariants are a
  known genre here.
- **P4. Refutation risk on P3.** Prior that the lemma is outright FALSE: **0.2**. The way it could
  fail: `ctorTr?` may recurse through a `.app` whose function argument came from a *binder body*
  it did build (a `.forallE` arm) and the spine head could then be a bound variable `.bvar`, which
  is not `.lam` — that does not refute the lemma but makes it *insufficient*, which is the 0.6
  branch of P3, not a refutation. A genuine refutation needs `ctorTr?` to emit `.lam`, e.g. via a
  `.letE` zeta-expansion or a projection-eta arm. Confidence such an arm exists: **0.2**.
- **P5. The witness.** `Lean4Lean.InductiveDeclExamples.ntreeAux` — prior that
  `InductiveDeclExamples` already exists in the tree with an `ntree`/`ntreeAux` nested block, and
  my job is a *theorem about* it, not the block itself. Confidence **0.7**. Confidence the
  arity-0 witness closes by `rfl`/`decide` after the general theorems are in place: **0.5**;
  more likely it needs a small `native_decide`-free evaluation, which I will avoid (it would add
  an axiom outside the whitelist — `Lean.ofReduceBool`). **Hard constraint I set now: no
  `native_decide`, ever, because guard 1 whitelists 24 axioms and `ofReduceBool` is not one.**
- **P6. `restore_noK`.** Prior that it exists and that the collapse re-proof is a rewrite chain
  over existing lemmas as the predecessor says: **0.6**. Residual risk: with `recArg := some _`
  the K-like collapse may genuinely change, i.e. the no-op *was* load-bearing and the collapse
  needs a new side condition (`recArg` points at a *smaller* index). Confidence a new side
  condition is needed: **0.4**. `recArgOf_idx_lt` already existing in `ClaimB` is evidence the
  predecessor anticipated exactly this, which raises `restore_noK` to a rewrite chain: **0.65**.
- **P7. Negative control.** Prior I can do it on the artefact (rename an auxiliary member so the
  map returns `none`) rather than on the premise: **0.7**, since the predecessor's
  `recog_roRedex_none` shows `rfl`-level negative facts are cheap in this setting.
- **P8. Claim A untouched.** I will not open any Claim A file for writing; the twelve
  `TrIndDeclN` field producers stay as they are. Verified at close by `git status --porcelain`
  showing only my two files as mine. Confidence **0.95**.
- **P9. Round-close.** Census **13 / NOT BUILT 0** with my file adding nothing to either;
  `lake build` exit 0; three guards as the predecessor reported (guard 2 still "proof
  INCOMPLETE"); `layer-check.py` exit 0; **0 warnings from `B6.lean`**; the in-repo "not
  explicitly referenced" total near **63** and reported as drift. Confidence **0.85**.
- **P10. Orphan discipline.** My consuming module is `Lean4Lean.Verify.Inductive.TrIndDeclNProducer`,
  measured cycle-free from `ClaimB` by the predecessor. Prior that `B6` importing `ClaimB` keeps
  that cycle-free: **0.85** (`ClaimB` closure 203, `TrIndDeclNProducer` 207, disjoint in both
  directions per M7 — but I will re-run `can-cite.py` because `ClaimB` is untracked and another
  stream may have moved things).
- **P11. Stale-artifact trap.** Four modules moved `Verify/Typing/` -> `Theory/Inductive/`
  (`ProjGen`, `ProjClosedG`, `ProjGenLift`, `ProjGenInst`). Prior that orphaned `.olean`s are
  still present and could make a population walk report a pre-migration snapshot: **0.5**. I check
  and delete before my first population measurement.

## Measurements (appended as made)

### M1. Orientation, and P11 half-refuted
HEAD = `82f8cc9` ("B5 and B7 closed"). `git status --porcelain` shows **two** other streams'
untracked files (`Theory/Inductive/IndepResidual.lean`, `docs/handoff-indepresidual.md`) plus my
`docs/handoff-b6.md`. Note the brief's snapshot listed `Theory/SetModel/CnstRecursion.lean`,
`InductOracleAudit.lean`, `Theory/Inductive/NestedRules.lean`, `Theory/SetModel/InaccChainOmega.lean`
as modified/untracked; none of those show now, so that stream **landed** (`git log` shows
`82f8cc9`, `a554def` as the two most recent). Nothing of mine is in flight from a prior round.

**P11 (0.5 that the four migrated modules left orphan `.olean`s): WRONG for those four** — the
`ProjGen`/`ProjClosedG`/`ProjGenLift`/`ProjGenInst` oleans sit at their *new* `Theory/Inductive/`
paths and no stale `Verify/Typing/` copy exists. But the general sweep found **13 orphan
`.olean`s** (`.lean` gone, module still loadable): `Reflect/Align`, `Theory/Inductive` (the old
`Theory/Inductive.lean` roll-up, deleted in `1ab5561`), `Verify/Inductive/UioLoopAxScratch`,
`UniformOccScratch`, `Theory/Typing/{SortInvWIP,DescendInstN,ScratchOneFactDup,RuleShape,UniqAux,
ProbeTmp,WeakNProjSwap}`, `Theory/Inductive/{ScratchAx,OccArgsTyping}`. **Zero live `.lean` files
import any of them** (checked with anchored `import ... $` greps — the unanchored grep for
`Lean4Lean.Theory.Inductive` reports 180 hits, all of which are `...Inductive.Foo`; the anchored
count is 0). Deleted all 13 sets of artifacts (39 files) before any population measurement.
Score P11 **0.5 as stated, but the *rule* earned its keep**: 13 stale modules were live in
`.lake` and a population walk would have counted them.

### M2. The three parts, read in the source rather than trusted
- `Lean4Lean.surfIndCtor?` (`Verify/Inductive/SurfaceMap.lean:135`) sets
  `fields := ((VExpr.peelPis ct).1.drop np).map fun A => { type := A, lvl := fl, recArg := none }`.
  **Confirmed: `recArg := none` at every field, and the field *types* are exactly the dropped
  segment of `peelPis` on the oracle's output** — so the predecessor's "the restoration is a no-op
  because `recArg := none`, not because of the domain" is verified in the definition, one line.
- `Lean4Lean.VInductDecl'.recArgOf` (`ClaimB.lean`): `(D.idRestore.recog D.nm i S).orElse fun _ =>
  D.idRestore.recog D.nm i (VExpr.betaHead S)`. It takes `D` in **two** places — `D.idRestore` and
  `D.nm`. **P2's cheaper branch is refuted on the nose**: `recog` needs `D.nm` (the member count)
  *and* `D.idRestore` (whose `tyName`/`tyLvls`/`tyArgs` are read off `D.types` and `D.uvars`), so it
  needs the member list, which is what the map is building. But note what it does *not* need: the
  **ctor** data. `D.idRestore` and `D.nm` are functions of `D.types.map (·.name)`, `D.uvars` and
  `D.types.length` only. So the two-pass restructure is forced (P2's 0.7 branch **CORRECT**) and it
  is cheap in a precise sense: pass 1 needs only the member *headers*.
- The map's output at `ntreeAux` is `eraseRecArgs ntreeAux`, not `ntreeAux`
  (`ntreeRTypes_maps`, `SurfaceMap.lean:589`), and the existing arity-0 witness
  `ntreeAux_surfaceMap_witness` **machine-checks the gap** in its own statement:
  `ntreeNode.recFields.length = 1` and the erasure's `= 0`. That is exactly what B6 must close.
- Part 3: `Lean4Lean.ctorStoresTr_of_ctorTr` (`ClaimB.lean` §1.3) really is stated with
  `{D : VInductDecl'} {R : VIndRestore}` both free and **no `surfInductDecl?` hypothesis** — the
  per-ctor data is a hypothesis `h` quantified over `C.typeR D R j`. **Part 3 verified done.**
  P1's residual (0.5 that a field-side analogue is missing) is the real question: `CtorStoresTr`
  speaks about `C.typeR D R j`, which *does* read `recArg` through `C.fieldTypesR`, so
  `ctorStoresTr_of_ctorTr` is already `recArg`-aware — it does not care what `recArg` is, it just
  demands the oracle reproduce `C.typeR D R j`. So no field-side analogue is missing; the *work*
  moves into showing the reproduced term is the user's type. P1 scored **1.0**, its residual
  refuted.

### M3. **Part 2's mechanism is WRONG in the handoff — and the correction makes part 2 free**
The predecessor's part 2 says: *"`typeR_surfIndCtor?` currently gets `C.fieldTypesR = C.fields.map
(·.type)` for free from `recArg = none`. With `recArg` populated it needs
`VIndRestore.restore_noK` at each recursive field instead."*

Read the lemmas:
- `Lean4Lean.VIndField.typeR_id` (`Theory/Inductive/NestedHead.lean:139`) is
  **`@[simp]` and UNCONDITIONAL**: `F.typeR D D.idRestore i = F.type`, proved by `split` +
  `VIndRestore.restore_id`, which is itself unconditional (`Restore.lean:430`).
- Hence `VIndCtor.fieldTypesR_id` and `VIndCtor.typeR_id` are unconditional too
  (`NestedHead.lean:147,158`), and both docstrings say "Unconditional; was conditional on
  `C.Canonical D`" — the ruling-116d reparameterisation already removed the condition.

So at `D.idRestore` **the collapse does not depend on `recArg` at all**, and `restore_noK` is not
needed: `restore_noK`'s job is the *non*-identity `R`, where it asks `VExpr.NoConsts K` of the whole
subterm. At `ntreeAux` the field that must move is `_nested.List_1 α`, which *is* a companion
constant, so `restore_noK` could not apply to it even there. **Part 2 is discharged by
`VIndField.typeR_id`, one `@[simp]` lemma, and the predecessor's named route is a red herring.**
P6 scored **0.3**: the prior "it is a rewrite chain over existing lemmas" is right in *kind*
(0.6 branch), the named lemma is wrong, and my 0.4 "a new side condition is needed" branch is also
wrong — no side condition, the condition was already deleted upstream.

### M4. `recArgOf` factors through the block **header** — the two-pass shape the tree already uses
`recogAt R i k S` reads only `R.tyName k`, `R.tyLvls k`, `R.tyArgs k`; `recog` adds `nm`. At
`R = D.idRestore` (`Restore.lean:158`) those are `(D.types.getD k default).name`, `D.ownLvls`,
`bvars 0 D.np`. So `recArgOf` depends on `D` through **exactly** `D.types.map (·.name)`, `D.uvars`,
`D.params.length`, `D.types.length` — i.e. through `Lean4Lean.VIndHeader`
(`NestedBuild.lean` Part 4: `uvars`, `params`, `nm`, `names`), which exists *for this reason*:
its docstring says "An auxiliary member's own field types are headed by constants of the block being
declared — including its own name — so the construction cannot take the finished `VInductDecl'` as
input." And `Lean4Lean.VNestedOcc.field` already takes `(H : VIndHeader) (R : VIndRestore)`
separately and calls `R.recog H.nm i S`. **P2 confirmed: two passes are forced; and the forced
shape is the tree's own `VIndHeader`, not an ad-hoc fixpoint.** Scored 1.0 for the 0.7 branch;
the 0.45 "cheaper shape" branch is refuted as stated (`recog` does need `nm` and the member names,
not just `R`) but its *spirit* — "pass 1 needs only the member headers" — is exactly right.

### M5. `shape.lean` on HELPER shapes: four queries, population **460** built modules
| HEADS | hits | reading |
|---|---|---|
| `VIndHeader VIndRestore` | 30, all `VNestedOcc.*`/`MRedex.*` in `NestedBuild`/`MemberRedex` | the header/restoration pair is an established idiom; **no `VIndHeader.idRestore` exists** |
| `surfIndCtor? VIndRecArg` | 2, both `surfIndCtor?.eq_1` and `surfIndCtor?_eq_some` | **no `recArg`-populating map exists** |
| `surfInductDecl? VIndRecArg` | 1, `ntreeAux_surfaceMap_witness` (arity 0) | the only link between the map and `recArg` is the existing witness's *statement of the gap* |
| `ctorTr? VExpr.spineFn` | **0** | no spine/`.lam`-freeness invariant on `ctorTr?`'s output exists |
| `VExpr.betaHead` | 21; the only general ones are `skips_betaHead`, `betaHead.eq_1`, `recArgOf_sound`, `field.eq_1` | **no general "`betaHead` is the identity on a non-`.lam`-headed term"** — `MemberRedex.lean:559` *observes* it in prose ("type is `.const`-headed, so `betaHead` is the identity on it") at a concrete block, and `listOcc_betaHead_control` is that observation as an arity-0 `rfl`. The general lemma is a genuine gap. |
No already-done catch this round on the deliverable side; two on the *route* (M3, M4).

### M6. Citability, cycle-freeness
`scripts/can-cite.py Lean4Lean.Verify.Inductive.ClaimB ...`: **YES** for `VIndHeader`,
`VExpr.betaHead`, `VExpr.peelPis`, `ctorTr?`, `VIndRestore.recog`,
`InductiveDeclExamples.ntreeAux` (in `Theory.Inductive.NestedHead`) and
`InductiveDeclExamples.ntreeRTypes` (in `Verify.Inductive.SurfaceMap`). So **`B6.lean` needs
exactly one import, `Lean4Lean.Verify.Inductive.ClaimB`.**
Cycle check (own closure walk): `ClaimB` closure 169, `TrIndDeclNProducer` closure 173, union 178,
**neither contains the other**. So the named consumer can import `B6` without a cycle. P10 **1.0**.

### M7. **The `.lam`-free lemma is PROVED, and it is sharper than the brief's statement**
`Lean4Lean/Verify/Inductive/B6.lean` §1, 0 errors 0 warnings, axioms `{propext, Quot.sound}` on
both key declarations. The chain (all `Lean4Lean.`-qualified):
- `VExpr.noLam : VExpr → Bool` — `.lam`-free, decidable (chosen over a `Prop` so the negative
  controls can be `decide`).
- `VExpr.ne_lam_of_noLam`, `VExpr.noLam_spineFn` — `.lam`-freeness passes to the spine head.
- `VExpr.betaSpine_eq_mkApp` — `betaSpine as f = f.mkApp as` for non-`.lam` `f`. **This is the
  general form of the fact `MemberRedex.lean:559` states only in prose at a concrete block.**
- `VExpr.betaHead_eq_self_of_noLam` — **`betaHead e = e` on a `.lam`-free `e`.** The lemma M5 found
  missing.
- `VExpr.noLam_peelPis` — closure under `peelPis`, both components (the projection my prior P3
  worried about, 0.6 branch: it *was* needed, and it is four lines).
- `VInductDecl'.recArgOf_eq_recog_of_noLam` — **the payload**: on a `.lam`-free stored type the
  two-stage reader *equals its first stage*. Not "stage 1 answers" — the two stages are the
  **same call**, because `betaHead` is the identity there. So the `whnf` gap does not merely stay
  shut, it **does not exist** on `.lam`-free input.
- `noLam_of_ctorTr` — the range invariant: `∀ e Γ p, ctorTr? Γc Us e Γ = some p → p.1.noLam`, by
  structural recursion on `Expr`, **with no hypothesis on the context `Γ`**, because the `.bvar`
  clause returns the de Bruijn variable itself (`bvarCtx_find?`) rather than anything read out of
  `Γ`. The five fallthrough clauses (`.fvar`, `.mvar`, `.lam`, `.letE`, `.lit`, `.proj`) are `none`.
- `noLam_ctorOracle` — the same for `ClaimB`'s `ctorOracle`.

**Verdict: the lemma is TRUE, in the strong form.** Scoring my priors: P3's 0.8 ("true as stated
about the clause list") **correct**; P3's 0.45 ("the useful corollary follows immediately")
**correct to have discounted** — the corollary needed `noLam_peelPis` *and* the
`betaHead`-is-identity lemma, neither of which existed; P3's 0.6 ("a closure invariant is needed")
**CORRECT**; its 0.4 ("it already exists in the tree") **WRONG** — M5's `shape.lean` run had
already told me 0 hits, and nothing turned up. P4 (0.2 that it is false) **correctly low**: no
`ctorTr?` clause emits `.lam`, and the `.bvar` clause was the only real risk.

### M8. **B6 part 1 built and part 2 discharged** — `Verify/Inductive/B6.lean` §2-§5, 0 errors 0 warnings
The two-pass construction, with the circularity broken by the tree's own `VIndHeader`:
- `VIndHeader.idRestore`, `VInductDecl'.header_idRestore` (**`rfl`**), `VIndHeader.recArgOf`,
  `VIndHeader.recArgOf_header` (**`rfl`**) — so pass 2's reader **is** `VInductDecl'.recArgOf`,
  not a new one.
- `VIndRestore.recogAt_congr`, `VIndRestore.recog_congr`, `VIndHeader.recArgOf_congr` — the
  recogniser only inspects members `k < nm`, so pass 1's header only has to be right below `nm`.
- `VIndHeader.setRecArgs` / `setRecArgsD` (pass 2), `surfHeader` (pass 1's header),
  **`surfInductDeclR?` = `(surfInductDecl? …).map (surfHeader …).setRecArgsD`** — the two passes as
  a literal composition, so `SurfaceMap.lean` is untouched (I do not own it).
- §3.1: pass 2 moves no name, no field *type*, no `params`, no `args`, no `tyApp`, no `nameSkelV`.
- **`VIndHeader.setRecArgs_typeR` — B6 PART 2**, and it is `VIndCtor.typeR_id`, not `restore_noK`
  (M3).
- **`recArgOf_surfHeader` — the two passes are WELL FOUNDED**: the reader pass 2 ran with equals
  `VInductDecl'.recArgOf` at the *finished* block, as an equation at every index and every stored
  type. This is what makes "populate `recArg` via `recArgOf`" a reading of the declaration rather
  than a circular definition.
- **`recArg_surfInductDeclR?` — B6 PART 1 at the field**: every field of the output carries the
  `recArg` the output block's own reader returns. `recArg := none` is gone.
- **`recArg_eq_recog_surfInductDeclR?`** — composing §1: the stored `recArg` is the answer of the
  **single-stage syntactic** `VIndRestore.recog`. The `whnf` gap cannot open here.
- §5: `surfInductDeclR?_data`, `nameSkelV_surfInductDeclR?` (still an *equation*),
  `skelPrefix_surfInductDeclR?`, `length_surfInductDeclR?`, `trType_surfInductDeclR?`,
  `ctorStoresTr_surfInductDeclR?`, `trCtors_surfInductDeclR?`, `surfInductDeclR?_arms_ctorTr`.
- §5.1 **`ctorStoresTr_of_ctorTr_setRecArgs` — B6 PART 3, verified not redone**: a one-line
  application of `ClaimB`'s `ctorStoresTr_of_ctorTr` at the populated block and an arbitrary `R`.
  The lemma needed no change, which is exactly the predecessor's claim.

### M9. **THE HEADLINE — `ntreeRTypes_mapsR` is `rfl`**
```
theorem InductiveDeclExamples.ntreeRTypes_mapsR :
    surfInductDeclR? (vtr? [`u]) 1 [.sort (.succ (.param 0))] (.succ (.param 0)) true
      ntreeRTypes = some ntreeAux := rfl
```
`SurfaceMap.lean`'s `ntreeRTypes_maps` lands on **`eraseRecArgs ntreeAux`**; the two-pass map lands
on **`ntreeAux` itself**, `recArg`s included, by *computation*. Hand-checked before elaborating and
then confirmed by the elaborator: at `ntreeNode`'s field 1 the reader sees
`.app (.const _nested.List_1 [.param 0]) (.bvar 1)` at field index `i = 1`, `nA = np = 1`,
`(tyArgs 1).map (·.liftN (0+1)) = [.bvar 1] = sp.take 1`, spine head `= .const (names 1) (params 1)`,
so it returns `{binders := [], idx := 1, args := []}` — `ntreeNode`'s stored `recArg` on the nose;
member 0 (`NTree`) is tried first and rejected on the head. Field 0 (`.bvar 0`) gets `none` at
every member, as stored.
A direct consequence visible in the witness: `ntreeAux_b6_witness` needs **no erasure bridge**,
where `SurfaceMap.lean`'s `ntreeAux_surfaceMap_witness` had to relate `eraseRecArgs ntreeAux` to
`ntreeAux` by hand at every member.

### M10. Axioms — **76 `#print axioms` lines, all inside the whitelist, no `sorryAx`**
Distribution: 11 lines "does not depend on any axioms"; the rest `[propext]`,
`[propext, Quot.sound]`, or `[propext, Classical.choice, Quot.sound]` (the last only for the five
arms that touch `TrExprS`/`VEnv`, i.e. `trType_surfInductDeclR?`,
`ctorStoresTr_surfInductDeclR?`, `trCtors_surfInductDeclR?`, `surfInductDeclR?_arms_ctorTr`,
`ctorStoresTr_of_ctorTr_setRecArgs`, and the witness). The five `private` helpers report under
their mangled `_private.…` names, which is expected and still checkable.
`lean_diagnostic_messages` with `severity=warning`: **0 warnings from `B6.lean`**.

### M11. The witness, and the exclusions
`Lean4Lean.InductiveDeclExamples.ntreeAux_b6_witness`, **arity 0**, eighteen conjuncts:
non-degeneracy (uvars 1, params `[Type u]`, 2 members, `ntreeNode` has 2 fields); the two-pass map
lands on `ntreeAux` and the blind map on the erasure; `ntreeNode.recFields.length = 1` vs the
erasure's `0` and `nlistCons.recFields.length = 2`; part 1 through `recArgOf_surfHeader` and
`recArg_surfInductDeclR?`; **single-stage** via `recArg_eq_recog_surfInductDeclR?`; the skeleton
*equation* plus `SkelPrefix`/`TrCtorsLen`/`CtorNameOwn`; part 2 via `VIndHeader.setRecArgs_typeR`;
the three arms at an arbitrary environment and arbitrary sound oracle; three negative controls.

**Exclusions (measured).** Closure **170** modules, one import (`ClaimB`). 35 modules in the tree
mention `TrIndDeclN`/`TrIndCtorR`/`TrIndType`; **20 are in the closure, 15 excluded.** The 15
excluded include **every** module holding a hand-built `ntreeAux` instance of what §6 concludes:
`TrIndDeclNProducer` (the hand-built `ntreeAux` `trType`/`trCtors`, *and* my named consumer),
`CtorPointwise`, `TrTypeProducer`, `TrSpineProducer`, `TrIndDeclNCtorOwn`, `FlipConstruct`
(`tr_ntreeType`, `tr_ntreeNodeType`), `FlipGeneral`, `FlipRemainder`, `FragmentWiden`,
`RestoreFaithful`, `RunIdentity`, `SpineClosedLand`, `HargsAttack`, `StagesFiring`, and
`MemberRedexScan` (the 790-field coverage measurement). Ten in-closure modules are inherited
through `ExprConstructionScope` (`ValAtParam`, `NestedRestoreWit`, `AddDeclWF`, `NestedRestore`,
`RestrictCompanion`, `SpineClause`, `ArgsTypedSupply`, `ValAtPrice`, `NestedOccData`,
`SpineTransfer`) — checked individually: **none holds a hand-built `TrIndType`/`TrIndCtorR` at
`ntreeAux`**; they mention the relation in prose or at other blocks. This is the price `ClaimB`
already disclosed for using the real supplier, and nothing here cites any of them.

### M12. Negative controls — **three, two on the artefact**
1. `ntreeRTypesBad_recArg_none` (**on the artefact, and it is a `recArg` control**): `NTree.node`'s
   recursive field applied to `Type u` instead of the block parameter `α`. Every name is still
   fresh, the type still translates, and the map **still succeeds** — the guard looks at the
   *target*, which is unchanged — but `recogAt`'s parameter-run test fails and the field is stored
   `recArg = none`. Paired with `ntreeAux_node_field1_recArg` (`some ⟨[], 1, []⟩`) this is the
   contrast: `recArg` is **read**, not stamped.
2. `ntreeRTypesRenamed_failsR` (**on the artefact**): rename the auxiliary member without renaming
   its occurrences and the two-pass map returns `none` — pass 2 never runs. `rfl`.
3. `roRedex_not_noLam` / `roRedex_betaHead_ne` / `roRedex_recog_ne_recArgOf` (**on the premise**):
   §1's `noLam` hypothesis is load-bearing. At `ROWit`'s block — accepted by `Lean4Lean.addDecl` —
   `noLam` is `false`, `betaHead` genuinely moves the term, and single-stage `recog` and two-stage
   `recArgOf` **disagree**. So §1's conclusion says something the general case denies.

### M13. **A VACUITY FINDING in `SurfaceMap.lean` §6 — refuted, then repaired**
Checked before closing rather than inherited. `SurfaceMap.lean` §6's oracle-dependent conjuncts read
`∀ env Us, OracleSound (vtr? [`u]) env Us → …`. **That premise is false at every environment**, and
now machine-checked: `Lean4Lean.InductiveDeclExamples.not_oracleSound_vtr?` (arity 3, cone 3605,
0-hole, 0-sorryAx). The witness is one line — `vtr? Us' (.bvar 0) = some (.bvar 0)` by `rfl`, while
`TrExprS.bvar` (`Verify/Typing/Expr.lean:154`) requires `Δ.find? (.inl i) = some (e, A)` and the
empty `VLCtx` has no entries. `vtr?` deletes exactly the context lookup `ctorTr?`'s `.bvar` clause
performs (`(bvarCtx Γ).find? (.inl i)`), and that clause is what soundness turns on.
So **four conjuncts of `ntreeAux_surfaceMap_witness` are vacuously true.** The file's docstring does
say `vtr?` "is not sound on its own" — the prose was honest, the *witness* was not tight. I kept the
three `vtr?` arms in my witness for continuity with that statement and then made them redundant.

**The repair, in §6.3, and it is entirely positive:**
- `ntreeΓc` — the two block constants as a table, `uvars = 1`, stored type `∀ (α : Type u), Type u`.
- `ntreeEnv` — a `VEnv` holding exactly it; `constLookup_ntreeEnv` is `fun _ _ h => h`.
- `constLookup_staged_ntree` — the same at every staged environment, through `FlipWiring.lean`'s
  `constLookup_staged_of_split` (every entry is a pre-block constant, so the block half is never
  needed).
- **`oracleSound_ntree : OracleSound (ctorOracle ntreeΓc Us) ntreeEnv Us`** — `ClaimB`'s producer,
  at a *concrete* environment. Exactly what `not_oracleSound_vtr?` says `vtr?` can never give.
- **`ntreeRTypes_mapsR_ctorTr` — the two-pass map lands on `ntreeAux` at the REAL `ctorTr?`
  supplier, by `rfl`** (arity 0, cone 1044). So `vtr?` was only ever a computational convenience:
  `ctorTr?` with this table infers every member and constructor type of the post-elimination block,
  and the `recArg` reader answers the same.
- Hence `ntreeAux_b6_witness` now carries the three arms at `ntreeEnv` with **no oracle hypothesis
  at all**, plus `∀ env Us, ¬ OracleSound (vtr? [`u]) env Us` as an explicit conjunct so the
  vacuity is recorded in the artefact and not only in prose.

### M14. Cones and cleanliness of every deliverable (`scripts/exists.lean`, population 462-463)
| declaration | arity | cone | own hole | sorryAx in cone | watched in cone |
|---|---|---|---|---|---|
| `Lean4Lean.VExpr.betaHead_eq_self_of_noLam` | 2 | **460** | false | **false** | **none of 6** |
| `Lean4Lean.VInductDecl'.recArgOf_eq_recog_of_noLam` | 4 | **874** | false | **false** | **none of 6** |
| `Lean4Lean.surfInductDeclR?` | 6 | **928** | false | **false** | **none of 6** |
| `Lean4Lean.noLam_of_ctorTr` | 6 | **957** | false | **false** | **none of 6** |
| `Lean4Lean.InductiveDeclExamples.ntreeRTypes_mapsR` | **0** | **994** | false | **false** | **none of 6** |
| `Lean4Lean.InductiveDeclExamples.ntreeRTypes_mapsR_ctorTr` | **0** | **1044** | false | **false** | **none of 6** |
| `Lean4Lean.InductiveDeclExamples.oracleSound_ntree` | 1 | **1160** | false | **false** | **none of 6** |
| `Lean4Lean.recArgOf_surfHeader` | 10 | **1254** | false | **false** | **none of 6** |
| `Lean4Lean.recArg_surfInductDeclR?` | 17 | **1265** | false | **false** | **none of 6** |
| `Lean4Lean.ctorStoresTr_of_ctorTr_setRecArgs` | 9 | **1266** | false | **false** | **none of 6** |
| `Lean4Lean.recArg_eq_recog_surfInductDeclR?` | 22 | **1383** | false | **false** | **none of 6** |
| `Lean4Lean.VIndHeader.setRecArgs_typeR` | 4 | **1761** | false | **false** | **none of 6** |
| `Lean4Lean.ctorStoresTr_surfInductDeclR?` | 11 | **1935** | false | **false** | **none of 6** |
| `Lean4Lean.InductiveDeclExamples.not_oracleSound_vtr?` | 3 | **3605** | false | **false** | **none of 6** |
| `Lean4Lean.InductiveDeclExamples.ntreeAux_b6_witness` | **0** | **4347** | false | **false** | **none of 6** |

**And the predecessor's two cone figures reproduce EXACTLY**: `Lean4Lean.ctorStoresTr_of_ctorTr`
arity 8 cone **1225**, `Lean4Lean.VInductDecl'.recArgOf` arity 3 cone **848** — the numbers its M10
reported. Its cone measurements are exact.

### M15. Round-close numbers
- whole-tree `lake build`: **exit 0**, **1648 jobs**. (Predecessor: 1645. +1 is `B6`; the other +2
  are two other streams' files that landed mid-round — `git log` gained `cca6500`, `4725908`,
  `44a66bc`, and `docs/handoff-descendsurplus.md` appeared untracked.)
- `scripts/sorry-census-all.lean --run`: **BUILT 465; NOT BUILT 0; HOLES 13.** Target met.
  `B6` appears in the 53-module orphan list — expected, nothing imports it yet.
- Guard 1: "Axioms.lean declares exactly the 24 frozen axioms ✓".
  Guard 2: "kernel_sound axioms within whitelist ✓ (proof INCOMPLETE: sorryAx present)".
  Guard 3: "checker cone implementation gaps within frozen list (2/2 remaining) ✓".
  All three re-run at the final state. `git status --porcelain -- Lean4Lean/Verify/Guard.lean` is
  **empty**: the file's *content* was never touched (only its mtime, to force the rebuild).
- `scripts/layer-check.py`: **exit 0**, hard rule "66 module(s) checked, none reaches Verify/".
  Soft report: 4 `Theory/` files with 1 direct `Verify/` import each (unchanged), and a **new**
  soft section (10 `Theory/` modules transitively downstream of `Verify/`) added by another
  stream's `cca6500`. Not mine, not a gate.
- **Warnings: 0 from `B6.lean`** (both `lake build` and `lean_diagnostic_messages severity=warning`).
  In-repo "not explicitly referenced" total is **63 across 23 files** — identical to the
  predecessor's figure, so no drift this round. Not my gate.
- **Axioms: 83 declarations, 83 `#print axioms` directives, exact 1-1 match (checked
  programmatically, not by eye)**; 13 "does not depend on any axioms", 11 `[propext]`,
  51 `[propext, Quot.sound]`, 8 `[propext, Classical.choice, Quot.sound]`. **Zero lines mention
  `sorryAx`.**
- **Claim A confirmed untouched**: `git diff --stat HEAD -- Lean4Lean/Verify/Inductive/` is
  **empty**; `git status --porcelain` lists my two files (`?? Lean4Lean/Verify/Inductive/B6.lean`,
  `?? docs/handoff-b6.md`) plus another stream's `?? docs/handoff-descendsurplus.md`. No Claim A
  file was opened for writing.
- Frozen files (`Verify/Soundness.lean`, `Verify/Axioms.lean`, `Verify/Guard.lean`): `git diff` is
  empty for all three, and **no frozen edit is requested by this round.**
- Consumer: `scripts/can-cite.py Lean4Lean.Verify.Inductive.TrIndDeclNProducer
  Lean4Lean.surfInductDeclR?` → **NO**, "would have to gain `Lean4Lean.Verify.Inductive.B6`" — one
  import, and it is cycle-free (B6 closure 170, `TrIndDeclNProducer` closure 173, neither contains
  the other, union 179, so the consumer gains 6 modules).

### M16. Prior scoring, closed
- **P1** (part 3 already done; 0.75) — **CORRECT**, and its residual (0.5, a missing field-side
  analogue) **refuted**: `CtorStoresTr` speaks about `C.typeR D R j`, which reads `recArg` through
  `fieldTypesR`, so `ctorStoresTr_of_ctorTr` is already `recArg`-aware and needed no change.
- **P2** (two passes forced; 0.7) — **CORRECT**, and the forced shape is the tree's own
  `VIndHeader`. The 0.45 "cheaper shape" branch is refuted as stated (`recog` needs `nm` and the
  member names, not just `R`) but right in spirit: pass 1 needs only the member *headers*, and §2.1
  weakens it further to "right below `nm`".
- **P3** (`.lam`-free lemma true; 0.8 / corollary immediate 0.45 / invariant needed 0.6 / already
  in tree 0.4) — **TRUE in the strong form**; the corollary was *not* immediate (0.45 correctly
  discounted); the closure invariant *was* needed (0.6 **correct**); it was **not** already in the
  tree (0.4 **wrong**, and M5 had already told me so).
- **P4** (0.2 that it is false) — correctly low; no `ctorTr?` clause emits `.lam`, and the `.bvar`
  clause returns the variable itself.
- **P5** (`InductiveDeclExamples` already exists, witness is a theorem about it; 0.7) —
  **CORRECT**. The 0.5 "closes by `rfl`" — **CORRECT and understated**: the headline
  `ntreeRTypes_mapsR` is `rfl`, and so is the `ctorTr?` version. `native_decide` never used;
  the hard constraint I set in P5 held.
- **P6** (`restore_noK` is the route; 0.6/0.4) — **WRONG in mechanism** (M3). Part 2 is
  `VIndField.typeR_id`, `@[simp]` and unconditional since ruling 116d; `restore_noK` asks
  `VExpr.NoConsts K` of the whole subterm and therefore cannot apply to the very field that must
  move. Scored **0.3**. This is the round's one clear inherited error: the predecessor's part-2
  route was a red herring, and the brief relayed it.
- **P7** (control on the artefact; 0.7) — **CORRECT**, and I got two on the artefact plus one on
  the premise.
- **P8** (Claim A untouched; 0.95) — **held**.
- **P9** (round-close; 0.85) — census exactly right, guards exactly as predicted, warnings
  **exactly** 63/23 with no drift. Scored **1.0**.
- **P10** (cycle-free; 0.85) — **CORRECT**, re-measured.
- **P11** (stale `.olean`s; 0.5) — wrong for the four named modules, right that the trap was live:
  **13** orphan `.olean`s existed and were deleted before any population walk.
- **What I did not price at all, and should have**: that the *inherited witness's* premises might be
  unsatisfiable (M13). Nothing in my priors covers "check the premise is satisfiable before quoting
  the conjunct". That is the lesson to carry: an arity-0 witness whose conjuncts are implications
  proves nothing until the antecedent is exhibited.

## What remains of Claim B

B1-B7 are now closed. What is left on the translation side is **not** B6:
1. **The user's original block.** `surfInductDeclR?`'s domain is the *post-elimination* member list
   (`ntreeRTypes`), whose auxiliary member is still `_nested.List_1`, and §4/§5 are stated at
   `D.idRestore`. Relating the **user's** `inductive NTree (α) | node : α → List (NTree α) → NTree α`
   to the same `D` needs the *real* restoration `ntreeRestore`, and that is where the populated
   `recArg`s now do work: `VIndField.typeR`'s `some` branch is `R.restore D i F.type`, which is no
   longer the identity. `ClaimB`'s `ctorStoresTr_of_ctorTr` (part 3) is already stated at arbitrary
   `R`, and `ctorStoresTr_of_ctorTr_setRecArgs` is it at the populated block — so the *lemma* is
   ready; what is missing is the per-constructor equation
   `C.typeR D ntreeRestore j = ctorTr?`'s output on the **user's** constructor type. The name side
   of that composition is already done (`skelPrefix_of_surfInductDecl?_run` chains with
   `runSkelExtends` by `rfl`).
2. **Completeness of the reader in the residue.** §1 shows the `whnf` gap cannot open on the map's
   own output. It still can on a block the kernel accepts directly: a redex **under a binder**
   (`∀ y, (fun x => I) y`) or one needing **δ**. Those need `AddInductive.isRecArg`'s full whnf
   loop, `Verify/Inductive/MemberRedexScan.lean` measures **0** such fields in the running
   environment, and the residue is named rather than measured away. Unchanged by this round.
3. **`VInductDecl'.WF`**, which is what actually *reads* `recArg` (`VIndField.WF.pos`). The
   translation relation still never reads it — that was always correct — so populating it is a gain
   for the restoration and for `WF`, not for `TrIndDeclN`.
