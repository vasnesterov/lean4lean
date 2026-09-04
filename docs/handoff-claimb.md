# handoff-claimb — B5 (composition), B6 (real restoration), B7 (recArg)

Owned files: `Lean4Lean/Verify/Inductive/ClaimB.lean` (new), `docs/handoff-claimb.md` (this).
Round start: `git status` shows ` M Lean4Lean/Verify/Inductive/SurfaceMap.lean`, `?? docs/handoff-crse.md`
— both other streams' work in flight. HEAD = d337a58.

## Priors (written BEFORE any measurement)

- P1. B5: the assignment says `trIndType_of_ctorTr` / `trCtors_of_ctorTr` are uncitable from
  `SurfaceMap.lean` in BOTH directions. Prior: the new module must import both
  `SurfaceMap` and whatever module holds the `*_of_ctorTr` producers. Expect that to be a
  leaf below nothing, i.e. nothing imports it yet => I must name a consumer explicitly.
  Confidence that a plain two-import module compiles: 0.75 (layer-check.py may forbid it).
- P2. B5: `OracleSound` is likely a structure/def of the "for every surface ctor, the oracle's
  output is a real translation" shape. Prior: dischargeable from the inferencer producers with
  a `fun .. => trIndType_of_ctorTr ..`-style term, no new induction. Confidence 0.6.
- P3. B6: `D.idRestore` vs `ntreeRestore`. Prior: the missing data is the *level*/*motive*
  reindexing plus the nested-tree positions; the name side being `rfl`-chained suggests the
  remaining obligations are (a) the restore map's action on ctor types and (b) that it is a
  left inverse on the post-elimination list. Prior: I can prove (a)-shaped congruence and will
  have to *state* (b). Confidence of fully closing B6: 0.25.
- P4. B7: `recFields.length` 0 vs 1. Prior — and this is the interesting one — `recArg` IS
  recoverable from the translated ctor type, because recursive occurrences are exactly the
  occurrences of the block's own type constants in the ctor's telescope, and the translation
  is injective on head constants. So I expect B7 = "derivable, not surface data". Confidence 0.55.
  The competing prior: `recArg` records a *positional index into the surface args* that the
  post-elimination type no longer distinguishes (nested params get erased), in which case it
  needs surface data. Confidence 0.45. I will machine-check rather than argue.
- P5. Supplier: I intend the CHECKER route (`TypeChecker.checkType.WF`), since the assignment
  measured its marginal cost at the artifact as ZERO (already contained in `addDecl.WF` 20365
  and `Bridge.kernel_sound_of` 20447) vs +94 constants for the fragment route. Prior: no
  contamination either way; zero marginal cost decides it.
- P6. Claim A (twelve `TrIndDeclN` field producers) must end the round untouched. I will not
  edit any Claim A file; I will re-verify by `git status` at close.

## Measurements (appended as made)

### M1. Tree state at round start
`lake build` from the modified tree: **exit 0** (green). HEAD d337a58, with another stream's
` M Lean4Lean/Verify/Inductive/SurfaceMap.lean` in the tree.

### M2. Where B5's two producers actually live (grep, then confirmed by `exists.lean` below)
- `Lean4Lean.trIndType_of_ctorTr` — `Lean4Lean/Verify/Inductive/FlipWiring.lean:143`
- `Lean4Lean.trCtors_of_ctorTr`  — `Lean4Lean/Verify/Inductive/TrExprSGeneral.lean:288`
- `Lean4Lean.OracleSound`        — `Lean4Lean/Verify/Inductive/SurfaceMap.lean:352`
Import chains: `FlipWiring` imports exactly `TrExprSGeneral`; `TrExprSGeneral` imports exactly
`ExprConstructionScope`; `SurfaceMap` imports exactly `CtorsLenGeneral`. So the two families are
siblings under `Verify/Inductive/`, neither above the other — consistent with the brief's
symmetric NO from `can-cite.py`, and it means **a new module importing `SurfaceMap` +
`FlipWiring` sees both** (FlipWiring drags TrExprSGeneral, so one import covers both producers).

### M3. `recArg` — the pre-existing in-repo prose, found BEFORE writing anything (B7)
`Lean4Lean/Theory/Inductive/Decl.lean` already carries two claims about this:
- L963-967: "`VIndType.indices`, `D.params`, `D.lvl`, `VIndField.lvl`, `VIndField.recArg` and
  `D.isLE` are all unrecoverable from the declaration".
- L1044 table row: "`fields[i].recArg` | checker | `checkPositivity`/`isRecArg`".
- L1067: `VIndCtor.skeleton` deliberately omits `lvl` and `recArg`.
And `VIndCtor.recFields` (Decl.lean:353) is **derived, not stored**:
`C.fields.zipIdx.filterMap fun (F, i) => F.recArg.map fun r => (i, r)`.
So B7 is NOT "is `recFields` stored" — it is entirely a question about `VIndField.recArg`.
The map already sets `recArg := none` at every field (SurfaceMap.lean:145), and the last round's
machine-check of the gap is SurfaceMap.lean:727-728 via an existing `eraseRecArgs`.

### M4. What `VIndField.WF.pos` demands of `recArg` (Decl.lean:463-535) — this decides B7
- `recArg = none` branch: `∃ A, D.NoBlock A ∧ env.IsDefEqType D.uvars Γ F.type A`
  — i.e. **only definitionally** block-free (deliberate: the comment cites
  `| mk : (r : T) -> (fun _ : T => Nat) r -> T`, which both kernels accept).
- `recArg = some r` branch: `r.idx < D.nm`, arg-count matches the member's index telescope,
  `binders`/`args` syntactically `D.NoBlock`, `IsDefEqType F.type (r.canonType D i)`, plus F7's
  residual clause `D.ResidualClean (r.binders.length + i) F.type`.
Both branches tie `F.type` to the canonical data **up to defeq only**. That is the crux:
`isSome` is forced (a syntactic block occurrence cannot be defeq to a block-free `A` in the
staged env where the block constants are opaque), but `r`'s *components* are defeq-slack — which
is exactly the freedom `VIndRecArg.exists_indep` is stated to exploit.

### M5. B5 is genuinely open — `shape.lean`, deliverable AND helper shapes
- `HEADS="OracleSound"`: **5 hits, all CONSUMERS** (`ntreeAux_surfaceMap_witness`,
  `ntreeAux_ctorStoresTr`, `ctorStoresTr_surfInductDecl?`, `trType_surfInductDecl?`,
  `trCtors_surfInductDecl?`) — every one takes it as a hypothesis. No producer.
- `HEADS="OracleSound ConstLookup"`: **NOTHING** (heads both resolved). So no theorem in the
  tree derives `OracleSound` from a `ConstLookup`. B5 is open.
- `exists.lean`: `Lean4Lean.eraseRecArgs` **NOT FOUND** — it is
  `Lean4Lean.InductiveDeclExamples.eraseRecArgs` (SurfaceMap.lean:579), inside the examples
  namespace. Recorded because it is exactly the "different name" trap.

### M6. Cleanliness of the two candidate suppliers (`exists.lean`, population 458)
| supplier | module | cone | own hole | sorryAx in cone | WATCHED IN CONE |
|---|---|---|---|---|---|
| `Lean4Lean.ctorTr?` | `Verify.Inductive.TrExprSGeneral` | **912** | false | **false** | **none of 6** |
| `Lean4Lean.trExprS_of_ctorTr` | `Verify.Inductive.TrExprSGeneral` | **1148** | false | **false** | **none of 6** |
| `Lean4Lean.trIndType_of_ctorTr` | `Verify.Inductive.FlipWiring` | **1156** | false | **false** | **none of 6** |
| `Lean4Lean.trCtors_of_ctorTr` | `Verify.Inductive.TrExprSGeneral` | **1257** | false | **false** | **none of 6** |
| `Lean4Lean.TypeChecker.checkType.WF` | `Verify.TypeChecker` | **18795** | false | **true** (8 holes) | ***`Lean4Lean.VEnv.IsDefEq.uniq`, `Lean4Lean.VEnv.IsDefEq.uniqU`*** |
The checker route's 8 holes, verbatim: `Lean4Lean.TrProj.weak'_inv`,
`Lean4Lean.TypeChecker.Inner.isDefEqUnitLike.WF`,
`Lean4Lean.TypeChecker.Inner.tryEtaStructCore.WF`, `Lean4Lean.VEnv.IsDefEqU.weakN_iff`,
`Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified`, `Lean4Lean.VEnv.WF.rigidShapeUniqNS`,
`Lean4Lean.VEnv.NormalEq.descend`, `Lean4Lean.TypeChecker.Inner.inferProj.WF`.
(Confirms the brief's "cone 18795, 8 holes, both watched" exactly.)

### M7. **The supplier choice is forced, not a preference** — and this is the round's first real finding
`OracleSound` (SurfaceMap.lean:352) quantifies over a **pure function**
`tr : Expr → Option VExpr`. `Lean4Lean.ctorTr?` *is* such a function (arity 4, total, `Option`).
`Lean4Lean.TypeChecker.checkType.WF` is
`M.WF c s (checkType e) fun ty _ => ∃ e' ty', c.TrTyping e ty e' ty'` — a **monadic
postcondition with an existential**, at a `VContext`, not a function and not `TrExprS env Us []`.
So the checker route cannot instantiate `OracleSound` at all without first extracting a pure
function from a monadic run. **I use the fragment route (`ctorTr?`)**: forced by the shape of the
obligation, and it happens also to be the clean one (0 holes, 0 watched, cone 912/1148).
The brief's "+94 constants at the artifact" is the price, paid for a supplier that is 0-hole and
0-watched rather than one that carries `IsDefEq.uniq`/`uniqU`.

### M8. **B7: the recogniser already exists** — `Lean4Lean.VIndRestore.recog`
`Lean4Lean/Theory/Inductive/NestedBuild.lean:144-180` already contains, with proofs:
- `Lean4Lean.VIndRestore.recogAt (R : VIndRestore) (i k : Nat) (S : VExpr) : Option VIndRecArg`
- `Lean4Lean.VIndRestore.recog (R : VIndRestore) (nm i : Nat) (S : VExpr) : Option VIndRecArg`
  `= (List.range nm).findSome? fun k => R.recogAt i k S`
- `Lean4Lean.VIndRestore.recogAt_sound` / `Lean4Lean.VIndRestore.recog_sound`:
  `R.recog nm i S = some r → ∀ D, r.canonTypeR D R i = S`
- plus `recogAt_idx`, `recogAt_binders`, `recog_binders`, `recog_idx_lt`.
Its docstring says outright: "Nothing about `D` enters: `VInductDecl'.tyAppR` ignores its
`VInductDecl'` argument, so the recogniser is a function of **the restoration alone**."
**This is a reader for `VIndField.recArg` off a field type, and it takes no surface data.**
It is the direct answer to B7 and I found it before writing a line of my own reader — logging it
here as the eighth already-done catch, and it was `shape.lean`'s 103-hit `recFields` query plus a
`grep` for `VIndRecArg`-valued definitions that surfaced it, not a deliverable-shaped query.

### M9. Import geometry, measured (`can-cite.py` + closure arithmetic)
- `can-cite.py Lean4Lean.Verify.Inductive.SurfaceMap …`:
  **NO** `Lean4Lean.trIndType_of_ctorTr` (in `Verify.Inductive.FlipWiring`),
  **NO** `Lean4Lean.trCtors_of_ctorTr` (in `Verify.Inductive.TrExprSGeneral`)
  — the brief's claim reproduced.
  **YES** `Lean4Lean.VIndRestore.recog`, **YES** `Lean4Lean.VIndRestore.recog_sound`
  (both `Theory.Inductive.NestedBuild`) — so B7's recogniser is *already* citable at
  SurfaceMap's own position, and a fortiori at mine.
- `can-cite.py Lean4Lean.Verify.Inductive.TrIndDeclNProducer …`:
  **NO** `Lean4Lean.OracleSound`, **NO** `Lean4Lean.surfInductDecl?` (both in `SurfaceMap`),
  **YES** `Lean4Lean.VIndRestore.recog`.
- Closures: `SurfaceMap` 148, `FlipWiring` 198, union **200**; `ClaimB` itself = **201**.
  `TrIndDeclNProducer` closure 207, already contains `FlipWiring`, does **not** contain
  `SurfaceMap`, and is **not** in ClaimB's closure — so `import ...ClaimB` there is cycle-free.
  (`AddDeclWF` and `NestedRestore` ARE in ClaimB's closure, so they cannot be consumers.)

**CONSUMING MODULE: `Lean4Lean.Verify.Inductive.TrIndDeclNProducer`.** It is the module that
assembles `TrIndDeclN` field-by-field (`trCtors := trCtors_of_ctorTr hΓc hctr`, line 100) and it
is exactly the one that today cannot see `OracleSound`/`surfInductDecl?`.

### M10. **B6 is not independent of B7** — and the "boundary" in SurfaceMap's docstring is a consequence, not a choice
`VIndCtor.fieldTypesR C D R = C.fields.zipIdx.map fun (F, i) => F.typeR D R i`
(`Theory/Inductive/Restore.lean:557`), and
`VIndField.typeR F D R i = match F.recArg with | none => F.type | some _ => R.restore D i F.type`
(Restore.lean:520). The map sets `recArg := none` at **every** field (SurfaceMap.lean:145).
Therefore at the map's output `C.fieldTypesR D R = C.fields.map (·.type)` **for every `R`** —
the restoration is a no-op on the entire field telescope, and the only `R`-dependence left in
`C.typeR D R j = mkPi (C.params ++ C.fieldTypesR D R) (D.tyAppR R j C.fields.length C.args)`
is the **result head**.
So the map's output cannot match the user's constructor type at `ntreeRestore` no matter what
restoration is supplied: the user's `NTree.node` has field `List (NTree α)` and the map's has
`_nested.List_1 α`, and no restoration can move it while `recArg = none`.
**B6 is blocked on B7, and populating `recArg` is what unblocks it.** This inverts the framing
in SurfaceMap's "The restoration is the identity here, and that is a boundary, not an oversight"
paragraph: it is the identity because `recArg` is `none`, not because the domain is the
post-elimination list.

### M11. B7's arithmetic checked by hand before coding, at `ntreeNode` field 1
`ntreeNode.fields[1].type = .app (.const `_nested.List_1 [.param 0]) (.bvar 1)`, i = 1
(`Theory/Inductive/NestedHead.lean:603`). `ntreeAux.idRestore`: `tyName 1 = `_nested.List_1`,
`tyLvls _ = ntreeAux.ownLvls = [.param 0]`, `tyArgs _ = bvars 0 1 = [.bvar 0]`.
`recogAt R 1 1 S`: `S.piArity = 0` so `ξ = []`, `b = S`; `b.spineFn = .const `_nested.List_1
[.param 0]` matches; `nA = 1`; `sp.take 1 = [.bvar 1]` and
`(tyArgs 1).map (·.liftN (0 + 1)) = [.bvar 1]` — equal; `1 ≤ 1`. Returns
`some { binders := [], idx := 1, args := [] }` = `ntreeNode.fields[1].recArg` **on the nose**.
Field 0 (`type := .bvar 0`) has `spineFn = .bvar 0`, matching no member constant, so `none` —
also correct. Same check passes at `nlistCons`' two fields (idx 0 and idx 1).
**Predicted: B7 is DERIVABLE with no surface data, and by an existing recogniser.**
