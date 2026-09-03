# Handoff: the **undecomposed whole-type bridge**, in general

**Owner files:** `Lean4Lean/Verify/Inductive/WholeTypeBridge.lean` (new, mine) and this file.
**Written incrementally from minute one**, per the standing rule.

## 0. Pre-flight — every name the brief names, against the compiled environment

`scripts/exists.lean`, population **426** built modules (the brief's predecessors ran at 421-425;
the tree moved, and `Theory/Inductive/NestedRules.lean` is now committed).

| name | arity | cone | own hole | reaches `sorryAx` |
|---|---|---|---|---|
| `VIndRestore.substC_fieldTypes_defeq'` | 8 | 972 | false | **false** |
| `VEnv.ctorConstsCR_wf_of_fieldsD` | 15 | 2529 | false | **false** |
| `VEnv.ctorConstsCR_wf_of_betaD` | 22 | 2973 | false | **false** |
| `VIndRestore.csubst_WFD` | 32 | 2978 | false | **false** |
| `VIndRestore.CtorTypeBridge` | 4 | 909 | false | **false** |
| `VIndRestore.RecTypeBridge` | 4 | 947 | false | **false** |
| `InductiveDeclExamples.ntree_hbridgeD` | 15 | 2056 | false | **false** |
| `InductiveDeclExamples.ntree_ctorTypeBridge` | 3 | 1064 | false | **false** |
| `InductiveDeclExamples.ntree_recTypeBridge` | 6 | 1882 | false | **false** |
| `InductiveDeclExamples.ntreeAux` | 0 | 43 | false | **false** |
| `InductiveDeclExamples.ntreeAux_valRestC_both_stages` | 0 | 3811 | false | **false** |
| `CSubst.val_of_hasType` | 14 | 2331 | false | **false** |
| `VEnv.IsDefEq.uniq` | 12 | 3472 | false | **TRUE** — `IsDefEqU.forallE_inv_stratified` |
| `VEnv.AxiomConservativityWF` | 2 | 362 | false | false (it is a `def`, a Prop) |
| `Lean4Lean.HasArgs.of_mkApp` | — | — | — | **NOT FOUND** (the real name is `VEnv.HasArgs.of_mkApp`; not used here either way) |

So the brief's premise checks out: **no false absence in the names.**  The one nit is the brief's
`Lean4Lean.HasArgs.of_mkApp`, which is `Lean4Lean.VEnv.HasArgs.of_mkApp`; the instruction not to use
it is honoured, and `PiInv` is absent from the owner file.

### 0a. The reported-absence claims, re-verified by conclusion shape

`docs/handoff-stagemono.md` §0a's scan, re-run at population 426 (`scripts/shape.lean`):

* `HEADS="Lean4Lean.VIndCtor.typeR Lean4Lean.VIndCtor.type Lean4Lean.VEnv.IsDefEq"` → **14 hits, 0
  structure fields**, and every hit that *concludes* a whole-type ctor bridge is still
  block-specific (`InductiveDeclExamples.*`, `MRedex.MPWit.*`); the only general ones,
  `csubst_WFD` / `csubst_WFD_const`, **consume** it as `hbridgeD`.  Absence confirmed **as of now**,
  not as of the handoff that claimed it.
* `HEADS="Lean4Lean.VInductDecl'.recTypeR Lean4Lean.VInductDecl'.recType Lean4Lean.VEnv.IsDefEq"` →
  the general hits are `recConstsR_wf_of_substC'` / `recConstsR_wf_of_substCD'` /
  `recConstsR_wf_of_blocks`, which conclude `∀ c ∈ D.recConstsR R K, VConstant.WF e₂ c.2` — **not** a
  whole-pi defeq.  Every whole-pi hit is block-specific (`rRecPi0`/`rRecPi1`, `mpRecConstClause*`).
  So `RecTypeBridge`'s general form is absent too, but its *ingredients* are not (see §2).

## 1. Item (a): what is block-specific in the three concrete instances — **stated before proving**

I read all three and their real sources.  The answer is not uniform, and the non-uniformity *is* the
task.

### 1.1 `ntree_recTypeBridge` (cone 1882) — nothing block-specific but the ingredients

Its whole proof is `match j` on `ntreeAux.types` plus `rRecPi1`.  And `rRecPi1`
(`ConstSubstNested.lean` §H.2) is literally

```
VEnv.IsDefEq.mkPi_congrU (rTeleDefEq …) (by simpa using rOnCtx …) (rB1 …)
```

i.e. **`mkPi_congrU` over a telescope defeq, an `OnCtx`, and a body defeq** — the general shape.
Block-specific: `rTeleDefEq` (the concrete telescope), `rOnCtx`, `rB1`, and the two `rfl`-grade
unfoldings `rrecType_eq_1` / `rrecTypeR_eq_1`.  Nothing else.

### 1.2 `ntree_ctorTypeBridge` (cone 1064) — block-specific in the *result*, not the telescope

`ntree_ctorTypeBridge_nil`/`_cons` are `forallEDF` chains over `.beta` steps.  Read structurally they
are also `mkPi_congrU`-shaped: the parameter binder is reflexive, the `NTree` field does not move,
the *companion* field moves by one β, and **the result head moves by one β** (`_nested.List_1 α ↝
ntreeVal α`).  So at a **companion** member the result conjunct is live — unlike (A)'s, which
`CtorBeta` §2 (`ctorResult_defeq`) discharges outright, and it discharges it precisely because
`hK : T.name ∉ K`.

There is a second, easily-missed asymmetry: `CtorTypeBridge`'s **left side is not substituted**
(`C.typeR D R j`, raw, against `(C.type D j).substC (R.csubst D K)`).  So its telescope is
`C.params ++ C.fieldTypesR` against `(C.params ++ fields).map (substC · σ)` — a *different* shape
from `CtorBeta`'s `substC_fieldTypes_defeq'`, which relates the two lists **both** under `substC`.
Closing that gap needs a σ-identity on `C.typeR D R j`, which is `decide`-able per block and is not
a theorem in the tree.  §3 below states it as an explicit premise with an `↔`, so no successor
re-attacks it as though it were derivable here.

### 1.3 `ntree_hbridgeD` (cone 2056) — the one that does **not** generalise, and why

`ntree_hbridgeD` is the outlier, and this is the finding of item (a).

* block-specific plumbing: `match j` over the two members, `match ls, hlen with | [l], _` (the
  `uvars = 1` decomposition), and the `decide` that `csubstTy` and `csubst` agree on `ntreeNode`'s
  stored type.  All three are general (`substC_ctorType_csubst_eq_csubstTy` covers the last).
* the substance is `ntree_node_const_defeq`, which builds the defeq **by hand, generically in `U`
  and in the single level `l`** — `constDF`, `sortDF`, `bvar`, one `.beta`, all at free `U`, with the
  `.instL [l]` pushed through the `show` by definitional unfolding.

Compare `rRecConstClause0`/`rRecConstClause1` (§H.3), which reach the *same* free-`U`/`Γ`/`ls` shape
from `rRecPi0`/`rRecPi1` — stated at `Γ = []` and `U = recUvars`, **no `instL`** — by exactly two
steps: `IsDefEq.instL` then `IsDefEq.weak0`.

**So the two instances cope with the free level context in two different ways, and only one of them
generalises.**  `ntree_node_const_defeq`'s way (prove it at free `U`/`l` from scratch) is
irreducibly per-block; `rRecConstClause0`'s way (prove it once at `Γ = []`, `U = uvars`, then
`instL` + `weak0`) is a two-line general lemma that was never stated.  Stating it is §2 below, and it
is what makes free `ls` **not** the obstacle the brief allowed it might be.

## 2. What I proved — `Lean4Lean/Verify/Inductive/WholeTypeBridge.lean`

### §A The level/context absorber, **as an `↔`** — and free `ls` is *not* the obstacle

* `VExpr.BridgeD e n X Y` (def) — the free-`U`/`Γ`/`ls` shape, named: exactly `CSubst.WFD.const`'s
  right disjunct and exactly `csubst_WFD`'s `hbridgeD` at one constructor.
* `VExpr.bridgeD_of_bridge` — forward, from a single defeq at `Γ = []`, `U = n`, no `instL`.
  `IsDefEq.instL` then `IsDefEq.weak0`.  **The `ls.length = n` hypothesis is not used at all** in this
  direction; recorded because it looks load-bearing and is not.
* `VExpr.bridge_of_bridgeD` — backward, at `ls := VLevel.params n` via `LevelWF.instL_id`.
* `VExpr.bridgeD_iff`, `VExpr.bridgeD_iff_of_isType` — **the `↔`**, under `Ordered` and the two
  `LevelWF` side conditions (the second variant reads one of them off an `IsType`).

This is the general form of the two-line move `ConstSubstNested.lean` §H.3 makes inline
(`rRecConstClause0`/`rRecConstClause1`).  It was never stated; the sister instance
`ntree_node_const_defeq` uses the non-generalising route instead (§1.3).

**Answer to the brief's (b) caveat, precisely.**  The free level context `ls` is *not* what resists,
and `CSubst.val_of_hasType`'s asymmetry (it absorbs the level quantifier for `val` but not for
`WFD.const`) is not the obstacle here either: `WFD.const`'s quantifier is absorbed by §A instead,
directly, without going through `val_of_hasType` at all.  What is irreducible is the single `Γ = []`
defeq underneath, which is §B/§D/§E's business.

### §B The whole-type ctor bridge at a **declared** member, general

* `VIndRestore.substC_ctorType_bridge'` — the primitive: `mkPi_congrU` over `CtorBeta` §1's telescope
  (`substC_fieldTypes_defeq_of_noK`) and a result datum, with the `OnCtx` **free** from
  `IsType.mkPi_inv` off the source constant's own typing.
* `VIndRestore.substC_ctorType_bridge` — the same with the result datum discharged by `CtorBeta` §2's
  `ctorResult_defeq` (which needs `T.name ∉ K`).  **Whole premise: `CtorBeta` §3's `hfld`.**

### §C Item (b) in general: `hbridgeD` **is** obligation (A)'s `hfld`

* `VIndRestore.csubst_hbridgeD` — `hbridgeD` at **every** `U`, `Γ`, `ls`, from `hfld` alone (plus
  `D.WF`, the staging, `Ordered`, `hown`, and `(R.csubstTy D K).WF`).  Its `hfld` is *character for
  character* `VEnv.ctorConstsCR_wf_of_fieldsD`'s.  Plugs into `csubst_WFD`'s `hbridgeD` at any fixed `U`
  as `fun j T C hT hK hC => csubst_hbridgeD … U j T C hT hK hC`.
* `VIndRestore.csubst_hbridgeD_iff` — the `↔` at one constructor, so the level quantifier cannot be
  handed back.  **Why the premise is `LevelWF` and not a typing is recorded at the statement**, per
  house style: a typing route would need either `RestoreStep`'s own declaration or unique typing
  (`IsDefEq.uniq`, a hole).

Note which substitution: `(R.csubstTy D K).WF` — the *type-constants-only* one, whose `const` bridge is
the syntactic equation `substC_tyType_eq`.  It is **not** the `(R.csubst D K).WF` that
`ConstSubstNested.lean` §B refutes at parameterised blocks.

### §D `RecTypeBridge` in general

* `VIndRestore.substC_recType_bridge` — the whole-pi defeq, `mkPi_congrU` over
  `NestedTele.lean` §T15.2's `recTypeTele_teleDefEq_of_blocks` and §T15.3's body defeq, `OnCtx` free.
  This is `rRecPi0`/`rRecPi1` de-instantiated.  **No `T.name ∈ K` needed**, so it covers declared and
  companion members alike.
* `VIndRestore.recTypeBridge_of_blocks` — `RecTypeBridge` itself, from
  `recConstsR_wf_of_blocks`' own `hM`, `hQ`, `hbody` and nothing else.  `hσ` is taken at `CSubst.WFD`
  (not `WF`), the same choice `recConstsR_wf_of_substCD'` makes and for the same reason.

So `ValRestGeneral` §5's premise costs (B)'s three telescope data — confirming, now in general and not
only at `ntreeAux`, the claim that "(C)'s extra residue over (B) is a datum (B) already carries".

### §E `CtorTypeBridge` in general — the asymmetry, isolated by an `↔`

The thing the brief's three-way grouping hides: **`CtorTypeBridge`'s left side is not substituted.**
So it is not `mkPi_congrU`'s shape until one σ-identity per companion constructor is supplied.

* `VIndRestore.ctorTypeBridge_iff_substC` — **the `↔`**: given
  `(C.typeR D R j).substC (R.csubst D K) = C.typeR D R j` at the companion constructors,
  `CtorTypeBridge` *is* the symmetric whole-type bridge.
* `VIndRestore.ctorTypeBridge_of_entries` — the composition: `hnoc` + `hfld` at the companions + a
  **live** result-head defeq per companion constructor.

**The result datum is live here and free in §B, and that is content.**  `ctorResult_defeq` discharges
the result conjunct from `hK : T.name ∉ K` (`OwnId.tyAppR_eq`: at a declared member the restored head
*is* the own head).  At a companion `T.name ∈ K` and the head moves — at `ntreeAux` it is the β-step
`_nested.List_1 α ↝ ntreeVal α` that `ntree_ctorTypeBridge_nil` performs.  Stated at the statement so a
successor does not try to make §E look like §B.

## 3. Item (c): the arity-0 witness at `ntreeAux`

`InductiveDeclExamples.ntreeAux_wholeTypeBridge_witness` — **arity 0**, existentially closed over the
three staging environments (`addInduct' listDecl`, `addIndTypes ntreeAux`,
`addConstList (typeConstsC ntreeK)`), at `ntreeAux` (`uvars = 1`,
`params = [.sort (.succ (.param 0))]`, `recUvars = 2`).  Deliberately **not** `nfnAux`: at `uvars = 0`
the `ls` §A quantifies over is `[]` and §A would be vacuous, and `params = []` would empty the
parameter telescope.  `ntreeAux_uvars_pos` and `ntreeAux_recUvars_ne_uvars` record both facts as
theorems rather than as prose.

It carries, at one block simultaneously:

* **§B's whole-type ctor bridge** at the one declared constructor `NTree.node`, at `Γ = []` and
  `U = uvars = 1`, obtained from obligation (A)'s single `.beta` step — the same step
  `ntreeAux_ctorConstsCR_wf_of_fieldsD` supplies, and nothing else;
* **§C's `hbridgeD`**, the free-`U`/`Γ`/`ls` form, at every `U`;
* the specific instance `csubst_WFD` consumes, `U = recUvars = 2` with `ls.length = uvars = 1` — the
  mixed instantiation `ValRestGeneral.lean` §6's correction was about.

**The point of the witness is the route, not the statement.**  `ntree_hbridgeD` already had this
conclusion; it got it from `ntree_node_const_defeq`'s hand-built free-`U` defeq.  This witness gets it
from the *general* theorems, so it certifies that §A ∘ §B ∘ §C's hypothesis set is jointly satisfiable
at a real parameterised nested block, which is what a reduction needs to be worth anything.

`HasArgs.of_mkApp` is not used (the brief forbade it); neither is `PiInv`.  Checked by grep over the
owner file and by the axiom/cone audit.

### 3a. Anti-vacuity for §E, exhibited

* `InductiveDeclExamples.ntree_typeR_noCSubst` — §E's `hnoc` at `ntreeAux`, by `decide` per companion
  constructor (the `∀ j : Nat` needs a `match`; the equality itself is decidable).
* `InductiveDeclExamples.ntree_ctorTypeBridge_substC` — §E.1's `↔` transporting the existing
  `ntree_ctorTypeBridge` into the symmetric form.  So **both sides of §E's `↔` are exhibited inhabited**
  at a parameterised nested block, not just the side the tree already had.

## 4. Measurements — `scripts/exists.lean`, population **428** built modules

All 18 declarations: **own value is not a hole; cone does not reach `sorryAx`.**

| name | arity | cone |
|---|---|---|
| `VExpr.BridgeD` (def) | 4 | 584 |
| `VExpr.bridgeD_of_bridge` | 6 | 2014 |
| `VExpr.bridge_of_bridgeD` | 7 | 902 |
| `VExpr.bridgeD_iff` | 7 | 2091 |
| `VExpr.bridgeD_iff_of_isType` | 7 | 2112 |
| `VIndRestore.substC_ctorType_bridge'` | 13 | 2304 |
| `VIndRestore.substC_ctorType_bridge` | 15 | 2306 |
| `VIndRestore.csubst_hbridgeD` | 24 | 2468 |
| `VIndRestore.csubst_hbridgeD_iff` | 17 | 2433 |
| `VIndRestore.substC_recType_bridge` | 12 | 2265 |
| `VIndRestore.recTypeBridge_of_blocks` | 11 | 2366 |
| `VIndRestore.ctorTypeBridge_iff_substC` | 5 | 910 |
| `VIndRestore.ctorTypeBridge_of_entries` | 15 | 2476 |
| `InductiveDeclExamples.ntreeAux_uvars_pos` | 0 | 107 |
| `InductiveDeclExamples.ntreeAux_recUvars_ne_uvars` | 0 | 121 |
| `InductiveDeclExamples.ntree_typeR_noCSubst` | 6 | 999 |
| `InductiveDeclExamples.ntree_ctorTypeBridge_substC` | 9 | 1070 |
| **`InductiveDeclExamples.ntreeAux_wholeTypeBridge_witness`** | **0** | **3659** |

**Axiom bar `after ⊆ before`: met.**  `propext`, `Quot.sound`, and `Classical.choice` (the last only in
the four declarations whose cone passes through `csubst_WF_const`'s / `CtorBeta`'s own, i.e.
`csubst_hbridgeD`, `csubst_hbridgeD_iff`, `ctorTypeBridge_of_entries`, and the witness).  Nothing new
relative to `ValRestGeneral.lean`, which already carries exactly those three.

**Zero warnings**: `lake env lean Lean4Lean/Verify/Inductive/WholeTypeBridge.lean` prints only the 18
`#print axioms` lines.

## 5. Item (d): which of the thirteen holes this routes through — **NONE**

Measured with `scripts/exists.lean` over the built population, per declaration, not asserted: every one
of the 18 reports `cone reaches sorryAx: false`.  Two were specifically at risk:

* **`VEnv.IsDefEq.uniq`** — pre-flight confirms it *is* holed (`cone reaches sorryAx: TRUE`, via
  `VEnv.IsDefEqU.forallE_inv_stratified`).  It is the natural route to §A's backward direction *if* one
  reads the bridge off two typings of the same term.  §A instead goes through
  `VExpr.LevelWF.instL_id` at `VLevel.params n`, which is syntactic.  §C's `↔` therefore carries a
  `LevelWF` premise instead of a typing, and **the reason is written at
  `VIndRestore.csubst_hbridgeD_iff` itself**, so a successor does not "improve" the premise into the
  hole.
* **`VEnv.AxiomConservativityWF`** and the restriction cycle — absent; nothing here enters
  `RestrictStep`.

No weaker statement had to be substituted for a stronger one anywhere else: §A, §C and §E are genuine
`↔`s, and §B/§D are implications only because their premises are the residual β-arithmetic, not because
a hole blocked the converse.

## 6. What is NOT claimed

1. **`CtorBeta`'s `hfld` is not discharged.**  §B/§C consume it.  It is one typed defeq per recursive
   field naming a companion, and `CtorBeta` §6/§6b already priced it as bottoming out in
   `HargsShared`'s `hargs`.
2. **§D's `hM`/`hQ`/`hbody` are not discharged.**  They are `recConstsR_wf_of_blocks`' own hypotheses;
   `NestedTele.lean` §T15.4/§T16 price them.
3. **§E's result-head datum is not discharged in general**, and §E says at the statement why it cannot
   be made free the way §B's is.  Its σ-identity `hnoc` is discharged at `ntreeAux` by `decide` (§3a) but
   is not proved in general — `substC_tyAppR_free`-style `NoCSubst` facts on `C.params`, `C.fieldTypesR`
   and `C.args` would be needed, and those are per-restoration data.
4. **`csubst_WFD` is not re-instantiated at `ntreeAux`.**  `ValRestGeneral.lean` §7 note 2 already
   explains why that belongs to other files; what §F instantiates is every premise *this* file
   introduced.
5. **The `ValAt` monotonicity step** (`FlipGeneral.lean` §2a caveat (i)) is untouched, and no claim is
   made about `HargsShared`'s two data.
6. No frozen file was read for editing, let alone edited.  No `sorry`.  No `VEnv.HasArgs.of_mkApp`, no
   `PiInv` (grep-checked in the owner file).  No state-changing git command was run;
   `docs/vacuity-ledger.md` was not touched.
