# Handoff: the `ValAt` stage-monotonicity step, and the general `hbridge`

**Owner files:** `Lean4Lean/Verify/Inductive/StageMono.lean` (new, mine) and this file.
**Written incrementally from the first minute** — eleven predecessor streams lost their handoff by
writing it at the end.

## 0. Pre-flight: what the brief named, re-verified before writing (`scripts/exists.lean`, population 425)

| name | arity | cone | own hole | reaches `sorryAx` |
|---|---|---|---|---|
| `VIndRestore.ValAt` | 5 | 397 | false | **false** |
| `VIndRestore.csubstTy_le_csubst` | 7 | 1080 | false | **false** |
| `VIndRestore.csubst_ctor_off_csubstTy` | 11 | 1223 | false | **false** |
| `VIndRestore.csubst_rec_off_csubstTy` | 9 | 1223 | false | **false** |
| `VIndRestore.ValRestC` | 5 | 808 | false | **false** |
| `VIndRestore.csubst_WFD` | 32 | 2978 | false | **false** |
| `CSubst.val_of_hasType` | 14 | 2331 | false | **false** |
| `InductiveDeclExamples.ntreeAux_valRestC_both_stages` | 0 | 3811 | false | **false** |
| `InductiveDeclExamples.ntree_hbridgeD` | 15 | 2056 | false | **false** |
| `InductiveDeclExamples.ntree_ctorTypeBridge` | 3 | 1064 | false | **false** |
| `InductiveDeclExamples.ntree_recTypeBridge` | 6 | 1882 | false | **false** |
| `VNestedOcc.OccursN.mono` | 5 | 942 | false | **false** |
| `VEnv.ConstsClosedC.addConst_sort` | 7 | 403 | false | **false** |
| `VInductDecl'.KFresh.addConst_sort` | 11 | 765 | false | **false** |

### 0a. Absence checks, by conclusion shape (`scripts/shape.lean`), run BEFORE writing

* `HEADS="Lean4Lean.VIndRestore.ValAt"` — 22 hits, 0 structure fields. **No environment-monotonicity
  lemma for `ValAt` exists** in any direction: every hit is either the cycle (`RestrictStep`), a
  producer (`valAt_of_*`), a consumer (`ArgsTypedK.restrict_of_val`, `csubst_val_of_valAt_of_valRestC`),
  or a witness. So target (1) is genuinely absent. Recorded because the brief warned it might not be.
* `HEADS="Lean4Lean.VIndCtor.typeR Lean4Lean.VIndCtor.type Lean4Lean.VEnv.IsDefEq"` — 14 hits, and
  **every one that concludes a whole-type bridge is block-specific** (`InductiveDeclExamples.*`);
  the only general ones are `csubst_WFD` / `csubst_WFD_const`, which *consume* the bridge as
  `hbridgeD`. So the general whole-type bridge is absent too.

### 0b. **PARTIAL FALSE ABSENCE — the brief's target (2) is already half-done upstream.**

This is the twelfth instance in the project and it is worth stating precisely, because it changes
what target (2) is.

`Theory/Inductive/CtorBeta.lean` **already** reduces obligation (A)'s `hbridge` in general, with no
bound on `D.np`:

* `VIndRestore.substC_fieldTypes_defeq'` / `substC_fieldTypes_defeq` / `substC_fieldTypes_defeq_of_noK`
  (CtorBeta §1) — the field telescope's `TeleDefEq`, reduced to the entries that name a **companion**
  constant; non-recursive and companion-free entries cost `VEnv.TeleDefEq.rfl`, i.e. nothing.
* `VEnv.ctorConstsCR_wf_of_fieldsD` (§3) and `VEnv.ctorConstsCR_wf_of_betaD` (§7) — (A)'s route with
  `hbridge` replaced by per-recursive-field β data, and the **result** conjunct discharged outright
  (§2: `OwnId.tyAppR_eq` + `IsType.mkPi_inv`, because at a *declared* member the restored head **is**
  the own head).

So "the same β-redex arithmetic, untouched" is not true of (A) any more. What **is** untouched, and
is what this round targets, is the *undecomposed whole-type* form that `csubst_WFD` (§6's `hbridgeD`),
`CtorTypeBridge` (§4) and `RecTypeBridge` (§5) consume — where the two sides are `mkPi`s under a
`substC` **and** a level instantiation, at a **free** `U`, `Γ` and `ls`.

## 1. In progress
