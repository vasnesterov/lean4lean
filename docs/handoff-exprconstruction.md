# handoff-exprconstruction

Round scope: **characterise the one missing construction** behind `Lean4Lean.TrIndDeclN.trCtors`
(+ `trCtorsLen`). Measure-first round; Lean only where a claim needs it.

## 0. Priors (written BEFORE the first measurement)

Recorded up front so they can be scored against what I actually find. These are guesses.

P1. **The convergence claim (`trCtors` + `trCtorsLen` = one construction) is probably right but for
    a boring reason**: `trCtorsLen` is almost certainly a `List.length` equation that falls out of
    whatever recursion produces `trCtors` (a `List.Forall₂`-shaped or per-index field). I expect to
    confirm it as "same recursion, free rider", not as "two tasks". Confidence 0.75.
    Risk flagged in the brief: the orchestrator has had this kind of attribution backwards before.

P2. **There is no general `Expr → VExpr` total translation function anywhere.** `TrExprS` is a
    *relation* (inductive predicate), not a function, and the whole architecture (de Bruijn +
    universe params + `VLocalDecl` contexts) makes a total function awkward. What likely *does*
    exist is (i) the checker's inference producing a `TrExprS` witness under a WF hypothesis, and
    (ii) inversion lemmas. Confidence 0.8 that no total function exists; confidence 0.5 that
    something "constructive enough" exists in the checker path.

P3. **The fragment trick (as in `trType_of_sortPiTr`) cannot straightforwardly transfer.** The brief
    already says a constructor type mentions the block's own members and the companion, so it is
    not constant-free; `trType_of_sortPiTr` presumably works precisely because sorts and pis have no
    `Expr.const` leaves needing environment lookup. My prior: the trick fails *as stated*, but a
    **relativised** version — "constant-free except for constants drawn from a supplied finite list
    whose translations are given as hypotheses" — should work, because each block member is a
    `.const` at a *known* index with a *known* abstract counterpart (that is exactly what the
    recursor/motive machinery already has to supply). Confidence 0.65 that a relativised fragment
    lemma is the right shape and is clean of watched statements.

P4. **The poisoned route probably *is* poisoned here too**, because the checker route is poisoned
    generically (`checkType.WF` carries them regardless of which expression you feed it) — the
    watched statements attach to the *route*, not to the input. So (c) likely answers "yes, same
    problem" and the interesting content is whether P3's relativised fragment dodges it.
    Confidence 0.7.

P5. **Price.** If P3 holds, the smallest useful version is: fix the non-indexed, non-nested
    fragment where `trType` already succeeded, and build `TrIndCtorR` for constructor types that are
    telescopes of `∀` over (sorts | block-member constants applied to params). I guess cone in the
    3k-6k range (comparable to `trType_of_sortPiTr` at 3692, plus the constant case) and 0 new holes
    if it can be phrased over existing `TrExprS` constructors. Confidence 0.4 — this is the guess I
    trust least.

P6. **Something already exists that I will be told about too late.** Five assignments this session
    were already done. My prior is 0.35 that at least a *partial* constructor-type translation lemma
    already sits in `Verify/Environment/` under a name that does not contain "Ctor".

## 1. Measurements (appended one line per instrument call, before the next call)

**M1** `sed -n 200,380p Lean4Lean/Verify/Environment/InductR.lean` — read `TrIndDeclN` in full.
12 fields: `safe, uvars, np, length, companions, trType, trCtorsLen, trCtors, trSpine,
ctorName_own, recName_own, recName_aux`. `TrIndCtorR env Us D R j c C :=
c.name = R.ctorName C.name ∧ TrExprS env Us [] c.type (C.typeR D R j)`. So `trCtors` is a
*conjunction*: a NAME equation plus the `TrExprS`. Note `ctorName_own` (a separate field) already
carries `c.name = C.name` **unstaged**; `trCtors`'s name half compares against `R.ctorName C.name`.
`trCtors` and `trSpine` are the only two fields staged over `env.addIndTypesC D K = some env₁`.
`trCtorsLen` is a plain `t.ctors.length = T.ctors.length` — NOT a `Forall₂`, so it is a genuinely
separate statement from `trCtors` in the current phrasing (P1 wobbles: see M-later).
**M2** grep for the brief's named witnesses. The brief said "two concrete `TrExprS` instances for
constructor types (`tr_ntreeNodeType` and an `nfn` sibling)". **The `nfn` sibling does not exist.**
`Lean4Lean/Verify/Inductive/FlipConstruct.lean` has *four* `TrExprS` witnesses, all `ntree`:
`tr_ntreeType:121`, `tr_ntreeNodeType:128`, `tr_ntreeRecType0:135`, `tr_ntreeRecType1:143`. Every
`nfn*` hit in the tree is about restorations/barriers (`NestedRestore.lean`,
`FlipPriceCompose.lean`), none is a `TrExprS`. So the concrete-instance population for constructor
types is **one** (`tr_ntreeNodeType`), not two — but there are two more `TrExprS` witnesses for
*recursor* types, which are richer than a constructor type and are therefore better evidence about
what the general construction must handle. (Orchestrator attribution wrong again, as calibrated.)
**M3** `FlipConstruct.lean:1-200`. All four bridges are discharged by a single tactic `trS_tac`
("`TrExprS` by structure, with `type_tac` on the side conditions"). The block-specific input is
*only* the hypothesis list: `tr_ntreeType` needs none; `tr_ntreeNodeType` needs
`hList : env.constants ``List = some ⟨1, listType.type⟩` and
`hNTree : env.constants ``NTree = some ⟨1, …⟩`; the two recursor bridges additionally need
`hNil, hCons, hNode`. So the *hand* content is: (i) the exact `VConstant` for each `Expr.const`
leaf appearing in the type, and (ii) the `exprOf%`/`vconst(type_of% …)` alignment. Everything else
is automation. This is strong evidence for the shape of the general construction: it is a
**leaf-lookup discharge**, not a term-by-term hand translation.
**M4** `InductR.lean:779-789` (`trS_tac`) + `Theory/Typing/Meta.lean:20-46` (`type_tac`,
`lookup_tac`). `trS_tac` is a **five-case syntax-directed macro**: `TrExprS.sort`, `.bvar`,
`.const (by assumption) rfl rfl`, `.forallE`, `.app`. It has **no** `lam`, `letE`, `proj`, `lit`,
`mdata` case. Its `const` case discharges the environment lookup by `by assumption` — i.e. the
caller must have the exact `env.constants c = some ci` in context — and both level side-conditions
by `rfl`. `type_tac` is likewise a `first`-combinator macro over sort/bvar/app/const/forallE/lam
with `decide` on level WF.
**This is the crux.** `trS_tac` recurses on a *concrete closed `Expr` literal* spliced by
`exprOf%`. It is reflection, not a theorem: it cannot be applied to a symbolic `c.type` coming
from an arbitrary `Constructor` in an arbitrary `List InductiveType`. So the "missing
construction" is precisely **`trS_tac` re-expressed as an induction over a syntactic class of
`Expr`, with the constant-lookup side conditions collected into a hypothesis about the
environment**. That is a sharp characterisation and it did not require guessing.
**M5** `Verify/Typing/Expr.lean:153-186`, the `TrExprS` inductive. Eleven constructors. Critically
`.app` carries **two `env.HasType` premises** and `.forallE`/`.lam` carry **`env.IsType`** premises:
`TrExprS` is *not* a purely syntactic relation — it bundles a typing derivation. So a general
`Expr → VExpr` construction must produce well-typedness at every node, which is exactly why
`type_tac` sits inside `trS_tac`. Any "general theorem" replacing `trS_tac` must therefore have a
typing hypothesis of comparable strength, or produce typing as part of its induction.
**M6** `exists.lean` on 8 names (population 442 modules, 6 watched):
```
Lean4Lean.TrIndDeclN                      arity 9,  cone 9 [no proof term]   sorryAx:false  watched:none
Lean4Lean.TrIndCtorR                      arity 7,  cone 730                 sorryAx:false  watched:none
Lean4Lean.InductiveDeclExamples.tr_ntreeNodeType  arity 3, cone 1064         sorryAx:false  watched:none
Lean4Lean.InductiveDeclExamples.tr_ntreeType      arity 1, cone 737          sorryAx:false  watched:none
Lean4Lean.InductiveDeclExamples.ntreeAux_trIndDeclN arity 0, cone 5958       sorryAx:false  watched:none
Lean4Lean.trType_of_sortPiTr              arity 10, cone 3692                sorryAx:false  watched:none
Lean4Lean.TypeChecker.checkType.WF        arity 4,  cone 18795               sorryAx:TRUE   *** WATCHED: IsDefEq.uniq, IsDefEq.uniqU ***
Lean4Lean.TrExprS.weakFV_inv              arity 16, cone 8653                sorryAx:TRUE   *** WATCHED: IsDefEq.uniq, IsDefEq.uniqU ***
```
`checkType.WF` holes (8): TrProj.weak'_inv, Inner.isDefEqUnitLike.WF, Inner.tryEtaStructCore.WF,
IsDefEqU.weakN_iff, IsDefEqU.forallE_inv_stratified, WF.rigidShapeUniqNS, NormalEq.descend,
Inner.inferProj.WF. `weakFV_inv` holes (5): the same minus the three checker-side ones.
**All the orchestrator's cone figures reproduced exactly.** Calibration holds.
**M7** `shape.lean Lean4Lean.TrIndCtorR` → only **7** constants mention it, and 4 are the
auto-generated `TrIndDeclN.{rec,recOn,casesOn,mk}` + the field `TrIndDeclN.trCtors`. The only two
substantive ones are `Lean4Lean.trIndDeclN_of_ownId` (arity 21) and
`Lean4Lean.trIndDeclN_of_restoreData` (arity 21), both in
`Verify/Inductive/TrIndDeclNProducer.lean`. So **nothing in the tree concludes a `TrIndCtorR`
except by taking one as a hypothesis.** The absence claim survives its first instrument.
**M8** `Verify/Inductive/TrIndDeclNProducer.lean` read in full. Its own docstring states the
checklist: of 12 fields, `trIndDeclN_of_ownId` proves `ctorName_own` and `recName_own` in its
body, takes block data + `hspine` + `hst`, and carries **exactly three** as named hypotheses:
`hty` (trType), `hclen` (trCtorsLen), `hctors` (trCtors). So the brief's "one missing
construction + bookkeeping" is really **two remaining** at this producer (`trType` having since
been discharged in general by `trType_of_sortPiTr`) — `trCtorsLen` and `trCtors`.
`ntreeAux_trIndDeclN` (§3) discharges the three at `ntreeAux` by hand: `trType` = `tr_ntreeType`,
`trCtorsLen` = `rfl` after `rintro (_|j)`, `trCtors` = `tr_ntreeNodeType` at the staged env.
**`trCtorsLen` at `ntreeAux` is literally `rfl`.** That is the first hard evidence on P1.
**M9** `Verify/Inductive/TrTypeProducer.lean:1-140`, the achieved `trType` route, is the exact
template. Its mechanism: `sortPiTr? : List Name → Expr → Option VExpr` (a *partial function* on
the sort/forallE/mdata fragment) plus two inductions —
`sortPiTr?_isType` (every fragment translation is an `IsType` at **every** `env` and **every** `Γ`)
and `trExprS_of_sortPiTr` (fragment translation ⟹ `TrExprS` at every `env`, every `Δ`).
The docstring states the reason env-uniformity works, and it is exactly the reason it will NOT
transfer: "`TrExprS.const` is the only constructor that reads `env.constants`… A sort-and-pi arity
therefore translates **at every `VEnv` whatsoever**." §6 machine-checks the boundary
(`sortPiTr?_none_of_const`, `no_trIndType_of_undeclared`). The file also confirms the poisoned
route independently and confines it: §4's `exists_indTypes_of_trExprS` takes the translation
existential as a hypothesis so contamination stays with whoever supplies it.
**M10** grep for `Option VExpr` / `Expr → VExpr` across `Lean4Lean/`. **`sortPiTr?` is the only
`Expr → Option VExpr` function in the tree.** Two independent files say so in prose:
`Verify/Inductive/NestedRestore.lean:854` and `Verify/Inductive/NestedRestoreWit.lean:115` — "there
is no `Lean.Expr → VExpr` function (`TrExprS` is a relation)" — and
`Verify/Inductive/SpineTransfer.lean:447` repeats it. P2 confirmed.
**M11** `shape.lean Lean4Lean.TrExprS Lean.Expr.app` → 106 constants, 0 fields. Cheapest, arity 3:
`Lean4Lean.InductiveDeclExamples.tr_ntreeNodeType` and **`Lean4Lean.NestedWit.tr_nodeType`** —
the latter is the `nfn` sibling the brief promised, and it lives in
`Verify/Environment/InductR.lean` (namespace `NestedWit`), **not** in `FlipConstruct.lean`.
**M2 partially corrected**: the sibling exists, in a different module, and my grep missed it
because its name is `tr_nodeType`, not `tr_nfn…`. Also visible: `NestedWit.tr_recType0/1`
(arity 5). And a genuinely general family: `Lean4Lean.TrExprS.listChar`, `.listCharCons`,
`.listCharNil`, `.listCharLit` in `Verify/Typing/Lemmas.lean` — `TrExprS` produced **by induction
over a datatype** rather than by reflection. That is a precedent worth reading.
**M12** `Theory/VEnv.lean:15-17`: `VEnv.constants : Name → Option VConstant` — a **plain
function field**. So a translation function *may* read the environment directly:
`ctorTr? (env : VEnv) …` is definable with no decidability or Finmap machinery. And
`Verify/VLCtx.lean:64-69`: `VLCtx.find? : VLCtx → Nat ⊕ FVarId → Option (VExpr × VExpr)` already
returns **(value, type)** — so a bvar's type is available to an inference function for free.
Both of the two things a `sortPiTr?`-for-constructor-types would need are already there.
**M13** `shape.lean Lean4Lean.VLCtx.find? Lean4Lean.VEnv.HasType` → 6 constants, 5 of them
`TrExprS.rec/casesOn/recOn/below.*`. The one real hit: **`Lean4Lean.VLCtx.WF.find?_wf`**
(arity 9, `Verify/Typing/Lemmas.lean`) — the bvar-typing bridge an inference function needs
already exists, gated on `VLCtx.WF`. Not a new obligation.
**M14** `Verify/Typing/Expr.lean:59-63`: `VLCtx.WF env U ((ofv,d) :: Δ) = VLCtx.WF Δ ∧ (fvar
freshness) ∧ VLocalDecl.WF env U Δ.toCtx d`, and `VLocalDecl.WF … (.vlam A) = env.IsType U Γ A`.
So pushing `(none, .vlam d')` onto a WF context costs exactly the `IsType d'` an inference
function already produces — `VLCtx.WF` is maintainable by the induction with no extra premise.
`VLevel.WF` is **decidable** (`Theory/VLevel.lean:27 decidable_WF`). `VExpr` has **no**
`deriving DecidableEq` (`Theory/VExpr.lean:7-14`) — one would have to be derived in the new file.
**M15** `Theory/Inductive/Decl.lean:248`: `deriving instance DecidableEq for VExpr` — **already
present**. So the app case's domain/argument-type comparison is available. M14's last sentence
is superseded: nothing new is needed.
**M16** Location of the `ntree` environment facts: `ntree_const₃`, `list_const₃`,
`ntree_stage₂_exists` are all in **`Theory/Typing/ConstSubstNested.lean`** (:864, :871, :1848), and
`ntreeRestore_ownId` in `Theory/Inductive/NestedHead.lean:675`, `ntreeAux_companions` in
`Verify/Inductive/ValAtParam.lean:196`. **None of them is in `FlipConstruct.lean`.** So a new
module can reach the staged environment facts without importing `FlipConstruct`, i.e. without
`tr_ntreeNodeType` ever being in scope — the non-borrowing standard the brief sets is achievable.
**M17** `Verify/VLCtx.lean:90-93` (`toCtx`) and `Theory/Typing/Lemmas.lean:560` (`HasType.weakN`,
inside a `variable! (henv : Ordered env)` block). Weakening needs `Ordered env`; `VLCtx.WF.find?_wf`
needs it too. `ntree_stage₂_exists` (`ConstSubstNested.lean:1848`) does **not** hand out an
`Ordered env₁`. **Design consequence**: state the soundness induction over an *all-`vlam`* context
built from a `List VExpr`, where `find?` computes to `(.bvar i, …)` and `Lookup` follows by a
one-page induction — no weakening, no `Ordered`, no `VLCtx.WF`. That is exactly the context shape
a constructor type's telescope produces from the empty base context.
**M18** All prerequisite signatures confirmed in `Theory/Typing/Lemmas.lean:221-234`:
`HasType.bvar (Lookup Γ i A)`, `.sort (l.WF U)`, `.const (h1 h2 h3) : HasType … (ci.type.instL ls)`,
`.app (h1 : … f (.forallE A B)) (h2 : … a A) : … (B.inst a)`,
`.forallE (h1 : A : sort u) (h2 : body : sort v) : … (.sort (.imax u v))`; plus
`VLevel.WF.of_mapM_ofLevel` (`Theory/VLevel.lean:185`). **Nothing needed for the app/const cases
is missing.** Decision: author §1–§3 (function + soundness + field producer) and attempt §4
(arity-0 `ntreeAux` witness) in `Lean4Lean/Verify/Inductive/ExprConstructionScope.lean`.
