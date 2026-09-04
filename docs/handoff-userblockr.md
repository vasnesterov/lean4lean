# handoff-userblockr — the user's original block at the real restoration `ntreeRestore`

Owner: the `UserBlockR` stream. Files owned: `Lean4Lean/Verify/Inductive/UserBlockR.lean`
(new) and this document. Everything else read-only.

Target, from `docs/handoff-b6.md` "What remains of Claim B", item 1: the per-constructor
equation `C.typeR D ntreeRestore j = ctorTr?`-output **on the user's constructor type**, and
its chaining with B6 part 3 (`Lean4Lean.ctorStoresTr_of_ctorTr_setRecArgs`) so that
`CtorStoresTr` holds at the *user's* original declaration rather than the post-elimination one.

---

## §1 PRIORS — written before any Lean was run. Never edited afterwards.

Corrections, if any, go in §2 MEASUREMENTS and later, never here.

### 1.1 What I take from the brief, and what I will re-check rather than trust

The brief hands me five claims. I verified nothing before writing this section except by
reading source with `grep`/`sed` (no elaboration, no `scripts/exists.lean`).

| # | Claim in the brief | Trust? | How I will check |
|---|---|---|---|
| C1 | `InductiveDeclExamples.ntreeNode_typeR` proves `ntreeNode.typeR ntreeAux ntreeRestore 0 = (vconst(type_of% @NTree.node)).type` by `rfl` (`NestedHead.lean:710`) | read it, believe it | re-elaborate it as a *cited* step in my own file; `scripts/exists.lean` on the name |
| C2 | `ntreeNode_declared_typeR` survives `ctorConstsCR`'s `substC`, by `rfl` | believe | cite, do not re-prove |
| C3 | `ctorStoresTr_of_ctorTr_setRecArgs` is stated at arbitrary `R` (arity 9) | **verified by reading B6.lean:709-717** — `{R : VIndRestore}` is free | re-measure arity with `exists.lean` |
| C4 | `noLam_of_ctorTr` has no context hypothesis | **verified by reading B6.lean ~205-243** | re-measure |
| C5 | "a `.lam`-free output cannot be a β-redex, so `ctorTr?` produces the contracted form and the equation closes" — the brief's own **hypothesis**, flagged as a guess | **do not trust** | see P3 |

### 1.2 Predictions, with probabilities

**P1 (0.85) — the equation closes at `ntreeNode`, and by `rfl`.**
Concretely: `ctorTr? Γc [`u] (exprOf% NTree.node) [] = some (ntreeNode.typeR ntreeAux
ntreeRestore 0, τ)` for a suitable constant table `Γc`. My reason is *not* the brief's: it is
that `ctorTr?` (`TrExprSGeneral.lean:126`) and `Meta.ofExpr` (`Theory/Meta.lean:36`, which is
what `vconst(…)` runs) are **the same structural recursion** on the fragment
`sort/bvar/const/app/forallE/mdata`, and `NTree.node`'s stored type lies entirely in that
fragment. `ctorTr?` adds side conditions (`Γc` lookup with a uvars-length check, `piOf?`, the
`AB.1 = q.2` domain check, `sortOf?`) but no rewriting: it never β-reduces and never
contracts. So if the side conditions pass, the outputs coincide on the nose.

**P2 (0.9) — B6's `ntreeΓc` is NOT enough; I will need a wider table.**
`ntreeΓc` (B6.lean:838) holds exactly `NTree` and `_nested.List_1`. The *user's* constructor
type mentions `List`, which the post-elimination one does not. So a new table
(`NTree`, `List`, and probably `_nested.List_1` kept for continuity) is required, plus its own
`ConstLookup`/environment. Corollary prediction (0.8): `List`'s entry must be
`{uvars := 1, type := ∀ (α : Type u), Type u}` — the same shape as `NTree`'s — for the
`AB.1 = q.2` check at `List (NTree α)` to pass.

**P3 (0.35 that the brief's stated mechanism is the operative one; 0.85 that its
*conclusion* is right).**
I think the brief's `noLam` hypothesis is **half the argument and is being asked to carry the
whole of it**. `noLam_of_ctorTr` shows `ctorTr?` can never *emit* the β-redex
`(fun α => List (NTree α)) α`, because that term contains a `.lam`. Good — that is a genuine
**exclusion**. But exclusion is not identification: "not the redex" does not entail "the
contracted `List (NTree α)`". What identifies the contracted form is a fact about the
**input**, not the output: Lean's own stored `Expr` for `NTree.node` already *is* the
contracted form, and `ctorTr?` is structural. So I predict the equation closes and that
`noLam` is **not needed at all** in the proof of the concrete equation (0.7). If I finish
without citing `noLam_of_ctorTr` anywhere in the equation's proof, that is the measurement
that settles this, and I will say so plainly.

**P4 (0.8) — the literal chaining with part 3 needs `ntreeAux` exhibited in `setRecArgsD`
form.** `ctorStoresTr_of_ctorTr_setRecArgs` concludes `CtorStoresTr … (H.setRecArgsD D) R`,
and `ntreeAux` is a hand-written structure literal, not syntactically of that form. B6's
`surfInductDeclR? = (surfInductDecl? …).map (surfHeader …).setRecArgsD` plus
`ntreeRTypes_mapsR : … = some ntreeAux` should give
`(surfHeader …).setRecArgsD (eraseRecArgs ntreeAux) = ntreeAux` by `rfl` or by a two-line
`Option` argument. I predict `rfl` works (0.7). If it does not I will use
`ctorStoresTr_of_ctorTr` directly and say that part 3's `setRecArgs` wrapper was cosmetic.

**P5 (0.45) — the honest generalisation is a *left-inverse* lemma, and I get it done.**
A `rfl` at one constructor is not a theorem. My candidate for the general statement:
`ctorTr?` **left-inverts reification on its first component**. Define
`VExpr.toExpr : VExpr → List Name → Expr` (the evident structural map back, with
`VLevel.toLevel`), and prove: *if* `ctorTr? Γc Us (v.toExpr Us) Γ = some (e', τ)` *then*
`e' = v` — no typing side conditions, because success already carries them. That reduces the
per-constructor equation to "the user's stored `Expr` is the reification of `C.typeR D R j`",
which is a statement about `restoreNested`'s faithfulness and is the right frontier. I give
0.45 that I land this in the round (the `.bvar` clause and the level round-trip
`VLevel.ofLevel Us ∘ toLevel = some` are the two places I expect friction), and 0.25 that I
land only a weaker version (levels restricted to `.param`/`.succ`).
Prediction inside the prediction (0.6): **no reification `VExpr → Expr` exists in the tree** —
`grep` for `VExpr → Expr` found none — so I must build it; I will run `exists.lean`,
`shape.lean` and `can-cite.py` before asserting that.

**P6 (0.8) — the control I intend, and it is a `typeR`-vs-restoration control.**
The sharp one available here is *swapping the restoration*: `ntreeRTypes`'s own node
constructor type (headed `_nested.List_1 α`) is what `ctorTr?` maps to
`ntreeNode.typeR ntreeAux ntreeAux.idRestore 0`; at `ntreeRestore` the same field must
instead be Lean's `List (NTree α)`. So I predict
`ctorTr? Γc [`u] (post-elimination node type) [] ≠ some (ntreeNode.typeR ntreeAux ntreeRestore
0, _)` — the equation reads the restoration and not just the block. Second control (0.7): a
surface constructor type written with the **β-redex** `(fun α => List (NTree α)) α` — the very
term `ntreeNode_substC_ne_typeR` says `substC` would produce — on which `ctorTr?` returns
`none` outright (no `.lam` clause). That is the one place `noLam`'s content is genuinely
visible, and it is a control, not the main proof.

**P7 (0.75) — anti-vacuity, checked and not inherited.** M13 of `handoff-b6.md` is the lesson:
an arity-0 witness whose conjuncts are implications proves nothing until the antecedent is
exhibited. So every oracle/lookup premise I state I will also *discharge* at a concrete
environment, and I predict that at my wider table `ConstLookup` is `fun _ _ h => h` again.

**P8 (0.9) — axioms clean.** Every declaration `propext`/`Quot.sound`/`Classical.choice` or
fewer; no `sorryAx`; zero errors and zero warnings from my file.

**P9 (0.55) — a named consumer exists.** Candidates to check with `scripts/can-cite.py`:
`Verify/Inductive/TrIndDeclNProducer.lean` (B6's named consumer),
`Verify/Inductive/NestedRestoreWit.lean`, `Verify/Environment/InductR.lean`. I predict at
least one of them can cite my headline; if none can without a cycle, I will say so rather than
invent one.

**P10 (0.7) — structural exclusion.** I plan **one import**, `Lean4Lean.Verify.Inductive.B6`,
giving closure 171. I predict the 15 modules B6 excluded stay excluded, and in particular that
`Verify.Inductive.TrIndDeclNProducer`, `FlipConstruct` (`tr_ntreeNodeType` — a *hand-built*
`TrExprS` of exactly the user's node type!) and `NestedRestoreWit` are **out**. `FlipConstruct`
is the dangerous one for this round specifically: `tr_ntreeNodeType` is a hand-built witness of
the very translation I am deriving, so if it were in my closure the result would be borrowable
rather than proved. I predict it is not (0.85) and will measure.

**P11 (0.3) — the round fails in the way the brief fears.** Named so it can be scored: the
failure mode is that `exprOf% NTree.node` carries a level parameter name other than `` `u ``,
or `mdata`, or a `Nat`-literal, so that the two structural maps diverge and the `rfl` does not
close. I think this is unlikely because `Meta.expandExpr` strips `mdata` on the `vconst` side
and `ctorTr?` has an explicit `mdata` clause on the other, but it is the concrete thing that
would sink P1.

### 1.3 What I will NOT do

- Not edit anything outside my two files. If the work implies an edit elsewhere it goes in
  §"Verbatim edits for other owners" below, and I stop.
- Not attempt `VInductDecl'.WF` (B6 item 3). A scoping paragraph only, if there is room.
- Not narrow any statement to make a proof go through.

