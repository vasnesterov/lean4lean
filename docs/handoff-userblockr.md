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

---

## §2 MEASUREMENTS

Appended in the order made, each one before the next tool call. Round 2 (round 1 crashed to an
API error having written no `.lean` file and no measurements; its claim of "hypothesis confirmed"
had no evidence behind it and is **not** inherited).

### M1 — `exprOf% NTree.node` read out of the compiled environment

```
Expr.forallE `α (Expr.sort (Level.param `u).succ)
  (Expr.forallE `a (Expr.bvar 0)
    (Expr.forallE `a
      ((Expr.const `List [Level.param `u]).app
        ((Expr.const `Lean4Lean.InductiveDeclExamples.NTree [Level.param `u]).app (Expr.bvar 1)))
      ((Expr.const `Lean4Lean.InductiveDeclExamples.NTree [Level.param `u]).app (Expr.bvar 2))
      BinderInfo.default)
    BinderInfo.default)
  BinderInfo.implicit
```

Three facts, none of them assumed: (a) the stored type is **already contracted** — `List (NTree α)`,
no `.lam` anywhere, no β-redex; (b) the level parameter really is `` `u ``; (c) the outer binder is
`BinderInfo.implicit`, which `ctorTr?`'s `.forallE _ d b _` clause discards, and there is no `mdata`
and no `Nat` literal. So **P11's three named sinkers are all absent** — measured, not argued.

### M2 — the equation, at the user's constructor type, by `rfl`

At the table `ntreeΓcU` = {`NTree`, `List`, `_nested.List_1`} ↦ `⟨1, ∀ (α : Type u), Type u⟩`:

```lean
∃ t', ctorTr? ntreeΓcU [`u] (exprOf% NTree.node) []
    = some (ntreeNode.typeR ntreeAux ntreeRestore 0, t')   -- ⟨_, rfl⟩
∃ t', ctorTr? ntreeΓcU [`u] (exprOf% NTree.node) []
    = some ((vconst(type_of% @NTree.node)).type, t')        -- ⟨_, rfl⟩
```

Both elaborate. **P1 (0.85) — HIT**, and by `rfl`, and for the reason P1 gave rather than the
brief's: `ctorTr?` and `Meta.ofExpr` are the same structural recursion on this fragment.
**P2 (0.9) — HIT**: `ntreeΓc` (B6:842) does not hold `List`, so a wider table was needed; its
corollary (0.8) that `List`'s entry must be `⟨1, ∀ (α : Type u), Type u⟩` — the same shape as
`NTree`'s — is also **HIT**, and it is *forced*, not chosen: the `.app` clause's `AB.1 = q.2` check
at `List (NTree α)` compares `List`'s instantiated domain against the inferred type of
`NTree α`, which is `.sort (.succ (.param 0))`.

### M3 — P4, and the chaining with B6 part 3

`(surfHeader 1 [.sort (.succ (.param 0))] ntreeRTypes).setRecArgsD (eraseRecArgs ntreeAux)
= ntreeAux` **by `rfl`** — `ntreeAux` *is* exhibited in `setRecArgsD` form, so part 3's wrapper is
not cosmetic and does not have to be routed around. **P4 (0.8, with 0.7 on `rfl` specifically) —
HIT on both halves.**

And then, first try:

```lean
theorem chain : CtorStoresTr ntreeEnvU [`u] [ntreeSurf] ntreeAux ntreeRestore
```

via `ctorStoresTr_of_ctorTr_setRecArgs constLookupU` after rewriting `ntreeAux` into
`setRecArgsD` form; the only per-constructor input is `⟨rfl, _, rfl⟩` — M2's equation. `ntreeSurf`
(`Verify/Inductive/CtorsLenGeneral.lean:389`, `type := exprOf% NTree`, one ctor
`type := exprOf% NTree.node`) is the **user's** declaration and is already inside B6's closure, so
no new surface artefact had to be written. `CtorStoresTr` quantifies over `j` with *both*
`rtypes[j]? = some t` and `D.types[j]? = some T`, so the one-member user list against the
two-member abstract block leaves `j = 1` with no obligation — that is why a `CtorStoresTr` at the
user's block is even statable.

**So the headline answer is yes on both counts**, and at the *real* restoration `ntreeRestore`, not
at `idRestore`.

### M4 — measured arities and cone sizes (`scripts/exists.lean`, population 465 built modules)

| name | module | arity | cone | own value a hole | cone reaches `sorryAx` |
|---|---|---|---|---|---|
| `Lean4Lean.ctorStoresTr_of_ctorTr_setRecArgs` | `Verify.Inductive.B6` | 9 | 1266 | false | **false** |
| `Lean4Lean.noLam_of_ctorTr` | `Verify.Inductive.B6` | 6 | 957 | false | false |
| `Lean4Lean.InductiveDeclExamples.ntreeNode_typeR` | `Theory.Inductive.NestedHead` | 0 | 737 | false | false |
| `Lean4Lean.InductiveDeclExamples.ntreeNode_declared_typeR` | `Theory.Inductive.NestedHead` | 0 | 907 | false | false |
| `Lean4Lean.InductiveDeclExamples.ntreeSurf` | `Verify.Inductive.CtorsLenGeneral` | 0 | 33 | false | false |
| `Lean4Lean.InductiveDeclExamples.ntreeΓc` | `Verify.Inductive.B6` | 1 | 341 | false | false |
| `Lean4Lean.ctorTr?` | `Verify.Inductive.TrExprSGeneral` | 4 | 912 | false | false |
| `Lean4Lean.CtorStoresTr` | `Verify.Inductive.SurfaceMap` | 5 | 853 | false | false |

**C1, C2, C3, C4 all confirmed** (C3's arity 9 and cone 1266 re-measured, not read off the brief).
No watched declaration in any cone. Note that a `sorryAx`-free cone is *not* the same verdict as
"open": every row above is a theorem with a proof term and no hole anywhere in its cone, so nothing
here is priced against a hole.

### M5 — the reification `VExpr → Expr`: P5's inner prediction, and a near-miss worth naming

Three instruments, per the brief:

* `scripts/exists.lean` on `Lean4Lean.VExpr.toExpr`, `Lean4Lean.VLevel.toLevel`,
  `Lean4Lean.VExpr.reify`, `Lean4Lean.VExpr.unTr`, `Lean4Lean.VLevel.toLevel?` — **all five NOT FOUND**.
* a structural scan of the same 465-module population for *any* constant whose result-type head is
  `Lean.Expr` with `VExpr` anywhere in its type, and likewise `Lean.Level`/`VLevel`: **exactly one
  hit**, `Lean4Lean.Meta.instToExprVExpr.toExpr` (`Theory/Meta.lean:55`, `deriving instance ToExpr
  for VExpr`), and **zero** for `VLevel → Level`.
* the one hit is **not** a reification. `ToExpr VExpr` is the *quoting* map: it sends a `VExpr`
  value to the `Expr` that is its own syntax tree (`VExpr.app ⟦f⟧ ⟦a⟧`), used by `vexpr(…)` to
  splice literals. Reification sends `VExpr.app f a` to `Expr.app`. Same source and target types,
  opposite jobs — which is exactly the "different name for the same content" failure inverted:
  here it is *the same shape for different content*. Recording it so the next round does not cite
  it by mistake.

**P5's inner prediction (0.6) — HIT**, with that caveat stated. I built the map.

### M6 — P5 proper: `ctorTr?` left-inverts reification. **Landed.**

```lean
def VLevel.toLevel (Us : List Name) : VLevel → Lean.Level
def VExpr.toExpr   (Us : List Name) : VExpr → Expr
def VExpr.lvlWF    (n : Nat) : VExpr → Prop      -- every level parameter index < n

theorem VLevel.ofLevel_toLevel (hUs : Us.Nodup) : u.WF Us.length → ofLevel Us (u.toLevel Us) = some u
theorem VExpr.ctorTr?_toExpr   (hUs : Us.Nodup) :
    ∀ {v}, v.lvlWF Us.length → ∀ {Γ p}, ctorTr? Γc Us (v.toExpr Us) Γ = some p → p.1 = v
```

**P5 (0.45) — HIT, in the full form, not the weakened one** (levels are *not* restricted to
`.param`/`.succ`: `zero`/`max`/`imax` are all in). The two frictions P5 named both appeared and
both were cheap: the `.bvar` clause is discharged by `bvarCtx_find?` (which already says the
translation *is* the de Bruijn index, with no context hypothesis), and the level round-trip needed
`List.Nodup.idxOf_getElem` plus two hypotheses — see M7, they are not slack.

No typing side conditions appear in the conclusion, as P5 predicted: success of `ctorTr?` already
carries them.

### M7 — **P3, settled, and against the brief's reading**

`noLam_of_ctorTr` is cited **nowhere** in this file — not in the concrete equation (M2), not in the
chaining (M3), and, the part I did not expect, **not in the general left-inverse either**. I tried
to use it in `ctorTr?_toExpr`'s `.lam` case and it cannot be used there, for a reason that is the
whole of P3 in one line: `noLam_of_ctorTr` constrains the **output** (`p.1.noLam`), and the `.lam`
case has to refute the **input** (`ctorTr?` has no `.lam` clause, so it returns `none` outright).
Knowing the output is `.lam`-free tells you nothing until you already know what the output is.

So: **P3 — HIT on both numbers.** Its 0.85 on the brief's *conclusion* holds (the equation closes);
its 0.35 on the brief's *mechanism* is where the brief was wrong, and 0.7 on "`noLam` not cited"
is confirmed. What identifies the contracted `List (NTree α)` is M1: Lean's stored `Expr` **already
is** contracted, and `ctorTr?` is a structural recursion with no β-reduction and no contraction
step. Exclusion is not identification, and the identification is a fact about the input.
`noLam_of_ctorTr` remains a real theorem doing real work in B6 §4 (the two-stage reader collapse);
it is simply not what closes this equation.

### M8 — the witness becomes an *instance* of the theorem, not a parallel `rfl`

`toExpr` writes every binder as `` `x `` with `BinderInfo.default`; Lean's stored type writes `` `α ``,
`` `a ``, and `BinderInfo.implicit` on the parameter (M1). So `exprOf% NTree.node` is **not**
syntactically `(ntreeNode.typeR ntreeAux ntreeRestore 0).toExpr [`u]`, and the general lemma would
not have reached the concrete case. The repair is one small function and one lemma:

```lean
def stripBinderData : Expr → Expr                     -- binder names → `x, infos → .default, mdata dropped
theorem ctorTr?_stripBinderData : ctorTr? Γc Us (stripBinderData e) Γ = ctorTr? Γc Us e Γ
```

and then, **by `rfl`**:

```lean
theorem user_is_reification :
    stripBinderData (exprOf% NTree.node) = (ntreeNode.typeR ntreeAux ntreeRestore 0).toExpr [`u]
```

That is the sentence the round was really after: *Lean's own stored type for `NTree.node` is the
reification of the abstract constructor type at the real restoration, up to binder annotations.*
The remaining content of the per-constructor equation is then general (M6), and `mdata` is handled
by the same lemma rather than by luck — which retires the `mdata` half of P11 structurally instead
of by inspection.

---

## §3 TRANSCRIPTION

Round 3. Rounds 1 and 2 crashed to API errors; round 2 finished the mathematics and recorded
it in §2 but lost the `.lean` file. This section is the log of writing that file back, appended
one verdict at a time before the next tool call, per the method rule that saved round 2's work.

T0 — starting. Plan: read the definitions §2 names (`ctorTr?`, `CtorStoresTr`,
`ctorStoresTr_of_ctorTr_setRecArgs`, `ntreeSurf`, `ntreeΓc`, `surfHeader`, `eraseRecArgs`,
`VLevel.ofLevel`) out of the tree, then write `Lean4Lean/Verify/Inductive/UserBlockR.lean` in
M1→M2→M3→M6→M8 order with the module docstring carrying M7's correction (P3 against the
brief's reading). No Lean call made yet.

### T1 — closure measured first (P10), before any Lean was elaborated

Sole planned import `Lean4Lean.Verify.Inductive.B6`, so my closure **is** B6's: **204 modules,
170 of them `Lean4Lean.*`** (`can-cite.py` header line; P10's guessed "171" was the
`Lean4Lean.*` count and is one off — cosmetic).

* `Lean4Lean.Verify.Inductive.FlipConstruct` — **OUT**, confirmed twice: absent from the
  transitive-import set, and `can-cite.py` says `Lean4Lean.InductiveDeclExamples.tr_ntreeNodeType`
  is **NO** for B6 ("would have to gain `Lean4Lean.Verify.Inductive.FlipConstruct`"). So the
  hand-built `TrExprS` of exactly the user's node type is **not borrowable here**. This is the
  exclusion P10 called the dangerous one, and it holds.
* `Lean4Lean.Verify.Inductive.TrIndDeclNProducer` — **OUT**.
* But **P10 is a MISS on two of the three it named**: `Lean4Lean.Verify.Inductive.ValAtParam`
  and `Lean4Lean.Verify.Inductive.NestedRestoreWit` are **IN**, via
  `B6 → ClaimB → FlipWiring → TrExprSGeneral → ExprConstructionScope → ValAtParam →
  SpineClause → ValAtPrice → RestrictCompanion → ArgsTypedSupply → NestedOccData →
  NestedRestoreWit`. `CtorsLenGeneral`'s docstring excludes `ValAtParam` from *its* closure, and
  P10 read that as holding for B6; it does not. Recorded as a miss rather than smoothed over.
  Nothing in either module is a `TrExprS`/`ctorTr?` fact about the user's node type at
  `ntreeRestore`, so the borrowability worry does not transfer — but the prediction was wrong.

### T2 — increment 1 landed: module docstring + §1.1 levels

`Lean4Lean/Verify/Inductive/UserBlockR.lean` created, sole import `Lean4Lean.Verify.Inductive.B6`,
**builds clean**. Contains the module docstring (carrying M7's correction: `noLam_of_ctorTr` is
cited nowhere and cannot be, because it constrains the *output* while the `.lam` case must refute
the *input*), `VLevel.toLevel`, `VLevel.ofLevel_toLevel` and `VLevel.mapM_ofLevel_toLevel`.

One deviation from §2's recorded text, and it is cosmetic, not mathematical: §2/M6 states
`ofLevel_toLevel` exactly as reproduced. The `.param` case needed `List.getElem_eq_getD`
(reversed) rather than `List.getD_eq_getElem` — the latter **does not exist** under that name in
this toolchain (v4.33.0-rc2). Statement unchanged; `hUs.idxOf_getElem` is
`List.Nodup.idxOf_getElem` as §2 records.

### T3 — increment 2 landed: §1.2, M6 in full

`VExpr.toExpr`, `VExpr.lvlWF`, `VExpr.ctorTr?_toExpr` — **exactly as §2/M6 records them**, builds
clean first try. Levels unrestricted (`zero`/`max`/`imax` all in), no typing side condition in the
conclusion, `hUs : Us.Nodup` and `v.lvlWF Us.length` the only hypotheses. `bvarCtx_find?` closes
`.bvar`; `VLevel.mapM_ofLevel_toLevel` (built in T2 off `List.Nodup.idxOf_getElem`) closes `.const`.

M7 confirmed *in the writing*: the `.lam` case is `rw [toExpr] at h; simp [ctorTr?] at h` — the
input is refuted because `ctorTr?` has no `.lam` clause. `noLam_of_ctorTr` is not cited and there is
no place for it to go.

### T4 — increment 3 landed: §2, M8's bridge

`stripBinderData` and `ctorTr?_stripBinderData` as §2/M8 records them, clean first try. The lemma is
an unconditional equation in `Γc`, `Us`, `Γ`; the `.forallE` case needs a two-level case split on
`ctorTr?` of the domain and on `sortOf?` of its type (the recursive call on the body sits under both
binds), which is bookkeeping, not content.

### T5 — increment 4 landed: §3, M2 and M8's `user_is_reification`

`ntreeΓcU` = {`NTree`, `List`, `_nested.List_1`} ↦ `⟨1, ∀ (α : Type u), Type u⟩`, `ntreeEnvU`,
`constLookupU` (**`fun _ _ h => h`, P7 again**), `constLookupU_staged`, the two M2 equations
(`ntreeNode_ctorTr?_typeR`, `ntreeNode_ctorTr?_declared`, both `⟨_, rfl⟩`) and
`user_is_reification` (**by `rfl`**) — all **exactly as §2 records**.

Two additions §2 did not name, both to make the concrete case an *instance* of M6 rather than a
parallel `rfl`:
* `VExpr.decidable_lvlWF` — a `Decidable` instance for `lvlWF`, so the side condition of
  `ctorTr?_toExpr` is `by decide` at a concrete block instead of a hand conjunction.
* `ntreeNode_ctorTr?_typeR_of_general` — the same statement as the M2 equation, but *derived* from
  `VExpr.ctorTr?_toExpr` + `user_is_reification` + `ctorTr?_stripBinderData`, with no `rfl` on
  `ctorTr?` at all. That is the honest form: the `rfl` version is a check, this one is the theorem.

One elaboration snag, fixed not restated: `VExpr.ctorTr?_toExpr` applied with all-implicit `Us`/`v`
gives "Expected type must not contain metavariables" at the two `by decide`s, since the implicits are
only fixed by the later argument. Supplying `(Γc := …) (Us := [`u]) (v := …) (Γ := []) (p := p)`
explicitly fixes it. Statement unchanged.

### T6 — increment 5 landed: §3.4, M3 in full

`ntreeAux_setRecArgsD` (**by `rfl`** — P4's `rfl` half reproduces) and
`chain : CtorStoresTr ntreeEnvU [`u] [ntreeSurf] ntreeAux ntreeRestore` via
`ctorStoresTr_of_ctorTr_setRecArgs constLookupU`, clean first try, exactly as §2/M3 records. The
per-constructor input is `⟨rfl, _, rfl⟩` at `j = 0, q = 0`; `j ≥ 1` and `q ≥ 1` are discharged from
`ntreeSurf`'s one-member/one-constructor shape, so the `j = 1` slot of the two-member abstract block
carries no obligation, as §2 explains.

### T7 — increment 6 landed: §4, the β-redex control

`ntreeNodeRedexE` (the user's constructor type with the recursive field's domain written as
`(fun β => List (NTree β)) α`) and `ntreeNodeRedex_ctorTr?_none : ctorTr? Γc Us ntreeNodeRedexE Γ =
none` — **for every `Γc`, every `Us`, every `Γ`**, by `simp [ntreeNodeRedexE, ntreeNodeRedexDom,
ctorTr?]`, because the `.app` clause's first bind hits a `.lam` and there is no `.lam` clause.
Paired with `ntreeNodeContr_ctorTr?_some`: the contracted form succeeds at `ntreeΓcU`, at the same
restored abstract type. Same type, one β-step apart, opposite answers. `noLam_of_ctorTr` still not
cited — this too is a fact about the input.

**One recorded intention that had to be restated, and it is worth naming.** I first wrote the β-step
as `ntreeNodeRedexDom.headBeta = ntreeNodeContrDom := rfl`. It **fails**: `Lean.Expr.headBeta` bottoms
out in `@[extern]`/`opaque` instantiation, so it does not reduce in the kernel, and `Expr` has no
`DecidableEq` either, so `decide` is unavailable too. Not a §2 result — §2 records no `headBeta`
claim — so nothing recorded failed to reproduce here; but the fix is on the record: the β-step is
stated at the `VExpr` level, where `VExpr.betaHead` (B6 §1) is pure Lean
(`vRedexDom_betaHead : vRedexDom.betaHead = vContrDom`, by `rfl`), and §1/§2 supply the bridge
(`ntreeNodeRedexDom_reify`, `ntreeNodeContrDom_reify`: each `Expr` domain is `stripBinderData`-equal
to the `toExpr` reification of the corresponding `VExpr`). That is a *stronger* statement than the
`Expr`-level one, not a weaker one, since it also exhibits the two as reifications.

### T8 — increment 7 landed: §5 anti-vacuity, §6 the arity-0 witness, §7 the axiom audit

File complete: 614 lines, **zero errors and zero warnings** (`lean_diagnostic_messages` at severity
`warning` returns an empty list; `lake build` replays clean).

**A finding, not in §2, and it is P7/M13's trap sprung.** `constLookupU_staged` — the staged
`ConstLookup`, written to mirror B6's `constLookup_staged_ntree` — has an antecedent that is
**unsatisfiable at `ntreeEnvU`**:

```lean
theorem ntreeEnvU_addIndTypesC_none : ntreeEnvU.addIndTypesC ntreeAux ntreeK = none := rfl
```

`VEnv.addConst` returns `none` on a name already present (`Theory/VEnv.lean:27`), `addIndTypesC` is
`addConstList (D.typeConstsC K)`, and `ntreeAux.typeConstsC ntreeK` is exactly
`[(NTree, ⟨1, ∀ (α : Type u), Type u⟩)]` (proved by `rfl`) — whose name `ntreeEnvU` already carries,
because the table has to carry it for the *unstaged* lookup. So `constLookupU_staged` is **vacuously
true as stated**, and **B6's `constLookup_staged_ntree` is vacuous at `ntreeEnv` for exactly the same
reason** (its table also carries `NTree`). That is a fact about B6, in B6's file, not mine — recorded
here, not acted on.

Nothing in this file depends on it: `ctorStoresTr_of_ctorTr_setRecArgs` asks only for
`ConstLookup Γc env`, which is `constLookupU = fun _ _ h => h`. And the non-vacuous version is
supplied at the *pre-block* table `ntreeΓcU0` (= `ntreeΓcU` minus `NTree`):

```lean
theorem constLookupU0_staged_witness :
    ∃ env₁, ntreeEnvU0.addIndTypesC ntreeAux ntreeK = some env₁ ∧ ConstLookup ntreeΓcU env₁
```

— antecedent exhibited, `NTree` arriving from the block and `List`/`_nested.List_1` from the pre-block
environment, which is `constLookup_staged_of_split`'s disjunction discharged leaf by leaf.

`ntreeSurf_userBlockR_witness` is arity 0 and **every conjunct is an equation or an existential**;
the four universally quantified conjuncts (the general left-inverse, the bridge, the redex control)
are the general theorems, whose hypotheses are `Us.Nodup`/`lvlWF` and nothing else.

### T9 — measurements (`scripts/exists.lean`, population 469 built modules)

Every name below: `own value is a hole: false`, `cone reaches sorryAx: false`, `watched declarations
in cone: none of 6`. Names as the script prints them (`ntreeΓcU` carries a Greek Γ).

| name | arity | cone | `#print axioms` |
|---|---|---|---|
| `Lean4Lean.VLevel.toLevel` | 2 | — | `propext` |
| `Lean4Lean.VLevel.ofLevel_toLevel` | 4 | 908 | `propext, Quot.sound` |
| `Lean4Lean.VLevel.mapM_ofLevel_toLevel` | — | — | `propext, Quot.sound` |
| `Lean4Lean.VExpr.toExpr` | 2 | 592 | `propext` |
| `Lean4Lean.VExpr.lvlWF` | 2 | 53 | none |
| `Lean4Lean.VExpr.ctorTr?_toExpr` | 8 | 1163 | `propext, Quot.sound` |
| `Lean4Lean.stripBinderData` | 1 | 396 | `propext` |
| `Lean4Lean.ctorTr?_stripBinderData` | 4 | 925 | `propext, Quot.sound` |
| `Lean4Lean.InductiveDeclExamples.ntreeΓcU` | 1 | 342 | `propext, Quot.sound` |
| `Lean4Lean.InductiveDeclExamples.constLookupU` | 0 | — | `propext, Quot.sound` |
| `Lean4Lean.InductiveDeclExamples.ntreeNode_ctorTr?_typeR` | 0 | 1007 | `propext, Quot.sound` |
| `Lean4Lean.InductiveDeclExamples.ntreeNode_ctorTr?_typeR_of_general` | 2 | 1279 | `propext, Quot.sound` |
| `Lean4Lean.InductiveDeclExamples.user_is_reification` | 0 | 900 | `propext, Quot.sound` |
| `Lean4Lean.InductiveDeclExamples.ntreeAux_setRecArgsD` | 0 | 898 | `propext, Quot.sound` |
| `Lean4Lean.InductiveDeclExamples.chain` | 0 | 1362 | `propext, Classical.choice, Quot.sound` |
| `Lean4Lean.InductiveDeclExamples.ntreeNodeRedex_ctorTr?_none` | 3 | 982 | `propext, Quot.sound` |
| `Lean4Lean.InductiveDeclExamples.vRedexDom_betaHead` | 0 | — | `propext` |
| `Lean4Lean.InductiveDeclExamples.ntreeEnvU_addIndTypesC_none` | 0 | — | `propext, Quot.sound` |
| `Lean4Lean.InductiveDeclExamples.constLookupU0_staged_witness` | 0 | 515 | `propext, Quot.sound` |
| `Lean4Lean.InductiveDeclExamples.ntreeSurf_userBlockR_witness` | 0 | **1561** | `propext, Classical.choice, Quot.sound` |

`ntreeΓcU`'s cone 342 against B6's `ntreeΓc` 341 is the one extra `` ``List `` literal — the whole
cost of widening the table. **P8 (0.9) — HIT**: nothing beyond
`propext`/`Quot.sound`/`Classical.choice` anywhere, no `sorryAx`, zero warnings.

`lean_verify` on the witness (not `#print axioms`, which line-wrapped in the build log) confirms
`["propext","Classical.choice","Quot.sound"]`.

### T10 — the consumer question (P9), and the closure re-measured

Closure with `UserBlockR` itself included: **205 modules, 171 `Lean4Lean.*`** — T1's B6 figure
(204/170) plus this file, consistent.

* `Lean4Lean.Verify.Inductive.TrIndDeclNProducer` — **the feasible named consumer.** It is OUT of
  this file's closure and this file is OUT of its 207-module closure, so `import
  Lean4Lean.Verify.Inductive.UserBlockR` there is **acyclic**: one import, no proof move, no
  migration. (It does not even import B6 today, so it would gain both.) `can-cite.py` reports `NO …
  would have to gain Lean4Lean.Verify.Inductive.UserBlockR`, which is the import-order fact, not a
  missing proof. I have not made that edit — `TrIndDeclNProducer` is not one of my two files.
* `Lean4Lean.Verify.Environment.InductR` — **impossible, and it is a cycle.** `exprOf%` is *defined*
  in `InductR` (line 771) and this file uses it, so `InductR` is IN this closure. It can never cite
  the headline.
* `Lean4Lean.Verify.Inductive.NestedRestoreWit` — **impossible, same reason**: IN this closure (via
  the `B6 → … → NestedOccData → NestedRestoreWit` chain T1 measured). So of P9's three candidates
  exactly one is viable, and it is B6's own named consumer.
* `Lean4Lean.Verify.Inductive.FlipConstruct` — **OUT**, re-confirmed. `tr_ntreeNodeType`, the
  hand-built `TrExprS` of exactly the user's node type, is `NO` for this file too (`can-cite.py`:
  "would have to gain `Lean4Lean.Verify.Inductive.FlipConstruct`"). So the headline is **proved, not
  borrowed** — P10's dangerous exclusion holds for `UserBlockR` as it did for B6.

### T11 — reproduction verdict on §2

**Everything in §2 reproduced.** M1's three facts are the premise of the file rather than restated in
it; M2, M3, M6 and M8 all elaborate exactly as recorded, and M7's negative measurement holds in the
writing (`noLam_of_ctorTr` is cited nowhere and there is no place in `ctorTr?_toExpr`'s `.lam` case
for it to go). Three deviations, all in the *proofs* and none in a statement, all logged above at the
increment that hit them:

1. T2 — `List.getD_eq_getElem` does not exist under that name on v4.33.0-rc2; `List.getElem_eq_getD`
   reversed does the same job.
2. T5 — `VExpr.ctorTr?_toExpr` needs its implicits supplied explicitly when the side conditions are
   discharged by `decide`, and `lvlWF` needed a `Decidable` instance (`VExpr.decidable_lvlWF`) for
   `decide` to be available at all.
3. T7 — the β-step of the control cannot be stated as `Expr.headBeta … = … := rfl` (`headBeta` is
   `@[extern]`/`opaque` and `Expr` has no `DecidableEq`); it is stated at the `VExpr` level with
   `VExpr.betaHead`, plus the `toExpr`/`stripBinderData` bridge to the `Expr` level, which is
   strictly more than the `Expr`-level claim would have been.

Plus one finding §2 did not have: **T8's vacuity of the staged `ConstLookup`** at any table that
carries the block's own member name — which applies verbatim to B6's `constLookup_staged_ntree`.
