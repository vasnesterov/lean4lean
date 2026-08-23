# Handoff: the stratified route to `IsDefEqU.sort_inv`

Rewritten after four candidate repairs failed their own row-zero checks. **The previous
version of this file described a route that is now known to be closed**; if you are reading a
cached copy, stop and re-read this one.

**Target:** `Lean4Lean.VEnv.IsDefEqU.sort_inv` and its family in
`Theory/Typing/Injectivity.lean`. **Still open, and the target statement has not moved.**

### Where the route stands, plainly

| statement | status |
|---|---|
| `PropTypeAgree` | **open.** Five of twelve conversion cases close. Three characterised obstructions: `forallEDF` (context conversion, index drop), `proofIrrel` (self-reference), `eta` (needs `SortForallEDisjoint`). `constDF`, `appDF`, `beta`, `extra` uncharacterised. |
| `SortForallEDisjoint` | **one open case, and likely true.** Six of seven typing cases close from `DefInv` alone; only `AppCase` remains, and a refutation is *provably impossible* at the model's own witness (§9). **The hereditary shape agreement proposed for `AppCase` is now closed both ways** — as disjointness it is *equivalent* to the statement itself, as agreement it is *false* (§9, machine-checked). `AppCase` is the statement's own fixpoint. |
| `PropUniq`, `SortUniq` | **in the normalisation family, and no model route.** Both fail the criterion's `trans` test; `SortUniq` is refuted as a semantic consequence by the cumulativity check, and the model is parameterised on it. |
| the reference | **two documented defects**, one machine-checked (§2a), one a reading result with a repair (§2b). |

The obstruction was diffuse and is now two named statements. What the route produced beyond
that is in §7 — read it, because it is more than what it closed.

---

## 0. Read this first

Two things a fresh reader will otherwise re-derive:

1. **The reference's proof of `thm:utype` is invalid**, machine-checked, over the empty
   environment. Not "hard", not "unproved" — the inference it uses at `unique.tex:51` is
   false. `docs/reference-gap-thm-utype.md` is the write-up; read its **§4 (scope)** before
   quoting anything else, because the *statement* of `thm:utype` is **not** refuted and
   `DefInv` in its literal form is **not** refuted.
2. **Every repair to the alternation index is closed by one arithmetic argument** (§3 below).
   The argument does not mention the repair's shape, so it closes the family: depth-0 rules,
   general-depth `Ctx.InstN` rules, explicit substitutions, and context morphisms alike.

The general rule the previous handoff drew — *necessity has to be checked against the
specification, not the tree* — held up and then paid again in the opposite direction: this
time the specification was the thing that was wrong, and the check that settled which way it
ran was verifying that this tree's one deviation only *enlarges* the judgment, so an
underivability result holds a fortiori for the reference.

---

## 1. What is proved, sorry-free

All `#print axioms` clean: `propext` and `Quot.sound` only. No `sorryAx`, no `native_decide`,
no `bv_decide`, no axiom added.

| Name | File | What |
|---|---|---|
| `Stratified.{mono, weakN, instN}`, `IsDefEqN.{zero_iff, inst0}`, `IsDefEq.stratifyN` | `Typing/Stratified.lean` | the index, the four n-provability basics, weakening and substitution |
| `DefInv`, `DefInv.zero` | `Typing/UniqueTypingN.lean` | definitional inversion (`unique.tex:29–35`) and `thm:0dinv` |
| `SubstC`, `SubstC.zero`, `SubstC.of_hasTypeN_zero` | `Typing/UniqueTypingN.lean` | the inference at `unique.tex:51`, isolated; true at `n = 0` and on the conversion-free fragment |
| `HasTypeN.{bvar,sort,const,app,lam,forallE}_inv` | `Typing/UniqueTypingN.lean` | subject-shape inversion at the index — **the most reusable thing here** |
| `Stratified.uniq`, `HasTypeN.uniq_zero` | `Typing/UniqueTypingN.lean` | `thm:utype` from `DefInv` + `SubstC`; content only at `n = 0` |
| `IsDefEqU.sort_inv_of_defInv`, `sort_forallE_inv_of_defInv` | `Typing/UniqueTypingN.lean` | **the target reduced to `∀ n, DefInv`** — uses neither `uniq` nor `SubstC` |
| `DefInv.sort_proofIrrel` | `Typing/UniqueTypingN.lean` | at the index, `unique.tex:266` needs only `DefInv` clause (1), not `SortUniq` |
| `SubstCRefute.{lhs_not_hasType0, stuck, substC_false, defInv_forallE_inst_false}` | `Typing/SubstCRefute.lean` | the refutation |
| `IsPropN`, `PropTypeAgree` | `Typing/UniqueTypingN.lean` | the set model's syntactic import, at the index |
| `sortNotProof_of`, `forallENotProof_of` | `Typing/UniqueTypingN.lean` | **the payoff, checked not assumed**: `PropTypeAgree` + `DefInv` at `n` give "a sort is not a proof" and "a Π-type is not a proof" at `n` — both the induction hypothesis, so not circular |
| `SortForallEDisjoint`, `SortForallEDisjoint.AppCase`, `sortForallEDisjoint_of` | `Typing/UniqueTypingN.lean` | the primitive `PropTypeAgree` needs, and six of its seven cases |
| `PropNotProof`, `PropTypeAgree.{eta_case, proofIrrel_case}`, `propNotProof_of` | `Typing/UniqueTypingN.lean` | each case closes **from its residual and nothing else** — which is what makes the residual an exact obligation rather than an approximation |
| `Apply`, `Apply.{conv_head, hasType}`, `Apply₂.{left,right}` | `Typing/ShapeSpine.lean` | spines at the index; `hasType` is the collapse lemma — a spine result is a type of the applied term |
| `SortForallEDisjointH{,₂}.iff`, `SortForallEDisjoint.appCase` | `Typing/ShapeSpine.lean` | **the hereditary disjointness is equivalent to `SortForallEDisjoint`**, and `AppCase` follows from the statement itself — §9 |
| `typeShapeAgree_false`, `substShapeAgree_false` | `Typing/ShapeSpine.lean` | **the agreement (`iff`) form is FALSE at `n = 1`**, by `SubstCRefute`'s witness lifted to a term with two types |
| `SubstDisj`, `SubstDisj.zero`, `applyDisj`, `applyDisj_zero` | `Typing/ShapeSpine.lean` | the surviving form, named and shown satisfiable; with `DefInv` it gives spine determinism at a type |

**The inversion lemmas are the asset.** They made the refutation a fifteen-line induction
instead of a confluence argument, and they made the `:266` improvement a five-line proof.
Reach for them before writing any new induction over `Stratified`.

---

## 2. The two reference defects, with confidence levels

Do not blur these.

**(a) `unique.tex:51` — machine-checked, empty environment.** `thm:utype`'s application case
uses "from `Γ,x:α ⊢ₙ β ≡ β'` and `Γ ⊢ₙ e₂ : α`, conclude `Γ ⊢ₙ β[e₂/x] ≡ β'[e₂/x]`". False at
`n = 1`. The counterexample puts the type mismatch **under an application**, where no
premise-free rule reaches — a first attempt that put it in a *binder annotation* was **not** a
counterexample, because `lamDF` + `sortDF`, both premise-free, repaired it. Write-up:
`docs/reference-gap-thm-utype.md`.

**(b) `unique.tex:180` — reading result with a worked configuration, plus a repair.** The
bullet concludes the lift's *output* type is a `Prop`; it does not follow, since
`Quot.lift`'s `{α : Sort u}` and `{β : Sort v}` are independent (verified against
`~/lean4/src/Init/Prelude.lean:443` and this repo's `quotLiftConst`). The reference's own
`typesys.tex:50` configuration is a counterexample to `thm:gg_compat`. **Repairable**, by the
reference's own device: a `K⁺` rule for `Prop`-quotients, exactly parallel to the one
`unique.tex:103` gives subsingleton inductives, with every clause of its justification
transferring verbatim. `reference-gap-thm-utype.md` §11.

---

## 3. Four candidates, four row-zero failures

| candidate | check | outcome |
|---|---|---|
| instantiation as a rule | does `thm:ckappa` absorb the new case? | **no**, by arithmetic — see below |
| a different stratification | is there a measure? | **no** — height gives `≤` not `<`; the tension is generic to the family |
| de-stratify | how many uses of unique typing in §§3–4? | **three**; `:180` now eliminated, `:266` reduced, `:272` remains |
| `sort_not_proof` from the model | which statement can a model reach? | **blocked** — the model is *parameterised* on `SortUniq` |

**The arithmetic that closed the first family.** Write `k` for the index an instantiation rule
concludes at and `j` for its typing premise's index.

* **(R1) `thm:utype`'s application case forces `j = k`** — the `app` rule hands it
  `Γ ⊢ₙ e₂ : A` and an IH at index `n`, and its conclusion must be at `n`.
* **(R2) `thm:ckappa` forces `j ≤ k−1`** — `≡ᵏ` is defined (`unique.tex:240`) with the side
  condition `Γ ⊢ e₁,e₂ : α`, a `⊢ₖ₋₁` typing under the §3 convention (`unique.tex:64`).

Both halves machine-checked at `k = 1`. The argument never mentions the rule's depth or
premise shape, so it closes explicit substitutions and context morphisms too — **the context
machinery was never the binding constraint.**

**The model check.** `Theory/SetModel/` is parameterised throughout on
`(L : LevelAssign env nv)` and nothing constructs one; `LevelAssign.srt_sound` *is* `SortUniq`
restated. And `SortUniq` is **false in the cumulative extension**, which any nested-universe
model validates — so no model can supply it. Recorded in `Typing/SortUniq.lean`'s docstring,
where its consumers look.

---

## 4. Where the obstruction sits: two statements

**"A sort is not a proof", and its Π analogue.** `:180` is eliminated by the `K⁺` repair;
`:266` needs only `DefInv` clause (1) (machine-checked); `:272` and clause (3)'s `proofIrrel`
case need exactly this.

* *Syntactically*, unstratified, it needs `uniq`, and the self-reference has no decreasing
  measure — the obvious height measure gives `≤`, not `<`.
* *Semantically*, it needs the model, which is parameterised on `SortUniq`.
* *At the stratified index* it is the induction hypothesis — which is what the index is
  **for**, and the index is broken by (a) above with no repair.

---

## 5. The live lead: `PropTypeAgree`

**The criterion, first, because it predicts rather than explains.**  It reformulated itself on
its third application, in the direction of being more predictive; the sharpened form is the
one to use.

> **Does the statement's induction ever have to look at a conversion derivation at all?**
> If it does not, it is tractable.  If it does, it is tractable exactly when its conclusion is
> **propagated along** the conversion rather than **asserted of** its endpoints — the first
> tolerates an arbitrary middle term at `trans`, the second does not.

The second clause is the earlier form of the criterion and is now a special case of the first.
Five applications, and it has predicted before explaining every time after the first:

| statement | induction sees a conversion? | conclusion | `trans` | outcome |
|---|---|---|---|---|
| `sort_inv` / `DefInv` clause (1) | yes | endpoint-asserted | fails | needs normalisation |
| `PropTypeAgree` (residual `PropConvInv`) | yes | propagated | closes | tractable |
| `PropUniq` | yes | endpoint-asserted | fails | needs normalisation |
| `SortForallEDisjoint` | **no** — induction on *typing* | — | never arises | tractable, 6 of 7 cases |
| shape-disjointness under substitution | yes | propagated | closes | does **not** inherit `SubstC`'s refutation |
| shape-***agreement*** under substitution | yes | propagated | closes | **FALSE** — `substShapeAgree_false` |

**Row 5 was under-specified and row 6 is the correction.** "Shape-disjointness under
substitution" names two different statements — a negation and an `iff` — and the criterion
separates them the wrong way round from what one wants: the `iff` is the one that composes at
`trans`, and the `iff` is **false**, refuted by the `SubstC` counterexample with no extra
construction.  The negation is true-as-far-as-known and does *not* compose.  §9 has the
detail; the general lesson is trap #10.

Route future statements through this before attempting them.

**And an irony worth stating, because the natural reasoning goes the other way.** The obvious
move is to attack these statements *unstratified*, since closing there would make the index
unnecessary. It is the wrong move: unstratified, the sort inversion these proofs need is
`HasTypeStrong.sort_type`, which *provably takes `SortUniq` as a hypothesis*, because this
tree's `IsDefEq` is type-indexed and composing conversions at two types **is** unique typing.
At the index, `HasTypeN.sort_inv` is free. So the setting that looks like the escape is the
one carrying the port's own defect, and the index — whose published metatheory is refuted in
§2 — is where this family of cases is cheap.


The model stream has re-parameterised and now imports one statement:

> `Γ ⊢ e : A`, `Γ ⊢ e : A'`, `A` a proposition ⟹ `A'` a proposition.

`sort_not_proof` is this at `e = .sort u`, so the two routes converged on it independently.
**It is strictly weaker than unique typing** (binary, not an equality) and it **passes the
cumulativity check** that refuted `SortUniq`.

**Row-zero, run: `trans` does *not* block it.** This is the finding that makes it worth
pursuing. Every case of `PropTypeAgree` reduces, via the inversion lemmas, to the residual

    PropConvInv : Γ ⊢ₙ A ≡ A'  ⟹  (IsProp A ↔ IsProp A')

and in that form `trans` **closes by composition** — `(ih1 d h).trans (ih2 d h)` — because the
property is *propagated along* the conversion rather than asserted of its endpoints. That is
exactly what `sort_inv`'s equality form is not, and it is why the arbitrary middle term that
blocks `sort_inv` is harmless here. `symm` likewise, given the `↔` form (the directed form
fails on `symm`, so state it as an iff).

Six of twelve conversion cases close, machine-checked in a scratch file:

* `rfl`, `symm`, `trans` — by composition;
* `sortDF` — retype the sort along the level equivalence;
* `lamDF` — **vacuous** given `DefInv` clause (3) (a λ's type is a Π, never `Prop`);
* the seven typing constructors die on `b = false`.

Open: `constDF`, `forallEDF`, `appDF`, `beta`, `eta`, `proofIrrel`, `extra`. Two things known
about these already:

* `forallEDF` is **not** vacuous — a Π *can* be a proposition (`imax u v ≈ 0` iff `v ≈ 0`,
  `VLevel.imax_eq_zero`), and the induction hypothesis is exactly about the codomain, which is
  what decides it. It resists on **context conversion** (`A::Γ` versus `A'::Γ`), the same
  thing that blocks `DefInv` clause (2)'s `symm` case.
* `beta` will meet the substitution index if attempted at the index; unstratified it should
  not.

### `PropUniq` — the model's *other* import, and it is on the wrong side

The model needs a second statement: **`PropUniq`** — `Γ ⊢ A : .sort u`, `Γ ⊢ A : .sort v`,
`u ≈ 0` ⟹ `v ≈ 0` (i.e. "`IsProp` is well-defined on types", where `PropTypeAgree` is
"`IsProof` is well-defined on terms"). Both are strictly weaker than `SortUniq`; that gain is
real. But they do not behave alike.

**Row-zero, run: `PropUniq` has `sort_inv`'s `trans` problem.** After shape inversion sends
both typings to the shape-determined type, its residual is
`.sort u ≡ₙ .sort v ⟹ (u ≈ 0 ↔ v ≈ 0)`. Machine-checked: `rfl`, `symm` and `sortDF` close, and
`trans` does **not** — `.sort u ≡ₙ X ≡ₙ .sort v` needs `X` to be a sort and nothing says it is.

The contrast with §5 is exact, and it is the same distinction:

| | conclusion | `trans` |
|---|---|---|
| `PropConvInv` (`PropTypeAgree`'s residual) | *propagated along* the conversion | closes: `(ih1 d h).trans (ih2 d h)` |
| `PropUniq`'s residual | *asserted of the endpoints* | fails: middle term need not be a sort |

So `PropUniq` needs normalisation, which puts it in the `SortUniq` family — and the
cumulativity check gives it no model route either. **Finishing `PropTypeAgree` does not
discharge the model.**

What `PropTypeAgree` *does* buy is on the syntactic side, and **both halves are now checked
rather than assumed**:

* `sortNotProof_of` and `forallENotProof_of` (landed, sorry-free, `Typing/UniqueTypingN.lean`):
  `PropTypeAgree` at `n` together with `DefInv` at `n` — both the induction hypothesis, so
  nothing is circular — give "a sort is not a proof" and "a Π-type is not a proof" at `n`.
  *(Note the second is not "a Π is not a proposition", which is false: `∀ x : α, β` is a
  proposition whenever `β` is. It says a term whose type is a Π does not also inhabit a
  proposition.)*
* With those, **`DefInv (n+1)` clause (1) closes in every case except `trans`** — machine-
  checked. `proofIrrel` closes outright.

So this removes **one** of the two obstacles in §4 and leaves the other standing alone:
`trans`/normalisation, and nothing else.

### The remaining cases, with what is known

**`forallEDF` resists on context conversion, and the target-preserving idea does not apply.**
The statement here is *already* target-preserving — same term `B'`, same target `.sort .zero`
— so the blocker is not an injectivity dependency but the index drop: context conversion for
the conversion half at `n+1` needs it for the typing half at `n`, while the context conversion
`A ≡ A'` is available only at `n+1`. Same family as the substitution gap. *Analysis, not
machine-checked.*

**`proofIrrel` is vacuous given the statement itself.** If `IsProp h` and `h : p : Prop`, then
`h`'s two types `p` and `.sort .zero` disagree on propositionhood, contradicting
`PropTypeAgree` at `h`. So it is not an obstruction to the *statement*, only a self-reference
in the *induction* — and the measure gives `≤`, not `<`, as at `DefInv.sort_proofIrrel`.
Attack it separately, not inside the induction. *Analysis.*

### Is `PropTypeAgree` closable at the index? — **No. One new primitive is needed.**

Settled, machine-checked. The three characterised cases are **two** obstructions, not one and
not three:

* **`forallEDF`** wants **context conversion at a preserved index**, and it is **not
  refuted** — the attempt is recorded below because where it resists is informative.

  *Diagnostic, machine-checked.* Context conversion at a preserved index closes for **every**
  rule except `appDF`, `beta`, `eta`, `proofIrrel` — the same four the substitution wall
  breaks at, and for the same reason (conclusion at `n+1`, typing premises at `n`, context
  conversion available only at `n+1`). Notably the `bvar` case, which looks like the obvious
  problem, closes cleanly: the fix-up conversion *is* the context conversion, weakened, and
  `Stratified.weak` preserves the index.

  *The conversion half is refutable*, by the same construction as §2a: in context `A'::Γ` the
  term `.app (.lam A (.bvar 0)) (.bvar 0)` is not `⊢₀`-typeable — its typing wants
  `.bvar 0 : A` at `⊢₀` while `Lookup` gives `A'` — so the `stuck` argument transfers and the
  `beta` conversion `.app (.lam A (.bvar 0)) (.bvar 0) ≡₁ .bvar 0` does not transport.
  ≈70 lines; not built, because it does not settle the question.

  *The typing half — which is what `forallEDF` actually needs — resists*, and for a specific
  reason: a typing's use of `bvar 0` at the wrong type is **repairable at index `n`** by
  `conv` along the context conversion itself. The index-`n−1` sub-derivations that break
  appear only *inside* conversions. So every counterexample that refutes the conversion half
  fails to lift to the typing half.

  **Status: the natural proof route for `forallEDF` is dead; the statement it needs is open.**
* **`proofIrrel` and `eta` look alike and are not.** `proofIrrel`'s residual is exactly
  `PropNotProof`, and `propNotProof_of` derives that *from `PropTypeAgree` itself* — the same
  statement at another subject, measure `≤` not `<`, so it is self-reference.  `eta`'s
  residual is exactly `SortForallEDisjoint`, and there is **no** such derivation: it is a
  separate weakening of unique typing, about a term's types being a sort versus a Π rather
  than about propositionhood.

**The primitive, named:**

    SortForallEDisjoint env U n :
      Γ ⊢ₙ e : .sort u  →  Γ ⊢ₙ e : .forallE A B  →  False

`PropTypeAgree.eta_case` and `PropTypeAgree.proofIrrel_case` (landed, sorry-free) show each
case closes from its residual and nothing else, so this is the precise obligation, not a
description of a gap.

It **passes the cumulativity check** — cumulativity retypes at sorts and never gives a Π-typed
term a sort type — so unlike `SortUniq` it is not excluded from a semantic argument in
principle. Whether the *model* can supply it is a separate question, since `Theory/SetModel/`
remains parameterised on `LevelAssign`.

**Unstratified is worse here, not better, and the reason is a port artifact.** The `sortDF`
case needs a typing inversion for sorts, and unstratified that is
`HasTypeStrong.sort_type` — which *provably takes `SortUniq` as a hypothesis*, because this
tree's `IsDefEq` is type-indexed and composing conversions at two types is `uniq`
(`Typing/SortUniq.lean` documents this). At the index, `HasTypeN.sort_inv` is free. **Work
this statement at the index.**

---

## 6. Traps that cost real time

1. **Arity.** `forallE_inv` names two unrelated families; a plain grep overcounts ~3.5×.
2. **Namespace.** `Lean4Lean.VEnv.Params` and `Lean4Lean.Params` are different classes. A
   claim about instantiation must carry its namespace.
3. **Case-pattern implicits.** `Stratified.bvar` has one more implicit than `IsDefEq.bvar`.
   Copying a case pattern between judgments requires counting implicits, not matching names.
   `induction ... with | ctor h1 h2` binds only explicit fields and IHs.
4. **Two head notions.** `VExpr.headConst?` peels λ; `VExpr.spineHead` does not.
5. **Index arithmetic.** `Stratified.instN` must be written `m + n`, never `n + m`.
6. **`rfl` is captured.** Inside these files `rfl` can elaborate to `Stratified.rfl`; write
   `(Eq.refl true)` when an equation is meant.
7. **`nomatch` needs constructors.** It cannot see through a `def`; `simp [thedef] at h`.
8. **A negative check licenses "not excluded", never "open".**  The cumulativity check shows
   `SortForallEDisjoint` is not *excluded* from semantic argument; it does not show a route
   exists.  **It cost a round.**  Writing "not excluded from a semantic argument in principle"
   was read as "a route exists"; the coordinator relayed the stronger reading and routed a
   model enquiry on it, and the model stream's first act was to correct the premise.  State
   what a negative check does not rule out, never what it opens.
9. **Reasoning about vacuity is unreliable.** Two cases in the `PropTypeAgree` pass were
   called vacuous by inspection and one was wrong (`forallEDF`). Run it.
10. **A statement that passes the criterion may pass it for free.** "The propagated iff
    `trans`-closes, machine-checked" was recorded for shape-disjointness and was *true* — of
    the version stated about a **conversion**, where it is not a theorem but a triviality
    (`SortLike` composes with `trans'`). The version that does the work is stated about a
    **substitution**, and it is false (`substShapeAgree_false`). Before recording a criterion
    pass, check the statement is the one the consumer needs *and* that the pass cost something.
11. **A "strengthening" can be the same statement.** The hereditary shape-disjointness is
    logically equivalent to `SortForallEDisjoint` (`SortForallEDisjointH.iff`), because a spine
    peeled off a type of `e` is a type of the applied term. Before funding a strengthening,
    prove it is one — or check whether the target's own rules already derive the extra clause.

---

## 7. What this route produced

The target has not moved, and the route produced more than it closed. Along the way:

* **a machine-checked defect in the published metatheory this project is built on** (§2a), and
  a second defect with a repair (§2b);
* **four candidate repairs closed by their own row-zero checks** (§3) — one of them by an
  arithmetic argument that closes a whole family without mentioning its shape, so the
  expensive machinery it would have needed was never the binding constraint;
* **a correction to the project's own model of the problem**: unique typing is used in §§3–4
  at three sites, not pervasively — and of those, `:180` is eliminated by the `K⁺` repair and
  `:266`/`:272` are discharged by `sortNotProof_of`/`forallENotProof_of`;
* **a diffuse obstruction reduced to two named statements**, each with its residual stated as
  an exact obligation rather than a description;
* **a criterion that predicts rather than explains** (§5), which reformulated itself on its
  third application in the direction of being more predictive, and has now decided five
  statements.

Build the unknown first. Every one of these came from running the check that was flagged as
unpriced, before building the thing it gated.

---

## 8. What is left after `PropTypeAgree`: `trans` alone

If `PropTypeAgree` lands, the residual of the whole route is one case. Framing for whoever
prices it — an option set, not a recommendation:

* **The criterion says `trans` cannot be dodged by reformulation.** Clause (1)'s conclusion is
  inherently asserted of its endpoints ("both are sorts, and their levels agree"), so no
  propagated-along restatement of it exists. It needs a *reduction relation* — something that
  says what the middle term does.
* **`unique.tex` §§3–4 (κ-reduction + Church–Rosser) is now materially cheaper than it looked.**
  Its uses of unique typing were measured at three sites; `:180` is eliminated by the `K⁺`
  repair (§2b), and `:266`/`:272` are exactly what `sortNotProof_of`/`forallENotProof_of`
  discharge. So if `PropTypeAgree` lands, §§3–4 restated over `IsDefEqN` has **no remaining
  unique-typing dependency** — it becomes transcription plus one rule repair.
* **A sorts-only normalisation is not a shortcut.** "A term convertible with a sort reduces to
  a sort" is not closed under its own induction: its `appDF` case needs the function's
  argument to reduce to a λ, dragging in Π-shape.
* **A different metatheory** (algorithmic conversion plus a logical relation) breaks the
  typing/conversion circle without a reduction relation at all. Standard in the literature,
  outside anything `~/lean-type-theory` provides, and large.

---

## 9. `SortForallEDisjoint`: where it stands

**Six of seven typing cases close from `DefInv` alone** (`sortForallEDisjoint_of`, sorry-free).
`trans` never arises — this is an induction on typing.  Only `app` is open.

**A refutation is provably impossible at the model's own witness.**  The six closed cases force
any counterexample to have an **application** subject.  The model's witness — `False` versus
`∀ x : False, B` — is a **constant**, and the `const` case is machine-checked.  So the model's
non-separation is real *and* cannot be lifted to syntax there.  The two facts are consistent
rather than in tension: the model genuinely does not separate them, the syntax genuinely does.

**`AppCase` is the whole remaining content of the statement — and read this before starting
it.**  Its first instinct will be that it inherits `SubstCRefute`'s refutation.  **It does
not, and not obviously so.**  What `SubstC` says, and what is refuted, is that *a conversion
survives substitution*.  What `AppCase` needs is only that *two shapes stay apart under it* —
a sort never becomes a Π.  Those are different claims and the second is much weaker: a
substituted term can fail to preserve a conversion while still never turning a sort into a Π.
The counterexample in `SubstCRefute` does not refute the disjointness form — both sides of it
are shape-inert — and the disjointness form **passes the criterion**: stated as a propagated
iff (`X ≡ₙ Y ⟹ (IsSortLike X ↔ IsSortLike Y) ∧ (IsPiLike X ↔ IsPiLike Y)`), `trans` closes by
composition, machine-checked.

*One detail that matters:* the formulation decides it.  Stated as `¬(sort(B[a]) ∧ Π(B'[a]))` —
the natural reading of "disjointness" — `trans` **fails**, because the middle term may be
neither.  Stated as the propagated iff, it closes.  Same content; only one passes.

*Read the paragraph above with one correction, because it was the trap.*  The propagated iff
that `trans`-closes is stated **about a conversion** — `X ≡ₙ Y ⟹ (SortLike X ↔ SortLike Y)` —
and in that form it is not merely tractable, it is **free**: `SortLike X := ∃u, Γ ⊢ₙ X ≡ .sort u`
composes with `X ≡ₙ Y` by `trans'`, no induction at all.  It is therefore no leverage.  The
statement that does the work is the one **about a substitution**, and that one is false.  See
below.

### The hereditary shape agreement, priced — both horns machine-checked

`Theory/Typing/ShapeSpine.lean` (new, sorry-free, `[propext, Quot.sound]`).  The primitive
proposed for `AppCase` was:

> the types of a term agree on shape, **and** their codomains agree on shape after
> instantiation at any argument typed at both domains.

It has two readings, and **both are closed**.

**(1) As disjointness — the usable reading — it is *equivalent to `SortForallEDisjoint`
itself*.**  `SortForallEDisjointH.iff`, machine-checked, and the joint-spine version the
sentence literally asks for (argument typed at *both* domains) collapses the same way
(`SortForallEDisjointH₂.iff`).  The collapse is one lemma:

    Apply.hasType :  Γ ⊢ₙ e : T  →  Apply Γ T args R  →  Γ ⊢ₙ e a₁ ⋯ aₖ : R

A spine peeled off a type of `e` is a type of the *applied term*, so quantifying over spines
quantifies over terms — which the unstrengthened statement already does.  The hereditary
clause is **derivable, not additional**.

And `AppCase` follows from `SortForallEDisjoint` in one line
(`SortForallEDisjoint.appCase`): `Stratified.app` already gives `.app f a` the type `B₀.inst a`,
and `conv` retypes it at the sort.  So **`AppCase` is the statement's own fixpoint**, and
nothing equivalent to the statement can close it.  *This is the finding to carry: the app case
is not a gap that a cleverer statement of the same strength will fill.*

**(2) As agreement — an `iff` of shape predicates, the reading that *would* be stronger — it
is FALSE.**  `typeShapeAgree_false`, at `n = 1` over the empty environment.  The witness is
`SubstCRefute`'s, lifted from a substituted conversion to *a term with two types*, which is the
hypothesis `SubstCRefute` explicitly declined to supply:

    A := .sort (succ p)     D := (fun _ : A => x) x     P := ∀ (_ : A), D      (P closed)

    [P] ⊢₁ .bvar 0 : P                     and    [P] ⊢₁ .bvar 0 : ∀ (_ : A), .bvar 0
                                                  (retyped by `forallEDF` of the beta step)

so the single term `.app (.bvar 0) a` has the two types `lhs` (stuck: `⊢₁`-related to nothing
but itself) and `a = .sort (max p p)` (a sort).  One is sort-shaped, the other is not.
`P` is a well-formed type (`P_type`), so the refutation does not turn on a junk context.

What it does **not** refute: `SortForallEDisjoint` (neither type is a Π), and `PropTypeAgree`
(`lhs` is typed at `.sort (succ p)`, not at `Prop`).  What dies is exactly the *agreement*
reading.  The same witness refutes the substitution form directly (`substShapeAgree_false`),
which is the §5 table's new row 6.

**The shape of the bind, stated once.**  The usable form is asserted of endpoints and does not
compose; the composable form is an `iff` and is false.  A transitive relation implying
disjointness would have to classify the stuck term: the witness forces it to relate `lhs` to a
sort, so transitivity forbids it from relating `lhs` to any Π — i.e. it has already decided the
target question at `lhs`.  That is §8's conclusion reached from a third direction: what is
missing is a **reduction relation**, something that says what the middle term does.

### What is left, named rather than described

    SubstDisj env U n :
      Γ ⊢ₙ a : A  →  A::Γ ⊢ₙ B ≡ B'  →
      Apply Γ (B.inst a) args R₁ → Apply Γ (B'.inst a) args R₂ →
      Γ ⊢ₙ R₁ ≡ .sort u  →  Γ ⊢ₙ R₂ ≡ .forallE C D  →  False

Not equivalent to `SortForallEDisjoint` (it is about two types with no common term, so
`Apply.hasType` does not collapse it), **satisfiable** (`SubstDisj.zero`, the base index, next
to `DefInv.zero`/`SubstC.zero`), and it buys one thing, machine-checked:

    applyDisj :  DefInv → SubstDisj → two spines off *one* type cannot end at a sort and a Π

— from `DefInv`'s clause (2) with **no induction on the spine**, which is what a `bvar` case
needs.  *But do not route `SubstDisj` as sufficient without pricing the `lam` case first.*
Analysis, not machine-checked: a spine induction on typing trades the open `app` case for two
others.  `app` closes (the IH applies at `f` with the spine extended by `a`); `bvar` reduces to
`applyDisj`; **`lam` does not close** — its two types are `.forallE A B` and `.forallE A B₂`
for two types `B, B₂` of the body, and bridging them under instantiation needs an existence
step (a spine on the middle) that only the refuted `∀∃` form provides.  Consistent with (1):
the difficulty moves, it does not shrink.

*On `docs/design-shape-lattice.md` and `Lean4Lean/Experimental/`, read as instructed.*  That
development is the same idea carried much further — a shape lattice with a logical relation —
and its recorded refutations are the same obstruction at a different altitude: `IsType.common`
false, and every relativisation of it (`Compat`-only, `LE_Interp`-relative, `TyDefEq`-relative)
refuted, each because *two compatible Π-shapes need not share a codomain sort when their
domains disagree*.  The one survivor there, `common_sort`, reads the sort off **the term's
universe** rather than off the shapes — the same shape of escape as "get the fact from the
accompanying term, not from the relation".  Nothing there is reusable as-is (it is unproved,
does not compile, and its `[ParamsExtra]` chain was vacuous twice), but that survivor is the
one idea in it that this route has not tried.

## 10. Four independent convergences on one family

Recorded because whatever breaks this open will almost certainly be a single argument that
several consumers share:

1. the syntactic cone's `proofIrrel` case (`sort_not_proof`);
2. the set model's `LevelAssign.srt_sound` (`SortUniq` restated);
3. `PropTypeAgree`'s own `proofIrrel` case — self-reference at another subject;
4. the cut-down model, which bottoms out at `sort_not_proof` — i.e. at (3), from the opposite
   direction.

Impredicative formation forces the collapse the model cannot avoid; proof irrelevance forces
the identification.  Between them they close the semantic side for `SortUniq` and `PropUniq`
both.