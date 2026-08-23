# Handoff: the stratified route to `IsDefEqU.sort_inv`

Rewritten after four candidate repairs failed their own row-zero checks. **The previous
version of this file described a route that is now known to be closed**; if you are reading a
cached copy, stop and re-read this one.

**Target:** `Lean4Lean.VEnv.IsDefEqU.sort_inv` and its family in
`Theory/Typing/Injectivity.lean`. **Still open, and the target statement has not moved.**
What has changed is that the obstruction is now localised to a single named statement with
three named, individually-blocked routes — and that a defect in the published metatheory this
project is built on has been machine-checked.

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

## 4. Where the obstruction now sits: one statement

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

**The criterion, first, because it predicts rather than explains.**

> A conclusion **propagated along** a conversion tolerates an arbitrary middle term.
> One **asserted of** its endpoints does not.

`sort_inv`'s `trans` case fails because `.sort u ≡ e₂ ≡ .sort v` says nothing about `e₂`; the
IHs do not apply. It has now decided three statements — it explained why the equality form was
hopeless, predicted that `PropTypeAgree`'s binary form would close `trans` (it does, by
composition), and predicted that `PropUniq` would not (it does not). Apply it before
attempting any new statement on this route.

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
8. **Reasoning about vacuity is unreliable.** Two cases in the `PropTypeAgree` pass were
   called vacuous by inspection and one was wrong (`forallEDF`). Run it.

---

## 7. What this route produced

The target has not moved. Along the way: a machine-checked defect in the published metatheory
this project is built on, a second defect with a repair, four candidate repairs closed by
their own row-zero checks — one of them by an arithmetic argument that closes a whole family —
a correction to the project's own model of the problem (unique typing is used in §§3–4 at
three sites, not pervasively), and the reduction of a diffuse obstruction to one named
statement with three individually-blocked routes. Plus the live lead in §5, whose row-zero
came back positive.

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
