# Circularity-breakers: four candidates, priced

Companion to `docs/reference-gap-thm-utype.md`, which establishes that the alternation index
of `unique.tex` cannot carry `thm:utype` and that no cheaper route to `∀ n, DefInv` exists.
This document scopes what could replace it. **Nothing here is built.**

## The bar every candidate must clear

The failing case is the application case of `thm:utype`:

> from `A::Γ ⊢ₙ B ≡ B'` and `Γ ⊢ₙ a : A`, conclude `Γ ⊢ₙ B[a] ≡ B'[a]`

and the counterexample that kills it puts the mismatch **under an application**, where no
premise-free rule reaches (`reference-gap-thm-utype.md` §8). A candidate that closes the
annotation case and leaves the application case is worth nothing at any price, so
"does it close the application case?" is the first line of every entry below.

---

## Candidate 1 — instantiation as a rule (explicit substitutions / context morphisms)

**What it is.** Stop treating substitution as an operation on finished derivations. Either add
`instC : (Γ ⊢ₙ a : A) → (A::Γ ⊢ₙ e ≡ e') → Γ ⊢ₙ e[a] ≡ e'[a]` to the conversion half, or, in
the general form, add a context-morphism judgment `Γ ⊢ₙ σ : Δ` and a rule instantiating a
conversion along it.

**Closes the application case? YES — checked, one line.** With the rule present,
`SubstC` is `fun h H => .instC h H`. Machine-checked against a scratch copy of
`Stratified.lean` carrying the rule.

**Cost, measured not estimated.** Adding the depth-0 rule to `Stratified.lean` costs exactly
four cases, and the modified file compiles sorry-free: one line each in `mono` and
`eq_of_zero`, two lines each in `weakN` and `instN`
(`rw [VExpr.liftN_inst_hi, VExpr.liftN_inst_hi]` and
`rw [← VExpr.inst_inst_hi _ _ _ 0 k, ← VExpr.inst_inst_hi _ _ _ 0 k]`; `beta`'s one-sided `▸`
is *not* the template, since both sides of a conversion move). The general-depth form needs a
`Ctx.InstN` premise plus lift/instantiate commutation lemmas for **contexts**, which this tree
does not have — and the general form is the one `§§3–4` needs, because instantiating a typing
derivation under a binder requires it.

**What breaks, and in which way.**

| already proved | fate |
|---|---|
| `Stratified.{mono, eq_of_zero, zero_iff, weakN, instN}`, `stratifyN` | **re-proof only** — verified, the modified file compiles |
| `SubstCRefute.stuck`, `substC_false` | **restatable and FALSE.** By design: the two hypotheses of the counterexample use only rules the candidate keeps, so `SubstC` becoming a theorem makes the refutation's conclusion derivable. This is the candidate working, not the candidate failing — but it means the refutation must be *deleted*, not ported |
| `DefInv` | **restatable but insufficient.** A conversion's subject becomes an arbitrary instance, and a variable instantiates to anything (`(.bvar 0).inst a = a`, checked), so subject-shape inversion must now handle a variable subject. `DefInv` grows clauses the reference does not have — at least "a sort is not `⊢ₙ`-equal to a variable" and its Π analogue |

**The risk that is not priced.** `thm:1dinv` proves definitional inversion by **inverting**
`⊢ₙ₊₁ X ≡ Y`, and so do `thm:gg_compat` and `thm:tri`. A substitution rule gives each of them
a case whose subject is an arbitrary substituted term. That is the same shape of failure one
level down, and it is why this candidate is not obviously a repair rather than a relocation.

**`Theory/` definition change?** `Stratified.lean` is in this stream's ownership. If the rule
has to go into the **ambient** judgment (`Theory/Typing/Basic.lean`'s `IsDefEq`), that is not
this stream's to make and would invalidate far more.

---

## Candidate 2 — a different stratification

**What it is.** Keep the strategy (make conversion at level `n+1` use only typings at `≤ n`)
but measure something other than alternation depth.

**Row-zero checks, run.**

* *Derivation height.* **Dead, and checked.** The `proofIrrel` case recurses on an instance of
  height `max(h₂,h₃) + O(1)` against the node's `max(h₁,h₂,h₃) + 1`: the measure gives `≤`,
  not `<` (`reference-gap-thm-utype.md` §9a).
* *Does the reference offer another form?* **No.** `typesys.tex` states the ambient judgments
  in the standard form and its "Regularity" section is a list of invariants, not an
  alternative stratification; `unique.tex:10–15` is the only stratification in the document.
* *Universe level as the measure.* Runs the wrong way: proof irrelevance relates `h ≡ h'` at
  type `p : Prop` from premises about `p` itself, one level **up**. Not obviously well-founded
  downward, and not attempted further.

**Closes the application case?** Unknown for any specific measure — and note the obstruction
is not tied to *which* measure: any measure satisfying "conversion at `n+1` uses typings at
`≤ n`" must count alternations, and alternations compose additively under substitution. That
is the tension stated in `reference-gap-thm-utype.md` §9a, and it applies to this whole
family. **This candidate is the weakest of the four and I would not fund it.**

---

## Candidate 3 — de-stratify: discharge §§3–4's uses of unique typing directly

**What it is.** The index exists for exactly one reason: `unique.tex` §§3–4 assumes unique
typing (`:64`) and so cannot be run before it. If each *use* is discharged independently, the
index is unnecessary — **and with the index gone, the substitution obstruction goes with it**,
because it is entirely an artifact of counting alternations.

**Row-zero check, run: how many uses are there?** Three, and they are identifiable:

| site | what it is | status |
|---|---|---|
| `unique.tex:266` | `thm:1dinv` clause (1), `proofIrrel` case | **needs strictly less than unique typing** — `VEnv.DefInv.sort_proofIrrel` (landed) shows it needs only clause (1) on a derived instance, and not even the `Prop`-ness premise. At the index that is the induction hypothesis; unstratified it is `sort_not_proof` |
| `unique.tex:272` | `thm:1dinv` clause (2), `proofIrrel` case | needs "a Π-type is not a proof" |
| `unique.tex:180` | `thm:gg_compat`, the `lift`/quotient case | **checked — and it does not reduce.** See below |

Plus the blanket assumption at `:64`, which is what the three sites cash out to.

So the coupling between confluence and unique typing is **three sites, not pervasive** — a
much thinner dependency than "the confluence development needs unique typing", which is how it
has been described in this repo up to now.

**Closes the application case?** It **dissolves** it: unstratified there is no index to
preserve, and substitution is the ordinary substitution lemma, already proved in this tree for
the ambient judgment (`IsDefEq.instN`, `Theory/Typing/Lemmas.lean`).

**Cost.** The §§3–4 development, unstratified — the κ-reduction, `≡ₚ`, parallel reduction,
`thm:gg_compat`, `thm:tri`, Church–Rosser, `thm:ckappa`. Large, but this is transcription of a
published proof whose *only* extra inputs are the three sites above, and it is the development
`ChurchRosser.lean` already partially is. **Nothing already proved becomes false**; the
stratified files (`Stratified.lean`, `UniqueTypingN.lean`, `SubstCRefute.lean`) become
unused rather than wrong.

**`Theory/` definition change?** None. This is proof work plus the two imports below.

**`unique.tex:180`, checked — and it sinks this candidate.**  The site uses unique typing in
its *full* form: from `Γ ⊢ q₁ : Quot R₁` and `Γ ⊢ q₁ : p` with `Γ ⊢ p : Prop`, conclude
`Quot R₁ ≡ p`.  The subject `q₁` is an arbitrary term, so there is no shape to invert and no
reduction to the "a sort/Π is not a proof" family that candidate 4 serves.  Discharging it
unstratified means proving `uniq` unstratified, which is `thm:unique` itself — circular.

*And it is worse than that: the site is not correct as written.*  See
`reference-gap-thm-utype.md` §11 — the bullet concludes that the lift's **output** type is a
`Prop`, which does not follow, and the reference's own `typesys.tex:50` configuration is a
counterexample to the lemma the bullet is proving.  So the third site cannot be discharged
*as written* because it does not go through; it needs re-derivation before its dependence on
unique typing can even be assessed.

**Verdict: do not build.**  Two of three sites reduce; the third does not, and is broken.
The number that made this candidate attractive — three — is right, but one of the three is
load-bearing in a way the other two are not.

---

## Candidate 4 — get "a sort/Π is not a proof" from the set model

**What it is.** Candidate 3's residual is mostly the two `proofIrrel` sites, and both reduce
to: *there is no `p` with `Γ ⊢ p : Prop` and `Γ ⊢ .sort u : p`* (and the Π analogue). Today
that is `VEnv.sort_not_proof` (`Theory/Typing/SortUniq.lean`), derived from the open
hypothesis `SortUniq`. A **semantic** argument may give it outright: in a set model whose
`Prop` types are interpreted as subsingletons whose elements are a fixed token, a universe
cannot be such an element.

**Row-zero check, run — and it discriminates sharply.** Ask which of the two statements a
model *can* prove, by asking which survives adding a cumulativity rule
(`Γ ⊢ e : .sort u`, `u ≤ v` ⟹ `Γ ⊢ e : .sort v`), since any model with nested universes — the
standard construction, and the one `soundness.tex` builds from n-inaccessibles — validates it:

* **`SortUniq` is false in the cumulative extension** (`.sort 0 : .sort 1` and `.sort 0 :
  .sort 2`, with `1 ≉ 2`). So `SortUniq` is **not a semantic consequence** and no
  model-theoretic route to it exists. This forecloses one of the four consumers listed in the
  `SortUniq` docstring, and it should be recorded there.
* **"A sort is not a proof" survives cumulativity** — cumulativity produces `.sort u : .sort
  v`, never `.sort u : p : Prop`. So the model route is open for it.

*(This check is an argument, not a Lean proof; it is the one item in this document that is
analysis. It is cheap to make rigorous by adding the cumulativity rule to a scratch copy of
`IsDefEq` and re-running the model's soundness proof — which is why it is worth doing before
anyone asks the model stream for `SortUniq`.)*

**Closes the application case?** Not by itself — it is an input to candidate 3, which does.

**Cost.** One export from `Theory/SetModel/`, whose difficulty depends on that model's
treatment of `Prop`. Small if the model already interprets propositions as subsingletons.

**`Theory/` definition change?** None, but it needs an export from `Theory/SetModel/`, owned
by another stream — not this one's to write.

---

## Ranking (after the `unique.tex:180` check)

The check was run and it inverted the order.

1. **Candidate 1** (instantiation as a rule).  It is now the only candidate that both closes
   the application case and serves `unique.tex:180` — and it serves `:180` for free, because
   in the stratified setting that site's "unique typing" is *unique typing at `⊢ₙ`*, i.e. the
   induction hypothesis, which is exactly what repairing `thm:utype` restores.  Its cost is
   the context machinery: the general-depth rule needs a `Ctx.InstN` premise plus
   lift/instantiate commutation lemmas **for contexts**, which this tree does not have.  That
   cost should be stated up front rather than discovered.
2. **Candidate 4** (`sort_not_proof` from the model) — still worth doing, now as an
   independent simplification rather than as candidate 3's enabler: it removes two of the
   three unique-typing sites whichever route is taken, and the cumulativity check shows it is
   the *only* one of the two statements a model can reach.  Recorded in `SortUniq.lean`'s
   docstring, where the question gets asked.
3. **Candidate 3** (de-stratify) — **withdrawn.**  Two of its three sites reduce; the third
   needs full `uniq` on an arbitrary subject, and is additionally broken as written.
4. **Candidate 2** (another stratification) — would not fund.

## What this check cost, and what it bought

It cost one reading pass and it changed the funding decision, which is what a row-zero check
is for.  It also turned up a second apparent gap in the reference
(`reference-gap-thm-utype.md` §11) — unformalized, unlike the first.
