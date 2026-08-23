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

**The unpriced risk, now run — and it fails.  This candidate is dead, and so is its whole
family.**

The risk was recorded here as "`thm:1dinv`, `thm:gg_compat` and `thm:tri` each gain a case
with an arbitrary substituted subject".  Running it corrects that description twice, and the
correction is worse, not better.

*First, the case lands in one place, not three.*  `instC` is added to `⊢ₙ`, not to `≡ₚ` or
`≫ᵏ`.  `thm:gg_compat` inducts on `≡ₚ` and `thm:tri` on `≫ᵏ`, so neither gains a case, and
`thm:1dinv` proceeds *via* `thm:ckappa` rather than by inducting on `≡`.  The single proof
that gains a case is **`thm:ckappa`** (`unique.tex:243`).

*Second, that one case is not merely hard — it is unsatisfiable, by index arithmetic.*  Write
`k` for the index a candidate instantiation rule concludes at and `j` for the index of its
typing premise.

* **(R1) `thm:utype`'s application case forces `j = k`.**  The `app` rule hands it
  `Γ ⊢ₙ e₂ : A` and an induction hypothesis at index `n`, and its conclusion must be at index
  `n`.  There is no lower-index typing of `e₂` to be had.
* **(R2) `thm:ckappa` forces `j ≤ k−1`.**  `≡ᵏ` is defined (`unique.tex:240`) with the side
  condition `Γ ⊢ e₁,e₂ : α`, which under the §3 convention (`unique.tex:64`) is a `⊢ₖ₋₁`
  typing.  So every conversion derivable at index `k` must relate `⊢ₖ₋₁`-typeable terms.  With
  the substituted term typed at index `j = k`, `e[a]` is in general only `⊢ₖ`-typeable.

`j = k` and `j ≤ k−1` are contradictory.  **No indexing of an instantiation rule satisfies
both**, and that argument does not mention the rule's *depth*, its premise shape, or whether
it instantiates one variable or a whole context morphism.  It kills the depth-0 rule, the
general-depth `Ctx.InstN` rule, and the explicit-substitution / context-morphism formulation
named as "the missing machinery" — all of them, for the same reason.

**Both halves are machine-checked**, at `k = 1`:

* (R1) holds: with the rule, `SubstC` is `fun h H => .instC h H`.
* (R2) fails: `[] ⊢₁ .app (.lam A (.bvar 0)) a ≡ a` becomes derivable
  (`.instC aa_hasType1 hBB'`), while `SubstCRefute.lhs_not_hasType0` — landed, sorry-free —
  proves that term is not `⊢₀`-typeable **in any context**.  So `thm:ckappa` at index 1 has a
  conversion with no `≡ᵏ` chain, and `thm:1dinv` loses its analysis route for exactly the new
  rule.

*And the side condition cannot simply be relaxed to `⊢ₖ`.*  `↝ᵏ`'s `K⁺` rule and `≡ₚ`'s
reflexivity and proof-irrelevance rules all carry `⊢ₙ` typing premises; moving them to `⊢ₙ₊₁`
makes a conversion at `n+1` depend on typings at `n+1`, which is precisely the circularity the
index exists to break.

**Verdict: do not build.**  The candidate does not repair the obstruction, it relocates it —
and the relocation is now demonstrated rather than suspected.

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
`Prop`, which does not follow (settled, §11.1), and the reference's own `typesys.tex:50`
configuration is a counterexample to the lemma the bullet is proving.  §11.2 supplies the
repair — a `K⁺` rule for `Prop`-quotients, the reference's own device for subsingleton
eliminators — so §§3–4 is repairable rather than dead, and the site's re-derivation is a
known quantity rather than an open one.  It still needs unique typing afterwards, which is
what sinks *this* candidate.

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

## State of play: every candidate has now failed its own row-zero check

| candidate | row-zero check | outcome |
|---|---|---|
| 1. instantiation as a rule | does `thm:ckappa` absorb the new case? | **no** — `j = k` (R1) contradicts `j ≤ k−1` (R2); both halves machine-checked. Kills the whole family, general-depth and context-morphism forms included |
| 2. another stratification | is there a measure? | **no** — height gives `≤` not `<`; the reference offers no alternative; the tension is generic to the family |
| 3. de-stratify | how many uses of unique typing? | **three** — two reduce, `unique.tex:180` does not, and is additionally broken as written |
| 4. `sort_not_proof` from the model | which statement can a model reach? | **it works**, but it is an input to candidate 3, not a route by itself |

So the alternation-index route is closed at three independent points, and the repair family
for the first point is closed by arithmetic. **This is a third obstruction and it is reported
rather than worked around.**

What remains is a genuine choice between two things, and neither is an increment:

* **Abandon the alternation index.** Candidate 3 is the only survivor in outline, and its
  single blocker is `unique.tex:180`. Worth noting that the blocker has moved since it was
  withdrawn: `reference-gap-thm-utype.md` §11.2's `K⁺` repair changes that site's rule set, so
  whether the repaired site still needs full `uniq` — rather than a typing side condition — is
  **open and unchecked**. That is the one thread worth pulling before anything larger.
* **A different metatheory** — algorithmic conversion plus a logical relation, which breaks
  the typing/conversion circle without an alternation count at all. Large, standard in the
  literature, and outside anything `~/lean-type-theory` provides.

Candidate 4 is worth doing under either, and is small.

## What the checks cost, and what they bought

Four row-zero checks, three of which changed a funding decision and none of which cost more
than a session. The last one — this one — was flagged as unpriced from the first round and
was the only thing between the plan and a build; running it before the expensive context
machinery is what kept that machinery from being written into an obstructed development.

---

## After the `:180` thread and candidate 4: the obstruction reduces to one statement

Two checks were run after the table above. Both landed, and together they replace "three
independent closure points" with something much sharper.

### The repaired `:180` site does **not** need unique typing

*Reading result about a **repaired** rule set — two steps from anything machine-checked, and
the lowest-confidence item in this document. Labelled accordingly.*

The original bullet's `uniq` was in service of the invalid `β : P` step (`reference-gap-thm-utype.md`
§11.1). With the quotient `K⁺` rule (§11.2), the case is discharged by a different route that
needs no unique typing at all:

* `e₁ = lift α₁ R₁ β₁ f₁ h₁ q₁ ≫ᵏ f₁' a₃'`, taking the reconstructed parameter `b := a₃`.
  The reference's own inductive `K⁺` explicitly permits this: `unique.tex:154` says
  "the `≡ₚ` hypothesis in the `ι` rule allows some freedom of choice of the parameters `b`".
* Its side conditions are a *typing* (`Γ ⊢ₙ mk_{R₁} a₃ : Quot R₁`, from `a₃ : α₃` and
  `α₁ ≡ α₃` by conversion) and a `≡` judgment (`mk_{R₁} a₃ ≡ q₁`, from `q₁ ≡ₚ mk_{R₃} a₃` plus
  congruence) — exactly the form `unique.tex:107` already uses for the inductive `K⁺`.
* Then `f₁' a₃' ≡ₚ f₃' a₃'` by application congruence, from the induction hypothesis on
  `f₁ ≡ₚ f₃`.

So the one site that needed `uniq` on an *arbitrary* subject is eliminated. Of the three,
`:266` needs only `DefInv` clause (1) (`DefInv.sort_proofIrrel`, machine-checked), and `:272`
plus clause (3)'s `proofIrrel` case need **"a sort is not a proof" and its Π analogue**.

### Candidate 4 is blocked, and by the same fact the cumulativity check predicted

`Theory/SetModel/` is parameterised throughout on `(L : LevelAssign env nv)` — `InterpSound.lean`
carries it in every section — and **nothing in the directory constructs one**. `LevelAssign`'s
`srt_sound` field *is* `SortUniq` restated; `Interp.lean`'s own `srt_uniq` docstring says so.

So "get `sort_not_proof` from the model" presupposes a `LevelAssign`, which presupposes
`SortUniq`, which the cumulativity check shows **no model can supply**. The two findings are
the same fact seen from either end. The escape hatch, if anyone wants it: `LevelAssign` exists
to decide proof-splitting (`IsProp`/`IsProof` are defined from `L.lvl`/`L.srt`); a model with a
proof-splitting criterion that does not require a canonical level per term would not need it.
That is a question for the model stream, not this one.

### Where that leaves everything

**One statement now carries the whole route: "a sort is not a proof" (and its Π analogue).**

* *Syntactically*, unstratified, it needs `uniq` — `SortUniq.lean` derives it that way — and
  the self-reference has no decreasing measure (`reference-gap-thm-utype.md` §9a).
* *Semantically*, it needs the model, which is parameterised on `SortUniq`.
* *At the stratified index* it is the induction hypothesis — which is what the index is
  **for**, and the index is broken by the substitution gap that no rule repairs.

That is a better handover than "closed at three points": it is one named statement, with three
known routes to it and a specific reason each is blocked. Anyone resuming should attack that
statement, not the route.
