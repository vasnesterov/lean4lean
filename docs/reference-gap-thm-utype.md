# A gap in `unique.tex`'s proof of `thm:utype`

**Status: machine-checked.** Every claim below marked "refuted" or "proved" is a sorry-free
Lean declaration in this repository, depending on no axioms beyond `propext` and `Quot.sound`.
Names and locations are in §10.

**Read §4 before quoting §1.** The distinction between "the proof is invalid" and "the theorem
is false" is load-bearing here, and only the first is established.

---

## 1. The claim, in one paragraph

Carneiro, *The Type Theory of Lean*, proves unique typing (`unique.tex`, `thm:unique`) by an
induction on an alternation index `⊢ₙ`. The inductive step `thm:utype` (`unique.tex:40–53`)
uses, in its application case, the inference

> from `Γ,x:α ⊢ₙ β ≡ β'` and `Γ ⊢ₙ e₂ : α`, conclude `Γ ⊢ₙ β[e₂/x] ≡ β'[e₂/x]`
> — `unique.tex:51`

**That inference is false.** It fails at `n = 1`, over the *empty* environment, and the
counterexample is machine-checked. Consequently the published proof of `thm:utype` is invalid,
and with it the induction `DefInv n → uniq n → DefInv (n+1)` on which `thm:unique` rests: the
induction reaches `DefInv 1` and stops.

What is **not** claimed: that `thm:utype` is false, or that `thm:unique` is false, or that
definitional inversion fails. See §4.

---

## 2. Background: what the index is and why substitution is the pressure point

`unique.tex:10–15` defines, by induction on `n`:

* `Γ ⊢₀ α ≡ β` iff `α = β`;
* `Γ ⊢ₙ₊₁ α ≡ β` iff `Γ ⊢ α ≡ β` is derivable using only `Γ ⊢ₙ e : α` typing judgments;
* `Γ ⊢ₙ e : α` iff `Γ ⊢ e : α` is derivable with every appeal to the conversion rule using
  `Γ ⊢ₘ α ≡ β` for some `m ≤ n`.

The index counts *alternations between the two judgments*, and it is a condition on
**derivations**. That is what breaks the circularity between typing and conversion, and it is
also why substitution is dangerous: substituting a derivation into a derivation composes their
alternation counts.

Writing `T(m,n)` for the index of the derivation obtained by substituting a `⊢ₘ` typing
derivation into a `⊢ₙ` derivation: a conversion appeal at level `k` inside the target has its
own typing subderivations at level `k−1`, which after substitution sit at `T(m,k−1)`, so that
conversion is now at `T(m,k−1)+1`. Hence

    T(m,0) = m        T(m,k+1) = T(m,k) + 1        so  T(m,n) = m + n.

`m + n` is exactly the index proved by this repository's substitution lemma
(`Stratified.instN`), and it collapses to `n` precisely when `m = 0`. In `thm:utype`'s
application case `m = n` — both derivations come from the same `⊢ₙ` derivation — so the
reference's step would land at `2n` where its consumer needs `n`. `DefInv` is antitone in
clause (1) and neither monotone nor antitone in clause (2), so a conclusion at `2n` cannot be
repaired downstream.

The counting argument located the failure; it did not establish it. §3 does.

The wall was also localised mechanically before the counterexample existed: an attempt to
prove `Stratified.instN` with the index *preserved* compiles for every rule except the four
whose typing premises drop an index — `appDF`, `beta`, `eta`, `proofIrrel` — where the
available `Γ ⊢ₙ₊₁ e₀ : A₀` cannot be lowered to the `Γ ⊢ₙ e₀ : A₀` the premise wants.

---

## 3. The counterexample

Everything lives in the **empty environment** — no constants, no `defeqs` — with one universe
parameter `p`. Nothing about any declaration is used.

```
a   := .sort (max p p)                    A  := .sort (succ p)
B   := .app (.lam A (.bvar 0)) (.bvar 0)  B' := .bvar 0
```

**Hypothesis 1: `[] ⊢₁ a : A`.** The `sort` rule gives `⊢₀ a : .sort (succ (max p p))`; one
`sortDF` step converts the type, since `succ (max p p) ≡ succ p`. One conversion, so index 1.

**`a` is not `⊢₀`-typeable at `A`.** At index 0 conversion *is* syntactic equality
(`unique.tex:12`), and `max p p ≠ p` as level expressions. This is the whole engine of the
counterexample.

**Hypothesis 2: `[A] ⊢₁ B ≡ B'`.** One `β` step, `(λy:A. y) x ≡ x` with `x` the context
variable. Its two typing premises are variable rules, both at index 0.

**Instantiating at `a`:** `B[a] = .app (.lam A (.bvar 0)) a` and `B'[a] = a`.

**Conclusion, which `unique.tex:51` asserts and which fails:**

    [] ⊢₁ .app (.lam A (.bvar 0)) a  ≡  a        is not derivable.

---

## 4. Scope — what is and is not refuted

This section is the point of the document.

**Refuted, machine-checked:**

* the inference at `unique.tex:51`, at `n = 1` (`SubstCRefute.substC_false`). Hence *the
  published proof of `thm:utype` is invalid.*
* the instantiated strengthening of `DefInv`'s clause (2) — see §7.

**Not refuted, and not claimed:**

* **`thm:utype`'s statement.** Its application case carries hypotheses this instance does not
  supply: a single term `e₁` carrying *both* Π types, and an argument typed at *both* domains.
  The theorem may well be true by a different argument. What is gone is the proof.
* **`thm:unique`.** It is the theorem `thm:utype` feeds; nothing here bears on its truth.
* **`DefInv` in the reference's literal form** (`unique.tex:33`: "then `Γ ⊢ₙ α ≡ α'` and
  `Γ,x:α ⊢ₙ β ≡ β'`", with no instantiation). This instance *satisfies* it — the body
  conversion `[A] ⊢₁ B ≡ B'` is exactly what a `forallEDF` premise looks like. Definitional
  inversion is untouched.
* **The case `n = 0`.** There the inference is a theorem (substituting into a syntactic
  equality), so `thm:utype` at index 0 is unconditional.

A reader who takes "the proof is invalid" for "the theorem is false" will draw the wrong
conclusion, and will also mis-scope the repair: the repair is owed to the *proof*.

---

## 5. Why the underivability argument is fifteen lines and not a confluence argument

Proving a *negative* about an inductively defined conversion relation normally requires
normalisation or confluence, because `trans` admits an arbitrary middle term. Here it does not,
because of one fact:

> **`.app (.lam A (.bvar 0)) a` is not `⊢₀`-typeable, at any type, in any context.**

Typing it needs `a` at the lam's *annotated* domain `A`, and `a`'s unique `⊢₀` type is
`.sort (succ (max p p))`. (Uniqueness of `⊢₀` types is itself available: it is `thm:utype` at
index 0, which is unconditional — §4.)

That single fact discharges every rule of `⊢₁` at once:

| rule | why it cannot relate the term to anything else |
|---|---|
| `rfl` | relates it only to itself — the conclusion we want |
| `symm`, `trans` | recursive; handled by stating the invariant in both directions |
| `sortDF`, `constDF`, `lamDF`, `forallEDF` | wrong shape: the term is an application |
| `appDF` | its premises type both sides at index 0 — and would type this term |
| `β`, left side | its premise is `Γ ⊢₀ e' : α`, i.e. exactly `⊢₀ a : A` |
| `β`, right side | see below |
| `η` | left side must be a `λ`; right side is a premise `Γ ⊢₀ e : ∀…` |
| `proofIrrel` | both sides are typing premises at index 0 |
| `extra` (δ/ι/quot rules) | the environment has none |

The one case where the term is not itself a premise is **`β`'s right side**: the contractum
`e[e'/x]` could *be* our term for some decomposition. It closes in one line, from β's own
premises: `Γ,x:α ⊢₀ e : β` and `Γ ⊢₀ e' : α` instantiate — by the substitution lemma at
`m = 0`, the one case where the index *is* preserved — to `Γ ⊢₀ e[e'/x] : β[e'/x]`, a `⊢₀`
typing of the contractum. Contradiction.

So the term is `⊢₁`-related to nothing but itself, while `a` is a different term.

---

## 6. Transfer: this is about the specification, not about our port

The refutation is carried out against this repository's `VEnv.Stratified`, a transcription of
the reference's judgments. Checked rule by rule against `axioms.tex:30–41`:

| reference rule | typing premises? | transcription |
|---|---|---|
| β (`axioms.tex:38`) | **yes** — `Γ,x:α ⊢ e : β` and `Γ ⊢ e' : α` | `Stratified.beta`, same two |
| η (`:38`) | yes — `Γ ⊢ e : ∀y:α.β` | `Stratified.eta`, same |
| application congruence (`:35`) | yes — via the `:41` abbreviation `Γ⊢e≡e':α  ≡  Γ⊢e≡e' ∧ Γ⊢e:α ∧ Γ⊢e':α` | `Stratified.appDF`, same |
| proof irrelevance (`:40`) | yes — three | `Stratified.proofIrrel`, same |
| universe congruence (`:34`) | **no** | `Stratified.sortDF`, plus level-`WF` side conditions |
| λ / ∀ congruences (`:36–37`) | no | `lamDF` / `forallEDF`, same |

The two rules the counterexample *needs* to be premise-free (`sortDF`, to retype `a`; and the
congruences, to see that no repair exists) are premise-free in the reference, and the four it
needs to carry index-0 typing premises do carry them. Under `unique.tex:13` those premises sit
at `⊢₀` when the conversion is at `⊢₁`.

Two further fidelity checks:

* **Level equivalence.** `max p p ≡ p` is derivable in the reference's *algorithmic* level
  judgment (`axioms.tex:44–46`: one `max`-introduction and one `max`-elimination rule), not
  only under the semantic reading. So the counterexample does not lean on this repo's
  semantic `≈`.
* **Our one deviation runs the safe way.** This tree's reflexivity rule is unconditional where
  the reference's (`axioms.tex:31`) requires `Γ ⊢ e : α`. That makes `⊢₁` here a *superset* of
  the reference's, so an underivability result holds *a fortiori* for the reference. And
  neither hypothesis of the counterexample uses `rfl`, so both are derivable in the
  reference's system as well. The reference's variable and weakening rules carry extra typing
  premises that ours omit; those too only shrink the relation, and the two premises the
  counterexample needs (`Γ ⊢ A : U_ℓ` for `A` a sort) are conversion-free.

This is the check that decides whether a discrepancy is mathematics or a port artifact. Here it
runs toward the specification.

---

## 7. The second casualty: the obvious repair to `DefInv`

Before the counterexample existed, the natural repair was to strengthen `DefInv`'s clause (2)
to conclude the *instantiated* form —

> if `Γ ⊢ₙ ∀x:α.β ≡ ∀x:α'.β'` and `Γ ⊢ₙ a : α` then `Γ ⊢ₙ β[a] ≡ β'[a]`

— which is exactly what `thm:utype`'s application case consumes, and which would have kept
`DefInv` as the single hypothesis. **It is false**, refuted by the same instance
(`SubstCRefute.defInv_forallE_inst_false`): `forallEDF` carries no typing premises, so the
counterexample's body conversion lifts to a Π-conversion for free, and the strengthened clause
then hands back precisely the judgment shown underivable.

Note where this cuts. The reference's literal clause (2) is the *premise* of that `forallEDF`
step, so it is satisfied here (§4). The refutation separates the reference's clause from its
instantiated strengthening, and only the strengthening dies.

---

## 8. The discriminating insight: a congruence-based repair cannot reach this

Anyone scoping a fix will try the congruence route first. It does not work, and the reason is
worth stating because the *first* counterexample attempted here was not a counterexample.

That attempt put the mismatch in a **binder annotation**: an `η` pair
`λx:α. y x ≡ y` where `a`'s conversion made the annotation `α` disagree with `a`'s real domain.
It failed to be a counterexample, because the conversion that retypes `a` is itself available
at index 1, and `lamDF` and `sortDF` — **both premise-free** — push it into the annotation:

    λx:S. y x  ≡(lamDF, sortDF)  λx:S₂. y x  ≡(η, with y's genuine ⊢₀ type)  y

So the mismatch was repaired by congruence and the derivation went through at index 1.

Putting the mismatch **under an application** is what makes it stick. Changing an annotation
inside an application requires `appDF`, and `appDF` demands the very index-0 typing of the
argument that is missing — the same premise that blocks `β`. There is no premise-free rule
that reaches inside an application.

**Consequence for a repair:** any fix that works by making conversions congruent, or by adding
congruence-shaped rules, will close the annotation case and leave the application case exactly
as it is. The failing case is not a congruence failure.

---

## 9. Where this leaves the route

* `SubstC 0` holds, so the reference's induction reaches `DefInv 1`. Then it needs `uniq 1`,
  and `SubstC 1` is false. **The induction cannot pass `n = 1`.**
* What survives untouched is the *destination*: `Injectivity.lean`'s two open sort goals,
  `IsDefEqU.sort_inv` and `IsDefEqU.sort_forallE_inv`, follow from `∀ n, DefInv env U n` alone
  — by `IsDefEqU.stratifyN` and clause (1) or (3). Neither reduction uses `uniq` and neither
  uses the refuted inference.
* So the open question is not "can `thm:utype` be repaired" but "**is there another route to
  `∀ n, DefInv`**". §9a answers it: no cheap one.

---

## 9a. Checked: `DefInv` does not yield to a direct argument

Since `DefInv` survives the refutation and is what the two open goals actually need, the next
question is whether it can be proved *directly*, by induction on the conversion derivation,
with no appeal to `uniq`. Attempted, all three clauses. Every case closes except:

| clause | open case | what it wants |
|---|---|---|
| (1), (2), (3) | `trans` | `.sort u ≡ₙ e ≡ₙ .sort v` with `e` arbitrary — normalisation |
| (1), (2), (3) | `proofIrrel` | see below |
| (2) only | `symm` | the IH lands `B ≡ B'` in context `A'::Γ`, the goal is `A::Γ` — context conversion at a preserved index |

The `extra` case — the one that has repeatedly looked like the obstacle — closes mechanically
from `DeclRules.lean`'s `instL_lhs_ne_sort` / `instL_lhs_ne_forallE`, as it does unstratified.

**One genuine improvement from the index.** Unstratified, `Injectivity.lean`'s `proofIrrel`
case needs `VEnv.SortUniq`: universe uniqueness for an *arbitrary* subject, strictly stronger
than clause (1). At the index it needs only **clause (1) itself**, on a different instance,
and does not even use the `Γ ⊢ₙ p : .sort .zero` premise — invert the two `sort` typings with
`HasTypeN.sort_inv`, compose, apply clause (1) (`DefInv.sort_proofIrrel`, machine-checked).

**Why that still does not close it.** The instance it recurses on is not smaller: the built
derivation has height `max(h₂,h₃) + O(1)` against the `proofIrrel` node's `max(h₁,h₂,h₃) + 1`,
so the obvious well-founded measure gives `≤`, not `<`. A derivation-height index — the
cheap-looking repair, with precedent in `Strong.lean`'s `HasTypeStratified` — does not rescue
it.

**Why `trans` cannot even be deferred.** It cannot be stated as a residual hypothesis without
new machinery. Any formulation avoiding a reduction relation — e.g. "`Γ ⊢ₙ .sort u ≡ e` and
`Γ ⊢ₙ e ≡ .sort v` give `u ≈ v`" — is *equivalent to clause (1) itself*, by `trans`. Naming
what is actually missing requires "`e` reduces to a sort", i.e. the κ-reduction of
`unique.tex` §3. And the sort really can be convertible to a non-sort: `β` relates a sort to a
redex whose contractum is that sort, so no shape invariant works without reduction.

**Conclusion for scoping.** There is no route to `∀ n, DefInv` that avoids the §§3–4
reduction/confluence development — and that development is where the same substitution
obstruction was located at two further sites (`item:p_subst` at `unique.tex:126`, whose `≡ₚ`
reflexivity rule carries a `⊢ₙ` typing premise; `item:gg_subst` at `:162`, whose `K⁺` side
condition `unique.tex:107` states outright is "a collection of `≡` judgments at `⊢ₙ`"). Both
are called easy inductions in the reference, and both are proved there by *inversion*, where
adding a substitution rule makes things worse rather than better.

So the choice is between the structural change (explicit substitutions, or context morphisms
`Γ ⊢ₙ σ : Γ'` as judgment formers, so substitution is a rule carrying its own index rather
than an operation on finished derivations) and abandoning the alternation index for a
different circularity-breaker. Nothing cheaper was found.

---

## 11. A second apparent gap, at `unique.tex:180` — **analysis, not machine-checked**

Found while checking whether `thm:gg_compat`'s use of unique typing could be discharged
independently. **Flagged at a lower confidence than everything above**: `≡ₚ` and `≫ᵏ` are not
formalised in this tree, so this is a reading result with a worked configuration, not a Lean
proof. It should be re-checked before it is relied on.

**The bullet.** `unique.tex:180`, inside `thm:gg_compat` (`:169`, "if `Γ ⊢ e₁ ≡ₚ e₃ ≫ᵏ e₂`
then there exists `e₄` with `Γ ⊢ e₁ ≫ᵏ e₄ ≡ₚ e₂`"):

> If `lift R₁ β₁ f₁ h₁ q₁ ≡ₚ lift R₃ β₃ f₃ h₃ (mk_R a₃)` where `q₁ ≡ₚ mk_R a₃` by proof
> irrelevance, then `β : P` so `e₁ : β` is a proof. (Note: we are using that `⊢ₙ` has unique
> typing here.)

**Where unique typing is used**, and it is the full form: `q₁` inhabits both `Quot R₁` and a
`Prop` `p`, and `uniq` reconciles them, giving `Quot R₁ : Prop`. The subject `q₁` is an
arbitrary term, so no inversion applies — this is not the "a sort is not a proof" family.

**The step that does not follow.** From `Quot R₁ : Prop` one gets that the quotient's *source*
`α` is a `Prop`. The bullet needs the *output* type `β₁` to be a `Prop`, and it does not
follow: `Quot.lift {α : Sort u} {r} {β : Sort v}` leaves `u` and `v` independent — checked
against `~/lean4/src/Init/Prelude.lean:443`, and against this repo's own spec, where
`Theory/Quot.lean`'s `quotLiftConst` is `type_of% @Quot.lift` with no added constraint. A
`Prop`-quotient may be eliminated into a `Type`.

**A configuration where the lemma fails** — and it is the reference's own, from two chapters
earlier. `typesys.tex:50` constructs exactly this to demonstrate non-transitivity: `p : P`,
`R : p → p → P`, `α : U₁`, `f : p → α`, `H`, `q : p/R`, `h : p`. Take `q` and `f` to be
variables. Then

* `lift R α f H q ≡ₚ lift R α f H (mk_R h)` — by the `lift` compatibility rule, with the
  last component by proof irrelevance, since `p/R : P` is a `Prop`;
* `lift R α f H (mk_R h) ≫ᵏ f h` — by the `ι_q` rule;
* but `lift R α f H q` reduces only componentwise, because `≫ᵏ`'s `ι_q` rule requires a
  syntactic `mk_R`, and `q` is a variable; and no `≡ₚ` rule relates a `lift` spine to `f h` —
  the heads differ, neither side is a `λ` so neither `η` rule applies, and proof irrelevance
  would need `α : P`, which it is not.

So no `e₄` exists, and `thm:gg_compat` — the compatibility lemma at the centre of the
Church–Rosser proof — fails on it.

**Scope, again.** This says the *bullet's argument* is wrong and that the *lemma as stated*
appears false for `Prop`-quotients with large elimination. It does not say Church–Rosser is
false; the lemma may be repairable by restricting `≡ₚ`'s `lift` compatibility rule, or by
handling the case as the reference handles other proof-irrelevance collisions. Nothing here
is machine-checked.

**Why it matters for planning.** `:180` was the third of the three sites where §§3–4 needs
unique typing, and the one that decided between two candidate repairs
(`docs/options-circularity-breakers.md`). It cannot be discharged as written, because as
written it does not go through.

---

## 10. The machine-checked artifacts

All in `Lean4Lean/Theory/Typing/`, all sorry-free, axioms `propext` and `Quot.sound` only.

| name | file | statement |
|---|---|---|
| `VEnv.SubstC` | `UniqueTypingN.lean` | the inference at `unique.tex:51`, as a predicate |
| `VEnv.SubstC.zero` | `UniqueTypingN.lean` | it holds at `n = 0` |
| `VEnv.SubstC.of_hasTypeN_zero` | `UniqueTypingN.lean` | it holds when the substituted term's typing is conversion-free — the `m = 0` fragment, and the whole of the true part |
| `SubstCRefute.a_not_hasType0` | `SubstCRefute.lean` | `a` is not `⊢₀`-typeable at `A` |
| `SubstCRefute.lhs_not_hasType0` | `SubstCRefute.lean` | the contractum is `⊢₀`-untypeable in any context |
| `SubstCRefute.stuck` | `SubstCRefute.lean` | `⊢₁` relates it to nothing but itself (the 15-line induction) |
| `SubstCRefute.substC_false` | `SubstCRefute.lean` | **`¬ SubstC ∅ 1 1`** |
| `SubstCRefute.defInv_forallE_inst_false` | `SubstCRefute.lean` | the strengthened clause (2) is false |
| `VEnv.Stratified.uniq` | `UniqueTypingN.lean` | `thm:utype` from `DefInv` + `SubstC`; content only at `n = 0` |
| `VEnv.HasTypeN.uniq_zero` | `UniqueTypingN.lean` | `thm:utype` at index 0, unconditional |
| `VEnv.IsDefEqU.sort_inv_of_defInv` | `UniqueTypingN.lean` | the target, reduced to `∀ n, DefInv` |
| `VEnv.DefInv.sort_proofIrrel` | `UniqueTypingN.lean` | §9a: at the index, `proofIrrel` needs only clause (1), not `SortUniq` |
