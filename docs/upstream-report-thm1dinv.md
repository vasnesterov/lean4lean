# A counterexample to `thm:1dinv`, clause (2)

**Status: DRAFT. Not sent to anyone.** See the last line of this file.

*Re: Mario Carneiro, "The Type Theory of Lean", `unique.tex`, Theorem (Definitional
inversion), `\label{thm:1dinv}` at `unique.tex:258`.*

---

## 0. Summary

Clause (2) of the definitional-inversion property (`unique.tex:33`) is false as stated, at
`n + 1 = 1`, over a signature with no constants, no inductive types and no quotients. The
counterexample is two ∀-congruences composed by transitivity, and can be checked by hand in a
few minutes; §2 gives it in full.

Since `thm:0dinv` gives definitional inversion at `n = 0` and clause (2) fails at `n = 1`, the
first step of the induction that closes `thm:unique` (`unique.tex:283–286`) does not go
through.

The mechanism is **context transport, not confluence**: the ∀-congruence rule
(`axioms.tex:37`) places its codomain premise in the context of the *left* domain, and a
derivation of `Γ ⊢ ∀x:α.β ≡ ∀x:α'.β'` can compose two ∀-congruences whose codomain premises
live in `Γ,x:α` and `Γ,x:α'` respectively. Clause (2) then asks for the codomain conversion
in `Γ,x:α`, and `⊢ₙ` is not invariant under moving a conversion from `Γ,x:α'` to `Γ,x:α`,
because the bridging conversion `Γ ⊢ₙ α ≡ α'` is unavailable to the *typing* judgment one
index down, where all of `⊢ₙ`'s typing premises sit.

**What this does not touch** (stated up front, because it is easy to over-read): the same
codomain pair *does* convert one index up, at `n = 2`; `thm:unique` itself is untouched; and
nothing here is a statement about Lean's type theory or about the kernel. `thm:utype`'s
*statement* also survives — it is conditional on definitional inversion, and its hypothesis is
now known false at that instance, so it is vacuously true there. §3 says this precisely.

Everything in §2 is machine-checked in Lean 4, sorry-free, with `#print axioms` reporting
`[propext, Quot.sound]` on every declaration. §6 separates what is machine-checked from what
is read off the source.

---

## 1. The claim

`unique.tex:29–35` defines: `⊢ₙ` has *definitional inversion* if

1. `Γ ⊢ₙ U_ℓ ≡ U_ℓ'` implies `ℓ ≡ ℓ'`;
2. `Γ ⊢ₙ ∀x:α.β ≡ ∀x:α'.β'` implies `Γ ⊢ₙ α ≡ α'` **and `Γ, x:α ⊢ₙ β ≡ β'`**;
3. `Γ ⊢ₙ U_ℓ ≢ ∀x:α.β`.

`thm:1dinv` (`unique.tex:258`, proof at `:261–278`) asserts this for every `⊢ₙ₊₁`.

**Claim.** Clause (2) is false at `n + 1 = 1`. Concretely, there are a level `p`, terms and a
context (the empty one) with

    ⊢₁ ∀x:U_{max(p,p)}. x  ≡  ∀x:U_p. (λy:U_p. y) x            derivable
    x : U_{max(p,p)} ⊢₁ x  ≡  (λy:U_p. y) x                    NOT derivable

so `thm:1dinv` fails at its first instance, and with it the step `⊢₀ ⟹ ⊢₁` of
`unique.tex:283–286`. The signature is empty: no constants, no inductives, no quotients, so
every δ-, ι-, quotient- and `K⁺`-rule is vacuous and the whole counterexample lives in the
pure fragment of `axioms.tex:6–8`.

Clauses (1) and (3) are **not** touched by this witness — it never relates a universe to a
non-universe. See §5.

---

## 2. The counterexample, in full

Fix one universe variable `p`. Write

    A  := U_{max(p,p)}          A' := U_p
    R  := (λ y : U_p. y) x      (the identity at U_p, applied to the ∀-bound variable x)

Two facts about levels, both from `axioms.tex:43–51` and both purely algorithmic (not merely
semantic):

* `max(p,p) ≡ p`: `max(p,p) ≤ p` by `:51` from `p ≤ p` twice (`:46` with `n = 0`), and
  `p ≤ max(p,p)` by `:49` from `p ≤ p`. So `A` and `A'` are convertible types.
* `max(p,p) ≠ p` **syntactically**. This is the entire engine of the counterexample.

### 2.1 The positive half: `⊢₁ ∀x:A. x ≡ ∀x:A'. R`

Recall `⊢₁ e ≡ e'` means: derivable by the rules of `axioms.tex:30–40`, with every *typing*
premise discharged at `⊢₀`, i.e. by a conversion-free typing derivation (`unique.tex:13`).
Three steps: two ∀-congruences, composed by `trans`.

**Step 1.** `⊢₁ ∀x:A. x ≡ ∀x:A'. x`, by ∀-congruence (`axioms.tex:37`) from

* `⊢₁ A ≡ A'` — the universe congruence rule `axioms.tex:34`, whose only premise is
  `max(p,p) ≡ p`. (Note that `:34` is stated in the *empty* context, and that is exactly
  where it is used here; no weakening of it is needed.)
* `x : A ⊢₁ x ≡ x` — reflexivity `axioms.tex:31`, whose premise is `x : A ⊢₀ x : A`. That
  premise holds by the variable rule (`axioms.tex:14`) from `⊢ A : U_{S max(p,p)}`
  (`axioms.tex:15`), with no conversion anywhere, hence at `⊢₀`.

**Step 2.** `⊢₁ ∀x:A'. x ≡ ∀x:A'. R`, by ∀-congruence from

* `⊢₁ A' ≡ A'` — reflexivity, premise `⊢₀ A' : U_{S p}` (`axioms.tex:15`).
* `x : A' ⊢₁ x ≡ (λ y:U_p. y) x` — symmetry of one β step (`axioms.tex:38`) in the context
  `x : A'`. The β rule's two premises are
  `x:A', y:U_p ⊢₀ y : U_p` and `x:A' ⊢₀ x : U_p`, both instances of the variable rule, both
  conversion-free. Its conclusion is
  `x:A' ⊢ (λ y:U_p. y) x ≡ y[x/y] = x`.

**Step 3.** `trans` (`axioms.tex:33`) of Steps 1 and 2 gives

    ⊢₁ ∀x:A. x ≡ ∀x:A'. (λ y:U_p. y) x.

Note that both Π-types are genuinely well-formed types —
`⊢ ∀x:A. x : U_{imax(S max(p,p), max(p,p))}` and `⊢ ∀x:A'. R : U_{imax(Sp, p)}` (machine-checked
at `⊢₁`; by inspection neither derivation uses the conversion rule, so both hold at `⊢₀`) — and
both contexts `x:A` and `x:A'` are `ok`. The counterexample does not turn on junk.

### 2.2 The negative half: `x : A ⊬₁ x ≡ (λ y:U_p. y) x`

Clause (2), applied to Step 3 with `α = A`, returns the codomain conversion in the **left**
domain's context, `x : A`. It is not derivable.

**The one fact that does all the work.** In the context `x : A`, the term `R` is not
`⊢₀`-typeable *at any type*.

> *Proof.* Suppose `x:A ⊢₀ R : T`. Inverting the application rule, the function
> `λ y:U_p. y` has a `⊢₀` type `∀y:C. D` and the argument `x` has `⊢₀` type `C`. Inverting the
> λ rule, `∀y:U_p. U_p` and `∀y:C. D` must be `⊢₀`-equal, i.e. *syntactically* equal
> (`unique.tex:12`), so `C = U_p`. Hence `x:A ⊢₀ x : U_p`. But `⊢₀` typing is syntactically
> unique — `⊢₀` admits no conversion rule at all, the variable rule types `x` only at its
> declared type, and weakening cannot retype it — so the only `⊢₀` type of `x` in `x:A` is
> `A = U_{max(p,p)}`, and `max(p,p) ≠ p` syntactically. Contradiction. ∎

**Consequently `⊢₁` relates `R` to nothing but itself in `x:A`.** By induction on the
derivation of `x:A ⊢₁ X ≡ Y` (in fact, for *any* context `Γ` in which `Γ ⊬₀ x : U_p`, which is
what makes the induction go through under the two context-extending congruences):

| rule (`axioms.tex`) | why `R` is stuck |
|---|---|
| refl `:31` | relates `R` only to `R` |
| symm `:32`, trans `:33` | recursive, in the *same* context — IH applies directly |
| universe congr. `:34`, constant congr. | wrong head shape (`R` is an application, `x` a variable) |
| λ-congr., ∀-congr. `:36–37` | wrong head shape; their IHs (which would need the context hypothesis in an *extended* context) are never reached |
| app congr. `:35` | its premises require both sides `⊢₀`-typed: the function at some `∀y:C.D` and the argument at `C`, which forces `Γ ⊢₀ x : U_p` |
| β `:38`, `R` as redex | the β premises again force `Γ ⊢₀ x : U_p` |
| β `:38`, `R` as contractum | then `R = e[e'/y]` with `Γ,y:α ⊢₀ e : β` and `Γ ⊢₀ e' : α`, and the substitution lemma gives `Γ ⊢₀ R : β[e'/y]` — contradicting the fact above |
| η `:39` | `R` is not a λ, so it can only be η's right-hand side, which requires `Γ ⊢₀ R : ∀y:α.β` |
| proof irrelevance `:40` | requires both sides `⊢₀`-typed |
| δ / ι / quotient / `K⁺` | vacuous: the signature is empty |

So `x:A ⊢₁ x ≡ R` is underivable, and clause (2) is false at `n + 1 = 1`. ∎

### 2.3 The same pair, one context to the right, and one index up

Two contrasts that locate the failure precisely.

* `x : A' ⊢₁ x ≡ R` **is** derivable — it is Step 2's second premise. So the failure is not
  about the terms; it is about which of the two domains names the context.
* `x : A ⊢₂ x ≡ R` **is** derivable. At index 2 the typing premises are taken at `⊢₁`, where
  the conversion `A ≡ A'` is available to the conversion rule, so `x:A ⊢₁ x : U_p` and the β
  step goes through in `x:A` after all. So the failure is a failure of a property *at a fixed
  alternation index* — which is, unfortunately, exactly the form the induction consumes.

---

## 3. Scope

Three registers, which we think must not be conflated. We state all three because we have
seen each of them mis-read.

1. **Our own stratified proxy is false.** The formalised predicate corresponding to the
   definition at `unique.tex:29–35` is refuted at index 1 over the empty environment. That is
   a statement about our development.

2. **`thm:1dinv` is false as stated, at `n + 1 = 1`.** §4 is our argument that this is a claim
   about the paper's rule set and not about our encoding.

   `thm:utype` (`unique.tex:40`) is **not** refuted by this. It is *conditional* — "If `⊢ₙ` has
   definitional inversion, and …" — and at `n = 1` over the empty signature its hypothesis is
   now known false, so the theorem is *vacuously true* at that instance. What fails is the
   supply of that hypothesis, i.e. `thm:1dinv` and the induction at `unique.tex:283–286`.

3. **Lean's actual type theory is not affected, and neither is `thm:unique`.** We know of no
   reason to doubt unique typing for Lean, and there is positive evidence the other way in
   this very witness: the conversion that clause (2) asks for *does* hold at `n = 2` (§2.3).
   What is refuted is an *indexed* approximation, at a fixed index. No kernel behaviour, no
   soundness claim, and no statement of `thm:unique` is in question here. We would be grateful
   if any onward description of this preserved that distinction.

---

## 4. Fidelity: is this the paper's clause (2), or an artifact of our encoding?

This is the section we would want to read first if we received this note, so we have tried to
make it easy to attack.

### 4.1 Rule-by-rule correspondence

| rule | `axioms.tex` | our transcription |
|---|---|---|
| ∀-congruence | `:37` — premises `Γ ⊢ α ≡ α'` and `Γ,x:α ⊢ β ≡ β'`; **no typing premises**; codomain premise in the **left** domain's context | identical |
| universe congruence | `:34` — sole premise `ℓ ≡ ℓ'` | identical, plus level well-formedness side conditions (satisfied here) |
| β | `:38` — premises `Γ,x:α ⊢ e : β` and `Γ ⊢ e' : α` | identical |
| reflexivity | `:31` — **typed**: premise `Γ ⊢ e : α` | ours is *unconditional* — the one deviation; see 4.3 |
| symm, trans | `:32`, `:33` | identical |
| app congruence, η, proof irrelevance | `:35`, `:39`, `:40` | identical |
| weakening | a rule of the typing judgment (`:13`); no weakening rule for `≡` | admissible and proved in our de Bruijn presentation |
| the index | `unique.tex:12–14` | identical: `⊢₀ ≡` is syntactic equality; a conversion at `n+1` takes its typing premises at `n`; congruence premises stay at `n+1` |
| clause (2) | `unique.tex:33` | identical, same context |

The two load-bearing features of the paper's ∀-congruence are exactly the two the
counterexample uses: it carries **no typing premises** (so the two Π-types need not be shown
well-typed for the rule to fire, though here they are anyway), and it puts the codomain
premise in the **left** domain's context (so `trans` can chain two of them across two
different contexts).

### 4.2 Direction of the discrepancies

Where our system differs from the paper's, it differs by being *larger*: reflexivity is
unconditional, and our universe congruence is available in any context rather than only the
empty one. Both differences make our `⊢₁` a superset of the paper's, which is the harmless
direction for the **negative** half — if the larger relation does not relate `x` and `R` in
`x:A`, the smaller one does not either.

The **positive** half is where a superset would be a problem, and that is 4.3.

### 4.3 The rebuild — please read this one

Our *first* version of this witness used reflexivity on a body that is **not** `⊢₀`-typeable
in the left context. That version depended on our unconditional-reflexivity deviation and was
therefore a statement about our encoding, not about the paper. We rebuilt it.

In the witness above, both uses of reflexivity are backed by conversion-free typings that the
paper's *typed* reflexivity rule accepts:

* Step 1's codomain premise: `x : A ⊢₀ x : A` (variable rule);
* Step 2's domain premise: `⊢₀ U_p : U_{S p}` (universe rule).

And the β step's two premises are the paper's two premises, both instances of the variable
rule. So every step of §2.1 is available under `axioms.tex` as written, with no appeal to the
deviation.

(There is a second, independent argument that the deviation is harmless — the paper's own
basics (2) asserts `⊢ₘ ⊆ ⊢ₙ` for `m ≤ n`, and `⊢₀ α ≡ β` is *unconditional* syntactic equality
by `unique.tex:12`, so the paper's `⊢₁` contains unconditional reflexivity anyway. The witness
does not rely on this.)

### 4.4 Two smaller checks

* **Level equality.** `max(p,p) ≡ p` is derivable in the paper's *algorithmic* level judgment
  (`axioms.tex:43–51`), not only under the semantic reading — the derivation is in §2.
* **Weakening of `≡`.** `axioms.tex:30–40` gives no weakening rule for the conversion
  judgment. If one were added it would not affect the negative half: `R` mentions the
  innermost variable, so it is not the weakening of a conversion in a shorter context.

### 4.5 Where the published proof appears to go wrong

*This paragraph is our reading of `unique.tex:268–272`, not a machine-checked claim.*

The proof of clause (2) applies `thm:ckappa` to obtain

    ∀x:α.β ↝*_κ ∀x:α₁.β₁  ≡_p  ∀x:α'₁.β'₁ *↜_κ ∀x:α'.β'

and then says "if these are `≡_p` equivalent using the compatibility rule then we are done"
(`unique.tex:270`).
Three contexts appear here and they are not the same one: the `≡_p` compatibility premise for
`∀` lands `β₁ ≡_p β'₁` in `Γ, x:α₁`; the right-hand reduction lives under `α'`; and the
conclusion is wanted in `Γ, x:α`. Additionally `≡_κ` requires both endpoints to be `⊢ₙ`-typed
*in the conclusion's context*, which is precisely what fails in §2.2. The step that is missing
is a **context-conversion** principle at a preserved index:

    Γ ⊢ₙ α ≡ α'      Γ, x:α' ⊢ₙ e ≡ e'
    ----------------------------------
            Γ, x:α ⊢ₙ e ≡ e'

and §2 shows this principle is *false at `n = 1`* — which is why the gap is not merely a
missing justification. In the unstratified system context conversion is a standard admissible
rule; the point is that the usual proof of its admissibility routes through the conversion
rule of the typing judgment, and so it **costs an index**. §2.3's `n = 2` derivation is
exactly that cost being paid.

---

## 5. What we think the repair might be

*Speculation, offered tentatively. We have not proved any of this, and we are not in a
position to know which repair fits the rest of the development.*

* **Clauses (1) and (3) look unaffected.** This witness never relates a universe to a
  non-universe, so it says nothing about them; and their conclusions carry no context at all,
  so the transport step of §4.5 does not arise for them. Our own reading of the confluence
  requirement for (1) and (3) is unchanged by this finding. (We have separately machine-checked
  one small piece of them: proof irrelevance can never relate a universe, a Π, or a λ to
  anything, in any environment and any context, because at `⊢₀` such a term's type has the
  shape `U_{Sℓ}`, `U_{imax(ℓ₁,ℓ₂)}` or `∀x:α.β`, none of which is itself `⊢₀`-typed at `P`.
  That discharges the proof-irrelevance case of (1) and (3) for free; the `trans` case, i.e.
  the confluence argument, remains.)

* **Two obvious weakenings of clause (2) do not work.** Concluding in the right domain's
  context, `Γ, x:α' ⊢ₙ β ≡ β'`, is refuted by the same witness read symmetrically. Concluding
  at `n + 1` rather than `n` is not refuted (§2.3 is a proof of it at this instance) but is a
  *weaker* conclusion, and at least in our reading `thm:utype`'s application case cannot
  absorb the index slack.

* **The repair we would try first** is to add the context-conversion rule of §4.5 as a
  primitive rule of `≡` — a rule whose premises sit at `n+1`, so it does not disturb the
  stratification, and which we expect is admissible in the *unstratified* system, hence
  changes nothing about `≡` itself. The obligation this creates is to check that admissibility
  in the presence of η and proof irrelevance, which we have not done. With such a rule the
  counterexample dies immediately, and the three-context step in `thm:1dinv`'s proof of
  clause (2) becomes an appeal to an actual rule.

* **One caution about `thm:utype`.** Repairing clause (2) is necessary but, on our reading, not
  sufficient for the proof of `thm:utype` as written: its application case (`unique.tex:51`)
  additionally needs `Γ ⊢ₙ β[e₂/x] ≡ β'[e₂/x]` from `Γ, x:α ⊢ₙ β ≡ β'`, i.e. closure of `⊢ₙ`
  under substitution by a `⊢ₙ`-typed term at a preserved index. We have a separate
  machine-checked counterexample to *that* inference at `n = 1`, which we have kept out of this
  note because it is a different theorem and a different mechanism. We mention it only so that
  "repair clause (2) and `thm:utype` goes through" is not read into the paragraph above. We are
  happy to write that one up too if it would be useful.

---

## 6. What is machine-checked, and what is read off the source

All Lean declarations are in one file, `Lean4Lean/Theory/Typing/DefInvRefute.lean`, sorry-free,
each verified with `#print axioms` to depend on `[propext, Quot.sound]` only. In our notation
`IsDefEqN env U n Γ a b` is `Γ ⊢ₙ a ≡ b` and `HasTypeN env U n Γ e A` is `Γ ⊢ₙ e : A`, over
the empty environment (`∅`: no constants, no `defeqs`) with one universe parameter. All names
below are in the namespace `Lean4Lean.VEnv.DefInvRefute`, and the file's identifiers map to
this note's as `dom = A`, `dom' = A'`, `cod = R`, `.bvar 0 = x`, `piL = ∀x:A. x`,
`piR = ∀x:A'. R`. Terms are de Bruijn, so `cod = .app (.lam dom' (.bvar 0)) (.bvar 0)` is the
*identity* at `U_p` applied to the ∀-bound variable, as in §2.

**Machine-checked.**

| name | statement |
|---|---|
| `hpi` | `⊢₁ ∀x:A. x ≡ ∀x:A'. R` — §2.1 |
| `hdom` | `⊢₁ A ≡ A'`, one universe-congruence step |
| `step1_codomain_typed0` | `x:A ⊢₀ x : A` — Step 1's reflexivity premise is typed (§4.3) |
| `dom'_type` | `⊢₀ A' : U_{Sp}` — Step 2's reflexivity premise is typed (§4.3) |
| `bvar_conv_cod_right` | `x:A' ⊢₁ x ≡ R` — Step 2's codomain premise, one β |
| `bvar_not_hasType0_left` | `x:A ⊬₀ x : U_p` |
| `cod_not_hasType0` | `R` is `⊢₀`-untypeable in any `Γ` with `Γ ⊬₀ x : U_p` — §2.2's key fact |
| `stuck` | `⊢₁` relates `R` to nothing but itself in any such `Γ` — §2.2's table |
| `bvar_not_conv_cod` | `x:A ⊬₁ x ≡ R` — the negative half |
| `defInv_one_false` | **clause (2) fails at `n+1 = 1`** |
| `defInv_one_witness` | the same as an explicit `∃` over `Γ, α, β, α', β'` |
| `defInv_forallE_right_false` | the right-domain reading of clause (2) fails too |
| `defInv_step_zero_false` | `¬ (definitional inversion at 0 → at 1)` — `thm:1dinv` at its first instance, with `DefInv.zero` = `thm:0dinv` proved separately |
| `cod_conv_bvar_succ` | `x:A ⊢₂ x ≡ R` — §2.3, the index is what fails |
| `thm_utype_one_vacuous` | `thm:utype` at this instance, vacuously — §3, register 2 |
| `env_ordered`, `dom_type`, `dom'_type`, `piL_type`, `piR_type` | the environment, both contexts and both Π-types are well-formed |
| `sort_not_proof0`, `forallE_not_proof0`, `lam_not_proof0` | proof irrelevance cannot relate a universe, a Π or a λ — §5, any environment, any context |

**Read off the source, not machine-checked.** The correspondence table of §4.1; the derivation
of `max(p,p) ≡ p` in the algorithmic level judgment, §2 (the Lean side uses the semantic level
equality, and the algorithmic derivation is the hand check that they agree here); the
weakening remark in §4.4; the diagnosis in §4.5; everything in §5.

**Where the two might come apart, and how to check.** The single point of contact is §4.1: if
our `Stratified` inductive is a faithful presentation of `axioms.tex:30–40` under the index of
`unique.tex:12–14`, then the machine-checked facts are facts about the paper. The whole of §2
is written so that this does not have to be taken on trust — it is checkable on paper without
running anything.

---

## 7. If any of this is wrong

We would much rather be corrected than be right. The likeliest failure modes, in the order we
would check them: (a) we have mis-transcribed the ∀-congruence rule's context — §4.1; (b) the
paper's reflexivity rule is doing work we have quietly weakened — §4.3, which is why the
witness was rebuilt; (c) `⊢₀` typing is not as rigid as §2.2 claims — this rests on `⊢₀`
having no conversion rule, `unique.tex:12–14`; (d) we have mis-read the definition of the
index. Any of these would dissolve the claim, and we would want to know.

---

*This document has not been sent to anyone; it is a draft held in this repository for its
author to review.*
