# `thm:gg_compat`'s quotient case, and a counterexample to `thm:ckappa`

**Status: DRAFT. Not sent to anyone.** See the last line of this file.

*Re: Mario Carneiro, "The Type Theory of Lean", `unique.tex`, Lemma (Compatibility of `≫_κ`
with `≡_p`), `\label{thm:gg_compat}` at `unique.tex:167`, and Theorem (Completeness of the
`κ` reduction), `\label{thm:ckappa}` at `unique.tex:242`.*

---

## 0. Summary

`thm:gg_compat`'s **`lift` bullet** (`unique.tex:180`) discharges its case by asserting that
the eliminated type is a proposition:

> If `lift R₁ β₁ f₁ h₁ q₁ ≡_p lift R₃ β₃ f₃ h₃ (mk_R a₃)` where `q₁ ≡_p mk_R a₃` by proof
> irrelevance, then **`β : P` so `e₁ : β` is a proof**. (Note: we are using that `⊢ₙ` has
> unique typing here.)

That inference is the one that works for the *recursor* bullet immediately below it, where
"the major premise is a proof" forces "`P` is a small eliminator" forces "the motive lands in
`Prop`". **It does not transfer to `lift`.** `q₁ : α/R` being a proof forces only `α : P`;
`lift`'s target universe `v` is an independent parameter of the constant
(`axioms.tex:227`: `lift_R : ∀β:U_v. ∀f:α→β. … → α/R → β`), so `α : P` and `β : U_1` are
simultaneously legal. `typesys.tex:50` is where this configuration is described — as a source
of non-transitivity of *algorithmic* equality — and it is exactly the configuration the
`lift` bullet excludes by assertion.

§2 gives the counterexample to `thm:gg_compat` and §3 propagates it to a counterexample to
`thm:ckappa` itself: there is a `Γ`, and terms `e`, `e'`, with `Γ ⊢ e ≡ e'` and
`Γ ⊬ e ≡_κ e'`.

§4 gives a repair, which is `K⁺` (`unique.tex:103`) transposed to the quotient: a rule
`(K_q)` firing at an arbitrary major premise, with an `inv` operator that **is definable**
for a `Prop` carrier, and definable for the same reason `K⁺`'s `inv_i` are (`unique.tex:109`).
With `(K_q)` added, the `lift` bullet goes through by the *other* argument — the one the `K⁺`
bullet uses — and `thm:ckappa` is restored.

**What this does not touch.** `thm:unique` (unique typing) is not claimed false: `thm:1dinv`
uses `thm:ckappa` only at `U_ℓ ≡ U_ℓ'`, `∀ ≡ ∀` and `U_ℓ ≢ ∀`, and this counterexample does
not obviously reach those three instances. The claim here is that the *proof* of `thm:ckappa`
has a false step and that `thm:ckappa` as stated is false; whether `thm:1dinv`'s three
instances survive is a separate question this note does not settle. Nothing here is a claim
about the Lean kernel: the kernel implements `⇔`, which `typesys.tex:50` already records as
non-transitive on exactly this input.

---

## 1. Setting

Take a context with

```
α : P        R : α → α → P        β : U_1
f : α → β    H : ∀ x y : α. R x y → f x = f y
q : α/R      a : α
```

All of these are legal. `α/R : U_u` for `α : U_u` (`axioms.tex:222`), so `α : P` gives
`α/R : P`; `lift_R`'s `β` is at an unrelated `U_v` (`axioms.tex:227`).

Because `α/R : P`, `q` and `mk_R a` are two proofs of the same proposition, so proof
irrelevance relates them. Because `β : U_1`, nothing of type `β` is a proof.

**[measured]** In Lean 4 (v4.33.0-rc2, kernel-checked `theorem`s) with
`α : Prop, R : α → α → Prop, β : Type, f : α → β, H, q : Quot R, a : α`:

| statement | `rfl` |
|---|---|
| `q = Quot.mk R a` | **accepted** (proof irrelevance) |
| `Quot.lift f H (Quot.mk R a) = f a` | **accepted** (`ι_q`) |
| `Quot.lift f H q = f a` | **rejected** |

The first two are the two halves of the `≡` derivation of §2; the third is the
`⇔`-non-transitivity `typesys.tex:50` predicts.

---

## 2. The counterexample to `thm:gg_compat`

`thm:gg_compat` claims: if `Γ ⊢ e₁ ≡_p e₃ ≫_κ e₂`, then there is `e₄` with
`Γ ⊢ e₁ ≫_κ e₄ ≡_p e₂`.

Instantiate

```
e₁ = lift_R β f H q
e₃ = lift_R β f H (mk_R a)
e₂ = f a
```

* `e₁ ≡_p e₃`: by the `≡_p` compatibility rules for application, four times, with reflexivity
  at `lift_R`, `β`, `f`, `H`, and **proof irrelevance** at the last argument
  (`q, mk_R a : α/R : P`).
* `e₃ ≫_κ e₂`: the `ι_q` rule (`unique.tex:145`), with `f ≫_κ f` and `a ≫_κ a`.

Now enumerate the `e₄` with `e₁ ≫_κ e₄`. `e₁`'s head is `lift_R` and its last argument is the
variable `q`, so no substantive rule applies: `β` is not the `ι_q` redex shape (that needs a
syntactic `mk_R`), there is no `β`/`δ`/`ζ` redex, and `K⁺` is stated for **SS inductives**
(`unique.tex:103`) while `α/R` is a primitive, not an inductive. So every `e₄` is
`lift_R β' f' H' q` obtained by the compatibility rules, with `β ≫_κ β'` etc. and the last
argument unchanged (a variable parallel-reduces only to itself).

Finally, `lift_R β' f' H' q ≡_p f a` is underivable:

* *reflexivity*: the terms are distinct.
* *compatibility (application)*: it would need `lift_R β' f' H' ≡_p f`, and `f` is a variable
  while the left side is an application; the application-compatibility rule cannot relate
  them, and no other rule has an application on the left and a variable on the right.
* *the two `η` rules*: each requires a `λ` on one side. Neither side is a `λ`.
  (`unique.tex:117` notes `≡_p`'s `η` "is tightly syntax-constrained … it does not apply at
  all on proving that two variables of function type are equivalent".)
* *proof irrelevance*: it requires both sides to inhabit a proposition. By unique typing at
  `⊢ₙ` (which `sec:kappa` assumes) both sides have type `β : U_1`, and `U_1 ≢ P` by
  definitional inversion at `⊢ₙ`, exactly as the same step is made in `thm:1dinv`.

So no `e₄` exists, and `thm:gg_compat` fails at this instance. The step of its proof that
fails is the assertion "`β : P`" in the `lift` bullet.

**Why the recursor bullet is not affected.** For `rec_P C₁ e₁ p₁ h₁` with `h₁` a proof, `P`'s
being a *non-SS* inductive means the eliminator is small, so the motive `C` lands in `Prop`
and the whole application is a proof. That inference chains "the major premise's type is a
`Prop`" to "the result type is a `Prop`" through the small-elimination restriction. `lift`
has no such restriction; SS eliminators do not either, which is precisely why `K⁺` exists for
them and why the recursor bullet is stated only for the non-SS case.

---

## 3. The counterexample to `thm:ckappa`

`Γ ⊢ e ≡_κ e'` is defined (`unique.tex:240`) as: `Γ ⊢ e, e' : α` for some `α`, and there are
`e₁', e₂'` with `e ↝*_κ e₁' ≡_p e₂' ↜*_κ e'`.

Take `e := lift_R β f H q` and `e' := f a`.

* `Γ ⊢ e ≡ e'` holds: proof irrelevance gives `Γ ⊢ q ≡ mk_R a`, congruence gives
  `Γ ⊢ e ≡ lift_R β f H (mk_R a)`, the `ι_q` computation rule (`axioms.tex:228`) gives
  `Γ ⊢ lift_R β f H (mk_R a) ≡ f a`, and transitivity composes them.
* `Γ ⊢ e ≡_κ e'` fails: as in §2, `e`'s `↝*_κ` reducts are `lift_R β' f' H' q`, `e'`'s are
  `f' a'` (a variable head, so only the arguments move), and no pair of these is `≡_p`-related,
  by the same four-case enumeration.

So `thm:ckappa`'s forward direction is false. In the proof, the case that breaks is the first
bullet — "the equivalence relation rules are immediate since `≡_κ` is an equivalence relation
(by the Church-Rosser property)". Transitivity of `≡_κ` is derived from `thm:church_rosser`,
whose proof (step (2), `unique.tex:230`) applies `thm:gg_compat` to commute a `≡_p` past a
`≫_κ`. That is the application §2 refutes.

The shape of the counterexample is exactly `typesys.tex:50`'s: the derivation of `≡` needs a
"creative" step — replacing the normal `q` by the non-normal `mk_R a` — and `≡_κ`, which
reduces first and compares afterwards, cannot make it.

---

## 4. The repair: `(K_q)`

`K⁺` (`unique.tex:103`) exists to make exactly this creative step unnecessary for SS
inductives, by letting the eliminator fire at an *arbitrary* major premise with the fields
recovered by `inv`. The same rule works for the quotient:

```
(K_q)   α : P     Γ ⊢ mk_R inv_R[q] : α/R
        ─────────────────────────────────────
        Γ ⊢ lift_R β f H q ↝_κ f inv_R[q]
```

`inv_R : α/R → α` is definable, and for the same reason `unique.tex:109`'s `inv_i` are: when
`α : P`, **every** `f : α → β` satisfies `lift`'s soundness hypothesis automatically, because
any two inhabitants of `α` are definitionally equal. So

```
inv_R := lift_R α (λx:α. x) (λx y _. refl) : α/R → α
```

is well-typed. **[measured]** In Lean 4:

```lean
def qinv {α : Prop} {R : α → α → Prop} (q : Quot R) : α := Quot.lift id (fun _ _ _ => rfl) q
theorem Q1 (α : Prop) (R : α → α → Prop) (q : Quot R) (a : α) : qinv q = a := rfl        -- accepted
theorem Q2 (α : Prop) (R) (β : Type) (f : α → β) (q) (a) : f (qinv q) = f a := rfl        -- accepted
```

Both are accepted (kernel-checked). As with `K⁺`'s `inv_i`, it does not matter whether
`inv_R[q]` itself reduces: it is a proof, and proofs are pushed into `≡_p`.

With `(K_q)` in `↝_κ` (and correspondingly in `≫_κ`, and with `ι_q` restricted to the
`α : P` complement, mirroring `unique.tex:101`'s restriction of `ι` to non-SS inductives):

* **`thm:gg_compat`'s `lift` bullet** goes through by the `K⁺` bullet's argument instead of
  the false one: `e₁ = lift_R β f H q ≫_κ f' inv_R[q]`, and
  `f' inv_R[q] ≡_p f a` because `f ≡_p f` and `inv_R[q] ≡_p a` by proof irrelevance
  (`inv_R[q], a : α : P`).
* **§3's counterexample to `thm:ckappa`** dissolves: `e ↝_κ f inv_R[q]` and
  `f inv_R[q] ≡_p f a = e'`.
* **Regularity** (`unique.tex:120`, item 1) holds for `(K_q)`: `q ≡ mk_R inv_R[q]` by proof
  irrelevance, then `ι_q`.

The one structural observation worth recording is that `K⁺` and `(K_q)` are the *same* rule at
two rule shapes: "when the major premise's type is a proposition, fire on any major premise,
with a canonical form supplied by proof irrelevance". Stating the rule once, indexed by the
rule table rather than by "SS inductive", covers both and cannot miss a third case.
`Lean4Lean/Theory/Typing/KRule.lean` in this repository states it that way.

---

## 5. Machine-checked vs. read

**[measured]** — the six `rfl` probes of §1 and §4, run under Lean 4 v4.33.0-rc2 as
kernel-checked `theorem`s.

**[read]** — every quotation from `unique.tex`, `axioms.tex` and `typesys.tex`, at the line
numbers given, from the working copy at `~/lean-type-theory`.

**[analysis]** — §2's enumeration of `≫_κ` reducts and of `≡_p` derivations, §3's propagation,
and §4's repair. These are hand arguments over the rules as printed; they are *not*
machine-checked, because `unique.tex`'s `≡_p` and `↝_κ` are not formalised in this repository
(this repository's `NormalEq`/`ParRed` are analogues, not transcriptions). The `≡_p`
enumeration in §2 is the load-bearing one: it is a four-case check against the rule list at
`unique.tex:111–117`.

---

**This document has not been sent to anyone and must not be.** It is a draft prepared inside
this repository, exactly as `docs/upstream-report-thm1dinv.md` is. Whether, when and to whom
it is submitted is the repository owner's decision alone.
