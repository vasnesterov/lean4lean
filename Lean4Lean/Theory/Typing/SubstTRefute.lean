import Lean4Lean.Theory.Typing.SubstCRefute

/-!
# `SubstT` is false: substitution does not preserve the index for *typings* either

`Theory/Typing/SubstCRefute.lean` refutes `SubstC` — index-preserving substitution into a
**conversion** — which is the step `unique.tex:51` takes in `thm:utype`'s application case.

This file refutes the companion statement for **typings**:

    SubstT env U n :
      Γ₀ ⊢ₙ e₀ : A₀  →  Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ  →  Γ₁ ⊢ₙ e : B  →  Γ ⊢ₙ e[e₀]ₖ : B[e₀]ₖ

**Why this one matters separately.**  `unique.tex` §§3–4 (κ-reduction and Church–Rosser)
substitutes at a fixed index in at least three places, and *none* of them is `SubstC`:

* `item:p_subst` (`unique.tex:126`) — substituting into `≡ₚ`, whose `proofIrrel` rule
  (`unique.tex:118`) carries three **typing** premises at `⊢ₙ`;
* `item:gg_subst` (`unique.tex:162`) — substituting into `≫ᵏ`, whose `K⁺` rule
  (`unique.tex:150`) carries the **typing** side condition `Γ ⊢ intro inv[p,h] : α` at `⊢ₙ`;
* `thm:ckappa`'s β case (`unique.tex:251`) — `≡ᵏ`'s own side condition (`unique.tex:240`) is
  `Γ ⊢ e₁,e₂ : α` at `⊢ₙ`, and for `Stratified.beta` the right-hand side is `e.inst e'`,
  whose `⊢ₙ` typing has to be *manufactured* from the rule's two premises.

Each of these needs substitution into a **typing** at a preserved index, not into a
conversion.  So the refutation of `SubstC` does not settle them, and the question "does the
§§3–4 development survive the substitution obstruction?" is exactly the question of `SubstT`.

**It does not.**  `SubstT` is false at `n = 1` over the empty environment.

## The witness

Everything is `SubstCRefute`'s, plus one move: put the redex in the **context**.

    p := .param 0        a := .sort (max p p)        A := .sort (succ p)
    C := (fun _ : A => #0) #0          -- `SubstCRefute`'s `B`, in context `[A]`

`C` is a *bona fide type*: `[A] ⊢₀ C : A` and `A` is a sort (`C_type`), so `C :: [A]` is a
well-formed context and this is not a junk-context artifact.

In that context the variable `#0 : C.lift` can be retyped by `SubstCRefute.hBB'`, weakened:

    [C, A] ⊢₀ #0 : C.lift      and      [C, A] ⊢₁ C.lift ≡ #1
    ⟹  [C, A] ⊢₁ #0 : #1                                            (`hvar`)

Now substitute `a` for the `A`-variable (`Ctx.InstN … 1 …`, i.e. under one binder).  The
context becomes `[C.inst a] = [lhs]` and `SubstT` would give

    [lhs] ⊢₁ #0 : a

But `#0`'s only `Lookup` type there is `lhs`, so this needs `[lhs] ⊢₁ lhs ≡ a` — and
`SubstCRefute.stuck` says `lhs` is `⊢₁`-related to nothing but itself.

**This is the hypothesis `SubstCRefute` explicitly declined to supply.**  Its note says the
counterexample does not exhibit "a single term carrying both types"; a *context variable*
carries both, for free, because `Lookup` gives one and `conv` gives the other.  The context
entry is well-typed, so nothing is smuggled in.

## What this settles, stated narrowly

**Refuted, machine-checked:** index-preserving substitution into a `⊢ₙ` typing, by a
`⊢ₙ`-typed term, at `n = 1` (`substT_false`).  Hence the three §§3–4 sites above cannot be
had at the index by *any* argument, not merely not by the reference's "easy induction".

**Not refuted, and not claimed:** the fragment `Stratified.instN` reaches (`m = 0`, the
substituted term's typing conversion-free) is untouched and remains true; so is the general
`instN` bound `m + n`.  What is refuted is only the *preserved-index* statement, `m = n`.
-/

namespace Lean4Lean
namespace VEnv

/-- **Substitution at a preserved index, for typings.**  The typing analogue of `SubstC`,
and what `unique.tex` §§3–4 needs at `item:p_subst`, `item:gg_subst` and `thm:ckappa`'s β
case.  `Stratified.instN` proves it with the conclusion at `m + n`; this is the `m = n`
instance the reference's fixed-index development requires. -/
def SubstT (env : VEnv) (U n : Nat) : Prop :=
  ∀ {Γ₀ Γ₁ Γ : List VExpr} {e₀ A₀ e B : VExpr} {k : Nat},
    env.HasTypeN U n Γ₀ e₀ A₀ → Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ →
    env.HasTypeN U n Γ₁ e B →
    env.HasTypeN U n Γ (e.inst e₀ k) (B.inst e₀ k)

/-- `SubstT` at the base index: `⊢₀` typings have no conversions to break. -/
theorem SubstT.zero (henv : Ordered env) : env.SubstT U 0 := fun h₀ W H => by
  have := Stratified.instN henv h₀ W H; rwa [Nat.zero_add] at this

namespace SubstTRefute

open VExpr SubstCRefute

/-- The context entry: `SubstCRefute`'s redex, used as a *type*. -/
def C : VExpr := .app (.lam A (.bvar 0)) (.bvar 0)

/-- **`C` is a genuine type**, so `C :: [A]` is a well-formed context — the refutation does
not turn on a junk context.  Note the index: `⊢₀`, no conversion at all. -/
theorem C_type : (∅ : VEnv).HasTypeN 1 0 [A] C A :=
  .app (.lam (.sort (by exact p_wf)) (.bvar .zero)) (.bvar .zero)

/-- And `A` is a sort, which is what "`C` is a valid context entry" means. -/
theorem A_type {Γ : List VExpr} : (∅ : VEnv).HasTypeN 1 0 Γ A (.sort (.succ (.succ p))) :=
  .sort (by exact p_wf)

/-- **The typing the substitution destroys.**  `#0`'s `Lookup` type is `C.lift`, and
`SubstCRefute.hBB'` weakened retypes it as `#1` — a `⊢₁` conversion whose two `beta`
premises are at `⊢₀`. -/
theorem hvar : (∅ : VEnv).HasTypeN 1 1 [C, A] (.bvar 0) (.bvar 1) :=
  .conv (hBB'.weak .empty) (.bvar .zero)

/-- The substituted context is `[lhs]`. -/
theorem C_inst : C.inst a = lhs := rfl

theorem lhs_lift : lhs.lift = lhs := rfl

theorem a_ne_lhs : a ≠ lhs := by simp [a, lhs]

/-- **`SubstT` is false at `n = 1`.**  Hence `unique.tex` §§3–4's three fixed-index
substitution steps — `item:p_subst`, `item:gg_subst`, and `≡ᵏ`'s side condition in
`thm:ckappa`'s β case — are not merely unproved but unavailable. -/
theorem substT_false : ¬ (∅ : VEnv).SubstT 1 1 := by
  intro hs
  have h : (∅ : VEnv).HasTypeN 1 1 [lhs] (.bvar 0) a :=
    hs (Γ₀ := []) (e₀ := a) (A₀ := A) (k := 1) a_hasType1 (.succ .zero) hvar
  have ⟨T, hl, hc⟩ := HasTypeN.bvar_inv h
  cases hl
  exact a_ne_lhs ((stuck hc rfl rfl).1 lhs_lift)

/-! ## Appendix: `thm:ckappa`'s base case is false as stated

Independent of everything above, and found while checking §§3–4's index bookkeeping.

`unique.tex:240` defines `Γ ⊢ e₁ ≡ᵏ e₂` to require **`Γ ⊢ e₁,e₂ : α` for some `α`** — one
type for both, at `⊢ₙ` under the §3 convention (`unique.tex:64`).  `unique.tex:285` then
starts the outer induction with

> For `n=0`, `⊢₀` has definitional inversion by `thm:0dinv`, and `thm:ckappa` is trivial
> (where both `Γ ⊢ e ≡ᵏ e'` and `Γ ⊢ e ≡ e'` mean `e = e'`).

The parenthetical is **wrong**: under the convention `Γ ⊢ e ≡ e'` is `⊢ₙ₊₁ = ⊢₁`, not `⊢₀`,
and `⊢₁` is strictly larger than syntactic equality — `sortDF` relates `.sort ℓ` and
`.sort ℓ'` whenever `ℓ ≈ ℓ'`, with no typing premise at all.  Meanwhile `⊢₀` typing *is*
syntactically unique, so two equivalent-but-unequal sorts have **no common `⊢₀` type** and
the `≡ᵏ` side condition cannot be met.

So `thm:ckappa` at `n = 0` is false, and the outer induction (`unique.tex:283`) has no base
case.  `unique.tex:252` uses `thm:ckappa` at `n` to prove it at `n+1`, so this is load-
bearing rather than cosmetic.

This is a *third* defect in the reference, alongside `docs/reference-gap-thm-utype.md`'s two.
It is plausibly repairable — drop "for some `α`" to two independent typings — but that
weakening is exactly the side condition the handoff's (R2) arithmetic rests on, so the repair
has to be re-priced, not assumed. -/

/-- `.sort (max p p)` and `.sort p` are `⊢₁`-convertible… -/
theorem sorts_defEq1 : (∅ : VEnv).IsDefEqN 1 1 [] a (.sort p) :=
  .sortDF (by exact ⟨p_wf, p_wf⟩) (by exact p_wf) (by simp [VLevel.equiv_def, VLevel.eval])

/-- …and have no common `⊢₀` type, because `⊢₀` typing is syntactically unique.  Hence
`≡ᵏ`'s side condition (`unique.tex:240`) fails on them and `thm:ckappa` at `n = 0`
(`unique.tex:285`) is false. -/
theorem sorts_no_common_hasType0 :
    ¬ ∃ α, (∅ : VEnv).HasTypeN 1 0 [] a α ∧ (∅ : VEnv).HasTypeN 1 0 [] (.sort p) α := by
  rintro ⟨α, h1, h2⟩
  have e1 := IsDefEqN.zero_iff.1 (HasTypeN.sort_inv h1).2
  have e2 := IsDefEqN.zero_iff.1 (HasTypeN.sort_inv h2).2
  rw [← e2] at e1
  injection e1 with e1; injection e1 with e1; injection e1

end SubstTRefute
end VEnv
end Lean4Lean
