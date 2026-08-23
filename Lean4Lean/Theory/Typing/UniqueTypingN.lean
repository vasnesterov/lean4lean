import Lean4Lean.Theory.Typing.Stratified

/-!
# `thm:utype`: unique typing at the alternation index

`~/lean-type-theory/unique.tex:29–53`.  This file supplies:

* `VEnv.DefInv env U n` — "`⊢ₙ` has definitional inversion" (`unique.tex:29–35`), transcribed
  clause for clause;
* `VEnv.SubstC env U n` — "`⊢ₙ` conversions are closed under instantiation by `⊢ₙ`-typed
  terms".  **This is not in the reference; it is a step the reference takes without
  justification.**  See below;
* `VEnv.DefInv.zero` and `VEnv.SubstC.zero` — both hypotheses hold at `n = 0` (`thm:0dinv`),
  which is what keeps everything below from being vacuous;
* `VEnv.Stratified.uniq` — `thm:utype` (`unique.tex:40`), sorry-free from those two;
* `VEnv.IsDefEqU.sort_inv_of_defInv` — the reduction of `Theory/Typing/Injectivity.lean`'s
  open `sort_inv` to `∀ n, DefInv env U n`, which is the point of the whole route.

`Theory/Typing/Stratified.lean` supplies the index and the four "n-provability basics"; this
file is the first thing that uses them.

## The gap in `thm:utype`, and what `SubstC` is

`thm:utype`'s application case (`unique.tex:51`) ends "…so `Γ ⊢ₙ β[e₂/x] ≡ β'[e₂/x]`": it
substitutes into a conversion and keeps the index `n`.  Nothing justifies that step, and no
proof of it exists here.

`⊢ₙ` is defined by a condition on *derivations* (`unique.tex:14`), and the derivation
transformation raises the index.  Substituting a derivation of `Γ ⊢ₘ e₂ : α` into one of
`Γ,x:α ⊢ₙ β ≡ β'` splices `e₂`'s conversions *underneath* `β`'s, so the alternation counts
add: writing `T(m,n)` for the index of the substituted derivation, `T(m,0) = m` and
`T(m,k+1) = T(m,k)+1`, hence `T(m,n) = m+n`.  That is exactly the index `Stratified.instN`
proves.  In `thm:utype`'s application case `m = n` — both derivations come out of the same
`⊢ₙ` derivation — so the reference's step lands at `2n`, while its consumer `thm:1dinv` needs
it at `n`, feeding it straight back into definitional inversion *at `n`*.  `DefInv` is
neither monotone nor antitone in `n` (clause (1) is antitone, clause (2) is neither), so a
conclusion at `2n` cannot be repaired downstream.

The wall is machine-witnessed and sits exactly where the counting says: an attempt at
`Stratified.instN` with the index preserved goes through for *every* rule except the four
whose typing premises drop an index — `appDF`, `beta`, `eta`, `proofIrrel` — where the
available `Γ ⊢ₙ₊₁ e₀ : A₀` cannot be lowered to the `Γ ⊢ₙ e₀ : A₀` the premise wants.

To be exact about the claim: this shows the reference's *step* is unjustified, not that
index-preserving substitution is *false*.  No counterexample is exhibited — that would need a
concrete environment — so `SubstC` may well hold; it simply has no proof, and `thm:utype` may
not appeal to it without one.  So it is carried as an explicit hypothesis, named, rather than
absorbed into `DefInv` where it would be easy to miss.

**What is known about `SubstC`.**  It holds at `n = 0` (`SubstC.zero`).  It holds at every
`n` for terms whose typing derivation is conversion-free (`SubstC.of_hasTypeN_zero`, an
instance of `Stratified.instN` at `m = 0`), which is the only fragment `instN` reaches: the
`m + n` bound collapses to `n` exactly when `m = 0`.  The general case is open.

## The gap is not local to `thm:utype`

`unique.tex` §§3–4 substitutes at a fixed index twice more, and both are the same wall:

* `item:p_subst` (`unique.tex:126`) substitutes into `≡ₚ`, whose *reflexivity* rule
  (`unique.tex:113`) carries a typing premise `Γ ⊢ e : α` — a `⊢ₙ` typing, under the §3
  convention stated at `unique.tex:64`.  Substituting a `⊢ₙ`-typed term into it lands at
  `⊢₂ₙ`.  The reference's proof is "All parts are easy inductions."
* `item:gg_subst` (`unique.tex:162`) substitutes into `≫ᵏ`, whose `K⁺` rule carries
  `Γ ⊢ intro inv[p,h] : α` — and `unique.tex:107` says outright that this side condition
  "can also be written as a collection of `≡` judgments at `⊢ₙ`".

So the plan "restate §§3–4 over `IsDefEqN`" meets this obstruction at least three times, not
once.  Pricing that transcription without pricing this is optimistic.

## What would actually fix it, and why the obvious repair does not

Adding instantiation as a **rule** looks like the fix and is not one.  It works locally: put
it on the conversion half only (the typing half would break `thm:utype`'s primary induction,
whose subject would become an arbitrary substituted term), and then `SubstC` is immediate,
`IsDefEqN.zero_iff` survives (the rule maps a syntactic equality to a syntactic equality),
`mono` and `stratifyN` are unaffected, and instantiation at a preserved index becomes
provable for the typing half too — by induction on the typing derivation alone, since typing
rules never change the index and the one rule mentioning a conversion, `conv`, is discharged
by the new rule.  The depth-0 form is cheap and this was measured, not estimated: adding
`| instC : (Γ ⊢[n] a : A) → (A::Γ ⊢[n] e ≡ e') → Γ ⊢[n] e.inst a ≡ e'.inst a` to
`Stratified` costs exactly four cases — one line each in `mono` and `eq_of_zero`, and in
`weakN`/`instN` a two-line case apiece (`rw [VExpr.liftN_inst_hi, VExpr.liftN_inst_hi]` and
`rw [← VExpr.inst_inst_hi _ _ _ 0 k, ← VExpr.inst_inst_hi _ _ _ 0 k]`; `beta`'s one-sided `▸`
is *not* the template, since both sides of a conversion move).  With those, all five landed
lemmas of `Stratified.lean` stay sorry-free.  The general-depth form is the one §§3–4 would
need — `instT` under a binder requires it — and that one needs a `Ctx.InstN` premise plus
lift/instantiate commutation lemmas for *contexts* that this tree lacks.

But it does not survive downstream.  `thm:1dinv` proves definitional inversion by inducting
on `⊢ₙ₊₁ X ≡ Y` through `thm:ckappa`; a new instantiation rule is a new case, and closing it
needs `≡ᵏ` to be closed under instantiation by `⊢ₙ₊₁`-typed terms — while `≡ₚ`'s and `↝ᵏ`'s
typing side conditions are at `⊢ₙ`.  Pushing the rule down into `≡ₚ` and `↝ᵏ` in turn is
worse: `thm:gg_compat` and `thm:tri` are proved by *inversion* on those relations, and a
substitution rule gives them a case whose subject is an arbitrary substituted term — the same
shape of failure, one level down.

**The missing machinery, stated precisely.**  What is needed is a stratification with both
of:

1. a conversion derivation at level `n+1` uses only typings at level `≤ n` — this is what
   breaks the circularity and is the entire point of the index; and
2. substituting a level-`m` typing derivation into a level-`n` derivation stays at level
   `≤ max(m,n)` — this is what every "substitution lemma" in the development assumes.

(1) and (2) are in tension: (1) forces the measure to count alternations, and alternations
compose additively under substitution, which is exactly what (2) forbids.  Any repair has to
either replace (1) with a different circularity-breaker, or make substitution structural
rather than a derivation transformation — explicit substitutions, or context morphisms
`Γ ⊢ₙ σ : Γ'` as judgment formers, so that "substitute" is a rule whose premises carry their
own index rather than an operation on finished derivations.  Neither exists in this tree, and
neither is in `unique.tex`.

Nothing below depends on how this is resolved: `thm:utype` is proved from `DefInv` and
`SubstC` as stated, and `sort_inv_of_defInv` needs only `DefInv`.

**Why `SubstC` is kept as a hypothesis rather than discharged by the depth-0 rule.**  The two
are the same difficulty, not a trade: adding the rule enlarges `⊢ₙ`, so it makes `DefInv n` —
the one remaining open goal on this route — *harder* by exactly the case it removes here.
Naming the obligation keeps it countable; folding it into the judgment would hide it inside a
definition that five landed lemmas already describe.
-/

namespace Lean4Lean
namespace VEnv

variable {env : VEnv} {U n : Nat}

/-! ## The two hypotheses -/

/-- **`⊢ₙ` has definitional inversion** (`unique.tex:29–35`), transcribed clause for clause. -/
structure DefInv (env : VEnv) (U n : Nat) : Prop where
  /-- `unique.tex:32`. -/
  sort : ∀ {Γ : List VExpr} {u v : VLevel},
    env.IsDefEqN U n Γ (.sort u) (.sort v) → u ≈ v
  /-- `unique.tex:33`. -/
  forallE : ∀ {Γ : List VExpr} {A B A' B' : VExpr},
    env.IsDefEqN U n Γ (.forallE A B) (.forallE A' B') →
    env.IsDefEqN U n Γ A A' ∧ env.IsDefEqN U n (A::Γ) B B'
  /-- `unique.tex:34`. -/
  sort_forallE : ∀ {Γ : List VExpr} {u : VLevel} {A B : VExpr},
    ¬ env.IsDefEqN U n Γ (.sort u) (.forallE A B)

/-- **`⊢ₙ` conversions are closed under instantiation by `⊢ₙ`-typed terms.**

Not a definition of the reference's; it is the step `thm:utype`'s application case takes
without justification.  See the module docstring for why it cannot be proved from
`Stratified.instN` (which lands at `m + n`) and for the two ways to discharge it. -/
def SubstC (env : VEnv) (U n : Nat) : Prop :=
  ∀ {Γ : List VExpr} {A B B' a : VExpr},
    env.HasTypeN U n Γ a A → env.IsDefEqN U n (A::Γ) B B' →
    env.IsDefEqN U n Γ (B.inst a) (B'.inst a)

/-- **`thm:0dinv`** (`unique.tex:56`): `⊢₀` has definitional inversion.

All three clauses are inversion on the term constructor, because `≡₀` *is* syntactic equality
(`IsDefEqN.zero_iff`).  This is the only instance of `DefInv` that exists; without it every
statement below is vacuous. -/
theorem DefInv.zero : env.DefInv U 0 where
  sort h := by have := IsDefEqN.zero_iff.1 h; injection this with h; subst h; rfl
  forallE h := by
    have := IsDefEqN.zero_iff.1 h; injection this with h1 h2
    exact ⟨IsDefEqN.zero_iff.2 h1, IsDefEqN.zero_iff.2 h2⟩
  sort_forallE h := by cases IsDefEqN.zero_iff.1 h

/-- `SubstC` at the base index: substituting into a syntactic equality. -/
theorem SubstC.zero : env.SubstC U 0 := fun _ h =>
  IsDefEqN.zero_iff.2 (by rw [IsDefEqN.zero_iff.1 h])

/-- The fragment of `SubstC` that `Stratified.instN` does reach: the substituted term's
typing derivation must be conversion-free.  `instN` lands at `m + n`, so `m = 0` — and only
`m = 0` — preserves the index.

This is what makes `SubstC` a *gap* rather than a *hypothesis picked to make things work*:
the statement is provable exactly as far as the substitution machinery goes, and no further. -/
theorem SubstC.of_hasTypeN_zero (henv : Ordered env) {Γ : List VExpr} {A B B' a : VExpr}
    (h₀ : env.HasTypeN U 0 Γ a A) (H : env.IsDefEqN U n (A::Γ) B B') :
    env.IsDefEqN U n Γ (B.inst a) (B'.inst a) := by
  have := IsDefEqN.inst0 henv h₀ H
  rwa [Nat.zero_add] at this

/-! ## Congruence and equivalence at a fixed index

Every conversion *rule* of `Stratified` concludes at `n+1`, while `thm:utype`'s conclusion is
at `n`.  So each rule that `thm:utype` needs has to be re-proved as an admissible rule at
`n`, by cases on `n`: at `n = 0` the judgment is syntactic equality (`IsDefEqN.zero_iff`) and
the congruence is `congrArg`; at `n = k+1` it is the rule itself. -/

theorem IsDefEqN.symm' {Γ e e'} (H : env.IsDefEqN U n Γ e e') : env.IsDefEqN U n Γ e' e := by
  cases n with
  | zero => exact zero_iff.2 (zero_iff.1 H).symm
  | succ => exact .symm H

theorem IsDefEqN.trans' {Γ e₁ e₂ e₃} (h1 : env.IsDefEqN U n Γ e₁ e₂)
    (h2 : env.IsDefEqN U n Γ e₂ e₃) : env.IsDefEqN U n Γ e₁ e₃ := by
  cases n with
  | zero => exact zero_iff.2 ((zero_iff.1 h1).trans (zero_iff.1 h2))
  | succ => exact .trans h1 h2

/-- The `∀`-congruence at index `n`, on the codomain only — the shape `thm:utype`'s lambda
case needs, where the domain is fixed by the subject `.lam A body`. -/
theorem IsDefEqN.forallE_congr_r {Γ A B B'} (H : env.IsDefEqN U n (A::Γ) B B') :
    env.IsDefEqN U n Γ (.forallE A B) (.forallE A B') := by
  cases n with
  | zero => exact zero_iff.2 (congrArg _ (zero_iff.1 H))
  | succ => exact .forallEDF .rfl H

/-- The sort congruence `thm:utype`'s `forallE` case needs (`unique.tex:50`).  The two
premises live in *different contexts* — the codomain's level is compared in `A::Γ` — and the
conclusion in a third; nothing about the contexts is used, which is why they are all free. -/
theorem IsDefEqN.sort_imax_congr (dinv : env.DefInv U n) {Γ Γ₁ Γ₂ : List VExpr}
    {u u' v v' : VLevel} (hu : u.WF U) (hu' : u'.WF U) (hv : v.WF U) (hv' : v'.WF U)
    (h1 : env.IsDefEqN U n Γ₁ (.sort u) (.sort u'))
    (h2 : env.IsDefEqN U n Γ₂ (.sort v) (.sort v')) :
    env.IsDefEqN U n Γ (.sort (.imax u v)) (.sort (.imax u' v')) := by
  cases n with
  | zero =>
    have e1 : u = u' := by injection zero_iff.1 h1
    have e2 : v = v' := by injection zero_iff.1 h2
    subst e1; subst e2; exact .rfl
  | succ =>
    exact .sortDF (by exact ⟨hu, hv⟩) (by exact ⟨hu', hv'⟩)
      (VLevel.imax_congr (dinv.sort h1) (dinv.sort h2))

/-! ## Inversion by subject shape

`thm:utype` is stated by the reference as a double induction, the secondary one peeling
conversion rules off the second derivation (`unique.tex:46–48`).  Peeling is the same work
for every subject shape, so it is done once here, as six inversion lemmas — each an induction
whose only interesting case is `conv`, discharged by transitivity at the index.  The primary
induction in `Stratified.uniq` then has no nested induction at all.

The `b = true` argument is how one induction over the `Bool`-indexed judgment is restricted
to its typing half: the eleven conversion constructors carry `b := false` and die on
`nomatch`. -/

theorem Stratified.bvar_inv' {Γ e T b} (H : Stratified env U n Γ e T b) :
    ∀ i, e = .bvar i → b = true → ∃ A, Lookup Γ i A ∧ env.IsDefEqN U n Γ A T := by
  induction H with
  | bvar h => intro _ eq _; cases eq; exact ⟨_, h, .rfl⟩
  | sort | const | app | lam | forallE => intro _ eq _; cases eq
  | conv h _ _ ih2 =>
    intro i eq hb
    have ⟨A, h1, h2⟩ := ih2 i eq hb
    exact ⟨A, h1, IsDefEqN.trans' h2 h⟩
  | rfl | symm | trans | sortDF | constDF | appDF | lamDF | forallEDF | beta | eta
  | proofIrrel | extra => intro _ _ hb; exact nomatch hb

theorem HasTypeN.bvar_inv {Γ i T} (H : env.HasTypeN U n Γ (.bvar i) T) :
    ∃ A, Lookup Γ i A ∧ env.IsDefEqN U n Γ A T := H.bvar_inv' _ rfl rfl

theorem Stratified.sort_inv' {Γ e T b} (H : Stratified env U n Γ e T b) :
    ∀ l, e = .sort l → b = true → l.WF U ∧ env.IsDefEqN U n Γ (.sort (.succ l)) T := by
  induction H with
  | sort h => intro _ eq _; cases eq; exact ⟨h, .rfl⟩
  | bvar | const | app | lam | forallE => intro _ eq _; cases eq
  | conv h _ _ ih2 =>
    intro l eq hb
    have ⟨h1, h2⟩ := ih2 l eq hb
    exact ⟨h1, IsDefEqN.trans' h2 h⟩
  | rfl | symm | trans | sortDF | constDF | appDF | lamDF | forallEDF | beta | eta
  | proofIrrel | extra => intro _ _ hb; exact nomatch hb

theorem HasTypeN.sort_inv {Γ l T} (H : env.HasTypeN U n Γ (.sort l) T) :
    l.WF U ∧ env.IsDefEqN U n Γ (.sort (.succ l)) T := H.sort_inv' _ rfl rfl

theorem Stratified.const_inv' {Γ e T b} (H : Stratified env U n Γ e T b) :
    ∀ c ls, e = .const c ls → b = true →
    ∃ ci, env.constants c = some ci ∧ (∀ l ∈ ls, l.WF U) ∧ ls.length = ci.uvars ∧
      env.IsDefEqN U n Γ (ci.type.instL ls) T := by
  induction H with
  | const h1 h2 h3 => intro _ _ eq _; cases eq; exact ⟨_, h1, h2, h3, .rfl⟩
  | bvar | sort | app | lam | forallE => intro _ _ eq _; cases eq
  | conv h _ _ ih2 =>
    intro c ls eq hb
    have ⟨ci, h1, h2, h3, h4⟩ := ih2 c ls eq hb
    exact ⟨ci, h1, h2, h3, IsDefEqN.trans' h4 h⟩
  | rfl | symm | trans | sortDF | constDF | appDF | lamDF | forallEDF | beta | eta
  | proofIrrel | extra => intro _ _ _ hb; exact nomatch hb

theorem HasTypeN.const_inv {Γ c ls T} (H : env.HasTypeN U n Γ (.const c ls) T) :
    ∃ ci, env.constants c = some ci ∧ (∀ l ∈ ls, l.WF U) ∧ ls.length = ci.uvars ∧
      env.IsDefEqN U n Γ (ci.type.instL ls) T := H.const_inv' _ _ rfl rfl

theorem Stratified.app_inv' {Γ e T b} (H : Stratified env U n Γ e T b) :
    ∀ f a, e = .app f a → b = true →
    ∃ A B, env.HasTypeN U n Γ f (.forallE A B) ∧ env.HasTypeN U n Γ a A ∧
      env.IsDefEqN U n Γ (B.inst a) T := by
  induction H with
  | app h1 h2 => intro _ _ eq _; cases eq; exact ⟨_, _, h1, h2, .rfl⟩
  | bvar | sort | const | lam | forallE => intro _ _ eq _; cases eq
  | conv h _ _ ih2 =>
    intro f a eq hb
    have ⟨A, B, h1, h2, h3⟩ := ih2 f a eq hb
    exact ⟨A, B, h1, h2, IsDefEqN.trans' h3 h⟩
  | rfl | symm | trans | sortDF | constDF | appDF | lamDF | forallEDF | beta | eta
  | proofIrrel | extra => intro _ _ _ hb; exact nomatch hb

theorem HasTypeN.app_inv {Γ f a T} (H : env.HasTypeN U n Γ (.app f a) T) :
    ∃ A B, env.HasTypeN U n Γ f (.forallE A B) ∧ env.HasTypeN U n Γ a A ∧
      env.IsDefEqN U n Γ (B.inst a) T := H.app_inv' _ _ rfl rfl

theorem Stratified.lam_inv' {Γ e T b} (H : Stratified env U n Γ e T b) :
    ∀ A body, e = .lam A body → b = true →
    ∃ u B, env.HasTypeN U n Γ A (.sort u) ∧ env.HasTypeN U n (A::Γ) body B ∧
      env.IsDefEqN U n Γ (.forallE A B) T := by
  induction H with
  | lam h1 h2 => intro _ _ eq _; cases eq; exact ⟨_, _, h1, h2, .rfl⟩
  | bvar | sort | const | app | forallE => intro _ _ eq _; cases eq
  | conv h _ _ ih2 =>
    intro A body eq hb
    have ⟨u, B, h1, h2, h3⟩ := ih2 A body eq hb
    exact ⟨u, B, h1, h2, IsDefEqN.trans' h3 h⟩
  | rfl | symm | trans | sortDF | constDF | appDF | lamDF | forallEDF | beta | eta
  | proofIrrel | extra => intro _ _ _ hb; exact nomatch hb

theorem HasTypeN.lam_inv {Γ A body T} (H : env.HasTypeN U n Γ (.lam A body) T) :
    ∃ u B, env.HasTypeN U n Γ A (.sort u) ∧ env.HasTypeN U n (A::Γ) body B ∧
      env.IsDefEqN U n Γ (.forallE A B) T := H.lam_inv' _ _ rfl rfl

theorem Stratified.forallE_inv' {Γ e T b} (H : Stratified env U n Γ e T b) :
    ∀ A B, e = .forallE A B → b = true →
    ∃ u v, u.WF U ∧ v.WF U ∧ env.HasTypeN U n Γ A (.sort u) ∧
      env.HasTypeN U n (A::Γ) B (.sort v) ∧
      env.IsDefEqN U n Γ (.sort (.imax u v)) T := by
  induction H with
  | forallE h1 h2 h3 h4 => intro _ _ eq _; cases eq; exact ⟨_, _, h1, h2, h3, h4, .rfl⟩
  | bvar | sort | const | app | lam => intro _ _ eq _; cases eq
  | conv h _ _ ih2 =>
    intro A B eq hb
    have ⟨u, v, h1, h2, h3, h4, h5⟩ := ih2 A B eq hb
    exact ⟨u, v, h1, h2, h3, h4, IsDefEqN.trans' h5 h⟩
  | rfl | symm | trans | sortDF | constDF | appDF | lamDF | forallEDF | beta | eta
  | proofIrrel | extra => intro _ _ _ hb; exact nomatch hb

theorem HasTypeN.forallE_inv {Γ A B T} (H : env.HasTypeN U n Γ (.forallE A B) T) :
    ∃ u v, u.WF U ∧ v.WF U ∧ env.HasTypeN U n Γ A (.sort u) ∧
      env.HasTypeN U n (A::Γ) B (.sort v) ∧
      env.IsDefEqN U n Γ (.sort (.imax u v)) T := H.forallE_inv' _ _ rfl rfl

/-! ## `thm:utype` -/

/-- **Unique typing at the index** (`thm:utype`, `unique.tex:40–53`): if `⊢ₙ` has definitional
inversion and is closed under instantiation, then a term's `⊢ₙ` types are all `⊢ₙ`-equal.

The reference's proof is a double induction; here the secondary induction has been factored
out into the `*_inv` lemmas above, so this is a single induction on the first derivation, with
the hypotheses reverted because `n` is an index of `Stratified` and is generalised by it.

Case by case against `unique.tex:48–51`: `conv` is the reference's (1); `bvar`, `sort`,
`const`, `lam` are its (2) — `lam` is "trivial" there but needs the index-`n` `∀`-congruence
here; `forallE` is its (3) and `app` its (4).  `DefInv` is consumed in exactly `app` and
`forallE`; `SubstC` in exactly `app`. -/
theorem Stratified.uniq {Γ e A b} (H : Stratified env U n Γ e A b) :
    env.DefInv U n → env.SubstC U n → b = true →
    ∀ B, env.HasTypeN U n Γ e B → env.IsDefEqN U n Γ A B := by
  induction H with
  | bvar h =>
    intro _ _ _ _ H2
    have ⟨_, h1, h2⟩ := H2.bvar_inv
    exact Lookup.uniq h h1 ▸ h2
  | sort _ => intro _ _ _ _ H2; exact H2.sort_inv.2
  | const h1 _ _ =>
    intro _ _ _ _ H2
    have ⟨_, h1', _, _, h2⟩ := H2.const_inv
    cases Option.some.inj (h1'.symm.trans h1); exact h2
  | app _ ha ihf _ =>
    intro dinv hs _ _ H2
    have ⟨_, _, hf', _, hc⟩ := H2.app_inv
    exact IsDefEqN.trans' (hs ha (dinv.forallE (ihf dinv hs (Eq.refl true) _ hf')).2) hc
  | lam _ _ _ ihb =>
    intro dinv hs _ _ H2
    have ⟨_, _, _, hb', hc⟩ := H2.lam_inv
    exact IsDefEqN.trans' (IsDefEqN.forallE_congr_r (ihb dinv hs (Eq.refl true) _ hb')) hc
  | forallE hu hv _ _ ihA ihB =>
    intro dinv hs _ _ H2
    have ⟨_, _, hu', hv', hA', hB', hc⟩ := H2.forallE_inv
    exact IsDefEqN.trans' (IsDefEqN.sort_imax_congr dinv hu hu' hv hv'
      (ihA dinv hs (Eq.refl true) _ hA') (ihB dinv hs (Eq.refl true) _ hB')) hc
  | conv h _ _ ih2 =>
    intro dinv hs _ _ H2
    exact IsDefEqN.trans' (IsDefEqN.symm' h) (ih2 dinv hs (Eq.refl true) _ H2)
  | rfl | symm | trans | sortDF | constDF | appDF | lamDF | forallEDF | beta | eta
  | proofIrrel | extra => intro _ _ hb; exact nomatch hb

/-- `thm:utype` in the form it is used: `Γ ⊢ₙ e : A` and `Γ ⊢ₙ e : B` give `Γ ⊢ₙ A ≡ B`. -/
theorem HasTypeN.uniq (dinv : env.DefInv U n) (hs : env.SubstC U n) {Γ e A B}
    (H1 : env.HasTypeN U n Γ e A) (H2 : env.HasTypeN U n Γ e B) :
    env.IsDefEqN U n Γ A B := Stratified.uniq H1 dinv hs (Eq.refl true) _ H2

/-! ## The theorem is not vacuous, and it is not weaker at `n = 0`

Two checks, because `DefInv` and `SubstC` are hypotheses everywhere above, and hypotheses
nothing satisfies prove nothing.

Both hold at `n = 0`.  At that instance `thm:utype` reads: *a term's conversion-free types are
syntactically equal* — `uniq_zero` below — which is a real statement, not a tautology, and
the class of derivations it speaks about is inhabited (`sort_zero_ex`). -/

/-- `thm:utype` at the base index, unfolded through `IsDefEqN.zero_iff`: at index `0` unique
typing is *syntactic* uniqueness of the type.  Depends on no hypothesis at all — `DefInv.zero`
and `SubstC.zero` are both proved. -/
theorem HasTypeN.uniq_zero {Γ e A B}
    (H1 : env.HasTypeN U 0 Γ e A) (H2 : env.HasTypeN U 0 Γ e B) : A = B :=
  IsDefEqN.zero_iff.1 (H1.uniq DefInv.zero SubstC.zero H2)

/-- A derivation at index `0`, so `uniq_zero` is not speaking about the empty relation. -/
theorem sort_zero_ex {Γ : List VExpr} {l : VLevel} (h : l.WF U) :
    env.HasTypeN U 0 Γ (.sort l) (.sort (.succ l)) := .sort h

example (Γ : List VExpr) {l : VLevel} (h : l.WF U) :
    VExpr.sort (.succ l) = VExpr.sort (.succ l) :=
  HasTypeN.uniq_zero (sort_zero_ex (env := env) (Γ := Γ) h) (sort_zero_ex h)

/-! ## What this buys against the target

`Theory/Typing/Injectivity.lean`'s `IsDefEqU.sort_inv` and `IsDefEqU.sort_forallE_inv` —
still `sorry` there — follow from definitional inversion *at every index* and nothing else,
by `IsDefEqU.stratifyN`.  Note `SubstC` does **not** appear: these two need only `DefInv`.
That is the direction the target needs; the converse (`IsDefEqN n → IsDefEqU`) is the
reference's regularity upgrade, needs `uniq` itself, and is not required here.

These are the cash value of `DefInv`: `∀ n, DefInv env U n` is now a *sufficient* hypothesis
for the sort half of the injectivity cone.  `thm:utype` is what makes that hypothesis
attackable — `unique.tex`'s induction proves `DefInv (n+1)` from `DefInv n` via `uniq n`, and
`uniq n` is what this file supplies. -/

/-- `IsDefEqU.sort_inv` (`Theory/Typing/Injectivity.lean`), reduced to definitional inversion
at every index. -/
theorem IsDefEqU.sort_inv_of_defInv (henv : Ordered env) {Γ : List VExpr} {u v : VLevel}
    (hΓ : OnCtx Γ (env.IsType U)) (dinv : ∀ n, env.DefInv U n)
    (h : env.IsDefEqU U Γ (.sort u) (.sort v)) : u ≈ v :=
  let ⟨n, hc⟩ := h.stratifyN henv hΓ
  (dinv n).sort hc

/-- `IsDefEqU.sort_forallE_inv` (`Theory/Typing/Injectivity.lean`), likewise. -/
theorem IsDefEqU.sort_forallE_inv_of_defInv (henv : Ordered env) {Γ : List VExpr}
    {u : VLevel} {A B : VExpr}
    (hΓ : OnCtx Γ (env.IsType U)) (dinv : ∀ n, env.DefInv U n) :
    ¬ env.IsDefEqU U Γ (.sort u) (.forallE A B) := fun h =>
  let ⟨n, hc⟩ := h.stratifyN henv hΓ
  (dinv n).sort_forallE hc

end VEnv
end Lean4Lean
