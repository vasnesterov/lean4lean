import Lean4Lean.Theory.Typing.RawDefEq
import Lean4Lean.Theory.Typing.Strong

/-!
# Carneiro's conversion-alternation index

`~/lean-type-theory/unique.tex:10–15` defines, by induction on `n`:

* `Γ ⊢₀ α ≡ β` iff `α = β`;
* `Γ ⊢ₙ₊₁ α ≡ β` iff `Γ ⊢ α ≡ β` is derivable using only `Γ ⊢ₙ e : α` typing judgments;
* `Γ ⊢ₙ e : α` iff `Γ ⊢ e : α` is derivable with every appeal to the conversion rule using
  `Γ ⊢ₘ α ≡ β` for some `m ≤ n`.

The whole of `unique.tex` is an induction on this `n`: definitional inversion at `n+1` is
proved from unique typing at `n` (`thm:1dinv`), and unique typing at `n` from definitional
inversion at `n` (`thm:utype`).  It is the only published proof of `IsDefEqU.sort_inv`, and
this index is the reason it is not circular.

`Theory/Typing/Strong.lean`'s `HasTypeStratified` is **not** this index: it counts derivation
height, and its `defeq` constructor carries a full *unstratified* `IsDefEq`, so "definitional
inversion at `n`" is not stateable against it.  What that file does supply is the other half
— `HasTypeStrong` is Carneiro's typing judgment with the conversion rule isolated in exactly
one constructor.  This file supplies the missing half.

## Presentation

One inductive with a `Bool` discriminator rather than a mutual pair, following
`HasTypeStrong`'s own comment: "functionally a mutual inductive type, but using a bool index
makes it easier to do induction in lean".  Both judgments have the same arity, so
`Stratified n Γ x y true` is `Γ ⊢ₙ x : y` and `Stratified n Γ x y false` is `Γ ⊢ₙ x ≡ y`.

The conversion rules are transcribed from `~/lean-type-theory/axioms.tex:30–41` — the
three-place judgment, as `Theory/Typing/RawDefEq.lean` explains at length — with every
typing premise dropped one index, and the typing rules from the reference's typing judgment
with `conv` the only rule mentioning conversion.

## One deviation from the reference, and why

`rfl` is **unconditional** here; the reference's reflexivity rule (`axioms.tex:31`) requires
`Γ ⊢ e : α`.  This is what makes `≡₀` *exactly* syntactic equality, which is the reference's
own stipulation for level `0` — and it repairs a gap in the reference's basics.  Carneiro
states monotonicity as "(2) follows from (1)", but at `m = 0` it does not: `⊢₀ α ≡ β` is
`α = β` with no typing content, while `⊢₁ α ≡ β` via a typing-guarded `refl` would demand
`Γ ⊢₀ α : γ`, which need not hold for an ill-typed `α`.  Unconditional `rfl` closes that
and changes nothing about well-typed terms, since `rfl` relates a term only to itself.
-/

namespace Lean4Lean
open Lean4Lean
namespace VEnv

section
set_option hygiene false
variable (env : VEnv) (U : Nat)

local notation:65 Γ " ⊢[" n "] " e " : " A:30 => Stratified n Γ e A true
local notation:65 Γ " ⊢[" n "] " e " ≡ " e':30 => Stratified n Γ e e' false

/-- **Carneiro's `⊢ₙ` pair** (`unique.tex:10–15`).  `b = true` is the typing judgment,
`b = false` the conversion judgment.

Every conversion rule concludes at `n+1` and takes its *typing* premises at `n`; that drop
is the entire content of the index.  Congruence premises stay at `n+1`.  The typing rules
all stay at `n`, and `conv` — the reference's conversion rule (`axioms.tex:19`) — is the
only one that mentions conversion at all. -/
inductive Stratified : Nat → List VExpr → VExpr → VExpr → Bool → Prop where
  | bvar : Lookup Γ i A → Γ ⊢[n] .bvar i : A
  | sort : l.WF U → Γ ⊢[n] .sort l : .sort (.succ l)
  | const :
    env.constants c = some ci → (∀ l ∈ ls, l.WF U) → ls.length = ci.uvars →
    Γ ⊢[n] .const c ls : ci.type.instL ls
  | app : (Γ ⊢[n] f : .forallE A B) → (Γ ⊢[n] a : A) → Γ ⊢[n] .app f a : B.inst a
  | lam : (Γ ⊢[n] A : .sort u) → (A::Γ ⊢[n] body : B) → Γ ⊢[n] .lam A body : .forallE A B
  | forallE :
    (Γ ⊢[n] A : .sort u) → (A::Γ ⊢[n] B : .sort v) →
    Γ ⊢[n] .forallE A B : .sort (.imax u v)
  /-- The reference's conversion rule (`axioms.tex:19`), and the only coupling point. -/
  | conv : (Γ ⊢[n] A ≡ B) → (Γ ⊢[n] e : A) → Γ ⊢[n] e : B
  /-- Unconditional, unlike `axioms.tex:31` — see the module docstring. -/
  | rfl : Γ ⊢[n] e ≡ e
  | symm : (Γ ⊢[n+1] e ≡ e') → Γ ⊢[n+1] e' ≡ e
  | trans : (Γ ⊢[n+1] e₁ ≡ e₂) → (Γ ⊢[n+1] e₂ ≡ e₃) → Γ ⊢[n+1] e₁ ≡ e₃
  | sortDF : l.WF U → l'.WF U → l ≈ l' → Γ ⊢[n+1] .sort l ≡ .sort l'
  | constDF :
    env.constants c = some ci →
    (∀ l ∈ ls, l.WF U) → (∀ l ∈ ls', l.WF U) →
    ls.length = ci.uvars → List.Forall₂ (· ≈ ·) ls ls' →
    Γ ⊢[n+1] .const c ls ≡ .const c ls'
  /-- The reference's one type-annotated conversion rule (`axioms.tex:35`, with the `:41`
  abbreviation expanded).  Its four typing premises are what drop to `n`. -/
  | appDF :
    (Γ ⊢[n+1] f ≡ f') → (Γ ⊢[n] f : .forallE A B) → (Γ ⊢[n] f' : .forallE A B) →
    (Γ ⊢[n+1] a ≡ a') → (Γ ⊢[n] a : A) → (Γ ⊢[n] a' : A) →
    Γ ⊢[n+1] .app f a ≡ .app f' a'
  | lamDF :
    (Γ ⊢[n+1] A ≡ A') → (A::Γ ⊢[n+1] body ≡ body') →
    Γ ⊢[n+1] .lam A body ≡ .lam A' body'
  | forallEDF :
    (Γ ⊢[n+1] A ≡ A') → (A::Γ ⊢[n+1] B ≡ B') →
    Γ ⊢[n+1] .forallE A B ≡ .forallE A' B'
  | beta :
    (A::Γ ⊢[n] e : B) → (Γ ⊢[n] e' : A) →
    Γ ⊢[n+1] .app (.lam A e) e' ≡ e.inst e'
  | eta :
    (Γ ⊢[n] e : .forallE A B) →
    Γ ⊢[n+1] .lam A (.app e.lift (.bvar 0)) ≡ e
  | proofIrrel :
    (Γ ⊢[n] p : .sort .zero) → (Γ ⊢[n] h : p) → (Γ ⊢[n] h' : p) →
    Γ ⊢[n+1] h ≡ h'
  | extra :
    env.defeqs df → (∀ l ∈ ls, l.WF U) → ls.length = df.uvars →
    Γ ⊢[n+1] df.lhs.instL ls ≡ df.rhs.instL ls

end

/-- `Γ ⊢ₙ e : A`. -/
abbrev HasTypeN (env : VEnv) (U n : Nat) (Γ : List VExpr) (e A : VExpr) : Prop :=
  Stratified env U n Γ e A true

/-- `Γ ⊢ₙ e ≡ e'`. -/
abbrev IsDefEqN (env : VEnv) (U n : Nat) (Γ : List VExpr) (e e' : VExpr) : Prop :=
  Stratified env U n Γ e e' false

variable {env : VEnv} {U : Nat}

/-! ## Basics (1) and (2): monotonicity in the index -/

/-- **Reference basics (1) and (2)**, as one statement: both judgments are monotone in the
index.  The reference proves (2) from (1); here they are the two values of `b`. -/
theorem Stratified.mono {m n : Nat} (le : m ≤ n) {Γ e₁ e₂ b}
    (H : Stratified env U m Γ e₁ e₂ b) : Stratified env U n Γ e₁ e₂ b := by
  induction H generalizing n with
  | bvar h => exact .bvar h
  | sort h => exact .sort h
  | const h1 h2 h3 => exact .const h1 h2 h3
  | app _ _ ih1 ih2 => exact .app (ih1 le) (ih2 le)
  | lam _ _ ih1 ih2 => exact .lam (ih1 le) (ih2 le)
  | forallE _ _ ih1 ih2 => exact .forallE (ih1 le) (ih2 le)
  | conv _ _ ih1 ih2 => exact .conv (ih1 le) (ih2 le)
  | rfl => exact .rfl
  | symm _ ih =>
    let k+1 := n; exact .symm (ih le)
  | trans _ _ ih1 ih2 =>
    let k+1 := n; exact .trans (ih1 le) (ih2 le)
  | sortDF h1 h2 h3 => let k+1 := n; exact .sortDF h1 h2 h3
  | constDF h1 h2 h3 h4 h5 => let k+1 := n; exact .constDF h1 h2 h3 h4 h5
  | appDF _ _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 ih6 =>
    let k+1 := n
    have le' := Nat.le_of_succ_le_succ le
    exact .appDF (ih1 le) (ih2 le') (ih3 le') (ih4 le) (ih5 le') (ih6 le')
  | lamDF _ _ ih1 ih2 => let k+1 := n; exact .lamDF (ih1 le) (ih2 le)
  | forallEDF _ _ ih1 ih2 => let k+1 := n; exact .forallEDF (ih1 le) (ih2 le)
  | beta _ _ ih1 ih2 =>
    let k+1 := n
    have le' := Nat.le_of_succ_le_succ le
    exact .beta (ih1 le') (ih2 le')
  | eta _ ih =>
    let k+1 := n; exact .eta (ih (Nat.le_of_succ_le_succ le))
  | proofIrrel _ _ _ ih1 ih2 ih3 =>
    let k+1 := n
    have le' := Nat.le_of_succ_le_succ le
    exact .proofIrrel (ih1 le') (ih2 le') (ih3 le')
  | extra h1 h2 h3 => let k+1 := n; exact .extra h1 h2 h3

theorem HasTypeN.mono {m n : Nat} (le : m ≤ n) {Γ e A}
    (H : env.HasTypeN U m Γ e A) : env.HasTypeN U n Γ e A := Stratified.mono le H

theorem IsDefEqN.mono {m n : Nat} (le : m ≤ n) {Γ e e'}
    (H : env.IsDefEqN U m Γ e e') : env.IsDefEqN U n Γ e e' := Stratified.mono le H

theorem Stratified.eq_of_zero {Γ e₁ e₂ n b} (H : Stratified env U n Γ e₁ e₂ b) :
    n = 0 → b = false → e₁ = e₂ := by
  induction H with
  | rfl => exact fun _ _ => Eq.refl _
  | bvar | sort | const | app | lam | forallE | conv => exact fun _ h => nomatch h
  | symm | trans | sortDF | constDF | appDF | lamDF | forallEDF | beta | eta
  | proofIrrel | extra => exact fun h _ => nomatch h

/-- **`≡₀` is exactly syntactic equality** — the reference's stipulation (`unique.tex:12`),
here a theorem, and the base case its induction on `n` rests on (`thm:0dinv`). -/
theorem IsDefEqN.zero_iff {Γ e e'} : env.IsDefEqN U 0 Γ e e' ↔ e = e' :=
  ⟨fun H => H.eq_of_zero rfl rfl, fun h => h ▸ .rfl⟩


/-! ## Basics (3) and (4): every derivation lands at some index

The reference states these separately ("If `Γ ⊢ e : α` then `Γ ⊢ₙ e : α` for some `n`", and
likewise for `≡`) and proves them "by a mutual induction on the typing judgment".  Here they
are one statement, for the reason that makes the induction go through: a conversion rule's
*typing* premises are, in `IsDefEqStrong`, diagonal instances of the conversion judgment
itself, so an induction that only produced the conversion half would have nothing to feed
`appDF`, `beta`, `eta` or `proofIrrel`.  Carrying both endpoints' typings in the conclusion
makes the single induction on `IsDefEqStrong` self-contained.
-/

theorem IsDefEqStrong.stratifyN {Γ e₁ e₂ A} (H : env.IsDefEqStrong U Γ e₁ e₂ A) :
    ∃ n, env.IsDefEqN U n Γ e₁ e₂ ∧ env.HasTypeN U n Γ e₁ A ∧ env.HasTypeN U n Γ e₂ A := by
  induction H with
  | bvar h1 _ _ _ => exact ⟨0, .rfl, .bvar h1, .bvar h1⟩
  | symm _ ih =>
    obtain ⟨n, c, t1, t2⟩ := ih
    exact ⟨n+1, .symm (c.mono (by omega)), t2.mono (by omega), t1.mono (by omega)⟩
  | trans _ _ ih1 ih2 =>
    obtain ⟨n₁, c1, t1, _⟩ := ih1
    obtain ⟨n₂, c2, _, t2⟩ := ih2
    exact ⟨max n₁ n₂ + 1, .trans (c1.mono (by omega)) (c2.mono (by omega)),
      t1.mono (by omega), t2.mono (by omega)⟩
  | sortDF h1 h2 h3 =>
    exact ⟨1, .sortDF h1 h2 h3, .sort h1,
      .conv (.sortDF (by exact h2) (by exact h1) (VLevel.succ_congr h3.symm)) (.sort h2)⟩
  | constDF h1 h2 h3 h4 h5 _ _ _ _ ih8 =>
    obtain ⟨n₈, c8, _, _⟩ := ih8
    refine ⟨n₈ + 1, ?_, ?_, ?_⟩
    · exact (Stratified.constDF (n := 0) h1 h2 h3 h4 h5).mono (by omega)
    · exact Stratified.const h1 h2 h4
    · exact .conv (.symm (c8.mono (by omega)))
        (Stratified.const h1 h3 (h5.length_eq.symm.trans h4))
  | appDF _ _ _ _ _ _ _ _ _ ih5 ih6 ih7 =>
    obtain ⟨n₅, cf, tf, tf'⟩ := ih5
    obtain ⟨n₆, ca, ta, ta'⟩ := ih6
    obtain ⟨n₇, cB, _, _⟩ := ih7
    refine ⟨max n₅ (max n₆ n₇) + 1, ?_, ?_, ?_⟩
    · exact .appDF (cf.mono (by omega)) (tf.mono (by omega)) (tf'.mono (by omega))
        (ca.mono (by omega)) (ta.mono (by omega)) (ta'.mono (by omega))
    · exact Stratified.app (tf.mono (by omega)) (ta.mono (by omega))
    · exact .conv (.symm (cB.mono (by omega)))
        (Stratified.app (tf'.mono (by omega)) (ta'.mono (by omega)))
  | lamDF _ _ _ _ _ _ _ ih3 _ _ ih6 ih7 =>
    obtain ⟨n₃, cA, tA, tA'⟩ := ih3
    obtain ⟨n₆, cb, tb, _⟩ := ih6
    obtain ⟨n₇, _, _, tb'⟩ := ih7
    refine ⟨max n₃ (max n₆ n₇) + 1, ?_, ?_, ?_⟩
    · exact .lamDF (cA.mono (by omega)) (cb.mono (by omega))
    · exact Stratified.lam (tA.mono (by omega)) (tb.mono (by omega))
    · exact .conv (.forallEDF (.symm (cA.mono (by omega))) .rfl)
        (Stratified.lam (tA'.mono (by omega)) (tb'.mono (by omega)))
  | forallEDF _ _ _ _ _ ih3 ih4 ih5 =>
    obtain ⟨n₃, cA, tA, tA'⟩ := ih3
    obtain ⟨n₄, cb, tb, _⟩ := ih4
    obtain ⟨n₅, _, _, tb'⟩ := ih5
    refine ⟨max n₃ (max n₄ n₅) + 1, ?_, ?_, ?_⟩
    · exact .forallEDF (cA.mono (by omega)) (cb.mono (by omega))
    · exact Stratified.forallE (tA.mono (by omega)) (tb.mono (by omega))
    · exact Stratified.forallE (tA'.mono (by omega)) (tb'.mono (by omega))
  | defeqDF _ _ _ ih2 ih3 =>
    obtain ⟨n₂, cAB, _, _⟩ := ih2
    obtain ⟨n₃, ce, te1, te2⟩ := ih3
    refine ⟨max n₂ n₃, ce.mono (by omega), ?_, ?_⟩
    · exact .conv (cAB.mono (by omega)) (te1.mono (by omega))
    · exact .conv (cAB.mono (by omega)) (te2.mono (by omega))
  | beta _ _ _ _ _ _ _ _ ih3 _ ih5 ih6 _ ih8 =>
    obtain ⟨n₃, _, tA, _⟩ := ih3
    obtain ⟨n₅, _, te, _⟩ := ih5
    obtain ⟨n₆, _, tE, _⟩ := ih6
    obtain ⟨n₈, _, tie, _⟩ := ih8
    refine ⟨max n₃ (max n₅ (max n₆ n₈)) + 1, ?_, ?_, ?_⟩
    · exact .beta (te.mono (by omega)) (tE.mono (by omega))
    · exact Stratified.app (Stratified.lam (tA.mono (by omega)) (te.mono (by omega)))
        (tE.mono (by omega))
    · exact tie.mono (by omega)
  | @eta Γ A u B v e _ _ _ _ _ _ _ _ ih3 _ _ ih6 ih7 _ =>
    obtain ⟨n₃, _, tA, _⟩ := ih3
    obtain ⟨n₆, _, te, _⟩ := ih6
    obtain ⟨n₇, _, tel, _⟩ := ih7
    refine ⟨max n₃ (max n₆ n₇) + 1, .eta (te.mono (by omega)), ?_, te.mono (by omega)⟩
    refine Stratified.lam (tA.mono (by omega)) ?_
    rw [← VExpr.instN_bvar0 B 0]
    exact Stratified.app (tel.mono (by omega)) (Stratified.bvar Lookup.zero)
  | proofIrrel _ _ _ ih1 ih2 ih3 =>
    obtain ⟨n₁, _, tp, _⟩ := ih1
    obtain ⟨n₂, _, th, _⟩ := ih2
    obtain ⟨n₃, _, th', _⟩ := ih3
    refine ⟨max n₁ (max n₂ n₃) + 1, ?_, th.mono (by omega), th'.mono (by omega)⟩
    exact .proofIrrel (tp.mono (by omega)) (th.mono (by omega)) (th'.mono (by omega))
  | extra h1 h2 h3 _ _ _ _ _ _ _ _ _ ih8 ih9 =>
    obtain ⟨n₈, _, tl, _⟩ := ih8
    obtain ⟨n₉, _, tr, _⟩ := ih9
    exact ⟨max n₈ n₉ + 1, (Stratified.extra (n := 0) h1 h2 h3).mono (by omega),
      tl.mono (by omega), tr.mono (by omega)⟩

/-- **Reference basics (3) and (4)** for the ambient judgment: every derivation is a
`⊢ₙ` derivation for some `n`, and both endpoints are typed at that same `n`.

The `Ordered`/`OnCtx` hypotheses are the tree's price for having a *separated* typing
judgment at all: they are what `IsDefEq.strong` needs to turn `IsDefEq` — in which typing is
the diagonal — into `IsDefEqStrong`, whose companion `HasTypeStrong` isolates the conversion
rule.  The reference pays nothing here because its two judgments are separate by
construction. -/
theorem IsDefEq.stratifyN {Γ e₁ e₂ A} (henv : Ordered env) (hΓ : OnCtx Γ (env.IsType U))
    (H : env.IsDefEq U Γ e₁ e₂ A) :
    ∃ n, env.IsDefEqN U n Γ e₁ e₂ ∧ env.HasTypeN U n Γ e₁ A ∧ env.HasTypeN U n Γ e₂ A :=
  (H.strong henv hΓ).stratifyN

theorem HasType.stratifyN {Γ e A} (henv : Ordered env) (hΓ : OnCtx Γ (env.IsType U))
    (H : env.HasType U Γ e A) : ∃ n, env.HasTypeN U n Γ e A :=
  let ⟨n, _, t, _⟩ := IsDefEq.stratifyN henv hΓ H; ⟨n, t⟩

theorem IsDefEqU.stratifyN {Γ e₁ e₂} (henv : Ordered env) (hΓ : OnCtx Γ (env.IsType U))
    (H : env.IsDefEqU U Γ e₁ e₂) : ∃ n, env.IsDefEqN U n Γ e₁ e₂ :=
  let ⟨_, h⟩ := H; let ⟨n, c, _, _⟩ := h.stratifyN henv hΓ; ⟨n, c⟩

/-! ## What this does and does not give

All four of the reference's basics are above, sorry-free.  With them, "definitional inversion
at `n`" — the reference's `unique.tex:30–35` — is *stateable* against this tree for the first
time, and its base case `thm:0dinv` is `IsDefEqN.zero_iff`.

What is not here is the inductive step.  `thm:1dinv` derives definitional inversion at `n+1`
from unique typing at `n`, and that route runs through the κ-reduction and Church–Rosser
development of `unique.tex` §§3–4, restated over `IsDefEqN`.  Nobody has written that.  This
file is the index it would be written against, not a proof that uses it.

**Two things worth knowing before continuing.**

*The direction proved here is the one the target needs.*  `IsDefEqU.sort_inv` follows from
"definitional inversion at every `n`" plus `IsDefEqU.stratifyN` alone: given
`Γ ⊢ .sort u ≡ .sort v`, basics (4) lands it at some `n`, and inversion at `n` finishes.  The
converse — `IsDefEqN n → IsDefEqU` — is *not* proved here and is not needed for that.  It is
the reference's "Regularity continued" upgrade (`typesys.tex`), and it needs `IsDefEq.uniq`,
because `IsDefEqN`'s `conv` rule is three-place while `IsDefEq.defeqDF` demands a type.  Do
not spend effort on it before something asks.

*Basics (3) and (4) are also this definition's anti-vacuity check.*  An index with a
misplaced drop can easily be a relation nothing lands in; `IsDefEq.stratifyN` rules that out
mechanically, for every ambient derivation.
-/

end VEnv
end Lean4Lean
