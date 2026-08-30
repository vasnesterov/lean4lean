import Lean4Lean.Theory.Typing.StrengthenVerdict
import Lean4Lean.Theory.Consistency

/-!
# The hole's context class collapses to a one-parameter family

`Theory/Typing/UniqueTyping.lean:174`'s `sorry` — the forward direction of
`IsDefEqU.weakN_iff` — is equivalent to `VEnv.Strengthening1`, the same statement
stripping a **single** context entry (`Theory/Typing/Strengthen.lean` §11), and §12 of that
file narrows it further to entries that are **uninhabited** in their own prefix.

This file narrows the *entry itself*.  The stripped entry may be taken to be

```
bigFalse u  :=  ∀ (α : Sort u), α
```

for a level `u` — one closed type per level, instead of an arbitrary type in an arbitrary
context.  `VEnv.StrengtheningCanon` is the target restricted to those entries, and
`VEnv.StrengtheningCanon.iff_strengthening1` proves the restriction loses nothing.

## Why it works

`bigFalse u` is the *strongest* hypothesis at level `u`: a variable `x : bigFalse u`
inhabits **every** `A : Sort u` of the context below it, by one application `x A`.  So a
derivation over a context carrying an arbitrary entry `A : Sort u` can be pushed through the
context carrying `bigFalse u` in that position:

1. **weaken** — insert `bigFalse u` immediately *below* the `A` entry (`Ctx.Ins.canon`
   builds the commuting square of context insertions);
2. **substitute** — the `A` entry is now inhabited by `.app (.bvar 0) A`, so
   `IsDefEqU.strengthen_of_instN` (`Strengthen.lean` §1 — the *proved* half) strips it;
3. what is left is the same conversion over the context with `bigFalse u` in place of `A`,
   which is exactly `StrengtheningCanon`'s hypothesis.

Both moves are theorems already in the tree.  Nothing here assumes the hole.

## What this is *not*

It is **not** progress towards a proof, and it is not a refutation.  It is a narrowing of
the statement's context class, and it cuts in both directions:

* a proof attempt now only has to handle one context shape per level;
* a refutation attempt now has one concrete target — `∀ (α : Sort u), α :: Γ` — instead of
  an arbitrary well-formed context with an arbitrary uninhabited entry.

The `u = .zero` member of the family is `falseProp = ∀ (p : Prop), p`, the entry
`Theory/Typing/CycleConv.lean` and `Theory/MutualDefUnsound.lean` already work with.

`StrengtheningCanonUninhab` composes this restriction with `Strengthen.lean` §12's, giving
the crispest form the statement has: *adding the hypothesis `∀ (α : Sort u), α` to a
well-formed context, at a level and position where it has no inhabitant, is conservative for
conversion.*

**The family does not collapse to a single level.**  `x : bigFalse u` inhabits `bigFalse v`
only when `u ≈ .imax (.succ v) v`, so level `w+2`'s entry implies level `w+1`'s and nothing
implies level `0`'s but itself.  A single entry covering every level would have to quantify
over `VLevel`, which is not a term of `VExpr`.

**Properness is machine-checked** (§4): the class of `Ctx.Ins (bigFalse u)` insertions is a
*proper* subclass of the `Ctx.LiftN 1 k` insertions, so the reduction is not the trivial
direction of a tautology.  The trivial direction is `Strengthening1 → StrengtheningCanon`.
-/

namespace Lean4Lean

open VExpr

/-! ## 1. `Ctx.Ins`: a `Ctx.LiftN 1 k` that remembers the entry and its prefix

`Ctx.LiftN 1 k Γ Γ'` says an entry was inserted at depth `k` but says neither *what* it is
nor *where* it is typed.  Both are needed here: what, because the residual is stated at a
specific entry; where, because the substituted inhabitant must be typed in the entry's own
prefix. -/

/-- `Ctx.Ins X k Γ Γ' Γ₀`: `Γ'` is `Γ` with the entry `X` inserted at de Bruijn depth `k`,
and `Γ₀` is the suffix of `Γ` below the insertion point — the context in which `X` lives. -/
inductive Ctx.Ins (X : VExpr) : Nat → List VExpr → List VExpr → List VExpr → Prop where
  | zero {Γ : List VExpr} : Ctx.Ins X 0 Γ (X :: Γ) Γ
  | succ {k : Nat} {Γ Γ' Γ₀ : List VExpr} {A : VExpr} :
    Ctx.Ins X k Γ Γ' Γ₀ → Ctx.Ins X (k+1) (A::Γ) (A.liftN 1 k :: Γ') Γ₀

namespace Ctx.Ins

variable {X : VExpr}

theorem liftN : ∀ {k Γ Γ' Γ₀}, Ctx.Ins X k Γ Γ' Γ₀ → Ctx.LiftN 1 k Γ Γ'
  | _, _, _, _, .zero => .one
  | _, _, _, _, .succ h => h.liftN.succ

/-- The insertion is invertible by substitution, at *any* substituted term: nothing in `Γ`
mentions the inserted variable. -/
theorem instN (e₀ : VExpr) :
    ∀ {k Γ Γ' Γ₀}, Ctx.Ins X k Γ Γ' Γ₀ → Ctx.InstN Γ₀ e₀ X k Γ' Γ := by
  intro k Γ Γ' Γ₀ h
  induction h with
  | zero => exact .zero
  | @succ k Γ Γ' Γ₀ A _ ih =>
    have h2 := ih.succ (A := A.liftN 1 k) (e₀ := e₀)
    rwa [VExpr.inst_liftN] at h2

/-- Every one-entry lifting *is* an insertion, of some entry, over some prefix. -/
theorem _root_.Lean4Lean.Ctx.LiftN.exists_ins :
    ∀ {k Γ Γ'}, Ctx.LiftN 1 k Γ Γ' → ∃ X Γ₀, Ctx.Ins X k Γ Γ' Γ₀ := by
  intro k Γ Γ' W
  induction W with
  | @zero Γ As h =>
    match As, h with
    | [A], _ => exact ⟨A, Γ, .zero⟩
  | succ _ ih => obtain ⟨X, Γ₀, h⟩ := ih; exact ⟨X, Γ₀, h.succ⟩

variable {env : VEnv} {U : Nat}

/-- The inserted entry is a type in its own prefix, and that prefix is well formed. -/
theorem entry_typed : ∀ {k Γ Γ' Γ₀}, Ctx.Ins X k Γ Γ' Γ₀ →
    OnCtx Γ' (env.IsType U) → OnCtx Γ₀ (env.IsType U) ∧ env.IsType U Γ₀ X
  | _, _, _, _, .zero, h => ⟨h.1, h.2⟩
  | _, _, _, _, .succ h, h' => h.entry_typed h'.1

/-- Inserting a type into a well-formed context leaves it well formed. -/
theorem onCtx (henv : env.Ordered) : ∀ {k Γ Γ' Γ₀}, Ctx.Ins X k Γ Γ' Γ₀ →
    OnCtx Γ (env.IsType U) → env.IsType U Γ₀ X → OnCtx Γ' (env.IsType U)
  | _, _, _, _, .zero, h, hX => ⟨h, hX⟩
  | _, _, _, _, .succ h, h', hX => ⟨h.onCtx henv h'.1 hX, h'.2.weakN henv h.liftN⟩

/-- **The commuting square.**  An insertion of `X` at depth `k` factors through an
insertion of `Y` at the *same* depth: put `Y` in first, then put `X` back on top of it.
The composite context `Γ₃` carries both, with `X` (lifted over `Y`) at depth `k` and `Y` at
depth `k+1`. -/
theorem canon (Y : VExpr) : ∀ {k Γ Γ' Γ₀}, Ctx.Ins X k Γ Γ' Γ₀ →
    ∃ Γ'' Γ₃, Ctx.Ins Y k Γ Γ'' Γ₀ ∧ Ctx.Ins X.lift k Γ'' Γ₃ (Y :: Γ₀) ∧
      Ctx.LiftN 1 (k+1) Γ' Γ₃ := by
  intro k Γ Γ' Γ₀ h
  induction h with
  | @zero Γ => exact ⟨Y :: Γ, X.lift :: Y :: Γ, .zero, .zero, .succ .one⟩
  | @succ k Γ Γ' Γ₀ A _ ih =>
    obtain ⟨Γ'', Γ₃, h1, h2, h3⟩ := ih
    refine ⟨A.liftN 1 k :: Γ'', (A.liftN 1 k).liftN 1 k :: Γ₃, h1.succ, h2.succ, ?_⟩
    have h4 := h3.succ (A := A.liftN 1 k)
    rw [VExpr.liftN'_liftN' (Nat.le_succ k) (by omega)] at h4
    rw [VExpr.liftN'_liftN_hi]
    exact h4

end Ctx.Ins

namespace VEnv

variable {env : VEnv} {U : Nat}

/-! ## 2. `bigFalse u = ∀ (α : Sort u), α`, and why it is the strongest entry at level `u` -/

/-- `∀ (α : Sort u), α`, at an arbitrary level.  `StrengthenVerdict.univType` is the
`u = .param 0` member of this family; `Theory.falseProp` is the `u = .zero` member. -/
def _root_.Lean4Lean.bigFalse (u : VLevel) : VExpr := .forallE (.sort u) (.bvar 0)

@[simp] theorem bigFalse_liftN {u : VLevel} {n k : Nat} :
    (bigFalse u).liftN n k = bigFalse u := rfl

/-- **The canonical entry is a closed term** — it does not depend on the context below it.
This is the second half of the narrowing: previously the stripped entry was an arbitrary
type *in an arbitrary prefix*; now it is one closed term per level. -/
theorem bigFalse_closed {u : VLevel} : (bigFalse u).ClosedN 0 := ⟨trivial, Nat.zero_lt_one⟩

/-- The `u = .zero` member of the family is `Theory/Consistency.lean`'s `falseProp`. -/
theorem bigFalse_zero : bigFalse .zero = Lean4Lean.falseProp := rfl

/-- The `u = .param 0` member is `StrengthenVerdict.lean`'s `univType`. -/
theorem bigFalse_param_zero : bigFalse (.param 0) = Lean4Lean.univType := rfl

/-- `bigFalse u` is a type, in every environment and every context. -/
theorem bigFalse_isType {u : VLevel} {Γ : List VExpr} (hu : u.WF U) :
    env.IsType U Γ (bigFalse u) :=
  ⟨_, IsDefEq.forallEDF (u := .succ u) (v := u) (.sortDF hu hu rfl) (.bvar .zero)⟩

/-- **The strongest hypothesis at level `u`.**  A variable of type `bigFalse u` at the head
of the context inhabits every type of the context below it that is classified by `.sort u`. -/
theorem hasType_bigFalse_app {u : VLevel} {Γ : List VExpr} {A : VExpr}
    (henv : env.Ordered) (hA : env.HasType U Γ A (.sort u)) :
    env.HasType U (bigFalse u :: Γ) (.app (.bvar 0) A.lift) A.lift := by
  have hx : env.HasType U (bigFalse u :: Γ) (.bvar 0) (bigFalse u) :=
    .bvar (by simpa using (Lookup.zero (ty := bigFalse u) (Γ := Γ)))
  have hAl : env.HasType U (bigFalse u :: Γ) A.lift (.sort u) := hA.weak (B := bigFalse u) henv
  have h := IsDefEq.appDF (A := .sort u) (B := .bvar 0) hx hAl
  simp only [VExpr.inst, VExpr.instVar_zero] at h
  exact h

/-! ## 3. The reduction -/

/-- **The target, restricted to the canonical entries.**  The same statement as
`Strengthening1`, with the stripped entry required to be `∀ (α : Sort u), α`. -/
def StrengtheningCanon (env : VEnv) (U : Nat) : Prop :=
  ∀ {k : Nat} {Γ Γ' Γ₀ : List VExpr} {e1 e2 : VExpr} {u : VLevel}, u.WF U →
    Ctx.Ins (bigFalse u) k Γ Γ' Γ₀ →
    OnCtx Γ (env.IsType U) → OnCtx Γ' (env.IsType U) →
    env.IsDefEqU U Γ' (e1.liftN 1 k) (e2.liftN 1 k) → env.IsDefEqU U Γ e1 e2

/-- The trivial direction: the canonical entries are entries. -/
theorem Strengthening1.canon (H : Strengthening1 env U) : StrengtheningCanon env U :=
  fun _ hins hΓ hΓ' h => H hins.liftN hΓ hΓ' h

/-- **The swap.**  An arbitrary one-entry stripping is replaced by a stripping of the
canonical entry `bigFalse u`, over the *same* `Γ`, `e1`, `e2` and depth `k`.

Two moves, both already theorems: insert `bigFalse u` below the stripped entry
(`Ctx.Ins.canon` builds the square, `IsDefEqU.weakN` transports the derivation), then strip
the original entry — now inhabited by `.app (.bvar 0) A` — with
`IsDefEqU.strengthen_of_instN` (`Strengthen.lean` §1, the **proved** half). -/
theorem canon_swap (henv : env.Ordered) {k : Nat} {Γ Γ' : List VExpr} {e1 e2 : VExpr}
    (W : Ctx.LiftN 1 k Γ Γ') (hΓ : OnCtx Γ (env.IsType U)) (hΓ' : OnCtx Γ' (env.IsType U))
    (h : env.IsDefEqU U Γ' (e1.liftN 1 k) (e2.liftN 1 k)) :
    ∃ (u : VLevel) (Γ'' Γ₀ : List VExpr), u.WF U ∧ Ctx.Ins (bigFalse u) k Γ Γ'' Γ₀ ∧
      OnCtx Γ₀ (env.IsType U) ∧ OnCtx Γ'' (env.IsType U) ∧
      env.IsDefEqU U Γ'' (e1.liftN 1 k) (e2.liftN 1 k) := by
  obtain ⟨A, Γ₀, hins⟩ := W.exists_ins
  obtain ⟨hΓ₀, u, hA⟩ := hins.entry_typed hΓ'
  have hu : u.WF U := (IsDefEq.levelWF hA (onCtx_levelWF hΓ₀)).2.2
  obtain ⟨Γ'', Γ₃, hY, hX, hW3⟩ := hins.canon (bigFalse u)
  have h1 := h.weakN henv hW3
  rw [VExpr.liftN'_liftN' (Nat.le_succ k) (by omega),
      VExpr.liftN'_liftN' (Nat.le_succ k) (by omega),
      ← VExpr.liftN'_liftN_hi (n1 := 1) (n2 := 1),
      ← VExpr.liftN'_liftN_hi (n1 := 1) (n2 := 1)] at h1
  exact ⟨u, Γ'', Γ₀, hu, hY, hΓ₀, hY.onCtx henv hΓ (bigFalse_isType hu),
    IsDefEqU.strengthen_of_instN henv (hX.instN _) (hasType_bigFalse_app henv hA) h1⟩

/-- **The canonical entries are enough.** -/
theorem StrengtheningCanon.strengthening1 (henv : env.Ordered) (H : StrengtheningCanon env U) :
    Strengthening1 env U := by
  intro k Γ Γ' e1 e2 W hΓ hΓ' h
  obtain ⟨u, Γ'', Γ₀, hu, hY, _, hΓ'', h2⟩ := canon_swap henv W hΓ hΓ' h
  exact H hu hY hΓ hΓ'' h2

/-- **The target, restricted to canonical entries that are also uninhabited.**  The two
restrictions of `Strengthen.lean` §12 and of this file compose. -/
def StrengtheningCanonUninhab (env : VEnv) (U : Nat) : Prop :=
  ∀ {k : Nat} {Γ Γ' Γ₀ : List VExpr} {e1 e2 : VExpr} {u : VLevel}, u.WF U →
    Ctx.Ins (bigFalse u) k Γ Γ' Γ₀ →
    OnCtx Γ (env.IsType U) → OnCtx Γ' (env.IsType U) →
    (∀ t, ¬ env.HasType U Γ₀ t (bigFalse u)) →
    env.IsDefEqU U Γ' (e1.liftN 1 k) (e2.liftN 1 k) → env.IsDefEqU U Γ e1 e2

theorem Strengthening1.canonUninhab (H : Strengthening1 env U) :
    StrengtheningCanonUninhab env U := fun _ hins hΓ hΓ' _ h => H hins.liftN hΓ hΓ' h

/-- **Both restrictions at once.**  After the swap, split classically on whether the
canonical entry has an inhabitant: if it does, `IsDefEqU.strengthen_of_instN` closes the
goal outright; if not, the doubly-restricted residual applies. -/
theorem StrengtheningCanonUninhab.strengthening1 (henv : env.Ordered)
    (H : StrengtheningCanonUninhab env U) : Strengthening1 env U := by
  intro k Γ Γ' e1 e2 W hΓ hΓ' h
  obtain ⟨u, Γ'', Γ₀, hu, hY, _, hΓ'', h2⟩ := canon_swap henv W hΓ hΓ' h
  by_cases hinh : ∃ t, env.HasType U Γ₀ t (bigFalse u)
  · obtain ⟨t, ht⟩ := hinh
    exact IsDefEqU.strengthen_of_instN henv (hY.instN t) ht h2
  · exact H hu hY hΓ hΓ'' (fun t ht => hinh ⟨t, ht⟩) h2

/-- **…and it is still the whole statement.** -/
theorem StrengtheningCanonUninhab.iff_strengthening1 (henv : env.Ordered) :
    StrengtheningCanonUninhab env U ↔ Strengthening1 env U :=
  ⟨fun H => H.strengthening1 henv, fun H => H.canonUninhab⟩

/-- **The restriction loses nothing.** -/
theorem StrengtheningCanon.iff_strengthening1 (henv : env.Ordered) :
    StrengtheningCanon env U ↔ Strengthening1 env U :=
  ⟨fun H => H.strengthening1 henv, fun H => H.canon⟩

/-- **…hence it is the hole.**  Chained through `Strengthen.lean` §11. -/
theorem StrengtheningCanon.iff_target (henv : VEnv.WF env) :
    StrengtheningCanon env U ↔ StrengtheningTarget env U :=
  (StrengtheningCanon.iff_strengthening1 henv.ordered).trans (Strengthening1.iff_target henv)

/-! ## 4. Non-vacuity and the properness check

Working rule 5: a claimed reduction is a reduction only if the residual is a *proper*
restriction.  `Strengthening1 → StrengtheningCanon` is the trivial direction; the content is
the converse, and it has content exactly because there are one-entry strippings whose entry
is not of the canonical form. -/

/-- The residual's premises are satisfiable, at the innermost position. -/
theorem strengtheningCanon_premises {u : VLevel} {Γ : List VExpr} (hu : u.WF U)
    (hΓ : OnCtx Γ (env.IsType U)) :
    Ctx.Ins (bigFalse u) 0 Γ (bigFalse u :: Γ) Γ ∧ OnCtx Γ (env.IsType U) ∧
      OnCtx (bigFalse u :: Γ) (env.IsType U) :=
  ⟨.zero, hΓ, hΓ, bigFalse_isType hu⟩

/-- **The negative control.**  `Ctx.Ins (bigFalse u)` is a *proper* subclass of the
`Ctx.LiftN 1 k` strippings: here is a well-formed one-entry stripping whose entry is not
`bigFalse u` for any `u`.  So the reduction is not the trivial direction read backwards. -/
theorem ins_sort_not_bigFalse {Γ : List VExpr} :
    Ctx.Ins (.sort .zero) 0 Γ (.sort .zero :: Γ) Γ ∧
      Ctx.LiftN 1 0 Γ (.sort .zero :: Γ) ∧ ∀ u : VLevel, (.sort .zero : VExpr) ≠ bigFalse u :=
  ⟨.zero, .one, fun _ => nofun⟩

end VEnv
end Lean4Lean
