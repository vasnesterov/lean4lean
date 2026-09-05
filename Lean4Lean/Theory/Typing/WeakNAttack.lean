import Lean4Lean.Theory.Typing.StrengthenCanon
import Lean4Lean.Theory.Typing.StrengthenAudit
import Lean4Lean.Theory.Typing.StrengthenInhabGate

/-!
# The position quantifier collapses: strengthening is a statement about the *innermost* entry

Round 10 of the `VEnv.IsDefEqU.weakN_iff` line (`Theory/Typing/UniqueTyping.lean:172`).
**Nothing here closes the hole, and nothing here removes a `sorry`.**

Every one of the twenty-odd statements in the strengthening family quantifies the *position* of
the stripped entry — `Ctx.LiftN n k Γ Γ'` with `k` universally quantified — and not one of them
is stated at `k = 0`.  This file shows the quantifier is redundant, for the target and for
**both** conjuncts of the standing decomposition
(`StrengtheningTarget ↔ PiDescend ∧ TransStrengtheningNarrow`, `StrengthenNarrow.lean` §3):

| statement | its innermost instance | link |
| --- | --- | --- |
| `StrengtheningTarget` / `Strengthening1` | `Strengthening1Inner` (§2) | `Strengthening1Inner.iff_target` |
| `PiDescend` / `TypingStrengthening` (the typing half) | `TypingStrengthening1Inner` (§3) | `TypingStrengthening1Inner.iff_piDescend` |
| `TransStrengtheningNarrow` (the `trans` residual) | `TransStrengtheningNarrowInner` (§4) | `TransStrengtheningNarrowInner.transNarrow` |
| `StrengtheningCanonUninhab` (`StrengthenCanon.lean` §3) | `StrengtheningCanonUninhabInner` (§5) | `StrengtheningCanonUninhabInner.iff_target` |

## The mechanism, in one paragraph

`(.lam A e).liftN n k` is `.lam (A.liftN n k) (e.liftN n (k+1))`: **the λ-abstraction of a lift
is a lift, one binder further out.**  So a stripping at depth `k+1` becomes a stripping at depth
`k` by abstracting every term in sight over the head entry — the two endpoints, the shared type
(`T` becomes `.forallE A T`), and, in the residual, the middle term.  Nothing has to be
*produced* to do this: `Strengthening1`'s own `OnCtx Γ` hypothesis is exactly the `IsType Γ A`
that `lamDF` wants.  Coming back down needs λ-injectivity for conversion, which is §1 — weaken,
apply both sides to `.bvar 0`, β-reduce, and retype through `uniqU`.  For the typing half even
that is unnecessary: `HasType.lam_inv` already returns the body's well-formedness *under* the
binder, which is why §3 is `sorryAx`-free where §1, §2 and §4 are not.

## Honest accounting

* **This is a reformulation, not a reduction in strength.**  Every link is an `iff` (or a pair of
  one-line implications), so no strength is claimed and none is lost.  A prover still faces the
  whole difficulty; what it no longer faces is a position quantifier and an induction over
  `Ctx.LiftN`.  For a *refutation* it is worth more: the counterexample search space loses a
  dimension, and by §5 the target is now a single sentence — *adding `∀ (α : Sort u), α` as the
  innermost hypothesis of a well-formed context, at a level where it has no inhabitant, is
  conservative for conversion.*
* **It does not empty the prefix.**  `Γ` below the entry stays quantified.  Moving a closed entry
  down past `Γ` is context *exchange*, and exchange in this tree costs one `HasType.weakN_iff`
  per swapped binder (`Verify/Typing/ProjSkip.lean:54`) — i.e. the hole itself.  So `Γ = []` is
  **not** a normal form of this statement, and the obvious next narrowing is circular.
* **It does not separate the two halves.**  §5's capstone is the round-5 decomposition with both
  conjuncts replaced; which of the two is the harder one is untouched.
* §6's `liftN_one_not_inner` is the properness control (working rule 5): the innermost class is a
  *proper* subclass of the strippings, so §2–§4 are not trivial directions read backwards.
* **Bound 1 for the inner residual is checked, not inherited** (§7): `StrengthenAudit.lean` §5's
  satisfiability witness is already at `n = 1`, `k = 0`, `Γ = []`, so §4's restriction has not
  narrowed the residual into vacuity.  This version is `sorryAx`-free (cone 793) where the
  original is not (3456), because it drops the `NeutralTyNL` and not-a-Prop conjuncts, which are
  what pull in `IsType.not_lam`.

## Measured cones (`scripts/exists.lean`, population 492 built modules, run after `lake build`)

| declaration | arity | cone | reaches `weakN_iff` | holes reached |
| --- | --- | --- | --- | --- |
| `TypingStrengthening1Inner.typingStrengthening1` (§3) | 4 | 3363 | no | **none — `sorryAx`-free** |
| `IsDefEqU.lamDF_inv` (§1) | 9 | 3486 | no | `forallE_inv_stratified` |
| `Strengthening1Inner.strengthening1` (§2) | 4 | 3490 | no | `forallE_inv_stratified` |
| `TransStrengtheningNarrowInner.transNarrow` (§4) | 4 | 3496 | no | `forallE_inv_stratified` |
| `StrengtheningCanonUninhabInner.iff_target` (§5) | 3 | 3550 | no | `forallE_inv_stratified` |
| `TypingStrengthening1Inner.iff_piDescend` (§3) | 3 | 3671 | no | both |
| `StrengtheningTarget.iff_inner` (§5) | 3 | 3730 | no | both |
| `liftN_one_not_inner` (§6, properness) | 0 | 230 | no | **none** |
| `transStrengtheningNarrowInner_hyps_satisfiable` (§7, bound 1) | 0 | 793 | no | **none** |

Baseline in the same run: round 5's `StrengtheningTarget.iff_piDescend_narrow` carries the same
two holes, and `addDecl.WF_honest` has arity 6, cone 20433 and exactly eight holes.  **Nothing
here reaches `IsDefEqU.weakN_iff`**, so the collapse is not circular with the statement it is
about; the single hole the conversion-side results do carry,
`IsDefEqU.forallE_inv_stratified`, enters through `IsDefEq.uniq` and is one of the tree's two
pervasive non-circular holes.

This file adds no `sorry`, no `axiom`, no `native_decide` and no `@[implemented_by]`.
Full `lake build`: green, 1678 jobs; census 13 holes; guards 1/2/3 ✓.
-/
namespace Lean4Lean
namespace VEnv

variable {env : VEnv} {U : Nat}

/-! ## 1. λ-injectivity for conversion -/

variable! (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U)) in
theorem IsDefEqU.lamDF_inv {A e1 e2 : VExpr} (H : env.IsDefEqU U Γ (.lam A e1) (.lam A e2)) :
    env.IsDefEqU U (A::Γ) e1 e2 := by
  obtain ⟨C, hC⟩ := H
  obtain ⟨⟨u, hA⟩, B₁, hb₁⟩ := HasType.lam_inv henv.ordered hΓ hC.hasType.1
  obtain ⟨-, B₂, hb₂⟩ := HasType.lam_inv henv.ordered hΓ hC.hasType.2
  have hl1 : env.HasType U Γ (.lam A e1) (.forallE A B₁) := .lamDF hA hb₁
  have hC' : env.IsDefEq U Γ (.lam A e1) (.lam A e2) (.forallE A B₁) :=
    (IsDefEq.uniqU henv hΓ hC.hasType.1 hl1).defeqDF henv hΓ hC
  have hΓ' : OnCtx (A::Γ) (env.IsType U) := ⟨hΓ, _, hA⟩
  have hb0 : env.HasType U (A::Γ) (.bvar 0) A.lift := .bvar .zero
  -- the two β steps
  have hbeta : ∀ {e B : VExpr}, env.HasType U (A::Γ) e B →
      env.IsDefEq U (A::Γ) (.app (VExpr.lam A e).lift (.bvar 0)) e B := by
    intro e B he
    have hw : env.HasType U (A.lift::A::Γ) (e.liftN 1 1) (B.liftN 1 1) :=
      he.weakN henv.ordered (Ctx.LiftN.one.succ (A := A))
    have := IsDefEq.beta hw hb0
    rw [VExpr.instN_bvar0, VExpr.instN_bvar0] at this
    exact this
  have happ := (hC'.weak (B := A) henv.ordered).appDF (A := A.lift) hb0
  rw [VExpr.instN_bvar0] at happ
  exact ⟨_, IsDefEq.trans_r henv hΓ' ((hbeta hb₁).symm.trans happ) (hbeta hb₂)⟩

end VEnv
end Lean4Lean

namespace Lean4Lean
namespace VEnv

variable {env : VEnv} {U : Nat}

/-! ## 2. The position quantifier collapses -/

/-- **The target at the innermost position.**  `Strengthening1` with `k = 0`, i.e. the stripped
entry is the *head* of the larger context.  `OnCtx (X::Γ)` is `Strengthening1`'s two context
hypotheses at this instance: it is `OnCtx Γ` together with `IsType Γ X`. -/
def Strengthening1Inner (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {X e1 e2 : VExpr}, OnCtx (X::Γ) (env.IsType U) →
    env.IsDefEqU U (X::Γ) e1.lift e2.lift → env.IsDefEqU U Γ e1 e2

/-- The trivial direction. -/
theorem Strengthening1.inner (H : Strengthening1 env U) : Strengthening1Inner env U :=
  fun hΓ' h => H .one hΓ'.1 hΓ' h

variable! (henv : VEnv.WF env) in
/-- **The innermost position is enough.**  Induction on the lifting witness.  In the `succ`
case the conversion is λ-abstracted over the head entry — `(.lam A e).liftN 1 (k+1)` *is*
`.lam (A.liftN 1 k) (e.liftN 1 (k+1))`, so the abstraction of a lift is a lift — the induction
hypothesis strips the entry one binder further out, and §1's λ-injectivity puts the binder back.
No typing has to be produced: `Strengthening1`'s own `OnCtx Γ` hypothesis supplies the domain's
`IsType` downstairs, which is the one thing the abstraction needs. -/
theorem Strengthening1Inner.strengthening1 (H : Strengthening1Inner env U) :
    Strengthening1 env U := by
  intro k Γ Γ' e1 e2 W
  induction W generalizing e1 e2 with
  | @zero Γ As h =>
    match As, h with
    | [X], _ => exact fun _ hΓ' h => H hΓ' h
  | @succ k Γ₁ Γ₁' A W ih =>
    intro hΓ hΓ' h
    obtain ⟨T, hT⟩ := h
    obtain ⟨u, hAu⟩ := hΓ'.2
    have hlam : env.IsDefEqU U Γ₁' ((VExpr.lam A e1).liftN 1 k) ((VExpr.lam A e2).liftN 1 k) :=
      ⟨_, .lamDF hAu hT⟩
    exact (ih hΓ.1 hΓ'.1 hlam).lamDF_inv henv hΓ.1

variable! (henv : VEnv.WF env) in
theorem Strengthening1Inner.iff_strengthening1 :
    Strengthening1Inner env U ↔ Strengthening1 env U :=
  ⟨fun H => H.strengthening1 henv, fun H => H.inner⟩

variable! (henv : VEnv.WF env) in
/-- **The hole is its own instance at the innermost position.** -/
theorem Strengthening1Inner.iff_target :
    Strengthening1Inner env U ↔ StrengtheningTarget env U :=
  (Strengthening1Inner.iff_strengthening1 henv).trans (Strengthening1.iff_target henv)

end VEnv
end Lean4Lean

namespace Lean4Lean
namespace VEnv

variable {env : VEnv} {U : Nat}

/-! ## 3. The typing half collapses too, and more cheaply

The same λ-abstraction, with `HasType.lam_inv` in place of §1: the typing half needs no
injectivity, because `lam_inv` already returns the body's well-formedness under the binder. -/

/-- **The typing half at the innermost position.** -/
def TypingStrengthening1Inner (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {X e A : VExpr}, OnCtx (X::Γ) (env.IsType U) →
    env.HasType U (X::Γ) e.lift A → VExpr.WF env U Γ e

/-- The trivial direction. -/
theorem TypingStrengthening1.inner (H : TypingStrengthening1 env U) :
    TypingStrengthening1Inner env U := fun hΓ' h => H .one hΓ'.1 hΓ' h

variable! (henv : VEnv.WF env) in
/-- **The innermost position is enough for the typing half.** -/
theorem TypingStrengthening1Inner.typingStrengthening1 (H : TypingStrengthening1Inner env U) :
    TypingStrengthening1 env U := by
  intro k Γ Γ' e A W
  induction W generalizing e A with
  | @zero Γ As h =>
    match As, h with
    | [X], _ => exact fun _ hΓ' h => H hΓ' h
  | @succ k Γ₁ Γ₁' A₁ W ih =>
    intro hΓ hΓ' h
    obtain ⟨u, hAu⟩ := hΓ'.2
    have hlam : env.HasType U Γ₁' ((VExpr.lam A₁ e).liftN 1 k)
        (.forallE (A₁.liftN 1 k) A) := .lamDF hAu h
    exact ((ih hΓ.1 hΓ'.1 hlam).lam_inv henv.ordered hΓ.1).2

variable! (henv : VEnv.WF env) in
theorem TypingStrengthening1Inner.iff_typing :
    TypingStrengthening1Inner env U ↔ TypingStrengthening env U :=
  ⟨fun H => TypingStrengthening1.typing henv (H.typingStrengthening1 henv),
   fun H => TypingStrengthening1.inner (TypingStrengthening.one H)⟩

variable! (henv : VEnv.WF env) in
/-- **The typing half of the hole is exactly its own innermost instance.**  `PiDescend` is the
typing half (`TypingStrengthening.iff_piDescend`), so this is the first of the hole's two
conjuncts, restated with no position quantifier. -/
theorem TypingStrengthening1Inner.iff_piDescend :
    TypingStrengthening1Inner env U ↔ PiDescend env U :=
  (TypingStrengthening1Inner.iff_typing henv).trans (TypingStrengthening.iff_piDescend henv)

end VEnv
end Lean4Lean

namespace Lean4Lean

/-! ## 4. The `trans` residual collapses as well -/

/-- The λ-abstracted middle term is not a lift either — the companion of
`StrengthenPiProp.lean`'s `not_skips_eta` for the abstraction step. -/
theorem VExpr.not_skips_lam {X b : VExpr} {n k : Nat} (h : ¬ b.Skips n (k+1)) :
    ¬ (VExpr.lam X b).Skips n k := by
  intro hs
  obtain ⟨c, hc⟩ := VExpr.skips_iff_exists.1 hs
  obtain ⟨_, _, _, _, rfl⟩ := VExpr.liftN_eq_lam hc.symm
  exact h .liftN

namespace VEnv

variable {env : VEnv} {U : Nat}

/-- **The `trans` residual at the innermost position.**  `TransStrengtheningNarrow` with `k = 0`;
`n` is left quantified, as there. -/
def TransStrengtheningNarrowInner (env : VEnv) (U : Nat) : Prop :=
  ∀ {n : Nat} {Γ Γ' : List VExpr} {e1 e2 b T : VExpr}, Ctx.LiftN n 0 Γ Γ' →
    OnCtx Γ (env.IsType U) → OnCtx Γ' (env.IsType U) →
    ¬ b.Skips n 0 → env.HasType U Γ e1 T → VExpr.WF env U Γ e2 →
    env.IsDefEq U Γ' (e1.liftN n 0) b (T.liftN n 0) →
    env.IsDefEq U Γ' b (e2.liftN n 0) (T.liftN n 0) →
    env.IsDefEqU U Γ e1 e2

/-- The trivial direction. -/
theorem TransStrengtheningNarrow.inner (H : TransStrengtheningNarrow env U) :
    TransStrengtheningNarrowInner env U := fun W => H W

variable! (henv : VEnv.WF env) in
/-- **The innermost position is enough for the `trans` residual.**  Abstracting all three terms
over the head binder keeps every hypothesis: the two lifted endpoints stay lifted, the shared
type `T` becomes `.forallE A T` downstairs, the endpoint typings are one `lamDF` each, and the
middle term stays a non-lift by `VExpr.not_skips_lam`. -/
theorem TransStrengtheningNarrowInner.transNarrow (H : TransStrengtheningNarrowInner env U) :
    TransStrengtheningNarrow env U := by
  intro n k Γ Γ' e1 e2 b T W
  induction W generalizing e1 e2 b T with
  | zero As h => exact fun hΓ hΓ' => H (.zero As h) hΓ hΓ'
  | @succ k Γ₁ Γ₁' A₁ W ih =>
    intro hΓ hΓ' hb hT he2 h1 h2
    obtain ⟨u, hAu⟩ := hΓ'.2
    obtain ⟨uA, hA⟩ := hΓ.2
    obtain ⟨B, hB⟩ := he2
    refine (ih hΓ.1 hΓ'.1 (VExpr.not_skips_lam hb) (.lamDF hA hT)
      ⟨_, .lamDF hA hB⟩ (.lamDF hAu h1) (.lamDF hAu h2)).lamDF_inv henv hΓ.1

end VEnv
end Lean4Lean

namespace Lean4Lean
namespace VEnv

variable {env : VEnv} {U : Nat}

/-! ## 5. The capstone, and the canonical entry at the innermost position -/

variable! (henv : VEnv.WF env) in
/-- **The hole, with no position quantifier in either conjunct.**  Round 5's
`StrengtheningTarget.iff_piDescend_narrow` with both halves replaced by their innermost
instances. -/
theorem StrengtheningTarget.iff_inner :
    StrengtheningTarget env U ↔
      TypingStrengthening1Inner env U ∧ TransStrengtheningNarrowInner env U := by
  refine (StrengtheningTarget.iff_piDescend_narrow henv).trans (and_congr ?_ ?_)
  · exact (TypingStrengthening1Inner.iff_piDescend henv).symm
  · exact ⟨TransStrengtheningNarrow.inner, fun H => H.transNarrow henv⟩

/-- **The target at the innermost position, with the canonical entry.** -/
def StrengtheningCanonInner (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {e1 e2 : VExpr} {u : VLevel}, u.WF U → OnCtx Γ (env.IsType U) →
    env.IsDefEqU U (bigFalse u :: Γ) e1.lift e2.lift → env.IsDefEqU U Γ e1 e2

/-- **…and with the entry also uninhabited.**  This is the crispest form the statement has:
*adding `∀ (α : Sort u), α` as the innermost hypothesis of a well-formed context, at a level
where it has no inhabitant, is conservative for conversion.*  No position, no entry and no
prefix-insertion data are quantified beyond the context itself. -/
def StrengtheningCanonUninhabInner (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {e1 e2 : VExpr} {u : VLevel}, u.WF U → OnCtx Γ (env.IsType U) →
    (∀ t, ¬ env.HasType U Γ t (bigFalse u)) →
    env.IsDefEqU U (bigFalse u :: Γ) e1.lift e2.lift → env.IsDefEqU U Γ e1 e2

theorem Strengthening1Inner.canonInner (H : Strengthening1Inner env U) :
    StrengtheningCanonInner env U := fun hu hΓ h => H ⟨hΓ, bigFalse_isType hu⟩ h

theorem Strengthening1Inner.canonUninhabInner (H : Strengthening1Inner env U) :
    StrengtheningCanonUninhabInner env U := fun hu hΓ _ h => H ⟨hΓ, bigFalse_isType hu⟩ h

variable! (henv : VEnv.WF env) in
/-- **The canonical uninhabited innermost entry is the whole statement.**  `canon_swap`
(`StrengthenCanon.lean` §3) preserves the depth `k`, so it maps the innermost class into itself;
the inhabited case is closed by `IsDefEqU.strengthen_of_instN`, the proved half. -/
theorem StrengtheningCanonUninhabInner.strengthening1Inner
    (H : StrengtheningCanonUninhabInner env U) : Strengthening1Inner env U := by
  intro Γ X e1 e2 hΓ' h
  obtain ⟨u, Γ'', Γ₀, hu, hY, _, hΓ'', h2⟩ :=
    canon_swap henv.ordered (Ctx.LiftN.one (A := X)) hΓ'.1 hΓ' h
  cases hY
  by_cases hinh : ∃ t, env.HasType U Γ t (bigFalse u)
  · obtain ⟨t, ht⟩ := hinh
    exact IsDefEqU.strengthen_of_instN henv.ordered (Ctx.Ins.zero.instN t) ht h2
  · exact H hu hΓ'.1 (fun t ht => hinh ⟨t, ht⟩) h2

variable! (henv : VEnv.WF env) in
theorem StrengtheningCanonUninhabInner.iff_target :
    StrengtheningCanonUninhabInner env U ↔ StrengtheningTarget env U :=
  ⟨fun H => Strengthening1.target henv
      (Strengthening1Inner.strengthening1 henv (H.strengthening1Inner henv)),
   fun H => Strengthening1Inner.canonUninhabInner
      (Strengthening1.inner (Strengthening.one (StrengtheningTarget.strengthening H)))⟩

variable! (henv : VEnv.WF env) in
theorem StrengtheningCanonInner.iff_target :
    StrengtheningCanonInner env U ↔ StrengtheningTarget env U :=
  ⟨fun H => (StrengtheningCanonUninhabInner.iff_target henv).1 (fun hu hΓ _ h => H hu hΓ h),
   fun H => Strengthening1Inner.canonInner
      (Strengthening1.inner (Strengthening.one (StrengtheningTarget.strengthening H)))⟩

/-! ## 6. Controls -/

/-- **The restriction is proper.**  A well-formed one-entry stripping at depth 1 whose larger
context is not the smaller one with an entry pushed on the front: so the innermost class is a
*proper* subclass of the strippings, and §2–§4 are not the trivial directions read backwards. -/
theorem liftN_one_not_inner :
    Ctx.LiftN 1 1 [VExpr.sort .zero] [VExpr.sort .zero, VExpr.sort (.succ .zero)] ∧
      ∀ X : VExpr,
        [VExpr.sort .zero, VExpr.sort (.succ .zero)] ≠ [X, VExpr.sort (.zero : VLevel)] :=
  ⟨(Ctx.LiftN.zero (Γ := []) [VExpr.sort (.succ .zero)]).succ (A := .sort .zero), fun _ => nofun⟩

/-- The innermost class is nonempty at every level, so the inner statements are not vacuous
for lack of an instance of their lifting premise. -/
theorem inner_premises {u : VLevel} {Γ : List VExpr} (hu : u.WF U)
    (hΓ : OnCtx Γ (env.IsType U)) :
    Ctx.LiftN 1 0 Γ (bigFalse u :: Γ) ∧ OnCtx (bigFalse u :: Γ) (env.IsType U) :=
  ⟨.one, hΓ, bigFalse_isType hu⟩

end VEnv
end Lean4Lean

namespace Lean4Lean
namespace VEnv

/-- **Bound 1 for the inner residual: its hypotheses are jointly satisfiable at `k = 0`.**
`StrengthenAudit.lean` §5's witness is already an innermost one (`n = 1`, `k = 0`, `Γ = []`), so
§4's restriction has not narrowed the residual into vacuity.  Without this, "the residual holds
at `k = 0`" would be compatible with there being no `k = 0` instance to hold at. -/
theorem transStrengtheningNarrowInner_hyps_satisfiable :
    ∃ (env : VEnv) (U n : Nat) (Γ Γ' : List VExpr) (e1 e2 b T : VExpr),
      VEnv.WF env ∧ Ctx.LiftN n 0 Γ Γ' ∧ OnCtx Γ (env.IsType U) ∧
      OnCtx Γ' (env.IsType U) ∧ ¬ b.Skips n 0 ∧
      env.HasType U Γ e1 T ∧ VExpr.WF env U Γ e2 ∧
      env.IsDefEq U Γ' (e1.liftN n 0) b (T.liftN n 0) ∧
      env.IsDefEq U Γ' b (e2.liftN n 0) (T.liftN n 0) ∧ e1 ≠ e2 :=
  ⟨VEnv.empty, 0, 1, [], [VExpr.sort .zero], auditE1, auditE2, auditB, auditT,
   ⟨[], .empty⟩, .one, trivial, audit_onCtx, auditB_not_skips,
   auditE1_hasType, ⟨_, auditE2_hasType⟩, audit_premise₁, audit_premise₂,
   by simp [auditE1, auditE2]⟩

end VEnv
end Lean4Lean
