import Lean4Lean.Theory.Typing.WeakNAttack

/-!
# The block size collapses too: the strengthening hole is about **one** added entry

Round 11 of the `VEnv.IsDefEqU.weakN_iff` line (`Theory/Typing/UniqueTyping.lean:172`).
**Nothing here closes the hole and nothing here removes a `sorry`.**

Round 10 (`WeakNAttack.lean`) collapsed the *position* quantifier `k`: the target and both
conjuncts of the standing decomposition are equivalent to their instances at the innermost
context position.  What it left standing in the `trans` residual is the **block size** `n`:
`TransStrengtheningNarrowInner` still reads `Ctx.LiftN n 0 Γ Γ'`, i.e. *`n` entries at once*,
while the target itself has been at `n = 1` since `Strengthening1` (`Strengthen.lean`:526).
That asymmetry is surplus, and this file removes it.

## The observation

`Strengthening.of_typing_narrow` (`StrengthenNarrow.lean`:155) is an induction on the
**conversion derivation**, not on the lifting witness.  Across all twelve rules the block size
`n` is never touched: `lamDF` and `forallEDF` push `W` to `W.succ`, which changes `k` and keeps
`n`; every other case passes `W` through unchanged; and the `trans` case applies the residual at
*exactly* the `W` of the goal.  So the reduction is really a family of reductions, one per block
size, and the `∀ n` in `TransStrengtheningNarrow` is never used at an `n` other than the one in
the conclusion.  §2's `Strengthening.of_typing_narrowBlock` is that statement — the original proof
text with `n` moved out of the motive — and `of_typing_narrow` is its `∀ n` corollary (§2), so
nothing is lost.

Combining with round 10's `k`-collapse, which is itself an induction that keeps `n` fixed:

* `TransStrengtheningNarrowInner1` (§3) — **one** entry, at the **innermost** position:
  no block size, no position, no lifting witness.  `Ctx.LiftN` has disappeared from the
  statement; what is left is `X :: Γ` and `VExpr.lift`.
* `StrengtheningTarget.iff_inner1` (§4) — the hole is exactly
  `TypingStrengthening1Inner ∧ TransStrengtheningNarrowInner1`, the first conjunct being the
  half round 10 measured `sorryAx`-free.

So the whole of `IsDefEqU.weakN_iff` now rests on: *given a well-formed `X :: Γ`, a conversion
`e1↑ ≡ b ≡ e2↑` at a lifted type whose middle term `b` genuinely mentions `bvar 0`, and types
downstairs for both endpoints, conclude `e1 ≡ e2` in `Γ`.*

## The prefix, and what last round got wrong about it

Round 10's honest accounting says `Γ` cannot be emptied because "moving a closed entry down past
`Γ` is context *exchange*, and exchange in this tree costs one `HasType.weakN_iff` per swapped
binder (`Verify/Typing/ProjSkip.lean:54`)".  The price is real and the citation is real, but it
is **not a price for exchange**: `VExpr.SwapCtx` (`ProjSkip.lean:321`) is
```
  | nil | keep : SwapCtx b B (F::Fs) (F::Fs') | swap : SwapCtx b B (F::Fs) (swapUnit::Fs')
```
— it *replaces an unused binder's type by `VExpr.swapUnit`, in place*.  Nothing moves; that is
binder **retyping**, and its `weakN_iff` price is a genuine strengthening price (one must know
the term does not use the binder).  `grep -rn "exchange\|Perm"` over `Lean4Lean/`: the tree has
**no context-exchange lemma at all**, so exchange has never been priced here.  §5 prices it, and
§6 records what emptying the prefix would then buy.

## What is *not* here

The residual itself.  §3 is a restatement at `n = 1`, `k = 0`; it is not weaker in strength
(§4 is an `iff`), only smaller.  No route foreclosed in `docs/handoff-weakn.md` is reopened.

## Measured cones (`scripts/exists.lean`, population 493 built modules, run after `lake build`)

| declaration | arity | cone | reaches `weakN_iff` | holes reached |
| --- | --- | --- | --- | --- |
| `IsDefEqU.exchangeClosed` (§5) | 12 | 3232 | no | **none — `sorryAx`-free** |
| `bottom_package` (§5) | 9 | 3490 | no | `forallE_inv_stratified` |
| `strengthen_of_bottom` (§5) | 12 | 3497 | no | `forallE_inv_stratified` |
| `TransStrengtheningNarrowInner1.block1` (§3) | 4 | 3497 | no | `forallE_inv_stratified` |
| `StrengtheningCanon0.canonInner` (§6) | 4 | 3502 | no | `forallE_inv_stratified` |
| `StrengtheningCanon0.iff_target` (§6) | 3 | 3563 | no | `forallE_inv_stratified` |
| `Strengthening.of_typing_narrowBlock` (§2) | 6 | 3662 | no | both |
| `StrengtheningTarget.iff_inner1` (§4) | 3 | 3708 | no | both |
| `StrengtheningCanon0.iff_inner1` (§7) | 3 | 3765 | no | both |

Baselines in the same run: round 10's `TransStrengtheningNarrowInner.transNarrow` 3496 and
`StrengtheningTarget.iff_inner` 3730; `IsDefEqU.weakN_iff` itself arity 11, cone 3231, own value a
hole.  **Nothing here reaches `IsDefEqU.weakN_iff`**, so neither the block-size collapse nor the
exchange is circular with the statement it is about.  Note the first row: **exchange of a closed
entry carries no hole at all**, and its cone (3232) is one declaration wider than the hole's own
(3231) — it is `weakN` plus `instN` plus two rewrites and nothing else.

`StrengtheningCanon0.iff_target` carries only `forallE_inv_stratified`; the second pervasive hole
`WF.rigidShapeUniqNS` enters only through the *decomposition* rows, i.e. through round 5's
`iff_piDescend_narrow`, not through this file's own reductions.

This file adds no `sorry`, no `axiom`, no `native_decide` and no `@[implemented_by]`.
Full `lake build`: green, 1679 jobs (1678 + this module); census 13 holes; guards 1/2/3 ✓.
-/

namespace Lean4Lean
namespace VEnv

open _root_.Lean4Lean.VExpr

variable {env : VEnv} {U : Nat} {n : Nat}

/-! ## 1. The two statements with the block size fixed -/

/-- `Strengthening` at a **fixed** block size `n`.  `StrengtheningBlock 1` is `Strengthening1`
(`Strengthen.lean`:526) on the nose. -/
def StrengtheningBlock (n : Nat) (env : VEnv) (U : Nat) : Prop :=
  ∀ {k : Nat} {Γ Γ' : List VExpr} {e1 e2 : VExpr}, Ctx.LiftN n k Γ Γ' →
    OnCtx Γ (env.IsType U) → OnCtx Γ' (env.IsType U) →
    env.IsDefEqU U Γ' (e1.liftN n k) (e2.liftN n k) → env.IsDefEqU U Γ e1 e2

/-- `TransStrengtheningNarrow` (`StrengthenNarrow.lean`:130) at a **fixed** block size `n`. -/
def TransStrengtheningNarrowBlock (n : Nat) (env : VEnv) (U : Nat) : Prop :=
  ∀ {k : Nat} {Γ Γ' : List VExpr} {e1 e2 b T : VExpr}, Ctx.LiftN n k Γ Γ' →
    OnCtx Γ (env.IsType U) → OnCtx Γ' (env.IsType U) →
    ¬ b.Skips n k → env.HasType U Γ e1 T → VExpr.WF env U Γ e2 →
    env.IsDefEq U Γ' (e1.liftN n k) b (T.liftN n k) →
    env.IsDefEq U Γ' b (e2.liftN n k) (T.liftN n k) →
    env.IsDefEqU U Γ e1 e2

/-- The block-size-1 instance of the target *is* `Strengthening1`, definitionally. -/
theorem StrengtheningBlock.iff_one : StrengtheningBlock 1 env U ↔ Strengthening1 env U := Iff.rfl

theorem StrengtheningBlock.of (H : Strengthening env U) : StrengtheningBlock n env U := fun W => H W

theorem TransStrengtheningNarrowBlock.of (H : TransStrengtheningNarrow env U) :
    TransStrengtheningNarrowBlock n env U := fun W => H W

theorem TransStrengtheningNarrowBlock.all (H : ∀ n, TransStrengtheningNarrowBlock n env U) :
    TransStrengtheningNarrow env U := fun {n _ _ _ _ _ _ _} W => H n W

/-! ## 2. The reduction, one block size at a time

`StrengthenNarrow.lean` §2's proof text with `n` moved out of the induction motive — the only
change.  That it type-checks *is* the observation: no case of the conversion induction changes
the block size. -/

variable! (henv : VEnv.WF env) in
theorem Strengthening.of_typing_narrowBlock (HT : TypingStrengthening env U)
    (Hn : TransStrengtheningNarrowBlock n env U) : StrengtheningBlock n env U := by
  suffices H : ∀ {Γ' a b A}, env.IsDefEq U Γ' a b A → ∀ {k Γ e1 e2}, Ctx.LiftN n k Γ Γ' →
      OnCtx Γ (env.IsType U) → OnCtx Γ' (env.IsType U) →
      e1.liftN n k = a → e2.liftN n k = b → env.IsDefEqU U Γ e1 e2 by
    intro k Γ Γ' e1 e2 W hΓ hΓ' h
    exact have ⟨_, h⟩ := h; H h W hΓ hΓ' rfl rfl
  intro Γ' a b A H
  induction H with
  | bvar h =>
    intro k Γ e1 e2 W hΓ hΓ' eq1 eq2
    cases liftN_inj.1 (eq1.trans eq2.symm)
    obtain ⟨j, rfl, rfl⟩ := VExpr.liftN_eq_bvar eq1
    exact HT W hΓ hΓ' (IsDefEq.bvar h)
  | symm _ ih => exact fun W hΓ hΓ' eq1 eq2 => (ih W hΓ hΓ' eq2 eq1).symm
  | @trans _ _ mid _ _ h1 h2 ih1 ih2 =>
    intro k Γ e1 e2 W hΓ hΓ' eq1 eq2
    by_cases hmid : mid.Skips n k
    · -- the middle term *is* a lift: the two induction hypotheses `of_typing` throws away
      obtain ⟨b₀, rfl⟩ := VExpr.skips_iff_exists.1 hmid
      exact (ih1 W hΓ hΓ' eq1 rfl).trans henv hΓ (ih2 W hΓ hΓ' rfl eq2)
    · -- the middle term is not a lift: the residual, at a lifted type
      subst eq1; subst eq2
      have ⟨T, hT⟩ := HT W hΓ hΓ' h1.hasType.1
      have uu := (hT.weakN henv W).uniqU henv hΓ' h1
      exact Hn W hΓ hΓ' hmid hT (HT W hΓ hΓ' h2.hasType.2)
        (IsDefEqU.defeqDF henv hΓ' uu.symm h1) (IsDefEqU.defeqDF henv hΓ' uu.symm h2)
  | sortDF h1 h2 h3 =>
    intro k Γ e1 e2 W hΓ hΓ' eq1 eq2
    cases VExpr.liftN_eq_sort eq1; cases VExpr.liftN_eq_sort eq2
    exact ⟨_, .sortDF h1 h2 h3⟩
  | constDF h1 h2 h3 h4 h5 =>
    intro k Γ e1 e2 W hΓ hΓ' eq1 eq2
    cases VExpr.liftN_eq_const eq1; cases VExpr.liftN_eq_const eq2
    exact ⟨_, .constDF h1 h2 h3 h4 h5⟩
  | appDF h1 h2 ih1 ih2 =>
    intro k Γ e1 e2 W hΓ hΓ' eq1 eq2
    obtain ⟨g, b, rfl, rfl, rfl⟩ := VExpr.liftN_eq_app eq1
    obtain ⟨g', b', rfl, rfl, rfl⟩ := VExpr.liftN_eq_app eq2
    have wf : VExpr.WF env U Γ (.app g b) := HT W hΓ hΓ'
      (show env.HasType U _ ((VExpr.app g b).liftN n k) _ from .appDF h1.hasType.1 h2.hasType.1)
    have ⟨A₀, B₀, hg, hb⟩ := wf.app_inv henv hΓ
    exact ⟨_, .appDF ((ih1 W hΓ hΓ' rfl rfl).of_l henv hΓ hg)
      ((ih2 W hΓ hΓ' rfl rfl).of_l henv hΓ hb)⟩
  | lamDF h1 h2 ih1 ih2 =>
    intro k Γ e1 e2 W hΓ hΓ' eq1 eq2
    obtain ⟨C, d, rfl, rfl, rfl⟩ := VExpr.liftN_eq_lam eq1
    obtain ⟨C', d', rfl, rfl, rfl⟩ := VExpr.liftN_eq_lam eq2
    have wf : VExpr.WF env U Γ (.lam C d) := HT W hΓ hΓ'
      (show env.HasType U _ ((VExpr.lam C d).liftN n k) _ from .lamDF h1.hasType.1 h2.hasType.1)
    have ⟨⟨u₀, hC⟩, B₀, hd⟩ := wf.lam_inv henv hΓ
    have hΓC : OnCtx (C::Γ) (env.IsType U) := ⟨hΓ, _, hC⟩
    have hbody := (ih2 W.succ hΓC ⟨hΓ', _, h1.hasType.1⟩ rfl rfl).of_l henv hΓC hd
    exact ⟨_, .lamDF ((ih1 W hΓ hΓ' rfl rfl).of_l henv hΓ hC) hbody⟩
  | forallEDF h1 h2 ih1 ih2 =>
    intro k Γ e1 e2 W hΓ hΓ' eq1 eq2
    obtain ⟨C, d, rfl, rfl, rfl⟩ := VExpr.liftN_eq_forallE eq1
    obtain ⟨C', d', rfl, rfl, rfl⟩ := VExpr.liftN_eq_forallE eq2
    have ⟨_, wf⟩ : VExpr.WF env U Γ (.forallE C d) := HT W hΓ hΓ'
      (show env.HasType U _ ((VExpr.forallE C d).liftN n k) _ from
        .forallEDF h1.hasType.1 h2.hasType.1)
    have ⟨⟨u₀, hC⟩, v₀, hd⟩ := HasType.forallE_inv henv wf
    have hΓC : OnCtx (C::Γ) (env.IsType U) := ⟨hΓ, _, hC⟩
    have hbody := (ih2 W.succ hΓC ⟨hΓ', _, h1.hasType.1⟩ rfl rfl).of_l henv hΓC hd
    exact ⟨_, .forallEDF ((ih1 W hΓ hΓ' rfl rfl).of_l henv hΓ hC) hbody⟩
  | defeqDF _ _ _ ih2 => exact fun W hΓ hΓ' eq1 eq2 => ih2 W hΓ hΓ' eq1 eq2
  | beta h1 h2 _ _ =>
    intro k Γ e1 e2 W hΓ hΓ' eq1 eq2
    obtain ⟨x, a₀, rfl, eqx, rfl⟩ := VExpr.liftN_eq_app eq1
    obtain ⟨A₀, b₀, rfl, rfl, rfl⟩ := VExpr.liftN_eq_lam eqx.symm
    rw [← liftN_inst_hi] at eq2
    cases liftN_inj.1 eq2
    have wf : VExpr.WF env U Γ (.app (.lam A₀ b₀) a₀) := HT W hΓ hΓ'
      (show env.HasType U _ ((VExpr.app (.lam A₀ b₀) a₀).liftN n k) _ from
        (IsDefEq.beta h1 h2).hasType.1)
    have ⟨A', B', hlam, ha⟩ := wf.app_inv henv hΓ
    have ⟨⟨u, hA₀⟩, B₀, hb₀⟩ := hlam.lam_inv henv hΓ
    have uu := (IsDefEq.lamDF hA₀ hb₀).uniqU henv hΓ hlam
    have ⟨⟨u', hAA'⟩, _⟩ := uu.forallE_inv henv hΓ
    exact ⟨_, .beta hb₀ (ha.defeqU_r henv hΓ ⟨_, hAA'.symm⟩)⟩
  | eta h1 _ =>
    intro k Γ e1 e2 W hΓ hΓ' eq1 eq2
    subst eq2
    obtain ⟨C, d, rfl, rfl, eqd⟩ := VExpr.liftN_eq_lam eq1
    obtain ⟨x, y, rfl, eqx, eqy⟩ := VExpr.liftN_eq_app eqd.symm
    obtain ⟨j, rfl, hj⟩ := VExpr.liftN_eq_bvar eqy.symm
    cases VExpr.liftVar_eq_zero hj.symm
    rw [lift_liftN'] at eqx
    cases liftN_inj.1 eqx
    have heta := IsDefEq.eta h1
    rw [lift_liftN'] at heta
    have wf : VExpr.WF env U Γ (.lam C (.app e2.lift (.bvar 0))) := HT W hΓ hΓ'
      (show env.HasType U _ ((VExpr.lam C (.app e2.lift (.bvar 0))).liftN n k) _ from
        heta.hasType.1)
    have ⟨⟨u₀, hC⟩, B₀, hbody⟩ := wf.lam_inv henv hΓ
    have hlam : env.HasType U Γ (.lam C (.app e2.lift (.bvar 0))) (.forallE C B₀) :=
      .lamDF hC hbody
    have uu := (hlam.weakN henv W).uniqU henv hΓ' heta
    have h2 := (IsDefEqU.defeqDF henv hΓ' uu.symm heta).hasType.2
    exact ⟨_, .eta (HT.typed henv W hΓ hΓ' h2)⟩
  | proofIrrel h1 h2 h3 _ _ _ =>
    intro k Γ e1 e2 W hΓ hΓ' eq1 eq2
    subst eq1; subst eq2
    have ⟨C, hC1⟩ := HT W hΓ hΓ' h2
    have uu := (hC1.weakN henv W).uniqU henv hΓ' h2
    have hp : env.HasType U _ (C.liftN n k) ((VExpr.sort .zero).liftN n k) :=
      HasType.defeqU_l henv hΓ' uu.symm h1
    have hC2 := HT.typed henv W hΓ hΓ' (HasType.defeqU_r henv hΓ' uu.symm h3)
    exact ⟨_, .proofIrrel (HT.typed henv W hΓ hΓ' hp) hC1 hC2⟩
  | extra h1 h2 h3 =>
    intro k Γ e1 e2 W hΓ hΓ' eq1 eq2
    have ⟨⟨hl, _⟩, hr, _⟩ := henv.ordered.closed.2 h1
    rw [← hl.instL.liftN_eq (n := n) (j := k) (Nat.zero_le _)] at eq1
    rw [← hr.instL.liftN_eq (n := n) (j := k) (Nat.zero_le _)] at eq2
    cases liftN_inj.1 eq1
    cases liftN_inj.1 eq2
    exact ⟨_, .extra h1 h2 h3⟩


variable! (henv : VEnv.WF env) in
/-- **Nothing is lost.**  `StrengthenNarrow.lean`'s `of_typing_narrow` is the `∀ n` corollary. -/
theorem Strengthening.of_typing_narrow' (HT : TypingStrengthening env U)
    (Hn : TransStrengtheningNarrow env U) : Strengthening env U :=
  fun {n _ _ _ _ _} W => Strengthening.of_typing_narrowBlock henv HT (n := n)
    (TransStrengtheningNarrowBlock.of Hn) W

/-! ## 3. The residual with **no** lifting witness at all

`WeakNAttack.lean` §4's `k`-collapse keeps `n` fixed (the abstraction step turns
`Ctx.LiftN n (k+1)` into `Ctx.LiftN n k`), so it applies verbatim at `n = 1`.  At `n = 1` and
`k = 0` the witness is `Ctx.LiftN.one`, which carries no information: the statement is about
`X :: Γ` and `VExpr.lift`, and `Ctx.LiftN` has left the vocabulary. -/

/-- **The `trans` residual, one entry, innermost.**  `TransStrengtheningNarrow` at `n = 1`,
`k = 0`.  `OnCtx (X::Γ)` is the two context hypotheses at this instance. -/
def TransStrengtheningNarrowInner1 (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {X e1 e2 b T : VExpr}, OnCtx (X::Γ) (env.IsType U) →
    ¬ b.Skips 1 0 → env.HasType U Γ e1 T → VExpr.WF env U Γ e2 →
    env.IsDefEq U (X::Γ) e1.lift b T.lift →
    env.IsDefEq U (X::Γ) b e2.lift T.lift →
    env.IsDefEqU U Γ e1 e2

/-- The trivial direction. -/
theorem TransStrengtheningNarrowBlock.inner1 (H : TransStrengtheningNarrowBlock 1 env U) :
    TransStrengtheningNarrowInner1 env U := fun hΓ' => H .one hΓ'.1 hΓ'

variable! (henv : VEnv.WF env) in
/-- **One entry at the innermost position is enough for the whole `trans` residual at block
size 1.**  `WeakNAttack.lean` §4's induction, which never touches the block size. -/
theorem TransStrengtheningNarrowInner1.block1 (H : TransStrengtheningNarrowInner1 env U) :
    TransStrengtheningNarrowBlock 1 env U := by
  intro k Γ Γ' e1 e2 b T W
  induction W generalizing e1 e2 b T with
  | zero As h =>
    match As, h with
    | [X], _ => exact fun _ hΓ' hb hT he2 h1 h2 => H hΓ' hb hT he2 h1 h2
  | @succ k Γ₁ Γ₁' A₁ W ih =>
    intro hΓ hΓ' hb hT he2 h1 h2
    obtain ⟨u, hAu⟩ := hΓ'.2
    obtain ⟨uA, hA⟩ := hΓ.2
    obtain ⟨B, hB⟩ := he2
    exact (ih hΓ.1 hΓ'.1 (VExpr.not_skips_lam hb) (.lamDF hA hT)
      ⟨_, .lamDF hA hB⟩ (.lamDF hAu h1) (.lamDF hAu h2)).lamDF_inv henv hΓ.1

variable! (henv : VEnv.WF env) in
theorem TransStrengtheningNarrowInner1.iff_block1 :
    TransStrengtheningNarrowInner1 env U ↔ TransStrengtheningNarrowBlock 1 env U :=
  ⟨fun H => H.block1 henv, fun H => H.inner1⟩

/-! ## 4. The capstone: the hole is two statements, neither of which mentions `Ctx.LiftN` -/

variable! (henv : VEnv.WF env) in
/-- **The hole, with no position quantifier and no block size.**  Round 10's
`StrengtheningTarget.iff_inner` with its second conjunct's surplus `∀ n` removed.  The first
conjunct is the half round 10 measured `sorryAx`-free
(`TypingStrengthening1Inner.typingStrengthening1`, cone 3363), so the whole of
`IsDefEqU.weakN_iff` is the second. -/
theorem StrengtheningTarget.iff_inner1 :
    StrengtheningTarget env U ↔
      TypingStrengthening1Inner env U ∧ TransStrengtheningNarrowInner1 env U := by
  refine ⟨fun H => ⟨?_, ?_⟩, fun ⟨h1, h2⟩ => ?_⟩
  · exact (TypingStrengthening1Inner.iff_typing henv).2
      (Strengthening.typing (StrengtheningTarget.strengthening H))
  · exact fun hΓ' _ _ _ p1 p2 => H .one hΓ' ⟨_, p1.trans p2⟩
  · exact (Strengthening1.iff_target henv).1 (StrengtheningBlock.iff_one.1
      (Strengthening.of_typing_narrowBlock henv
        ((TypingStrengthening1Inner.iff_typing henv).1 h1) (h2.block1 henv)))

/-! ## 5. Exchange of a closed entry is free, and the prefix empties

Round 10 left this as the named open question.  The answer is **yes, and cheaply**: moving a
*closed* entry from the innermost position to the bottom of the context is
`IsDefEq.weakN` followed by a single `IsDefEq.instN`, with no strengthening anywhere.

The trick is that the permutation `bvar 0 ↦ bvar Γ.length`, `bvar (i+1) ↦ bvar i` — which is
what "move the head entry to the far end" does to terms — is not a new renaming primitive at
all.  It is *substitution of a variable*: `VExpr.inst e (.bvar Γ.length) 0` does exactly that.
So: weaken `X :: Γ` at the bottom to `X :: Γ''` (where `Γ''` is `Γ` with a copy of `X` appended
at the far end), then instantiate `bvar 0` by the *new* copy, which is `bvar Γ.length` in `Γ''`.
Weakening and substitution are both `sorryAx`-free in this tree, and neither is the hole.

`X` closed is exactly what makes this well-formed: the appended copy has to typecheck in `[]`,
and `X.liftN 1 Γ.length = X` is what identifies the head of the weakened context with `X`. -/

/-- The bottom-anchored insertion, with everything the reduction needs, in one induction on the
prefix: the lifting witness, the well-formedness of the enlarged context, the `Lookup` for the
appended copy of `X`, and — the payload — the reduction of strengthening at that witness to
strengthening at the **empty** prefix. -/
theorem bottom_package (henv : VEnv.WF env) {X : VExpr}
    (hX : X.ClosedN 0) (hXT : env.IsType U [] X)
    (H0 : ∀ {e1 e2 : VExpr}, env.IsDefEqU U [X] e1.lift e2.lift → env.IsDefEqU U [] e1 e2) :
    ∀ {Γ : List VExpr}, OnCtx Γ (env.IsType U) →
      ∃ Γ'', Ctx.LiftN 1 Γ.length Γ Γ'' ∧ OnCtx Γ'' (env.IsType U) ∧
        Lookup Γ'' Γ.length X ∧
        ∀ {e1 e2 : VExpr}, env.IsDefEqU U Γ'' (e1.liftN 1 Γ.length) (e2.liftN 1 Γ.length) →
          env.IsDefEqU U Γ e1 e2
  | [], _ => by
    refine ⟨[X], .zero [X], ⟨trivial, hXT⟩, ?_, fun h => H0 h⟩
    have h0 : Lookup [X] 0 X.lift := .zero
    rw [hX.lift_eq] at h0; exact h0
  | A::Γ₁, hΓ => by
    obtain ⟨Γ₁'', W₁, hΓ₁'', hlook, Hstr⟩ := bottom_package henv hX hXT H0 hΓ.1
    obtain ⟨u, hAu⟩ := hΓ.2
    refine ⟨_, W₁.succ, ⟨hΓ₁'', _, hAu.weakN henv.ordered W₁⟩, ?_, ?_⟩
    · have h1 := hlook.succ (A := A.liftN 1 Γ₁.length)
      rw [hX.lift_eq] at h1; exact h1
    intro e1 e2 h
    obtain ⟨T, hT⟩ := h
    have hlam : env.IsDefEqU U Γ₁'' ((VExpr.lam A e1).liftN 1 Γ₁.length)
        ((VExpr.lam A e2).liftN 1 Γ₁.length) := ⟨_, .lamDF (hAu.weakN henv.ordered W₁) hT⟩
    exact (Hstr hlam).lamDF_inv henv hΓ.1

/-- **Exchange of a closed entry is free.**  This is the round's named question, answered as a
lemma: a conversion under a *closed* innermost hypothesis `X` is a conversion in the context
with that hypothesis moved to the far end.  The proof is `IsDefEq.weakN` (append a second copy
of `X` at the bottom) followed by one `IsDefEq.instN` (substitute `bvar 0` by that copy, which
is `bvar Γ.length` there).  The de Bruijn permutation "head entry to the far end" *is*
`VExpr.inst · (.bvar Γ.length) 0`, so no renaming primitive is needed and no strengthening is
used.  `X` closed is what makes the appended copy typecheck in `[]` and makes the head of the
weakened context `X` again (`X.liftN 1 Γ.length = X`). -/
theorem IsDefEqU.exchangeClosed (henv : VEnv.WF env) {X : VExpr} (hX : X.ClosedN 0)
    {Γ Γ'' : List VExpr} (W : Ctx.LiftN 1 Γ.length Γ Γ'')
    (hlook : Lookup Γ'' Γ.length X) {e1 e2 : VExpr}
    (H : env.IsDefEqU U (X::Γ) e1.lift e2.lift) :
    env.IsDefEqU U Γ'' (e1.liftN 1 Γ.length) (e2.liftN 1 Γ.length) := by
  have hW : Ctx.LiftN 1 (Γ.length + 1) (X::Γ) (X::Γ'') := by
    have := W.succ (A := X); rwa [hX.liftN_eq (Nat.zero_le _)] at this
  have hw := H.weakN henv.ordered hW
  rw [← VExpr.lift_liftN' (n := 1), ← VExpr.lift_liftN' (n := 1)] at hw
  have hb : env.HasType U Γ'' (.bvar Γ.length) X := .bvar hlook
  have := hw.instN (Γ₀ := Γ'') (e₀ := .bvar Γ.length) (A₀ := X) henv.ordered .zero hb
  rwa [VExpr.inst_lift, VExpr.inst_lift] at this

/-- **The whole reduction.**  If strengthening by the closed entry `X` holds over the *empty*
prefix, it holds over every well-formed prefix: exchange moves `X` to the bottom, and the
λ-abstraction of `bottom_package` eats the prefix that is now above it. -/
theorem strengthen_of_bottom (henv : VEnv.WF env) {X : VExpr}
    (hX : X.ClosedN 0) (hXT : env.IsType U [] X)
    (H0 : ∀ {e1 e2 : VExpr}, env.IsDefEqU U [X] e1.lift e2.lift → env.IsDefEqU U [] e1 e2)
    {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U)) {e1 e2 : VExpr}
    (H : env.IsDefEqU U (X::Γ) e1.lift e2.lift) : env.IsDefEqU U Γ e1 e2 :=
  have ⟨_, W, _, hlook, Hstr⟩ := bottom_package henv hX hXT H0 hΓ
  Hstr (H.exchangeClosed henv hX W hlook)

/-! ## 6. The capstone: the hole is a statement about a **one-entry** context

`StrengthenCanon.lean` §3 and `WeakNAttack.lean` §5 had already reduced the entry to one closed
term per level (`bigFalse u = ∀ (α : Sort u), α`) at the innermost position.  §5 removes the
prefix as well, so nothing of the context survives. -/

/-- **The hole with no context at all.**  *Adding `∀ (α : Sort u), α` to the **empty** context is
conservative for conversion of closed terms.*  No position, no block size, no entry and no
prefix is quantified: `Γ`, `Ctx.LiftN`, `n` and `k` have all left the statement, and what is
left is one term per level and two closed terms. -/
def StrengtheningCanon0 (env : VEnv) (U : Nat) : Prop :=
  ∀ {e1 e2 : VExpr} {u : VLevel}, u.WF U →
    env.IsDefEqU U [bigFalse u] e1.lift e2.lift → env.IsDefEqU U [] e1 e2

variable! (henv : VEnv.WF env) in
/-- The prefix is recovered by §5's exchange, the entry being closed. -/
theorem StrengtheningCanon0.canonInner (H : StrengtheningCanon0 env U) :
    StrengtheningCanonInner env U := fun hu hΓ h =>
  strengthen_of_bottom henv bigFalse_closed (bigFalse_isType hu) (fun h' => H hu h') hΓ h

variable! (henv : VEnv.WF env) in
/-- **`IsDefEqU.weakN_iff` is equivalent to a sentence about a one-entry context.** -/
theorem StrengtheningCanon0.iff_target :
    StrengtheningCanon0 env U ↔ StrengtheningTarget env U :=
  ⟨fun H => (StrengtheningCanonInner.iff_target henv).1 (H.canonInner henv),
   fun H _ _ _ hu h => (StrengtheningCanonInner.iff_target henv).2 H hu trivial h⟩

/-! ## 7. Limits of §5-§6, stated and where possible proved

* **§6 and §4 are two *alternative* narrow forms, not one.**  Both are equivalent to the target
  (`StrengtheningCanon0.iff_target`, `StrengtheningTarget.iff_inner1`), so each may be assumed
  when proving the other, but they do not compose into a single statement that is narrow in both
  senses: `Strengthening.of_typing_narrowBlock`'s induction *enlarges* the context at `lamDF` and
  `forallEDF`, so decomposing the empty-prefix form still needs the residual at every prefix.
  §8 records the composite that *does* hold.
* **§5 needs the entry closed, and that is not a limitation of the proof but of the statement.**
  `Strengthening1Inner`'s entry `X` is typed in `Γ`, so for a general `X` there is no context
  `Γ ++ [X]` to move it to — the appended copy would not typecheck.  This is why the route goes
  through the *canonical* entry, which `StrengthenCanon.lean` had already shown suffices.
* **§5 is not circular.**  It uses `IsDefEq.weakN` and `IsDefEq.instN` only.  Measured cone in
  §9 below: `StrengtheningCanon0.iff_target` does not reach `IsDefEqU.weakN_iff`. -/

variable! (henv : VEnv.WF env) in
/-- The composite that does hold: the hole is the typing half plus the one-entry residual, and
*separately* the one-entry-context sentence. -/
theorem StrengtheningCanon0.iff_inner1 :
    StrengtheningCanon0 env U ↔
      TypingStrengthening1Inner env U ∧ TransStrengtheningNarrowInner1 env U :=
  (StrengtheningCanon0.iff_target henv).trans (StrengtheningTarget.iff_inner1 henv)
