import Lean4Lean.Theory.Typing.ChurchRosser
import Lean4Lean.Theory.Typing.StrengthenNarrow
import Lean4Lean.Theory.Typing.ParRedKGraded

/-!
# Π-shape descent for `hasType_app_bvar0`: the residual **is** the typing half

`Theory/Typing/CRBetaGen.lean` localises site 7's `appDF` x `beta` row down to a single
appeal to `IsDefEqU.weakN_iff` beyond `TypingStrengthening`, namely

    theorem hasType_app_bvar0 (hΓ : OnCtx (A::Γ) (IsType env univs))
        (H : A :: Γ ⊢ e.lift.app (bvar 0) : B) : ∃ B', Γ ⊢ e : .forallE A B'

whose proof (`ChurchRosser.lean:1347`) strengthens the η-conversion
`A::Γ ⊢ (A.lam (e.lift.app (bvar 0))).lift ≡ e.lift` -- a conversion with two *distinct*
endpoints, hence outside `StrengthenNarrow.lean` §5's nine typing gates.  That file's closing
note reads the residual as "Π-shape descent for a `C` that is not syntactically a Π" and calls
it an appeal beyond the typing half.

**That reading is wrong, and this file proves it wrong.**  The η-route never needs the
*conversion* strengthened: it needs two *typings* strengthened, and both of them have a
subject **and a type** in the image of the lift.

## The proof, in one paragraph

Write `t := A.lam (e.lift.app (bvar 0))`, a term of `Γ`; the `rw` already in
`ChurchRosser.lean:1345` is the equation `A.lift.lam (e.lift.lift.app (bvar 0)) = t.lift`.

1. `c1.eta` gives `hη : A::Γ ⊢ t.lift ≡ e.lift : .forallE A.lift B₁`.  Its left `hasType`
   half, `A::Γ ⊢ t.lift : .forallE A.lift B₁`, is a typing whose **subject is a lift**, so
   `TypingStrengthening` (whose type argument is arbitrary) descends it: `Γ ⊢ t : D`.
2. `HasType.lam_inv` + `HasType.lam` re-derive `Γ ⊢ t : .forallE A D'` -- and *this* type is a
   Π **by construction**, with the binder `A` on the nose.  No shape descent is performed:
   the Π is built downstairs from the λ, not descended from upstairs.
3. Weakening step 2 and pushing `hη` across it with `HasType.defeqU_l` gives
   `A::Γ ⊢ e.lift : (.forallE A D').lift` -- subject *and* type now both lifts -- so
   `TypingStrengthening.hasType_inv` (`StrengthenNarrow.lean:377`) finishes.

The `IsDefEqU.weakN_iff` appeal is *eliminated*, not weakened: the conversion `hη` is still
used, but only upstairs, where it is free.

## Consequences, measured at `c9ac713` (`scripts/hole-cone.lean`'s walker, `allowOpaque`)

| seed | cone | holes |
| --- | --- | --- |
| `hasType_app_bvar0` (original) | 3465 | `IsDefEqU.weakN_iff`, `forallE_inv_stratified` |
| `hasType_app_bvar0_of_typing` | 3609 | `forallE_inv_stratified`, `rigidShapeUniqNS` |
| `TypingStrengthening.hasType_inv` (baseline) | 3594 | `forallE_inv_stratified`, `rigidShapeUniqNS` |
| `ParRedExt.parRed_beta_gen` (`CRBetaGen.lean`) | 3847 | `weakN_iff`, `forallE_inv_stratified`, `rigidShapeUniqNS` |
| §2 `parRed_beta_gen_of_typing` | 3855 | `forallE_inv_stratified`, `rigidShapeUniqNS` |
| `NormalEq.appDF_beta_of_parRedKn'` (the row) | 3906 | `weakN_iff`, `forallE_inv_stratified`, `rigidShapeUniqNS` |
| §3 `appDF_beta_of_parRedKn_of_typing` | 3914 | `forallE_inv_stratified`, `rigidShapeUniqNS` |

`rigidShapeUniqNS` is new to `hasType_app_bvar0` *in isolation* (it arrives with
`TypingStrengthening.hasType_inv`), but **not** to the row: `parRed_beta_gen` and
`appDF_beta_of_parRedKn'` already carried it.  So the row trades `IsDefEqU.weakN_iff` for
nothing.

`#print axioms` does **not** witness this: every declaration here reports
`[propext, sorryAx, Classical.choice, Quot.sound]`, because the two baseline holes carry
`sorryAx` too.  The cone table is the discriminating measurement.  (§5's
`piTypeDescend_hasType_app_bvar0` is the one exception: cone 3324, holes `[]`, axioms
`[propext, Classical.choice, Quot.sound]`.)

So `hasType_app_bvar0` joins `StrengthenNarrow.lean` §5's nine wrappers as a **tenth typing
gate**.  Reverse split of `IsDefEqU.weakN_iff`'s users with it in the gate set:

| gate set | users still reaching the hole | freed |
| --- | --- | --- |
| none cut | 211 | 0 |
| the nine (`scripts/weakn-gate-split.lean`) | 194 | 17 |
| the nine + `hasType_app_bvar0` | **191** | **20** |

The three newly freed are exactly `CRBetaGen.lean`'s rewired row and the two lemmas it rests
on: `NormalEq.appDF_beta_of_parRedKn'`, `ParRedExt.parRed_beta_gen`,
`ParRedExt.parRed_beta_of_gen`.

### A trap in those three numbers: `scripts/weakn-gate-split.lean` undercounts

The table above reproduces the repo script's methodology, which skips `n.isInternal` when it
builds the dependency graph.  That **breaks reachability through every equation compiler
auxiliary**, and one such auxiliary sits on a live path to this hole:

    NormalEq.trans → NormalEq.trans._unary → NormalEq.weakN_iff
                   → NormalEq.weakN_inv_DFC → IsDefEqU.weakN_iff

`NormalEq.trans._unary` is internal, so the script drops it and `NormalEq.trans` is scored as
**not** a user of the hole -- even though `#print axioms Lean4Lean.VEnv.NormalEq.trans` reports
`sorryAx`.  Re-running the same reverse reachability with internal names kept in the graph (and
still reporting only non-internal users), at `c9ac713`, this file's declarations excluded:

| gate set | users still reaching the hole | freed |
| --- | --- | --- |
| none cut | **293** | 0 |
| the nine | **250** | **43** |
| the nine + `hasType_app_bvar0` | **247** | **46** |

Both readings agree on this file's contribution (3 declarations freed); they disagree by 82 on
the size of the population and by 26 on how much the typing half buys.  The `131`/`211`/`18`/
`17` figures quoted in `UniqueTyping.lean:181`, `StrengthenNarrow.lean` §5 and
`NormalEqStrengthen.lean`'s header are all from the undercounting graph.  §2 and §3 below turn that gate-cut *measurement* into
theorems: `parRed_beta_gen_of_typing` and `appDF_beta_of_parRedKn_of_typing` are the same
proofs with `(HT : TypingStrengthening env univs)` threaded and the five appeals
(`VExpr.WF.weakN_iff` x2, `HasType.weakN_iff` x1, `hasType_app_bvar0` x2) replaced by
`HT.wf_inv`, `HT.hasType_inv` and §1.  **Neither has `IsDefEqU.weakN_iff` in its cone.**

## Bounds, both ways

* Nothing is lost (§4).  `typingStrengthening_of_weakN_iff` inhabits `TypingStrengthening`
  from the hole itself, so `parRed_beta_gen_of_typing` recovers `parRed_beta_gen` verbatim
  (`parRed_beta_gen_of_typing_recovers`).  The reduction is therefore an implication in the
  useful direction only, which is what a reduction should be.
* Nothing collapses.  With `hasType_app_bvar0` promoted, **191 of the 211 users still reach
  the hole**, so `TypingStrengthening` has not silently become the target: the narrow `trans`
  residual (`StrengthenNarrow.lean` §1) is untouched and still carries almost everything.
* This is *not* the Π-shape descent statement `KEta.lean:830`'s `PiTypeDescend` asks for.
  `PiTypeDescend` descends a Π type for an arbitrary lifted subject; §1 works only because the
  subject is an **η-expansion**, i.e. syntactically a λ downstairs, so its Π type is built
  rather than descended.  §5 records that the two are *not* interchangeable.

## Not done here

Threading `HT` through `ChurchRosser.lean`'s own `hasType_app_bvar0`/`parRed_beta` (rather than
restating them here) is the `TypingStrengthening` flag day, which terminates outside this
stream's files.  Nothing in this file edits an existing declaration.
-/

namespace Lean4Lean
namespace VEnv

open VExpr

section
variable [Params]
open Params

set_option hygiene false
local notation:65 Γ " ⊢ " e " : " A:36 => HasType env univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 " : " A:36 => IsDefEq env univs Γ e1 e2 A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 => IsDefEqU env univs Γ e1 e2
local notation:65 Γ " ⊢ " e1 " ≡ₚ " e2:30 => NormalEq Γ e1 e2
local notation:65 Γ " ⊢ " e1 " ≫ " e2:36 => ParRed Γ e1 e2
local notation:65 Γ " ⊢ " e1 " ≫* " e2:36 => ParRedS Γ e1 e2


/-! ## 1. The residual, from the typing half alone -/

variable! (hΓ : OnCtx (A::Γ) (IsType env univs)) in
/-- **`ChurchRosser.lean:1336` from `TypingStrengthening`.**  Statement verbatim; the
`IsDefEqU.weakN_iff` appeal at `:1347` is replaced by two typing descents whose subject *and*
type are lifts.  See the module docstring for why no shape descent is needed. -/
theorem hasType_app_bvar0_of_typing (HT : TypingStrengthening env univs)
    (H : A :: Γ ⊢ e.lift.app (bvar 0) : B) : ∃ B', Γ ⊢ e : .forallE A B' := by
  have ⟨_, _, c1, c2⟩ := H.app_inv henv hΓ
  replace c1 :=
    have ⟨_, d1⟩ := c1.isType henv hΓ
    have ⟨_, _, d3⟩ := d1.forallE_inv henv
    have ⟨_, d4⟩ := c2.uniq henv hΓ (.bvar .zero)
    HasType.defeqU_r henv hΓ ⟨_, d4.forallEDF d3⟩ c1
  have hη := c1.eta
  rw [show A.lift.lam (e.lift.lift.app (bvar 0)) = (A.lam (e.lift.app (bvar 0))).lift by
    simp [VExpr.liftN, liftN'_liftN_lo, liftN_liftN]] at hη
  have ⟨D, hD⟩ := HT (n := 1) (k := 0) .one hΓ.1 hΓ hη.hasType.1
  have ⟨⟨_, f2⟩, _, f3⟩ := HasType.lam_inv henv hΓ.1 hD
  have key := HasType.defeqU_l henv hΓ ⟨_, hη⟩ ((HasType.lam f2 f3).weakN henv .one)
  exact ⟨_, HT.hasType_inv henv .one hΓ key⟩

/-! ## 2. `CRBetaGen.lean`'s `parRed_beta_gen`, with the hole replaced by the typing half

`CRBetaGen.lean:29`'s proof verbatim, with five appeals rewired: the two
`VExpr.WF.weakN_iff` uses become `HT.wf_inv`, the one `HasType.weakN_iff` use becomes
`HT.hasType_inv`, and the two `hasType_app_bvar0` calls become §1. -/

variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem ParRedExt.parRed_beta_gen_of_typing (HT : TypingStrengthening env univs) :
    Γ ⊢ f ≡ₚ lam A e' → ∀ {a a₂ B}, Γ ⊢ a ≡ₚ a₂ → Γ ⊢ f.app a : B →
      ∃ e, Γ ⊢ f.app a ≫* e ∧ Γ ⊢ e ≡ₚ e'.inst a₂ := by
  refine (?_ : _ ∧ ∀ (l : ParRedExt), l.depth ≤ Γ.length →
    Γ ⊢ f ≡ₚ l.apply ((lam A e').lift.app (bvar 0)) → ∃ e, Γ ⊢ f ≫* e ∧ Γ ⊢ e ≡ₚ l.apply e').1
  induction f using VExpr.brecOn generalizing Γ A e' with | _ f f_ih => ?_
  revert f_ih; change let motive := ?_; ∀ _: f.below (motive := motive), _; intro motive f_ih
  refine ⟨fun h1 a a₂ B ha h2 => ?_, fun l W h1 => ?_⟩
  · cases h1 with
    | @refl _ _ B0 H =>
      clear f_ih motive
      have ⟨_, _, H1, H2⟩ := h2.app_inv henv hΓ
      have ⟨⟨_, H3⟩, _, H4⟩ := H1.lam_inv henv hΓ
      have ⟨⟨_, u1⟩, u2⟩ := ((H3.lam H4).uniqU henv hΓ H1).forallE_inv henv hΓ
      refine have h := ParRed.beta .rfl .rfl; ⟨_, .tail .rfl h, ?_⟩
      exact NormalEq.instN_r (by exact ⟨hΓ, _, H3⟩) (u1.symm.defeq H2) ha .zero H4
    | lamDF a1 a2 a3 =>
      have ⟨_, _, H1, H2⟩ := h2.app_inv henv hΓ
      have ⟨⟨_, H3⟩, _, H4⟩ := H1.lam_inv henv hΓ
      have ⟨⟨_, u1⟩, u2⟩ := ((H3.lam H4).uniqU henv hΓ H1).forallE_inv henv hΓ
      exact ⟨_, .tail .rfl <| .beta .rfl .rfl,
        NormalEq.instN₂ (.defeq (.symm <| .trans_l henv hΓ a1 u1) H2) ha a3
          (by exact ⟨hΓ, _, a1.hasType.1⟩) .zero⟩
    | @etaL _ _ A' _ _ a1 a2 =>
      have ⟨⟨_, hA⟩, _, hB⟩ := have ⟨_, h⟩ := a1.isType henv hΓ; h.forallE_inv henv
      have ⟨_, d1, d2⟩ := (f_ih.2.1 <| by exact ⟨hΓ, _, hA⟩).2 .base (Nat.zero_le _) a2
      have ⟨_, _, c3, c4⟩ := h2.app_inv henv hΓ
      have ⟨⟨_, c1⟩, _, c2⟩ := c3.lam_inv henv hΓ
      have ⟨⟨_, u1⟩, u2⟩ := ((c1.lam c2).uniqU henv hΓ c3).forallE_inv henv hΓ
      exact ⟨_, .tail (ParRedS.app (.lam .rfl d1) .rfl) <| .beta .rfl .rfl,
        NormalEq.instN₂ (.defeq u1.symm c4) ha d2 (by exact ⟨hΓ, _, c1⟩) .zero⟩
    | etaR a1 a2 =>
      have ⟨_, _, H1, H2⟩ := h2.app_inv henv hΓ
      have ⟨⟨_, hA⟩, _, hB⟩ := have ⟨_, h⟩ := a1.isType henv hΓ; h.forallE_inv henv
      have ⟨⟨_, u1⟩, u2⟩ := (H1.uniqU henv hΓ a1).forallE_inv henv hΓ
      have := NormalEq.instN₂ (.defeq u1 H2) ha a2 (by exact ⟨hΓ, _, hA⟩) .zero
      simp [inst, inst_lift] at this
      exact ⟨_, .rfl, this⟩
    | proofIrrel a1 a2 a3 =>
      have ⟨_, _, H1, H2⟩ := h2.app_inv henv hΓ
      have hf := a2.uniqU henv hΓ H1; have := a1.defeqU_l henv hΓ hf
      have ⟨⟨_, b1⟩, _, b2⟩ := this.forallE_inv henv
      have := ((b1.forallE b2).uniqU henv hΓ this).sort_inv henv hΓ
      have b3 := let ⟨_, h⟩ := b2.isType henv (by exact ⟨hΓ, _, b1⟩); h.sort_inv henv
      have b2 := IsDefEq.defeq (.sortDF b3 (by trivial) (VLevel.imax_eq_zero.1 this)) b2
      have ⟨⟨_, c1⟩, _, c2⟩ := a3.lam_inv henv hΓ
      have ⟨⟨_, u1⟩, _, u2⟩ := ((c1.lam c2).uniqU henv hΓ a3).trans henv hΓ hf |>.forallE_inv henv hΓ
      have hc2 := (u2.defeq c2).instN henv (Γ := Γ) .zero (u1.symm.defeq H2)
      have hr : Γ ⊢ e'.inst a ≡ e'.inst a₂ :=
        (NormalEq.instN_r (by exact ⟨hΓ, _, c1⟩) (u1.symm.defeq H2) ha .zero
          (u2.defeq c2)).defeq hΓ
      exact ⟨_, .rfl, .proofIrrel (b2.instN henv .zero H2) (H1.app H2)
        (hc2.defeqU_l henv hΓ hr)⟩
  generalize eq : l.apply .. = s at h1
  cases h1 with
  | @refl _ _ B H =>
    subst eq; clear f_ih motive
    generalize ls : l.meas = n
    induction n using Nat.strongRecOn generalizing l Γ B with | _ _ ih; subst ls
    cases l with
    | base =>
      refine have h := ParRed.beta .rfl .rfl; ⟨_, .tail .rfl h, ?_⟩
      simp [instN_bvar0] at h ⊢; exact .refl (h.hasType hΓ H)
    | lift l =>
      let A::Γ := Γ
      have ⟨_, a1⟩ := HT.wf_inv henv .one hΓ ⟨_, H⟩
      have ⟨_, a2, a3⟩ := ih _ (by simp [ParRedExt.meas]) hΓ.1 l (by simpa [ParRedExt.depth] using W) a1 rfl
      exact ⟨_, .weakN .one a2, .weakN .one a3⟩
    | app l =>
      let A::Γ := Γ
      have ⟨_, _, H1, H2⟩ := H.app_inv henv hΓ
      have ⟨_, a1, a2⟩ := ih _ (by simp [ParRedExt.meas]) hΓ (lift l) W H1 rfl
      have := a1.hasType hΓ H1
      exact ⟨_, .app a1 .rfl, .appDF this (this.defeqU_l henv hΓ (a2.defeq hΓ)) H2 H2 a2 (.refl H2)⟩
  | @appDF _ _ A' B' f' _ a' a1 a2 a3 a4 a5 a6 =>
    obtain ⟨n, rfl, ⟨rfl, h⟩ | ⟨l', W', rfl, h⟩⟩ : ∃ n, a' = bvar n ∧
        (f' = (A.lam e').liftN (n+1) ∧ l.apply e' = liftN n e' ∨
        ∃ l', l'.depth ≤ l.depth ∧
          f' = ParRedExt.apply l' ((A.lam e').lift.app (bvar 0)) ∧
          l.apply e' = (l'.apply e').app (bvar n)) := by
      clear W a2 a4 a5 a6
      induction l generalizing f' a' with
      | base => cases eq; exact ⟨_, rfl, .inl ⟨rfl, by simp [ParRedExt.apply]⟩⟩
      | lift l ih =>
        simp [ParRedExt.apply] at eq
        generalize eq' : ParRedExt.apply .. = s at eq; cases s <;> cases eq
        obtain ⟨n, rfl, ⟨rfl, h⟩ | ⟨l', W', rfl, h⟩⟩ := ih eq'
        · refine ⟨_, rfl, .inl ⟨by simp [liftN_liftN], ?_⟩⟩
          have := congrArg VExpr.lift h
          simpa [lift_inst_hi, liftN'_liftN']
        · exact ⟨_, rfl, .inr ⟨lift _, Nat.succ_le_succ W', rfl, congrArg VExpr.lift h⟩⟩
      | app l ih => cases eq; exact ⟨_, rfl, .inr ⟨lift _, Nat.le_refl _, rfl, rfl⟩⟩
    · have ⟨⟨_, c1⟩, _, c2⟩ := (a1.defeqU_l henv hΓ (a5.defeq hΓ)).lam_inv henv hΓ
      have ⟨⟨_, u1⟩, _, u2⟩ := a1.defeqU_l henv hΓ (a5.defeq hΓ)
        |>.uniqU henv hΓ (c1.lam c2) |>.forallE_inv henv hΓ
      have ⟨_, b1, b2⟩ := (f_ih.1.1 hΓ).1 a5 a6 (.app a1 a3)
      have := congrArg (liftN n) (instN_bvar0 e' 0)
      simp [liftN_inst_hi, liftN'_liftN', liftN] at this
      rw [Nat.add_comm, this, ← h] at b2
      exact ⟨_, b1, b2⟩
    · have ⟨_, b1, b2⟩ := (f_ih.1.1 hΓ).2 l' (Nat.le_trans W' W) a5
      rw [h]; have := b1.hasType hΓ a1
      exact ⟨_, .app b1 .rfl, .appDF this (.defeqU_l henv hΓ (b2.defeq hΓ) this) a3 a4 b2 a6⟩
  | @etaL _ _ A' _ _ a1 a2 =>
    subst eq
    have ⟨⟨_, hA⟩, _, hB⟩ := have ⟨_, h⟩ := a1.isType henv hΓ; h.forallE_inv henv
    refine have hΓ' := ⟨hΓ, _, hA⟩
      have ⟨_, b1, b2⟩ := (f_ih.2.1 hΓ').2 (ParRedExt.app l) (by exact Nat.succ_le_succ W) a2; ?_
    have ⟨_, c1⟩ := b2.defeq hΓ'
    let ⟨_, b3⟩ := hasType_app_bvar0_of_typing hΓ' HT c1.hasType.2
    exact ⟨_, .lam .rfl b1, .etaL b3 b2⟩
  | @proofIrrel _ p _ _ a1 a2 a3 =>
    subst eq; refine ⟨_, .rfl, .proofIrrel a1 a2 ?_⟩
    clear a2; induction l generalizing Γ p with
    | base =>
      have ⟨_, _, b1, b2⟩ := a3.app_inv henv hΓ
      have ⟨⟨_, b3⟩, _, b4⟩ := b1.lam_inv henv hΓ
      have ⟨⟨_, u1⟩, _, u2⟩ := ((b3.lam b4).uniqU henv hΓ b1).forallE_inv henv hΓ
      have := b4.beta (u1.symm.defeq b2)
      simp [instN_bvar0] at this
      exact .defeqU_l henv hΓ ⟨_, this⟩ a3
    | lift l ih =>
      let A::Γ := Γ
      have ⟨_, b1⟩ := HT.wf_inv henv .one hΓ ⟨_, a3⟩
      have u1 := a3.uniqU henv hΓ (b1.weak henv)
      have := HT.hasType_inv (A := .sort _) henv .one hΓ (a1.defeqU_l henv hΓ u1)
      have := ih hΓ.1 (Nat.le_of_succ_le_succ W) this b1
      exact .defeqU_r henv hΓ u1.symm (this.weak henv)
    | app l ih =>
      let A::Γ := Γ
      let ⟨_, b1⟩ := hasType_app_bvar0_of_typing hΓ HT a3
      have H := a3.uniqU henv hΓ (HasType.app (b1.weak henv) (.bvar .zero))
      simp [instN_bvar0] at H
      have ⟨⟨_, b2⟩, _, b3⟩ := have ⟨_, b2⟩ := b1.isType henv hΓ.1; b2.forallE_inv henv
      have wf := let ⟨_, h⟩ := b2.isType henv hΓ.1; h.sort_inv henv
      have := b2.forallE (.defeqU_l henv hΓ H a1)
      have := IsDefEq.defeq (.sortDF (by exact ⟨wf, ⟨⟩⟩) (by trivial) VLevel.imax_zero) this
      have := ih hΓ.1 (Nat.le_of_succ_le_succ W) this b1
      have := HasType.app (this.weak henv) (.bvar .zero)
      simp [instN_bvar0] at this
      exact .defeqU_r henv hΓ H.symm this
  | _ => cases l.isApp eq


/-! ## 3. Site 7's `appDF` x `beta` row, `IsDefEqU.weakN_iff`-free

`CRBetaGen.lean:178`'s row with §2 in place of `parRed_beta_gen`. -/

theorem NormalEq.appDF_beta_of_parRedKn_of_typing {M : Nat} {Γ : List VExpr}
    {f A B a b A₀ eb : VExpr}
    (HT : TypingStrengthening env univs) (hΓ : OnCtx Γ (IsType env univs))
    (l1 : Γ ⊢ f : .forallE A B) (l2 : Γ ⊢ .lam A₀ eb : .forallE A B)
    (l3 : Γ ⊢ a : A) (l4 : Γ ⊢ b : A)
    (ih1 : ∀ {x : VExpr}, ParRedKn M Γ (.lam A₀ eb) x →
      ∃ e₁', ParRedKS Γ f e₁' ∧ Γ ⊢ e₁' ≡ₚ x)
    (ih2 : ∀ {x : VExpr}, ParRedKn M Γ b x → ∃ e₁', ParRedKS Γ a e₁' ∧ Γ ⊢ e₁' ≡ₚ x)
    {eb' b' : VExpr} (r1 : ParRedKn M (A₀::Γ) eb eb') (r2 : ParRedKn M Γ b b') :
    ∃ e₁', ParRedKS Γ (.app f a) e₁' ∧ Γ ⊢ e₁' ≡ₚ eb'.inst b' := by
  let ⟨f', a1, a2⟩ := ih1 (.lam .rfl r1)
  let ⟨a', b1, b2⟩ := ih2 r2
  let ⟨⟨_, d1⟩, _, d2⟩ := l2.lam_inv henv hΓ
  let ⟨⟨_, u1⟩, _, u2⟩ := ((d1.lam d2).uniqU henv hΓ l2).forallE_inv henv hΓ
  refine have hΓ' := (by exact ⟨hΓ, _, d1⟩); have d2 := r1.toParRedK.hasType hΓ' (u2.defeq d2); ?_
  replace l3 := b1.hasType hΓ (u1.symm.defeq l3)
  let ⟨_, h1, h2⟩ := ParRedExt.parRed_beta_gen_of_typing hΓ HT a2 b2
    (.app (.defeqU_l henv hΓ (a2.defeq hΓ).symm (d1.lam d2)) l3)
  exact ⟨_, (ParRedKS.app a1 b1).trans h1.toK, h2⟩


/-! ## 4. Controls: nothing is lost, and nothing collapses

`typingStrengthening_of_weakN_iff` inhabits the hypothesis from the hole itself, so §2
recovers `CRBetaGen.lean`'s `parRed_beta_gen` verbatim -- the generalisation costs nothing.
This is the only declaration in the file whose cone contains `IsDefEqU.weakN_iff`, and it is
here precisely so the recovery is machine-checked rather than asserted. -/

theorem typingStrengthening_of_weakN_iff : TypingStrengthening env univs :=
  fun W _ hΓ' h => (IsDefEqU.weakN_iff henv hΓ' W).1 ⟨_, h⟩

variable! (hΓ : OnCtx Γ (IsType env univs)) in
/-- **§2 recovers the original.** -/
theorem ParRedExt.parRed_beta_gen_of_typing_recovers
    (h1 : Γ ⊢ f ≡ₚ lam A e') {a a₂ B} (ha : Γ ⊢ a ≡ₚ a₂) (h2 : Γ ⊢ f.app a : B) :
    ∃ e, Γ ⊢ f.app a ≫* e ∧ Γ ⊢ e ≡ₚ e'.inst a₂ :=
  parRed_beta_gen_of_typing hΓ typingStrengthening_of_weakN_iff h1 ha h2

variable! (hΓ : OnCtx (A::Γ) (IsType env univs)) in
/-- **§1 recovers `ChurchRosser.lean:1336`.** -/
theorem hasType_app_bvar0_of_typing_recovers
    (H : A :: Γ ⊢ e.lift.app (bvar 0) : B) : ∃ B', Γ ⊢ e : .forallE A B' :=
  hasType_app_bvar0_of_typing hΓ typingStrengthening_of_weakN_iff H

/-! ## 5. Negative control: §1 is **not** `PiTypeDescend`

`KEta.lean:830`'s `PiTypeDescend` asks for a Π type downstairs for an *arbitrary* lifted
subject.  §1 gets one only because its subject is an η-expansion, so downstairs it is a λ and
its Π type is **built** by `HasType.lam`, not descended.  The two are not interchangeable in
the direction that matters: §1's technique does not give `PiTypeDescend`, because there is no
λ to invert.  What §1 *does* give is the instance of `PiTypeDescend` at `n = 1`, `k = 0`
restricted to subjects of the form `e` whose η-expansion is already known to type-check --
i.e. exactly `hasType_app_bvar0`.  Conversely `PiTypeDescend` implies §1 only up to the
binder: it returns *some* domain `A₀`, and identifying `A₀` with the context binder `A` needs
`A::Γ ⊢ A₀.lift ≡ A.lift` descended, which is `SortConvStrengthening`
(`NormalEqStrengthen.lean:155`) -- itself the typing half again, so the round trip is
consistent but not free.

The recorded consequence is therefore narrower than "Π-shape descent is available": it is
"the *one instance* of Π-shape descent that site 7's row needs is available, from the typing
half, because the subject is an η-expansion". -/

theorem piTypeDescend_hasType_app_bvar0 (HP : PiTypeDescend)
    (hΓ : OnCtx (A::Γ) (IsType env univs))
    (H : A :: Γ ⊢ e.lift.app (bvar 0) : B) : ∃ A₀ B₀, Γ ⊢ e : .forallE A₀ B₀ :=
  have ⟨_, _, c1, _⟩ := H.app_inv henv hΓ
  HP hΓ.1 hΓ .one c1



/-! ## 6. Cross-stream check: `ConvPiFromEntry` is a **different** statement

`Theory/Typing/InjPiInhab.lean` §7 offers `ConvPiFromEntry` -- two `ConvC` chains out of a
common source `X.lift`, both landing on Π shapes, have chain-linked codomains -- as "the form
to aim a parallel-reduction / Church-Rosser development at", naming this file as the meeting
point.  It is not this file's residual, in either direction:

* `ConvPiFromEntry` relates the **components of two Πs that are already given**.  §1's residual
  had to **produce a Π where none is given** -- that is why `CRBetaGen.lean`'s note correctly
  ruled out `IsDefEqU.forallE_inv_stratified` ("both sides must already be Π"), and
  `ConvPiFromEntry` is the typing-free form of that same Π-injectivity node.  It cannot
  manufacture a Π type for `e` in `Γ`, so it does not imply §1.
* §1 does not imply it either: §1 concludes a *typing*, and there is no route from one Π-typing
  to codomain confluence in a context extended by the domain.
* Moot in any case: §1 is **closed**, and closed without any shape descent at all -- the Π is
  built downstairs by `HasType.lam` from the λ that `TypingStrengthening` descends.  No
  Π-injectivity, no confluence at a Π head, no shape descent is touched.

**The real connection is one layer further out, and it is worth having.**  §1-§3 still carry
`IsDefEqU.forallE_inv_stratified` and `WF.rigidShapeUniqNS`, and `InjPiInhab.lean` §8's two
bridges to those are `sorryAx`-free (`piInvStratApp_of_convStep2` `[propext, Classical.choice,
Quot.sound]`; `rigidShapeUniqNS_of_family_convStep2` `[propext, Quot.sound]`), with
`ConvStep2 ↔ ConvSortInv ∧ ConvPiFromEntry`.  So `ConvPiFromEntry` is upstream of what is
*left over* in this file, not of what it closed.  Two cautions against overreading that:
`ConvStep2` is necessary but **not sufficient** for either hole -- `piInvStratApp_of_convStep2`
also wants `SortInv` and `PiInv`, and `rigidShapeUniqNS_of_family_convStep2` wants `PiInv` plus
four `Rigid*` conjuncts -- and `PiInvStratApp` is only *part* of hole A
(`PiLevelPin.piInvCod_of_piInvStratApp` recovers only `PiInvCod`; nothing in the tree derives
`forallE_inv_stratified` from it).

### The inhabitant move does not apply here

The same stream retired `ConvCStrengthen` by noting that strengthening across an **inhabited**
entry is just substitution.  At §1's two call sites there is no such inhabitant.  At
`ChurchRosser.lean:1453` the entry is `A'`, the Π-domain of `a1 : Γ ⊢ e' : forallE A' B`, and
`a1.isType`/`forallE_inv` yields only `Γ ⊢ A' : sort _` -- a type, not a term of it.  At `:1474`
the entry is the ambient context head.  The only inhabitant anywhere in sight is `.bvar 0`,
which lives **upstairs** and *is* the variable being stripped, so it is precisely the one term
that cannot serve.  This is moot for the same reason as above: `TypingStrengthening` needs no
inhabitant, so §1 closes with no strengthening-across-an-entry step at all. -/


end
