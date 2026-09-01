import Lean4Lean.Theory.Typing.ChurchRosser
import Lean4Lean.Theory.Typing.ParRedKGraded

/-!
# `ParRedExt.parRed_beta` with the argument mismatch absorbed

`ChurchRosser.lean:1438` composes the recursive call's `NormalEq` with `NormalEq.instN_r`
through `NormalEq.trans`, and `trans`'s `etaR`-after-`etaL` case (`ChurchRosser.lean:640`) is
the file's only `NormalEq`-strengthening appeal.  This file tests whether that composition is
*forced*, by re-proving the lemma with the mismatch carried in the statement instead: the first
component takes `Γ ⊢ a ≡ₚ a₂` and concludes at `e'.inst a₂`, so the four places that used
`NormalEq.instN` (plus one `trans ∘ instN_r`) use `NormalEq.instN₂` / `instN_r` instead.
-/

namespace Lean4Lean
namespace VEnv
open VExpr
variable [Params]
open Params

local notation:65 Γ " ⊢ " e " : " A:36 => HasType env univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 " : " A:36 => IsDefEq env univs Γ e1 e2 A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 => IsDefEqU env univs Γ e1 e2
local notation:65 Γ " ⊢ " e1 " ≡ₚ " e2:30 => NormalEq Γ e1 e2
local notation:65 Γ " ⊢ " e1 " ≫ " e2:36 => ParRed Γ e1 e2
local notation:65 Γ " ⊢ " e1 " ≫* " e2:36 => ParRedS Γ e1 e2

variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem ParRedExt.parRed_beta_gen :
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
      have ⟨_, a1⟩ := (VExpr.WF.weakN_iff henv hΓ .one).1 ⟨_, H⟩
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
    let ⟨_, b3⟩ := hasType_app_bvar0 hΓ' c1.hasType.2
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
      have ⟨_, b1⟩ := (VExpr.WF.weakN_iff henv hΓ .one).1 ⟨_, a3⟩
      have u1 := a3.uniqU henv hΓ (b1.weak henv)
      have := (HasType.weakN_iff henv hΓ (A := sort _) .one).1 (a1.defeqU_l henv hΓ u1)
      have := ih hΓ.1 (Nat.le_of_succ_le_succ W) this b1
      exact .defeqU_r henv hΓ u1.symm (this.weak henv)
    | app l ih =>
      let A::Γ := Γ
      let ⟨_, b1⟩ := hasType_app_bvar0 hΓ a3
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

/-! ## The `appDF` x `beta` row of site 7, rewired onto `parRed_beta_gen`

`ParRedKGraded.NormalEq.appDF_beta_of_parRedKn`'s body with its closing
`h2.trans hΓ (.instN_r ...)` replaced by passing `b2` into the generalised lemma.  Measured
consequence: `NormalEq.trans`, `NormalEq.weakN_iff` and `NormalEq.weakN_inv_DFC` all leave the
row's cone; `hasType_app_bvar0` does not. -/
theorem NormalEq.appDF_beta_of_parRedKn' {M : Nat} {Γ : List VExpr}
    {f A B a b A₀ eb : VExpr}
    (hΓ : OnCtx Γ (IsType env univs))
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
  let ⟨_, h1, h2⟩ := ParRedExt.parRed_beta_gen hΓ a2 b2
    (.app (.defeqU_l henv hΓ (a2.defeq hΓ).symm (d1.lam d2)) l3)
  exact ⟨_, (ParRedKS.app a1 b1).trans h1.toK, h2⟩

/-! ## Controls: the generalised statement is inter-derivable with the original

Both directions are machine-checked below, which is what makes the cone comparison meaningful.

* `parRed_beta_of_gen` -- the original statement follows from the generalised one **for free**
  (`a₂ := a`, `ha := .refl`), so nothing was lost.
* `parRed_beta_gen_of_beta` -- the generalised statement follows from the original **only
  through the very `NormalEq.trans ∘ instN_r` step it was built to avoid**, so the
  generalisation is not a restatement: it is the strengthening that lets the induction close
  without `trans`.  Measured: this direction's cone contains `NormalEq.trans`; the direct proof
  above does not. -/
theorem ParRedExt.parRed_beta_of_gen (hΓ : OnCtx Γ (IsType env univs))
    (h1 : Γ ⊢ f ≡ₚ lam A e') {a B} (h2 : Γ ⊢ f.app a : B) :
    ∃ e, Γ ⊢ f.app a ≫* e ∧ Γ ⊢ e ≡ₚ e'.inst a :=
  have ⟨_, _, _, H2⟩ := h2.app_inv henv hΓ
  parRed_beta_gen hΓ h1 (.refl H2) h2

theorem ParRedExt.parRed_beta_gen_of_beta (hΓ : OnCtx Γ (IsType env univs))
    (h1 : Γ ⊢ f ≡ₚ lam A e') {a a₂ B} (ha : Γ ⊢ a ≡ₚ a₂) (h2 : Γ ⊢ f.app a : B) :
    ∃ e, Γ ⊢ f.app a ≫* e ∧ Γ ⊢ e ≡ₚ e'.inst a₂ := by
  have ⟨_, _, H1, H2⟩ := h2.app_inv henv hΓ
  have ⟨⟨_, H3⟩, _, H4⟩ := (H1.defeqU_l henv hΓ (h1.defeq hΓ)).lam_inv henv hΓ
  have ⟨⟨_, u1⟩, _⟩ := (H1.defeqU_l henv hΓ (h1.defeq hΓ)).uniqU henv hΓ (H3.lam H4)
    |>.forallE_inv henv hΓ
  have ⟨_, b1, b2⟩ := ParRedExt.parRed_beta hΓ h1 h2
  exact ⟨_, b1, b2.trans hΓ
    (NormalEq.instN_r (by exact ⟨hΓ, _, H3⟩) (u1.defeq H2) ha .zero H4)⟩

/-! ## Measurements (all at `f850241`, `scripts/hole-cone.lean`'s walker)

| seed | cone | `NormalEq.trans` in cone | direct `weakN_iff` users in cone |
| --- | --- | --- | --- |
| `ParRedExt.parRed_beta` (original) | 3875 | yes | `WF.weakN_iff`, `NormalEq.weakN_inv_DFC`, `hasType_app_bvar0`, `IsDefEq.weakN_iff'`, itself |
| `ParRedExt.parRed_beta_gen` | 3847 | **no** | `WF.weakN_iff`, `hasType_app_bvar0`, `IsDefEq.weakN_iff'` |
| `ParRedExt.parRed_beta_of_gen` | 3849 | no | as above |
| `ParRedExt.parRed_beta_gen_of_beta` | 3880 | yes | as the original |
| `NormalEq.appDF_beta_of_parRedKn` (`ParRedKGraded`) | 3934 | yes | as the original |
| `NormalEq.appDF_beta_of_parRedKn'` | 3906 | **no** | `WF.weakN_iff`, `hasType_app_bvar0`, `IsDefEq.weakN_iff'` |

Gate-cut (the nine wrappers `StrengthenNarrow.lean` §5 reproves from `TypingStrengthening`,
treated as leaves):

| seed | typing gates cut | + `hasType_app_bvar0` cut |
| --- | --- | --- |
| `parRed_beta` | still reaches the hole | **still reaches the hole** |
| `parRed_beta_gen` | still reaches the hole | **does not reach the hole** |
| `appDF_beta_of_parRedKn` | still reaches | **still reaches** |
| `appDF_beta_of_parRedKn'` | still reaches | **does not reach** |

So site 7's `appDF` x `beta` row appeals to `IsDefEqU.weakN_iff` in exactly two ways once the
`trans` is absorbed: `TypingStrengthening` (nine wrappers plus two reflexive uses in the row's
own body, rewritten here through `VExpr.WF.weakN_iff` so the cut sees them), and
`hasType_app_bvar0`.

### Correction to `ParRedKGraded.lean`'s closing note (lines 425-434)

That note says `parRed_beta` touches `weakN_iff` "in four places (lines 1407, 1438, 1467,
1469)", that the first three are typing-half, and that line 1438 "is the whole obstruction, and
it is not reducible to the typing half" -- flagged there as inspection, not machine-checked.
Two of the three claims are wrong:

* **There is a fifth touch, and it is the hard one.**  `parRed_beta` calls
  `hasType_app_bvar0` (`ChurchRosser.lean:1336`) twice -- at `:1453` in the `etaL` case and at
  `:1474` in the `proofIrrel`/`app` case -- and that lemma's own appeal (`ChurchRosser.lean:1347`)
  strengthens `A::Γ ⊢ (A.lam (e.lift.app (bvar 0))).lift ≡ e.lift`, a conversion with **two
  distinct endpoints**.  It is not a typing gate: `IsDefEq.skips`, its closest gate-set
  neighbour, is excluded from the typing gates for exactly this reason
  (`StrengthenNarrow.lean` §6's note).  The gate-cut table above is the machine check.
* **Line 1438 is not irreducible.**  `parRed_beta_gen` above is the same proof with the
  argument mismatch carried in the statement, and `NormalEq.instN₂` -- the fused substitution
  `ChurchRosser.lean` §"Parallel substitution" already built to take `weakN_iff` out of the
  descent -- doing the work of `instN` and of `trans ∘ instN_r`.  `NormalEq.trans`,
  `NormalEq.weakN_iff` and `NormalEq.weakN_inv_DFC` all leave the cone.

The note's third claim -- that 1407, 1467, 1469 are typing-half -- holds: 1407 and 1467 apply
`IsDefEqU.weakN_iff` to a *reflexive* pair (so they are `VExpr.WF.weakN_iff`, which is how they
are written here), and 1469 already goes through `HasType.weakN_iff`.

### What the remaining obstruction is, exactly

    theorem hasType_app_bvar0 (hΓ : OnCtx (A::Γ) (IsType env univs))
        (H : A :: Γ ⊢ e.lift.app (bvar 0) : B) : ∃ B', Γ ⊢ e : .forallE A B'

The typing half gives `∃ C, Γ ⊢ e : C` (from `A::Γ ⊢ e.lift : forallE A.lift B₁`), and
uniqueness then gives `A::Γ ⊢ C.lift ≡ forallE A.lift B₁`.  What is missing downstairs is
Π-*shape* descent for a `C` that is not syntactically a Π, which is why
`IsDefEqU.forallE_inv_stratified` (both of whose sides must already be Π) does not supply it
either.  The eta route in `ChurchRosser.lean` sidesteps that by strengthening the eta
conversion instead -- hence the appeal.

### Retracted, 2026-09-01: the appeal is the typing half after all

**The paragraph above analyses one route and mistakes it for the only route.**  It is wrong;
`Theory/Typing/CRPiDescend.lean` proves it wrong.  Do not take the uniqueness step at all:

* `c1.eta`'s left `hasType` half is `A::Γ ⊢ (A.lam (e.lift.app (bvar 0))).lift : forallE A.lift B₁`
  -- a typing whose **subject is a lift** and whose type is arbitrary, which is exactly the
  shape `TypingStrengthening` consumes.  It descends to `Γ ⊢ A.lam (e.lift.app (bvar 0)) : D`.
* `HasType.lam_inv` then `HasType.lam` re-derive `Γ ⊢ A.lam (e.lift.app (bvar 0)) : forallE A D'`.
  This Π is **built downstairs from the λ**, with the binder `A` on the nose.  No shape descent
  happens anywhere.
* Weakening that and pushing the η-conversion across it with `HasType.defeqU_l` gives
  `A::Γ ⊢ e.lift : (forallE A D').lift` -- subject *and* type now both lifts -- so
  `TypingStrengthening.hasType_inv` finishes.

So `hasType_app_bvar0` is a **tenth typing gate**, and the gate-cut table above becomes a
theorem: `CRPiDescend.lean` §3's `NormalEq.appDF_beta_of_parRedKn_of_typing` is this file's row
with `(HT : TypingStrengthening env univs)` threaded, and its cone (3914) does **not** contain
`IsDefEqU.weakN_iff`.  Site 7's `appDF` x `beta` row appeals to the hole in exactly **one** way,
not two: `TypingStrengthening`, i.e. `PiDescend`.
-/

end VEnv
end Lean4Lean
