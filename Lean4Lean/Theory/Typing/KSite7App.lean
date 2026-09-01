import Lean4Lean.Theory.Typing.KSite7

/-!
# Site 7's `appDF` × `extra` case, for `ParRedK`, with **no hypothesis**

`KDescend.lean`'s `NormalEq.appDF_extra_of_descendV` is the sorry-free replacement for
`ChurchRosser.lean`'s `NormalEq.appDF_extra_of_descend`, and it carries exactly one
hypothesis:

```
hK : ∀ {Δ e e'}, KStep Δ e e' → Δ ⊢ e ≫ e'
```

`ParRedPropRefute.lean`'s `not_hK_of_propMajor` shows that hypothesis is **false** against
`ChurchRosser.lean`'s `ParRed` as soon as one registered `.app` rule has a `Prop`-typed
major-premise slot.  Against `KEta.lean`'s `ParRedK` it is a *theorem*: `ParRedK.hK`.

This file therefore re-runs the whole `appDF` × `extra` argument in the `ParRedK` world and
discharges `hK`.  The result, `NormalEq.appDF_extra_of_descendVK`, is unconditional (no `hK`,
no `HasEtaK`, no `KDiamond`, no new `Params` field).

## What had to be ported, and what did not

**Did not:** `NormalEq.descendV` itself.  Its statement mentions `ParRedS` only inside
`DescentLam`, and `DescentLam.toK` below weakens a `ParRedS`-answer into a `ParRedKS`-answer
by pure relation monotonicity (`ParRedS.toK`, `KMeasure.lean`).  So the descent proper is
reused **verbatim**, holes and all -- and it has none.

**Did:** the three pieces whose *conclusions* are reductions, hence must be restated at
`ParRedKS`:

* `parRedK_of_matches` -- `ChurchRosser.lean`'s `parRed_of_matches`;
* `DescentLamK` + `DescentLamK.head` -- `ChurchRosser.lean`'s `DescentLam`;
* `DescentLamK.fire` -- `ChurchRosser.lean`'s `DescentLam.fire`.

Each port is a constructor-for-constructor transcription; `ParRedK` has every congruence
constructor `ParRed` has, and `KMeasure.lean` already supplies `ParRedKS.app`, `.lam`,
`.hasType`, `.defeq`, `.weakN`.  Nothing in the ported proofs needed a new idea, which is
itself the content: **the descent machinery is insensitive to which reduction relation it runs
over.**  The defect the `propMajor` witness exposes is entirely in whether the rule may fire
up to definitional equality of the major premise, and that is one constructor.

## Where this leaves site 7

`KSite7.lean`'s `parRedKStatement_of_domEq` closes four of nine cases (`refl`, `sortDF`,
`constDF`, `proofIrrel`) and `etaR_case` closes `etaR` against `WeakNInvDS`.  This file closes
the hardest sub-case of `appDF`, the one that motivated `NormalEq.descend`'s existence.  The
ledger of what is *still* open is `site7_ledger` at the end of this file, stated in Lean so it
cannot drift from the source.
-/

namespace Lean4Lean

open VExpr

namespace VEnv

variable [Params]
open Params

set_option hygiene false
local notation:65 Γ " ⊢ " e " : " A:36 => HasType env univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 " : " A:36 => IsDefEq env univs Γ e1 e2 A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 => IsDefEqU env univs Γ e1 e2
local notation:65 Γ " ⊢ " e1 " ≡ₚ " e2:30 => NormalEq Γ e1 e2
local notation:65 Γ " ⊢ " e1 " ≫ " e2:36 => ParRed Γ e1 e2
local notation:65 Γ " ⊢ " e1 " ≫* " e2:36 => ParRedS Γ e1 e2

/-! ## The three ports -/

omit [Params] in
/-- `parRed_of_matches`, **generic in the development relation**.  Reduce a matched term's
arguments in place; the spine is untouched, so the result still matches the same pattern with
the reduced arguments.

The proof of `parRedK_of_matches` used exactly two constructors of `ParRedK` -- `const` and
`app` -- so those two closure properties are all it needs.  Abstracting them is what lets the
*graded* relation `ParRedKn n` (`KKetaRow.lean`) reuse this body verbatim instead of
duplicating it: `ParRedKn n Γ` satisfies both at the **same** grade `n`, which is the fact the
grade-preservation conjecture for this row amounts to. -/
theorem develop_of_matches {R : VExpr → VExpr → Prop}
    (hRc : ∀ {c : Lean.Name} {ls : List VLevel}, R (.const c ls) (.const c ls))
    (hRa : ∀ {f f' a a' : VExpr}, R f f' → R a a' → R (.app f a) (.app f' a')) :
    ∀ {q : Pattern} {g : VExpr} {m1 : q.LPath → List VLevel} {m2 m2' : q.Path → VExpr},
      q.Matches g m1 m2 → (∀ x, R (m2 x) (m2' x)) →
      ∃ g', R g g' ∧ q.Matches g' m1 m2'
  | .const c, _, _, _, m2', .const, _ => ⟨_, hRc, by
      have : m2' = nofun := funext nofun
      subst this; exact .const⟩
  | .var q, _, _, _, m2', .var h, hr => by
    obtain ⟨g', h1, h2⟩ :=
      develop_of_matches hRc hRa h (m2' := fun x => m2' (some x)) (fun x => hr (some x))
    refine ⟨.app g' (m2' none), hRa h1 (hr none), ?_⟩
    have : m2' = (·.elim (m2' none) fun x => m2' (some x)) := funext fun x => by cases x <;> rfl
    rw [this]; exact .var h2
  | .app q₁ q₂, _, _, _, m2', .app h1 h2, hr => by
    obtain ⟨g1, a1, b1⟩ :=
      develop_of_matches hRc hRa h1 (m2' := fun x => m2' (.inl x)) (fun x => hr (.inl x))
    obtain ⟨g2, a2, b2⟩ :=
      develop_of_matches hRc hRa h2 (m2' := fun x => m2' (.inr x)) (fun x => hr (.inr x))
    refine ⟨.app g1 g2, hRa a1 a2, ?_⟩
    have : m2' = Sum.elim (fun x => m2' (.inl x)) (fun x => m2' (.inr x)) :=
      funext fun x => by cases x <;> rfl
    rw [this]; exact .app b1 b2

/-- `parRed_of_matches` for `ParRedK`: the instance of `develop_of_matches` at `ParRedK Γ`.
Statement unchanged from before the generalisation. -/
theorem parRedK_of_matches {Γ : List VExpr} {q : Pattern} {g : VExpr}
    {m1 : q.LPath → List VLevel} {m2 m2' : q.Path → VExpr}
    (hm : q.Matches g m1 m2) (hr : ∀ x, ParRedK Γ (m2 x) (m2' x)) :
    ∃ g', ParRedK Γ g g' ∧ q.Matches g' m1 m2' :=
  develop_of_matches (R := ParRedK Γ) .const .app hm hr

/-- `DescentLam` for `ParRedK`.  The only change is `ParRedS` → `ParRedKS` in the two
reduction positions; the `NormalEq` and level data are untouched. -/
def DescentLamK : Nat → (Γ : List VExpr) → (q : Pattern) → VExpr → VExpr →
    (q.LPath → List VLevel) → (q.Path → VExpr) → Prop
  | 0, Γ, q, g, _, n1, n2 =>
    ∃ t n1' n, ParRedKS Γ g t ∧ q.Matches t n1' n ∧
      (∀ lp, List.Forall₂ (· ≈ ·) (n1' lp) (n1 lp)) ∧
      (∀ lp, ∀ l ∈ n1' lp, VLevel.WF univs l) ∧
      (∀ lp, ∀ l ∈ n1 lp, VLevel.WF univs l) ∧
      (∀ x, NormalEq Γ (n x) (n2 x))
  | k+1, Γ, q, g, g', n1, n2 =>
    ∃ A e B, ParRedKS Γ g (.lam A e) ∧ HasType env univs Γ g' (.forallE A B) ∧
      DescentLamK k (A::Γ) (.var q) e (.app g'.lift (.bvar 0)) n1
        (fun x => x.elim (.bvar 0) fun y => (n2 y).lift)

/-- **Relation monotonicity: `NormalEq.descendV` is reused unchanged.**  A `ParRedS`-answer is
a `ParRedKS`-answer, by `ParRedS.toK` at each of the two reduction positions.  This is why this
file does not have to re-prove the descent: the descent's output is weakened here instead. -/
theorem DescentLam.toK : ∀ {k : Nat} {Γ : List VExpr} {q : Pattern} {g g' : VExpr}
    {n1 : q.LPath → List VLevel} {n2 : q.Path → VExpr},
    DescentLam k Γ q g g' n1 n2 → DescentLamK k Γ q g g' n1 n2
  | 0, _, _, _, _, _, _, ⟨t, u1, u2, h, rest⟩ => ⟨t, u1, u2, h.toK, rest⟩
  | _+1, _, _, _, _, _, _, ⟨A, e, B, h, hty, D⟩ => ⟨A, e, B, h.toK, hty, DescentLam.toK D⟩

/-- Prepend a reduction to a `ParRedK` answer. -/
theorem DescentLamK.head {k : Nat} {Γ : List VExpr} {q : Pattern} {g g₀ g' : VExpr}
    {n1 : q.LPath → List VLevel} {n2 : q.Path → VExpr}
    (hred : ParRedKS Γ g g₀) (H : DescentLamK k Γ q g₀ g' n1 n2) :
    DescentLamK k Γ q g g' n1 n2 := by
  cases k with
  | zero => let ⟨t, u1, u2, h, rest⟩ := H; exact ⟨t, u1, u2, hred.trans h, rest⟩
  | succ k => let ⟨A, e, B, h, rest⟩ := H; exact ⟨A, e, B, hred.trans h, rest⟩

/-- Replace the right-hand arguments by pointwise-equal ones. -/
theorem DescentLamK.congr_args {k : Nat} {Γ : List VExpr} {q : Pattern} {g g' : VExpr}
    {n1 : q.LPath → List VLevel} {n2 n2' : q.Path → VExpr}
    (h : ∀ x, n2 x = n2' x) (H : DescentLamK k Γ q g g' n1 n2) :
    DescentLamK k Γ q g g' n1 n2' := funext h ▸ H

/-- `DescentLam.fire` for `ParRedK`.  Discharge the pending eta layers: the caller supplies
`bot`, which fires the rule at zero layers in an arbitrary context extension, and each layer is
climbed back with `NormalEq.etaL`.

The proof is `ChurchRosser.lean`'s, with `ParRedS.app`/`ParRedS.lam` replaced by
`ParRedKS.app`/`ParRedKS.lam`.  No case is added: `DescentLamK`'s reduction positions are
opaque to the argument. -/
theorem DescentLamK.fire : ∀ {k : Nat} {Γ : List VExpr} {P : Pattern} {S g g' : VExpr}
    {n1 : P.LPath → List VLevel} {n2 : P.Path → VExpr},
    OnCtx Γ (IsType env univs) → (∃ T, Γ ⊢ g : T) → Γ ⊢ S ≡ g' →
    (∀ {Γ' : List VExpr} {n : Nat} {t : VExpr} {u1 u2},
      Ctx.LiftN n 0 Γ Γ' → OnCtx Γ' (IsType env univs) → (∃ T, Γ' ⊢ t : T) →
      P.Matches t u1 u2 →
      (∀ lp, List.Forall₂ (· ≈ ·) (u1 lp) (n1 lp)) →
      (∀ lp, ∀ l ∈ u1 lp, VLevel.WF univs l) →
      (∀ x, Γ' ⊢ u2 x ≡ₚ (n2 x).liftN n) →
      ∃ s, ParRedKS Γ' t s ∧ Γ' ⊢ s ≡ₚ S.liftN n) →
    DescentLamK k Γ P g g' n1 n2 →
    ∃ t, ParRedKS Γ g t ∧ Γ ⊢ t ≡ₚ S := by
  intro k
  induction k with
  | zero =>
    rintro Γ P S g g' n1 n2 hΓ hg _ bot ⟨t, u1, u2, hred, hmt, hlv, hwa, hwb, hn⟩
    have ⟨_, hT⟩ := hg
    have ⟨s, hs1, hs2⟩ := bot (Γ' := Γ) (n := 0) (.zero []) hΓ ⟨_, hred.hasType hΓ hT⟩
      hmt hlv hwa (by simpa using hn)
    exact ⟨s, hred.trans hs1, by simpa using hs2⟩
  | succ k ih =>
    rintro Γ P S g g' n1 n2 hΓ hg hSg' bot ⟨A, e, B, hred, hty, D⟩
    have ⟨_, hgT⟩ := hg
    have ⟨⟨_, hA⟩, heT⟩ := (hred.hasType hΓ hgT).lam_inv henv hΓ
    have hΓA : OnCtx (A::Γ) (IsType env univs) := ⟨hΓ, _, hA⟩
    have hSty : Γ ⊢ S : .forallE A B := (hSg'.symm.of_l henv hΓ hty).hasType.2
    have hSl : Γ ⊢ S ≡ g' : .forallE A B := hSg'.of_l henv hΓ hSty
    have hbot' : ∀ {Γ' : List VExpr} {n : Nat} {t : VExpr}
        {u1 : (Pattern.var P).LPath → List VLevel} {u2 : (Pattern.var P).Path → VExpr},
        Ctx.LiftN n 0 (A::Γ) Γ' → OnCtx Γ' (IsType env univs) → (∃ T, Γ' ⊢ t : T) →
        (Pattern.var P).Matches t u1 u2 →
        (∀ lp, List.Forall₂ (· ≈ ·) (u1 lp) (n1 lp)) →
        (∀ lp, ∀ l ∈ u1 lp, VLevel.WF univs l) →
        (∀ x, Γ' ⊢ u2 x ≡ₚ ((x.elim (.bvar 0) fun y => (n2 y).lift : VExpr)).liftN n) →
        ∃ s, ParRedKS Γ' t s ∧ Γ' ⊢ s ≡ₚ ((VExpr.app S.lift (.bvar 0))).liftN n := by
      intro Γ' n t u1 u2 W hΓ' ht' hmt' hlv' hwa' hn'
      cases hmt' with
      | @var _ tf _ tg ta hmtf =>
        rename_i hmtf
        have ⟨_, htT⟩ := ht'
        have ⟨_, _, htf, hta⟩ := htT.app_inv henv hΓ'
        have ⟨s, hs1, hs2⟩ :=
          bot (Ctx.LiftN.comp (Nat.le_refl 0) (Nat.zero_le _) .one W) hΓ' ⟨_, htf⟩ hmtf hlv'
            hwa' (fun y => by simpa [VExpr.liftN_liftN] using hn' (some y))
        have hbv : Γ' ⊢ ta ≡ₚ .bvar n := by simpa [VExpr.liftN] using hn' none
        have hs' := hs1.hasType hΓ' htf
        refine ⟨.app s ta, ParRedKS.app hs1 .rfl, ?_⟩
        have hS' := ((hs2.defeq hΓ').of_l henv hΓ' hs').hasType.2
        have hbvT := ((hbv.defeq hΓ').of_l henv hΓ' hta).hasType.2
        simpa [VExpr.liftN, VExpr.liftN_liftN] using
          NormalEq.appDF hs' hS' hta hbvT hs2 hbv
    have ⟨t, ht1, ht2⟩ := ih hΓA heT
      ⟨_, .appDF (hSl.weakN henv .one) (.bvar .zero)⟩ hbot' D
    exact ⟨_, hred.trans (ParRedKS.lam .rfl ht1), .etaL hSty ht2⟩

/-! ## The case itself

`NormalEq.appDF_extra_of_descendVK` is `KDescend.lean`'s `NormalEq.appDF_extra_of_descendV`
with `ParRed`/`ParRedS` replaced by `ParRedK`/`ParRedKS` **and the `hK` hypothesis deleted**.
The single firing step, which in `descendV` reads `hK (.mk r1 hmK hckK htf' hdq)`, here reads
`ParRedK.hK (.mk r1 hmK hckK htf' hdq)`.

That one-token difference is the whole repair, and `ParRedPropRefute.lean`'s
`not_hK_of_propMajor` is the proof that no smaller one exists. -/

/-- **Site 7's `appDF` × `extra` case, unconditionally.**  The `hK` hypothesis of
`NormalEq.appDF_extra_of_descendV` is discharged by `ParRedK.hK`.

Read against `ParRedPropRefute.lean`: `not_parRedStatement_of_propMajor` refutes site 7 for
`ParRed` at precisely this case, and `ParRedK.propMajor_fires` kills its rigidity hypothesis.
This theorem is the positive form -- the case that was refuted is now proved. -/
theorem NormalEq.appDF_extra_of_descendVK'
    {Γ : List VExpr} {f A B a b f₂ : VExpr} {R : VExpr → VExpr → Prop}
    (hRs : ∀ {e e' : VExpr}, R e e' → ParRedK Γ e e')
    (hRc : ∀ {c : Lean.Name} {ls : List VLevel}, R (.const c ls) (.const c ls))
    (hRa : ∀ {f f' a a' : VExpr}, R f f' → R a a' → R (.app f a) (.app f' a'))
    (hΓ : OnCtx Γ (IsType env univs))
    (l1 : Γ ⊢ f : .forallE A B) (l2 : Γ ⊢ f₂ : .forallE A B)
    (l3 : Γ ⊢ a : A) (l4 : Γ ⊢ b : A)
    (ih1 : ∀ {e₂'}, R f₂ e₂' → ∃ e₁', ParRedKS Γ f e₁' ∧ Γ ⊢ e₁' ≡ₚ e₂')
    (ih2 : ∀ {e₂'}, R b e₂' → ∃ e₁', ParRedKS Γ a e₁' ∧ Γ ⊢ e₁' ≡ₚ e₂')
    {p : Pattern} {r : p.RHS × p.Check} {m1 m2 m2'}
    (r1 : Params.Pat p r) (r2 : p.Matches (f₂.app b) m1 m2)
    (r3 : Pattern.Check.OK (IsDefEqU env univs Γ) m1 m2 r.snd)
    (r4 : ∀ x, R (m2 x) (m2' x)) :
    ∃ e₁', ParRedKS Γ (f.app a) e₁' ∧ Γ ⊢ e₁' ≡ₚ Pattern.RHS.apply m1 m2' r.fst := by
  cases r2 with
  | var h => exact absurd r1 Params.pat_not_var
  | @app q₁ _ f1 g1 q₂ _ f2 g2 h1 h2 =>
    obtain ⟨hq1, hq2⟩ := Params.pat_app_noApp r1
    obtain ⟨f₂', hpf, hmf⟩ :=
      develop_of_matches hRc hRa h1 (m2' := fun x => m2' (.inl x)) (fun x => r4 (.inl x))
    obtain ⟨b', hpb, hmb⟩ :=
      develop_of_matches hRc hRa h2 (m2' := fun x => m2' (.inr x)) (fun x => r4 (.inr x))
    obtain ⟨tf, hf1, hf2⟩ := ih1 hpf
    obtain ⟨ta, ha1, ha2⟩ := ih2 hpb
    have heq : Sum.elim (fun x => m2' (Sum.inl x)) (fun x => m2' (Sum.inr x)) = m2' :=
      funext fun x => by cases x <;> rfl
    have hmnode : (q₁.app q₂).Matches (f₂'.app b') (Sum.elim f1 f2) m2' := heq ▸ .app hmf hmb
    have hb'ty : Γ ⊢ b' : A := (hRs hpb).hasType hΓ l4
    have hf₂'ty : Γ ⊢ f₂' : .forallE A B := (hRs hpf).hasType hΓ l2
    have htf : Γ ⊢ tf : .forallE A B := hf1.hasType hΓ l1
    have hta : Γ ⊢ ta : A := ha1.hasType hΓ l3
    have hnode : Γ ⊢ tf.app ta ≡ₚ f₂'.app b' := .appDF htf hf₂'ty hta hb'ty hf2 ha2
    have hck' : Pattern.Check.OK (IsDefEqU env univs Γ) (p := q₁.app q₂)
        (Sum.elim f1 f2) m2' r.snd :=
      r3.congr_defeq hΓ _ fun x _ hty => ⟨_, (hRs (r4 x)).defeq hΓ hty⟩
    have hwB : ∀ lp, ∀ l ∈ Sum.elim f1 f2 lp, VLevel.WF univs l :=
      hmnode.levelWF hΓ (hf₂'ty.app hb'ty)
    -- The node, matched at `.var q₁`: the function side's pattern, argument position free.
    have hmvar : (Pattern.var q₁).Matches (f₂'.app b') f1
        (fun x => x.elim b' (fun y => m2' (.inl y))) := .var hmf
    -- **The firing step**, quantified over context extensions because `DescentLamK.fire`
    -- descends under one binder per pending eta layer.
    have hbot : ∀ {Γ' : List VExpr} {n : Nat} {t : VExpr}
        {u1 : (Pattern.var q₁).LPath → List VLevel} {u2 : (Pattern.var q₁).Path → VExpr},
        Ctx.LiftN n 0 Γ Γ' → OnCtx Γ' (IsType env univs) → (∃ T, Γ' ⊢ t : T) →
        (Pattern.var q₁).Matches t u1 u2 →
        (∀ lp, List.Forall₂ (· ≈ ·) (u1 lp) (f1 lp)) →
        (∀ lp, ∀ l ∈ u1 lp, VLevel.WF univs l) →
        (∀ x, Γ' ⊢ u2 x ≡ₚ ((x.elim b' (fun y => m2' (.inl y)) : VExpr)).liftN n) →
        ∃ s, ParRedKS Γ' t s ∧
          Γ' ⊢ s ≡ₚ (Pattern.RHS.apply (p := q₁.app q₂) (Sum.elim f1 f2) m2' r.fst).liftN n := by
      intro Γ' n t u1 u2 W hΓ' ht' hmt hlv hwA hne
      cases hmt with
      | @var _ tf' _ g1' ta' hmtf =>
        rename_i hmtf
        have ⟨_, htT⟩ := ht'
        have ⟨A₀, B₀, htf', hta'⟩ := htT.app_inv henv hΓ'
        -- the canonical major premise, weakened into `Γ'`
        have hmb' : q₂.Matches (b'.liftN n) f2 (fun x => (m2' (.inr x)).liftN n) :=
          Pattern.matches_liftN.2 ⟨_, hmb, fun _ => rfl⟩
        have hb'W : Γ' ⊢ b'.liftN n : A.liftN n := hb'ty.weakN henv W
        have hbv : Γ' ⊢ ta' ≡ₚ b'.liftN n := by simpa using hne none
        have hleaf : ∀ x, Γ' ⊢ g1' x ≡ₚ (m2' (.inl x)).liftN n := fun x => by
          simpa using hne (some x)
        -- the K-redex's data, assembled
        have hmK : (q₁.app q₂).Matches (.app tf' (b'.liftN n)) (Sum.elim u1 f2)
            (Sum.elim g1' (fun x => (m2' (.inr x)).liftN n)) := .app hmtf hmb'
        have hlvS : ∀ lp, List.Forall₂ (· ≈ ·)
            (Sum.elim u1 f2 lp) (Sum.elim f1 f2 lp) := by
          rintro (lp|lp)
          · exact hlv lp
          · exact VLevel.forall₂_equiv_refl _
        have flipeq : ∀ {l1 l2 : List VLevel},
            List.Forall₂ (· ≈ ·) l1 l2 → List.Forall₂ (· ≈ ·) l2 l1 := by
          intro l1 l2 h
          induction h with
          | nil => exact .nil
          | cons h _ ih => exact .cons h.symm ih
        have hlvS' : ∀ lp, List.Forall₂ (· ≈ ·)
            (Sum.elim f1 f2 lp) (Sum.elim u1 f2 lp) := fun lp => flipeq (hlvS lp)
        have hwAS : ∀ lp, ∀ l ∈ Sum.elim u1 f2 lp, VLevel.WF univs l := by
          rintro (lp|lp)
          · exact hwA lp
          · exact hwB (.inr lp)
        have hneS : ∀ x : (q₁.app q₂).Path,
            Γ' ⊢ (Sum.elim g1' (fun y => (m2' (.inr y)).liftN n) : _ → VExpr) x
              ≡ₚ (m2' x).liftN n := by
          rintro (x|x)
          · exact hleaf x
          · exact have ⟨_, ht⟩ := hmb'.hasType hΓ' hb'W x; .refl ht
        have hckW := hck'.weakN W r.snd
        have hckK : Pattern.Check.OK (IsDefEqU env univs Γ') (p := q₁.app q₂)
            (Sum.elim u1 f2) (Sum.elim g1' (fun y => (m2' (.inr y)).liftN n)) r.snd := by
          refine hckW.map_levels (fun x i y j hl => ?_) (fun u v h => ?_)
          · exact ((VLevel.forall₂_getD (hlvS x) i).trans hl).trans
              (VLevel.forall₂_getD (hlvS y) j).symm
          · obtain ⟨T, hT⟩ := h
            have step : ∀ (w : (q₁.app q₂).RHS) {C},
                Γ' ⊢ Pattern.RHS.apply (p := q₁.app q₂) (Sum.elim f1 f2)
                      (fun x => (m2' x).liftN n) w : C →
                Γ' ⊢ Pattern.RHS.apply (p := q₁.app q₂) (Sum.elim f1 f2)
                      (fun x => (m2' x).liftN n) w ≡
                    Pattern.RHS.apply (p := q₁.app q₂) (Sum.elim u1 f2)
                      (Sum.elim g1' (fun y => (m2' (.inr y)).liftN n)) w := by
              intro w C hw
              have hins := NormalEq.apply_instL (p := q₁.app q₂) (r := w) hΓ' hwB hwAS hlvS' hw
              have ⟨_, hh⟩ := hins.defeq hΓ'
              refine (hins.defeq hΓ').trans henv hΓ'
                (IsDefEqU.apply_pat hΓ'
                  (fun x _ _ => ((hneS x).defeq hΓ').symm) hh.hasType.2)
            exact ((step u hT.hasType.1).symm.trans henv hΓ' ⟨_, hT⟩).trans henv hΓ'
              (step v hT.hasType.2)
        -- **`KStep` fires, and it is a `ParRedK` step outright** (`ParRedK.hK`).  Only the
        -- function side matches; the argument `ta'` is bridged to `b'` by the node's own
        -- `NormalEq`, which is exactly what `KStep.mk`'s `hdq` premise asks for.
        have hdq : Γ' ⊢ ta' ≡ b'.liftN n : A₀ :=
          ((hbv.defeq hΓ').of_l henv hΓ' hta')
        have hfire : ParRedK Γ' (.app tf' ta')
            (Pattern.RHS.apply (p := q₁.app q₂) (Sum.elim u1 f2)
              (Sum.elim g1' (fun y => (m2' (.inr y)).liftN n)) r.fst) :=
          ParRedK.hK (.mk r1 hmK hckK htf' hdq)
        refine ⟨_, .tail .rfl hfire, ?_⟩
        rw [Pattern.RHS.liftN_apply (p := q₁.app q₂) (m1 := Sum.elim f1 f2) (m2 := m2') r.fst]
        exact NormalEq.apply_congr (p := q₁.app q₂) (r := r.fst) hΓ' hwAS hwB hlvS
          (fun x _ _ => hneS x) (hfire.hasType hΓ' htT)
    match NormalEq.descendV _ (Nat.le_refl _)
        (show (Pattern.var q₁).NoApp from hq1) hΓ hnode hmvar with
    | .inl ⟨k, D⟩ =>
      have ⟨t, ht1, ht2⟩ := DescentLamK.fire hΓ ⟨_, htf.app hta⟩
        (Params.pat_wf r1 hmnode hΓ (hf₂'ty.app hb'ty) hck').symm hbot D.toK
      exact ⟨t, (ParRedKS.app hf1 ha1).trans ht1, ht2⟩
    | .inr ⟨P, hP, hp1, hp2⟩ =>
      exact ⟨_, ParRedKS.app hf1 ha1,
        .proofIrrel hP hp1
          ((Params.pat_wf r1 hmnode hΓ hp2 hck').of_l henv hΓ hp2).hasType.2⟩

/-- **The `ParRedK` instance**, with the statement `KSite7Rows.lean` and `KKetaRow.lean` call.
Unchanged from before `appDF_extra_of_descendVK'` was abstracted out of it. -/
theorem NormalEq.appDF_extra_of_descendVK
    {Γ : List VExpr} {f A B a b f₂ : VExpr}
    (hΓ : OnCtx Γ (IsType env univs))
    (l1 : Γ ⊢ f : .forallE A B) (l2 : Γ ⊢ f₂ : .forallE A B)
    (l3 : Γ ⊢ a : A) (l4 : Γ ⊢ b : A)
    (ih1 : ∀ {e₂'}, ParRedK Γ f₂ e₂' → ∃ e₁', ParRedKS Γ f e₁' ∧ Γ ⊢ e₁' ≡ₚ e₂')
    (ih2 : ∀ {e₂'}, ParRedK Γ b e₂' → ∃ e₁', ParRedKS Γ a e₁' ∧ Γ ⊢ e₁' ≡ₚ e₂')
    {p : Pattern} {r : p.RHS × p.Check} {m1 m2 m2'}
    (r1 : Params.Pat p r) (r2 : p.Matches (f₂.app b) m1 m2)
    (r3 : Pattern.Check.OK (IsDefEqU env univs Γ) m1 m2 r.snd)
    (r4 : ∀ x, ParRedK Γ (m2 x) (m2' x)) :
    ∃ e₁', ParRedKS Γ (f.app a) e₁' ∧ Γ ⊢ e₁' ≡ₚ Pattern.RHS.apply m1 m2' r.fst :=
  NormalEq.appDF_extra_of_descendVK' (R := ParRedK Γ) id .const .app
    hΓ l1 l2 l3 l4 ih1 ih2 r1 r2 r3 r4

/-! ## The routine rows: `appDF` congruence, `lamDF`, `forallEDF`

These are `ChurchRosser.NormalEq.parRed`'s own case bodies with `ParRed`/`ParRedS` replaced by
`ParRedK`/`ParRedKS` and **one extra branch each** for the new constructor, discharged by the
`EtaK` consumer kit: `EtaK.not_lam` and `EtaK.not_forallE` say no `EtaK` step starts at a `.lam`
or a `.forallE`, so `keta` is unreachable at those nodes exactly as `extra` already was.

They are stated as standalone case lemmas, taking site 7's induction hypotheses as explicit
premises, so that the eventual induction is an assembly rather than a rewrite. -/

/-- Site 7's `appDF` x congruence row. -/
theorem NormalEq.appDF_app_of_parRedK {Γ : List VExpr} {f A B f₂ a b f' b' : VExpr}
    (hΓ : OnCtx Γ (IsType env univs))
    (l1 : Γ ⊢ f : .forallE A B) (l2 : Γ ⊢ f₂ : .forallE A B)
    (l3 : Γ ⊢ a : A) (l4 : Γ ⊢ b : A)
    (ih1 : ∀ {e₂'}, ParRedK Γ f₂ e₂' → ∃ e₁', ParRedKS Γ f e₁' ∧ Γ ⊢ e₁' ≡ₚ e₂')
    (ih2 : ∀ {e₂'}, ParRedK Γ b e₂' → ∃ e₁', ParRedKS Γ a e₁' ∧ Γ ⊢ e₁' ≡ₚ e₂')
    (r1 : ParRedK Γ f₂ f') (r2 : ParRedK Γ b b') :
    ∃ e₁', ParRedKS Γ (.app f a) e₁' ∧ Γ ⊢ e₁' ≡ₚ .app f' b' :=
  let ⟨_, a1, a2⟩ := ih1 r1
  let ⟨_, b1, b2⟩ := ih2 r2
  ⟨_, a1.app b1,
    .appDF (a1.hasType hΓ l1) (r1.hasType hΓ l2) (b1.hasType hΓ l3) (r2.hasType hΓ l4) a2 b2⟩

/-- Site 7's `lamDF` row.  `extra` cannot match a `.lam` and `keta` cannot fire at one
(`EtaK.not_lam`), so `lam` is the only step. -/
theorem NormalEq.lamDF_of_parRedK {Γ : List VExpr} {A A₁ A₂ body₁ body₂ : VExpr} {u : VLevel}
    (hΓ : OnCtx Γ (IsType env univs))
    (l1 : Γ ⊢ A ≡ A₁ : .sort u) (l2 : Γ ⊢ A ≡ A₂ : .sort u)
    (l3 : (A::Γ) ⊢ body₁ ≡ₚ body₂)
    (ih1 : ∀ {e₂'}, ParRedK (A::Γ) body₂ e₂' →
      ∃ e₁', ParRedKS (A::Γ) body₁ e₁' ∧ NormalEq (A::Γ) e₁' e₂')
    {e₂' : VExpr} (H2 : ParRedK Γ (.lam A₂ body₂) e₂') :
    ∃ e₁', ParRedKS Γ (.lam A₁ body₁) e₁' ∧ Γ ⊢ e₁' ≡ₚ e₂' := by
  cases H2 with
  | lam r1 r2 =>
    refine have hΓ' := (by exact ⟨hΓ, _, l1.hasType.1⟩); have ⟨_, h1⟩ := l3.defeq hΓ'; ?_
    have h2 := h1.hasType.1.defeqU_l henv hΓ' (l3.defeq hΓ')
    replace r2 := r2.defeqDFC hΓ (.succ .zero l2.symm) <| .defeqDFC henv (.succ .zero l2) h2
    let ⟨_, b1, b2⟩ := ih1 r2
    exact ⟨_, .lam .rfl (b1.defeqDFC hΓ (.succ .zero l1) h1.hasType.1),
      .lamDF l1 (.trans l2 (r1.defeq hΓ (.defeqU_l henv hΓ ⟨_, l2⟩ l1.hasType.1))) b2⟩
  | extra _ r2 => cases r2
  | keta hek _ => exact absurd hek EtaK.not_lam

/-- Site 7's `forallEDF` row.  Same two impossible branches as `lamDF`, by
`EtaK.not_forallE`. -/
theorem NormalEq.forallEDF_of_parRedK
    {Γ : List VExpr} {A A₁ A₂ B₁ B₂ : VExpr} {u v : VLevel}
    (hΓ : OnCtx Γ (IsType env univs))
    (l1 : Γ ⊢ A ≡ A₁ : .sort u) (l2 : Γ ⊢ A₁ ≡ₚ A₂)
    (l3 : (A::Γ) ⊢ B₁ : .sort v) (l4 : (A::Γ) ⊢ B₁ ≡ₚ B₂)
    (ih1 : ∀ {e₂'}, ParRedK Γ A₂ e₂' → ∃ e₁', ParRedKS Γ A₁ e₁' ∧ Γ ⊢ e₁' ≡ₚ e₂')
    (ih2 : ∀ {e₂'}, ParRedK (A::Γ) B₂ e₂' →
      ∃ e₁', ParRedKS (A::Γ) B₁ e₁' ∧ NormalEq (A::Γ) e₁' e₂')
    {e₂' : VExpr} (H2 : ParRedK Γ (.forallE A₂ B₂) e₂') :
    ∃ e₁', ParRedKS Γ (.forallE A₁ B₁) e₁' ∧ Γ ⊢ e₁' ≡ₚ e₂' := by
  cases H2 with
  | forallE r1 r2 =>
    let ⟨_, a1, a2⟩ := ih1 r1
    refine have hΓ' := (by exact ⟨hΓ, _, l1.hasType.1⟩)
      have h2 := l3.defeqU_l henv hΓ' (l4.defeq hΓ'); ?_
    have W := l1.transU_l henv hΓ (l2.defeq hΓ)
    replace r2 := r2.defeqDFC hΓ (.succ .zero W.symm) <| .defeqDFC henv (.succ .zero W) h2
    let ⟨_, b1, b2⟩ := ih2 r2
    have := r1.defeq hΓ (.defeqU_l henv hΓ ⟨_, W⟩ l1.hasType.1)
    exact ⟨_, .forallE a1 (b1.defeqDFC hΓ (.succ .zero l1) l3),
      .forallEDF (.transU_l henv hΓ (W.trans this) (a2.defeq hΓ).symm) a2
        (b1.hasType hΓ' l3) b2⟩
  | extra _ r2 => cases r2
  | keta hek _ => exact absurd hek EtaK.not_forallE


/-! ## Ledger: site 7 for `ParRedK`, case by case

Recorded here rather than in a handoff document so it cannot drift from the source.  `H1` is
site 7's `NormalEq` premise, `H2` its `ParRedK` step; the rows are `H1`'s constructors.

* `refl`, `sortDF`, `constDF`, `proofIrrel` -- **closed, no hypothesis**:
  `KSite7.parRedKStatement_of_domEq` (these four are exactly `DomEq`).
* `etaR` -- **closed against `WeakNInvDS`**: `KSite7.etaR_case`, `KSite7.etaR_inner`.
* `appDF` x `extra` -- **closed, no hypothesis**: `NormalEq.appDF_extra_of_descendVK`, this file.
* `appDF` x `keta .here` -- reduces to the row above; same shape, a `KStep` at the node.
* `appDF` x `beta` -- open; needs `ChurchRosser.ParRedExt.parRed_beta` ported to `ParRedK`.
* `appDF` x `keta .under` -- open; needs an inner induction like `KSite7.etaR_inner`.
* `appDF` x congruence -- **closed, no hypothesis**: `NormalEq.appDF_app_of_parRedK`, this file.
* `lamDF`, `forallEDF` -- **closed, no hypothesis**: `NormalEq.lamDF_of_parRedK`,
  `NormalEq.forallEDF_of_parRedK`, this file.  A `ParRedK` step out of a `.lam`/`.forallE` can
  only be `lam`/`forallE`: `extra` cannot match, and `keta` cannot fire by `EtaK.not_lam` /
  `EtaK.not_forallE`.
* `etaL` -- open; the mirror of `etaR`, and `KSite7.etaR_inner`'s invariant is not symmetric.

## Ledger: what `church_rosser`-on-`ParRedK` still owes

Re-deriving `IsDefEq.church_rosser` over `ParRedK` needs four things beyond site 7, and none is
a consequence of this file:

1. `ParRed.weakN_inv` -- **false** in equality form once a K-step is live
   (`KEta.not_weakNInvStatement_of_etaK`).  Its replacement is `WeakNInvDS`, plus
   `KStepLiftInv` (which wants a new `Params` field, `KTable`/M3) and `PiTypeDescend`
   (= `IsDefEqU.weakN_iff`).
2. `CParRed.exists` -- needs a classical decision of `NonNeutralK` and a canonical K-contractum.
3. `ParRed.triangle` -- needs `KDiamond` (`KDescend.lean`) and `EtaKDiamond` (`KEta.lean`),
   both stated and unproved.
4. site 7's three open rows above (`appDF` x `beta`, `appDF` x `keta .under`, `etaL`), plus
   the `WeakNInvDS` residual that `etaR` is closed against.

**Score after this file: six of nine `H1` rows closed with no hypothesis at all**
(`refl`, `sortDF`, `constDF`, `proofIrrel`, `lamDF`, `forallEDF`), `etaR` closed against
`WeakNInvDS`, and `appDF` closed except for its `beta` and `keta .under` sub-cases.  What is
left is `etaL` and those two sub-cases.

So the census does **not** drop this round and `ChurchRosser.NormalEq.descend` stays: nothing
yet replaces it in `NormalEq.parRed`, and deleting it before `parRed` is re-proved would only
move the hole.

## Measurement: where `IsDefEqU.weakN_iff` enters, in the `ParRedK` world

Cones measured with `scripts/hole-cone.lean`'s `deps` (`allowOpaque := true`).

*Clean of `IsDefEqU.weakN_iff`* (only `forallE_inv_stratified` + `WF.rigidShapeUniqNS`):
`parRedK_of_matches`, `DescentLam.toK`, `DescentLamK.fire`, `NormalEq.appDF_app_of_parRedK`,
`NormalEq.lamDF_of_parRedK`, `NormalEq.forallEDF_of_parRedK`, `ParRedK.defeq`,
`KSite7.DomEq.parRedK`, `KSite7.parRedKStatement_of_domEq`.  So **five of the six rows closed
without hypotheses are also clean of the 131-user hole.**

*Not clean:* `NormalEq.appDF_extra_of_descendVK` and `KSite7.etaR_case`, **both by the same
single path**

```
... -> NormalEq.trans -> NormalEq.weakN_iff -> NormalEq.weakN_inv_DFC -> IsDefEqU.weakN_iff
```

and `NormalEq.descendV` likewise (via `DescentLam.beta -> DescentLam.instN -> NormalEq.trans`).

**What is *not* in the `ParRedK` cone: `ParRed.weakN_inv`.**  `ChurchRosser.NormalEq.parRed`
reaches the hole in one hop through it (`parRed -> ParRed.weakN_inv -> IsDefEqU.weakN_iff`); the
`ParRedK` route replaces that hop by the hypothesis `WeakNInvDS`, so on this side the *only*
entry is `NormalEq.trans`.  That is the entry `NormalEq`-strengthening would remove.

The cost is honest, though: discharging `WeakNInvDS` brings the second entry back.
`ParRed.weakN_inv` uses `IsDefEqU.weakN_iff` in exactly one case -- `extra`, to carry the
rule's `Pattern.Check.OK` side conditions downstairs -- and by `Pattern.RHS.liftN_apply` the
obligation there is `IsDefEqU Γ' (u.liftN n k) (v.liftN n k) -> IsDefEqU Γ u v` at
**arbitrary** `u`, `v`: full untyped conversion strengthening, with no shape restriction and no
typing-only weakening available.  `Pattern.Check.defeq` is genuinely used by the real ι-rule
(`PatternDecode.lean`'s `Check.ofDefeqs`), so this is not vacuous.  A `Params` field saying the
rule table's checks are strengthening-stable would break the circle; nothing else here does. -/

end VEnv
end Lean4Lean
