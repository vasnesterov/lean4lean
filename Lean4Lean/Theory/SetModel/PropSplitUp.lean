import Lean4Lean.Theory.SetModel.StableAudit

/-!
# A `PropSplit` whose `Stable` does not consume strengthening

`SetModel/StableAudit.lean` proves that the tree's only `PropSplit`,
`propSplitOf`, is `Stable` **iff** `PropDescend` holds, and that `PropDescend`'s
two `lift` fields follow from `TypingStrengthening` + `SortDescend` — the
strengthening hole (`Theory/Typing/UniqueTyping.lean`'s `IsDefEqU.weakN_iff`).
That was read as *"the model route is circular: every soundness fact it produces
is conditional on the statement one might hope to refute with it."*

**That reading is too strong, and this file is the counterexample.**  The
dependence is a property of `propSplitOf`'s *predicate*, not of `PropSplit`,
`PropSplit.Stable`, or `soundAbove`.  Replacing

    "A is a proposition at Γ"        (`propSplitOf`)

by

    "A is a proposition somewhere above Γ"      (`IsPropUp`, §2)

keeps `prop_sound`/`proof_sound` — from the same two inputs `PropUniq` and
`PropTypeAgree`, and nothing else — and makes **all four** of `Stable`'s
directions that strengthening was paying for into theorems:

* both `lift` fields, in **both** directions (§3).  Descent becomes composition
  of lifts (`Ctx.Lift'.comp`, already in the tree); ascent becomes the *pushout*
  of two lifts out of a common context (§1), which is pure syntax.
* the **ascent** halves of both `inst` fields (§4), by the substitution/lift
  square — again pure syntax.

What is left is `InstDescendUp` (§5): the two **descent** halves of the `inst`
fields.  Those are `PropDescend.sort_inst`/`proof_inst`, which `StableAudit.lean`
records as open *and blocked on `IsDefEqU.sort_forallE_inv`* — a different
statement from strengthening, in a different file.

So: **the model route does not have to consume the strengthening hole.**  What
it still consumes is `PropUniq`, `PropTypeAgree`, and substitution-descent.

## The exact price, and why this is not the trivial direction backwards

`IsPropUp` is a *weaker* predicate than `propSplitOf`'s.  §6 shows the two agree
on every well-typed input — the weakening only moves the predicate on syntax
that has no sort at `Γ`, which is exactly the region `Stable` quantifies over
(raw syntax) and `prop_sound` does not (typing premise).  §7 makes the trade
exact: collapsing `IsPropUp` back to the canonical predicate is **equivalent**
to `PropDescend.sort_lift`, i.e. to the very field that was being derived from
the hole.  §8 checks there is no regression: `PropDescend` still discharges
`InstDescendUp`.

## What this does *not* say

It does not say the model can now refute strengthening.  A `⊬` obtained from
`sound` would be conditional on `InstDescendUp`, which is open.  It says the
conditional is no longer *on the statement being refuted*, which is what made
the earlier route circular.
-/

namespace Lean4Lean

/-! ## 1. The pushout of two lifts -/

namespace Lift

/-- The left leg of the pushout of `l₁` and `l₂` (both out of a common
context): the lift that takes `l₁`'s target to the join. -/
def pushOutL : Lift → Lift → Lift
  | .refl, l₂ => l₂
  | .skip l₁, l₂ => .cons (pushOutL l₁ l₂)
  | .cons _, .refl => .refl
  | .cons l₁, .skip l₂ => .skip (pushOutL (.cons l₁) l₂)
  | .cons l₁, .cons l₂ => .cons (pushOutL l₁ l₂)
termination_by l₁ l₂ => sizeOf l₁ + sizeOf l₂

/-- The right leg of the pushout: the lift that takes `l₂`'s target to the
join. -/
def pushOutR : Lift → Lift → Lift
  | .refl, _ => .refl
  | .skip l₁, l₂ => .skip (pushOutR l₁ l₂)
  | .cons l₁, .refl => .cons l₁
  | .cons l₁, .skip l₂ => .cons (pushOutR (.cons l₁) l₂)
  | .cons l₁, .cons l₂ => .cons (pushOutR l₁ l₂)
termination_by l₁ l₂ => sizeOf l₁ + sizeOf l₂

/-- **The pushout square commutes.** -/
theorem pushOut_comp : ∀ l₁ l₂ : Lift,
    Lift.comp l₁ (pushOutL l₁ l₂) = Lift.comp l₂ (pushOutR l₁ l₂)
  | .refl, l₂ => by simp [pushOutL, pushOutR]
  | .skip l₁, l₂ => by
    simp only [pushOutL, pushOutR, comp]
    exact congrArg _ (pushOut_comp l₁ l₂)
  | .cons _, .refl => by simp [pushOutL, pushOutR]
  | .cons l₁, .skip l₂ => by
    simp only [pushOutL, pushOutR, comp]
    exact congrArg _ (pushOut_comp (.cons l₁) l₂)
  | .cons l₁, .cons l₂ => by
    simp only [pushOutL, pushOutR, comp]
    exact congrArg _ (pushOut_comp l₁ l₂)
termination_by l₁ l₂ => sizeOf l₁ + sizeOf l₂

end Lift

/-- **The pushout of two lifts out of a common context exists.**

Purely syntactic: no typing hypothesis, no environment.  This is the whole
technical content that makes `IsPropUp`'s `lift` stability free. -/
theorem Ctx.Lift'.pushOut : ∀ (l₁ l₂ : Lift) {Γ Γ₁ Γ₂ : List VExpr},
    Ctx.Lift' l₁ Γ Γ₁ → Ctx.Lift' l₂ Γ Γ₂ →
    ∃ Γ₃, Ctx.Lift' (Lift.pushOutL l₁ l₂) Γ₁ Γ₃ ∧ Ctx.Lift' (Lift.pushOutR l₁ l₂) Γ₂ Γ₃ := by
  intro l₁
  induction l₁ with
  | refl =>
    intro l₂ Γ Γ₁ Γ₂ H1 H2
    cases H1
    rw [Lift.pushOutL, Lift.pushOutR]
    exact ⟨Γ₂, H2, .refl⟩
  | skip l₁ ih =>
    intro l₂ Γ Γ₁ Γ₂ H1 H2
    cases H1 with
    | skip H1 =>
      obtain ⟨Γ₃, a, b⟩ := ih l₂ H1 H2
      rw [Lift.pushOutL, Lift.pushOutR]
      exact ⟨_, a.cons, b.skip⟩
  | cons l₁ ih =>
    intro l₂
    induction l₂ with
    | refl =>
      intro Γ Γ₁ Γ₂ H1 H2
      cases H2
      rw [Lift.pushOutL, Lift.pushOutR]
      exact ⟨Γ₁, .refl, H1⟩
    | skip l₂ ih2 =>
      intro Γ Γ₁ Γ₂ H1 H2
      cases H2 with
      | skip H2 =>
        obtain ⟨Γ₃, a, b⟩ := ih2 H1 H2
        rw [Lift.pushOutL, Lift.pushOutR]
        exact ⟨_, a.skip, b.cons⟩
    | cons l₂ _ =>
      intro Γ Γ₁ Γ₂ H1 H2
      cases H1 with
      | cons H1 =>
        cases H2 with
        | cons H2 =>
          obtain ⟨Γ₃, a, b⟩ := ih l₂ H1 H2
          have heq : ∀ X : VExpr, (X.lift' l₂).lift' (Lift.pushOutR l₁ l₂)
              = (X.lift' l₁).lift' (Lift.pushOutL l₁ l₂) := fun X => by
            rw [← VExpr.lift'_comp, ← VExpr.lift'_comp, Lift.pushOut_comp]
          rw [Lift.pushOutL, Lift.pushOutR]
          exact ⟨_, a.cons, heq _ ▸ b.cons⟩

/-! ## 2. The lift-closed proof-splitting predicates -/

namespace VEnv

variable {env : VEnv} {nv : ℕ}

/-- **`A` is a proposition somewhere above `Γ`.**

`propSplitOf`'s predicate is the `l = .refl` instance.  Closing under lifts is
what makes the two `lift` fields of `PropSplit.Stable` free: descent becomes
*prepending a step*, and ascent becomes the syntactic pushout of §1.  The price
is paid in the two `inst` fields (§4). -/
def IsPropUp (env : VEnv) (nv : ℕ) (ls : List ℕ) (Γ : List VExpr) (A : VExpr) : Prop :=
  ∃ (l : Lift) (Γ' : List VExpr) (u : VLevel),
    Ctx.Lift' l Γ Γ' ∧ u.WF nv ∧ env.HasType nv Γ' (A.lift' l) (.sort u) ∧ u.eval ls = 0

/-- **`e` is a proof somewhere above `Γ`.** -/
def IsProofUp (env : VEnv) (nv : ℕ) (ls : List ℕ) (Γ : List VExpr) (e : VExpr) : Prop :=
  ∃ (l : Lift) (Γ' : List VExpr) (B : VExpr) (u : VLevel),
    Ctx.Lift' l Γ Γ' ∧ u.WF nv ∧ env.HasType nv Γ' (e.lift' l) B ∧
      env.HasType nv Γ' B (.sort u) ∧ u.eval ls = 0

/-- The canonical predicate implies the lift-closed one, by the empty lift. -/
theorem IsPropUp.of_hasType {ls Γ A u} (hw : u.WF nv)
    (ht : env.HasType nv Γ A (.sort u)) (h0 : u.eval ls = 0) : env.IsPropUp nv ls Γ A :=
  ⟨.refl, Γ, u, .refl, hw, by simpa using ht, h0⟩

/-- The canonical predicate implies the lift-closed one, by the empty lift. -/
theorem IsProofUp.of_hasType {ls Γ e A u} (hw : u.WF nv)
    (he : env.HasType nv Γ e A) (hA : env.HasType nv Γ A (.sort u)) (h0 : u.eval ls = 0) :
    env.IsProofUp nv ls Γ e :=
  ⟨.refl, Γ, A, u, .refl, hw, by simpa using he, by simpa using hA, h0⟩

/-- **`prop_sound` for the lift-closed predicate, from `PropUniq` alone.**

This is the same input `propSplitOf` uses; closing under lifts costs nothing
here, because typing transports *forward* along a lift and `PropUniq` is
available at the far end. -/
theorem isPropUp_iff (henv : env.Ordered) (hU : env.PropUniq nv)
    {ls Γ A u} (hw : u.WF nv) (ht : env.HasType nv Γ A (.sort u)) :
    env.IsPropUp nv ls Γ A ↔ u.eval ls = 0 := by
  refine ⟨fun ⟨l, Γ', v, W, hv, hA, h0⟩ => ?_, fun h0 => .of_hasType hw ht h0⟩
  have h := ht.weak' henv W
  simp only [VExpr.lift'] at h
  exact (hU hv hw hA h).mp h0

/-- **`proof_sound` for the lift-closed predicate, from `PropTypeAgree` alone.** -/
theorem isProofUp_iff (henv : env.Ordered) (hT : env.PropTypeAgree nv)
    {ls Γ e A u} (hw : u.WF nv) (he : env.HasType nv Γ e A)
    (hA : env.HasType nv Γ A (.sort u)) :
    env.IsProofUp nv ls Γ e ↔ u.eval ls = 0 := by
  refine ⟨fun ⟨l, Γ', B, v, W, hv, he', hB, h0⟩ => ?_, fun h0 => .of_hasType hw he hA h0⟩
  have hA' := hA.weak' henv W
  simp only [VExpr.lift'] at hA'
  exact (hT hv hw he' (he.weak' henv W) hB hA').mp h0

/-! ## 3. The `lift` fields, free

Neither theorem below mentions `TypingStrengthening`, `SortDescend`,
`PropDescend`, or any other open statement: the descent direction is a
composition of lifts and the ascent direction is the pushout of §1. -/

/-- **Lift stability of `IsPropUp`, for a general lift.** -/
theorem isPropUp_lift' (henv : env.Ordered) {ρ : Lift} {Γ Γ' : List VExpr}
    (W : Ctx.Lift' ρ Γ Γ') {ls : List ℕ} {A : VExpr} :
    env.IsPropUp nv ls Γ' (A.lift' ρ) ↔ env.IsPropUp nv ls Γ A := by
  constructor
  · rintro ⟨l, Γ'', u, W', hu, hA, h0⟩
    exact ⟨Lift.comp ρ l, Γ'', u, W.comp W', hu, by rwa [VExpr.lift'_comp], h0⟩
  · rintro ⟨l, Γ'', u, W', hu, hA, h0⟩
    obtain ⟨Γ₃, a, b⟩ := Ctx.Lift'.pushOut ρ l W W'
    refine ⟨Lift.pushOutL ρ l, Γ₃, u, a, hu, ?_, h0⟩
    have h := hA.weak' henv b
    simp only [VExpr.lift'] at h
    rwa [← VExpr.lift'_comp, ← Lift.pushOut_comp, VExpr.lift'_comp] at h

/-- **Lift stability of `IsProofUp`, for a general lift.** -/
theorem isProofUp_lift' (henv : env.Ordered) {ρ : Lift} {Γ Γ' : List VExpr}
    (W : Ctx.Lift' ρ Γ Γ') {ls : List ℕ} {e : VExpr} :
    env.IsProofUp nv ls Γ' (e.lift' ρ) ↔ env.IsProofUp nv ls Γ e := by
  constructor
  · rintro ⟨l, Γ'', B, u, W', hu, he, hB, h0⟩
    exact ⟨Lift.comp ρ l, Γ'', B, u, W.comp W', hu, by rwa [VExpr.lift'_comp], hB, h0⟩
  · rintro ⟨l, Γ'', B, u, W', hu, he, hB, h0⟩
    obtain ⟨Γ₃, a, b⟩ := Ctx.Lift'.pushOut ρ l W W'
    refine ⟨Lift.pushOutL ρ l, Γ₃, B.lift' (Lift.pushOutR ρ l), u, a, hu, ?_, ?_, h0⟩
    · have h := he.weak' henv b
      rwa [← VExpr.lift'_comp, ← Lift.pushOut_comp, VExpr.lift'_comp] at h
    · have h := hB.weak' henv b
      simpa only [VExpr.lift'] using h

/-- **`PropSplit.Stable.prop_liftN` for the lift-closed predicate.** -/
theorem isPropUp_liftN (henv : env.Ordered) {n k : ℕ} {Γ Γ' : List VExpr}
    (W : Ctx.LiftN n k Γ Γ') {ls : List ℕ} {A : VExpr} :
    env.IsPropUp nv ls Γ' (A.liftN n k) ↔ env.IsPropUp nv ls Γ A := by
  rw [← VExpr.lift'_consN_skipN]
  exact isPropUp_lift' henv (Ctx.liftN_iff_lift'.1 W)

/-- **`PropSplit.Stable.proof_liftN` for the lift-closed predicate.** -/
theorem isProofUp_liftN (henv : env.Ordered) {n k : ℕ} {Γ Γ' : List VExpr}
    (W : Ctx.LiftN n k Γ Γ') {ls : List ℕ} {e : VExpr} :
    env.IsProofUp nv ls Γ' (e.liftN n k) ↔ env.IsProofUp nv ls Γ e := by
  rw [← VExpr.lift'_consN_skipN]
  exact isProofUp_lift' henv (Ctx.liftN_iff_lift'.1 W)

end VEnv


/-! ## 4. The substitution square, and the `inst` ascent

The two `inst` fields of `PropSplit.Stable` are `↔`s.  Their **ascent** halves —
from the unsubstituted body to the substituted one — are, like §3's, purely
syntactic: the substitution commutes past the lift.  Only the **descent** halves
remain open, and those are `PropDescend`'s `sort_inst`/`proof_inst`, which
`StableAudit.lean` records as blocked on `IsDefEqU.sort_forallE_inv`, not on
strengthening. -/

namespace VExpr

/-- The `consN` generalisation of `lift_r_one`. -/
theorem lift_r_liftN_one (e : VExpr) (ρ : Lift) : ∀ j : ℕ,
    (Subst.liftN (Subst.one e) j).lift_r (Lift.consN ρ j)
      = Subst.lift_l (Lift.consN ρ (j+1)) (Subst.liftN (Subst.one (e.lift' ρ)) j)
  | 0 => lift_r_one e ρ
  | j+1 => by
    show (Subst.lift _).lift_r (Lift.cons _) = _
    rw [← Subst.lift_r_lift, lift_r_liftN_one e ρ j, Subst.lift_l_lift]
    rfl

/-- The `consN` generalisation of `lift'_inst_hi`: a substitution at depth `j`
commutes with a lift that keeps the first `j+1` variables. -/
theorem lift'_inst_consN (C e : VExpr) (ρ : Lift) (j : ℕ) :
    (C.inst e j).lift' (Lift.consN ρ j)
      = (C.lift' (Lift.consN ρ (j+1))).inst (e.lift' ρ) j := by
  rw [instN_eq, instN_eq, lift'_subst, subst_lift', lift_r_liftN_one]

end VExpr

/-- **The substitution/lift square.**

Given a substitution `Γ₁ ⟶ Γ` and a lift `Γ₁ ⟶ Γ₂`, there is a lift
`Γ ⟶ Γ'` and a substitution `Γ₂ ⟶ Γ'` closing the square, together with the
term identity relating the two paths — stated under `j` extra binders so the
induction goes through.  No typing, no environment: this is de Bruijn
bookkeeping. -/
theorem Ctx.InstN.pushLift' : ∀ (l : Lift) {Γ₁ Γ₂ : List VExpr}, Ctx.Lift' l Γ₁ Γ₂ →
    ∀ {Γ₀ : List VExpr} {e₀ A₀ : VExpr} {k : ℕ} {Γ : List VExpr},
      Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ →
      ∃ (l' ρ : Lift) (Γ' Γ₀' : List VExpr) (k' : ℕ),
        Ctx.Lift' l' Γ Γ' ∧ Ctx.Lift' ρ Γ₀ Γ₀' ∧
        Ctx.InstN Γ₀' (e₀.lift' ρ) (A₀.lift' ρ) k' Γ₂ Γ' ∧
        ∀ (j : ℕ) (C : VExpr),
          (C.inst e₀ (k+j)).lift' (Lift.consN l' j)
            = (C.lift' (Lift.consN l j)).inst (e₀.lift' ρ) (k'+j) := by
  intro l
  induction l with
  | refl =>
    intro Γ₁ Γ₂ WL Γ₀ e₀ A₀ k Γ WI
    cases WL
    refine ⟨.refl, .refl, Γ, Γ₀, k, .refl, .refl, ?_, fun j C => ?_⟩
    · simp only [VExpr.lift'_refl]; exact WI
    · have hz : ∀ e : VExpr, e.lift' (Lift.consN Lift.refl j) = e := fun e =>
        VExpr.lift'_depth_zero (by simp)
      rw [hz, hz, VExpr.lift'_refl]
  | skip l₀ ih =>
    intro Γ₁ Γ₂ WL Γ₀ e₀ A₀ k Γ WI
    cases WL with
    | @skip _ _ _ X WL =>
      obtain ⟨l₀', ρ, Γ', Γ₀', k'', WL', Wρ, WI', heq⟩ := ih WL WI
      refine ⟨.skip l₀', ρ, _, Γ₀', k''+1, WL'.skip, Wρ, WI'.succ, fun j C => ?_⟩
      have hs : ∀ (m : Lift) (E : VExpr), E.lift' (Lift.consN (Lift.skip m) j)
          = VExpr.liftN 1 (E.lift' (Lift.consN m j)) j := fun m E => by
        rw [Lift.consN_skip_eq, VExpr.lift'_comp]; exact VExpr.lift'_consN_skipN (n := 1) (k := j)
      rw [hs, hs, heq j C,
        VExpr.liftN_instN_lo 1 (C.lift' (Lift.consN l₀ j)) (e₀.lift' ρ) (k''+j) j
          (Nat.le_add_left j k''),
        show 1 + (k''+j) = k''+1+j from by omega]
  | cons l₀ ih =>
    intro Γ₁ Γ₂ WL Γ₀ e₀ A₀ k Γ WI
    cases WL with
    | @cons _ _ _ X WL =>
      cases WI with
      | zero =>
        refine ⟨l₀, l₀, _, _, 0, WL, WL, .zero, fun j C => ?_⟩
        have hc : Lift.consN (Lift.cons l₀) j = Lift.consN l₀ (j+1) := by
          rw [show Lift.cons l₀ = Lift.consN l₀ 1 from rfl, Lift.consN_consN,
            Nat.add_comm]
        simp only [Nat.zero_add, hc]
        exact VExpr.lift'_inst_consN C e₀ l₀ j
      | succ WI =>
        obtain ⟨l₀', ρ, Γ', Γ₀', k'', WL', Wρ, WI', heq⟩ := ih WL WI
        have hX := heq 0 X
        simp only [Nat.add_zero, Lift.consN] at hX
        refine ⟨.cons l₀', ρ, _, Γ₀', k''+1, WL'.cons, Wρ, hX ▸ WI'.succ, fun j C => ?_⟩
        have hc : ∀ m : Lift, Lift.consN (Lift.cons m) j = Lift.consN m (j+1) := fun m => by
          rw [show Lift.cons m = Lift.consN m 1 from rfl, Lift.consN_consN, Nat.add_comm]
        rw [hc, hc]
        simp only [Nat.add_assoc, Nat.add_comm 1 j]
        exact heq (j+1) C

namespace VEnv

variable {env : VEnv} {nv : ℕ}

/-- **The ascent half of `prop_instN`, free.** -/
theorem isPropUp_instN_up (henv : env.Ordered) {Γ₀ : List VExpr} {e₀ A₀ : VExpr} {k : ℕ}
    {Γ₁ Γ : List VExpr} (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ) (h₀ : env.HasType nv Γ₀ e₀ A₀)
    {ls : List ℕ} {B : VExpr} (h : env.IsPropUp nv ls Γ₁ B) :
    env.IsPropUp nv ls Γ (B.inst e₀ k) := by
  obtain ⟨l, Γ₂, u, WL, hu, hB, h0⟩ := h
  obtain ⟨l', ρ, Γ', Γ₀', k', WL', Wρ, WI', heq⟩ := Ctx.InstN.pushLift' l WL W
  refine ⟨l', Γ', u, WL', hu, ?_, h0⟩
  have := hB.instN henv WI' (h₀.weak' henv Wρ)
  have he := heq 0 B
  simp only [Nat.add_zero, Lift.consN] at he
  rw [he]
  exact this

/-- **The ascent half of `proof_instN`, free.** -/
theorem isProofUp_instN_up (henv : env.Ordered) {Γ₀ : List VExpr} {e₀ A₀ : VExpr} {k : ℕ}
    {Γ₁ Γ : List VExpr} (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ) (h₀ : env.HasType nv Γ₀ e₀ A₀)
    {ls : List ℕ} {e : VExpr} (h : env.IsProofUp nv ls Γ₁ e) :
    env.IsProofUp nv ls Γ (e.inst e₀ k) := by
  obtain ⟨l, Γ₂, B, u, WL, hu, he, hB, h0⟩ := h
  obtain ⟨l', ρ, Γ', Γ₀', k', WL', Wρ, WI', heq⟩ := Ctx.InstN.pushLift' l WL W
  have h₀' := h₀.weak' henv Wρ
  refine ⟨l', Γ', B.inst (e₀.lift' ρ) k', u, WL', hu, ?_, hB.instN henv WI' h₀', h0⟩
  have hi := he.instN henv WI' h₀'
  have hq := heq 0 e
  simp only [Nat.add_zero, Lift.consN] at hq
  rw [hq]
  exact hi

end VEnv

/-! ## 5. The residual, and the assembled `Stable` `PropSplit` -/

namespace VEnv

/-- **The residual of `PropSplit.Stable` for the lift-closed predicate.**

`PropDescend` (`SetModel/StableAudit.lean`) has four fields.  Two of them —
`sort_lift`, `proof_lift` — are the ones that file derives *from*
`TypingStrengthening` + `SortDescend`, i.e. from the strengthening hole; for
`IsPropUp` they are theorems (§3).  Of the remaining two, the ascent halves are
theorems as well (§4).  This is everything that is left: the two **descent**
halves of the substitution fields, which are `PropDescend.sort_inst` and
`.proof_inst` transported to the lift-closed predicate.

`StableAudit.lean`'s own note on `sort_inst` says its candidate refutation is
blocked on `IsDefEqU.sort_forallE_inv` (`Theory/Typing/Injectivity.lean`) — not
on strengthening.  So this residual is a *different* open statement, and that is
the whole point of the file. -/
structure InstDescendUp (env : VEnv) (nv : ℕ) : Prop where
  prop_inst : ∀ {Γ₀ : List VExpr} {e₀ A₀ : VExpr} {k : ℕ} {Γ₁ Γ : List VExpr}
      {ls : List ℕ} {B : VExpr},
    Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ → env.HasType nv Γ₀ e₀ A₀ →
    env.IsPropUp nv ls Γ (B.inst e₀ k) → env.IsPropUp nv ls Γ₁ B
  proof_inst : ∀ {Γ₀ : List VExpr} {e₀ A₀ : VExpr} {k : ℕ} {Γ₁ Γ : List VExpr}
      {ls : List ℕ} {e : VExpr},
    Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ → env.HasType nv Γ₀ e₀ A₀ →
    env.IsProofUp nv ls Γ (e.inst e₀ k) → env.IsProofUp nv ls Γ₁ e

end VEnv

namespace SetModel

variable {env : VEnv} {nv : ℕ}

/-- **The lift-closed `PropSplit`.**  Same two inputs as `propSplitOf`:
`PropUniq` and `PropTypeAgree`. -/
noncomputable def propSplitUp (env : VEnv) (nv : ℕ) (henv : env.Ordered)
    (hU : env.PropUniq nv) (hT : env.PropTypeAgree nv) : PropSplit env nv where
  IsPropAt := env.IsPropUp nv
  IsProofAt := env.IsProofUp nv
  decProp _ _ _ := Classical.propDecidable _
  decProof _ _ _ := Classical.propDecidable _
  prop_sound _ hw ht := VEnv.isPropUp_iff henv hU hw ht
  proof_sound _ hw he hA := VEnv.isProofUp_iff henv hT hw he hA

/-- **The headline.**  `Stable` for `propSplitUp`, from `Ordered` and the
substitution residual alone.

Compare `StableAudit.propSplitOf_stable`, whose hypothesis `PropDescend` has two
further fields that `sort_lift_of_strengthening` / `proof_lift_of_strengthening`
obtain from `TypingStrengthening` + `SortDescend`.  Neither of those statements —
nor any other open statement of `Theory/Typing/Strengthen.lean` — occurs in the
hypotheses below. -/
theorem propSplitUp_stable (henv : env.Ordered) (hU : env.PropUniq nv)
    (hT : env.PropTypeAgree nv) (hI : env.InstDescendUp nv) :
    (propSplitUp env nv henv hU hT).Stable where
  prop_liftN W _ _ := VEnv.isPropUp_liftN henv W
  proof_liftN W _ _ := VEnv.isProofUp_liftN henv W
  prop_instN W h₀ _ _ := ⟨hI.prop_inst W h₀, VEnv.isPropUp_instN_up henv W h₀⟩
  proof_instN W h₀ _ _ := ⟨hI.proof_inst W h₀, VEnv.isProofUp_instN_up henv W h₀⟩

/-- The existence form, to be compared with
`StableAudit.exists_stable_propSplit`: the `PropDescend` there is replaced by
`InstDescendUp`, which has no `lift` fields. -/
theorem exists_stable_propSplitUp (henv : env.Ordered) (hU : env.PropUniq nv)
    (hT : env.PropTypeAgree nv) (hI : env.InstDescendUp nv) :
    ∃ L : PropSplit env nv, L.Stable :=
  ⟨_, propSplitUp_stable henv hU hT hI⟩

/-- **The exact counterpart of `StableAudit.exists_stable_propSplit`**, with the
goal's own `hfalse` supplying `PropUniq` as there.  Side by side, the two
statements differ in exactly one hypothesis: `PropDescend` (four fields, two of
them strengthening) versus `InstDescendUp` (two fields, neither of them). -/
theorem exists_stable_propSplitUp_of_agree {env : VEnv} (nv : ℕ) (henv : env.Ordered)
    (hf : ∃ e, env.HasType 0 [] e falseProp) (hT : env.PropTypeAgree 0)
    (hI : env.InstDescendUp nv) : ∃ L : PropSplit env nv, L.Stable :=
  ⟨_, propSplitUp_stable henv
    (VEnv.PropUniq.of_zero (VEnv.PropUniq.of_propTypeAgree henv hf hT) nv)
    (VEnv.PropTypeAgree.of_zero hT nv) hI⟩

/-! ## 6. Audit: what the weakening changed, and what it did not -/

/-- **`propSplitOf` refines `propSplitUp`, always.**  The empty lift. -/
theorem isPropAt_le_isPropUp {hU : env.PropUniq nv} {hT : env.PropTypeAgree nv}
    {ls Γ A} (h : (propSplitOf env nv hU hT).IsPropAt ls Γ A) : env.IsPropUp nv ls Γ A :=
  let ⟨_, hw, ht, h0⟩ := h; .of_hasType hw ht h0

/-- **…and on well-typed input the two agree.**

So the weakening changes the predicate only where the type has no sort at `Γ` —
which is precisely the region `PropSplit.Stable` quantifies over and
`prop_sound` does not.  That asymmetry (raw syntax in `Stable`, a typing premise
in `prop_sound`) is the whole source of the freedom. -/
theorem isPropUp_iff_isPropAt (henv : env.Ordered) (hU : env.PropUniq nv)
    {hT : env.PropTypeAgree nv} {ls Γ A u} (hw : u.WF nv)
    (ht : env.HasType nv Γ A (.sort u)) :
    env.IsPropUp nv ls Γ A ↔ (propSplitOf env nv hU hT).IsPropAt ls Γ A :=
  (VEnv.isPropUp_iff henv hU hw ht).trans (propSplitOf_isPropAt_iff hw ht).symm

/-- The same for terms. -/
theorem isProofUp_iff_isProofAt (henv : env.Ordered) {hU : env.PropUniq nv}
    (hT : env.PropTypeAgree nv) {ls Γ e A u} (hw : u.WF nv)
    (he : env.HasType nv Γ e A) (hA : env.HasType nv Γ A (.sort u)) :
    env.IsProofUp nv ls Γ e ↔ (propSplitOf env nv hU hT).IsProofAt ls Γ e :=
  (VEnv.isProofUp_iff henv hT hw he hA).trans (propSplitOf_isProofAt_iff hw he hA).symm

/-- **The negative control.**  Collapsing `IsPropUp` back to the canonical
predicate at *arbitrary* input is not a harmless simplification: it is exactly
`PropDescend.sort_lift`, the field `StableAudit.sort_lift_of_strengthening`
obtains from the strengthening hole.

So §3 is not the trivial direction read backwards, and `propSplitUp` is a
genuinely different `PropSplit` from `propSplitOf`. -/
theorem sort_lift_of_isPropUp_collapse
    (h : ∀ (ls : List ℕ) (Γ : List VExpr) (A : VExpr), env.IsPropUp nv ls Γ A →
      ∃ u : VLevel, u.WF nv ∧ env.HasType nv Γ A (.sort u) ∧ u.eval ls = 0)
    {n k : ℕ} {Γ Γ' : List VExpr} {A : VExpr} {u : VLevel} {ls : List ℕ}
    (W : Ctx.LiftN n k Γ Γ') (hu : u.WF nv)
    (hA : env.HasType nv Γ' (A.liftN n k) (.sort u)) (h0 : u.eval ls = 0) :
    ∃ v : VLevel, v.WF nv ∧ env.HasType nv Γ A (.sort v) ∧ v.eval ls = 0 :=
  h ls Γ A ⟨_, Γ', u, Ctx.liftN_iff_lift'.1 W, hu, by
    rwa [VExpr.lift'_consN_skipN], h0⟩

/-- `∀ p : Prop, p` is a proposition in every context, in every environment. -/
theorem allProp_hasType {Γ : List VExpr} :
    env.HasType nv Γ (.forallE (.sort .zero) (.bvar 0)) (.sort .zero) := by
  refine VEnv.IsDefEq.defeqDF (u := .succ (.imax (.succ .zero) .zero))
    (.sortDF ⟨trivial, trivial⟩ trivial ?_) (VEnv.IsDefEq.forallEDF
      (u := .succ .zero) (v := .zero) (.sortDF trivial trivial rfl) (.bvar .zero))
  funext ls; simp [VLevel.eval, Lean.Nat.imax]

/-- **Non-vacuity, positive branch.**  `∀ p : Prop, p` is a proposition
everywhere, with no hypothesis at all. -/
theorem isPropUp_falseProp (ls : List ℕ) (Γ : List VExpr) :
    env.IsPropUp nv ls Γ falseProp :=
  .of_hasType (u := .zero) trivial allProp_hasType rfl

/-- **Non-vacuity, negative branch.**  `Prop` itself is not a proposition —
including in any context above `[]`.  Together with the previous theorem this
rules out the two constant predicates, the check `PropSplitAudit.lean` runs on
`propSplitOf`. -/
theorem not_isPropUp_sort (henv : env.Ordered) (hU : env.PropUniq nv) (ls : List ℕ) :
    ¬ env.IsPropUp nv ls [] (.sort .zero) := by
  have h : env.HasType nv [] (.sort .zero) (.sort (.succ .zero)) :=
    VEnv.IsDefEq.sortDF trivial trivial rfl
  rw [VEnv.isPropUp_iff henv hU (u := .succ .zero) trivial h]
  simp [VLevel.eval]

end SetModel


/-! ## 7. Exactly what the closure bought

The two theorems of §3 are free.  The price is that `IsPropUp` is a *weaker*
predicate than `propSplitOf`'s, and §5 already showed the two agree on well-typed
input.  This section pins the difference down to the nose: collapsing `IsPropUp`
back to the canonical predicate is **equivalent** to `PropDescend.sort_lift`,
which is the field `StableAudit.sort_lift_of_strengthening` obtains from
`TypingStrengthening` + `SortDescend`.

So the trade is exact: `propSplitOf` pays `sort_lift`/`proof_lift` inside
`Stable`; `propSplitUp` pays them nowhere, and the same two statements reappear
as the (unneeded) claim that its predicate is the canonical one. -/

namespace VEnv

variable {env : VEnv} {nv : ℕ}

/-- `PropDescend.sort_lift`, standalone. -/
def SortLiftDescend (env : VEnv) (nv : ℕ) : Prop :=
  ∀ {n k : ℕ} {Γ Γ' : List VExpr} {A : VExpr} {u : VLevel} {ls : List ℕ},
    Ctx.LiftN n k Γ Γ' → u.WF nv → env.HasType nv Γ' (A.liftN n k) (.sort u) →
    u.eval ls = 0 → ∃ v : VLevel, v.WF nv ∧ env.HasType nv Γ A (.sort v) ∧ v.eval ls = 0

/-- `PropDescend.proof_lift`, standalone. -/
def ProofLiftDescend (env : VEnv) (nv : ℕ) : Prop :=
  ∀ {n k : ℕ} {Γ Γ' : List VExpr} {e A : VExpr} {u : VLevel} {ls : List ℕ},
    Ctx.LiftN n k Γ Γ' → u.WF nv → env.HasType nv Γ' (e.liftN n k) A →
    env.HasType nv Γ' A (.sort u) → u.eval ls = 0 →
    ∃ (B : VExpr) (v : VLevel), v.WF nv ∧ env.HasType nv Γ e B ∧
      env.HasType nv Γ B (.sort v) ∧ v.eval ls = 0

theorem PropDescend.sortLiftDescend (hD : env.PropDescend nv) : env.SortLiftDescend nv :=
  fun W hu hA h0 => hD.sort_lift W hu hA h0

theorem PropDescend.proofLiftDescend (hD : env.PropDescend nv) : env.ProofLiftDescend nv :=
  fun W hu he hA h0 => hD.proof_lift W hu he hA h0

/-- `IsPropUp` is the canonical predicate. -/
def PropUpCollapse (env : VEnv) (nv : ℕ) : Prop :=
  ∀ (ls : List ℕ) (Γ : List VExpr) (A : VExpr), env.IsPropUp nv ls Γ A →
    ∃ u : VLevel, u.WF nv ∧ env.HasType nv Γ A (.sort u) ∧ u.eval ls = 0

/-- `IsProofUp` is the canonical predicate. -/
def ProofUpCollapse (env : VEnv) (nv : ℕ) : Prop :=
  ∀ (ls : List ℕ) (Γ : List VExpr) (e : VExpr), env.IsProofUp nv ls Γ e →
    ∃ (A : VExpr) (u : VLevel), u.WF nv ∧ env.HasType nv Γ e A ∧
      env.HasType nv Γ A (.sort u) ∧ u.eval ls = 0

private theorem propUpCollapse_aux (hSL : env.SortLiftDescend nv) :
    ∀ (d : ℕ) {l : Lift} {Γ Γ' : List VExpr} {ls : List ℕ} {A : VExpr} {u : VLevel},
      l.depth = d → Ctx.Lift' l Γ Γ' → u.WF nv → env.HasType nv Γ' (A.lift' l) (.sort u) →
      u.eval ls = 0 → ∃ v : VLevel, v.WF nv ∧ env.HasType nv Γ A (.sort v) ∧ v.eval ls = 0
  | 0, l, Γ, Γ', ls, A, u, hd, W, hu, hA, h0 => by
    cases Ctx.Lift'.depth_zero hd W
    rw [VExpr.lift'_depth_zero hd] at hA
    exact ⟨u, hu, hA, h0⟩
  | d+1, l, Γ, Γ', ls, A, u, hd, W, hu, hA, h0 => by
    obtain ⟨l', k, hd', rfl⟩ := Lift.depth_succ hd
    obtain ⟨Γ₁, W1, W2⟩ := W.of_cons_skip
    rw [Lift.consN_skip_eq, VExpr.lift'_comp, ← Lift.skipN_one,
      VExpr.lift'_consN_skipN] at hA
    obtain ⟨v, hv, hAv, h0'⟩ := hSL W2 hu hA h0
    exact propUpCollapse_aux hSL d (by simp [hd']) W1 hv hAv h0'

private theorem proofUpCollapse_aux (hPL : env.ProofLiftDescend nv) :
    ∀ (d : ℕ) {l : Lift} {Γ Γ' : List VExpr} {ls : List ℕ} {e B : VExpr} {u : VLevel},
      l.depth = d → Ctx.Lift' l Γ Γ' → u.WF nv → env.HasType nv Γ' (e.lift' l) B →
      env.HasType nv Γ' B (.sort u) → u.eval ls = 0 →
      ∃ (C : VExpr) (v : VLevel), v.WF nv ∧ env.HasType nv Γ e C ∧
        env.HasType nv Γ C (.sort v) ∧ v.eval ls = 0
  | 0, l, Γ, Γ', ls, e, B, u, hd, W, hu, he, hB, h0 => by
    cases Ctx.Lift'.depth_zero hd W
    rw [VExpr.lift'_depth_zero hd] at he
    exact ⟨B, u, hu, he, hB, h0⟩
  | d+1, l, Γ, Γ', ls, e, B, u, hd, W, hu, he, hB, h0 => by
    obtain ⟨l', k, hd', rfl⟩ := Lift.depth_succ hd
    obtain ⟨Γ₁, W1, W2⟩ := W.of_cons_skip
    rw [Lift.consN_skip_eq, VExpr.lift'_comp, ← Lift.skipN_one,
      VExpr.lift'_consN_skipN] at he
    obtain ⟨C, v, hv, heC, hC, h0'⟩ := hPL W2 hu he hB h0
    exact proofUpCollapse_aux hPL d (by simp [hd']) W1 hv heC hC h0'

/-- **`sort_lift` gives the collapse.** -/
theorem propUpCollapse_of_sortLiftDescend (hSL : env.SortLiftDescend nv) :
    env.PropUpCollapse nv := fun _ _ _ ⟨_, _, _, W, hu, hA, h0⟩ =>
  propUpCollapse_aux hSL _ rfl W hu hA h0

/-- **`proof_lift` gives the collapse.** -/
theorem proofUpCollapse_of_proofLiftDescend (hPL : env.ProofLiftDescend nv) :
    env.ProofUpCollapse nv := fun _ _ _ ⟨_, _, _, _, W, hu, he, hB, h0⟩ =>
  proofUpCollapse_aux hPL _ rfl W hu he hB h0

/-- **…and the collapse gives `sort_lift` back.** -/
theorem sortLiftDescend_of_propUpCollapse (h : env.PropUpCollapse nv) :
    env.SortLiftDescend nv := fun {_ _ _ Γ' A _ ls} W hu hA h0 =>
  h ls _ A ⟨_, Γ', _, Ctx.liftN_iff_lift'.1 W, hu, by rwa [VExpr.lift'_consN_skipN], h0⟩

/-- **…and the collapse gives `proof_lift` back.** -/
theorem proofLiftDescend_of_proofUpCollapse (h : env.ProofUpCollapse nv) :
    env.ProofLiftDescend nv := fun {_ _ _ Γ' e B _ ls} W hu he hB h0 =>
  h ls _ e ⟨_, Γ', B, _, Ctx.liftN_iff_lift'.1 W, hu, by rwa [VExpr.lift'_consN_skipN], hB, h0⟩

/-- **The exact price of §3**, as an equivalence.  `propSplitUp`'s predicate is
`propSplitOf`'s **iff** the strengthening-derived field `PropDescend.sort_lift`
holds. -/
theorem propUpCollapse_iff : env.PropUpCollapse nv ↔ env.SortLiftDescend nv :=
  ⟨sortLiftDescend_of_propUpCollapse, propUpCollapse_of_sortLiftDescend⟩

/-- The same for terms. -/
theorem proofUpCollapse_iff : env.ProofUpCollapse nv ↔ env.ProofLiftDescend nv :=
  ⟨proofLiftDescend_of_proofUpCollapse, proofUpCollapse_of_proofLiftDescend⟩

end VEnv


/-! ## 8. No regression: the old hypothesis still discharges the new one -/

namespace VEnv

variable {env : VEnv} {nv : ℕ}

/-- **`PropDescend` implies `InstDescendUp`.**

So `propSplitUp` is `Stable` wherever `propSplitOf` is, and the two `lift`
fields of `PropDescend` are simply not used for the new predicate — that is what
§3 removed.  (Audit against consumers: nothing that could stabilise the old
`PropSplit` fails to stabilise the new one.) -/
theorem instDescendUp_of_propDescend (hD : env.PropDescend nv) :
    env.InstDescendUp nv where
  prop_inst {_ _ _ _ _ _ ls _} W h₀ h := by
    obtain ⟨u, hu, hB, h0⟩ := propUpCollapse_of_sortLiftDescend hD.sortLiftDescend ls _ _ h
    obtain ⟨v, hv, hB', h0'⟩ := hD.sort_inst W h₀ hu hB h0
    exact .of_hasType hv hB' h0'
  proof_inst {_ _ _ _ _ _ ls _} W h₀ h := by
    obtain ⟨A, u, hu, he, hA, h0⟩ :=
      proofUpCollapse_of_proofLiftDescend hD.proofLiftDescend ls _ _ h
    obtain ⟨B, v, hv, he', hB, h0'⟩ := hD.proof_inst W h₀ hu he hA h0
    exact .of_hasType hv he' hB h0'

end VEnv



end Lean4Lean
