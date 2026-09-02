import Lean4Lean.Theory.SetModel.InstDescendBvar
import Lean4Lean.Theory.SetModel.PropSplitUp

/-!
# `PropSplit.Stable` with the `OnCtx` guard: what the guard buys, and where it cannot be paid

This file executes ruling 140 (`docs/vacuity-ledger.md` row 140) as far as it goes, and measures
the two places the ruling's costing is wrong.

## The result

1. **`Ctx.Lift'.pushOut_onCtx`** — the pushout of two lifts out of a common context carries the
   `OnCtx` guard whenever *both* legs' targets do.  `PropSplitUp.lean` §1 already had the
   syntactic pushout; this adds the semantic half, and it is **new mathematics**, contra the
   ruling's "flag day with no new mathematics".  It is what `handoff-setmodel.md` §13.5 item 3
   abandoned — and it was abandoned for a reason that does not apply here (there the ascent's
   target context `Γ₁` was *unguarded*; guarding it is exactly what this file assumes).
2. **`isPropUpOn_lift'` / `isProofUpOn_lift'` and their `liftN` forms** — the two `lift` fields of
   `PropSplit.Stable` for the **guarded** lift-closed predicate `IsPropUpOn`, in **both**
   directions, with **no hole of any kind**.  Descent is free (`IsPropUpOn.of_lift'`); ascent is
   §1's guarded pushout.
3. **`propUpOnLiftAscend_at`** — `VEnv.PropUpOnLiftAscend`, the single obligation
   `InstDescendBvar` §7 named as the price of the guarded framing, is **a theorem at a guarded
   target**.  `isPropUpOn_liftN_up` proved it only for a *canonically witnessed* source; §2 proves
   it for an arbitrary one, which is what `Stable`'s field actually quantifies over.
   **The unguarded name `PropUpOnLiftAscend` itself is NOT discharged**, and deliberately so:
   deriving it would need "every lift target is `OnCtx`", which `notOnCtx_lift_target` refutes.
   Saying otherwise would be ledger blindness 4 with extra steps.
4. **`PropSplit.StableOn`** — `Stable`'s four fields with the guard, `Stable.stableOn` showing it
   is the weaker demand, and `propSplitUpOn`'s two `lift` fields of it discharged outright.
5. **§6: `prop_inst_bvar_on` / `proof_inst_bvar_on`** — `InstDescendUp`'s `.bvar k` case with
   **both** sides guarded, which `handoff-setmodel.md` §13.5 item 4 wrote off for want of
   `OnCtx Γ₁`.  `StableOn.prop_instN` supplies exactly that hypothesis, so the case goes through.
6. **§7: `OnCtx.instN`, `isPropUpOn_instN_up` / `isProofUpOn_instN_up`** — the **ascent** halves of
   both `inst` fields, at *every* `B`, for the guarded predicate.  `PropSplitUp` §4 had them for
   the unguarded one; the only missing ingredient was that `OnCtx` survives instantiation.  With
   §6 this closes **all four** `StableOn` fields at `B = .bvar k` for `propSplitUpOn`
   (`isPropUpOn_instN_bvar`, `isProofUpOn_instN_bvar`), leaving only the `inst` **descent** at
   general `B` — i.e. `InstDescendUp`, unchanged as the corner's residual.

## What the ruling gets wrong, measured

* "**No new mathematics**": item 1 is new mathematics.  40 lines, five cases, and the `.cons/.cons`
  case needs the pushout square to commute before the guard entry can be weakened into place.
* "**A flag day**": the guard **cannot be threaded into `Stable` in place**, because `Stable`'s two
  load-bearing consumers — `InterpSubst.interp_liftN` and `interp_inst` — are recursions over *raw
  syntax* whose only hypothesis about the term is `ClosedN`.  At the `.lam A b` and `.forallE A B`
  cases they apply the field at `Ctx.LiftN n (k+1) (A :: Γ) (A.liftN n k :: Γ')`, and the guard
  there is `OnCtx (A.liftN n k :: Γ') = OnCtx Γ' ∧ env.IsType nv Γ' (A.liftN n k)`.  **The second
  conjunct is not available and cannot be derived**: nothing in those recursions types `A`.
  `SetModel/StableAudit.lean`'s note (§"Connecting the two `lift` fields…") says this in prose;
  §4 below makes it a Lean **theorem** (`InterpLiftNObligation`, `not_interpLiftNObligation`):
  the obligation is not merely unproved, it is **false**.
  So the funded route stops one layer short of `Stable` itself, and what it does close is
  `PropUpOnLiftAscend` — which was the point.
-/

namespace Lean4Lean

open SetModel

/-! ## 1. The pushout of two lifts carries the `OnCtx` guard -/

/-- **`Ctx.Lift'.pushOut`, with the guard.**  If both legs' targets are well-formed contexts, so
is the join.

The proof is `PropSplitUp.Ctx.Lift'.pushOut`'s induction with one extra obligation per
`skip`/`cons` case: the entry that the join gains is an entry of one of the two legs, lifted
along the *other* leg's push-out, so `IsType.weak'` puts it in place.  In the `.cons`/`.cons`
case the entry is already a lift (`X.lift' l₁`) and the guard on `Γ₁` supplies it directly. -/
theorem Ctx.Lift'.pushOut_onCtx {env : VEnv} {nv : ℕ} (henv : env.Ordered) :
    ∀ (l₁ l₂ : Lift) {Γ Γ₁ Γ₂ : List VExpr},
      Ctx.Lift' l₁ Γ Γ₁ → Ctx.Lift' l₂ Γ Γ₂ →
      OnCtx Γ₁ (env.IsType nv) → OnCtx Γ₂ (env.IsType nv) →
      ∃ Γ₃, Ctx.Lift' (Lift.pushOutL l₁ l₂) Γ₁ Γ₃ ∧ Ctx.Lift' (Lift.pushOutR l₁ l₂) Γ₂ Γ₃ ∧
        OnCtx Γ₃ (env.IsType nv) := by
  intro l₁
  induction l₁ with
  | refl =>
    intro l₂ Γ Γ₁ Γ₂ H1 H2 h1 h2
    cases H1
    rw [Lift.pushOutL, Lift.pushOutR]
    exact ⟨Γ₂, H2, .refl, h2⟩
  | skip l₁ ih =>
    intro l₂ Γ Γ₁ Γ₂ H1 H2 h1 h2
    cases H1 with
    | skip H1 =>
      obtain ⟨Γ₃, a, b, h3⟩ := ih l₂ H1 H2 h1.1 h2
      rw [Lift.pushOutL, Lift.pushOutR]
      exact ⟨_, a.cons, b.skip, h3, h1.2.weak' henv a⟩
  | cons l₁ ih =>
    intro l₂
    induction l₂ with
    | refl =>
      intro Γ Γ₁ Γ₂ H1 H2 h1 h2
      cases H2
      rw [Lift.pushOutL, Lift.pushOutR]
      exact ⟨Γ₁, .refl, H1, h1⟩
    | skip l₂ ih2 =>
      intro Γ Γ₁ Γ₂ H1 H2 h1 h2
      cases H2 with
      | skip H2 =>
        obtain ⟨Γ₃, a, b, h3⟩ := ih2 H1 H2 h1 h2.1
        rw [Lift.pushOutL, Lift.pushOutR]
        exact ⟨_, a.skip, b.cons, h3, h2.2.weak' henv b⟩
    | cons l₂ _ =>
      intro Γ Γ₁ Γ₂ H1 H2 h1 h2
      cases H1 with
      | cons H1 =>
        cases H2 with
        | cons H2 =>
          obtain ⟨Γ₃, a, b, h3⟩ := ih l₂ H1 H2 h1.1 h2.1
          have heq : ∀ X : VExpr, (X.lift' l₂).lift' (Lift.pushOutR l₁ l₂)
              = (X.lift' l₁).lift' (Lift.pushOutL l₁ l₂) := fun X => by
            rw [← VExpr.lift'_comp, ← VExpr.lift'_comp, Lift.pushOut_comp]
          rw [Lift.pushOutL, Lift.pushOutR]
          exact ⟨_, a.cons, heq _ ▸ b.cons, h3, h1.2.weak' henv a⟩

/-! ## 2. The two `lift` fields, for the **guarded** lift-closed predicate, free

`PropSplitUp.lean` §3 proves these for the unguarded `IsPropUp`.  The guard survives the descent
for nothing (`IsPropUpOn.of_lift'` keeps the witness context), and survives the **ascent** by §1 —
which is the whole point of §1, and the step `handoff-setmodel.md` §13.5 item 3 wrote off. -/

namespace VEnv

variable {env : VEnv} {nv : ℕ}

/-- **Lift stability of `IsPropUpOn`, for a general lift**, given the guard on the lift's target.

Compare `PropSplitUp.isPropUp_lift'`, which needs no guard but delivers only the unguarded
predicate, and `isPropUpOn_liftN_up`, which delivers the guarded one only from a *canonically*
witnessed source.  This is the field `PropSplit.Stable.prop_liftN` asks for, at
`L := propSplitUpOn`. -/
theorem isPropUpOn_lift' (henv : env.Ordered) {ρ : Lift} {Γ Γ' : List VExpr}
    (W : Ctx.Lift' ρ Γ Γ') (hΓ' : OnCtx Γ' (env.IsType nv)) {ls : List ℕ} {A : VExpr} :
    env.IsPropUpOn nv ls Γ' (A.lift' ρ) ↔ env.IsPropUpOn nv ls Γ A := by
  refine ⟨IsPropUpOn.of_lift' W, ?_⟩
  rintro ⟨l, Γ'', u, W', hΓ'', hu, hA, h0⟩
  obtain ⟨Γ₃, a, b, h3⟩ := Ctx.Lift'.pushOut_onCtx henv ρ l W W' hΓ' hΓ''
  refine ⟨Lift.pushOutL ρ l, Γ₃, u, a, h3, hu, ?_, h0⟩
  have h := hA.weak' henv b
  simp only [VExpr.lift'] at h
  rwa [← VExpr.lift'_comp, ← Lift.pushOut_comp, VExpr.lift'_comp] at h

/-- **Lift stability of `IsProofUpOn`, for a general lift**, given the guard on the target. -/
theorem isProofUpOn_lift' (henv : env.Ordered) {ρ : Lift} {Γ Γ' : List VExpr}
    (W : Ctx.Lift' ρ Γ Γ') (hΓ' : OnCtx Γ' (env.IsType nv)) {ls : List ℕ} {e : VExpr} :
    env.IsProofUpOn nv ls Γ' (e.lift' ρ) ↔ env.IsProofUpOn nv ls Γ e := by
  refine ⟨IsProofUpOn.of_lift' W, ?_⟩
  rintro ⟨l, Γ'', B, u, W', hΓ'', hu, he, hB, h0⟩
  obtain ⟨Γ₃, a, b, h3⟩ := Ctx.Lift'.pushOut_onCtx henv ρ l W W' hΓ' hΓ''
  refine ⟨Lift.pushOutL ρ l, Γ₃, B.lift' (Lift.pushOutR ρ l), u, a, h3, hu, ?_, ?_, h0⟩
  · have h := he.weak' henv b
    rwa [← VExpr.lift'_comp, ← Lift.pushOut_comp, VExpr.lift'_comp] at h
  · have h := hB.weak' henv b
    simpa only [VExpr.lift'] using h

/-- **`PropSplit.Stable.prop_liftN` for the guarded lift-closed predicate.** -/
theorem isPropUpOn_liftN (henv : env.Ordered) {n k : ℕ} {Γ Γ' : List VExpr}
    (W : Ctx.LiftN n k Γ Γ') (hΓ' : OnCtx Γ' (env.IsType nv)) {ls : List ℕ} {A : VExpr} :
    env.IsPropUpOn nv ls Γ' (A.liftN n k) ↔ env.IsPropUpOn nv ls Γ A := by
  rw [← VExpr.lift'_consN_skipN]
  exact isPropUpOn_lift' henv (Ctx.liftN_iff_lift'.1 W) hΓ'

/-- **`PropSplit.Stable.proof_liftN` for the guarded lift-closed predicate.** -/
theorem isProofUpOn_liftN (henv : env.Ordered) {n k : ℕ} {Γ Γ' : List VExpr}
    (W : Ctx.LiftN n k Γ Γ') (hΓ' : OnCtx Γ' (env.IsType nv)) {ls : List ℕ} {e : VExpr} :
    env.IsProofUpOn nv ls Γ' (e.liftN n k) ↔ env.IsProofUpOn nv ls Γ e := by
  rw [← VExpr.lift'_consN_skipN]
  exact isProofUpOn_lift' henv (Ctx.liftN_iff_lift'.1 W) hΓ'

/-- **`PropUpOnLiftAscend`, with the guard — and this is the honest form.**

`VEnv.PropUpOnLiftAscend` (`InstDescendBvar` §7) is stated **without** a guard on `Γ'`, and it is
*not* discharged here: guarding it is precisely the trade ruling 140 makes.  Discharging the
unguarded name from "every lift target is `OnCtx`" would be blindness 4 in a new costume — that
hypothesis is refuted by `PropAgreeWall.not_onCtx_junk` at `Ctx.LiftN.one (A := .bvar 0)`
(`stableOn_narrowing_is_real` below), so such a lemma would be vacuous.  What is a theorem is
this: the ascent, at a guarded target. -/
theorem propUpOnLiftAscend_at (henv : env.Ordered) {n k : ℕ} {Γ Γ' : List VExpr}
    (W : Ctx.LiftN n k Γ Γ') (hΓ' : OnCtx Γ' (env.IsType nv)) {ls : List ℕ} {A : VExpr}
    (h : env.IsPropUpOn nv ls Γ A) : env.IsPropUpOn nv ls Γ' (A.liftN n k) :=
  (isPropUpOn_liftN henv W hΓ').2 h

end VEnv

/-! ## 3. `PropSplit.StableOn` — `Stable`'s four fields with the guard -/

namespace SetModel

variable {env : VEnv} {nv : ℕ}

/-- **`PropSplit.Stable` with the `OnCtx` guard on both contexts of every field.**

Ruling 140's target.  The guard shape is the one `StableAudit.sort_lift_of_strengthening` and
`proof_lift_of_strengthening` already have, so `StableOn`'s `lift` fields are directly comparable
with the strengthening stream's `TypingStrengthening ∧ SortDescend`.

**Which guard each field actually uses**, measured rather than asserted: §3's two `lift` theorems
for `propSplitUpOn` use only `hΓ'` (the *larger* context).  `hΓ` is carried because the
strengthening statements have it and because a consumer that can supply one can supply the other;
it is not used below.  The two `inst` fields are **not** discharged for any `PropSplit` — they are
`InstDescendUp`, of which only the `.bvar k` case is closed (`InstDescendBvar` §4). -/
structure PropSplit.StableOn (L : PropSplit env nv) : Prop where
  prop_liftN : ∀ {n k : ℕ} {Γ Γ' : List VExpr}, Ctx.LiftN n k Γ Γ' →
    OnCtx Γ (env.IsType nv) → OnCtx Γ' (env.IsType nv) →
    ∀ (ls : List ℕ) (A : VExpr), (L.IsPropAt ls Γ' (A.liftN n k) ↔ L.IsPropAt ls Γ A)
  proof_liftN : ∀ {n k : ℕ} {Γ Γ' : List VExpr}, Ctx.LiftN n k Γ Γ' →
    OnCtx Γ (env.IsType nv) → OnCtx Γ' (env.IsType nv) →
    ∀ (ls : List ℕ) (e : VExpr), (L.IsProofAt ls Γ' (e.liftN n k) ↔ L.IsProofAt ls Γ e)
  prop_instN : ∀ {Γ₀ : List VExpr} {e₀ A₀ : VExpr} {k : ℕ} {Γ₁ Γ : List VExpr},
    Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ → env.HasType nv Γ₀ e₀ A₀ →
    OnCtx Γ₁ (env.IsType nv) → OnCtx Γ (env.IsType nv) →
    ∀ (ls : List ℕ) (B : VExpr), (L.IsPropAt ls Γ (B.inst e₀ k) ↔ L.IsPropAt ls Γ₁ B)
  proof_instN : ∀ {Γ₀ : List VExpr} {e₀ A₀ : VExpr} {k : ℕ} {Γ₁ Γ : List VExpr},
    Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ → env.HasType nv Γ₀ e₀ A₀ →
    OnCtx Γ₁ (env.IsType nv) → OnCtx Γ (env.IsType nv) →
    ∀ (ls : List ℕ) (e : VExpr), (L.IsProofAt ls Γ (e.inst e₀ k) ↔ L.IsProofAt ls Γ₁ e)

/-- **`StableOn` is the weaker demand**, so guarding is a genuine narrowing of the quantifier and
everything that has `Stable` still has `StableOn`.  (The converse fails — see
`stableOn_narrowing_is_real`.) -/
theorem PropSplit.Stable.stableOn {L : PropSplit env nv} (hS : L.Stable) : L.StableOn where
  prop_liftN W _ _ := hS.prop_liftN W
  proof_liftN W _ _ := hS.proof_liftN W
  prop_instN W h₀ _ _ := hS.prop_instN W h₀
  proof_instN W h₀ _ _ := hS.proof_instN W h₀

/-- **The two `lift` fields of `StableOn` for the guarded lift-closed split, discharged.**

No hole, no hypothesis beyond `Ordered` and the guard the field carries.  This is what ruling 140
predicted, and it is the only part of the ruling that lands: §2's guarded pushout does the work. -/
theorem propSplitUpOn_stableOn_prop_liftN (henv : env.Ordered)
    (hU : env.PropUniqOnCtx nv) (hT : env.PropTypeAgreeOnCtx nv)
    {n k : ℕ} {Γ Γ' : List VExpr} (W : Ctx.LiftN n k Γ Γ')
    (hΓ' : OnCtx Γ' (env.IsType nv)) (ls : List ℕ) (A : VExpr) :
    (propSplitUpOn env nv henv hU hT).IsPropAt ls Γ' (A.liftN n k) ↔
      (propSplitUpOn env nv henv hU hT).IsPropAt ls Γ A :=
  VEnv.isPropUpOn_liftN henv W hΓ'

theorem propSplitUpOn_stableOn_proof_liftN (henv : env.Ordered)
    (hU : env.PropUniqOnCtx nv) (hT : env.PropTypeAgreeOnCtx nv)
    {n k : ℕ} {Γ Γ' : List VExpr} (W : Ctx.LiftN n k Γ Γ')
    (hΓ' : OnCtx Γ' (env.IsType nv)) (ls : List ℕ) (e : VExpr) :
    (propSplitUpOn env nv henv hU hT).IsProofAt ls Γ' (e.liftN n k) ↔
      (propSplitUpOn env nv henv hU hT).IsProofAt ls Γ e :=
  VEnv.isProofUpOn_liftN henv W hΓ'

/-- **`StableOn` for the guarded split, modulo exactly the two `inst` fields.**

Stated as an implication from the two `inst` fields so that the residual is *visible* rather than
carried silently: whoever supplies `InstDescendUp`'s two fields at the guarded predicate gets
`StableOn` for free.  `InstDescendBvar` §4 supplies the `.bvar k` case of both. -/
theorem propSplitUpOn_stableOn (henv : env.Ordered)
    (hU : env.PropUniqOnCtx nv) (hT : env.PropTypeAgreeOnCtx nv)
    (hpi : ∀ {Γ₀ : List VExpr} {e₀ A₀ : VExpr} {k : ℕ} {Γ₁ Γ : List VExpr},
      Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ → env.HasType nv Γ₀ e₀ A₀ →
      OnCtx Γ₁ (env.IsType nv) → OnCtx Γ (env.IsType nv) →
      ∀ (ls : List ℕ) (B : VExpr),
        (env.IsPropUpOn nv ls Γ (B.inst e₀ k) ↔ env.IsPropUpOn nv ls Γ₁ B))
    (hei : ∀ {Γ₀ : List VExpr} {e₀ A₀ : VExpr} {k : ℕ} {Γ₁ Γ : List VExpr},
      Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ → env.HasType nv Γ₀ e₀ A₀ →
      OnCtx Γ₁ (env.IsType nv) → OnCtx Γ (env.IsType nv) →
      ∀ (ls : List ℕ) (e : VExpr),
        (env.IsProofUpOn nv ls Γ (e.inst e₀ k) ↔ env.IsProofUpOn nv ls Γ₁ e)) :
    (propSplitUpOn env nv henv hU hT).StableOn where
  prop_liftN W _ hΓ' := propSplitUpOn_stableOn_prop_liftN henv hU hT W hΓ'
  proof_liftN W _ hΓ' := propSplitUpOn_stableOn_proof_liftN henv hU hT W hΓ'
  prop_instN := hpi
  proof_instN := hei

end SetModel

/-! ## 4. Where the guard **cannot** be paid: `interp_liftN` and `interp_inst`

`PropSplit.Stable`'s two load-bearing consumers are `InterpSubst.interp_liftN` and
`interp_inst`.  Both recurse over *raw syntax*; the only hypothesis either has about the term is
`ClosedN`.  At `.lam A b` and `.forallE A B` they apply the field at
`W' : Ctx.LiftN n (k+1) (A :: Γ) (A.liftN n k :: Γ')` (`InterpSubst.lean:235` and `:259`), so a
guarded field would demand `OnCtx (A.liftN n k :: Γ') (env.IsType nv)`.

`StableAudit.lean` says in prose that this is why `Stable` is unguarded.  Below it is a theorem:
the obligation is **false**, at every `Ordered` environment, for a *non-degenerate* lift and a
context that satisfies the guard.  The witness is a sort at an out-of-range universe parameter —
closed, so `ClosedN` cannot exclude it — and `IsDefEq.levelWF` refutes its typing without any
inversion and without any hole. -/

namespace SetModel

namespace StableGuarded

variable {env : VEnv} {nv : ℕ}

/-- **The obligation a guarded `Stable` would put on `interp_liftN`'s binder cases.**

Read off `InterpSubst.lean`'s `.lam`/`.forallE` cases: everything the recursion has about the
binder `A` at that point, plus the guard on the outer contexts, and the guard it would owe. -/
def InterpLiftNObligation (env : VEnv) (nv : ℕ) : Prop :=
  ∀ {n k : ℕ} {Γ Γ' : List VExpr} {A : VExpr}, Ctx.LiftN n k Γ Γ' →
    OnCtx Γ (env.IsType nv) → OnCtx Γ' (env.IsType nv) → A.ClosedN Γ.length →
    OnCtx (A.liftN n k :: Γ') (env.IsType nv)

/-- A sort at an out-of-range universe parameter has no type, in any context whose entries have
well-formed levels.  No environment hypothesis, no hole: `IsDefEq.levelWF` alone. -/
theorem not_isType_sort_param (hΓ : OnCtx Γ fun _ A => A.LevelWF 0) :
    ¬ env.IsType 0 Γ (.sort (.param 0)) := by
  rintro ⟨u, hu⟩
  exact absurd (hu.levelWF hΓ).1 (by simp [VExpr.LevelWF, VLevel.WF])

/-- **The obligation is FALSE**, at every environment, at a non-degenerate lift
(`Ctx.LiftN 1 0 [] [Prop]`) and a guard-satisfying context (`OnCtx [Prop]`).

So the flag day ruling 140 describes **stops here**: `Stable` cannot acquire an `OnCtx` guard
while `interp_liftN` keeps its present hypotheses.  Either `interp_liftN`/`interp_inst` gain a
hypothesis that types every binder of the term (and then `InterpSound.lean`'s six call sites owe
it), or `Stable` stays unguarded and `StableOn` is used only where the interpretation is not
involved.  This is a refutation, not a conjecture — contrast `handoff-setmodel.md` §13.5 item 1,
where the analogous negative had to be recorded as unproved. -/
theorem not_interpLiftNObligation : ¬ InterpLiftNObligation env 0 := by
  intro h
  have hs : env.HasType 0 [] (.sort .zero) (.sort (.succ .zero)) :=
    VEnv.IsDefEq.sortDF trivial trivial rfl
  have hΓ' : OnCtx [(VExpr.sort .zero : VExpr)] (env.IsType 0) := ⟨trivial, _, hs⟩
  have hcl : (VExpr.sort (.param 0)).ClosedN ([] : List VExpr).length := trivial
  have hobl := h (A := .sort (.param 0)) (Γ := []) (Γ' := [(VExpr.sort .zero : VExpr)])
    (Ctx.LiftN.one (A := .sort .zero)) trivial hΓ' hcl
  refine not_isType_sort_param (env := env) (Γ := [(VExpr.sort .zero : VExpr)])
    ⟨trivial, ?_⟩ ?_
  · show (VExpr.sort .zero).LevelWF 0
    simp [VExpr.LevelWF, VLevel.WF]
  · simpa [VExpr.liftN] using hobl.2

/-- The same fact stated the way a repair plan needs it: what `interp_liftN` would have to be
given.  `ClosedN` is not enough; the binder must be *typed*. -/
theorem interpLiftNObligation_iff_binder_isType :
    InterpLiftNObligation env nv ↔
      ∀ {n k : ℕ} {Γ Γ' : List VExpr} {A : VExpr}, Ctx.LiftN n k Γ Γ' →
        OnCtx Γ (env.IsType nv) → OnCtx Γ' (env.IsType nv) → A.ClosedN Γ.length →
        env.IsType nv Γ' (A.liftN n k) := by
  constructor
  · intro h _ _ _ _ _ W hΓ hΓ' hcl; exact (h W hΓ hΓ' hcl).2
  · intro h _ _ _ _ _ W hΓ hΓ' hcl; exact ⟨hΓ', h W hΓ hΓ' hcl⟩

end StableGuarded

end SetModel

/-! ## 5. Anti-vacuity: the narrowing is real, and the narrowed fields still have content

Adding `OnCtx` **narrows a quantifier**, so both halves are checked here, machine-checked, in the
order `docs/vacuity-ledger.md` §0 asks for.

**Also a correction to `handoff-setmodel.md` §13.4 item 4 and ledger rows 139d / 140d.**  Those
claim `bvar_one_instance` runs "with `Γ₁ = [.bvar 0, Prop]`, a context that is **not** `OnCtx`
(`PropAgreeWall.not_isType_bvar`)", and conclude from that witness that the guard sits on the
premise only.  **That context *is* `OnCtx`** — `onCtx_bvar_prop` below proves it at every
environment with no hypotheses.  `not_isType_bvar` is about `¬ env.IsType 0 [] (.bvar 0)`, i.e.
`.bvar 0` over the **empty** context; in `[.bvar 0, Prop]` the variable is looked up in `[Prop]`
and its type is `Prop`, which is a sort.  So `bvar_one_instance` shows the theorem works at
`k = 1`, and **nothing more**; the "guard is on the premise only" check is *not* established by it.
The genuine junk witnesses are `notOnCtx_lift_target` and `notOnCtx_inst_target` below, which use
an out-of-range universe parameter rather than a variable. -/

namespace SetModel

namespace StableGuarded

variable {env : VEnv} {nv : ℕ}

/-- **The correction.**  `[.bvar 0, Prop]` *is* a well-formed context. -/
theorem onCtx_bvar_prop :
    OnCtx [(VExpr.bvar 0 : VExpr), (VExpr.sort .zero : VExpr)] (env.IsType 0) :=
  ⟨⟨trivial, _, VEnv.IsDefEq.sortDF trivial trivial rfl⟩, .zero, VEnv.IsDefEq.bvar Lookup.zero⟩

/-- **The narrowing is real, for the two `lift` fields**: a lift whose target the guard excludes.
`Stable.prop_liftN` speaks at this lift; `StableOn.prop_liftN` says nothing. -/
theorem notOnCtx_lift_target :
    Ctx.LiftN 1 0 ([] : List VExpr) [(VExpr.sort (.param 0) : VExpr)] ∧
      ¬ OnCtx [(VExpr.sort (.param 0) : VExpr)] (env.IsType 0) :=
  ⟨Ctx.LiftN.one, fun h => not_isType_sort_param (env := env) (Γ := []) trivial h.2⟩

/-- **The narrowing is real, for the two `inst` fields** — and with the field's typing premise
`env.HasType nv Γ₀ e₀ A₀` *satisfied*, so this is not a witness that the field would have ignored
anyway.  `Γ₀ = []`, `e₀ = ∀ p : Prop, p`, `A₀ = Prop`, `k = 1`, and the extra binder is a sort at
an out-of-range parameter. -/
theorem notOnCtx_inst_target :
    Ctx.InstN ([] : List VExpr) (.forallE (.sort .zero) (.bvar 0)) (.sort .zero) 1
        [(VExpr.sort (.param 0) : VExpr), (VExpr.sort .zero : VExpr)]
        [(VExpr.sort (.param 0) : VExpr)] ∧
      preludeEnv.HasType 0 [] (.forallE (.sort .zero) (.bvar 0)) (.sort .zero) ∧
      ¬ OnCtx [(VExpr.sort (.param 0) : VExpr), (VExpr.sort .zero : VExpr)]
          (preludeEnv.IsType 0) := by
  refine ⟨?_, allProp_hasType, fun h => ?_⟩
  · exact (Ctx.InstN.succ (A := .sort (.param 0)) .zero)
  · refine not_isType_sort_param (env := preludeEnv) (Γ := [(VExpr.sort .zero : VExpr)])
      ⟨trivial, ?_⟩ h.2
    show (VExpr.sort .zero).LevelWF 0
    simp [VExpr.LevelWF, VLevel.WF]

/-! ### Content at `preludeEnv`

`propSplitUpOnPreludeEnv` is already a `PropSplit preludeEnv 0` **as data**
(`InstDescendBvar` §8b), so the class the guarded fields live on is inhabited where the recursion
goes.  What is checked here is the *fields*: that the guarded `prop_liftN` instance at
`preludeEnv` relates two **true** statements at one term and two **false** statements at another,
so it is neither vacuous nor constant. -/

/-- The guard *is* satisfiable at a non-degenerate lift: `OnCtx [Prop]`. -/
theorem onCtx_prop : OnCtx [(VExpr.sort .zero : VExpr)] (env.IsType 0) :=
  ⟨trivial, _, VEnv.IsDefEq.sortDF trivial trivial rfl⟩

/-- **Positive content.**  The guarded `prop_liftN` field at `preludeEnv`, at the lift
`Ctx.LiftN 1 0 [] [Prop]` whose target the guard admits, relating two statements that are **both
true**: `∀ p : Prop, p` is a proposition at `[]` and its lift is one at `[Prop]`. -/
theorem liftN_field_positive (ls : List ℕ) :
    OnCtx [(VExpr.sort .zero : VExpr)] (preludeEnv.IsType 0) ∧
      (preludeEnv.IsPropUpOn 0 ls [(VExpr.sort .zero : VExpr)]
          ((VExpr.forallE (.sort .zero) (.bvar 0)).liftN 1 0) ↔
        preludeEnv.IsPropUpOn 0 ls [] (.forallE (.sort .zero) (.bvar 0))) ∧
      preludeEnv.IsPropUpOn 0 ls [] (.forallE (.sort .zero) (.bvar 0)) := by
  refine ⟨onCtx_prop, VEnv.isPropUpOn_liftN preludeEnv_ordered Ctx.LiftN.one onCtx_prop, ?_⟩
  exact VEnv.IsPropUpOn.of_hasType (u := .zero) (Γ := []) trivial trivial allProp_hasType rfl

/-- **Discriminating content.**  At the same guarded lift, with `A := Prop`, both sides are
**false** — so the field is not the constant-true relation.  The negative half is
`InstDescendBvar.not_isPropUpOn_sort`, which itself goes through the *guarded* `PropUniqOnCtx`. -/
theorem liftN_field_discriminates (ls : List ℕ) :
    (preludeEnv.IsPropUpOn 0 ls [(VExpr.sort .zero : VExpr)]
        ((VExpr.sort .zero).liftN 1 0) ↔
      preludeEnv.IsPropUpOn 0 ls [] (.sort .zero)) ∧
      ¬ preludeEnv.IsPropUpOn 0 ls [] (.sort .zero) :=
  ⟨VEnv.isPropUpOn_liftN preludeEnv_ordered Ctx.LiftN.one onCtx_prop,
   InstDescendBvar.not_isPropUpOn_sort ls⟩

/-- **`StableOn`'s two `lift` fields are inhabited at `preludeEnv`, as data-free theorems**: the
guarded split there satisfies them, with no hypotheses at all. -/
theorem preludeEnv_stableOn_liftN
    {n k : ℕ} {Γ Γ' : List VExpr} (W : Ctx.LiftN n k Γ Γ')
    (hΓ' : OnCtx Γ' (preludeEnv.IsType 0)) (ls : List ℕ) (A e : VExpr) :
    (preludeEnv.IsPropUpOn 0 ls Γ' (A.liftN n k) ↔ preludeEnv.IsPropUpOn 0 ls Γ A) ∧
      (preludeEnv.IsProofUpOn 0 ls Γ' (e.liftN n k) ↔ preludeEnv.IsProofUpOn 0 ls Γ e) :=
  ⟨VEnv.isPropUpOn_liftN preludeEnv_ordered W hΓ',
   VEnv.isProofUpOn_liftN preludeEnv_ordered W hΓ'⟩

/-! ### `Above` — not used

Grep-level and stated as such: this file contains **no** occurrence of `Above`, no chosen `κ`, and
no `VDecl.unsafeDef`; every `preludeEnv` fact above comes from `preludeEnv_ordered` /
`allProp_hasType` / `PropAgreeWall.preludeEnv_propUniqOnCtx`.  So no result here is free at a
false antecedent of the `IsInaccessibleChain` kind. -/

end StableGuarded

end SetModel

end Lean4Lean

namespace Lean4Lean

/-! ## 6. The `.bvar k` case of `InstDescendUp` with **both** sides guarded

`InstDescendBvar` §4 proves the `.bvar k` case with a guarded premise and an *unguarded*
conclusion, and `handoff-setmodel.md` §13.5 item 4 records that guarding the conclusion too fails
"at the ascent `IsPropUpOn ls (A₀::Γ₀) → IsPropUpOn ls Γ₁`, which needs `OnCtx Γ₁`".

`StableOn.prop_instN` **supplies exactly that hypothesis**.  So the fully guarded case goes
through, and it is the shape `StableOn`'s `inst` fields at `L := propSplitUpOn` actually ask for.
The proof is §4's, with `isPropUpOn_liftN` (§2) in place of `isPropUp_liftN`. -/

namespace VEnv

variable {env : VEnv} {nv : ℕ}

/-- **`InstDescendUp.prop_inst`'s `.bvar k` case, guarded on both sides.**  Exactly what
`PropSplit.StableOn.prop_instN` at `propSplitUpOn` needs for `B = .bvar k`. -/
theorem prop_inst_bvar_on (henv : env.Ordered) (hR : env.SortRetypeOnCtx nv)
    {Γ₀ : List VExpr} {e₀ A₀ : VExpr} {k : ℕ} {Γ₁ Γ : List VExpr} {ls : List ℕ}
    (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ) (hΓ₁ : OnCtx Γ₁ (env.IsType nv))
    (h₀ : env.HasType nv Γ₀ e₀ A₀)
    (h : env.IsPropUpOn nv ls Γ ((VExpr.bvar k).inst e₀ k)) :
    env.IsPropUpOn nv ls Γ₁ (.bvar k) := by
  rw [VExpr.bvar_inst_self] at h
  have h₀' := IsPropUpOn.of_liftN W.liftN_target h
  have hz := isPropUpOn_bvar_zero henv hR h₀ h₀'
  rw [← VExpr.bvar_zero_liftN k]
  exact (isPropUpOn_liftN henv W.liftN_source hΓ₁).2 hz

/-- **`InstDescendUp.proof_inst`'s `.bvar k` case, guarded on both sides.** -/
theorem proof_inst_bvar_on (henv : env.Ordered) (hT : env.PropTypeAgreeOnCtx nv)
    {Γ₀ : List VExpr} {e₀ A₀ : VExpr} {k : ℕ} {Γ₁ Γ : List VExpr} {ls : List ℕ}
    (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ) (hΓ₁ : OnCtx Γ₁ (env.IsType nv))
    (h₀ : env.HasType nv Γ₀ e₀ A₀)
    (h : env.IsProofUpOn nv ls Γ ((VExpr.bvar k).inst e₀ k)) :
    env.IsProofUpOn nv ls Γ₁ (.bvar k) := by
  rw [VExpr.bvar_inst_self] at h
  have h₀' := IsProofUpOn.of_liftN W.liftN_target h
  have hz := isProofUpOn_bvar_zero henv hT h₀ h₀'
  rw [← VExpr.bvar_zero_liftN k]
  exact (isProofUpOn_liftN henv W.liftN_source hΓ₁).2 hz

end VEnv

end Lean4Lean

namespace Lean4Lean

/-! ## 7. The **ascent** halves of `StableOn`'s two `inst` fields, for the guarded predicate

`PropSplitUp` §4 proves the ascent halves for the unguarded `IsPropUp`
(`isPropUp_instN_up` / `isProofUp_instN_up`), through the purely syntactic square
`Ctx.InstN.pushLift'`.  Porting them to `IsPropUpOn` needs exactly one new fact: **`OnCtx` is
preserved by instantiation**, which the tree did not have.  With it, the two ports are
`PropSplitUp`'s proofs with one extra component in each anonymous constructor. -/

/-- **`OnCtx` survives instantiation.**  Two cases; the `.succ` one is `IsType.instN`. -/
theorem OnCtx.instN {env : VEnv} {nv : ℕ} (henv : env.Ordered) :
    ∀ {Γ₀ : List VExpr} {e₀ A₀ : VExpr} {k : ℕ} {Γ₁ Γ : List VExpr},
      Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ → env.HasType nv Γ₀ e₀ A₀ →
      OnCtx Γ₁ (env.IsType nv) → OnCtx Γ (env.IsType nv)
  | _, _, _, _, _, _, .zero, _, h => h.1
  | _, _, _, _, _, _, .succ W, h₀, h => ⟨OnCtx.instN henv W h₀ h.1, h.2.instN henv W h₀⟩

namespace VEnv

variable {env : VEnv} {nv : ℕ}

/-- **The ascent half of `StableOn.prop_instN`, for the guarded predicate — free.** -/
theorem isPropUpOn_instN_up (henv : env.Ordered) {Γ₀ : List VExpr} {e₀ A₀ : VExpr} {k : ℕ}
    {Γ₁ Γ : List VExpr} (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ) (h₀ : env.HasType nv Γ₀ e₀ A₀)
    {ls : List ℕ} {B : VExpr} (h : env.IsPropUpOn nv ls Γ₁ B) :
    env.IsPropUpOn nv ls Γ (B.inst e₀ k) := by
  obtain ⟨l, Γ₂, u, WL, hΓ₂, hu, hB, h0⟩ := h
  obtain ⟨l', ρ, Γ', Γ₀', k', WL', Wρ, WI', heq⟩ := Ctx.InstN.pushLift' l WL W
  have h₀' := h₀.weak' henv Wρ
  refine ⟨l', Γ', u, WL', OnCtx.instN henv WI' h₀' hΓ₂, hu, ?_, h0⟩
  have hi := hB.instN henv WI' h₀'
  have he := heq 0 B
  simp only [Nat.add_zero, Lift.consN] at he
  rw [he]
  exact hi

/-- **The ascent half of `StableOn.proof_instN`, for the guarded predicate — free.** -/
theorem isProofUpOn_instN_up (henv : env.Ordered) {Γ₀ : List VExpr} {e₀ A₀ : VExpr} {k : ℕ}
    {Γ₁ Γ : List VExpr} (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ) (h₀ : env.HasType nv Γ₀ e₀ A₀)
    {ls : List ℕ} {e : VExpr} (h : env.IsProofUpOn nv ls Γ₁ e) :
    env.IsProofUpOn nv ls Γ (e.inst e₀ k) := by
  obtain ⟨l, Γ₂, B, u, WL, hΓ₂, hu, he, hB, h0⟩ := h
  obtain ⟨l', ρ, Γ', Γ₀', k', WL', Wρ, WI', heq⟩ := Ctx.InstN.pushLift' l WL W
  have h₀' := h₀.weak' henv Wρ
  refine ⟨l', Γ', B.inst (e₀.lift' ρ) k', u, WL', OnCtx.instN henv WI' h₀' hΓ₂, hu, ?_,
    hB.instN henv WI' h₀', h0⟩
  have hi := he.instN henv WI' h₀'
  have hq := heq 0 e
  simp only [Nat.add_zero, Lift.consN] at hq
  rw [hq]
  exact hi

/-- **`StableOn`'s two `inst` fields at `B = .bvar k`, as `↔`s** — descent by §6, ascent by §7.
So the `.bvar k` instance of all four `StableOn` fields is now closed for `propSplitUpOn`. -/
theorem isPropUpOn_instN_bvar (henv : env.Ordered) (hR : env.SortRetypeOnCtx nv)
    {Γ₀ : List VExpr} {e₀ A₀ : VExpr} {k : ℕ} {Γ₁ Γ : List VExpr} {ls : List ℕ}
    (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ) (hΓ₁ : OnCtx Γ₁ (env.IsType nv))
    (h₀ : env.HasType nv Γ₀ e₀ A₀) :
    env.IsPropUpOn nv ls Γ ((VExpr.bvar k).inst e₀ k) ↔ env.IsPropUpOn nv ls Γ₁ (.bvar k) :=
  ⟨prop_inst_bvar_on henv hR W hΓ₁ h₀, isPropUpOn_instN_up henv W h₀⟩

theorem isProofUpOn_instN_bvar (henv : env.Ordered) (hT : env.PropTypeAgreeOnCtx nv)
    {Γ₀ : List VExpr} {e₀ A₀ : VExpr} {k : ℕ} {Γ₁ Γ : List VExpr} {ls : List ℕ}
    (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ) (hΓ₁ : OnCtx Γ₁ (env.IsType nv))
    (h₀ : env.HasType nv Γ₀ e₀ A₀) :
    env.IsProofUpOn nv ls Γ ((VExpr.bvar k).inst e₀ k) ↔ env.IsProofUpOn nv ls Γ₁ (.bvar k) :=
  ⟨proof_inst_bvar_on henv hT W hΓ₁ h₀, isProofUpOn_instN_up henv W h₀⟩

end VEnv

end Lean4Lean

/-! ## Axiom census -/

#print axioms Lean4Lean.Ctx.Lift'.pushOut_onCtx
#print axioms Lean4Lean.VEnv.isPropUpOn_lift'
#print axioms Lean4Lean.VEnv.isProofUpOn_lift'
#print axioms Lean4Lean.VEnv.isPropUpOn_liftN
#print axioms Lean4Lean.VEnv.isProofUpOn_liftN
#print axioms Lean4Lean.VEnv.propUpOnLiftAscend_at
#print axioms Lean4Lean.SetModel.PropSplit.StableOn
#print axioms Lean4Lean.SetModel.PropSplit.Stable.stableOn
#print axioms Lean4Lean.SetModel.propSplitUpOn_stableOn_prop_liftN
#print axioms Lean4Lean.SetModel.propSplitUpOn_stableOn_proof_liftN
#print axioms Lean4Lean.SetModel.propSplitUpOn_stableOn
#print axioms Lean4Lean.SetModel.StableGuarded.InterpLiftNObligation
#print axioms Lean4Lean.SetModel.StableGuarded.not_isType_sort_param
#print axioms Lean4Lean.SetModel.StableGuarded.not_interpLiftNObligation
#print axioms Lean4Lean.SetModel.StableGuarded.interpLiftNObligation_iff_binder_isType
#print axioms Lean4Lean.SetModel.StableGuarded.onCtx_bvar_prop
#print axioms Lean4Lean.SetModel.StableGuarded.notOnCtx_lift_target
#print axioms Lean4Lean.SetModel.StableGuarded.notOnCtx_inst_target
#print axioms Lean4Lean.SetModel.StableGuarded.onCtx_prop
#print axioms Lean4Lean.SetModel.StableGuarded.liftN_field_positive
#print axioms Lean4Lean.SetModel.StableGuarded.liftN_field_discriminates
#print axioms Lean4Lean.SetModel.StableGuarded.preludeEnv_stableOn_liftN
#print axioms Lean4Lean.VEnv.prop_inst_bvar_on
#print axioms Lean4Lean.VEnv.proof_inst_bvar_on
#print axioms Lean4Lean.OnCtx.instN
#print axioms Lean4Lean.VEnv.isPropUpOn_instN_up
#print axioms Lean4Lean.VEnv.isProofUpOn_instN_up
#print axioms Lean4Lean.VEnv.isPropUpOn_instN_bvar
#print axioms Lean4Lean.VEnv.isProofUpOn_instN_bvar
