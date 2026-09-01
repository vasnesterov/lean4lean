import Lean4Lean.Theory.Typing.Strengthen

/-!
# The typing half's obstruction is the **uninhabited** stripped entries — so the
"consumer hands over the missing inhabitant" manoeuvre is dead here

`TypingStrengthening` (`Strengthen.lean` §2, equivalently `PiDescend` by §9(b)) is the typing
half of `IsDefEqU.weakN_iff` and, with `hasType_app_bvar0`, the gate that 46 of the hole's 296
transitive users route through (`scripts/weakn-gate-split.lean` at `d67375b`).

Two files closed their residuals by the same trick: `InjPiInhab.lean` retired `ConvCStrengthen`
by noticing every consumer hands over the subject whose typings produced the chain, and
`CRPiDescend.lean` closed `hasType_app_bvar0` by noticing the Π is *built* downstairs.  The
obvious next move is to try it on `TypingStrengthening`: is it an obligation stated without an
inhabitant its consumers always have?

**No, and this file says why with theorems rather than by inspection.**

* §1 `TypingStrengthening.of_instN`, `PiDescend.of_instN` — the instance where an inhabitant of
  the *stripped entry*
  is available is a theorem, `sorry`-free.  This is `Strengthen.lean` §1 at the typing
  judgment, and it is the only shape of inhabitant that helps: the conclusion `VExpr.WF env U Γ e`
  is about a context `Γ` the hypothesis already talks about, so an inhabitant of anything in
  `Γ` is derivable from `hΓ`-side data and buys nothing.
* §2 `TypingStrengthening1` — the typing half restricted to stripping **one** entry is the
  whole of it (`iff`, both directions).  `Strengthen.lean` §11 does this for the conversion
  target; the typing half needs its own version because `TypingStrengthening.typed`, which the
  context-inversion step consumes, quantifies over all lifting witnesses.
* §3 `TypingStrengthening1Uninhab` — the typing half restricted to a stripped entry that is
  **uninhabited in its own prefix context** is the whole of it (`iff`), by the classical case
  split §1 makes available.  So *every* instance in which any consumer could hand over an
  inhabitant of the stripped entry is already closed, and the residual consists exactly of the
  instances where no such inhabitant exists — which no consumer can supply.
* §4 the vacuity dual, `typingStrengthening_of_allInhabited`: if every stripped entry were
  inhabited, §1 alone would close the typing half.  So §3 is non-vacuous exactly to the extent
  that uninhabited types over a `VEnv.WF` environment exist, which by
  `consistent_iff_exists_uninhabited_prop` (`Verify/Typing/ProjInhab.lean:185`) is
  `VEnv.Consistent` — proved here for no environment.  The bound is therefore two-sided and
  neither side is an accident.
* §5 `hasType_app_bvar0_of_inhab` — the same manoeuvre applied to the *tenth* typing gate, and
  here it **works**: `hasType_app_bvar0` with an inhabitant of its binder needs neither
  `TypingStrengthening` nor `IsDefEqU.weakN_iff`, and its cone is strictly smaller than both
  existing versions'.  But **neither of its two call sites can supply the inhabitant** --
  `ChurchRosser.lean:1453` is the `etaL` case of `parRed_beta`'s second component, where the
  binder comes from the η-premise and no term of it is in scope, and `:1474` is the `app` case
  of the `proofIrrel` branch, where the binder is the context head and again unpopulated.  Read
  by inspection of those two branches, *not* machine-checked.  So §5 is a lemma looking for a
  caller, not a reduction of site 7's row.

## Why this closes the route rather than narrowing it

`Strengthen.lean` §12 proves the analogous `iff` for the *conversion* target.  What §3 adds is
that the typing half — the part that is *not* the `trans` residual, and the part ten gates
depend on — has the same obstruction, so the two halves do not differ in this respect.  The
consequence for the manoeuvre is exact:

> An extra hypothesis on `TypingStrengthening` can only make it provable if it is (or yields)
> an inhabitant of the stripped entry, by §3.  A consumer that had one would already be
> discharged by §1 without any hypothesis.  Hence no consumer of `TypingStrengthening` in this
> tree can be relieved by handing over data it already has.

That is a negative about a *technique*, not about the statement: `TypingStrengthening` remains
open, and nothing here bears on the confluence route (`NormalEqStrengthen.lean` §3), which does
not go through an inhabitant.

## Measured cones (`scripts/hole-cone.lean`'s `deps`, `allowOpaque := true`)

| seed | cone | holes in cone |
| --- | --- | --- |
| §1 `TypingStrengthening.of_instN` | 1119 | **none** |
| §1 `TypingStrengthening.wf_of_instN` | 1122 | **none** |
| §3 `TypingStrengthening1Uninhab.typingStrengthening1` | 1151 | **none** |
| §3 `TypingStrengthening1.split` | 1153 | **none** |
| §1 `PiDescend.of_instN` | 3324 | **none** |
| §2 `typed_of_at` | 3587 | `forallE_inv_stratified`, `rigidShapeUniqNS` |
| §2 `TypingStrengthening1.typing` | 3599 | `forallE_inv_stratified`, `rigidShapeUniqNS` |
| §3 `TypingStrengthening1Uninhab.iff_typing` | 3607 | `forallE_inv_stratified`, `rigidShapeUniqNS` |
| §4 `typingStrengthening_of_allInhabited` | 3602 | `forallE_inv_stratified`, `rigidShapeUniqNS` |
| baseline `TypingStrengthening.typed` (`Strengthen.lean` §3) | 3588 | `forallE_inv_stratified`, `rigidShapeUniqNS` |
| baseline `TypingStrengthening.onCtx_inv` (`StrengthenNarrow.lean` §5) | 3593 | `forallE_inv_stratified`, `rigidShapeUniqNS` |
| §5 `hasType_app_bvar0_of_inhab` | **3449** | **`forallE_inv_stratified`** |
| `hasType_app_bvar0` (`ChurchRosser.lean:1336`) | 3465 | `IsDefEqU.weakN_iff`, `forallE_inv_stratified` |
| `hasType_app_bvar0_of_typing` (`CRPiDescend.lean` §1) | 3609 | `forallE_inv_stratified`, `rigidShapeUniqNS` |

Two readings:

* `IsDefEqU.weakN_iff` is in **no** cone in this file.  §2-§4 take on the two holes the
  baseline `TypingStrengthening` machinery already carries and nothing else, and §1 and §3's
  `←` direction are hole-free outright (`#print axioms` `[propext, Quot.sound]` /
  `[propext, Classical.choice, Quot.sound]`).
* §5 is **not** `sorry`-free — `IsDefEq.uniq` puts `forallE_inv_stratified` in its cone, as it
  does in the original — but it is strictly better than *both* existing versions of the gate:
  3449 against 3465 and 3609, and its hole set is a strict subset of both.  It drops
  `IsDefEqU.weakN_iff` (which the original has) *and* `rigidShapeUniqNS` (which the typing-half
  version brings in).  `#print axioms` cannot see any of this: every declaration in the second
  block reports `sorryAx` because the ambient holes carry it.
-/

namespace Lean4Lean
namespace VEnv

open VExpr

variable {env : VEnv} {U : Nat}

/-! ## 1. The instance with an inhabited stripped entry is a theorem

`Strengthen.lean` §1's `IsDefEq.strengthen_of_instN` at the typing judgment, with the type left
existential exactly as `TypingStrengthening` leaves it.  Note the type of the conclusion is
`A.inst e₀ k`, *not* `A`: the hypothesis's type `A` lives upstairs and need not be a lift, so
substituting the inhabitant into it is the only type available — which is precisely why
`TypingStrengthening` is stated with an existential type. -/

/-- **Strengthening a typing across an inhabited entry**, sorry-free. -/
theorem TypingStrengthening.of_instN (henv : Ordered env)
    (W : Ctx.InstN Γ₀ e₀ A₀ k Γ' Γ) (h₀ : env.HasType U Γ₀ e₀ A₀)
    (H : env.HasType U Γ' (e.liftN 1 k) A) : env.HasType U Γ e (A.inst e₀ k) := by
  have := H.instN henv W h₀
  rwa [inst_liftN] at this

/-- The same, in `TypingStrengthening`'s own conclusion shape. -/
theorem TypingStrengthening.wf_of_instN (henv : Ordered env)
    (W : Ctx.InstN Γ₀ e₀ A₀ k Γ' Γ) (h₀ : env.HasType U Γ₀ e₀ A₀)
    (H : env.HasType U Γ' (e.liftN 1 k) A) : VExpr.WF env U Γ e :=
  ⟨_, TypingStrengthening.of_instN henv W h₀ H⟩

variable! (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U)) in
/-- **The same for `PiDescend`**, the statement `TypingStrengthening` actually *is*
(`Strengthen.lean` §9(b)), so that the negative below is about the open statement itself and not
only about its packaging.  The application is assembled upstairs, strengthened across the
inhabited entry by §1, and taken apart downstairs by `HasType.app_inv`. -/
theorem PiDescend.of_instN {f a A B : VExpr}
    (W : Ctx.InstN Γ₀ e₀ A₀ k Γ' Γ) (h₀ : env.HasType U Γ₀ e₀ A₀)
    (hf : env.HasType U Γ' (f.liftN 1 k) (.forallE A B))
    (ha : env.HasType U Γ' (a.liftN 1 k) A) :
    ∃ A₁ B₁, env.HasType U Γ f (.forallE A₁ B₁) ∧ env.HasType U Γ a A₁ :=
  (TypingStrengthening.wf_of_instN henv.ordered W h₀
    (show env.HasType U Γ' ((VExpr.app f a).liftN 1 k) _ from hf.app ha)).app_inv henv hΓ

/-! ## 2. One entry at a time is enough for the typing half

`TypingStrengthening.typed` (`Strengthen.lean` §3) is applied at a *single* lifting witness in
its own proof, so it localises: `typed_of_at` below takes only the instance of the hypothesis
at that witness.  That is what lets the `n = 1` statement drive the context inversion, which is
in turn what lets the general `n` be reassembled from it. -/

private theorem onCtx_of_append₁ {P} :
    ∀ {As Γ : List VExpr}, OnCtx (As ++ Γ) P → OnCtx Γ P
  | [], _, h => h
  | _::_, _, h => onCtx_of_append₁ h.1

variable! (henv : VEnv.WF env) in
/-- `TypingStrengthening.typed`, with the hypothesis localised to the one lifting witness its
proof uses.  Statement and proof are `Strengthen.lean` §3's, with `HT W hΓ hΓ'` replaced by the
localised `HT`. -/
theorem typed_of_at {n k : Nat} {Γ Γ' : List VExpr} {e A : VExpr}
    (HT : ∀ {e' A' : VExpr}, env.HasType U Γ' (e'.liftN n k) A' → VExpr.WF env U Γ e')
    (hΓ : OnCtx Γ (env.IsType U)) (hΓ' : OnCtx Γ' (env.IsType U))
    (H : env.HasType U Γ' (e.liftN n k) (A.liftN n k)) : env.HasType U Γ e A := by
  have ⟨u, hA⟩ := H.isType henv hΓ'
  have hlam : env.HasType U Γ' (.lam (A.liftN n k) (.bvar 0))
      (.forallE (A.liftN n k) ((A.liftN n k).lift)) := .lamDF hA (.bvar .zero)
  have happ := hlam.app H
  rw [inst_lift] at happ
  have hlift : VExpr.liftN n (.app (.lam A (.bvar 0)) e) k
      = .app (.lam (A.liftN n k) (.bvar 0)) (e.liftN n k) := rfl
  have wf : VExpr.WF env U Γ (.app (.lam A (.bvar 0)) e) := HT (hlift ▸ happ)
  have ⟨A'', B'', hf, ha⟩ := wf.app_inv henv hΓ
  have ⟨⟨u₀, hA₀⟩, _, hb⟩ := hf.lam_inv henv hΓ
  have hf' : env.HasType U Γ (.lam A (.bvar 0)) (.forallE A A.lift) := .lamDF hA₀ (.bvar .zero)
  have := (hf'.uniqU henv hΓ hf).forallE_inv henv hΓ
  exact ha.defeqU_r henv hΓ (let ⟨_, h⟩ := this.1; ⟨_, h.symm⟩)

/-- **The typing half, restricted to stripping a single entry.** -/
def TypingStrengthening1 (env : VEnv) (U : Nat) : Prop :=
  ∀ {k : Nat} {Γ Γ' : List VExpr} {e A : VExpr}, Ctx.LiftN 1 k Γ Γ' →
    OnCtx Γ (env.IsType U) → OnCtx Γ' (env.IsType U) →
    env.HasType U Γ' (e.liftN 1 k) A → VExpr.WF env U Γ e

theorem TypingStrengthening.one (H : TypingStrengthening env U) : TypingStrengthening1 env U :=
  fun W hΓ hΓ' h => H W hΓ hΓ' h

variable! (henv : VEnv.WF env) in
/-- `StrengthenNarrow.lean` §5's `onCtx_inv` off the one-entry hypothesis.  Every use is at the
same witness the statement is given at, so `n = 1` suffices. -/
theorem TypingStrengthening1.onCtx_inv (HT : TypingStrengthening1 env U) :
    ∀ {k : Nat} {Γ Γ' : List VExpr}, Ctx.LiftN 1 k Γ Γ' →
      OnCtx Γ' (env.IsType U) → OnCtx Γ (env.IsType U) := by
  intro k Γ Γ' W
  induction W with
  | zero => exact onCtx_of_append₁
  | @succ k Γ Γ' A W ih =>
    intro h
    have hΓ := ih h.1
    have ⟨u, hA⟩ := h.2
    exact ⟨hΓ, u, typed_of_at henv (fun h' => HT W hΓ h.1 h') hΓ h.1 hA⟩

variable! (henv : VEnv.WF env) in
/-- **Stripping one entry at a time is enough for the typing half.** -/
theorem TypingStrengthening1.typing (H : TypingStrengthening1 env U) :
    TypingStrengthening env U := by
  intro n
  induction n with
  | zero =>
    intro k Γ Γ' e A W _ _ h
    cases W.eq_of_zero
    have h' : env.HasType U Γ e A := by simpa using h
    exact ⟨A, h'⟩
  | succ n ih =>
    intro k Γ Γ' e A W hΓ hΓ' h
    obtain ⟨Γ₁, W1, W2⟩ := W.split_one
    have hΓ₁ := H.onCtx_inv henv W2 hΓ'
    have h' : env.HasType U Γ' (VExpr.liftN 1 (VExpr.liftN n e k) k) A := by
      rw [VExpr.liftN'_liftN_hi]; exact h
    have ⟨A₁, h₁⟩ := H W2 hΓ₁ hΓ' h'
    exact ih W1 hΓ hΓ₁ h₁

variable! (henv : VEnv.WF env) in
/-- **The one-entry typing half is the typing half.** -/
theorem TypingStrengthening1.iff_typing :
    TypingStrengthening1 env U ↔ TypingStrengthening env U :=
  ⟨fun H => H.typing henv, TypingStrengthening.one⟩

/-! ## 3. And the obstruction is exactly the uninhabited entries

The typing-half analogue of `Strengthen.lean` §12.  The case split is §1's. -/

/-- **The typing half, restricted to an uninhabited stripped entry.** -/
def TypingStrengthening1Uninhab (env : VEnv) (U : Nat) : Prop :=
  ∀ {k : Nat} {Γ Γ' : List VExpr} {e A : VExpr}, Ctx.LiftN 1 k Γ Γ' →
    OnCtx Γ (env.IsType U) → OnCtx Γ' (env.IsType U) →
    (∀ Γ₀ A₀ e₀, Ctx.InstN Γ₀ e₀ A₀ k Γ' Γ → ¬ env.HasType U Γ₀ e₀ A₀) →
    env.HasType U Γ' (e.liftN 1 k) A → VExpr.WF env U Γ e

theorem TypingStrengthening1.uninhab (H : TypingStrengthening1 env U) :
    TypingStrengthening1Uninhab env U := fun W hΓ hΓ' _ h => H W hΓ hΓ' h

/-- **The uninhabited case is the whole one-entry typing half**, sorry-free: if the entry has an
inhabitant, §1 closes the instance outright. -/
theorem TypingStrengthening1Uninhab.typingStrengthening1 (henv : Ordered env)
    (H : TypingStrengthening1Uninhab env U) : TypingStrengthening1 env U := by
  intro k Γ Γ' e A W hΓ hΓ' h
  by_cases hin : ∃ Γ₀ A₀ e₀, Ctx.InstN Γ₀ e₀ A₀ k Γ' Γ ∧ env.HasType U Γ₀ e₀ A₀
  · obtain ⟨Γ₀, A₀, e₀, hI, h₀⟩ := hin
    exact TypingStrengthening.wf_of_instN henv hI h₀ h
  · exact H W hΓ hΓ' (fun Γ₀ A₀ e₀ hI h₀ => hin ⟨Γ₀, A₀, e₀, hI, h₀⟩) h

variable! (henv : VEnv.WF env) in
/-- **The uninhabited case is the whole typing half.** -/
theorem TypingStrengthening1Uninhab.typing (H : TypingStrengthening1Uninhab env U) :
    TypingStrengthening env U :=
  TypingStrengthening1.typing henv (H.typingStrengthening1 henv.ordered)

variable! (henv : VEnv.WF env) in
theorem TypingStrengthening1Uninhab.iff_typing :
    TypingStrengthening1Uninhab env U ↔ TypingStrengthening env U :=
  ⟨fun H => H.typing henv, fun H => TypingStrengthening1.uninhab (TypingStrengthening.one H)⟩

/-! ## 4. The vacuity dual -/

variable! (henv : VEnv.WF env) in
/-- **If every stripped entry were inhabited, §1 alone would close the typing half.**  So §3's
residual carries content exactly to the extent that uninhabited entries exist. -/
theorem typingStrengthening_of_allInhabited
    (hinh : ∀ {k : Nat} {Γ Γ' : List VExpr}, Ctx.LiftN 1 k Γ Γ' → OnCtx Γ' (env.IsType U) →
      ∃ Γ₀ A₀ e₀, Ctx.InstN Γ₀ e₀ A₀ k Γ' Γ ∧ env.HasType U Γ₀ e₀ A₀) :
    TypingStrengthening env U := by
  refine TypingStrengthening1.typing henv fun {k Γ Γ' e A} W _ hΓ' h => ?_
  obtain ⟨Γ₀, A₀, e₀, hI, h₀⟩ := hinh W hΓ'
  exact TypingStrengthening.wf_of_instN henv.ordered hI h₀ h

/-- **The manoeuvre's exact scope**, as a statement rather than a remark: an extra hypothesis
handed over by a consumer relieves `TypingStrengthening` only if it yields an inhabitant of the
stripped entry, and in that case §1 already discharges the instance with no hypothesis at all.
Formally: the *only* instances of the one-entry typing half that are still open are those in
which no consumer can supply such an inhabitant. -/
theorem TypingStrengthening1.split (henv : Ordered env) :
    TypingStrengthening1 env U ↔ TypingStrengthening1Uninhab env U :=
  ⟨TypingStrengthening1.uninhab, fun H => H.typingStrengthening1 henv⟩

/-! ## 5. The same manoeuvre on the tenth gate, where it does work

`ChurchRosser.lean:1336`'s

    hasType_app_bvar0 (hΓ : OnCtx (A::Γ)) (H : A::Γ ⊢ e.lift.app (bvar 0) : B) :
        ∃ B', Γ ⊢ e : .forallE A B'

is `CRPiDescend.lean` §1's tenth typing gate.  Given an inhabitant of the binder `A` it needs
no strengthening at all: instantiate the hypothesis at that inhabitant, and
`(e.lift.app (bvar 0)).inst a = e.app a`, so `HasType.app_inv` downstairs hands back a Π type
for `e` directly.  Its domain is only *convertible* to `A`, and that conversion is between two
types of `Γ` — no lift in sight — so aligning it is free. -/

variable! (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U)) in
/-- **`hasType_app_bvar0` with an inhabited binder**: no `TypingStrengthening` and no
`IsDefEqU.weakN_iff`, and `rigidShapeUniqNS` absent too, so its cone (3449) is strictly smaller
than the original's (3465) and than `hasType_app_bvar0_of_typing`'s (3609), with a strictly
smaller hole set than either.  Not `sorry`-free: `IsDefEq.uniq` carries
`forallE_inv_stratified`, which the original carries as well. -/
theorem hasType_app_bvar0_of_inhab {A a e B : VExpr} (ha : env.HasType U Γ a A)
    (H : env.HasType U (A::Γ) ((e.lift).app (.bvar 0)) B) :
    ∃ B', env.HasType U Γ e (.forallE A B') := by
  have hi : env.HasType U Γ (((e.lift).app (.bvar 0)).inst a 0) (B.inst a 0) :=
    H.instN henv.ordered .zero ha
  rw [show ((e.lift).app (.bvar 0)).inst a 0 = e.app a by simp [VExpr.inst, inst_lift]] at hi
  have ⟨A', B', hf, ha'⟩ := hi.app_inv henv hΓ
  have ⟨_, d4⟩ := ha'.uniq henv hΓ ha
  have ⟨_, d1⟩ := hf.isType henv hΓ
  have ⟨_, _, d3⟩ := d1.forallE_inv henv
  exact ⟨B', HasType.defeqU_r henv hΓ ⟨_, d4.forallEDF d3⟩ hf⟩
