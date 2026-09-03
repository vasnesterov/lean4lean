import Lean4Lean.Theory.Typing.Strong
import Lean4Lean.Theory.Typing.EnvLemmas

/-!
# The shape-descent statements, moved *above* `UniqueTyping.lean`, and the gate bodies they buy

## Why this file exists

`docs/handoff-pidescend.md` §3.3 proposes replacing the **bodies** of the fourteen declarations
that `Theory/Typing/UniqueTyping.lean` states after its hole `VEnv.IsDefEqU.weakN_iff` (`:190`)
so that they route through `VEnv.TypingStrengthening` instead of through the hole.  Two things
block that, and this file removes the first and *measures* the second.

**Blocker 1 -- import order.**  `TypingStrengthening`, `SortDescend`, `PiDescend` and the three
theorems relating them were defined in `Theory/Typing/Strengthen.lean`, which *imports*
`UniqueTyping.lean`, so they were unusable in it.  They are moved here verbatim; this module's
import closure is a subset of `UniqueTyping.lean`'s own, so `UniqueTyping.lean` can import it,
and nothing in this file can possibly depend on the hole.  `Strengthen.lean` re-exports them by
importing this module, so **no name changes and no call sites change**.

**Blocker 2 -- `TypingStrengthening` has no unconditional inhabitant.**  It is exactly
`PiDescend` (`Strengthen.lean` §9), which is open.  So the gate bodies *cannot* be replaced
today: every producer of `TypingStrengthening` in the built environment needs either an open
statement or the hole itself as a hypothesis (measured: `docs/handoff-gatebody.md` §2).  What
this file therefore provides is the **conditional** gate bodies, machine-checked, in a position
where they provably cannot see the hole -- so that when `PiDescend` becomes a theorem the edit
to `UniqueTyping.lean` is `body := GateBody.<lemma> henv (thePiDescendTheorem …) …` and nothing
else.

## What is here

* §1  moved verbatim from `Strengthen.lean`: `VExpr.liftVar_eq_zero`, `VExpr.liftN_eq_*`,
  `Lookup.weakN_inv` (its §4), `TypingStrengthening` (its §2), `SortDescend` / `PiDescend` and
  `TypingStrengthening.of` / `.sortDescend` / `.piDescend` (its §7).
* §2  `namespace GateBody`: the six gates of `UniqueTyping.lean` that `TypingStrengthening`
  discharges **hole-free**, each stated *verbatim* as `UniqueTyping.lean` states it with one
  hypothesis `HT : TypingStrengthening env U` added.  These are the drop-in bodies.
* §3  what is **not** here, and why: the three `HasType`-shaped gates and the five conversion
  gates.  See `docs/handoff-gatebody.md` §3 for the measured per-gate table.

Nothing here closes a hole, and nothing here removes a `sorry`.
-/

namespace Lean4Lean
namespace VEnv

open VExpr

variable {env : VEnv} {U : Nat}

/-! ## 1. Moved from `Theory/Typing/Strengthen.lean`

Verbatim; only the section headings are new.  `Strengthen.lean` §2's `Strengthening`,
`TransStrengthening` and everything from its §3 on stay where they were. -/

/-- **Typing strengthening**: the reflexive instance of `Strengthening`, with the type left
existential.  This is `VExpr.WF.weakN_iff`'s forward direction, weakened so that the type is
not required to be lifted. -/
def TypingStrengthening (env : VEnv) (U : Nat) : Prop :=
  ∀ {n k : Nat} {Γ Γ' : List VExpr} {e A : VExpr}, Ctx.LiftN n k Γ Γ' →
    OnCtx Γ (env.IsType U) → OnCtx Γ' (env.IsType U) →
    env.HasType U Γ' (e.liftN n k) A → VExpr.WF env U Γ e

/-! ### Inversion of `liftN` against a head constructor (`Strengthen.lean` §4) -/

section
variable {n k : Nat}

theorem _root_.Lean4Lean.VExpr.liftVar_eq_zero {j : Nat} (h : liftVar n j k = 0) : j = 0 := by
  unfold liftVar at h; split at h <;> omega

theorem _root_.Lean4Lean.VExpr.liftN_eq_bvar {e : VExpr} (h : e.liftN n k = .bvar i) :
    ∃ j, e = .bvar j ∧ i = liftVar n j k := by
  cases e <;> simp [VExpr.liftN] at h; exact ⟨_, rfl, h.symm⟩

theorem _root_.Lean4Lean.VExpr.liftN_eq_sort {e : VExpr} (h : e.liftN n k = .sort l) :
    e = .sort l := by cases e <;> simp [VExpr.liftN] at h; exact h ▸ rfl

theorem _root_.Lean4Lean.VExpr.liftN_eq_const {e : VExpr} (h : e.liftN n k = .const c ls) :
    e = .const c ls := by cases e <;> simp [VExpr.liftN] at h; exact h.1 ▸ h.2 ▸ rfl

theorem _root_.Lean4Lean.VExpr.liftN_eq_app {e : VExpr} (h : e.liftN n k = .app f a) :
    ∃ f' a', e = .app f' a' ∧ f = f'.liftN n k ∧ a = a'.liftN n k := by
  cases e <;> simp [VExpr.liftN] at h; exact ⟨_, _, rfl, h.1.symm, h.2.symm⟩

theorem _root_.Lean4Lean.VExpr.liftN_eq_lam {e : VExpr} (h : e.liftN n k = .lam A b) :
    ∃ A' b', e = .lam A' b' ∧ A = A'.liftN n k ∧ b = b'.liftN n (k+1) := by
  cases e <;> simp [VExpr.liftN] at h; exact ⟨_, _, rfl, h.1.symm, h.2.symm⟩

theorem _root_.Lean4Lean.VExpr.liftN_eq_forallE {e : VExpr} (h : e.liftN n k = .forallE A b) :
    ∃ A' b', e = .forallE A' b' ∧ A = A'.liftN n k ∧ b = b'.liftN n (k+1) := by
  cases e <;> simp [VExpr.liftN] at h; exact ⟨_, _, rfl, h.1.symm, h.2.symm⟩

end

/-! ### The two shape-descent statements (`Strengthen.lean` §7) -/

/-- A lifted term typed at a sort upstairs is typed at a sort downstairs. -/
def SortDescend (env : VEnv) (U : Nat) : Prop :=
  ∀ {n k : Nat} {Γ Γ' : List VExpr} {e : VExpr} {u : VLevel}, Ctx.LiftN n k Γ Γ' →
    OnCtx Γ (env.IsType U) → OnCtx Γ' (env.IsType U) →
    env.HasType U Γ' (e.liftN n k) (.sort u) → VExpr.WF env U Γ e →
    ∃ u₀, env.HasType U Γ e (.sort u₀)

/-- A lifted function applied to a lifted argument upstairs is a function applied to an
argument of its domain downstairs. -/
def PiDescend (env : VEnv) (U : Nat) : Prop :=
  ∀ {n k : Nat} {Γ Γ' : List VExpr} {f a A B : VExpr}, Ctx.LiftN n k Γ Γ' →
    OnCtx Γ (env.IsType U) → OnCtx Γ' (env.IsType U) →
    env.HasType U Γ' (f.liftN n k) (.forallE A B) → env.HasType U Γ' (a.liftN n k) A →
    VExpr.WF env U Γ f → VExpr.WF env U Γ a →
    ∃ A₀ B₀, env.HasType U Γ f (.forallE A₀ B₀) ∧ env.HasType U Γ a A₀

theorem _root_.Lean4Lean.Lookup.weakN_inv (W : Ctx.LiftN n k Γ Γ')
    (H : Lookup Γ' (liftVar n i k) A') : ∃ A, A' = A.liftN n k ∧ Lookup Γ i A := by
  rw [← Lift.liftVar_consN_skipN] at H
  obtain ⟨A, rfl, h⟩ := H.weakU_inv (Ctx.liftN_iff_lift'.1 W)
  exact ⟨A, by rw [VExpr.lift'_consN_skipN], h⟩

variable! (henv : VEnv.WF env) in
theorem TypingStrengthening.of (HS : SortDescend env U) (HP : PiDescend env U) :
    TypingStrengthening env U := by
  suffices H : ∀ {Γ' e' A b}, env.HasTypeStrong U Γ' e' A b → ∀ {n k Γ e}, Ctx.LiftN n k Γ Γ' →
      OnCtx Γ (env.IsType U) → OnCtx Γ' (env.IsType U) → e.liftN n k = e' →
      VExpr.WF env U Γ e by
    intro n k Γ Γ' e A W hΓ hΓ' h
    exact H (h.strong henv hΓ').hasType'.1 W hΓ hΓ' rfl
  intro Γ' e' A b H
  induction H with
  | bvar h _ _ _ =>
    intro n k Γ e W hΓ hΓ' eq
    obtain ⟨j, rfl, rfl⟩ := VExpr.liftN_eq_bvar eq
    obtain ⟨A₀, rfl, h'⟩ := Lookup.weakN_inv W h
    exact ⟨_, .bvar h'⟩
  | sort' h1 _ _ =>
    intro n k Γ e W hΓ hΓ' eq
    cases VExpr.liftN_eq_sort eq
    exact ⟨_, .sortDF h1 h1 rfl⟩
  | const h1 h2 h3 _ _ _ _ _ =>
    intro n k Γ e W hΓ hΓ' eq
    cases VExpr.liftN_eq_const eq
    exact ⟨_, .constDF h1 h2 h2 h3 (List.Forall₂.rfl fun _ _ => rfl)⟩
  | app _ _ _ _ _ hf ha _ _ _ _ ihf iha _ =>
    intro n k Γ e W hΓ hΓ' eq
    obtain ⟨f₀, a₀, rfl, rfl, rfl⟩ := VExpr.liftN_eq_app eq
    have ⟨A₀, B₀, hf', ha'⟩ := HP W hΓ hΓ' hf.hasType ha.hasType
      (ihf W hΓ hΓ' rfl) (iha W hΓ hΓ' rfl)
    exact ⟨_, .appDF hf' ha'⟩
  | lam _ _ hA _ hbody _ ihA _ ihbody _ =>
    intro n k Γ e W hΓ hΓ' eq
    obtain ⟨A₀, b₀, rfl, rfl, rfl⟩ := VExpr.liftN_eq_lam eq
    have ⟨u₀, hA₀⟩ := HS W hΓ hΓ' hA.hasType (ihA W hΓ hΓ' rfl)
    have hΓ₁ : OnCtx (A₀::Γ) (env.IsType U) := ⟨hΓ, _, hA₀⟩
    have ⟨B₀, hb₀⟩ := ihbody W.succ hΓ₁ ⟨hΓ', _, hA.hasType⟩ rfl
    exact ⟨_, .lamDF hA₀ hb₀⟩
  | forallE _ _ hA hbody ihA ihbody =>
    intro n k Γ e W hΓ hΓ' eq
    obtain ⟨A₀, b₀, rfl, rfl, rfl⟩ := VExpr.liftN_eq_forallE eq
    have ⟨u₀, hA₀⟩ := HS W hΓ hΓ' hA.hasType (ihA W hΓ hΓ' rfl)
    have hΓ₁ : OnCtx (A₀::Γ) (env.IsType U) := ⟨hΓ, _, hA₀⟩
    have ⟨v₀, hb₀⟩ := HS W.succ hΓ₁ ⟨hΓ', _, hA.hasType⟩ hbody.hasType
      (ihbody W.succ hΓ₁ ⟨hΓ', _, hA.hasType⟩ rfl)
    exact ⟨_, .forallEDF hA₀ hb₀⟩
  | base _ ih => exact ih
  | defeq _ _ _ _ _ _ _ ih => exact ih

variable! (henv : VEnv.WF env) in
theorem TypingStrengthening.sortDescend (HT : TypingStrengthening env U) : SortDescend env U := by
  intro n k Γ Γ' e u W hΓ hΓ' h _
  have wf : VExpr.WF env U Γ (.forallE e (.sort .zero)) := HT W hΓ hΓ'
    (show env.HasType U _ ((VExpr.forallE e (.sort .zero)).liftN n k) _ from
      .forallEDF h (.sortDF trivial trivial rfl))
  have ⟨_, wf⟩ := wf
  exact (HasType.forallE_inv henv wf).1

variable! (henv : VEnv.WF env) in
theorem TypingStrengthening.piDescend (HT : TypingStrengthening env U) : PiDescend env U := by
  intro n k Γ Γ' f a A B W hΓ hΓ' hf ha _ _
  have wf : VExpr.WF env U Γ (.app f a) :=
    HT W hΓ hΓ' (show env.HasType U _ ((VExpr.app f a).liftN n k) _ from .appDF hf ha)
  exact wf.app_inv henv hΓ

/-! ## 2. The gate bodies that `TypingStrengthening` discharges **hole-free**

Six of the fourteen declarations `UniqueTyping.lean` states after its hole are re-proved here
from `TypingStrengthening`, each with **exactly** the statement `UniqueTyping.lean` gives it and
one extra hypothesis `HT`.  So when `PiDescend` becomes a theorem, each of those six bodies
becomes an application of the corresponding lemma below and nothing else changes -- in
particular no call site changes, because the statements are identical.

Why these six and not the other eight: the route used here is `SortDescend`, which
`TypingStrengthening.sortDescend` supplies with no hole in its cone, and it produces *a* sort
downstairs.  `IsType`, `OnCtx` and `VExpr.WF` leave the type (resp. the level) existential, so a
sort is all they need.  The three `HasType`-shaped gates demand the *given* type `A` downstairs,
which costs `TypingStrengthening.typed`'s ascription-redex trick and hence
`IsDefEqU.forallE_inv` -- a different hole.  The five conversion-shaped gates
(`IsDefEq.weakN_iff{,'}`, `IsDefEqU.weak'_iff`, `IsDefEq.weak'_iff`, `IsDefEq.skips`) have two
distinct endpoints and are not instances of `TypingStrengthening` at all.  See
`docs/handoff-gatebody.md` §3 for the measured table.

`Theory/Typing/WeakNProjGate.lean` §1 proves the first three of these below `UniqueTyping.lean`;
that file cannot be imported above it, so the proofs are repeated here.  Once this module is
imported by `UniqueTyping.lean`, `WeakNProjGate.onCtx_inv'` / `.isType_inv'` /
`.isType_weakN_iff'` can be re-exported from here instead (that file is not mine to edit). -/

namespace GateBody

/-- `OnCtx` of a suffix: at `k = 0` a `LiftN` only appends a block. -/
theorem onCtx_of_appendL {P : List VExpr → VExpr → Prop} :
    ∀ {As Γ : List VExpr}, OnCtx (As ++ Γ) P → OnCtx Γ P
  | [], _, h => h
  | _::_, _, h => onCtx_of_appendL h.1

variable! (henv : VEnv.WF env) in
/-- **`OnCtx.weakN_inv` and `IsType.weakN_iff`'s forward direction, together, from the typing
half -- with no hole in the cone.**  They are proved together because the `IsType` step needs
`OnCtx` of the smaller context, which the induction supplies. -/
theorem onCtx_isType_inv (HT : TypingStrengthening env U) :
    ∀ {n k : Nat} {Γ Γ' : List VExpr}, Ctx.LiftN n k Γ Γ' →
      OnCtx Γ' (env.IsType U) →
      OnCtx Γ (env.IsType U) ∧
        ∀ {A : VExpr}, env.IsType U Γ' (A.liftN n k) → env.IsType U Γ A := by
  intro n k Γ Γ' W
  induction W with
  | zero As h =>
    intro hΓ'
    refine ⟨onCtx_of_appendL hΓ', fun {A} ⟨u, hu⟩ => ?_⟩
    have hΓ := onCtx_of_appendL (P := fun Γ A => env.IsType U Γ A) hΓ'
    exact HT.sortDescend henv (.zero As h) hΓ hΓ' hu (HT (.zero As h) hΓ hΓ' hu)
  | @succ k Γ Γ' A W ih =>
    intro hΓ'
    have ⟨hΓ'0, hstep⟩ := ih hΓ'.1
    have hA : env.IsType U Γ A := hstep hΓ'.2
    refine ⟨⟨hΓ'0, hA⟩, fun {B} ⟨u, hu⟩ => ?_⟩
    exact HT.sortDescend henv W.succ ⟨hΓ'0, hA⟩ hΓ' hu (HT W.succ ⟨hΓ'0, hA⟩ hΓ' hu)

/-! ### The four `weakN` gates -/

variable! (henv : VEnv.WF env) in
/-- Body for `Lean4Lean.OnCtx.weakN_inv` (`UniqueTyping.lean:216`). -/
theorem onCtx_weakN_inv (HT : TypingStrengthening env U)
    (W : Ctx.LiftN n k Γ Γ') (H : OnCtx Γ' (env.IsType U)) : OnCtx Γ (env.IsType U) :=
  (onCtx_isType_inv henv HT W H).1

variable! (henv : VEnv.WF env) (hΓ' : OnCtx Γ' (env.IsType U)) in
/-- Body for `VEnv.IsType.weakN_iff` (`UniqueTyping.lean:239`). -/
theorem isType_weakN_iff (HT : TypingStrengthening env U) (W : Ctx.LiftN n k Γ Γ') :
    env.IsType U Γ' (A.liftN n k) ↔ env.IsType U Γ A :=
  ⟨(onCtx_isType_inv henv HT W hΓ').2, fun h => h.weakN henv W⟩

variable! (henv : VEnv.WF env) (hΓ : OnCtx Γ' (env.IsType U)) in
/-- Body for `Lean4Lean.VExpr.WF.weakN_iff` (`UniqueTyping.lean:195`).  This one is
`TypingStrengthening` almost verbatim: the statement leaves the type existential, which is
exactly what the hypothesis provides. -/
theorem wf_weakN_iff (HT : TypingStrengthening env U) (W : Ctx.LiftN n k Γ Γ') :
    VExpr.WF env U Γ' (e.liftN n k) ↔ VExpr.WF env U Γ e :=
  ⟨fun ⟨_, h⟩ => HT W (onCtx_weakN_inv henv HT W hΓ) hΓ h, fun h => h.weakN henv W⟩

/-! ### The three `weak'` gates, by the same `Lift.depth` induction the file already uses -/

variable! (henv : VEnv.WF env) in
/-- Body for `Lean4Lean.OnCtx.weak'_inv` (`UniqueTyping.lean:289`). -/
theorem onCtx_weak'_inv (HT : TypingStrengthening env U)
    (W : Ctx.Lift' ρ Γ Γ') (H : OnCtx Γ' (env.IsType U)) : OnCtx Γ (env.IsType U) := by
  generalize e : ρ.depth = n
  induction n generalizing ρ Γ' with
  | zero => simp [W.depth_zero e, H]
  | succ n ih =>
    obtain ⟨l, k, rfl, rfl⟩ := Lift.depth_succ e
    have ⟨Γ₁, W1, W2⟩ := W.of_cons_skip
    exact ih W1 (onCtx_weakN_inv henv HT W2 H) (by simp)

variable! (henv : VEnv.WF env) (hΓ' : OnCtx Γ' (env.IsType U)) in
/-- Body for `VEnv.IsType.weak'_iff` (`UniqueTyping.lean:280`). -/
theorem isType_weak'_iff (HT : TypingStrengthening env U) (W : Ctx.Lift' l Γ Γ') :
    env.IsType U Γ' (e.lift' l) ↔ env.IsType U Γ e := by
  generalize e : l.depth = n
  induction n generalizing l Γ' with
  | zero => simp [VExpr.lift'_depth_zero e, W.depth_zero e]
  | succ n ih =>
    obtain ⟨l, k, rfl, rfl⟩ := Lift.depth_succ e
    have ⟨Γ₁, W1, W2⟩ := W.of_cons_skip
    rw [Lift.consN_skip_eq, VExpr.lift'_comp,
      ← Lift.skipN_one, VExpr.lift'_consN_skipN,
      isType_weakN_iff henv hΓ' HT W2, ih (onCtx_weakN_inv henv HT W2 hΓ') W1 Lift.depth_consN]

variable! (henv : VEnv.WF env) (hΓ' : OnCtx Γ' (env.IsType U)) in
/-- Body for `Lean4Lean.VExpr.WF.weak'_iff` (`UniqueTyping.lean:285`). -/
theorem wf_weak'_iff (HT : TypingStrengthening env U) (W : Ctx.Lift' l Γ Γ') :
    VExpr.WF env U Γ' (e.lift' l) ↔ VExpr.WF env U Γ e := by
  generalize e : l.depth = n
  induction n generalizing l Γ' with
  | zero => simp [VExpr.lift'_depth_zero e, W.depth_zero e]
  | succ n ih =>
    obtain ⟨l, k, rfl, rfl⟩ := Lift.depth_succ e
    have ⟨Γ₁, W1, W2⟩ := W.of_cons_skip
    rw [Lift.consN_skip_eq, VExpr.lift'_comp,
      ← Lift.skipN_one, VExpr.lift'_consN_skipN,
      wf_weakN_iff henv hΓ' HT W2, ih (onCtx_weakN_inv henv HT W2 hΓ') W1 Lift.depth_consN]

end GateBody
