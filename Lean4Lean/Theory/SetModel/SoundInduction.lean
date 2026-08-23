import Lean4Lean.Theory.SetModel.InterpSound
import Lean4Lean.Theory.Typing.Strong

/-!
# Assembling the thirteen cases

`SetModel/InterpSound.lean` proves each rule's obligation as a standalone lemma.
This file runs the induction that ties them together.

## Two design decisions, both forced

**The induction is on `IsDefEqStrong`, not `IsDefEq`.**  Several cases need the
sort derivations for *intermediate* types — `appDF` needs `A::Γ ⊢ B : .sort v`
to know whether `B` is a proposition, which is the branch `interp` takes.  From
plain `IsDefEq.appDF` that is `forallE_inv`, one of the injectivity `sorry`s.
`IsDefEqStrong` carries it as a premise, and `IsDefEq.strong`
(`Theory/Typing/Strong.lean`, sorry-free) converts, needing only `Ordered env`
and a well-formed context.  So the assembly costs **no** injectivity beyond
`sort_inv`, which is spent on `LevelAssign` and nothing else.

**The universe bound is a threshold, not a property of the judgement.**  The
original `SoundBound` bounded the levels appearing in the *conclusion*.  That
does not work: in `appDF` the domain `A` does not occur in the conclusion at
all, so `f : A → B` with `A : Sort 100` and `B : Prop` has a conclusion whose
levels are all `≤ 1` and a subderivation that needs the 100th inaccessible.  No
bound on the conclusion can be inherited by the premises.

Nor can the bound be moved onto `L`: `L.lvl Γ (.sort k) = k+1` for every `k`, so
no single `n` bounds a fixed environment's assignment.

What is true is that a *derivation* mentions finitely many levels.  `SoundAbove`
says exactly that: there is a threshold `m`, produced by the induction from the
derivation, such that any chain of `m` inaccessibles validates the judgement.
The `∃` is over derivations and comes *before* the model is quantified, so this
is the schema form and not an `∃ k` about the model.
-/

namespace Lean4Lean.SetModel

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V]

section
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF env₀ : VEnv} {nv : ℕ} {M : ModelData V} {L : LevelAssign envF nv}

/-- A chain of `n` inaccessibles is a chain of `m` inaccessibles for `m ≤ n`.
This is what lets the induction take the maximum of its premises' thresholds. -/
theorem IsInaccessibleChain.le {m n : ℕ} {κ : ℕ → V} (h : m ≤ n)
    (H : IsInaccessibleChain n κ) : IsInaccessibleChain m κ where
  inaccessible i hi := H.inaccessible i (Nat.lt_of_lt_of_le hi h)
  mem i j hij hj := H.mem i j hij (Nat.lt_of_lt_of_le hj h)

/-- **Soundness above a threshold.**  There is an `m`, determined by the
derivation, such that any chain of `m` inaccessibles validates the judgement. -/
def SoundAbove (M : ModelData V) (L : LevelAssign envF nv)
    (Γ : List VExpr) (e₁ e₂ A : VExpr) : Prop :=
  Above M (Sound M L Γ e₁ e₂ A)

theorem SoundAbove.of_le {Γ : List VExpr} {e₁ e₂ A : VExpr} {m : ℕ}
    (h : IsInaccessibleChain m M.κ → Sound M L Γ e₁ e₂ A) : SoundAbove M L Γ e₁ e₂ A := ⟨m, h⟩

/-! ### The proof-splitting decisions, read off the judgement

`interp` branches on `L.IsProp`/`L.IsProof`, which are total functions of the
syntax.  On *well-typed* input they are pinned by `lvl_sound`/`srt_sound`, and
these two lemmas are how every case discharges its `hsplit` hypothesis. -/

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
/-- A type is a proposition exactly when its sort evaluates to `0`. -/
theorem isProp_iff (hle : env₀ ≤ envF) {Γ : List VExpr} {A : VExpr} {u : VLevel}
    (hA : env₀.HasType nv Γ A (.sort u)) (hw : u.WF nv) :
    L.IsProp M Γ A ↔ u.eval M.ls = 0 := by
  rw [LevelAssign.IsProp, VLevel.equiv_def.mp (L.lvl_sound hw (hA.mono hle)) M.ls]

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
/-- A term is a proof exactly when the sort of its type evaluates to `0`. -/
theorem isProof_iff (hle : env₀ ≤ envF) {Γ : List VExpr} {e A : VExpr} {u : VLevel}
    (he : env₀.HasType nv Γ e A) (hA : env₀.HasType nv Γ A (.sort u)) (hw : u.WF nv) :
    L.IsProof M Γ e ↔ u.eval M.ls = 0 := by
  rw [LevelAssign.IsProof, VLevel.equiv_def.mp (L.srt_sound (he.mono hle)) M.ls,
    VLevel.equiv_def.mp (L.lvl_sound hw (hA.mono hle)) M.ls]



omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
/-- `∀` lands in `Prop` exactly when its codomain does — the impredicative
clause, read off `Nat.imax`. -/
theorem imax_eq_zero_iff {a b : ℕ} : Lean.Nat.imax a b = 0 ↔ b = 0 := by
  unfold Lean.Nat.imax; split <;> rename_i h <;> simp [h]

/-- **The `forallE` rule, as a reusable step.**  Stated separately from the
induction because `appDF` needs it too: to know whether `f` is a proof it needs
soundness for `f`'s *type*, which is a `forallE` that no premise of `appDF`
mentions. -/
theorem sound_forallE (hle : env₀ ≤ envF) {R : List VExpr → List VExpr → Prop}
    (hR : CtxInvariant L R)
    (hRd : ∀ {Γ : List VExpr} {A A' : VExpr} {u : VLevel},
      env₀.IsDefEq nv Γ A A' (.sort u) → R (A' :: Γ) (A :: Γ))
    {m : ℕ} (hc : IsInaccessibleChain m M.κ)
    {Γ : List VExpr} {A A' body body' : VExpr} {u v : VLevel} (hwv : v.WF nv)
    (hbu : u.eval M.ls ≤ m) (hbv : v.eval M.ls ≤ m)
    (h3 : env₀.IsDefEq nv Γ A A' (.sort u))
    (h4 : env₀.IsDefEq nv (A :: Γ) body body' (.sort v))
    (h5 : env₀.IsDefEq nv (A' :: Γ) body body' (.sort v))
    (sA : Sound M L Γ A A' (.sort u))
    (sb : Sound M L (A :: Γ) body body' (.sort v)) :
    Sound M L Γ (.forallE A body) (.forallE A' body') (.sort (.imax u v)) := by
  have hctx : interp M L (A' :: Γ) body' = interp M L (A :: Γ) body' :=
    interp_ctxInvariant M L hR body' (hRd h3)
  have hpB : L.IsProp M (A :: Γ) body ↔ v.eval M.ls = 0 := isProp_iff hle (h4.trans h4.symm) hwv
  have hpB' : L.IsProp M (A' :: Γ) body' ↔ v.eval M.ls = 0 := isProp_iff hle (h5.symm.trans h5) hwv
  refine ⟨fun ρ hρ ↦ forallEDF_sound_eq M L hctx (hpB.trans hpB'.symm) (sA.eq ρ hρ)
    (fun w hw ↦ sb.eq (snoc ρ w) ((mem_interpCtx_cons M L).mpr ⟨ρ, hρ, w, hw, rfl⟩)),
    fun ρ hρ ↦ ?_⟩
  rw [interp_sort]
  by_cases hp : L.IsProp M (A :: Γ) body
  · have h0 : (VLevel.imax u v).eval M.ls = 0 := imax_eq_zero_iff.mpr (hpB.mp hp)
    rw [h0, U_zero]
    exact forallEDF_sound_prop M L hp ρ
  · have hv0 : v.eval M.ls ≠ 0 := fun h ↦ hp (hpB.mpr h)
    have hmax : (VLevel.imax u v).eval M.ls = max (u.eval M.ls) (v.eval M.ls) := if_neg hv0
    have hpos : 1 ≤ max (u.eval M.ls) (v.eval M.ls) := by omega
    have hi1 : max (u.eval M.ls) (v.eval M.ls) - 1 + 1 = max (u.eval M.ls) (v.eval M.ls) := by
      omega
    rw [hmax, ← hi1]
    refine forallEDF_sound_type M L hc (i := _) (by omega) hp ?_ ?_
    · have h := sA.type ρ hρ
      rw [interp_sort] at h
      exact U_mono hc (by omega) (by omega) _ h
    · intro w hw
      have h := sb.type (snoc ρ w) ((mem_interpCtx_cons M L).mpr ⟨ρ, hρ, w, hw, rfl⟩)
      rw [interp_sort] at h
      exact U_mono hc (by omega) (by omega) _ h

/-! ## The induction -/

section Induction

variable (hle : env₀ ≤ envF) (henv : env₀.Ordered) (hS : L.Stable)
  (hC : CoherentOn M L env₀)
variable {R : List VExpr → List VExpr → Prop} (hR : CtxInvariant L R)
variable (hRd : ∀ {Γ : List VExpr} {A A' : VExpr} {u : VLevel},
  env₀.IsDefEq nv Γ A A' (.sort u) → R (A' :: Γ) (A :: Γ))

include hle henv hS hC hR hRd in
/-- **Soundness.**  Every derivation is validated by every chain of
inaccessibles long enough for it. -/
theorem soundAbove : ∀ {Γ : List VExpr} {e₁ e₂ A : VExpr},
    env₀.IsDefEqStrong nv Γ e₁ e₂ A → CtxClosed Γ → SoundAbove M L Γ e₁ e₂ A := by
  intro Γ e₁ e₂ A H
  induction H with
  | @bvar Γ i A u h1 _ _ _ =>
    exact fun hΓ ↦ ⟨0, fun _ ↦ ⟨fun _ _ ↦ rfl, fun ρ hρ ↦ bvar_sound M L hS hΓ h1 hρ⟩⟩
  | symm _ ih =>
    exact fun hΓ ↦ let ⟨m, hm⟩ := ih hΓ; ⟨m, fun hc ↦ (hm hc).symm⟩
  | trans _ _ ih1 ih2 =>
    refine fun hΓ ↦ ?_
    obtain ⟨m₁, k₁⟩ := ih1 hΓ
    obtain ⟨m₂, k₂⟩ := ih2 hΓ
    refine ⟨max m₁ m₂, fun hc ↦ ?_⟩
    have s₁ := k₁ (hc.le (Nat.le_max_left _ _))
    have s₂ := k₂ (hc.le (Nat.le_max_right _ _))
    exact ⟨fun ρ hρ ↦ (s₁.eq ρ hρ).trans (s₂.eq ρ hρ), s₁.type⟩
  | @sortDF l l' Γ _ _ h3 =>
    exact fun _ ↦ ⟨l.eval M.ls + 1, fun hc ↦
      ⟨fun ρ _ ↦ (sortDF_sound M L hc rfl h3 (Nat.lt_succ_self _) ρ).1,
       fun ρ _ ↦ (sortDF_sound M L hc rfl h3 (Nat.lt_succ_self _) ρ).2⟩⟩
  | @constDF c ci ls ls' u Γ h1 h2 h3 h4 h5 _ _ _ _ _ =>
    refine fun _ ↦ ?_
    obtain ⟨m₁, k₁⟩ := hC.const_congr (c := c) h2 h3 h5
    obtain ⟨m₂, k₂⟩ := hC.const_type h1 h2 h4
    exact ⟨max m₁ m₂, fun hc ↦
      ⟨fun ρ _ ↦ constDF_sound_eq M L (k₁ (hc.le (Nat.le_max_left _ _))) Γ ρ,
       fun ρ hρ ↦ constDF_sound_type M L henv hS h1 (k₂ (hc.le (Nat.le_max_right _ _))) hρ⟩⟩
  | @defeqDF Γ A B u e1 e2 _ _ _ ih2 ih3 =>
    refine fun hΓ ↦ ?_
    obtain ⟨m₁, k₁⟩ := ih2 hΓ
    obtain ⟨m₂, k₂⟩ := ih3 hΓ
    refine ⟨max m₁ m₂, fun hc ↦ ?_⟩
    have s₁ := k₁ (hc.le (Nat.le_max_left _ _))
    have s₂ := k₂ (hc.le (Nat.le_max_right _ _))
    exact ⟨s₂.eq, fun ρ hρ ↦ defeqDF_sound M L (s₁.eq ρ hρ) (s₂.type ρ hρ)⟩
  | @proofIrrel Γ p h h' _ _ _ ih1 ih2 ih3 =>
    refine fun hΓ ↦ ?_
    obtain ⟨m₁, k₁⟩ := ih1 hΓ
    obtain ⟨m₂, k₂⟩ := ih2 hΓ
    obtain ⟨m₃, k₃⟩ := ih3 hΓ
    refine ⟨max m₁ (max m₂ m₃), fun hc ↦ ?_⟩
    have s₁ := k₁ (hc.le (Nat.le_max_left _ _))
    have s₂ := k₂ (hc.le ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _)))
    have s₃ := k₃ (hc.le ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _)))
    exact ⟨fun ρ hρ ↦ proofIrrel_sound M L (s₁.type ρ hρ) (s₂.type ρ hρ) (s₃.type ρ hρ),
      s₂.type⟩
  | @extra df ls u Γ h1 h2 h3 _ _ _ _ _ _ _ _ _ _ _ =>
    refine fun _ ↦ ?_
    obtain ⟨m₁, k₁⟩ := hC.defeq h1 h2 h3
    obtain ⟨m₂, k₂⟩ := hC.defeq_type h1 h2 h3
    exact ⟨max m₁ m₂, fun hc ↦
      ⟨fun ρ hρ ↦ extra_sound_eq M L henv hS h1 (k₁ (hc.le (Nat.le_max_left _ _))) hρ,
       fun ρ hρ ↦ extra_sound_type M L henv hS h1 (k₂ (hc.le (Nat.le_max_right _ _))) hρ⟩⟩
  | @appDF Γ A u B v f f' a a' h1 h2 h3 h4 h5 h6 h7 ihA ihB ihf iha ihBi =>
    refine fun hΓ ↦ ?_
    have hclA : A.ClosedN Γ.length := h3.defeq.closedN henv hΓ
    have hΓA : CtxClosed (A :: Γ) := ⟨hΓ, hclA⟩
    have hclB : B.ClosedN (Γ.length + 1) := h4.defeq.closedN henv hΓA
    have hcla : a.ClosedN Γ.length := h6.defeq.closedN henv hΓ
    obtain ⟨m₁, k₁⟩ := ihA hΓ
    obtain ⟨m₂, k₂⟩ := ihB hΓA
    obtain ⟨m₃, k₃⟩ := ihf hΓ
    obtain ⟨m₄, k₄⟩ := iha hΓ
    refine ⟨max (max m₁ m₂) (max (max m₃ m₄) (max (u.eval M.ls) (v.eval M.ls))), fun hc ↦ ?_⟩
    have sA := k₁ (hc.le (by omega))
    have sB := k₂ (hc.le (by omega))
    have sf := k₃ (hc.le (by omega))
    have sa := k₄ (hc.le (by omega))
    have hFA : env₀.IsDefEqStrong nv Γ (.forallE A B) (.forallE A B) (.sort (.imax u v)) :=
      .forallEDF h1 h2 h3 h4 h4
    have sFA := sound_forallE hle hR hRd hc h2 (by omega) (by omega) h3.defeq h4.defeq h4.defeq sA sB
    have hpf : L.IsProof M Γ f ↔ (VLevel.imax u v).eval M.ls = 0 :=
      isProof_iff hle (h5.trans h5.symm).defeq hFA.defeq ⟨h1, h2⟩
    have hsp : L.IsProof M Γ f ↔ L.IsProp M (A :: Γ) B := by
      rw [hpf, isProp_iff hle (h4.trans h4.symm).defeq h2]; exact imax_eq_zero_iff
    refine ⟨fun ρ hρ ↦ appDF_sound_eq M L ?_ (sf.eq ρ hρ) (sa.eq ρ hρ), fun ρ hρ ↦ ?_⟩
    · show _ ↔ _
      unfold LevelAssign.IsProof
      rw [VLevel.equiv_def.mp (L.srt_congr (h5.defeq.mono hle)) M.ls]
    · exact appDF_sound_type M L hS ((h6.trans h6.symm).defeq.mono hle) hclB hcla hρ (sf.type ρ hρ) (sa.type ρ hρ)
        (fun hp ↦ Sound.proof M L sFA (hpf.mp hp) sf ρ hρ) hsp
  | @lamDF Γ A A' u B v body body' h1 h2 h3 h4 h5 h6 h7 ihA ihB ihB' ihb ihb' =>
    refine fun hΓ ↦ ?_
    have hclA : A.ClosedN Γ.length := h3.defeq.closedN henv hΓ
    have hΓA : CtxClosed (A :: Γ) := ⟨hΓ, hclA⟩
    obtain ⟨m₁, k₁⟩ := ihA hΓ
    obtain ⟨m₂, k₂⟩ := ihB hΓA
    obtain ⟨m₃, k₃⟩ := ihb hΓA
    refine ⟨max m₁ (max m₂ m₃), fun hc ↦ ?_⟩
    have sA := k₁ (hc.le (by omega))
    have sB := k₂ (hc.le (by omega))
    have sb := k₃ (hc.le (by omega))
    have hpb : L.IsProof M (A :: Γ) body ↔ v.eval M.ls = 0 :=
      isProof_iff hle (h6.trans h6.symm).defeq h4.defeq h2
    have hpb' : L.IsProof M (A' :: Γ) body' ↔ v.eval M.ls = 0 :=
      isProof_iff hle (h7.symm.trans h7).defeq h5.defeq h2
    have hpB : L.IsProp M (A :: Γ) B ↔ v.eval M.ls = 0 := isProp_iff hle h4.defeq h2
    refine ⟨fun ρ hρ ↦ lamDF_sound_eq M L
        (interp_ctxInvariant M L hR body' (hRd h3.defeq)) (hpb.trans hpb'.symm) (sA.eq ρ hρ)
        (fun w hw ↦ sb.eq (snoc ρ w) ((mem_interpCtx_cons M L).mpr ⟨ρ, hρ, w, hw, rfl⟩)),
      fun ρ hρ ↦ lamDF_sound_type M L (hpb.trans hpB.symm)
        (fun w hw ↦ sb.type (snoc ρ w) ((mem_interpCtx_cons M L).mpr ⟨ρ, hρ, w, hw, rfl⟩))
        (fun hp w hw ↦ Sound.proof M L sB (hpb.mp hp) sb (snoc ρ w)
          ((mem_interpCtx_cons M L).mpr ⟨ρ, hρ, w, hw, rfl⟩))⟩
  | @forallEDF Γ A A' u body body' v h1 h2 h3 h4 h5 ihA ihb ihb' =>
    refine fun hΓ ↦ ?_
    have hclA : A.ClosedN Γ.length := h3.defeq.closedN henv hΓ
    obtain ⟨m₁, k₁⟩ := ihA hΓ
    obtain ⟨m₂, k₂⟩ := ihb ⟨hΓ, hclA⟩
    refine ⟨max (max m₁ m₂) (max (u.eval M.ls) (v.eval M.ls)), fun hc ↦ ?_⟩
    exact sound_forallE hle hR hRd hc h2 (by omega) (by omega) h3.defeq h4.defeq h5.defeq
      (k₁ (hc.le (by omega))) (k₂ (hc.le (by omega)))
  | @beta Γ A u B v e e' h1 h2 h3 h4 h5 h6 h7 h8 ihA ihB ihe ihe' ihBi ihei =>
    refine fun hΓ ↦ ?_
    have hclA : A.ClosedN Γ.length := h3.defeq.closedN henv hΓ
    have hΓA : CtxClosed (A :: Γ) := ⟨hΓ, hclA⟩
    obtain ⟨m₂, k₂⟩ := ihB hΓA
    obtain ⟨m₃, k₃⟩ := ihe hΓA
    obtain ⟨m₄, k₄⟩ := ihe' hΓ
    obtain ⟨m₆, k₆⟩ := ihei hΓ
    refine ⟨max (max m₂ m₃) (max m₄ m₆), fun hc ↦ ?_⟩
    have sB := k₂ (hc.le (by omega))
    have se := k₃ (hc.le (by omega))
    have se' := k₄ (hc.le (by omega))
    have sei := k₆ (hc.le (by omega))
    have hpe : L.IsProof M (A :: Γ) e ↔ v.eval M.ls = 0 :=
      isProof_iff hle (h5.trans h5.symm).defeq h4.defeq h2
    have hFA : env₀.IsDefEqStrong nv Γ (.forallE A B) (.forallE A B) (.sort (.imax u v)) :=
      .forallEDF h1 h2 h3 h4 h4
    have hlam : env₀.IsDefEqStrong nv Γ (.lam A e) (.lam A e) (.forallE A B) :=
      .lamDF h1 h2 h3 h4 h4 h5 h5
    have hsplit : L.IsProof M Γ (.lam A e) ↔ L.IsProof M (A :: Γ) e := by
      rw [isProof_iff hle hlam.defeq hFA.defeq ⟨h1, h2⟩, hpe]; exact imax_eq_zero_iff
    have heq : EqSound M L Γ (.app (.lam A e) e') (e.inst e') := fun ρ hρ ↦
      beta_sound M L hS (h6.defeq.mono hle) (h5.defeq.closedN henv hΓA)
        (h6.defeq.closedN henv hΓ)
        se'.type
        (fun hp ρ' hρ' ↦ Sound.proof M L sB (hpe.mp hp) se ρ' hρ')
        hsplit hρ
    exact ⟨heq, fun ρ hρ ↦ (heq ρ hρ) ▸ sei.type ρ hρ⟩
  | @eta Γ A u B v e h1 h2 h3 h4 h5 h6 h7 h8 ihA ihB ihBl ihe ihel ihAl =>
    refine fun hΓ ↦ ?_
    have hclA : A.ClosedN Γ.length := h3.defeq.closedN henv hΓ
    have hΓA : CtxClosed (A :: Γ) := ⟨hΓ, hclA⟩
    obtain ⟨m₁, k₁⟩ := ihA hΓ
    obtain ⟨m₂, k₂⟩ := ihB hΓA
    obtain ⟨m₄, k₄⟩ := ihe hΓ
    refine ⟨max (max m₁ m₂) (max m₄ (max (u.eval M.ls) (v.eval M.ls))), fun hc ↦ ?_⟩
    have sA := k₁ (hc.le (by omega))
    have sB := k₂ (hc.le (by omega))
    have se := k₄ (hc.le (by omega))
    have sFA := sound_forallE hle hR hRd hc h2 (by omega) (by omega) h3.defeq h4.defeq h4.defeq sA sB
    have hFA : env₀.IsDefEqStrong nv Γ (.forallE A B) (.forallE A B) (.sort (.imax u v)) :=
      .forallEDF h1 h2 h3 h4 h4
    have hFAl : env₀.IsDefEqStrong nv (A :: Γ) (.forallE A.lift (B.liftN 1 1))
        (.forallE A.lift (B.liftN 1 1)) (.sort (.imax u v)) := .forallEDF h1 h2 h8 h5 h5
    have hpe : L.IsProof M Γ e ↔ (VLevel.imax u v).eval M.ls = 0 :=
      isProof_iff hle h6.defeq hFA.defeq ⟨h1, h2⟩
    have hpev : L.IsProof M Γ e ↔ v.eval M.ls = 0 := hpe.trans imax_eq_zero_iff
    have hbv : env₀.IsDefEqStrong nv (A :: Γ) (.bvar 0) (.bvar 0) A.lift := .bvar .zero h1 h8
    have happ : env₀.IsDefEqStrong nv (A :: Γ)
        (.app e.lift (.bvar 0)) (.app e.lift (.bvar 0)) B := by
      have c : env₀.IsDefEqStrong nv (A :: Γ) _ _ _ :=
        .appDF h1 h2 h8 h5 h7 hbv (by rw [VExpr.instN_bvar0]; exact h4)
      rwa [VExpr.instN_bvar0] at c
    have hsplit₂ : L.IsProof M (A :: Γ) (.app e.lift (.bvar 0)) ↔ L.IsProof M Γ e := by
      rw [isProof_iff hle happ.defeq h4.defeq h2, hpev]
    have hsplit₃ : ¬ L.IsProof M Γ e → ¬ L.IsProp M (A :: Γ) B := by
      rw [hpev, isProp_iff hle h4.defeq h2]; exact id
    have hsplit₄ : L.IsProof M (A :: Γ) e.lift ↔ L.IsProof M Γ e := by
      rw [isProof_iff hle h7.defeq hFAl.defeq ⟨h1, h2⟩, hpe]
    have heq : EqSound M L Γ (.lam A (.app e.lift (.bvar 0))) e := fun ρ hρ ↦
      eta_sound M L hS (h6.defeq.closedN henv hΓ) se.type
        (fun hp ρ' hρ' ↦ Sound.proof M L sFA (hpe.mp hp) se ρ' hρ')
        hsplit₂ hsplit₃ hsplit₄ hρ
    exact ⟨heq, fun ρ hρ ↦ (heq ρ hρ) ▸ se.type ρ hρ⟩

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
theorem ctxClosed_of_isType (henv : env₀.Ordered) :
    ∀ {Γ : List VExpr}, OnCtx Γ (env₀.IsType nv) → CtxClosed Γ
  | [], _ => trivial
  | _ :: _, ⟨h1, _, h2⟩ =>
    have hΓ := ctxClosed_of_isType henv h1
    ⟨hΓ, h2.closedN henv hΓ⟩

include hle henv hS hC hR hRd in
/-- **Soundness, from the ordinary judgement.**  `IsDefEq.strong` supplies the
sort derivations the induction needs; it is sorry-free, so this costs no
injectivity beyond the `sort_inv` already spent on `LevelAssign`. -/
theorem sound {Γ : List VExpr} {e₁ e₂ A : VExpr} (hΓ : OnCtx Γ (env₀.IsType nv))
    (H : env₀.IsDefEq nv Γ e₁ e₂ A) : SoundAbove M L Γ e₁ e₂ A :=
  soundAbove hle henv hS hC hR hRd (H.strong henv hΓ) (ctxClosed_of_isType henv hΓ)

include hle henv hS hC hR hRd in
/-- The form the coherence induction consumes: a closed judgement, at the empty
context, where `ModelData.Coherent` is stated. -/
theorem sound_nil {e₁ e₂ A : VExpr} (H : env₀.IsDefEq nv [] e₁ e₂ A) :
    ∃ m : ℕ, IsInaccessibleChain m M.κ →
      (interp M L [] e₁).toFun ∅ = (interp M L [] e₂).toFun ∅ ∧
      (interp M L [] e₁).toFun ∅ ∈ (interp M L [] A).toFun ∅ := by
  obtain ⟨m, k⟩ := sound hle henv hS hC hR hRd (Γ := []) trivial H
  refine ⟨m, fun hc ↦ ?_⟩
  have hnil : (∅ : V) ∈ interpCtx M L ([] : List VExpr) := by
    rw [interpCtx_nil]; exact mem_singleton_iff.2 rfl
  exact ⟨(k hc).eq ∅ hnil, (k hc).type ∅ hnil⟩

include hle henv hS hC hR hRd in
/-- **Defeq-invariance of the interpretation** — `interp_congr`, the obligation
`docs/model-interface.md` §4 names as the *first* thing the inductive bridge
needs, and which it lists as unproved and owed by the syntax side.

It is not a new theorem. It is `Sound.eq` with the `Sound.type` half dropped:
the soundness induction already proves that definitionally equal terms denote
equal values at every valuation of the context, and `interp_congr` is exactly
that projection.

Two things to notice before planning around it.

* **It is `Above`-wrapped**, because soundness is. So what is available is
  "there is a threshold `m` such that any chain of `m` inaccessibles makes the
  two denotations agree", not an unconditional equality of `DefFun`s. That is
  enough to *prove* things about a construction, and not enough to *define* one
  by rewriting `⟦F.type⟧` to `⟦A⟧` — which is how `model-interface.md` §2 phrases
  the first step of `interpSig`.
* **It holds for arbitrary `B`, not just for `.sort u`** — the bridge needs it
  only at types, but nothing about the proof is specific to them. -/
theorem interp_congr {Γ : List VExpr} {e₁ e₂ B : VExpr}
    (hΓ : OnCtx Γ (env₀.IsType nv)) (H : env₀.IsDefEq nv Γ e₁ e₂ B) :
    Above M (EqSound M L Γ e₁ e₂) :=
  (sound hle henv hS hC hR hRd hΓ H).imp Sound.eq

end Induction

end

end Lean4Lean.SetModel
