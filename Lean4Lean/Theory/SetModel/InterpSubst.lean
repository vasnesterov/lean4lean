import Lean4Lean.Theory.SetModel.Interp
import Lean4Lean.Theory.Typing.Lemmas

/-!
# Weakening and substitution for the interpretation

Stage 2 of `SetModel/Interp.lean`.  Carneiro `soundness.tex:206-214`.

## What the interpretation actually uses a valuation for

Exactly one thing: `⟦Γ ⊢ bvar i⟧ ρ = ρ ‘ (|Γ| - 1 - i)`.  Every other clause
passes the valuation through unchanged or extends it with `snoc`.  So both
weakening and substitution reduce to an agreement condition on *positions*, and
that is what `LiftVal` and `InstVal` below say.

The context enters the interpretation in only two ways — `Γ.length`, and the
three proof-splitting decisions — so weakening and substitution for `interp`
need exactly two things: the position arithmetic, and stability of the level
assignment.  The latter is not derivable from `lvl_sound` alone (which
constrains the assignment only on well-typed input), so it is added to
`LevelAssign` as four further fields.  Any assignment built the natural way — by
a syntactic recursion mirroring `inferType` — satisfies them automatically.
-/

namespace Lean4Lean.SetModel

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LO.FirstOrder.SetTheory.Ordinal (lt_def le_def lt_succ)

variable {V : Type*} [SetStructure V] [Nonempty V]

/-! ## Numerals -/

section Numerals

variable [V↓[ℒₛₑₜ] ⊧* 𝗭]

theorem ofNat_mem_ofNat : ∀ {a b : ℕ}, a < b → ((a : ℕ) : V) ∈ ((b : ℕ) : V)
  | a, 0, h => absurd h (by omega)
  | a, b + 1, h => by
    rw [num_succ_def, mem_succ_iff]
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h' | rfl
    · exact Or.inr (ofNat_mem_ofNat h')
    · exact Or.inl rfl

theorem ofNat_ne_ofNat {a b : ℕ} (h : a ≠ b) : ((a : ℕ) : V) ≠ ((b : ℕ) : V) := by
  rcases Nat.lt_or_ge a b with hab | hab
  · exact ne_of_mem (ofNat_mem_ofNat hab)
  · have hba : b < a := by omega
    exact (ne_of_mem (ofNat_mem_ofNat (V := V) hba)).symm

end Numerals

/-! ## Valuations are internal sequences -/

section Valuation

variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {env : VEnv} {nv : ℕ} (M : ModelData V) (L : LevelAssign env nv)

/-- A valuation of `Γ` is an internal function whose domain is `|Γ|`. -/
theorem interpCtx_domain : ∀ {Γ : List VExpr} {ρ : V}, ρ ∈ interpCtx M L Γ →
    IsFunction ρ ∧ domain ρ = ((Γ.length : ℕ) : V)
  | [], ρ, h => by
    rw [interpCtx_nil] at h
    rcases mem_singleton_iff.mp h with rfl
    exact ⟨IsFunction.empty, by simp [zero_def]⟩
  | A :: Γ, ρ, h => by
    obtain ⟨ρ₀, hρ₀, v, -, rfl⟩ := (mem_interpCtx_cons M L).mp h
    obtain ⟨hfun, hdom⟩ := interpCtx_domain hρ₀
    have hni : domain ρ₀ ∉ domain ρ₀ := mem_irrefl _
    refine ⟨IsFunction.insert ρ₀ _ v hni, ?_⟩
    rw [snoc, domain_insert, hdom]
    simp [num_succ_def, succ]

lemma snoc_value_lt {ρ v p : V} (hfun : IsFunction ρ) (hp : p ∈ domain ρ) :
    (snoc ρ v) ‘ p = ρ ‘ p := by
  have hmem : (⟨p, ρ ‘ p⟩ₖ : V) ∈ ρ := kpair_value_mem (IsFunction.mem_function ρ) hp
  have hni : domain ρ ∉ domain ρ := mem_irrefl _
  have : IsFunction (snoc ρ v) := IsFunction.insert ρ _ v hni
  exact value_eq_of_kpair_mem (mem_snoc_iff.mpr (Or.inr hmem))

lemma snoc_value_top {ρ v : V} (hfun : IsFunction ρ) : (snoc ρ v) ‘ (domain ρ) = v := by
  have hni : domain ρ ∉ domain ρ := mem_irrefl _
  have : IsFunction (snoc ρ v) := IsFunction.insert ρ _ v hni
  exact value_eq_of_kpair_mem (mem_snoc_iff.mpr (Or.inl rfl))

/-- The value of a valuation of `A :: Γ` at a position below `|Γ|` is the value
of its restriction. -/
lemma snoc_value_of_lt {Γ : List VExpr} {ρ v : V} (hρ : ρ ∈ interpCtx M L Γ)
    {j : ℕ} (hj : j < Γ.length) : (snoc ρ v) ‘ ((j : ℕ) : V) = ρ ‘ ((j : ℕ) : V) := by
  obtain ⟨hfun, hdom⟩ := interpCtx_domain M L hρ
  exact snoc_value_lt hfun (by rw [hdom]; exact ofNat_mem_ofNat hj)

lemma snoc_value_at_len {Γ : List VExpr} {ρ v : V} (hρ : ρ ∈ interpCtx M L Γ) :
    (snoc ρ v) ‘ ((Γ.length : ℕ) : V) = v := by
  obtain ⟨hfun, hdom⟩ := interpCtx_domain M L hρ
  rw [← hdom]; exact snoc_value_top hfun

end Valuation

/-! ## Stability of the level assignment

`LevelAssign.lvl_sound` constrains the assignment only on *well-typed* input, so
it does not by itself give stability under lifting and instantiation.  These
four facts are therefore added separately.  They are not extra mathematical
content: an assignment built the natural way — a syntactic recursion mirroring
`inferType` — satisfies them by construction, and for well-typed input they
follow from `sort_inv` together with `IsDefEq.weakN` / `IsDefEq.instN`.
-/

section Stable

variable {env : VEnv} {nv : ℕ}

/-- The level assignment commutes with weakening and substitution. -/
structure LevelAssign.Stable (L : LevelAssign env nv) : Prop where
  lvl_liftN : ∀ {n k : ℕ} {Γ Γ' : List VExpr}, Ctx.LiftN n k Γ Γ' → ∀ A : VExpr,
    L.lvl Γ' (A.liftN n k) ≈ L.lvl Γ A
  srt_liftN : ∀ {n k : ℕ} {Γ Γ' : List VExpr}, Ctx.LiftN n k Γ Γ' → ∀ e : VExpr,
    L.srt Γ' (e.liftN n k) ≈ L.srt Γ e
  lvl_instN : ∀ {Γ₀ : List VExpr} {e₀ A₀ : VExpr} {k : ℕ} {Γ₁ Γ : List VExpr},
    Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ → ∀ B : VExpr, L.lvl Γ (B.inst e₀ k) ≈ L.lvl Γ₁ B
  srt_instN : ∀ {Γ₀ : List VExpr} {e₀ A₀ : VExpr} {k : ℕ} {Γ₁ Γ : List VExpr},
    Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ → ∀ e : VExpr, L.srt Γ (e.inst e₀ k) ≈ L.srt Γ₁ e

theorem Ctx.LiftN.length : ∀ {n k : ℕ} {Γ Γ' : List VExpr},
    Ctx.LiftN n k Γ Γ' → Γ'.length = Γ.length + n
  | _, _, _, _, .zero As h => by simp [h]; omega
  | _, _, _, _, .succ W => by simp [Ctx.LiftN.length W]; omega

theorem Ctx.LiftN.le : ∀ {n k : ℕ} {Γ Γ' : List VExpr},
    Ctx.LiftN n k Γ Γ' → k ≤ Γ.length
  | _, _, _, _, .zero .. => Nat.zero_le _
  | _, _, _, _, .succ W => by simpa using Nat.succ_le_succ (Ctx.LiftN.le W)

theorem Ctx.InstN.length : ∀ {Γ₀ : List VExpr} {e₀ A₀ : VExpr} {k : ℕ} {Γ₁ Γ : List VExpr},
    Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ → Γ₁.length = Γ.length + 1
  | _, _, _, _, _, _, .zero => by simp
  | _, _, _, _, _, _, .succ W => by simp [Ctx.InstN.length W]

theorem Ctx.InstN.le : ∀ {Γ₀ : List VExpr} {e₀ A₀ : VExpr} {k : ℕ} {Γ₁ Γ : List VExpr},
    Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ → k ≤ Γ.length
  | _, _, _, _, _, _, .zero => Nat.zero_le _
  | _, _, _, _, _, _, .succ W => by simpa using Nat.succ_le_succ (Ctx.InstN.le W)

end Stable

/-! ## Weakening -/

section Weakening

variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {env : VEnv} {nv : ℕ} (M : ModelData V) (L : LevelAssign env nv)

/-- Reindexing of valuation positions when `n` slots are inserted at position
`j`.  Positions are counted from the *outside*, so `j` is invariant as the
recursion goes under a binder — which is what makes the induction go through
without any further arithmetic. -/
def liftPos (n j p : ℕ) : ℕ := if p < j then p else p + n

/-- `ρ'` extends `ρ` along the insertion of `n` slots at position `j`. -/
def AgreePos (n j m : ℕ) (ρ' ρ : V) : Prop :=
  ∀ p, p < m → ρ' ‘ ((liftPos n j p : ℕ) : V) = ρ ‘ ((p : ℕ) : V)

/-- Going under a binder preserves agreement: both valuations gain the same new
value, at the top of their respective ranges. -/
lemma AgreePos.snoc {n j m : ℕ} {ρ' ρ : V} (hj : j ≤ m)
    {Γ Γ' : List VExpr} (hΓ : Γ.length = m) (hΓ' : Γ'.length = m + n)
    (hρ : ρ ∈ interpCtx M L Γ) (hρ' : ρ' ∈ interpCtx M L Γ')
    (h : AgreePos n j m ρ' ρ) (v : V) :
    AgreePos n j (m + 1) (snoc ρ' v) (snoc ρ v) := by
  intro p hp
  rcases Nat.lt_succ_iff_lt_or_eq.mp hp with hp' | rfl
  · have h1 : liftPos n j p < m + n := by
      simp only [liftPos]; split <;> omega
    rw [snoc_value_of_lt M L hρ' (by omega : liftPos n j p < Γ'.length),
      snoc_value_of_lt M L hρ (by omega : p < Γ.length)]
    exact h p hp'
  · have hpj : ¬ p < j := by omega
    have : liftPos n j p = p + n := by simp [liftPos, hpj]
    rw [this]
    rw [show ((p + n : ℕ) : V) = ((Γ'.length : ℕ) : V) by rw [hΓ'],
      show ((p : ℕ) : V) = ((Γ.length : ℕ) : V) by rw [hΓ]]
    rw [snoc_value_at_len M L hρ', snoc_value_at_len M L hρ]

/-- **Weakening.**  The interpretation is invariant under inserting unused
context slots.  The only clause that touches the valuation is `bvar`, so the
position arithmetic appears exactly once. -/
theorem interp_liftN (hS : L.Stable) {n j : ℕ} :
    ∀ (e : VExpr) {k : ℕ} {Γ Γ' : List VExpr}, Ctx.LiftN n k Γ Γ' → Γ.length - k = j →
      e.ClosedN Γ.length → ∀ {ρ ρ' : V}, ρ ∈ interpCtx M L Γ → ρ' ∈ interpCtx M L Γ' →
      AgreePos n j Γ.length ρ' ρ →
      (interp M L Γ' (e.liftN n k)).toFun ρ' = (interp M L Γ e).toFun ρ
  | .bvar i, k, Γ, Γ', W, hj, hcl, ρ, ρ', hρ, hρ', hag => by
    have hlen := Ctx.LiftN.length W
    have hkle := Ctx.LiftN.le W
    have hi : i < Γ.length := hcl
    rw [show (VExpr.bvar i).liftN n k = .bvar (liftVar n i k) from rfl,
      interp_bvar, interp_bvar]
    have hpos : Γ'.length - 1 - liftVar n i k = liftPos n j (Γ.length - 1 - i) := by
      simp only [liftPos, liftVar, hlen, ← hj]
      split <;> split <;> omega
    rw [hpos]
    exact hag _ (by omega)
  | .sort u, k, Γ, Γ', W, hj, hcl, ρ, ρ', hρ, hρ', hag => by
    rw [show (VExpr.sort u).liftN n k = .sort u from rfl, interp_sort, interp_sort]
  | .const c us, k, Γ, Γ', W, hj, hcl, ρ, ρ', hρ, hρ', hag => by
    rw [show (VExpr.const c us).liftN n k = .const c us from rfl, interp_const, interp_const]
  | .app f a, k, Γ, Γ', W, hj, hcl, ρ, ρ', hρ, hρ', hag => by
    obtain ⟨hf, ha⟩ := hcl
    have hsplit : L.IsProof M Γ' (f.liftN n k) ↔ L.IsProof M Γ f := by
      simp only [LevelAssign.IsProof, VLevel.equiv_def.mp (hS.srt_liftN W f) M.ls]
    by_cases hp : L.IsProof M Γ f
    · rw [show (VExpr.app f a).liftN n k = .app (f.liftN n k) (a.liftN n k) from rfl,
        interp_app_proof M L (hsplit.mpr hp), interp_app_proof M L hp]
    · rw [show (VExpr.app f a).liftN n k = .app (f.liftN n k) (a.liftN n k) from rfl,
        interp_app_type M L (fun h => hp (hsplit.mp h)), interp_app_type M L hp,
        interp_liftN hS f W hj hf hρ hρ' hag, interp_liftN hS a W hj ha hρ hρ' hag]
  | .lam A b, k, Γ, Γ', W, hj, hcl, ρ, ρ', hρ, hρ', hag => by
    obtain ⟨hA, hb⟩ := hcl
    have hlen := Ctx.LiftN.length W
    have hkle := Ctx.LiftN.le W
    have W' : Ctx.LiftN n (k + 1) (A :: Γ) (A.liftN n k :: Γ') := W.succ
    have hj' : (A :: Γ).length - (k + 1) = j := by simp; omega
    have hsplit : L.IsProof M (A.liftN n k :: Γ') (b.liftN n (k + 1)) ↔
        L.IsProof M (A :: Γ) b := by
      simp only [LevelAssign.IsProof, VLevel.equiv_def.mp (hS.srt_liftN W' b) M.ls]
    by_cases hp : L.IsProof M (A :: Γ) b
    · rw [show (VExpr.lam A b).liftN n k = .lam (A.liftN n k) (b.liftN n (k + 1)) from rfl,
        interp_lam_proof M L (hsplit.mpr hp), interp_lam_proof M L hp]
    · rw [show (VExpr.lam A b).liftN n k = .lam (A.liftN n k) (b.liftN n (k + 1)) from rfl,
        interp_lam_type M L (fun h => hp (hsplit.mp h)), interp_lam_type M L hp]
      have hAeq := interp_liftN hS A W hj hA hρ hρ' hag
      ext y
      rw [mem_mkLam_iff, mem_mkLam_iff, hAeq]
      refine exists_congr fun v ↦ and_congr_right fun hv ↦ ?_
      rw [interp_liftN hS b W' hj' hb
        ((mem_interpCtx_cons M L).mpr ⟨ρ, hρ, v, by rwa [← hAeq] at hv ⊢, rfl⟩)
        ((mem_interpCtx_cons M L).mpr ⟨ρ', hρ', v, by rwa [hAeq], rfl⟩)
        (AgreePos.snoc M L (by omega) rfl (by omega) hρ hρ' hag v)]
  | .forallE A B, k, Γ, Γ', W, hj, hcl, ρ, ρ', hρ, hρ', hag => by
    obtain ⟨hA, hB⟩ := hcl
    have hlen := Ctx.LiftN.length W
    have hkle := Ctx.LiftN.le W
    have W' : Ctx.LiftN n (k + 1) (A :: Γ) (A.liftN n k :: Γ') := W.succ
    have hj' : (A :: Γ).length - (k + 1) = j := by simp; omega
    have hsplit : L.IsProp M (A.liftN n k :: Γ') (B.liftN n (k + 1)) ↔
        L.IsProp M (A :: Γ) B := by
      simp only [LevelAssign.IsProp, VLevel.equiv_def.mp (hS.lvl_liftN W' B) M.ls]
    have hAeq := interp_liftN hS A W hj hA hρ hρ' hag
    have hBeq : ∀ v ∈ (interp M L Γ A).toFun ρ,
        (interp M L (A.liftN n k :: Γ') (B.liftN n (k + 1))).toFun (snoc ρ' v) =
          (interp M L (A :: Γ) B).toFun (snoc ρ v) := by
      intro v hv
      exact interp_liftN hS B W' hj' hB
        ((mem_interpCtx_cons M L).mpr ⟨ρ, hρ, v, hv, rfl⟩)
        ((mem_interpCtx_cons M L).mpr ⟨ρ', hρ', v, by rwa [hAeq], rfl⟩)
        (AgreePos.snoc M L (by omega) rfl (by omega) hρ hρ' hag v)
    by_cases hp : L.IsProp M (A :: Γ) B
    · rw [show (VExpr.forallE A B).liftN n k
          = .forallE (A.liftN n k) (B.liftN n (k + 1)) from rfl,
        interp_forallE_prop M L (hsplit.mpr hp), interp_forallE_prop M L hp]
      ext z
      rw [mem_mkForallProp_iff, mem_mkForallProp_iff, hAeq]
      exact and_congr_right fun _ ↦ forall₂_congr fun v hv ↦ by rw [hBeq v hv]
    · rw [show (VExpr.forallE A B).liftN n k
          = .forallE (A.liftN n k) (B.liftN n (k + 1)) from rfl,
        interp_forallE_type M L (fun h => hp (hsplit.mp h)), interp_forallE_type M L hp]
      ext f
      rw [mem_mkForallType_iff, mem_mkForallType_iff, hAeq]
      refine and_congr ?_ ?_
      · congr! 2
        ext y
        rw [mem_mkFamUnion_iff, mem_mkFamUnion_iff, hAeq]
        exact exists_congr fun v ↦ and_congr_right fun hv ↦ by
          rw [hBeq v hv]
      · exact forall₂_congr fun v hv ↦ forall_congr' fun y ↦ imp_congr_right fun _ ↦ by
          rw [hBeq v hv]

end Weakening

/-! ## Substitution

Carneiro's substitution lemma (`soundness.tex:206-214`) is entangled with the
main soundness induction: it presupposes the interpretation of the term being
substituted.  That entanglement is made explicit here as the `top` field of
`AgreeInst` — "the valuation's value at the substituted slot *is* the
interpretation of the substituted term" — rather than being proved first.
-/

section Substitution

variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {env : VEnv} {nv : ℕ} (M : ModelData V) (L : LevelAssign env nv)

theorem Ctx.InstN.length₀ : ∀ {Γ₀ : List VExpr} {e₀ A₀ : VExpr} {k : ℕ} {Γ₁ Γ : List VExpr},
    Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ → Γ.length = Γ₀.length + k
  | _, _, _, _, _, _, .zero => by simp
  | _, _, _, _, _, _, .succ W => by simp [Ctx.InstN.length₀ W]; omega

/-- Reindexing of valuation positions when one slot at position `j` is filled
in.  As with `liftPos`, `j` is invariant under going below a binder. -/
def instPos (j p : ℕ) : ℕ := if p < j then p else p + 1

/-- `ρ₁` is `ρ` with the substituted value inserted at position `j`.  The second
component is Carneiro's entanglement, stated rather than proved. -/
def AgreeInst (j m k : ℕ) (e₀ : VExpr) (Γ : List VExpr) (ρ₁ ρ : V) : Prop :=
  (∀ p, p < m → ρ₁ ‘ ((instPos j p : ℕ) : V) = ρ ‘ ((p : ℕ) : V)) ∧
    ρ₁ ‘ ((j : ℕ) : V) = (interp M L Γ (e₀.liftN k)).toFun ρ

lemma AgreeInst.snoc (hS : L.Stable) {j m k : ℕ} {e₀ A : VExpr} {Γ Γ₁ : List VExpr}
    {ρ₁ ρ v : V} (hj : j ≤ m) (hk : k ≤ m)
    (hΓ : Γ.length = m) (hΓ₁ : Γ₁.length = m + 1)
    (hcl : (e₀.liftN k).ClosedN Γ.length)
    (hρ : ρ ∈ interpCtx M L Γ) (hρ₁ : ρ₁ ∈ interpCtx M L Γ₁)
    (hv : v ∈ (interp M L Γ A).toFun ρ)
    (h : AgreeInst M L j m k e₀ Γ ρ₁ ρ) :
    AgreeInst M L j (m + 1) (k + 1) e₀ (A :: Γ) (snoc ρ₁ v) (snoc ρ v) := by
  obtain ⟨hpos, htop⟩ := h
  constructor
  · intro p hp
    rcases Nat.lt_succ_iff_lt_or_eq.mp hp with hp' | rfl
    · have h1 : instPos j p < m + 1 := by simp only [instPos]; split <;> omega
      rw [snoc_value_of_lt M L hρ₁ (by omega : instPos j p < Γ₁.length),
        snoc_value_of_lt M L hρ (by omega : p < Γ.length)]
      exact hpos p hp'
    · have hpj : ¬ p < j := by omega
      have hip : instPos j p = p + 1 := by simp [instPos, hpj]
      rw [hip, show ((p + 1 : ℕ) : V) = ((Γ₁.length : ℕ) : V) by rw [hΓ₁],
        show ((p : ℕ) : V) = ((Γ.length : ℕ) : V) by rw [hΓ],
        snoc_value_at_len M L hρ₁, snoc_value_at_len M L hρ]
  · rw [snoc_value_of_lt M L hρ₁ (by omega : j < Γ₁.length), htop]
    have hlift : e₀.liftN (k + 1) = (e₀.liftN k).liftN 1 := by
      rw [VExpr.liftN'_liftN_hi]
    rw [hlift]
    refine (interp_liftN M L hS (n := 1) (j := Γ.length) (e₀.liftN k)
      (Ctx.LiftN.zero (n := 1) [A] rfl) (by simp) hcl hρ ((mem_interpCtx_cons M L).mpr ⟨ρ, hρ, v, hv, rfl⟩) ?_).symm
    · intro p hp
      have : liftPos 1 Γ.length p = p := by simp [liftPos]; omega
      rw [this]
      exact snoc_value_of_lt M L hρ (by omega)

/-- **Substitution.**  `⟦Γ ⊢ e[e₀/k]⟧ ρ = ⟦Γ₁ ⊢ e⟧ ρ₁` whenever `ρ₁` is `ρ`
with the interpretation of `e₀` inserted at the substituted slot.

The hypothesis `AgreeInst` carries Carneiro's entanglement in its second
component; nothing here proves that the substituted term *has* an
interpretation in the right set — that is soundness, and it is supplied by the
main induction. -/
theorem interp_inst (hS : L.Stable) {j : ℕ} :
    ∀ (e : VExpr) {Γ₀ Γ₁ Γ : List VExpr} {e₀ A₀ : VExpr} {k : ℕ},
      Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ → Γ.length - k = j →
      e.ClosedN Γ₁.length → (e₀.liftN k).ClosedN Γ.length →
      ∀ {ρ ρ₁ : V}, ρ ∈ interpCtx M L Γ → ρ₁ ∈ interpCtx M L Γ₁ →
      AgreeInst M L j Γ.length k e₀ Γ ρ₁ ρ →
      (interp M L Γ (e.inst e₀ k)).toFun ρ = (interp M L Γ₁ e).toFun ρ₁
  | .bvar i, Γ₀, Γ₁, Γ, e₀, A₀, k, W, hj, hcl, hcl₀, ρ, ρ₁, hρ, hρ₁, hag => by
    have hlen := Ctx.InstN.length W
    have hkle := Ctx.InstN.le W
    have hi : i < Γ₁.length := hcl
    obtain ⟨hpos, htop⟩ := hag
    rw [show (VExpr.bvar i).inst e₀ k = VExpr.instVar i e₀ k from rfl]
    by_cases h1 : i < k
    · rw [show VExpr.instVar i e₀ k = .bvar i by simp [VExpr.instVar, h1],
        interp_bvar, interp_bvar]
      have hp : instPos j (Γ.length - 1 - i) = Γ₁.length - 1 - i := by
        simp only [instPos, ← hj, hlen]; split <;> omega
      rw [← hp]
      exact (hpos _ (by omega)).symm
    · by_cases h2 : i = k
      · subst h2
        rw [show VExpr.instVar i e₀ i = e₀.liftN i by simp [VExpr.instVar], interp_bvar]
        rw [show Γ₁.length - 1 - i = j by omega, htop]
      · rw [show VExpr.instVar i e₀ k = .bvar (i - 1) by simp [VExpr.instVar, h1, h2],
          interp_bvar, interp_bvar]
        have hp : instPos j (Γ.length - 1 - (i - 1)) = Γ₁.length - 1 - i := by
          simp only [instPos, ← hj, hlen]; split <;> omega
        rw [← hp]
        exact (hpos _ (by omega)).symm
  | .sort u, Γ₀, Γ₁, Γ, e₀, A₀, k, W, hj, hcl, hcl₀, ρ, ρ₁, hρ, hρ₁, hag => by
    rw [show (VExpr.sort u).inst e₀ k = .sort u from rfl, interp_sort, interp_sort]
  | .const c us, Γ₀, Γ₁, Γ, e₀, A₀, k, W, hj, hcl, hcl₀, ρ, ρ₁, hρ, hρ₁, hag => by
    rw [show (VExpr.const c us).inst e₀ k = .const c us from rfl, interp_const, interp_const]
  | .app f a, Γ₀, Γ₁, Γ, e₀, A₀, k, W, hj, hcl, hcl₀, ρ, ρ₁, hρ, hρ₁, hag => by
    obtain ⟨hf, ha⟩ := hcl
    have hsplit : L.IsProof M Γ (f.inst e₀ k) ↔ L.IsProof M Γ₁ f := by
      simp only [LevelAssign.IsProof, VLevel.equiv_def.mp (hS.srt_instN W f) M.ls]
    by_cases hp : L.IsProof M Γ₁ f
    · rw [show (VExpr.app f a).inst e₀ k = .app (f.inst e₀ k) (a.inst e₀ k) from rfl,
        interp_app_proof M L (hsplit.mpr hp), interp_app_proof M L hp]
    · rw [show (VExpr.app f a).inst e₀ k = .app (f.inst e₀ k) (a.inst e₀ k) from rfl,
        interp_app_type M L (fun h => hp (hsplit.mp h)), interp_app_type M L hp,
        interp_inst hS f W hj hf hcl₀ hρ hρ₁ hag, interp_inst hS a W hj ha hcl₀ hρ hρ₁ hag]
  | .lam A b, Γ₀, Γ₁, Γ, e₀, A₀, k, W, hj, hcl, hcl₀, ρ, ρ₁, hρ, hρ₁, hag => by
    obtain ⟨hA, hb⟩ := hcl
    have hlen := Ctx.InstN.length W
    have hkle := Ctx.InstN.le W
    have W' : Ctx.InstN Γ₀ e₀ A₀ (k + 1) (A :: Γ₁) (A.inst e₀ k :: Γ) := W.succ
    have hj' : (A.inst e₀ k :: Γ).length - (k + 1) = j := by simp; omega
    have hcl₀' : (e₀.liftN (k + 1)).ClosedN (A.inst e₀ k :: Γ).length := by
      have hx := hcl₀.liftN (n := 1) (j := 0)
      rw [VExpr.liftN_liftN] at hx
      simpa using hx
    have hAeq := interp_inst hS A W hj hA hcl₀ hρ hρ₁ hag
    have hsplit : L.IsProof M (A.inst e₀ k :: Γ) (b.inst e₀ (k + 1)) ↔
        L.IsProof M (A :: Γ₁) b := by
      simp only [LevelAssign.IsProof, VLevel.equiv_def.mp (hS.srt_instN W' b) M.ls]
    by_cases hp : L.IsProof M (A :: Γ₁) b
    · rw [show (VExpr.lam A b).inst e₀ k = .lam (A.inst e₀ k) (b.inst e₀ (k + 1)) from rfl,
        interp_lam_proof M L (hsplit.mpr hp), interp_lam_proof M L hp]
    · rw [show (VExpr.lam A b).inst e₀ k = .lam (A.inst e₀ k) (b.inst e₀ (k + 1)) from rfl,
        interp_lam_type M L (fun h => hp (hsplit.mp h)), interp_lam_type M L hp]
      ext y
      rw [mem_mkLam_iff, mem_mkLam_iff, hAeq]
      refine exists_congr fun v ↦ and_congr_right fun hv ↦ ?_
      rw [interp_inst hS b W' hj' hb hcl₀'
        ((mem_interpCtx_cons M L).mpr ⟨ρ, hρ, v, by rwa [hAeq], rfl⟩)
        ((mem_interpCtx_cons M L).mpr ⟨ρ₁, hρ₁, v, hv, rfl⟩)
        (AgreeInst.snoc M L hS (by omega) (by omega) rfl (by omega) hcl₀ hρ hρ₁
          (by rwa [hAeq]) hag)]
  | .forallE A B, Γ₀, Γ₁, Γ, e₀, A₀, k, W, hj, hcl, hcl₀, ρ, ρ₁, hρ, hρ₁, hag => by
    obtain ⟨hA, hB⟩ := hcl
    have hlen := Ctx.InstN.length W
    have hkle := Ctx.InstN.le W
    have W' : Ctx.InstN Γ₀ e₀ A₀ (k + 1) (A :: Γ₁) (A.inst e₀ k :: Γ) := W.succ
    have hj' : (A.inst e₀ k :: Γ).length - (k + 1) = j := by simp; omega
    have hcl₀' : (e₀.liftN (k + 1)).ClosedN (A.inst e₀ k :: Γ).length := by
      have hx := hcl₀.liftN (n := 1) (j := 0)
      rw [VExpr.liftN_liftN] at hx
      simpa using hx
    have hAeq := interp_inst hS A W hj hA hcl₀ hρ hρ₁ hag
    have hsplit : L.IsProp M (A.inst e₀ k :: Γ) (B.inst e₀ (k + 1)) ↔
        L.IsProp M (A :: Γ₁) B := by
      simp only [LevelAssign.IsProp, VLevel.equiv_def.mp (hS.lvl_instN W' B) M.ls]
    have hBeq : ∀ v ∈ (interp M L Γ₁ A).toFun ρ₁,
        (interp M L (A.inst e₀ k :: Γ) (B.inst e₀ (k + 1))).toFun (snoc ρ v) =
          (interp M L (A :: Γ₁) B).toFun (snoc ρ₁ v) := by
      intro v hv
      exact interp_inst hS B W' hj' hB hcl₀'
        ((mem_interpCtx_cons M L).mpr ⟨ρ, hρ, v, by rwa [hAeq], rfl⟩)
        ((mem_interpCtx_cons M L).mpr ⟨ρ₁, hρ₁, v, hv, rfl⟩)
        (AgreeInst.snoc M L hS (by omega) (by omega) rfl (by omega) hcl₀ hρ hρ₁
          (by rwa [hAeq]) hag)
    by_cases hp : L.IsProp M (A :: Γ₁) B
    · rw [show (VExpr.forallE A B).inst e₀ k
          = .forallE (A.inst e₀ k) (B.inst e₀ (k + 1)) from rfl,
        interp_forallE_prop M L (hsplit.mpr hp), interp_forallE_prop M L hp]
      ext z
      rw [mem_mkForallProp_iff, mem_mkForallProp_iff, hAeq]
      exact and_congr_right fun _ ↦ forall₂_congr fun v hv ↦ by rw [hBeq v hv]
    · rw [show (VExpr.forallE A B).inst e₀ k
          = .forallE (A.inst e₀ k) (B.inst e₀ (k + 1)) from rfl,
        interp_forallE_type M L (fun h => hp (hsplit.mp h)), interp_forallE_type M L hp]
      ext f
      rw [mem_mkForallType_iff, mem_mkForallType_iff, hAeq]
      refine and_congr ?_ ?_
      · congr! 2
        ext y
        rw [mem_mkFamUnion_iff, mem_mkFamUnion_iff, hAeq]
        exact exists_congr fun v ↦ and_congr_right fun hv ↦ by rw [hBeq v hv]
      · exact forall₂_congr fun v hv ↦ forall_congr' fun y ↦ imp_congr_right fun _ ↦ by
          rw [hBeq v hv]

end Substitution

end Lean4Lean.SetModel
