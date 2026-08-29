import Lean4Lean.Theory.Typing.SortUniqDown
import Lean4Lean.Theory.Typing.UniqueTyping

/-!
# `sort_inv`, `SortUniq` and `uniq` from Π-injectivity alone

**`IsDefEqU.sort_inv` is not an independent obligation.**  This file proves it — and
`VEnv.SortUniq`, and `IsDefEq.uniq` — from `IsDefEqU.forallE_inv_stratified` and nothing else
that is open.  Measured with the cut instrument (`docs/handoff-sortuniq.md` §3): cutting
`forallE_inv_stratified` out of `uniqAux`'s forward cone leaves **no** declaration in it that
mentions `sorryAx`, and `IsDefEqU.sort_inv` is **not in the cone at all**.

    forallE_inv_stratified  ⟹  uniqAux  ⟹  SortUniq  ⟹  sort_inv
                                       ⟹  uniq

## What changed, in one sentence

`IsDefEq.uniq`'s induction (`Theory/Typing/UniqueTyping.lean:13`) calls `IsDefEqU.sort_inv`
nine times, and **every one of those calls is applied to an output of its own induction
hypothesis, at a point where both types are syntactic sorts.**  So the level equivalence they
extract can be *carried by the invariant* instead of imported: `UniqAux` below is `uniq`'s
invariant plus the conjunct

    ∀ s₁ s₂, A = .sort s₁ → B = .sort s₂ → s₁ ≈ s₂

and that conjunct is exactly `VEnv.SortUniq`, read off the invariant at `A = .sort u`,
`B = .sort v`.

## Why the extra conjunct costs nothing

It is not proved case by case — it is derived *once*, uniformly, from the components the
invariant already carries (`sortType_level`).  Given `HTS Γ A (.sort u) true (n-1)`,
`HTS Γ B (.sort v) true (n-1)` and `u ≈ v`, with `A = .sort s₁` and `B = .sort s₂`: apply the
invariant **at index `n-1`** to `.sort s₁` at its two types `.sort u` and `.sort (.succ s₁)`
(the second by `sort'`, at index `0`) to get `u ≈ .succ s₁`, symmetrically `v ≈ .succ s₂`, and
compose.  The recursion is on the same well-founded `n` the original proof already uses, and
it strictly decreases.  At `n = 0` the only derivation available is `sort'`, so the type is
pinned outright (`HasTypeStratified.sort_zero_inv`) — that is the base case.

**Where the type index pays.**  This works because `HasTypeStratified`'s `defeq` premise
carries the type as `.sort u` *syntactically* — so "both types are sorts" is a decidable
pattern on the invariant rather than a fact about a conversion derivation.  The same port
artifact that makes `sort_inv` a corollary of `SortUniq`
(`Theory/Typing/SortUniqDown.lean`) makes `SortUniq` a corollary of `uniq`'s own induction.

## Provenance and honesty

`uniqQ` is `IsDefEq.uniq`'s proof from `Theory/Typing/UniqueTyping.lean`, transcribed with
exactly two kinds of change: the nine `IsDefEqU.sort_inv` calls are replaced by
`hc _ _ rfl rfl` from the strengthened induction hypothesis, and the binder order is adjusted
so the same `induction … generalizing` shape elaborates in a standalone statement.  Nothing
in `UniqueTyping.lean` was edited; that file is another stream's.

**This does not lower the `sorry` count by itself.**  `Injectivity.lean`'s `sort_inv` is still
`sorry`-backed where it stands, because this file *imports* it.  Removing it is a
reordering — `IsDefEqU.sort_inv` has exactly **two** direct users in the tree
(`IsDefEq.uniq` and one declaration in `ChurchRosser.lean`), and `IsDefEq.uniq'` below
replaces the first — but the edit is in files this stream does not own.  See
`docs/handoff-sortuniq.md` §9.
-/

namespace Lean4Lean
namespace VEnv

variable {env : VEnv} {U : Nat}
local notation:65 Γ " ⊢ " e " : " A:36 => HasType env U Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2 " : " A:36 => IsDefEq env U Γ e1 e2 A

/-- The strengthened invariant of `IsDefEq.uniq`: the original conclusion, plus the level
equivalence in the case where both types are syntactic sorts. -/
def UniqAux (env : VEnv) (U n : Nat) : Prop :=
  ∀ {Γ : List VExpr} {e A B : VExpr} {b : Bool} {n₁ n₂ : Nat},
    OnCtx Γ (env.IsType U) → n₁ ≤ n → n₂ ≤ n →
    env.HasTypeStratified U Γ e A b n₁ → env.HasTypeStratified U Γ e B b n₂ →
    ∃ u, env.IsDefEq U Γ A B (.sort u) ∧ ∃ v, u ≈ v ∧
      env.HasTypeStratified U Γ A (.sort u) true (n-1) ∧
      env.HasTypeStratified U Γ B (.sort v) true (n-1) ∧
      ∀ s₁ s₂, A = .sort s₁ → B = .sort s₂ → s₁ ≈ s₂

/-- At index `0` the only derivation of a sort's type is `sort'`, so the type is pinned. -/
theorem HasTypeStratified.sort_zero_inv {Γ : List VExpr} {s u : VLevel}
    (h : env.HasTypeStratified U Γ (.sort s) (.sort u) true 0) : u ≈ .succ s := by
  cases h with | base h => cases h with | sort' _ _ h3 => exact (VLevel.succ_congr h3).symm

/-- The level of a sort's type, read off the strengthened invariant one index down. -/
theorem sortType_level (henv : VEnv.WF env) {Γ : List VExpr} {s u : VLevel} {n : Nat}
    (IH : ∀ m, m < n → UniqAux env U m) (hΓ : OnCtx Γ (env.IsType U))
    (h : env.HasTypeStratified U Γ (.sort s) (.sort u) true (n-1)) : u ≈ .succ s := by
  match n with
  | 0 => exact h.sort_zero_inv
  | m+1 =>
    have hs : s.WF U := h.hasType.sort_inv henv.ordered
    have ⟨_, _, _, _, _, _, hc⟩ := IH m (Nat.lt_succ_self _) hΓ (Nat.le_refl m) (Nat.zero_le m)
      h (.base (.sort' hs hs rfl))
    exact hc _ _ rfl rfl

/-- The body of `IsDefEq.uniq`'s induction, with each of its nine appeals to
`IsDefEqU.sort_inv` replaced by the strengthened invariant at a smaller index. -/
theorem uniqQ (henv : VEnv.WF env) : ∀ {n : Nat}, (∀ m, m < n → UniqAux env U m) →
    ∀ {n₁ n₂ : Nat} {Γ : List VExpr} {e A B : VExpr} {b : Bool},
    OnCtx Γ (env.IsType U) → n₁ ≤ n → n₂ ≤ n →
    env.HasTypeStratified U Γ e A b n₁ → env.HasTypeStratified U Γ e B b n₂ →
    ∃ u, Γ ⊢ A ≡ B : .sort u ∧ ∃ v, u ≈ v ∧
      env.HasTypeStratified U Γ A (.sort u) true (n-1) ∧
      env.HasTypeStratified U Γ B (.sort v) true (n-1) := by
  intro n IH n₁ n₂ Γ e A B b hΓ le₁ le₂ H1
  induction H1 generalizing B n₂ n with
  | bvar a1 a2 =>
    intro (.bvar b1 b2); cases a1.uniq b1
    exact ⟨_, b2.hasType, _, rfl, b2.mono (by omega), b2.mono (by omega)⟩
  | sort' a1 a2 a3 =>
    intro (.sort' b1 b2 b3)
    have := VLevel.succ_congr (b3.symm.trans a3)
    exact ⟨_, .symm <| .sortDF b2 a2 this, _, VLevel.succ_congr this,
      .base <| .sort' a2 b2 this.symm, .base <| .sort' b2 a2 this⟩
  | const a1 a2 a3 a4 =>
    intro (.const b1 b2 b3 b4); cases a1.symm.trans b1
    replace le₁ := Nat.sub_le_sub_right le₁ 1
    exact ⟨_, a4.hasType, _, rfl, a4.mono le₁, a4.mono le₁⟩
  | app _ a2 a3 a4 _ a6 a7 _ _ ih3 =>
    intro (.app _ _ b3 b4 b5 _ b7)
    have ⟨_, c1, _, _, c3, c4⟩ := ih3 (n := n) IH hΓ (Nat.le_of_succ_le le₁) (Nat.le_of_succ_le le₂) b5
    have ⟨_, _, d3, d4, d5⟩ := IsDefEqU.forallE_inv_stratified henv hΓ ⟨_, c1⟩ c3 c4
    let n+1 := n
    replace le₁ := Nat.le_of_succ_le_succ le₁
    replace le₂ := Nat.le_of_succ_le_succ le₂
    refine have hΓ₁ := ⟨hΓ, _, a3.hasType⟩
      have ⟨_, _, _, _, _, _, hc1⟩ :=
        IH _ (Nat.lt_succ_self _) hΓ₁ le₁ (Nat.le_refl _) a4 d4; ?_
    have e3 := hc1 _ _ rfl rfl
    have e4 := have ⟨_, h⟩ := d4.hasType.isType henv hΓ₁; h.sort_inv henv
    refine have hΓ₂ := ⟨hΓ, _, b3.hasType⟩
      have ⟨_, _, _, _, _, _, hc2⟩ :=
        IH _ (Nat.lt_succ_self _) hΓ₂ le₂ (Nat.le_refl _) b4 d5; ?_
    have e5 := hc2 _ _ rfl rfl
    exact ⟨_, .defeqDF (.sortDF e4 a2 e3.symm) (d3.instN henv a6.hasType .zero), _,
      e3.trans e5.symm, a7.mono le₁, b7.mono le₂⟩
  | lam a1 a2 _ a4 _ _ ih3 =>
    intro (.lam b1 b2 b3 b4)
    have ⟨_, c1, _, c2, c3, c4⟩ := ih3 (n := n) IH ⟨hΓ, _, a1.hasType⟩
      (Nat.le_of_succ_le le₁) (Nat.le_of_succ_le le₂) b3
    let n+1 := n
    replace le₁ := Nat.le_of_succ_le_succ le₁
    replace le₂ := Nat.le_of_succ_le_succ le₂
    have ⟨_, _, _, _, _, _, hc1⟩ := IH _ (Nat.lt_succ_self _) hΓ le₁ le₂ a1 b1
    have e1 := hc1 _ _ rfl rfl
    refine have hΓ' := ⟨hΓ, _, a1.hasType⟩
      have ⟨_, h, _, _, _, _, hc2⟩ :=
        IH _ (Nat.lt_succ_self _) hΓ' le₁ (Nat.le_refl _) a2 c3; ?_
    have f1 := h.sort_inv_l henv; have f2 := h.sort_inv_r henv
    have e2 := hc2 _ _ rfl rfl
    have ⟨_, _, _, _, _, _, hc3⟩ := IH _ (Nat.lt_succ_self _) hΓ' le₂ (Nat.le_refl _) b2 c4
    have e3 := hc3 _ _ rfl rfl
    exact ⟨_, .forallEDF a1.hasType (.defeqDF (.symm <| .sortDF f1 f2 e2) c1),
      _, VLevel.imax_congr e1 (e2.trans <| c2.trans e3.symm), a4.mono le₁, b4.mono le₂⟩
  | forallE a1 a2 a3 a4 =>
    intro (.forallE b1 b2 b3 b4)
    let n+1 := n
    replace le₁ := Nat.le_of_succ_le_succ le₁
    replace le₂ := Nat.le_of_succ_le_succ le₂
    have ⟨_, _, _, _, _, _, hc1⟩ := IH _ (Nat.lt_succ_self _) hΓ le₁ le₂ a3 b3
    have e1 := hc1 _ _ rfl rfl
    refine have hΓ' := ⟨hΓ, _, a3.hasType⟩
      have ⟨_, _, _, _, _, _, hc2⟩ := IH _ (Nat.lt_succ_self _) hΓ' le₁ le₂ a4 b4; ?_
    have e2 := hc2 _ _ rfl rfl
    have := VLevel.imax_congr e1 e2
    exact ⟨_, .sortDF ⟨a1, a2⟩ ⟨b1, b2⟩ this, _, rfl,
      .base <| .sort' ⟨a1, a2⟩ ⟨a1, a2⟩ rfl, .base <| .sort' ⟨b1, b2⟩ ⟨a1, a2⟩ this.symm⟩
  | @base Γ e A n₁ a1 ih =>
    intro H2
    replace ih {n'} (le : n' ≤ n) {n₂' : Nat} {B' : VExpr} :=
      ih (n := n') (fun y h1 => IH y (Nat.lt_of_lt_of_le h1 le)) (n₂ := n₂') (B := B') hΓ
    generalize eq : true = b at H2
    induction H2 with cases eq
    | @base _ _  _ n' b1 => exact ih (Nat.le_refl _) le₁ le₂ b1
    | @defeq Γ B' B u n' _ b1 b2 b3 b4 b5 _ _ ih' =>
      have ⟨u₁, c1, u₂, c2, c3, c4⟩ := ih' a1 hΓ (Nat.le_of_succ_le le₂) ih rfl
      let n+1 := n
      replace le₂ := Nat.le_of_succ_le_succ le₂
      have ⟨_, _, _, _, _, _, hc⟩ :=
        IH _ (Nat.lt_succ_self _) hΓ le₂ (Nat.le_refl _) b3 c4
      have e1 := hc _ _ rfl rfl
      have e2 := have ⟨_, h⟩ := c3.hasType.isType henv hΓ; h.sort_inv henv
      have eq : u₁ ≈ u := c2.trans e1.symm
      exact ⟨_, c1.trans (.defeqDF (.symm <| .sortDF e2 b1 eq) b2), _, eq, c3, b4.mono le₂⟩
  | @defeq Γ A' A u n' _ a1 a2 a3 a4 a5 ih1 ih2 ih' =>
    intro H2
    have ⟨_, c1, u₂, c2, c3, c4⟩ := ih' IH hΓ (Nat.le_of_succ_le le₁) le₂ H2
    let n+1 := n
    replace le₁ := Nat.le_of_succ_le_succ le₁
    have ⟨_, _, _, _, _, _, hc⟩ := IH _ (Nat.lt_succ_self _) hΓ le₁ (Nat.le_refl _) a3 c3
    have e1 := hc _ _ rfl rfl
    have e2 := have ⟨_, h⟩ := c3.hasType.isType henv hΓ; h.sort_inv henv
    have eq : u ≈ u₂ := e1.trans c2
    exact ⟨_, a2.symm.trans (.defeqDF (.symm <| .sortDF a1 e2 e1) c1), _, eq, a4.mono le₁, c4⟩

/-- The strengthened invariant, at every index. -/
theorem uniqAux (henv : VEnv.WF env) : ∀ n, UniqAux env U n := by
  intro n
  induction n using WellFounded.induction Nat.lt_wfRel.2 with | _ n IH
  intro Γ e A B b n₁ n₂ hΓ le₁ le₂ H1 H2
  obtain ⟨u, h, v, hv, c3, c4⟩ := uniqQ henv IH hΓ le₁ le₂ H1 H2
  refine ⟨u, h, v, hv, c3, c4, ?_⟩
  rintro s₁ s₂ rfl rfl
  have h1 := sortType_level henv IH hΓ c3
  have h2 := sortType_level henv IH hΓ c4
  exact VLevel.succ_congr_iff.1 (h1.symm.trans (hv.trans h2))

/-! ## Consequences -/

/-- **Universe uniqueness, from Π-injectivity alone.**  The only `sorry`-backed input is
`IsDefEqU.forallE_inv_stratified`; `IsDefEqU.sort_inv` is *not* used. -/
theorem WF.sortUniq' (henv : VEnv.WF env) : env.SortUniq U := by
  intro Γ e u v hΓ _ _ h1 h2
  obtain ⟨n₁, H1⟩ := (h1.strong henv.ordered hΓ).hasType'.1.stratify
  obtain ⟨n₂, H2⟩ := (h2.strong henv.ordered hΓ).hasType'.1.stratify
  obtain ⟨_, _, _, _, _, _, hc⟩ :=
    uniqAux henv _ hΓ (Nat.le_max_left n₁ n₂) (Nat.le_max_right n₁ n₂) H1 H2
  exact hc _ _ rfl rfl

/-- **Sort injectivity, from Π-injectivity alone** — the statement of
`IsDefEqU.sort_inv`, with `IsDefEqU.sort_inv` itself not in the proof's cone. -/
theorem IsDefEqU.sort_inv' {Γ : List VExpr} {u v : VLevel} (henv : VEnv.WF env)
    (hΓ : OnCtx Γ (env.IsType U)) (h1 : env.IsDefEqU U Γ (.sort u) (.sort v)) : u ≈ v :=
  sort_inv_of_sortUniq (WF.sortUniq' henv) henv.ordered hΓ h1

/-- Unique typing, from Π-injectivity alone — the statement of `IsDefEq.uniq`. -/
theorem IsDefEq.uniq' {Γ : List VExpr} {e₁ e₂ e₃ A B : VExpr} (henv : VEnv.WF env)
    (hΓ : OnCtx Γ (env.IsType U))
    (h1 : Γ ⊢ e₁ ≡ e₂ : A) (h2 : Γ ⊢ e₂ ≡ e₃ : B) : ∃ u, Γ ⊢ A ≡ B : .sort u := by
  obtain ⟨n₁, H1⟩ := (h1.strong henv.ordered hΓ).hasType'.2.stratify
  obtain ⟨n₂, H2⟩ := (h2.strong henv.ordered hΓ).hasType'.1.stratify
  obtain ⟨u, h, _⟩ :=
    uniqAux henv _ hΓ (Nat.le_max_left n₁ n₂) (Nat.le_max_right n₁ n₂) H1 H2
  exact ⟨u, h⟩

/-! ## Non-vacuity: fired at `CycleConv.propLoopEnv`

`propLoopEnv` is a proved-`VEnv.WF` environment whose head reduction has a two-cycle
(`propLoop_headStep_not_wf`), so no normalisation argument terminates there.  The hypothesis
`Typing/CycleConv.lean`'s `propLoop_no_direct_collapse` carries is discharged at it. -/

theorem propLoop_sortUniq : propLoopEnv.SortUniq 0 := WF.sortUniq' propLoopEnv_wf

theorem propLoop_no_direct_collapse' {Γ} (hΓ : OnCtx Γ (propLoopEnv.IsType 0)) :
    ¬ propLoopEnv.HasType 0 Γ (.sort .zero) (.sort .zero) :=
  propLoop_no_direct_collapse propLoop_sortUniq hΓ

theorem propLoop_zero_not_defeq_one' :
    ¬ propLoopEnv.IsDefEqU 0 [] (.sort .zero) (.sort (.succ .zero)) :=
  propLoop_zero_not_defeq_one propLoop_sortUniq

end VEnv
end Lean4Lean
