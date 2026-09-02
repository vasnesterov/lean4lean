import Lean4Lean.Theory.SetModel.PropAgreeWall
import Lean4Lean.Theory.Typing.UniqueTyping

/-!
# `InstDescendUp`'s `.bvar k` case: **closed**, and the obstruction relocated

`docs/handoff-setmodel.md` §§7.9, 8.7, 9.7, 10.9 and 12.7 name "`InstDescendUp 0`'s `.bvar k`
case" as the sharpest open mathematics on the model side, untouched for five rounds.  This file
closes it, and reports what the closure cost.

## The result

`prop_inst_bvar` / `proof_inst_bvar` (§4) are the `B = .bvar k` instances of
`VEnv.InstDescendUp`'s two fields, at **every** `k`, with **one** change to the field's
statement: the premise's *witness context* carries `OnCtx`.  Written out for `prop_inst`:

    Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ →  env.HasType nv Γ₀ e₀ A₀ →
    env.IsPropUpOn nv ls Γ ((VExpr.bvar k).inst e₀ k) →  env.IsPropUp nv ls Γ₁ (.bvar k)

`IsPropUpOn` is `IsPropUp` with `OnCtx Γ' (env.IsType nv)` demanded of the context its
existential produces — the same guard `PropSplit`'s own two fields acquired on 2026-09-02.  The
conclusion is the *unguarded* predicate, i.e. exactly what `InstDescendUp` asks for.  From
`env.WF` alone: `prop_inst_bvar_of_wf`, `proof_inst_bvar_of_wf` (§6).

## Three findings, all measured

1. **It is a uniqueness-of-typing instance, and nothing else.**  §7.3's reading was right:
   `SortRetypeOnCtx` — "a term with a type *and* a sort has that type convertible to that
   sort" — is the whole content, and it is the `B = .sort u` instance of `IsDefEq.uniq`
   (`sortRetypeOnCtx_of_wf`).  For `proof_inst` the demand is weaker still: `A₀` need only
   *have* a vanishing sort, which is `PropTypeAgreeOnCtx` plus `IsDefEq.isType`.

2. **No strengthening.**  The proof never moves a defeq down a lift.  The witness context of
   the conclusion is the *premise's own witness context with one binder added*
   (`A₀.lift' l :: Γ'`), so uniqueness is applied exactly where the premise supplied its typing.
   Neither `IsDefEqU.weakN_iff` nor `PropDescend.sort_lift` appears anywhere in §§1–4.  The
   general `k` reduces to `k = 0` for free, because `isPropUp_liftN` is free in both directions
   (`PropSplitUp` §3) and `(.bvar k).inst e₀ k` is `e₀` lifted out of `Γ₀`.

3. **The obstruction that is left is a missing guard, not mathematics.**  Two framings, §7:
   * keep `InstDescendUp`'s premise unguarded and you owe `PropUpNormalise` — normalising
     `IsPropUp`'s witness context — which needs `UnguardedStrengthen`, i.e.
     `IsDefEqU.weakN_iff` **with its `OnCtx Γ'` hypothesis deleted**.  That is *strictly
     stronger* than the tree's hole and is **not** one of the four big holes.
   * guard the premise (this file's theorems) and the cost moves to
     `PropSplit.Stable`'s four fields, which are still unguarded.  `PropUpOnLiftAscend` is the
     one obligation that appears, and `isPropUpOn_liftN_up` shows it is free as soon as the
     target context is guarded — a `§12`-style flag day on `Stable`, with no new mathematics.

## What this does *not* claim

No refutation.  `InstDescendUp` as literally stated (arbitrary `env`, arbitrary contexts) is not
shown false here; a refutation needs a non-derivability argument at a junk context, and every
route to one that was tried (§10) is itself gated on inversion.  And nothing here closes
`InstDescendUp` as a *structure*: the `.forallE` / `.app` / `.lam` cases still need inversion at
a sort, and `.bvar i` with `i < k` is a smaller instance of the same descent (§9, which corrects
§7.3's table on that point).
-/

namespace Lean4Lean

/-! ## 1. de Bruijn bookkeeping: `Ctx.InstN` exposes two lifts out of `Γ₀` -/

/-- Both contexts of a `Ctx.InstN` are `Γ₀` with `k` entries prepended — the substituted one
with `k`, the unsubstituted one with `k` **plus the entry `A₀` being substituted for**. -/
theorem Ctx.InstN.eq_append : ∀ {Γ₀ : List VExpr} {e₀ A₀ : VExpr} {k : ℕ} {Γ₁ Γ : List VExpr},
    Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ →
    ∃ Δ Δ' : List VExpr, Δ.length = k ∧ Δ'.length = k ∧ Γ = Δ ++ Γ₀ ∧ Γ₁ = Δ' ++ A₀ :: Γ₀
  | _, _, _, _, _, _, .zero => ⟨[], [], rfl, rfl, rfl, rfl⟩
  | _, _, _, _, _, _, .succ W => by
    obtain ⟨Δ, Δ', h1, h2, rfl, rfl⟩ := W.eq_append
    exact ⟨_ :: Δ, _ :: Δ', by simp [h1], by simp [h2], rfl, rfl⟩

/-- The substituted context is `Γ₀` weakened by `k`. -/
theorem Ctx.InstN.liftN_target {Γ₀ : List VExpr} {e₀ A₀ : VExpr} {k : ℕ} {Γ₁ Γ : List VExpr}
    (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ) : Ctx.LiftN k 0 Γ₀ Γ := by
  obtain ⟨Δ, _, h1, _, rfl, _⟩ := W.eq_append; exact .zero Δ h1

/-- The unsubstituted context is `A₀ :: Γ₀` weakened by `k`. -/
theorem Ctx.InstN.liftN_source {Γ₀ : List VExpr} {e₀ A₀ : VExpr} {k : ℕ} {Γ₁ Γ : List VExpr}
    (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ) : Ctx.LiftN k 0 (A₀ :: Γ₀) Γ₁ := by
  obtain ⟨_, Δ', _, h2, _, rfl⟩ := W.eq_append; exact .zero Δ' h2

/-- Substituting `e₀` for the variable it replaces returns `e₀`, weakened past the `k`
binders crossed. -/
theorem VExpr.bvar_inst_self (k : ℕ) (e₀ : VExpr) :
    (VExpr.bvar k).inst e₀ k = e₀.liftN k 0 := by
  simp [VExpr.inst, VExpr.instVar]

/-- …and the variable itself, weakened by `k`, is `.bvar k`. -/
theorem VExpr.bvar_zero_liftN (k : ℕ) : (VExpr.bvar 0).liftN k 0 = .bvar k := by
  simp [VExpr.liftN, liftVar]

/-! ## 2. The uniqueness input, named -/

namespace VEnv

variable {env : VEnv} {nv : ℕ}

/-- **The exact input the `.bvar k` case of `InstDescendUp.prop_inst` needs.**

"If a term has a type *and* has a sort, then that type is convertible to that sort."  This is
the `A = A`, `B = .sort u` instance of `IsDefEq.uniq`, and it is `OnCtx`-guarded because
`IsDefEq.uniq` is: the unguarded form quantifies over contexts in which `Lookup` hands out
types that are not themselves typeable (`PropAgreeWall.hasType_junk_lookup`). -/
def SortRetypeOnCtx (env : VEnv) (nv : ℕ) : Prop :=
  ∀ {Γ : List VExpr} {e A : VExpr} {u : VLevel}, OnCtx Γ (env.IsType nv) →
    env.HasType nv Γ e A → env.HasType nv Γ e (.sort u) →
    ∃ w : VLevel, env.IsDefEq nv Γ A (.sort u) (.sort w)

/-- **…and it is `IsDefEq.uniq`, nothing more.**  So the input is available at every `WF`
environment, at every `OnCtx` context. -/
theorem sortRetypeOnCtx_of_wf (henv : env.WF) : env.SortRetypeOnCtx nv :=
  fun hΓ hA hs => hA.uniq henv hΓ hs

/-- **The companion input for `proof_inst`.**  There the demand is not that `A₀` *be* a sort
but that it *have* one whose level vanishes — which is `PropTypeAgreeOnCtx` together with
`IsDefEq.isType`. -/
theorem propTypeAgreeOnCtx_retype (henv : env.Ordered) (hT : env.PropTypeAgreeOnCtx nv)
    {Γ : List VExpr} {e A B : VExpr} {u : VLevel} {ls : List ℕ}
    (hΓ : OnCtx Γ (env.IsType nv)) (hu : u.WF nv)
    (heA : env.HasType nv Γ e A) (heB : env.HasType nv Γ e B)
    (hB : env.HasType nv Γ B (.sort u)) (h0 : u.eval ls = 0) :
    ∃ w : VLevel, w.WF nv ∧ env.HasType nv Γ A (.sort w) ∧ w.eval ls = 0 := by
  obtain ⟨w, hA⟩ := heA.isType henv hΓ
  have hw : w.WF nv := (hA.isType henv hΓ).sort_inv henv
  exact ⟨w, hw, hA, (hT hΓ hw hu heA heB hA hB).2 h0⟩

/-! ## 3. `IsPropUp` / `IsProofUp` with the witness context guarded -/

/-- **`IsPropUp` whose witness context is required to be well-formed.**

`IsPropUp` lets the witness context be *any* context above `Γ`, junk entries included.  This
is the same predicate with `OnCtx` demanded of that context — the guard `PropSplit`'s own two
fields acquired on 2026-09-02, moved to where `IsPropUp` keeps its existential. -/
def IsPropUpOn (env : VEnv) (nv : ℕ) (ls : List ℕ) (Γ : List VExpr) (A : VExpr) : Prop :=
  ∃ (l : Lift) (Γ' : List VExpr) (u : VLevel),
    Ctx.Lift' l Γ Γ' ∧ OnCtx Γ' (env.IsType nv) ∧ u.WF nv ∧
      env.HasType nv Γ' (A.lift' l) (.sort u) ∧ u.eval ls = 0

/-- **`IsProofUp` whose witness context is required to be well-formed.** -/
def IsProofUpOn (env : VEnv) (nv : ℕ) (ls : List ℕ) (Γ : List VExpr) (e : VExpr) : Prop :=
  ∃ (l : Lift) (Γ' : List VExpr) (B : VExpr) (u : VLevel),
    Ctx.Lift' l Γ Γ' ∧ OnCtx Γ' (env.IsType nv) ∧ u.WF nv ∧
      env.HasType nv Γ' (e.lift' l) B ∧ env.HasType nv Γ' B (.sort u) ∧ u.eval ls = 0

theorem IsPropUpOn.isPropUp {ls Γ A} (h : env.IsPropUpOn nv ls Γ A) :
    env.IsPropUp nv ls Γ A := let ⟨l, Γ', u, W, _, hu, ht, h0⟩ := h; ⟨l, Γ', u, W, hu, ht, h0⟩

theorem IsProofUpOn.isProofUp {ls Γ e} (h : env.IsProofUpOn nv ls Γ e) :
    env.IsProofUp nv ls Γ e :=
  let ⟨l, Γ', B, u, W, _, hu, he, hB, h0⟩ := h; ⟨l, Γ', B, u, W, hu, he, hB, h0⟩

/-- The canonical predicate gives the guarded one at a well-formed context: the empty lift. -/
theorem IsPropUpOn.of_hasType {ls Γ A u} (hΓ : OnCtx Γ (env.IsType nv)) (hw : u.WF nv)
    (ht : env.HasType nv Γ A (.sort u)) (h0 : u.eval ls = 0) : env.IsPropUpOn nv ls Γ A :=
  ⟨.refl, Γ, u, .refl, hΓ, hw, by simpa using ht, h0⟩

theorem IsProofUpOn.of_hasType {ls Γ e A u} (hΓ : OnCtx Γ (env.IsType nv)) (hw : u.WF nv)
    (he : env.HasType nv Γ e A) (hA : env.HasType nv Γ A (.sort u)) (h0 : u.eval ls = 0) :
    env.IsProofUpOn nv ls Γ e :=
  ⟨.refl, Γ, A, u, .refl, hΓ, hw, by simpa using he, by simpa using hA, h0⟩

/-- **Descent along a lift, guard-preserving and free.**  The witness context is untouched, so
the `OnCtx` guard survives; this is `isPropUp_lift'`'s easy half. -/
theorem IsPropUpOn.of_lift' {ρ : Lift} {Γ Γ' : List VExpr} (W : Ctx.Lift' ρ Γ Γ')
    {ls : List ℕ} {A : VExpr} (h : env.IsPropUpOn nv ls Γ' (A.lift' ρ)) :
    env.IsPropUpOn nv ls Γ A :=
  let ⟨l, Γ'', u, W', hΓ'', hu, hA, h0⟩ := h
  ⟨Lift.comp ρ l, Γ'', u, W.comp W', hΓ'', hu, by rwa [VExpr.lift'_comp], h0⟩

theorem IsProofUpOn.of_lift' {ρ : Lift} {Γ Γ' : List VExpr} (W : Ctx.Lift' ρ Γ Γ')
    {ls : List ℕ} {e : VExpr} (h : env.IsProofUpOn nv ls Γ' (e.lift' ρ)) :
    env.IsProofUpOn nv ls Γ e :=
  let ⟨l, Γ'', B, u, W', hΓ'', hu, he, hB, h0⟩ := h
  ⟨Lift.comp ρ l, Γ'', B, u, W.comp W', hΓ'', hu, by rwa [VExpr.lift'_comp], hB, h0⟩

theorem IsPropUpOn.of_liftN {n k : ℕ} {Γ Γ' : List VExpr} (W : Ctx.LiftN n k Γ Γ')
    {ls : List ℕ} {A : VExpr} (h : env.IsPropUpOn nv ls Γ' (A.liftN n k)) :
    env.IsPropUpOn nv ls Γ A :=
  IsPropUpOn.of_lift' (Ctx.liftN_iff_lift'.1 W) (by rwa [VExpr.lift'_consN_skipN])

theorem IsProofUpOn.of_liftN {n k : ℕ} {Γ Γ' : List VExpr} (W : Ctx.LiftN n k Γ Γ')
    {ls : List ℕ} {e : VExpr} (h : env.IsProofUpOn nv ls Γ' (e.liftN n k)) :
    env.IsProofUpOn nv ls Γ e :=
  IsProofUpOn.of_lift' (Ctx.liftN_iff_lift'.1 W) (by rwa [VExpr.lift'_consN_skipN])

/-! ## 4. The `.bvar k` case, closed -/

/-- **The `k = 0` core of `InstDescendUp.prop_inst`'s `.bvar k` case.**

From "`e₀ : A₀`" and "`e₀` is a proposition somewhere above `Γ₀`", conclude "the variable of
type `A₀` is a proposition somewhere above `A₀ :: Γ₀`".

The witness context is `A₀.lift' l :: Γ'` — the premise's own witness context with one binder
added — so the uniqueness input is used **at the context where the premise supplied its
typing**, and no defeq ever has to travel down a lift.  That is why nothing here needs
strengthening. -/
theorem isPropUpOn_bvar_zero (henv : env.Ordered) (hR : env.SortRetypeOnCtx nv)
    {Γ₀ : List VExpr} {e₀ A₀ : VExpr} {ls : List ℕ}
    (h₀ : env.HasType nv Γ₀ e₀ A₀) (h : env.IsPropUpOn nv ls Γ₀ e₀) :
    env.IsPropUpOn nv ls (A₀ :: Γ₀) (.bvar 0) := by
  obtain ⟨l, Γ', u, W, hΓ', hu, ht, h0⟩ := h
  have h₀' : env.HasType nv Γ' (e₀.lift' l) (A₀.lift' l) := h₀.weak' henv W
  obtain ⟨w, hd⟩ := hR hΓ' h₀' ht
  refine ⟨.cons l, A₀.lift' l :: Γ', u, W.cons, ⟨hΓ', w, hd.hasType.1⟩, hu, ?_, h0⟩
  have hd' := hd.weakN henv (Ctx.LiftN.one (A := A₀.lift' l))
  simp only [VExpr.liftN] at hd'
  exact hd'.defeqDF (.bvar Lookup.zero)

/-- **The `k = 0` core of `InstDescendUp.proof_inst`'s `.bvar k` case.**

Same shape, but the demand on `A₀` is weaker: it must *have* a sort whose level vanishes rather
than *be* one.  So the input is `PropTypeAgreeOnCtx` (plus `IsDefEq.isType`) instead of
uniqueness. -/
theorem isProofUpOn_bvar_zero (henv : env.Ordered) (hT : env.PropTypeAgreeOnCtx nv)
    {Γ₀ : List VExpr} {e₀ A₀ : VExpr} {ls : List ℕ}
    (h₀ : env.HasType nv Γ₀ e₀ A₀) (h : env.IsProofUpOn nv ls Γ₀ e₀) :
    env.IsProofUpOn nv ls (A₀ :: Γ₀) (.bvar 0) := by
  obtain ⟨l, Γ', B, u, W, hΓ', hu, he, hB, h0⟩ := h
  have h₀' : env.HasType nv Γ' (e₀.lift' l) (A₀.lift' l) := h₀.weak' henv W
  obtain ⟨w, hw, hA, h0'⟩ := propTypeAgreeOnCtx_retype henv hT hΓ' hu h₀' he hB h0
  refine ⟨.cons l, A₀.lift' l :: Γ', (A₀.lift' l).lift, w, W.cons, ⟨hΓ', w, hA⟩, hw,
    ?_, ?_, h0'⟩
  · exact .bvar Lookup.zero
  · have := hA.weakN henv (Ctx.LiftN.one (A := A₀.lift' l))
    simpa only [VExpr.liftN] using this

/-- **The `.bvar k` case of `InstDescendUp.prop_inst`**, at every `k`, with the premise's
witness context guarded.  The conclusion is the *unguarded* predicate — which is what
`InstDescendUp` asks for, and which is why the general `k` costs nothing beyond `k = 0`:
`isPropUp_liftN`'s ascent half is already free. -/
theorem prop_inst_bvar (henv : env.Ordered) (hR : env.SortRetypeOnCtx nv)
    {Γ₀ : List VExpr} {e₀ A₀ : VExpr} {k : ℕ} {Γ₁ Γ : List VExpr} {ls : List ℕ}
    (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ) (h₀ : env.HasType nv Γ₀ e₀ A₀)
    (h : env.IsPropUpOn nv ls Γ ((VExpr.bvar k).inst e₀ k)) :
    env.IsPropUp nv ls Γ₁ (.bvar k) := by
  rw [VExpr.bvar_inst_self] at h
  have h₀' := IsPropUpOn.of_liftN W.liftN_target h
  have := (isPropUpOn_bvar_zero henv hR h₀ h₀').isPropUp
  rw [← VExpr.bvar_zero_liftN k]
  exact (isPropUp_liftN henv W.liftN_source).2 this

/-- **The `.bvar k` case of `InstDescendUp.proof_inst`**, at every `k`. -/
theorem proof_inst_bvar (henv : env.Ordered) (hT : env.PropTypeAgreeOnCtx nv)
    {Γ₀ : List VExpr} {e₀ A₀ : VExpr} {k : ℕ} {Γ₁ Γ : List VExpr} {ls : List ℕ}
    (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ) (h₀ : env.HasType nv Γ₀ e₀ A₀)
    (h : env.IsProofUpOn nv ls Γ ((VExpr.bvar k).inst e₀ k)) :
    env.IsProofUp nv ls Γ₁ (.bvar k) := by
  rw [VExpr.bvar_inst_self] at h
  have h₀' := IsProofUpOn.of_liftN W.liftN_target h
  have := (isProofUpOn_bvar_zero henv hT h₀ h₀').isProofUp
  rw [← VExpr.bvar_zero_liftN k]
  exact (isProofUp_liftN henv W.liftN_source).2 this

/-! ## 5. `IsPropUpOn` is a `PropSplit`, and from the **guarded** inputs -/

/-- **`prop_sound` for the guarded lift-closed predicate, from `PropUniqOnCtx`.**

Note the improvement over `isPropUp_iff`, which needs the *unguarded* `PropUniq`: the guard on
the witness context is exactly what lets the uniqueness comparison be made there.  And
`PropUniqOnCtx` is the statement the tree has at `preludeEnv` (`PropAgreeWall`), while
`PropUniq` is not. -/
theorem isPropUpOn_iff (henv : env.Ordered) (hU : env.PropUniqOnCtx nv)
    {ls Γ A u} (hΓ : OnCtx Γ (env.IsType nv)) (hw : u.WF nv)
    (ht : env.HasType nv Γ A (.sort u)) :
    env.IsPropUpOn nv ls Γ A ↔ u.eval ls = 0 := by
  refine ⟨fun ⟨l, Γ', v, W, hΓ', hv, hA, h0⟩ => ?_,
    fun h0 => IsPropUpOn.of_hasType hΓ hw ht h0⟩
  have h := ht.weak' henv W
  simp only [VExpr.lift'] at h
  exact (hU hΓ' hv hw hA h).mp h0

/-- **`proof_sound` for the guarded lift-closed predicate, from `PropTypeAgreeOnCtx`.** -/
theorem isProofUpOn_iff (henv : env.Ordered) (hT : env.PropTypeAgreeOnCtx nv)
    {ls Γ e A u} (hΓ : OnCtx Γ (env.IsType nv)) (hw : u.WF nv)
    (he : env.HasType nv Γ e A) (hA : env.HasType nv Γ A (.sort u)) :
    env.IsProofUpOn nv ls Γ e ↔ u.eval ls = 0 := by
  refine ⟨fun ⟨l, Γ', B, v, W, hΓ', hv, he', hB, h0⟩ => ?_,
    fun h0 => IsProofUpOn.of_hasType hΓ hw he hA h0⟩
  have hA' := hA.weak' henv W
  simp only [VExpr.lift'] at hA'
  exact (hT hΓ' hv hw he' (he.weak' henv W) hB hA').mp h0

end VEnv

namespace SetModel

variable {env : VEnv} {nv : ℕ}

/-- **The guarded lift-closed `PropSplit`.**  Compare `propSplitUp`, which needs the two
*unguarded* statements; this one needs only the guarded ones, which are the ones the tree
proves. -/
noncomputable def propSplitUpOn (env : VEnv) (nv : ℕ) (henv : env.Ordered)
    (hU : env.PropUniqOnCtx nv) (hT : env.PropTypeAgreeOnCtx nv) : PropSplit env nv where
  IsPropAt := env.IsPropUpOn nv
  IsProofAt := env.IsProofUpOn nv
  decProp _ _ _ := Classical.propDecidable _
  decProof _ _ _ := Classical.propDecidable _
  prop_sound hΓ hw ht := VEnv.isPropUpOn_iff henv hU hΓ hw ht
  proof_sound hΓ hw he hA := VEnv.isProofUpOn_iff henv hT hΓ hw he hA

end SetModel

namespace VEnv

variable {env : VEnv} {nv : ℕ}

/-! ## 6. The `.bvar k` case at a `WF` environment -/

/-- **`InstDescendUp.prop_inst`'s `.bvar k` case, from `env.WF` and nothing else.**

`SortRetypeOnCtx` is discharged by `IsDefEq.uniq`.  Every hypothesis is either syntactic
(`Ctx.InstN`), the field's own typing premise, or the guard on the premise's witness context. -/
theorem prop_inst_bvar_of_wf (henv : env.WF)
    {Γ₀ : List VExpr} {e₀ A₀ : VExpr} {k : ℕ} {Γ₁ Γ : List VExpr} {ls : List ℕ}
    (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ) (h₀ : env.HasType nv Γ₀ e₀ A₀)
    (h : env.IsPropUpOn nv ls Γ ((VExpr.bvar k).inst e₀ k)) :
    env.IsPropUp nv ls Γ₁ (.bvar k) :=
  prop_inst_bvar henv.ordered (sortRetypeOnCtx_of_wf henv) W h₀ h

/-- **`InstDescendUp.proof_inst`'s `.bvar k` case, from `env.WF` and nothing else.** -/
theorem proof_inst_bvar_of_wf (henv : env.WF)
    {Γ₀ : List VExpr} {e₀ A₀ : VExpr} {k : ℕ} {Γ₁ Γ : List VExpr} {ls : List ℕ}
    (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ) (h₀ : env.HasType nv Γ₀ e₀ A₀)
    (h : env.IsProofUpOn nv ls Γ ((VExpr.bvar k).inst e₀ k)) :
    env.IsProofUp nv ls Γ₁ (.bvar k) :=
  proof_inst_bvar henv.ordered (VEnv.WF.propTypeAgreeOn henv) W h₀ h

/-- **The same, with the guarded predicate on both sides** — the shape a guarded
`InstDescendUp` would ask for. -/
theorem prop_inst_bvar_on_of_wf (henv : env.WF)
    {Γ₀ : List VExpr} {e₀ A₀ : VExpr} {ls : List ℕ}
    (h₀ : env.HasType nv Γ₀ e₀ A₀) (h : env.IsPropUpOn nv ls Γ₀ e₀) :
    env.IsPropUpOn nv ls (A₀ :: Γ₀) (.bvar 0) :=
  isPropUpOn_bvar_zero henv.ordered (sortRetypeOnCtx_of_wf henv) h₀ h

/-! ## 9. The free part of the descent, and what is left

The `.bvar k` case above is one case of `InstDescendUp.prop_inst`'s case analysis on `B`.  This
section closes the cases that are free, so the residual of the whole field is visible.

**Correction to `docs/handoff-setmodel.md` §7.3.**  That table is for `SortInstDescend0`, whose
premise and conclusion use the *canonical* predicate, and it lists `.bvar i (i ≠ k)` as free.
For `InstDescendUp`, whose predicate re-chooses a witness context, the split is different:
`i > k` is free (the variable points into `Γ₀` on both sides), while **`i < k` is not** — there
the variable points at an entry of `Γ₁` whose `Γ`-counterpart is *its own instantiation*, so the
case is a smaller instance of the same descent rather than a free transport. -/

/-- **The free part**: every `B` whose substituted form is a lift out of `Γ₀`, and which is
itself the corresponding lift out of `Γ₀` past the extra binder.  Both directions are
`isPropUp_liftN`, which is free (`PropSplitUp` §3). -/
theorem prop_inst_of_liftN (henv : env.Ordered)
    {Γ₀ : List VExpr} {e₀ A₀ : VExpr} {k : ℕ} {Γ₁ Γ : List VExpr} {ls : List ℕ} {B C : VExpr}
    (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ) (h1 : B.inst e₀ k = C.liftN k 0)
    (h2 : B = C.liftN (k+1) 0) (h : env.IsPropUp nv ls Γ (B.inst e₀ k)) :
    env.IsPropUp nv ls Γ₁ B := by
  rw [h1] at h
  have h0 := (isPropUp_liftN henv W.liftN_target).1 h
  have h1' := (isPropUp_liftN henv (Ctx.LiftN.one (A := A₀))).2 h0
  have h2' := (isPropUp_liftN henv W.liftN_source).2 h1'
  rw [h2]
  rwa [VExpr.liftN_liftN, Nat.add_comm 1 k] at h2'

/-- The same for `IsProofUp`. -/
theorem proof_inst_of_liftN (henv : env.Ordered)
    {Γ₀ : List VExpr} {e₀ A₀ : VExpr} {k : ℕ} {Γ₁ Γ : List VExpr} {ls : List ℕ} {B C : VExpr}
    (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ) (h1 : B.inst e₀ k = C.liftN k 0)
    (h2 : B = C.liftN (k+1) 0) (h : env.IsProofUp nv ls Γ (B.inst e₀ k)) :
    env.IsProofUp nv ls Γ₁ B := by
  rw [h1] at h
  have h0 := (isProofUp_liftN henv W.liftN_target).1 h
  have h1' := (isProofUp_liftN henv (Ctx.LiftN.one (A := A₀))).2 h0
  have h2' := (isProofUp_liftN henv W.liftN_source).2 h1'
  rw [h2]
  rwa [VExpr.liftN_liftN, Nat.add_comm 1 k] at h2'

/-- **`.sort`, `.const`, and every other closed `B`: free.** -/
theorem prop_inst_closed (henv : env.Ordered)
    {Γ₀ : List VExpr} {e₀ A₀ : VExpr} {k : ℕ} {Γ₁ Γ : List VExpr} {ls : List ℕ} {B : VExpr}
    (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ) (hB : B.ClosedN 0)
    (h : env.IsPropUp nv ls Γ (B.inst e₀ k)) : env.IsPropUp nv ls Γ₁ B :=
  prop_inst_of_liftN henv W
    (by rw [hB.instN_eq (Nat.zero_le _), hB.liftN_eq (Nat.le_refl _)])
    (hB.liftN_eq (Nat.le_refl _)).symm h

theorem proof_inst_closed (henv : env.Ordered)
    {Γ₀ : List VExpr} {e₀ A₀ : VExpr} {k : ℕ} {Γ₁ Γ : List VExpr} {ls : List ℕ} {B : VExpr}
    (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ) (hB : B.ClosedN 0)
    (h : env.IsProofUp nv ls Γ (B.inst e₀ k)) : env.IsProofUp nv ls Γ₁ B :=
  proof_inst_of_liftN henv W
    (by rw [hB.instN_eq (Nat.zero_le _), hB.liftN_eq (Nat.le_refl _)])
    (hB.liftN_eq (Nat.le_refl _)).symm h

/-- **`.bvar i` with `i > k`: free.**  The variable points into `Γ₀` on both sides. -/
theorem prop_inst_bvar_high (henv : env.Ordered)
    {Γ₀ : List VExpr} {e₀ A₀ : VExpr} {k j : ℕ} {Γ₁ Γ : List VExpr} {ls : List ℕ}
    (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ)
    (h : env.IsPropUp nv ls Γ ((VExpr.bvar (k+j+1)).inst e₀ k)) :
    env.IsPropUp nv ls Γ₁ (.bvar (k+j+1)) :=
  prop_inst_of_liftN henv W (C := .bvar j)
    (by
      show VExpr.instVar (k+j+1) e₀ k = _
      rw [VExpr.instVar, if_neg (by omega), if_neg (by omega)]
      simp [VExpr.liftN, liftVar])
    (by simp [VExpr.liftN, liftVar]; omega) h

theorem proof_inst_bvar_high (henv : env.Ordered)
    {Γ₀ : List VExpr} {e₀ A₀ : VExpr} {k j : ℕ} {Γ₁ Γ : List VExpr} {ls : List ℕ}
    (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ)
    (h : env.IsProofUp nv ls Γ ((VExpr.bvar (k+j+1)).inst e₀ k)) :
    env.IsProofUp nv ls Γ₁ (.bvar (k+j+1)) :=
  proof_inst_of_liftN henv W (C := .bvar j)
    (by
      show VExpr.instVar (k+j+1) e₀ k = _
      rw [VExpr.instVar, if_neg (by omega), if_neg (by omega)]
      simp [VExpr.liftN, liftVar])
    (by simp [VExpr.liftN, liftVar]; omega) h

end VEnv

namespace VEnv

variable {env : VEnv} {nv : ℕ}

/-! ## 7. The residual, named in both framings -/

/-- **The price of keeping `InstDescendUp`'s premise unguarded**: normalising `IsPropUp`'s own
witness context to a well-formed one. -/
def PropUpNormalise (env : VEnv) (nv : ℕ) : Prop :=
  ∀ {ls : List ℕ} {Γ : List VExpr} {A : VExpr}, OnCtx Γ (env.IsType nv) →
    env.IsPropUp nv ls Γ A → env.IsPropUpOn nv ls Γ A

/-- **Strengthening with the well-formedness guard on the *larger* context deleted.**

`IsDefEqU.weakN_iff` (the tree's hole) carries `OnCtx Γ' (env.IsType U)` on the big context;
here the big context is `IsPropUp`'s witness context, which is exactly the thing that may be
junk.  So this is a **strictly stronger statement than the tree's `weakN_iff`**, and not one of
the four holes. -/
def UnguardedStrengthen (env : VEnv) (nv : ℕ) : Prop :=
  ∀ {l : Lift} {Γ Γ' : List VExpr} {e A : VExpr}, Ctx.Lift' l Γ Γ' →
    env.HasType nv Γ' (e.lift' l) (A.lift' l) → env.HasType nv Γ e A

theorem propUpNormalise_of_unguardedStrengthen (h : env.UnguardedStrengthen nv) :
    env.PropUpNormalise nv := by
  rintro ls Γ A hΓ ⟨l, Γ', u, W, hu, ht, h0⟩
  exact IsPropUpOn.of_hasType hΓ hu (h W (by simpa using ht)) h0

/-- **The `.bvar k` case with `InstDescendUp`'s own (unguarded) premise**, at the price of
`PropUpNormalise` plus `OnCtx` on the substituted context. -/
theorem prop_inst_bvar_of_normalise (henv : env.WF) (hN : env.PropUpNormalise nv)
    {Γ₀ : List VExpr} {e₀ A₀ : VExpr} {k : ℕ} {Γ₁ Γ : List VExpr} {ls : List ℕ}
    (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ) (hΓ : OnCtx Γ (env.IsType nv))
    (h₀ : env.HasType nv Γ₀ e₀ A₀)
    (h : env.IsPropUp nv ls Γ ((VExpr.bvar k).inst e₀ k)) :
    env.IsPropUp nv ls Γ₁ (.bvar k) :=
  prop_inst_bvar_of_wf henv W h₀ (hN hΓ h)

/-- **The price of the other framing** — swapping the predicate for the guarded one.
`PropSplit.Stable.prop_liftN`'s `←` half asks for a well-formed context above `Γ'`, and `Γ'` is
unconstrained there; if it carries a junk entry, every context above it carries it too.  Adding
`OnCtx Γ'` to `Stable`'s four fields — the edit `PropSplit`'s own fields received on
2026-09-02 — is what discharges this. -/
def PropUpOnLiftAscend (env : VEnv) (nv : ℕ) : Prop :=
  ∀ {n k : ℕ} {Γ Γ' : List VExpr} {ls : List ℕ} {A : VExpr}, Ctx.LiftN n k Γ Γ' →
    env.IsPropUpOn nv ls Γ A → env.IsPropUpOn nv ls Γ' (A.liftN n k)

/-- …and it **is** free once the target context is guarded and the source witness is the
canonical one, which is the shape `prop_sound` produces.  So the obligation is about `Stable`'s
missing guard, not about new mathematics. -/
theorem isPropUpOn_liftN_up (henv : env.Ordered) {n k : ℕ} {Γ Γ' : List VExpr}
    (W : Ctx.LiftN n k Γ Γ') (hΓ' : OnCtx Γ' (env.IsType nv))
    {ls : List ℕ} {A : VExpr} {u : VLevel} (hu : u.WF nv)
    (ht : env.HasType nv Γ A (.sort u)) (h0 : u.eval ls = 0) :
    env.IsPropUpOn nv ls Γ' (A.liftN n k) := by
  refine IsPropUpOn.of_hasType hΓ' hu ?_ h0
  have := ht.weakN henv W
  simpa only [VExpr.liftN] using this

end VEnv

/-! ## 8. Anti-vacuity, at `preludeEnv` -/

namespace SetModel

namespace InstDescendBvar

open Lean4Lean.VEnv

/-! ## 8b. Route B: the `proof_inst` half of the `.bvar k` case, **`sorryAx`-free**

`propTypeAgreeOnCtx_retype` is `sorryAx`-free (see the census), and so is `proof_inst_bvar`.  So
composing with `PropAgreeWall.propTypeAgreeOnCtx_of_stratifiedN` — route B, also `sorryAx`-free —
closes `InstDescendUp 0`'s `proof_inst` `.bvar k` case **with no hole of any kind**, conditional
only on the two `∀ n` statements the `Theory/Typing` stream already owns.  The `prop_inst` half
does *not* factor this way: it needs `A₀` convertible to a sort, which is `IsDefEq.uniq`. -/
theorem proof_inst_bvar_of_stratifiedN (henv : VEnv.Ordered env)
    (pta : ∀ n, env.PropTypeAgreeN 0 n) (pun : ∀ n, env.PropUniqN 0 n)
    {Γ₀ : List VExpr} {e₀ A₀ : VExpr} {k : ℕ} {Γ₁ Γ : List VExpr} {ls : List ℕ}
    (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ) (h₀ : env.HasType 0 Γ₀ e₀ A₀)
    (h : env.IsProofUpOn 0 ls Γ ((VExpr.bvar k).inst e₀ k)) :
    env.IsProofUp 0 ls Γ₁ (.bvar k) :=
  VEnv.proof_inst_bvar henv (PropAgreeWall.propTypeAgreeOnCtx_of_stratifiedN henv pta pun) W h₀ h

/-- **The uniqueness input holds at `preludeEnv`**, with no hypotheses. -/
theorem preludeEnv_sortRetypeOnCtx : preludeEnv.SortRetypeOnCtx 0 :=
  sortRetypeOnCtx_of_wf preludeEnv_WF

/-- **The guarded lift-closed `PropSplit` exists at `preludeEnv`, as data** — from the two
*guarded* imports, both of which are theorems there. -/
noncomputable def propSplitUpOnPreludeEnv : PropSplit preludeEnv 0 :=
  propSplitUpOn preludeEnv 0 preludeEnv_ordered
    PropAgreeWall.preludeEnv_propUniqOnCtx PropAgreeWall.preludeEnv_propTypeAgreeOnCtx

/-- **A genuine instance of the `.bvar k` case, at `k = 0`, at `preludeEnv`.**

`Γ₀ = []`, `A₀ = Prop`, `e₀ = ∀ p : Prop, p` (`= falseProp`), `Γ₁ = [Prop]`, `Γ = []` — the same
configuration as `InstDescendAudit.sortInstDescend0_nonvacuous`, so the substitution really
substitutes.  **Both** the premise and the conclusion hold, so neither side of the implication
is empty. -/
theorem bvar_zero_instance (ls : List ℕ) :
    preludeEnv.IsPropUpOn 0 ls []
        ((VExpr.bvar 0).inst (.forallE (.sort .zero) (.bvar 0)) 0) ∧
      preludeEnv.IsPropUp 0 ls [(VExpr.sort .zero : VExpr)] (.bvar 0) := by
  have h₀ : preludeEnv.HasType 0 [] (.forallE (.sort .zero) (.bvar 0)) (.sort .zero) :=
    allProp_hasType
  have hpre : preludeEnv.IsPropUpOn 0 ls []
      ((VExpr.bvar 0).inst (.forallE (.sort .zero) (.bvar 0)) 0) := by
    rw [VExpr.bvar_inst_self]
    exact IsPropUpOn.of_hasType (u := .zero) trivial trivial
      (by simpa [VExpr.liftN, liftVar] using h₀) rfl
  exact ⟨hpre, prop_inst_bvar_of_wf preludeEnv_WF (Γ₀ := []) (A₀ := .sort .zero)
    (k := 0) .zero h₀ hpre⟩

/-- **…and at `k = 1`, with a junk *conclusion* context.**

`Γ₀ = []`, `A₀ = Prop`, `k = 1`, `Γ₁ = [.bvar 0, Prop]`, `Γ = [∀ p : Prop, p]`.  The conclusion
context is not `OnCtx` (`PropAgreeWall.not_isType_bvar`), and the theorem still delivers — which
is the check that the guard sits on the *premise* only. -/
theorem bvar_one_instance (ls : List ℕ) :
    preludeEnv.IsPropUpOn 0 ls [(.forallE (.sort .zero) (.bvar 0) : VExpr)]
        ((VExpr.bvar 1).inst (.forallE (.sort .zero) (.bvar 0)) 1) ∧
      preludeEnv.IsPropUp 0 ls [(.bvar 0 : VExpr), (VExpr.sort .zero : VExpr)] (.bvar 1) := by
  have h₀ : ∀ Γ, preludeEnv.HasType 0 Γ (.forallE (.sort .zero) (.bvar 0)) (.sort .zero) :=
    fun _ => allProp_hasType
  have hΓ : OnCtx [(.forallE (.sort .zero) (.bvar 0) : VExpr)] (preludeEnv.IsType 0) :=
    ⟨trivial, _, h₀ []⟩
  have hW : Ctx.InstN ([] : List VExpr) (.forallE (.sort .zero) (.bvar 0)) (.sort .zero) 1
      [(.bvar 0 : VExpr), (VExpr.sort .zero : VExpr)]
      [(.forallE (.sort .zero) (.bvar 0) : VExpr)] := .succ .zero
  have hpre : preludeEnv.IsPropUpOn 0 ls [(.forallE (.sort .zero) (.bvar 0) : VExpr)]
      ((VExpr.bvar 1).inst (.forallE (.sort .zero) (.bvar 0)) 1) := by
    rw [VExpr.bvar_inst_self]
    exact IsPropUpOn.of_hasType (u := .zero) hΓ trivial
      (by simpa [VExpr.liftN, liftVar] using h₀ _) rfl
  exact ⟨hpre, prop_inst_bvar_of_wf preludeEnv_WF hW (h₀ []) hpre⟩

/-- **The premise is not constant-true**: `Prop` is not a proposition, so `IsPropUpOn` really
does discriminate.  Uses the *guarded* `PropUniqOnCtx`, which is a theorem at `preludeEnv` —
`not_isPropUp_sort` needs the unguarded `PropUniq`, which is not. -/
theorem not_isPropUpOn_sort (ls : List ℕ) :
    ¬ preludeEnv.IsPropUpOn 0 ls [] (.sort .zero) := by
  have h : preludeEnv.HasType 0 [] (.sort .zero) (.sort (.succ .zero)) :=
    VEnv.IsDefEq.sortDF trivial trivial rfl
  rw [isPropUpOn_iff (Γ := []) (ls := ls) (u := .succ .zero) preludeEnv_ordered
    PropAgreeWall.preludeEnv_propUniqOnCtx trivial trivial h]
  simp [VLevel.eval]

end InstDescendBvar

end SetModel

end Lean4Lean

/-! ## Axiom census -/

#print axioms Lean4Lean.Ctx.InstN.eq_append
#print axioms Lean4Lean.Ctx.InstN.liftN_target
#print axioms Lean4Lean.Ctx.InstN.liftN_source
#print axioms Lean4Lean.VExpr.bvar_inst_self
#print axioms Lean4Lean.VExpr.bvar_zero_liftN
#print axioms Lean4Lean.VEnv.sortRetypeOnCtx_of_wf
#print axioms Lean4Lean.VEnv.propTypeAgreeOnCtx_retype
#print axioms Lean4Lean.VEnv.IsPropUpOn.isPropUp
#print axioms Lean4Lean.VEnv.IsProofUpOn.isProofUp
#print axioms Lean4Lean.VEnv.IsPropUpOn.of_hasType
#print axioms Lean4Lean.VEnv.IsProofUpOn.of_hasType
#print axioms Lean4Lean.VEnv.IsPropUpOn.of_lift'
#print axioms Lean4Lean.VEnv.IsProofUpOn.of_lift'
#print axioms Lean4Lean.VEnv.IsPropUpOn.of_liftN
#print axioms Lean4Lean.VEnv.IsProofUpOn.of_liftN
#print axioms Lean4Lean.VEnv.isPropUpOn_bvar_zero
#print axioms Lean4Lean.VEnv.isProofUpOn_bvar_zero
#print axioms Lean4Lean.VEnv.prop_inst_bvar
#print axioms Lean4Lean.VEnv.proof_inst_bvar
#print axioms Lean4Lean.VEnv.isPropUpOn_iff
#print axioms Lean4Lean.VEnv.isProofUpOn_iff
#print axioms Lean4Lean.SetModel.propSplitUpOn
#print axioms Lean4Lean.VEnv.prop_inst_bvar_of_wf
#print axioms Lean4Lean.VEnv.proof_inst_bvar_of_wf
#print axioms Lean4Lean.VEnv.prop_inst_bvar_on_of_wf
#print axioms Lean4Lean.VEnv.prop_inst_of_liftN
#print axioms Lean4Lean.VEnv.proof_inst_of_liftN
#print axioms Lean4Lean.VEnv.prop_inst_closed
#print axioms Lean4Lean.VEnv.proof_inst_closed
#print axioms Lean4Lean.VEnv.prop_inst_bvar_high
#print axioms Lean4Lean.VEnv.proof_inst_bvar_high
#print axioms Lean4Lean.VEnv.propUpNormalise_of_unguardedStrengthen
#print axioms Lean4Lean.VEnv.prop_inst_bvar_of_normalise
#print axioms Lean4Lean.VEnv.isPropUpOn_liftN_up
#print axioms Lean4Lean.SetModel.InstDescendBvar.proof_inst_bvar_of_stratifiedN
#print axioms Lean4Lean.SetModel.InstDescendBvar.preludeEnv_sortRetypeOnCtx
#print axioms Lean4Lean.SetModel.InstDescendBvar.propSplitUpOnPreludeEnv
#print axioms Lean4Lean.SetModel.InstDescendBvar.bvar_zero_instance
#print axioms Lean4Lean.SetModel.InstDescendBvar.bvar_one_instance
#print axioms Lean4Lean.SetModel.InstDescendBvar.not_isPropUpOn_sort
