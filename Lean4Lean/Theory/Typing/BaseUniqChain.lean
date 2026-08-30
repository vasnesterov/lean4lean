import Lean4Lean.Theory.Typing.ProofRetypeHeads

/-!
# Breaking `peelEq`'s `defeq` case: keep the **chain**, not the equation

`Theory/Typing/BaseUniqTerm.lean` proves `BaseUniq` by structural recursion on the term and is
left with one hypothesis it cannot localise, `SortUniq`.  Its §"The localisation goes through
at the subject and not at the type" records the exact failing step:

> `uniqStrongAt_of_baseUniqAt` goes through `HasTypeStrong.peelEq`, whose `defeq` case applies
> `SortUniq` at the derivation's intermediate **type** `A` — an arbitrary term with no
> structural relation to the subject.

**That reading is corrected here, and the correction is `ORCHESTRATOR.md` working rule 5:
*keep the reason, not the conclusion*.**  `peelEq` is an inversion, and what it throws away is
that the `defeq` wrappers form a *walk*.  The walk itself is all the consumers need; only the
demand to hand back a single **equation** forces two conversions indexed at different sorts to
be composed, and that composition is the whole of `SortUniq`'s job there.

So state the conclusion as a chain:

```lean
inductive ConvC (env) (U) (Γ) : VExpr → VExpr → Prop
  | refl : ConvC env U Γ A A
  | step : env.IsDefEqStrong U Γ A B (.sort u) → ConvC env U Γ B C → ConvC env U Γ A C
```

with the links **not** required to be at the same sort.  Then

| | `ProofRetypeHeads` / `BaseUniqTerm` | here |
|---|---|---|
| peel a `defeq` chain | `peelEq`: `Ordered`, `SortUniq`, `CtxStrong` | `peelChain`: **nothing** |
| base ⇒ full unique typing | `uniqStrongAt_of_baseUniqAt`: `Ordered`, `SortUniq` | `uniqStrongCAt_of_baseUniqCAt`: **nothing** |
| `.forallE` head | `SortUniq`, **no** recursive call | `ConvSortInv`, recursion at **domain and body** |
| `.lam` head | `Ordered` + recursion at body | same |
| `.app` head | `Ordered` + `PiInv` + recursion at fn | `Ordered` + `ConvPiInv` + recursion at fn |
| `.bvar`/`.const`/`.sort` | free | free |

`peelChain` and `uniqStrongCAt_of_baseUniqCAt` are checked to depend on `[propext]` alone.
Nowhere in this file are two conversions at different sorts composed, so the four-place
obstruction (`docs/handoff-injectivity.md` §2) never arises.

## What is gained, and what is not — read this before quoting the headline

The result is

```lean
retypes_of_convInv : Ordered env → ConvSortInv env U → ConvPiInv env U →
  IsDefEqStrong U Γ e₁ e₂ A → CtxStrong env U Γ → Retypes env U Γ e₁ e₂
```

with **no `SortUniq`**.  But `ConvSortInv` and `ConvPiInv` are the *chain* forms of sort- and
Π-injectivity, and both directions of the comparison are machine-checked here:

* `convSortInv_of_sortUniq`, `convPiInv_of_sortUniq_piInv` — the old hypotheses imply the new
  ones, so the new theorem subsumes the old one (`retypes_of_sortUniq_piInv_via_chain`
  re-derives `BaseUniqTerm.retypes_of_sortUniq_piInv` verbatim);
* `sortUniq_of_convInv` — the new hypotheses give `SortUniq` straight back, and
  `sortUniq_iff_convSortInv` states the resulting equivalence.

**So the corner's circle is not cut.**  What changes is *where* the demand sits.  Before, the
demand was `SortUniq` — a statement about two sort typings of an arbitrary term — consumed at
arbitrary intermediate types inside arbitrary derivations, at a place no recursion on the
subject reaches.  Now the demand is `ConvSortInv` — *a chain between two syntactic sorts forces
the levels equivalent* — and everything else `SortUniq` was doing (composing a chain into one
conversion) has been shown to be bookkeeping the chain absorbs.  `peelEq_of_peelChain` makes
that split explicit: `peelEq` *is* `peelChain` followed by `ConvC.collapse`, and `collapse` is
the only place `SortUniq` is spent.

## Non-vacuity and the negative controls

`baseUniqCAt_forallE`'s two recursive calls are new — `BaseUniqTerm.baseUniqAt_forallE` makes
none.  Both are fired at Π-terms whose two base types are syntactically different
(`forallE_body_fires`, `forallE_domain_fires`), and the two witnesses differ in *which*
subterm carries the difference.  Neither call can be dropped:
`forallE_body_call_not_droppable` and `forallE_domain_call_not_droppable` refute the two
one-call readings outright, at the level algebra (`imax` is not determined by either argument
alone).  `baseUniqCAt_app_fires` re-fires the `.app` branch through the chain-valued
conclusion.

`ConvSortInv` and `ConvPiInv` are *carried* by those witnesses, not discharged: firing a branch
is not evidence the hypotheses are jointly satisfiable (`ORCHESTRATOR.md` rule 4).

## What is *not* claimed

Every implication is an **upper** bound.  Nothing here shows `ConvSortInv` is necessary, and no
refutation of it is offered.  No cone moves: this file is imported only by
`BaseUniqTerm.lean`, which reaches nothing in `Verify/`.

## Axioms

Checked by the `#print axioms` block at the end; none mentions `sorryAx`, none mentions
`Classical.choice`.
-/namespace Lean4Lean
namespace VEnv

variable {env : VEnv} {U : Nat}

/-- **A conversion chain.**  Each link is an `IsDefEqStrong` at a syntactic sort, and the
links are *not* required to be at the *same* sort.  This is the whole point: `ConvC` is what
`HasTypeStrong.peelEq` would produce if it did not insist on composing the chain into a single
equation, and composing is the only step that costs anything. -/
inductive ConvC (env : VEnv) (U : Nat) (Γ : List VExpr) : VExpr → VExpr → Prop where
  | refl {A : VExpr} : ConvC env U Γ A A
  | step {A B C : VExpr} {u : VLevel} :
      env.IsDefEqStrong U Γ A B (.sort u) → ConvC env U Γ B C → ConvC env U Γ A C

namespace ConvC

theorem one {Γ : List VExpr} {A B : VExpr} {u : VLevel}
    (h : env.IsDefEqStrong U Γ A B (.sort u)) : ConvC env U Γ A B := .step h .refl

theorem trans {Γ : List VExpr} {A B C : VExpr}
    (h1 : ConvC env U Γ A B) (h2 : ConvC env U Γ B C) : ConvC env U Γ A C := by
  induction h1 with
  | refl => exact h2
  | step h _ ih => exact .step h (ih h2)

theorem symm {Γ : List VExpr} {A B : VExpr} (h : ConvC env U Γ A B) : ConvC env U Γ B A := by
  induction h with
  | refl => exact .refl
  | step h _ ih => exact ih.trans (one h.symm)

/-- **Transport along a chain is free**: each link is one `defeqDF`, and no two links are ever
composed. -/
theorem transport (henv : Ordered env) {Γ : List VExpr} (hΓ : CtxStrong env U Γ)
    {A B : VExpr} (h : ConvC env U Γ A B) :
    ∀ {e₁ e₂ : VExpr}, env.IsDefEqStrong U Γ e₁ e₂ A → env.IsDefEqStrong U Γ e₁ e₂ B := by
  induction h with
  | refl => exact id
  | step h _ ih => exact fun hd => ih (.defeqDF (h.defeq.sort_r henv hΓ.defeq) h hd)

end ConvC

/-- **`peelEq` with the equation replaced by a chain — and it takes no hypothesis at all.**

Compare `HasTypeStrong.peelEq` (`ProofRetypeHeads.lean`), which needs `Ordered env` *and*
`SortUniq`, both spent entirely in its `defeq` case in order to bring two conversions indexed
at different sorts to a common sort.  Here the `defeq` case is one `ConvC.step`. -/
theorem HasTypeStrong.peelChain :
    ∀ {Γ : List VExpr} {e B : VExpr} {b : Bool}, env.HasTypeStrong U Γ e B b →
      ∃ B₀, env.HasTypeStrong U Γ e B₀ false ∧ ConvC env U Γ B₀ B := by
  intro Γ e B b H
  induction H with
  | bvar h1 h2 h3 _ => exact ⟨_, .bvar h1 h2 h3, .refl⟩
  | sort' h1 h2 h3 => exact ⟨_, .sort' h1 h2 h3, .refl⟩
  | const h1 h2 h3 h4 h5 h6 _ _ => exact ⟨_, .const h1 h2 h3 h4 h5 h6, .refl⟩
  | app h1 h2 h3 h4 h5 h6 h7 h8 _ _ _ _ _ _ => exact ⟨_, .app h1 h2 h3 h4 h5 h6 h7 h8, .refl⟩
  | lam h1 h2 h3 h4 h5 h6 _ _ _ _ => exact ⟨_, .lam h1 h2 h3 h4 h5 h6, .refl⟩
  | forallE h1 h2 h3 h4 _ _ => exact ⟨_, .forallE h1 h2 h3 h4, .refl⟩
  | base _ ih => exact ih
  | defeq _ h2 _ _ _ _ _ ih5 =>
    obtain ⟨B₀, hb, e1⟩ := ih5
    exact ⟨B₀, hb, e1.trans (.one h2)⟩

/-! ## The chain-valued predicates -/

/-- `BaseUniq` with the conclusion a chain instead of a single conversion. -/
def BaseUniqC (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {e A B : VExpr}, CtxStrong env U Γ →
    env.HasTypeStrong U Γ e A false → env.HasTypeStrong U Γ e B false → ConvC env U Γ A B

/-- `BaseUniqC` at a single subject term. -/
def BaseUniqCAt (env : VEnv) (U : Nat) (e : VExpr) : Prop :=
  ∀ {Γ : List VExpr} {A B : VExpr}, CtxStrong env U Γ →
    env.HasTypeStrong U Γ e A false → env.HasTypeStrong U Γ e B false → ConvC env U Γ A B

/-- `UniqStrong` with the conclusion a chain, at a single subject term. -/
def UniqStrongCAt (env : VEnv) (U : Nat) (e : VExpr) : Prop :=
  ∀ {Γ : List VExpr} {A B : VExpr}, CtxStrong env U Γ →
    env.HasTypeStrong U Γ e A true → env.HasTypeStrong U Γ e B true → ConvC env U Γ A B

/-- **The step that `SortUniq` was paying for, now free.**

`BaseUniqTerm.uniqStrongAt_of_baseUniqAt` takes `Ordered env` and `env.SortUniq U`, and spends
both inside `peelEq`.  With the conclusion stated as a chain there is nothing to spend them
on: peel each side (free), put the two chains together with the base-level fact in the middle,
and the result is a chain. -/
theorem uniqStrongCAt_of_baseUniqCAt {e : VExpr} (hbu : BaseUniqCAt env U e) :
    UniqStrongCAt env U e := by
  intro Γ A B hΓ h1 h2
  obtain ⟨A₀, hA₀, e1⟩ := h1.peelChain
  obtain ⟨B₀, hB₀, e2⟩ := h2.peelChain
  exact (e1.symm.trans (hbu hΓ hA₀ hB₀)).trans e2

/-! ## The two chain-inversion hypotheses

These are the *only* hypotheses the development below takes beyond `Ordered env`.  Each is the
chain form of one of the corner's two named halves. -/

/-- **Sort injectivity along a chain.**  The chain form of `IsDefEqU.sort_inv`. -/
def ConvSortInv (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {u v : VLevel}, CtxStrong env U Γ →
    ConvC env U Γ (.sort u) (.sort v) → u ≈ v

/-- **Π-injectivity along a chain.**  The chain form of `PiInv`. -/
def ConvPiInv (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {A B A' B' : VExpr}, CtxStrong env U Γ →
    ConvC env U Γ (.forallE A B) (.forallE A' B') →
    ConvC env U Γ A A' ∧ ConvC env U (A::Γ) B B'

/-! ## Chains are closed under the two congruences the heads need -/

/-- Π-formation applies to a chain **link by link**; the sorts of the links never have to
agree, because the conclusion is a chain too. -/
theorem ConvC.forallE (henv : Ordered env) {Γ : List VExpr} {D : VExpr} {u : VLevel}
    (hΓ' : CtxStrong env U (D::Γ)) (hu : u.WF U)
    (hD : env.IsDefEqStrong U Γ D D (.sort u)) {B₁ B₂ : VExpr}
    (h : ConvC env U (D::Γ) B₁ B₂) :
    ConvC env U Γ (.forallE D B₁) (.forallE D B₂) := by
  induction h with
  | refl => exact .refl
  | step hl _ ih =>
    exact .step (.forallEDF hu (hl.defeq.sort_r henv hΓ'.defeq) hD hl hl) ih

/-- Instantiation applies to a chain link by link. -/
theorem ConvC.inst (henv : Ordered env) {Γ : List VExpr} (hΓ : CtxStrong env U Γ)
    {A a : VExpr} (ha : env.IsDefEqStrong U Γ a a A) {B₁ B₂ : VExpr}
    (h : ConvC env U (A::Γ) B₁ B₂) :
    ConvC env U Γ (B₁.inst a) (B₂.inst a) := by
  induction h with
  | refl => exact .refl
  | step hl _ ih =>
    exact .step ((IsDefEq.instDF henv hΓ.defeq hl.defeq ha.defeq).strong henv hΓ.defeq) ih

/-! ## The six heads, with the conclusion a chain -/

theorem baseUniqCAt_bvar {i : Nat} : BaseUniqCAt env U (.bvar i) := by
  intro Γ A B _ h1 h2
  cases h1 with
  | bvar l1 u1 t1 => cases h2 with | bvar l2 u2 t2 => cases l1.uniq l2; exact .refl

theorem baseUniqCAt_const {c : Name} {ls : List VLevel} : BaseUniqCAt env U (.const c ls) := by
  intro Γ A B _ h1 h2
  cases h1 with
  | const c1 c2 c3 c4 c5 c6 =>
    cases h2 with
    | const d1 d2 d3 d4 d5 d6 => cases c1.symm.trans d1; exact .refl

theorem baseUniqCAt_sort {l : VLevel} : BaseUniqCAt env U (.sort l) := by
  intro Γ A B _ h1 h2
  cases h1 with
  | sort' a1 a2 a3 =>
    cases h2 with
    | sort' b1 b2 b3 =>
      exact .one (.sortDF (l := .succ _) (l' := .succ _) a2 b2
        (VLevel.succ_congr (a3.symm.trans b3)))

/-- **`.forallE`, and this is the row that changes.**  `BaseUniqTerm.baseUniqAt_forallE` takes
`SortUniq` — a statement about arbitrary terms — and makes no recursive call.  Here the two
level equivalences come from the recursion at the Π's **own domain and body**, both proper
subterms, plus `ConvSortInv`. -/
theorem baseUniqCAt_forallE (hsi : ConvSortInv env U) {D b : VExpr}
    (hdom : UniqStrongCAt env U D) (hbody : UniqStrongCAt env U b) :
    BaseUniqCAt env U (.forallE D b) := by
  intro Γ A B hΓ h1 h2
  cases h1 with
  | forallE a1 a2 a3 a4 =>
    cases h2 with
    | forallE b1 b2 b3 b4 =>
      have hΓ' : CtxStrong env U (D::Γ) := ⟨hΓ, _, a3.refl⟩
      have hu := hsi hΓ (hdom hΓ a3 b3)
      have hv := hsi hΓ' (hbody hΓ' a4 b4)
      exact .one (.sortDF (l := .imax _ _) (l' := .imax _ _) ⟨a1, a2⟩ ⟨b1, b2⟩
        (VLevel.imax_congr hu hv))

theorem baseUniqCAt_lam (henv : Ordered env) {D b : VExpr}
    (hbody : UniqStrongCAt env U b) : BaseUniqCAt env U (.lam D b) := by
  intro Γ A B hΓ h1 h2
  cases h1 with
  | lam a1 a2 a3 a4 a5 a6 =>
    cases h2 with
    | lam b1 b2 b3 b4 b5 b6 =>
      have hΓ' : CtxStrong env U (D::Γ) := ⟨hΓ, _, a3.refl⟩
      exact ConvC.forallE henv hΓ' a1 a3.refl (hbody hΓ' a5 b5)

theorem baseUniqCAt_app (henv : Ordered env) (hpi : ConvPiInv env U) {f a : VExpr}
    (hfn : UniqStrongCAt env U f) : BaseUniqCAt env U (.app f a) := by
  intro Γ A B hΓ h1 h2
  cases h1 with
  | app a1 a2 a3 a4 a5 a6 a7 a8 =>
    cases h2 with
    | app b1 b2 b3 b4 b5 b6 b7 b8 =>
      exact ConvC.inst henv hΓ a7.refl (hpi hΓ (hfn hΓ a6 b6)).2

/-! ## The recursion -/

/-- **`BaseUniqC` at every term, by structural recursion on the term** — from `Ordered env`
and the two chain-inversion hypotheses, and **nothing else**.  In particular no `SortUniq`. -/
theorem baseUniqCAt_of (henv : Ordered env) (hsi : ConvSortInv env U) (hpi : ConvPiInv env U) :
    ∀ e : VExpr, BaseUniqCAt env U e
  | .bvar _ => baseUniqCAt_bvar
  | .sort _ => baseUniqCAt_sort
  | .const _ _ => baseUniqCAt_const
  | .forallE D b => baseUniqCAt_forallE hsi
      (uniqStrongCAt_of_baseUniqCAt (baseUniqCAt_of henv hsi hpi D))
      (uniqStrongCAt_of_baseUniqCAt (baseUniqCAt_of henv hsi hpi b))
  | .lam _ b => baseUniqCAt_lam henv
      (uniqStrongCAt_of_baseUniqCAt (baseUniqCAt_of henv hsi hpi b))
  | .app f _ => baseUniqCAt_app henv hpi
      (uniqStrongCAt_of_baseUniqCAt (baseUniqCAt_of henv hsi hpi f))

theorem baseUniqC_of (henv : Ordered env) (hsi : ConvSortInv env U) (hpi : ConvPiInv env U) :
    BaseUniqC env U := fun hΓ h1 h2 => baseUniqCAt_of henv hsi hpi _ hΓ h1 h2

/-! ## `retypes`, from the chain form -/

/-- `ProofRetypeHeads.retypeAt_of_baseUniq`, with the single conversion replaced by a chain and
`defeqDF` replaced by `ConvC.transport`. -/
theorem retypeAtC_of_baseUniqC (henv : Ordered env) (hbu : BaseUniqC env U)
    {Γ : List VExpr} {e₁ e₂ X : VExpr} (hΓ : CtxStrong env U Γ)
    {A : VExpr} (canon : env.IsDefEqStrong U Γ e₁ e₂ A)
    (hor : env.HasTypeStrong U Γ e₁ X false ∨ env.HasTypeStrong U Γ e₂ X false) :
    env.IsDefEqStrong U Γ e₁ e₂ X := by
  cases hor with
  | inl hb =>
    obtain ⟨P₀, hP₀, t⟩ := canon.hasType'.1.peelDown
    exact (hbu hΓ hP₀ hb).transport henv hΓ (t canon)
  | inr hb =>
    obtain ⟨P₀, hP₀, t⟩ := canon.hasType'.2.peelDown
    exact ((hbu hΓ hP₀ hb).transport henv hΓ (t canon.symm)).symm

theorem retypes_of_baseUniqC (henv : Ordered env) (hbu : BaseUniqC env U)
    {Γ : List VExpr} {e₁ e₂ A : VExpr} (H : env.IsDefEqStrong U Γ e₁ e₂ A)
    (hΓ : CtxStrong env U Γ) : Retypes env U Γ e₁ e₂ := by
  intro B hor
  cases hor with
  | inl h => exact h.peelTo fun hb => retypeAtC_of_baseUniqC henv hbu hΓ H (.inl hb)
  | inr h =>
    exact (h.peelTo fun hb => (retypeAtC_of_baseUniqC henv hbu hΓ H (.inr hb)).symm).symm

/-- **The headline: `Ordered + ConvSortInv + ConvPiInv → retypes`.**

No `SortUniq`, no `VEnv.WF`, no stratification, no `PiInvStratApp`, and — the point of this
file — no composition of two conversions indexed at different sorts anywhere in the proof. -/
theorem retypes_of_convInv (henv : Ordered env) (hsi : ConvSortInv env U)
    (hpi : ConvPiInv env U) {Γ : List VExpr} {e₁ e₂ A : VExpr}
    (H : env.IsDefEqStrong U Γ e₁ e₂ A) (hΓ : CtxStrong env U Γ) :
    Retypes env U Γ e₁ e₂ :=
  retypes_of_baseUniqC henv (baseUniqC_of henv hsi hpi) H hΓ

/-! ## The price: the two hypothesis sets are interderivable

This half is the collapse test (`ORCHESTRATOR.md` rule 6) and the consumer audit.  Nothing
above is a strengthening smuggled in as a reformulation, and nothing above is a weakening
either: `{ConvSortInv, ConvPiInv}` and `{SortUniq, PiInv}` imply each other over `Ordered`
environments. -/

/-- A level is `WF` as soon as its sort has any typing at all — read off the base typing that
`peelChain` produces, so this needs no hypothesis. -/
theorem sortWF_of_hasTypeStrong {Γ : List VExpr} {l : VLevel} {X : VExpr} {b : Bool}
    (H : env.HasTypeStrong U Γ (.sort l) X b) : l.WF U := by
  obtain ⟨X₀, h, -⟩ := H.peelChain
  cases h with | sort' a1 _ _ => exact a1

/-- **Collapsing a chain is exactly what `SortUniq` buys.**  Each junction of the chain is a
term with two sort typings, and aligning them is one appeal to `SortUniq`. -/
theorem ConvC.collapse (henv : Ordered env) (hsu : env.SortUniq U) {Γ : List VExpr}
    (hΓ : CtxStrong env U Γ) {A B : VExpr} (h : ConvC env U Γ A B) :
    ∀ {u : VLevel}, env.IsDefEqStrong U Γ A A (.sort u) →
      env.IsDefEqStrong U Γ A B (.sort u) := by
  induction h with
  | refl => exact fun hA => hA
  | step hl _ ih =>
    intro u hA
    have hu0 := hl.defeq.sort_r henv hΓ.defeq
    have hu := hA.defeq.sort_r henv hΓ.defeq
    have hl' := hl.atSort hu0 hu (hsu hΓ.defeq hu0 hu hl.hasType.1.defeq hA.defeq)
    exact hl'.trans (ih hl'.hasType.2)

/-- **`SortUniq` implies sort injectivity**: if `.sort l` and `.sort l'` share a type then that
type is `.sort w` with `w ≈ l.succ ≈ l'.succ`. -/
theorem sortInv_of_sortUniq (henv : Ordered env) (hsu : env.SortUniq U) {Γ : List VExpr}
    (hΓ : CtxStrong env U Γ) {l l' w : VLevel}
    (h : env.IsDefEqStrong U Γ (.sort l) (.sort l') (.sort w)) : l ≈ l' := by
  have hw := h.defeq.sort_r henv hΓ.defeq
  have hl : l.WF U := sortWF_of_hasTypeStrong h.hasType'.1
  have hl' : l'.WF U := sortWF_of_hasTypeStrong h.hasType'.2
  have e1 : VLevel.succ l ≈ w :=
    hsu hΓ.defeq (by exact hl) hw (IsDefEq.sortDF hl hl rfl) h.hasType.1.defeq
  have e2 : VLevel.succ l' ≈ w :=
    hsu hΓ.defeq (by exact hl') hw (IsDefEq.sortDF hl' hl' rfl) h.hasType.2.defeq
  exact VLevel.succ_congr_iff.1 (e1.trans e2.symm)

theorem convSortInv_of_sortUniq (henv : Ordered env) (hsu : env.SortUniq U) :
    ConvSortInv env U := by
  intro Γ u v hΓ h
  cases h with
  | refl => exact rfl
  | step hl t =>
    have hu : u.WF U := sortWF_of_hasTypeStrong hl.hasType'.1
    exact sortInv_of_sortUniq henv hsu hΓ
      ((ConvC.step hl t).collapse henv hsu hΓ (.sortDF hu hu rfl))

theorem convPiInv_of_sortUniq_piInv (henv : Ordered env) (hsu : env.SortUniq U)
    (hpi : PiInv env U) : ConvPiInv env U := by
  intro Γ A B A' B' hΓ h
  cases h with
  | refl => exact ⟨.refl, .refl⟩
  | step hl t =>
    have hc := (ConvC.step hl t).collapse henv hsu hΓ hl.hasType.1
    obtain ⟨⟨u1, hd⟩, u2, hb⟩ := hpi hΓ.defeq ⟨_, hc.defeq⟩
    exact ⟨.one (hd.strong henv hΓ.defeq),
      .one (hb.strong henv (Γ := _::_) ⟨hΓ.defeq, _, hd.hasType.1⟩)⟩

/-- **The circle, stated honestly.**  The new hypotheses give `SortUniq` straight back: run the
recursion at the term whose two sort typings are in question and invert the resulting chain. -/
theorem sortUniq_of_convInv (henv : Ordered env) (hsi : ConvSortInv env U)
    (hpi : ConvPiInv env U) : env.SortUniq U := by
  intro Γ e u v hΓ _ _ h1 h2
  have hΓ' : CtxStrong env U Γ := .strong henv hΓ
  exact hsi hΓ' (uniqStrongCAt_of_baseUniqCAt (baseUniqCAt_of henv hsi hpi e) hΓ'
    (h1.strong henv hΓ).hasType'.1 (h2.strong henv hΓ).hasType'.1)

/-- **Subsumption**: `BaseUniqTerm.retypes_of_sortUniq_piInv`, re-derived through this file.
So the chain route loses nothing; §"The price" above shows it also gains nothing in strength,
only in the *shape* of the proof. -/
theorem retypes_of_sortUniq_piInv_via_chain (henv : Ordered env) (hsu : env.SortUniq U)
    (hpi : PiInv env U) {Γ : List VExpr} {e₁ e₂ A : VExpr}
    (H : env.IsDefEqStrong U Γ e₁ e₂ A) (hΓ : CtxStrong env U Γ) :
    Retypes env U Γ e₁ e₂ :=
  retypes_of_convInv henv (convSortInv_of_sortUniq henv hsu)
    (convPiInv_of_sortUniq_piInv henv hsu hpi) H hΓ

/-- **The whole cost of `peelEq` is the collapse.**  `ProofRetypeHeads.HasTypeStrong.peelEq` is
`peelChain` — which takes nothing — followed by `ConvC.collapse`, which spends one appeal to
`SortUniq` per junction of the chain.  Nothing else in it needs a hypothesis. -/
theorem peelEq_of_peelChain (henv : Ordered env) (hsu : env.SortUniq U)
    {Γ : List VExpr} {e B : VExpr} {b : Bool} (hΓ : CtxStrong env U Γ)
    (H : env.HasTypeStrong U Γ e B b) :
    ∃ B₀, env.HasTypeStrong U Γ e B₀ false ∧
      ∃ u, env.IsDefEqStrong U Γ B₀ B (.sort u) := by
  obtain ⟨B₀, hB₀, hc⟩ := H.peelChain
  obtain ⟨u, hu⟩ := hB₀.refl.isType' henv henv.strong hΓ
  exact ⟨B₀, hB₀, u, hc.collapse henv hsu hΓ hu⟩

/-- **`SortUniq` and `ConvSortInv` are the same hypothesis** over an `Ordered` environment in
which `ConvPiInv` holds.  So the chain reformulation does not weaken the demand; what it does
is relocate it — see the module docstring. -/
theorem sortUniq_iff_convSortInv (henv : Ordered env) (hpi : ConvPiInv env U) :
    env.SortUniq U ↔ ConvSortInv env U :=
  ⟨convSortInv_of_sortUniq henv, fun h => sortUniq_of_convInv henv h hpi⟩

/-! ## Non-vacuity, and the negative control for the **two** recursive calls

`BaseUniqTerm.baseUniqAt_forallE` makes *no* recursive call and pays `SortUniq`.
`baseUniqCAt_forallE` makes *two* — at the Π's own domain and at its own body — and pays
`ConvSortInv`.  The witnesses below fire each of the two calls separately, at a Π whose two
base types are **syntactically different**, and the rejections show that neither call can be
dropped. -/

/-- `(X : Type) → Sort (imax 0 0)`, typed twice: the two base types differ **only in the
codomain level**, because `.sort (.imax .zero .zero)` inhabits both `.sort (.succ (.imax 0 0))`
and `.sort (.succ 0)`.  This is the instance the recursion at the **body** decides. -/
theorem forallE_body_fires :
    env.HasTypeStrong U [] (.forallE (.sort (.succ .zero)) (.sort (.imax .zero .zero)))
        (.sort (.imax (.succ (.succ .zero)) (.succ (.imax .zero .zero)))) false ∧
      env.HasTypeStrong U [] (.forallE (.sort (.succ .zero)) (.sort (.imax .zero .zero)))
        (.sort (.imax (.succ (.succ .zero)) (.succ .zero))) false ∧
      (VExpr.sort (.imax (.succ (.succ .zero)) (.succ (.imax .zero .zero))) : VExpr) ≠
        .sort (.imax (.succ (.succ .zero)) (.succ .zero)) := by
  refine ⟨.forallE trivial ⟨trivial, trivial⟩ (.base (.sort' trivial trivial rfl))
      (.base (.sort' ⟨trivial, trivial⟩ ⟨trivial, trivial⟩ rfl)),
    .forallE trivial trivial (.base (.sort' trivial trivial rfl))
      (.base (.sort' ⟨trivial, trivial⟩ trivial VLevel.imax_zero)), ?_⟩
  intro h; injection h with h1; injection h1 with _ h3; injection h3 with h4
  exact VLevel.noConfusion h4

/-- `(X : Prop) → Prop`, typed twice: the two base types differ **only in the domain level**,
because `.sort .zero` inhabits both `.sort (.succ 0)` and `.sort (.succ (.imax 0 0))`.  This is
the instance the recursion at the **domain** decides. -/
theorem forallE_domain_fires :
    env.HasTypeStrong U [] (.forallE (.sort .zero) (.sort .zero))
        (.sort (.imax (.succ .zero) (.succ .zero))) false ∧
      env.HasTypeStrong U [] (.forallE (.sort .zero) (.sort .zero))
        (.sort (.imax (.succ (.imax .zero .zero)) (.succ .zero))) false ∧
      (VExpr.sort (.imax (.succ .zero) (.succ .zero)) : VExpr) ≠
        .sort (.imax (.succ (.imax .zero .zero)) (.succ .zero)) := by
  refine ⟨.forallE trivial trivial (.base (.sort' trivial trivial rfl))
      (.base (.sort' trivial trivial rfl)),
    .forallE ⟨trivial, trivial⟩ trivial
      (.base (.sort' trivial ⟨trivial, trivial⟩ VLevel.imax_zero.symm))
      (.base (.sort' trivial trivial rfl)), ?_⟩
  intro h; injection h with h1; injection h1 with h2; injection h2 with h3
  exact VLevel.noConfusion h3

/-- **The body recursion cannot be dropped**: knowing the two domain levels agree does not
determine the Π's level. -/
theorem forallE_body_call_not_droppable :
    ¬ ∀ u₁ u₂ v₁ v₂ : VLevel, u₁ ≈ u₂ → VLevel.imax u₁ v₁ ≈ VLevel.imax u₂ v₂ := by
  intro H
  have := VLevel.equiv_def.1 (H .zero .zero .zero (.succ .zero) rfl) []
  simp [VLevel.eval, Lean.Nat.imax] at this

/-- **The domain recursion cannot be dropped**: knowing the two codomain levels agree does not
determine the Π's level either. -/
theorem forallE_domain_call_not_droppable :
    ¬ ∀ u₁ u₂ v₁ v₂ : VLevel, v₁ ≈ v₂ → VLevel.imax u₁ v₁ ≈ VLevel.imax u₂ v₂ := by
  intro H
  have := VLevel.equiv_def.1
    (H .zero (.succ (.succ .zero)) (.succ .zero) (.succ .zero) rfl) []
  simp [VLevel.eval, Lean.Nat.imax] at this

/-- **The `.app` branch still fires non-degenerately**, at `ProofRetypeHeads`' witness, now
with a chain-valued conclusion.  `ConvSortInv` and `ConvPiInv` are *carried*, not discharged:
this fires the branch and is not evidence that they are jointly satisfiable
(`ORCHESTRATOR.md` rule 4). -/
theorem baseUniqCAt_app_fires (henv : Ordered env) (hsi : ConvSortInv env U)
    (hpi : ConvPiInv env U) :
    ∃ (Γ : List VExpr) (f a A B : VExpr), A ≠ B ∧ CtxStrong env U Γ ∧
      env.HasTypeStrong U Γ (.app f a) A false ∧
      env.HasTypeStrong U Γ (.app f a) B false ∧ ConvC env U Γ A B := by
  obtain ⟨Γ, f, a, A, B, hne, hΓ, h1, h2⟩ := baseUniqApp_nonvacuous (env := env) (U := U) henv
  exact ⟨Γ, f, a, A, B, hne, hΓ, h1, h2, baseUniqCAt_of henv hsi hpi (.app f a) hΓ h1 h2⟩

end VEnv
end Lean4Lean

section Audit
open Lean4Lean.VEnv
#print axioms Lean4Lean.VEnv.ConvC.one
#print axioms Lean4Lean.VEnv.ConvC.trans
#print axioms Lean4Lean.VEnv.ConvC.symm
#print axioms Lean4Lean.VEnv.HasTypeStrong.peelChain
#print axioms Lean4Lean.VEnv.uniqStrongCAt_of_baseUniqCAt
#print axioms Lean4Lean.VEnv.ConvC.transport
#print axioms Lean4Lean.VEnv.ConvC.forallE
#print axioms Lean4Lean.VEnv.ConvC.inst
#print axioms Lean4Lean.VEnv.baseUniqCAt_bvar
#print axioms Lean4Lean.VEnv.baseUniqCAt_const
#print axioms Lean4Lean.VEnv.baseUniqCAt_sort
#print axioms Lean4Lean.VEnv.baseUniqCAt_forallE
#print axioms Lean4Lean.VEnv.baseUniqCAt_lam
#print axioms Lean4Lean.VEnv.baseUniqCAt_app
#print axioms Lean4Lean.VEnv.baseUniqCAt_of
#print axioms Lean4Lean.VEnv.baseUniqC_of
#print axioms Lean4Lean.VEnv.retypeAtC_of_baseUniqC
#print axioms Lean4Lean.VEnv.retypes_of_baseUniqC
#print axioms Lean4Lean.VEnv.retypes_of_convInv
#print axioms Lean4Lean.VEnv.sortWF_of_hasTypeStrong
#print axioms Lean4Lean.VEnv.ConvC.collapse
#print axioms Lean4Lean.VEnv.sortInv_of_sortUniq
#print axioms Lean4Lean.VEnv.convSortInv_of_sortUniq
#print axioms Lean4Lean.VEnv.convPiInv_of_sortUniq_piInv
#print axioms Lean4Lean.VEnv.sortUniq_of_convInv
#print axioms Lean4Lean.VEnv.peelEq_of_peelChain
#print axioms Lean4Lean.VEnv.sortUniq_iff_convSortInv
#print axioms Lean4Lean.VEnv.retypes_of_sortUniq_piInv_via_chain
#print axioms Lean4Lean.VEnv.forallE_body_fires
#print axioms Lean4Lean.VEnv.forallE_domain_fires
#print axioms Lean4Lean.VEnv.forallE_body_call_not_droppable
#print axioms Lean4Lean.VEnv.forallE_domain_call_not_droppable
#print axioms Lean4Lean.VEnv.baseUniqCAt_app_fires
end Audit

