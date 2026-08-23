import Lean4Lean.Verify.Typing.Lemmas

/-!
# Target-preserving transport of `TrExprS` across a definitionally equal context

`TrExprS.defeqDFC` and `TrExprS.defeqDFC'` (`Verify/Typing/Lemmas.lean`) move a translation to a
definitionally equal `VLCtx`, but both let the **target move**: the first concludes
`∃ e₂, TrExprS Δ₂ e e₂` and the second `TrExpr Δ₂ e e'`.  That is fatal for any caller that
then has to *invert* the result at a `forallE`, because re-inverting a target known only up to
conversion is pi injectivity — `Typing/Injectivity.lean`, open, and the most blocked family in
the tree.

**This file is the observation that the target does not have to move.**  `defeqDFC` re-derives
the target existentially at every node; a statement that *preserves* it can simply **reuse** the
data the original derivation already chose.  The case that looks decisive is `proj`, whose
target `VInductDecl'.projTerm T C us ps ιs i e'` depends on the parameter and index arguments
read off the type of `e'` — but a target-preserving statement keeps the very same `us`, `ps`,
`ιs` and only transports the `HasType`/`HasArgs` premises that justify them, so it never needs
`TrProj.uniq`.  **Nothing here is injectivity-blocked.**

## What the relation has to be

Not `VLCtx.IsDefEq`: that permits a `vlet` entry's *value* to move, and `VLCtx.find?` returns
that value, so a `.bvar`/`.fvar` would translate differently on the two sides.  `DefEqVLam`
below keeps every `vlet` entry identical and lets only `vlam` *types* move — which is exactly
the slack a caller has when the same term is checked in a context whose binder types were
recorded up to conversion (`Lean4Lean/Inductive/Add.lean`'s annotation stripping is the
motivating instance; `VIndCtor.WF.params_eq` is the same slack in the spec).
-/

namespace Lean4Lean

open Lean (Name Expr)

/-- Two local contexts with the same shape and the same `vlet` entries, whose `vlam` binder
types are definitionally equal.  Strictly stronger than `VLCtx.IsDefEq`, and the extra strength
is what makes `VLCtx.find?` return the *same* value on both sides. -/
inductive VLCtx.DefEqVLam (env : VEnv) (U : Nat) : VLCtx → VLCtx → Prop
  | nil : VLCtx.DefEqVLam env U [] []
  | vlam {Δ₁ Δ₂ : VLCtx} {ofv A₁ A₂ u} :
    VLCtx.DefEqVLam env U Δ₁ Δ₂ →
    (∀ fv deps, ofv = some (fv, deps) → fv ∉ Δ₁.fvars ∧ deps ⊆ Δ₁.fvars) →
    env.IsDefEq U Δ₁.toCtx A₁ A₂ (.sort u) →
    VLCtx.DefEqVLam env U ((ofv, .vlam A₁) :: Δ₁) ((ofv, .vlam A₂) :: Δ₂)
  | vlet {Δ₁ Δ₂ : VLCtx} {ofv A v u} :
    VLCtx.DefEqVLam env U Δ₁ Δ₂ →
    (∀ fv deps, ofv = some (fv, deps) → fv ∉ Δ₁.fvars ∧ deps ⊆ Δ₁.fvars) →
    env.HasType U Δ₁.toCtx v A →
    env.IsDefEq U Δ₁.toCtx A A (.sort u) →
    VLCtx.DefEqVLam env U ((ofv, .vlet A v) :: Δ₁) ((ofv, .vlet A v) :: Δ₂)

namespace VLCtx.DefEqVLam

variable {env : VEnv} {U : Nat}

/-- Forgetting the extra strength recovers `VLCtx.IsDefEq`, so every consumer of that relation
applies unchanged. -/
theorem toIsDefEq : ∀ {Δ₁ Δ₂ : VLCtx}, DefEqVLam env U Δ₁ Δ₂ → VLCtx.IsDefEq env U Δ₁ Δ₂
  | _, _, .nil => .nil
  | _, _, .vlam h1 h2 h3 => .cons h1.toIsDefEq h2 (.vlam h3)
  | _, _, .vlet h1 h2 h3 h4 => .cons h1.toIsDefEq h2 (.vlet h3 h4)

theorem defeqCtx {Δ₁ Δ₂ : VLCtx} (h : DefEqVLam env U Δ₁ Δ₂) :
    env.IsDefEqCtx U [] Δ₁.toCtx Δ₂.toCtx := h.toIsDefEq.defeqCtx

theorem wf {Δ₁ Δ₂ : VLCtx} (h : DefEqVLam env U Δ₁ Δ₂) : VLCtx.WF env U Δ₁ := h.toIsDefEq.wf

theorem fvars {Δ₁ Δ₂ : VLCtx} (h : DefEqVLam env U Δ₁ Δ₂) : Δ₁.fvars = Δ₂.fvars :=
  h.toIsDefEq.fvars

/-- **The relation is inhabited**, at every well-formed context.  A relation with no instance
proves nothing, and `DefEqVLam` is strictly stronger than `VLCtx.IsDefEq`, so reflexivity is
not inherited — it has to be exhibited.  This is also what a caller uses on the binders it did
*not* move. -/
theorem refl (henv : VEnv.Ordered env) :
    ∀ {Δ : VLCtx}, VLCtx.WF env U Δ → DefEqVLam env U Δ Δ
  | [], _ => .nil
  | (_, .vlam _) :: _, ⟨h1, h2, h3⟩ =>
    let ⟨_, h⟩ := h3
    .vlam (refl henv h1) h2 h
  | (_, .vlet ..) :: _, ⟨h1, h2, h3⟩ =>
    let ⟨_, h⟩ := h3.isType henv h1.toCtx
    .vlet (refl henv h1) h2 h3 h

/-- **The point of the extra strength.**  A lookup returns the *same value* on both sides — only
its type may have moved.  `VLCtx.IsDefEq` cannot say this: its `vlet` case lets the stored value
move, and `find?` returns exactly that value. -/
theorem find?_fst {Δ₁ Δ₂ : VLCtx} (h : DefEqVLam env U Δ₁ Δ₂) (v) :
    (Δ₁.find? v).map Prod.fst = (Δ₂.find? v).map Prod.fst := by
  induction h generalizing v with
  | nil => rfl
  | @vlam Δ₁ Δ₂ ofv A₁ A₂ u _ _ _ ih =>
    rw [VLCtx.find?, VLCtx.find?]
    cases VLCtx.next ofv v with
    | none => rfl
    | some v' =>
      have ih := ih v'
      cases hf1 : Δ₁.find? v' <;> cases hf2 : Δ₂.find? v' <;>
        simp_all [VLocalDecl.depth]
  | @vlet Δ₁ Δ₂ ofv A w u _ _ _ _ ih =>
    rw [VLCtx.find?, VLCtx.find?]
    cases VLCtx.next ofv v with
    | none => rfl
    | some v' =>
      have ih := ih v'
      cases hf1 : Δ₁.find? v' <;> cases hf2 : Δ₂.find? v' <;>
        simp_all [VLocalDecl.depth]

/-- **The one-binder step, packaged.**  A caller that pushes a binder whose recorded type is
only *definitionally* the one its target supplies never has to build a `DefEqVLam` by hand: the
tail is reflexivity and the head is the conversion it already holds.  This is the shape every
`withLocalDecl` site needs, and the only one this file's clients use. -/
theorem head (henv : VEnv.Ordered env) {Δ : VLCtx} {ofv A₁ A₂ u}
    (hΔ : VLCtx.WF env U Δ)
    (hofv : ∀ fv deps, ofv = some (fv, deps) → fv ∉ Δ.fvars ∧ deps ⊆ Δ.fvars)
    (h : env.IsDefEq U Δ.toCtx A₁ A₂ (.sort u)) :
    DefEqVLam env U ((ofv, .vlam A₁) :: Δ) ((ofv, .vlam A₂) :: Δ) :=
  .vlam (refl henv hΔ) hofv h

/-- `find?_fst` in the form the `bvar`/`fvar` cases of the transport use. -/
theorem find?_same {Δ₁ Δ₂ : VLCtx} (h : DefEqVLam env U Δ₁ Δ₂) {v e A₁}
    (H : Δ₁.find? v = some (e, A₁)) : ∃ A₂, Δ₂.find? v = some (e, A₂) := by
  have := h.find?_fst v
  rw [H] at this
  cases hf : Δ₂.find? v with
  | none => rw [hf] at this; exact absurd this nofun
  | some q => rw [hf] at this; simp at this; exact ⟨q.2, by rw [this]⟩

end VLCtx.DefEqVLam

/-- `VEnv.HasArgs` transports across a definitionally equal context, argument by argument.
Absent upstream because `TrExprS.defeqDFC` never needed it — it re-derives the `proj` case's
spine instead of transporting the one it was given. -/
theorem VEnv.HasArgs.defeqDFC {env : VEnv} {U : Nat} {Γ₀ Γ₁ Γ₂ : List VExpr}
    (henv : VEnv.Ordered env) (h1 : VEnv.IsDefEqCtx env U Γ₀ Γ₁ Γ₂) :
    ∀ {As as : List VExpr}, env.HasArgs U Γ₁ As as → env.HasArgs U Γ₂ As as
  | _, _, .nil => .nil
  | _, _, .cons ha h => .cons (ha.defeqDFC henv h1) (h.defeqDFC henv h1)

/-- **`TrProj`, with the target preserved.**  This is the case that makes the whole file
possible: `projTerm`'s value is a function of `D`, `T`, `C`, `us`, `ps`, `ιs`, `i` and `e`, and
a target-*preserving* statement simply keeps all of them and transports the judgements that
justify them.  `TrExprS.defeqDFC` cannot do this because it re-derives `ps`/`ιs` existentially,
which is what makes it look as though `TrProj.uniq` — and hence injectivity — were needed. -/
theorem TrProj.defeqDFC_target {env : VEnv} {U : Nat} {Γ₁ Γ₂ : List VExpr} {Γ₀}
    (henv : VEnv.Ordered env) (hΓ : VEnv.IsDefEqCtx env U Γ₀ Γ₁ Γ₂)
    {s : Name} {i : Nat} {e e' : VExpr} (H : TrProj env U Γ₁ s i e e') :
    TrProj env U Γ₂ s i e e' := by
  cases H with
  | mk hS hty hus hps hιs hi hlv hargs hιargs hF17 =>
    exact .mk hS (hty.defeqDFC henv hΓ) hus hps hιs hi hlv
      (hargs.defeqDFC henv hΓ) (hιargs.defeqDFC henv hΓ) hF17

/-- **The transport, with the target preserved.**  Contrast `TrExprS.defeqDFC`
(`Verify/Typing/Lemmas.lean`), whose conclusion is `∃ e₂, TrExprS Δ₂ e e₂`: a caller that must
invert the result at a `forallE` cannot use that without pi injectivity, and can use this. -/
theorem TrExprS.defeqDFC_target {env : VEnv} {Us : List Name} (henv : VEnv.WF env) :
    ∀ {Δ₁ Δ₂ : VLCtx} {e : Expr} {e' : VExpr},
      VLCtx.DefEqVLam env Us.length Δ₁ Δ₂ → TrExprS env Us Δ₁ e e' → TrExprS env Us Δ₂ e e' := by
  intro Δ₁ Δ₂ e e' hΔ H
  induction H generalizing Δ₂ with
  | bvar h1 => let ⟨_, h⟩ := hΔ.find?_same h1; exact .bvar h
  | fvar h1 => let ⟨_, h⟩ := hΔ.find?_same h1; exact .fvar h
  | sort h1 => exact .sort h1
  | const h1 h2 h3 => exact .const h1 h2 h3
  | app h1 h2 _ _ ih3 ih4 =>
    exact .app (h1.defeqDFC henv.ordered hΔ.defeqCtx) (h2.defeqDFC henv.ordered hΔ.defeqCtx)
      (ih3 hΔ) (ih4 hΔ)
  | lam h1 _ _ ih2 ih3 =>
    have ⟨_, h1'⟩ := h1
    refine .lam (h1.defeqDFC henv.ordered hΔ.defeqCtx) (ih2 hΔ) (ih3 (.vlam (ofv := none) hΔ (by rintro _ _ ⟨⟩) h1'))
  | forallE h1 h2 _ _ ih3 ih4 =>
    have ⟨_, h1'⟩ := h1
    have hΔ' : VLCtx.DefEqVLam env Us.length _ _ := .vlam (ofv := none) hΔ (by rintro _ _ ⟨⟩) h1'
    exact .forallE (h1.defeqDFC henv.ordered hΔ.defeqCtx)
      (h2.defeqDFC henv.ordered hΔ'.defeqCtx) (ih3 hΔ) (ih4 hΔ')
  | letE h1 _ _ _ ih2 ih3 ih4 =>
    have ⟨_, h0⟩ := h1.isType henv.ordered hΔ.wf.toCtx
    exact .letE (h1.defeqDFC henv.ordered hΔ.defeqCtx) (ih2 hΔ) (ih3 hΔ)
      (ih4 (.vlet (ofv := none) hΔ (by rintro _ _ ⟨⟩) h1 h0))
  | lit h1 _ ih => exact .lit h1 (ih hΔ)
  | mdata _ ih => exact .mdata (ih hΔ)
  | proj _ h2 ih => exact .proj (ih hΔ) (h2.defeqDFC_target henv.ordered hΔ.defeqCtx)

/-- **The transport at a single binder** — the form a `withLocalDecl` caller actually needs.
The binder's *recorded* type `A₂` may differ from the type the target telescope supplies
(`A₁`); everything below the binder is untouched, so the whole `DefEqVLam` is `head`.

`Lean4Lean/Inductive/Add.lean`'s `consumeAnnotations` is the motivating instance: it records
`optParam α d`'s stripped domain `α` while the constructor's stored telescope still carries the
annotation, and the two are definitionally — not syntactically — equal. -/
theorem TrExprS.defeqDFC_vlam {env : VEnv} {Us : List Name} {Δ : VLCtx} {ofv}
    {A₁ A₂ : VExpr} {u : VLevel} {e : Expr} {e' : VExpr}
    (henv : VEnv.WF env) (hΔ : VLCtx.WF env Us.length Δ)
    (hofv : ∀ fv deps, ofv = some (fv, deps) → fv ∉ Δ.fvars ∧ deps ⊆ Δ.fvars)
    (h : env.IsDefEq Us.length Δ.toCtx A₁ A₂ (.sort u))
    (H : TrExprS env Us ((ofv, .vlam A₁) :: Δ) e e') :
    TrExprS env Us ((ofv, .vlam A₂) :: Δ) e e' :=
  H.defeqDFC_target henv (.head henv.ordered hΔ hofv h)

end Lean4Lean
