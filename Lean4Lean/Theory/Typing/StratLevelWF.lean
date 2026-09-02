import Lean4Lean.Theory.Typing.Stratified

/-!
# `LevelWF` at Carneiro's conversion-alternation index

`Theory/Typing/Lemmas.lean`'s `IsDefEq.levelWF` reads level well-formedness off an ambient
derivation: from `env.IsDefEq U Γ e₁ e₂ A` and a context whose entries are `LevelWF U`, all
three of `e₁`, `e₂`, `A` are `LevelWF U`.  This file is its `Stratified` analogue, and the
analogue is **not** the same statement.

## Why the literal analogue is false

`Stratified.rfl` is unconditional (see `Stratified.lean`'s module docstring, "One deviation
from the reference"), so `Γ ⊢[n] e ≡ e` holds for *every* `e` — including `e` whose levels
are not `WF U`, in every context, however well formed.  So the conjunctive reading of the
conversion half,

    Γ ⊢[n] e ≡ e' → e.LevelWF U ∧ e'.LevelWF U

is false at every environment, every `U`, every `n` and every context
(`isDefEqN_levelWF_conj_false`).  That is the loophole, and it is not an artifact of the
deviation: the reference's own `⊢₀` is *syntactic equality* (`unique.tex:12`,
`IsDefEqN.zero_iff`), so a typing-guarded `refl` would not close it either — `⊢₀ α ≡ β` has
no typing content by stipulation.

## What is true, and what it costs

The conversion half must be read as an **iff** rather than a conjunction:

    Γ ⊢[n] e ≡ e'  →  (e.LevelWF U ↔ e'.LevelWF U)

which `rfl` satisfies trivially and every other rule preserves.  The typing half keeps the
ambient shape.  The two must be proved *together* — `Stratified.levelWF` — for the reason
`Stratified.lean`'s standing warning gives: `beta` needs the annotation's `LevelWF` from a
typing premise's *type*, and `conv` needs the conversion iff.

The context hypothesis is unavoidable (`isDefEqN_levelWF_iff_needs_ctx`): without it `beta`
manufactures a conversion whose left side carries a bad `bvar` type and whose right side does
not.  And the one place where an induction on this pair looks stuck — `lamDF`/`forallEDF`
recurse under a binder whose annotation is only known `LevelWF`-*equivalent* to the other
side's — is not stuck: the annotation's `LevelWF` is exactly what the goal's own conjunction
hands you in each direction of the iff, so no case split (and no `Classical`) is needed.
-/

namespace Lean4Lean
namespace VEnv

variable {env : VEnv} {U : Nat}

/-! ## The analogue -/

/-- **The `Stratified` analogue of `IsDefEq.levelWF`.**  One induction over the `Bool`-indexed
pair: the typing half is the ambient statement, the conversion half is an *iff* rather than a
conjunction (the module docstring says why it must be).

Both halves are needed in the same induction — `conv` consumes the conversion half, and
`beta`/`eta`/`appDF`/`proofIrrel` consume the typing half. -/
theorem Stratified.levelWF {n : Nat} {Γ : List VExpr} {e A : VExpr} {b : Bool}
    (H : Stratified env U n Γ e A b) (W : OnCtx Γ fun _ A => A.LevelWF U) :
    (b = true → e.LevelWF U ∧ A.LevelWF U) ∧
    (b = false → (e.LevelWF U ↔ A.LevelWF U)) := by
  induction H with
  | bvar h =>
    refine ⟨fun _ => ⟨⟨⟩, ?_⟩, (fun h => nomatch h)⟩
    induction h with
    | zero => exact W.2.liftN
    | succ _ ih => exact (ih W.1).liftN
  | sort h => exact ⟨fun _ => ⟨h, h⟩, (fun h => nomatch h)⟩
  | const _ h2 _ => exact ⟨fun _ => ⟨h2, .instL h2⟩, (fun h => nomatch h)⟩
  | app _ _ ih1 ih2 =>
    refine ⟨fun _ => ?_, (fun h => nomatch h)⟩
    let ⟨hf, hA, hB⟩ := (ih1 W).1 (Eq.refl true)
    let ⟨ha, _⟩ := (ih2 W).1 (Eq.refl true)
    exact ⟨⟨hf, ha⟩, hB.inst ha⟩
  | lam _ _ ih1 ih2 =>
    refine ⟨fun _ => ?_, (fun h => nomatch h)⟩
    let ⟨hA, _⟩ := (ih1 W).1 (Eq.refl true)
    let ⟨hb, hB⟩ := (ih2 ⟨W, hA⟩).1 (Eq.refl true)
    exact ⟨⟨hA, hb⟩, hA, hB⟩
  | forallE h1 h2 _ _ ih1 ih2 =>
    refine ⟨fun _ => ?_, (fun h => nomatch h)⟩
    let ⟨hA, _⟩ := (ih1 W).1 (Eq.refl true)
    let ⟨hB, _⟩ := (ih2 ⟨W, hA⟩).1 (Eq.refl true)
    exact ⟨⟨hA, hB⟩, h1, h2⟩
  | conv _ _ ih1 ih2 =>
    refine ⟨fun _ => ?_, (fun h => nomatch h)⟩
    let ⟨he, hA⟩ := (ih2 W).1 (Eq.refl true)
    exact ⟨he, ((ih1 W).2 (Eq.refl false)).1 hA⟩
  | rfl => exact ⟨(fun h => nomatch h), fun _ => Iff.rfl⟩
  | symm _ ih => exact ⟨(fun h => nomatch h), fun _ => ((ih W).2 (Eq.refl false)).symm⟩
  | trans _ _ ih1 ih2 =>
    exact ⟨(fun h => nomatch h), fun _ => ((ih1 W).2 (Eq.refl false)).trans ((ih2 W).2 (Eq.refl false))⟩
  | sortDF h1 h2 _ => exact ⟨(fun h => nomatch h), fun _ => iff_of_true h1 h2⟩
  | constDF _ h2 h3 _ _ => exact ⟨(fun h => nomatch h), fun _ => iff_of_true h2 h3⟩
  | appDF _ _ _ _ _ _ _ ih2 ih3 _ ih5 ih6 =>
    refine ⟨(fun h => nomatch h), fun _ => ?_⟩
    let ⟨hf, _⟩ := (ih2 W).1 (Eq.refl true)
    let ⟨hf', _⟩ := (ih3 W).1 (Eq.refl true)
    let ⟨ha, _⟩ := (ih5 W).1 (Eq.refl true)
    let ⟨ha', _⟩ := (ih6 W).1 (Eq.refl true)
    exact iff_of_true ⟨hf, ha⟩ ⟨hf', ha'⟩
  | lamDF _ _ ih1 ih2 =>
    refine ⟨(fun h => nomatch h), fun _ => ⟨fun ⟨hA, hb⟩ => ?_, fun ⟨hA', hb'⟩ => ?_⟩⟩
    · exact ⟨((ih1 W).2 (Eq.refl false)).1 hA, ((ih2 ⟨W, hA⟩).2 (Eq.refl false)).1 hb⟩
    · have hA := ((ih1 W).2 (Eq.refl false)).2 hA'
      exact ⟨hA, ((ih2 ⟨W, hA⟩).2 (Eq.refl false)).2 hb'⟩
  | forallEDF _ _ ih1 ih2 =>
    refine ⟨(fun h => nomatch h), fun _ => ⟨fun ⟨hA, hb⟩ => ?_, fun ⟨hA', hb'⟩ => ?_⟩⟩
    · exact ⟨((ih1 W).2 (Eq.refl false)).1 hA, ((ih2 ⟨W, hA⟩).2 (Eq.refl false)).1 hb⟩
    · have hA := ((ih1 W).2 (Eq.refl false)).2 hA'
      exact ⟨hA, ((ih2 ⟨W, hA⟩).2 (Eq.refl false)).2 hb'⟩
  | beta _ _ ih1 ih2 =>
    refine ⟨(fun h => nomatch h), fun _ => ?_⟩
    let ⟨he', hA⟩ := (ih2 W).1 (Eq.refl true)
    let ⟨he, _⟩ := (ih1 ⟨W, hA⟩).1 (Eq.refl true)
    exact iff_of_true ⟨⟨hA, he⟩, he'⟩ (he.inst he')
  | eta _ ih =>
    refine ⟨(fun h => nomatch h), fun _ => ?_⟩
    let ⟨he, hA, _⟩ := (ih W).1 (Eq.refl true)
    exact iff_of_true ⟨hA, he.liftN, ⟨⟩⟩ he
  | proofIrrel _ _ _ _ ih2 ih3 =>
    refine ⟨(fun h => nomatch h), fun _ => ?_⟩
    let ⟨hh, _⟩ := (ih2 W).1 (Eq.refl true)
    let ⟨hh', _⟩ := (ih3 W).1 (Eq.refl true)
    exact iff_of_true hh hh'
  | extra _ h2 _ => exact ⟨(fun h => nomatch h), fun _ => iff_of_true (VExpr.LevelWF.instL h2) (VExpr.LevelWF.instL h2)⟩

/-- The typing half, in the shape callers want. -/
theorem HasTypeN.levelWF {n : Nat} {Γ : List VExpr} {e A : VExpr}
    (H : env.HasTypeN U n Γ e A) (W : OnCtx Γ fun _ A => A.LevelWF U) :
    e.LevelWF U ∧ A.LevelWF U := (Stratified.levelWF H W).1 (Eq.refl true)

/-- The conversion half, in the shape callers want.  **An iff, not a conjunction** — see
`isDefEqN_levelWF_conj_false`. -/
theorem IsDefEqN.levelWF {n : Nat} {Γ : List VExpr} {e e' : VExpr}
    (H : env.IsDefEqN U n Γ e e') (W : OnCtx Γ fun _ A => A.LevelWF U) :
    e.LevelWF U ↔ e'.LevelWF U := (Stratified.levelWF H W).2 (Eq.refl false)


/-! ## The loophole, refuted: the literal analogue is false

`IsDefEq.levelWF` is a *conjunction* on both endpoints.  Transcribing that shape onto the
conversion half gives a statement that fails on `Stratified.rfl` alone, with no environment,
no context and no index doing any work. -/

/-- **The conjunctive reading of the conversion half is false** — at every environment, every
`U`, every index, every context.  `Stratified.rfl` relates `.sort (.param U)` to itself and
`.param U` is not `WF U`. -/
theorem isDefEqN_levelWF_conj_false (env : VEnv) (U n : Nat) (Γ : List VExpr) :
    ¬ ∀ {e e' : VExpr}, env.IsDefEqN U n Γ e e' → e.LevelWF U ∧ e'.LevelWF U := fun h =>
  absurd (h (e := .sort (.param U)) (e' := .sort (.param U)) .rfl).1 (Nat.lt_irrefl U)

/-- **And the context hypothesis is not removable from the iff either.**  Over a context whose
one entry has a bad level, `beta` manufactures a conversion whose left side carries that entry
as a λ-annotation and whose right side has dropped it.

So `Stratified.levelWF` needs `W`, and needs it in the conversion half specifically — this
witness's conversion is derivable at every environment and every index `n+1`. -/
theorem isDefEqN_levelWF_iff_needs_ctx (env : VEnv) (U n : Nat) :
    ∃ (Γ : List VExpr) (e e' : VExpr), env.IsDefEqN U (n+1) Γ e e' ∧
      ¬ (e.LevelWF U ↔ e'.LevelWF U) :=
  by
  refine ⟨[.sort (.param U)], .app (.lam (.sort (.param U)) (.sort .zero)) (.bvar 0), .sort .zero,
    ?_, fun h => absurd (h.2 trivial).1.1 (Nat.lt_irrefl U)⟩
  exact Stratified.beta (Stratified.sort trivial) (Stratified.bvar Lookup.zero)

/-! ## The half that is free

The *subject* of a typing derivation is `LevelWF` with no context hypothesis at all: no typing
rule reads a level off the context except through a `bvar`'s **type**.  Cheap, and worth having
separately — it is the half that survives when the guard is unavailable. -/

/-- The subject half of the typing judgment, **with no context hypothesis**. -/
theorem Stratified.levelWF_subject {n : Nat} {Γ : List VExpr} {e A : VExpr} {b : Bool}
    (H : Stratified env U n Γ e A b) : b = true → e.LevelWF U := by
  induction H with
  | bvar => exact fun _ => ⟨⟩
  | sort h => exact fun _ => h
  | const _ h2 _ => exact fun _ => h2
  | app _ _ ih1 ih2 => exact fun _ => ⟨ih1 (Eq.refl true), ih2 (Eq.refl true)⟩
  | lam _ _ ih1 ih2 => exact fun _ => ⟨ih1 (Eq.refl true), ih2 (Eq.refl true)⟩
  | forallE _ _ _ _ ih1 ih2 => exact fun _ => ⟨ih1 (Eq.refl true), ih2 (Eq.refl true)⟩
  | conv _ _ _ ih2 => exact fun _ => ih2 (Eq.refl true)
  | rfl | symm | trans | sortDF | constDF | appDF | lamDF | forallEDF | beta | eta
  | proofIrrel | extra => exact fun h => nomatch h

theorem HasTypeN.levelWF_subject {n : Nat} {Γ : List VExpr} {e A : VExpr}
    (H : env.HasTypeN U n Γ e A) : e.LevelWF U := Stratified.levelWF_subject H (Eq.refl true)

/-- ...and the type half genuinely is not free: the same witness as
`isDefEqN_levelWF_iff_needs_ctx`, one rule earlier. -/
theorem hasTypeN_levelWF_type_needs_ctx (env : VEnv) (U n : Nat) :
    ∃ (Γ : List VExpr) (e A : VExpr), env.HasTypeN U n Γ e A ∧ ¬ A.LevelWF U :=
  ⟨[.sort (.param U)], .bvar 0, .sort (.param U), Stratified.bvar Lookup.zero,
    Nat.lt_irrefl U⟩


/-! ## A premise of `Stratified.forallE` that is not needed for the reason given

`Stratified.forallE` carries `u.WF U` and `v.WF U`, and its docstring says they "cannot be
recovered afterwards without the soundness direction (which needs `uniq`)".  Over a `LevelWF`
context they can: `Stratified.levelWF`'s *type* half reads them straight off the two typing
premises.  No `uniq`, no `Ordered env`, no environment condition at all. -/

/-- **Both of `Stratified.forallE`'s level premises are derivable from its typing premises**, over
a `LevelWF` context.  Note the second one needs only the *subject* half for the context
extension, which is itself hypothesis-free (`Stratified.levelWF_subject`). -/
theorem forallE_wf_free {n : Nat} {Γ : List VExpr} {A B : VExpr} {u v : VLevel}
    (W : OnCtx Γ fun _ A => A.LevelWF U)
    (h1 : env.HasTypeN U n Γ A (.sort u)) (h2 : env.HasTypeN U n (A::Γ) B (.sort v)) :
    u.WF U ∧ v.WF U :=
  ⟨(HasTypeN.levelWF h1 W).2, (HasTypeN.levelWF h2 ⟨W, HasTypeN.levelWF_subject h1⟩).2⟩


section Audit

/-! `#print axioms`, by namespace.  Every declaration in this file is in `Lean4Lean.VEnv`; there is no second namespace. -/
#print axioms Lean4Lean.VEnv.Stratified.levelWF
#print axioms Lean4Lean.VEnv.HasTypeN.levelWF
#print axioms Lean4Lean.VEnv.IsDefEqN.levelWF
#print axioms Lean4Lean.VEnv.isDefEqN_levelWF_conj_false
#print axioms Lean4Lean.VEnv.isDefEqN_levelWF_iff_needs_ctx
#print axioms Lean4Lean.VEnv.Stratified.levelWF_subject
#print axioms Lean4Lean.VEnv.HasTypeN.levelWF_subject
#print axioms Lean4Lean.VEnv.hasTypeN_levelWF_type_needs_ctx
#print axioms Lean4Lean.VEnv.forallE_wf_free

end Audit
end VEnv
end Lean4Lean
