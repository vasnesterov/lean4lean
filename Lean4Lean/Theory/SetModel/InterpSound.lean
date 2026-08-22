import Lean4Lean.Theory.SetModel.InterpSubst

/-!
# Soundness: the statement, and what it consumes

Stage 3 of `SetModel/Interp.lean`.  Carneiro `soundness.tex:216`.

This file fixes the *statement* of soundness — machine-checked as a statement,
so that the ledger in `docs/soundness-ledger.md` is written against something
real — together with the pieces of it that are immediate.  The induction itself
is not carried out here.

## The four parts

Carneiro proves four things by one simultaneous induction on the derivation:

1. a proposition denotes a subset of `{•}`;
2. a proof denotes `•`;
3. `⟦Γ ⊢ e⟧ ρ ∈ ⟦Γ ⊢ α⟧ ρ`;
4. `Γ ⊢ e₁ ≡ e₂ : α` implies `⟦e₁⟧ ρ = ⟦e₂⟧ ρ`.

**Part 2 is a corollary of 1 and 3, not a separate induction.**  If `α` is a
proposition then `⟦α⟧ ρ ⊆ {•}` by part 1, and `⟦e⟧ ρ ∈ ⟦α⟧ ρ` by part 3, so
`⟦e⟧ ρ = •`.  `proofSound_of` below is that argument; it means the induction
carries three parts, not four.

## Schema form

The universe bound is explicit and finite: `SoundBound` says every universe
level occurring in the judgement evaluates below `n`, where `n` is the length of
the inaccessible chain.  There is no `∃ k` anywhere — see
`docs/model-interface.md` §3.
-/

namespace Lean4Lean.SetModel

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LO.FirstOrder.SetTheory.Ordinal (lt_def le_def lt_succ)

variable {V : Type*} [SetStructure V] [Nonempty V]

section Statement

variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {env : VEnv} {nv : ℕ} (M : ModelData V) (L : LevelAssign env nv)

/-- **Part 1**: a proposition denotes a subset of `{•}`. -/
def PropSound (Γ : List VExpr) (A : VExpr) : Prop :=
  ∀ ρ ∈ interpCtx M L Γ, (interp M L Γ A).toFun ρ ⊆ ({pt} : V)

/-- **Part 3**: a term denotes an element of the denotation of its type. -/
def TypeSound (Γ : List VExpr) (e A : VExpr) : Prop :=
  ∀ ρ ∈ interpCtx M L Γ, (interp M L Γ e).toFun ρ ∈ (interp M L Γ A).toFun ρ

/-- **Part 4**: definitionally equal terms denote equal values. -/
def EqSound (Γ : List VExpr) (e₁ e₂ : VExpr) : Prop :=
  ∀ ρ ∈ interpCtx M L Γ, (interp M L Γ e₁).toFun ρ = (interp M L Γ e₂).toFun ρ

/-- **Part 2 is a corollary of parts 1 and 3.**  This is why the simultaneous
induction carries three parts and not four. -/
theorem proofSound_of {Γ : List VExpr} {e A : VExpr}
    (h1 : PropSound M L Γ A) (h3 : TypeSound M L Γ e A)
    {ρ : V} (hρ : ρ ∈ interpCtx M L Γ) : (interp M L Γ e).toFun ρ = pt :=
  mem_singleton_iff.mp (h1 ρ hρ _ (h3 ρ hρ))

/-- Every universe level occurring in a judgement evaluates strictly below `n`.
This is the explicit bound: `Sound` is stated for a *fixed* `n` and a *fixed*
chain of `n` inaccessibles, never for an existential one. -/
def SoundBound (n : ℕ) (Γ : List VExpr) (e A : VExpr) : Prop :=
  (∀ B ∈ A :: e :: Γ, (L.lvl Γ B).eval M.ls < n) ∧ (L.srt Γ e).eval M.ls < n

/-- **Soundness**, in the form the induction proves it: for a well-formed
environment, a well-formed context and a judgement whose universe levels are
bounded by the length of the inaccessible chain, parts 1, 3 and 4 hold. -/
structure Sound (n : ℕ) (κ : ℕ → V) (Γ : List VExpr) (e₁ e₂ A : VExpr) : Prop where
  prop : PropSound M L Γ A
  type : TypeSound M L Γ e₁ A
  eq : EqSound M L Γ e₁ e₂

/-- The shape of the theorem to be proved.  `hchain` is where the inaccessibles
enter, `hb` is the explicit bound, and `hL`/`hS` are the packaged unique-typing
hypotheses.  `hcnst` is the constant-assignment coherence, which is an obligation
on `ModelData` rather than on the syntax. -/
def SoundnessStatement (n : ℕ) (κ : ℕ → V) (hcnst : Prop) : Prop :=
  IsInaccessibleChain n κ → M.κ = κ → L.Stable → hcnst →
    ∀ {Γ : List VExpr} {e₁ e₂ A : VExpr},
      env.IsDefEq nv Γ e₁ e₂ A → SoundBound M L n Γ e₁ A →
      Sound M L n κ Γ e₁ e₂ A

end Statement

/-!
## Ledger: what soundness consumes, case by case

Worked out by analysis against the thirteen constructors of `VEnv.IsDefEq`
(`Theory/Typing/Basic.lean`).  Recorded in full in `docs/soundness-ledger.md`;
the headline is stated here because it changes what the injectivity stream
should do next.

**Finding: no injectivity fact beyond `sort_inv` appears in any case.**

The two facts I expected to bite — `IsDefEqU.forallE_inv` and
`IsDefEqU.sort_forallE_inv` — do not, and the reason is structural rather than
lucky.  Both are *inversion* principles: they recover the components of a `∀`
from a definitional equality between two `∀`s.  Soundness never needs to invert,
because in every congruence rule the premises already supply the components:

* `appDF` gives `Γ ⊢ f ≡ f' : forallE A B` with `A` and `B` *named in the rule*,
  so the induction hypothesis is already about the right domain and codomain;
* `lamDF` and `forallEDF` state their premises in the *same* extended context
  `A :: Γ` for both sides, so the two interpretations are compared at the same
  valuations with no inversion;
* `defeqDF` needs only part 4 applied to the type, which is an induction
  hypothesis.

What the cases do consume is `LevelAssign` — and only through two derived facts,
`lvl_congr` and `srt_congr` (both already proved in `SetModel/Interp.lean` from
`lvl_sound`/`srt_sound` alone), which say the three proof-splitting decisions
agree on both sides of a `≡`.

A second consistency fact is used repeatedly and is worth naming: for
`Γ ⊢ f : forallE A B`, the split for `app` (on `srt Γ f`) and the split for
`forallE` (on `lvl (A::Γ) B`) **agree**, because
`srt Γ f ≈ lvl Γ (forallE A B) ≈ imax (lvl Γ A) (lvl (A::Γ) B)` and `imax u v`
evaluates to `0` exactly when `v` does.  It follows from `srt_sound`, `lvl_sound`
and level arithmetic — no injectivity.

**Caveat.**  This is analysis, not a machine-checked proof; the induction is not
carried out in this file.  The two places I would expect it to be tested first
are `beta` (which consumes substitution together with part 3 for the substituted
term — Carneiro's entanglement) and `eta` (which needs an internal function to
equal its own graph).  Neither looks like it needs inversion, but neither has
been checked.

## What soundness does consume

| Ingredient | Where | Status |
|---|---|---|
| `interp_liftN` (weakening) | `bvar`, `eta` | **proved**, `InterpSubst.lean` |
| `interp_inst` (substitution) | `appDF` part 3, `beta` | **proved**, `InterpSubst.lean` |
| `LevelAssign.lvl_congr`/`srt_congr` | every congruence case | **proved**, `Interp.lean` |
| `LevelAssign.Stable` | `bvar`, `beta`, `eta` | hypothesis |
| `U_mem_succ` + the universe bound | `sortDF` part 3 | **proved**, `Universe.lean` |
| `piProp_mem_UProp` | part 1, `forallE` case | **proved**, `Universe.lean` |
| validity (`Γ ⊢ e : A → IsType Γ A`) | `appDF`, to level the `∀` | available in `Theory/Typing/` |
| `cnst` coherence with `env.defeqs` | `constDF`, `extra` | **open**, a `ModelData` obligation |
| `IsDefEqU.sort_inv` | packaged as `LevelAssign` | **open**, one `sorry` |
| `IsDefEqU.forallE_inv` | — | **not needed** |
| `IsDefEqU.sort_forallE_inv` | — | **not needed** |
-/

end Lean4Lean.SetModel
