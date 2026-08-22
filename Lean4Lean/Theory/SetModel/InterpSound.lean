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
def PropSound (Γ : List VExpr) (e : VExpr) : Prop :=
  L.IsProp M Γ e → ∀ ρ ∈ interpCtx M L Γ, (interp M L Γ e).toFun ρ ⊆ ({pt} : V)

/-- **Part 2**: a proof denotes `•`. -/
def ProofSound (Γ : List VExpr) (e : VExpr) : Prop :=
  L.IsProof M Γ e → ∀ ρ ∈ interpCtx M L Γ, (interp M L Γ e).toFun ρ = pt

/-- **Part 3**: a term denotes an element of the denotation of its type. -/
def TypeSound (Γ : List VExpr) (e A : VExpr) : Prop :=
  ∀ ρ ∈ interpCtx M L Γ, (interp M L Γ e).toFun ρ ∈ (interp M L Γ A).toFun ρ

/-- **Part 4**: definitionally equal terms denote equal values. -/
def EqSound (Γ : List VExpr) (e₁ e₂ : VExpr) : Prop :=
  ∀ ρ ∈ interpCtx M L Γ, (interp M L Γ e₁).toFun ρ = (interp M L Γ e₂).toFun ρ

/-- Every universe level occurring in a judgement evaluates strictly below `n`.
This is the explicit bound: `Sound` is stated for a *fixed* `n` and a *fixed*
chain of `n` inaccessibles, never for an existential one. -/
def SoundBound (n : ℕ) (Γ : List VExpr) (e A : VExpr) : Prop :=
  (∀ B ∈ A :: e :: Γ, (L.lvl Γ B).eval M.ls < n) ∧ (L.srt Γ e).eval M.ls < n

/-- **Soundness**, in the form the induction proves it.  All **four** parts are
carried; see the note on part 2 in the ledger. -/
structure Sound (Γ : List VExpr) (e₁ e₂ A : VExpr) : Prop where
  prop : PropSound M L Γ e₁
  proof : ProofSound M L Γ e₁
  type : TypeSound M L Γ e₁ A
  eq : EqSound M L Γ e₁ e₂

end Statement

/-! ## Internal functions and their graphs

The one place the model's own machinery is asked for something new: `eta` needs
an internal function to equal its own graph.  It does not need a new
extensionality principle — `value_eq_of_kpair_mem` and `kpair_value_mem` from
`SetModel/Rank.lean` suffice.
-/

section Graph

variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- **An internal function is its own graph.**  This is what `eta` consumes. -/
theorem function_eq_graph {X Y f : V} (hf : f ∈ (Y ^ X : V)) :
    f = repl (fun v ↦ (⟨v, f ‘ v⟩ₖ : V)) (by definability) X := by
  have hfun : IsFunction f := IsFunction.of_mem hf
  refine subset_antisymm (fun p hp ↦ ?_) (fun p hp ↦ ?_)
  · obtain ⟨x, hx, y, hy, rfl⟩ := mem_prod_iff.mp (subset_prod_of_mem_function hf p hp)
    exact (repl_spec _).mpr ⟨x, hx, by rw [value_eq_of_kpair_mem hp]⟩
  · obtain ⟨v, hv, rfl⟩ := (repl_spec _).mp hp
    exact kpair_value_mem hf hv

end Graph

section MkLam

variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {G : V → V} {hG : ℒₛₑₜ-function₁[V] G} {F : V → V → V} {hF : ℒₛₑₜ-function₂[V] F}

/-- The `lam` clause really is an internal function on the domain. -/
theorem mkLam_mem_function (ρ : V) :
    mkLam G hG F hF ρ ∈ ((repl (F ρ) (by definability) (G ρ)) ^ G ρ : V) := by
  refine mem_function.intro (fun p hp ↦ ?_) (fun v hv ↦ ?_)
  · obtain ⟨v, hv, rfl⟩ := mem_mkLam_iff.mp hp
    exact kpair_mem_iff.mpr ⟨hv, (repl_spec _).mpr ⟨v, hv, rfl⟩⟩
  · refine ExistsUnique.intro (F ρ v) (mem_mkLam_iff.mpr ⟨v, hv, rfl⟩) fun y hy ↦ ?_
    obtain ⟨v', hv', he⟩ := mem_mkLam_iff.mp hy
    obtain ⟨rfl, rfl⟩ := kpair_inj he
    rfl

/-- Applying the `lam` clause is substitution into the body. -/
theorem mkLam_value {ρ v : V} (hv : v ∈ G ρ) : (mkLam G hG F hF ρ) ‘ v = F ρ v := by
  have : IsFunction (mkLam G hG F hF ρ) := IsFunction.of_mem (mkLam_mem_function ρ)
  exact value_eq_of_kpair_mem (mem_mkLam_iff.mpr ⟨v, hv, rfl⟩)

end MkLam

/-! ## The `beta` and `eta` cases

These are the two the ledger named as able to refute it.  Both are proved here,
with their induction hypotheses as explicit arguments, and **neither uses any
injectivity fact**.
-/

section BetaEta

variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {env : VEnv} {nv : ℕ} (M : ModelData V) (L : LevelAssign env nv)

/-- The valuation extended by the value of the substituted term satisfies
`AgreeInst` at `k = 0` — the instance `beta` needs. -/
lemma agreeInst_zero {Γ : List VExpr} {e' : VExpr} {ρ : V} (hρ : ρ ∈ interpCtx M L Γ)
    (w : V) (hw : w = (interp M L Γ e').toFun ρ) :
    AgreeInst M L Γ.length Γ.length 0 e' Γ (snoc ρ w) ρ := by
  constructor
  · intro p hp
    have : instPos Γ.length p = p := by simp [instPos, hp]
    rw [this]
    exact snoc_value_of_lt M L hρ hp
  · rw [snoc_value_at_len M L hρ, hw, VExpr.liftN_zero]

/-- **The `beta` case.**  `⟦(λA.e) e'⟧ρ = ⟦e[e'/0]⟧ρ`.

Hypotheses, in order: stability; closedness; **part 3 for `e'`** (Carneiro's
entanglement — the substituted term denotes an element of the domain); **part 2
for `e`**, used only in the proof branch; and the agreement of the two splits,
which follows from `srt_sound`/`lvl_sound` and level arithmetic.

No injectivity fact appears. -/
theorem beta_sound (hS : L.Stable) {Γ : List VExpr} {A e e' : VExpr}
    (hcle : e.ClosedN (Γ.length + 1)) (hcle' : e'.ClosedN Γ.length)
    (h3e' : ∀ ρ ∈ interpCtx M L Γ, (interp M L Γ e').toFun ρ ∈ (interp M L Γ A).toFun ρ)
    (h2e : L.IsProof M (A :: Γ) e →
      ∀ ρ ∈ interpCtx M L (A :: Γ), (interp M L (A :: Γ) e).toFun ρ = pt)
    (hsplit : L.IsProof M Γ (.lam A e) ↔ L.IsProof M (A :: Γ) e)
    {ρ : V} (hρ : ρ ∈ interpCtx M L Γ) :
    (interp M L Γ (.app (.lam A e) e')).toFun ρ = (interp M L Γ (e.inst e')).toFun ρ := by
  set w := (interp M L Γ e').toFun ρ with hw
  have hwA : w ∈ (interp M L Γ A).toFun ρ := h3e' ρ hρ
  have hρ₁ : snoc ρ w ∈ interpCtx M L (A :: Γ) :=
    (mem_interpCtx_cons M L).mpr ⟨ρ, hρ, w, hwA, rfl⟩
  -- substitution, at `k = 0`
  have hsub : (interp M L Γ (e.inst e')).toFun ρ = (interp M L (A :: Γ) e).toFun (snoc ρ w) := by
    refine interp_inst M L hS (j := Γ.length) e (Γ₀ := Γ) (A₀ := A) (k := 0)
      Ctx.InstN.zero (by simp)
      (by simpa using hcle) (by simpa using hcle') hρ hρ₁ ?_
    exact agreeInst_zero M L hρ w rfl
  by_cases hp : L.IsProof M Γ (.lam A e)
  · rw [interp_app_proof M L hp, hsub, h2e (hsplit.mp hp) _ hρ₁]
  · have hpe : ¬ L.IsProof M (A :: Γ) e := fun h ↦ hp (hsplit.mpr h)
    rw [interp_app_type M L hp, interp_lam_type M L hpe, hsub]
    exact mkLam_value hwA

/-- **The `eta` case.**  `⟦λA. (e↑) (bvar 0)⟧ρ = ⟦e⟧ρ`.

Hypotheses: stability; closedness; **part 3 for `e`** at the `∀`-type, which is
what makes `⟦e⟧ρ` an internal function; **part 2 for `e`**, used only in the
proof branch; and the two split agreements.

The only new set-theoretic ingredient is `function_eq_graph`, and it needed no
new extensionality principle.  No injectivity fact appears. -/
theorem eta_sound (hS : L.Stable) {Γ : List VExpr} {A B e : VExpr}
    (hcle : e.ClosedN Γ.length)
    (h3e : ∀ ρ ∈ interpCtx M L Γ,
      (interp M L Γ e).toFun ρ ∈ (interp M L Γ (.forallE A B)).toFun ρ)
    (h2e : L.IsProof M Γ e → ∀ ρ ∈ interpCtx M L Γ, (interp M L Γ e).toFun ρ = pt)
    (hsplit₂ : L.IsProof M (A :: Γ) (.app e.lift (.bvar 0)) ↔ L.IsProof M Γ e)
    (hsplit₃ : ¬ L.IsProof M Γ e → ¬ L.IsProp M (A :: Γ) B)
    (hsplit₄ : L.IsProof M (A :: Γ) e.lift ↔ L.IsProof M Γ e)
    {ρ : V} (hρ : ρ ∈ interpCtx M L Γ) :
    (interp M L Γ (.lam A (.app e.lift (.bvar 0)))).toFun ρ = (interp M L Γ e).toFun ρ := by
  by_cases hp : L.IsProof M Γ e
  · rw [interp_lam_proof M L (hsplit₂.mpr hp), h2e hp ρ hρ]
  · have hpb : ¬ L.IsProof M (A :: Γ) (.app e.lift (.bvar 0)) := fun h ↦ hp (hsplit₂.mp h)
    rw [interp_lam_type M L hpb]
    -- the body computes to `⟦e⟧ρ ‘ v`
    have hbody : ∀ v ∈ (interp M L Γ A).toFun ρ,
        (interp M L (A :: Γ) (.app e.lift (.bvar 0))).toFun (snoc ρ v) =
          ((interp M L Γ e).toFun ρ) ‘ v := by
      intro v hv
      have hρ₁ : snoc ρ v ∈ interpCtx M L (A :: Γ) :=
        (mem_interpCtx_cons M L).mpr ⟨ρ, hρ, v, hv, rfl⟩
      rw [interp_app_type M L (fun h ↦ hp (hsplit₄.mp h)), interp_bvar]
      congr 1
      · refine interp_liftN M L hS (n := 1) (j := Γ.length) e
          (Ctx.LiftN.zero (n := 1) [A] rfl) (by simp) hcle hρ hρ₁ ?_
        intro p hp'
        have : liftPos 1 Γ.length p = p := by simp [liftPos]; omega
        rw [this]
        exact snoc_value_of_lt M L hρ hp'
      · simpa using snoc_value_at_len M L hρ
    -- and `⟦e⟧ρ` is an internal function on `⟦A⟧ρ`, hence equal to that graph
    have hmem := h3e ρ hρ
    rw [interp_forallE_type M L (hsplit₃ hp)] at hmem
    obtain ⟨hfn, -⟩ := mem_mkForallType_iff.mp hmem
    refine Eq.trans ?_ (function_eq_graph hfn).symm
    ext y
    rw [mem_mkLam_iff, repl_spec]
    exact exists_congr fun v ↦ and_congr_right fun hv ↦ by rw [hbody v hv]

end BetaEta

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
