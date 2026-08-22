import Lean4Lean.Theory.SetModel.InterpSubst
import Lean4Lean.Theory.VDecl

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

/-! ## Parts 1 and 2 are derived, not branches

A second correction, and a simplification: **part 1 is a corollary of part 3**,
because `⟦sort u⟧ρ = U κ (u.eval)` and `U κ 0` is literally `UProp = ℘ {•}`, so
`⟦e⟧ρ ∈ ⟦sort u⟧ρ` with `u.eval = 0` *is* `⟦e⟧ρ ⊆ {•}`.  No induction is needed
for it at all — only the judgement `Γ ⊢ e : sort u`, which is a premise wherever
part 1 is used (`proofIrrel` is the example).

Part 2 is then a corollary of part 3 plus part 1 applied to the *type*, which
needs validity (`IsDefEq.isType`, available and sorry-free in
`Theory/Typing/Lemmas.lean`).  It is still convenient to carry it through the
induction — `beta` and `eta` consume it directly — but it is not independent
content.
-/

section DefFunExt

omit [Nonempty V] in
theorem DefFun.ext {f g : DefFun V} (h : f.toFun = g.toFun) : f = g := by
  cases f; cases g; simp_all

end DefFunExt

section Derived

variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {env : VEnv} {nv : ℕ} (M : ModelData V) (L : LevelAssign env nv)

/-- **Part 1 from part 3.**  A term of a `Prop`-level sort denotes a subset of
`{•}`, because `U κ 0` is `℘ {•}` on the nose. -/
theorem propSound_of_mem_sort {Γ : List VExpr} {e : VExpr} {u : VLevel} {ρ : V}
    (hu : u.eval M.ls = 0)
    (h : (interp M L Γ e).toFun ρ ∈ (interp M L Γ (.sort u)).toFun ρ) :
    (interp M L Γ e).toFun ρ ⊆ ({pt} : V) := by
  rw [interp_sort, hu, U_zero] at h
  exact mem_UProp_iff.mp h

/-- **Part 2 from parts 1 and 3.** -/
theorem proofSound_of {Γ : List VExpr} {e A : VExpr} {ρ : V}
    (h1 : (interp M L Γ A).toFun ρ ⊆ ({pt} : V))
    (h3 : (interp M L Γ e).toFun ρ ∈ (interp M L Γ A).toFun ρ) :
    (interp M L Γ e).toFun ρ = pt :=
  mem_singleton_iff.mp (h1 _ h3)

end Derived

/-! ## The remaining cases

Each is stated with its induction hypotheses as explicit arguments, so that it
is machine-checked against exactly the premises the real induction supplies.
-/

section Cases

variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {env : VEnv} {nv : ℕ} (M : ModelData V) (L : LevelAssign env nv)

/-- A looked-up type is closed in its context. -/
theorem Lookup.closedN : ∀ {Γ : List VExpr} {i : ℕ} {A : VExpr},
    CtxClosed Γ → Lookup Γ i A → A.ClosedN Γ.length
  | _ :: Γ, _, _, hΓ, .zero => by
    have h : VExpr.ClosedN _ Γ.length := hΓ.2
    simpa using h.liftN (n := 1) (j := 0)
  | _ :: Γ, _, _, hΓ, .succ H => by
    have h := Lookup.closedN hΓ.1 H
    simpa using h.liftN (n := 1) (j := 0)

/-- **The `bvar` case** (part 3).  The valuation is typed by construction; the
`.lift` that `Lookup` inserts is discharged by weakening. -/
theorem bvar_sound (hS : L.Stable) : ∀ {Γ : List VExpr} {i : ℕ} {A : VExpr},
    CtxClosed Γ → Lookup Γ i A → ∀ {ρ : V}, ρ ∈ interpCtx M L Γ →
    (interp M L Γ (.bvar i)).toFun ρ ∈ (interp M L Γ A).toFun ρ
  | ty :: Γ, _, _, hΓ, .zero, ρ, hρ => by
    obtain ⟨ρ₀, hρ₀, v, hv, rfl⟩ := (mem_interpCtx_cons M L).mp hρ
    have hcl : ty.ClosedN Γ.length := hΓ.2
    have hlift : (interp M L (ty :: Γ) ty.lift).toFun (snoc ρ₀ v)
        = (interp M L Γ ty).toFun ρ₀ := by
      refine interp_liftN M L hS (n := 1) (j := Γ.length) ty
        (Ctx.LiftN.zero (n := 1) [ty] rfl) (by simp) hcl hρ₀ hρ ?_
      intro p hp
      have : liftPos 1 Γ.length p = p := by simp [liftPos]; omega
      rw [this]
      exact snoc_value_of_lt M L hρ₀ hp
    rw [interp_bvar, hlift, show (ty :: Γ).length - 1 - 0 = Γ.length from by simp,
      snoc_value_at_len M L hρ₀]
    exact hv
  | A :: Γ, _, _, hΓ, .succ (ty := ty) (n := m) H, ρ, hρ => by
    obtain ⟨ρ₀, hρ₀, v, hv, rfl⟩ := (mem_interpCtx_cons M L).mp hρ
    have hclA : A.ClosedN Γ.length := hΓ.2
    have hclty : ty.ClosedN Γ.length := Lookup.closedN hΓ.1 H
    have hm : m < Γ.length := H.lt
    have hlift : (interp M L (A :: Γ) ty.lift).toFun (snoc ρ₀ v)
        = (interp M L Γ ty).toFun ρ₀ := by
      refine interp_liftN M L hS (n := 1) (j := Γ.length) ty
        (Ctx.LiftN.zero (n := 1) [A] rfl) (by simp) hclty hρ₀ hρ ?_
      intro p hp
      have : liftPos 1 Γ.length p = p := by simp [liftPos]; omega
      rw [this]
      exact snoc_value_of_lt M L hρ₀ hp
    rw [interp_bvar, hlift]
    have hpos : (A :: Γ).length - 1 - (m + 1) = Γ.length - 1 - m := by simp; omega
    rw [hpos, snoc_value_of_lt M L hρ₀ (by omega : Γ.length - 1 - m < Γ.length)]
    have := bvar_sound hS hΓ.1 H hρ₀
    rwa [interp_bvar] at this

/-- **The `defeqDF` case.**  Part 3 transports along part 4 for the type; part 4
is unchanged. -/
theorem defeqDF_sound {Γ : List VExpr} {A B e : VExpr} {ρ : V}
    (hAB : (interp M L Γ A).toFun ρ = (interp M L Γ B).toFun ρ)
    (he : (interp M L Γ e).toFun ρ ∈ (interp M L Γ A).toFun ρ) :
    (interp M L Γ e).toFun ρ ∈ (interp M L Γ B).toFun ρ := hAB ▸ he

/-- **The `proofIrrel` case.**  Needs only part 3, three times: the premise
`Γ ⊢ p : sort 0` gives `⟦p⟧ρ ⊆ {•}` by `propSound_of_mem_sort`, and both proofs
land in it. -/
theorem proofIrrel_sound {Γ : List VExpr} {p h h' : VExpr} {ρ : V}
    (hp : (interp M L Γ p).toFun ρ ∈ (interp M L Γ (.sort .zero)).toFun ρ)
    (hh : (interp M L Γ h).toFun ρ ∈ (interp M L Γ p).toFun ρ)
    (hh' : (interp M L Γ h').toFun ρ ∈ (interp M L Γ p).toFun ρ) :
    (interp M L Γ h).toFun ρ = (interp M L Γ h').toFun ρ := by
  have hsub : (interp M L Γ p).toFun ρ ⊆ ({pt} : V) :=
    propSound_of_mem_sort M L (u := .zero) rfl hp
  rw [proofSound_of M L hsub hh, proofSound_of M L hsub hh']

/-- **The `sortDF` case.**  This is where the universe bound is spent, and it is
the only place: part 3 is `U κ i ∈ U κ (i+1)`, which needs `i < n` — the length
of the inaccessible chain.  There is no `∃ k`: `n` and `κ` are fixed. -/
theorem sortDF_sound {n : ℕ} {κ : ℕ → V} (hκ : IsInaccessibleChain n κ) (hMκ : M.κ = κ)
    {Γ : List VExpr} {l l' : VLevel} (hll : l ≈ l') (hb : l.eval M.ls < n) (ρ : V) :
    (interp M L Γ (.sort l)).toFun ρ = (interp M L Γ (.sort l')).toFun ρ ∧
      (interp M L Γ (.sort l)).toFun ρ ∈ (interp M L Γ (.sort (.succ l))).toFun ρ := by
  rw [interp_sort, interp_sort, interp_sort]
  refine ⟨by rw [VLevel.equiv_def.mp hll], ?_⟩
  subst hMκ
  exact U_mem_succ hκ hb

end Cases

/-! ### Context conversion — a requirement the ledger did not have

`lamDF` and `forallEDF` type their body premise in `A :: Γ` but their right-hand
side is `lam A' body'` / `forallE A' body'`, whose interpretation uses
`A' :: Γ`.  So the interpretation must not distinguish contexts that differ by a
definitional equality.

This is **not** an injectivity fact — it is a stability property of the level
assignment, in the same family as `LevelAssign.Stable` — but it was missing from
the ledger, and it is a genuine extra obligation on whoever constructs a
`LevelAssign`.  It is discharged for well-typed input by `srt_sound`/`lvl_sound`
together with context conversion (`IsDefEq.defeqDFC` in `Theory/Typing/`).
-/

section CtxConv

variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {env : VEnv} {nv : ℕ} (M : ModelData V) (L : LevelAssign env nv)

/-- A relation on contexts that the level assignment cannot see, closed under
extending both sides by a common type. -/
structure CtxInvariant (R : List VExpr → List VExpr → Prop) : Prop where
  len : ∀ {Γ₁ Γ₂}, R Γ₁ Γ₂ → Γ₁.length = Γ₂.length
  lvl : ∀ {Γ₁ Γ₂}, R Γ₁ Γ₂ → ∀ A, L.lvl Γ₁ A ≈ L.lvl Γ₂ A
  srt : ∀ {Γ₁ Γ₂}, R Γ₁ Γ₂ → ∀ e, L.srt Γ₁ e ≈ L.srt Γ₂ e
  cons : ∀ {Γ₁ Γ₂}, R Γ₁ Γ₂ → ∀ A, R (A :: Γ₁) (A :: Γ₂)

/-- **Context conversion for the interpretation.** -/
theorem interp_ctxInvariant {R : List VExpr → List VExpr → Prop} (hR : CtxInvariant L R) :
    ∀ (e : VExpr) {Γ₁ Γ₂ : List VExpr}, R Γ₁ Γ₂ →
      interp M L Γ₁ e = interp M L Γ₂ e
  | .bvar i, Γ₁, Γ₂, h => by
    refine DefFun.ext (funext fun ρ ↦ ?_); rw [interp_bvar, interp_bvar, hR.len h]
  | .sort u, Γ₁, Γ₂, h => by
    refine DefFun.ext (funext fun ρ ↦ ?_); rw [interp_sort, interp_sort]
  | .const c us, Γ₁, Γ₂, h => by
    refine DefFun.ext (funext fun ρ ↦ ?_); rw [interp_const, interp_const]
  | .app f a, Γ₁, Γ₂, h => by
    have hsp : L.IsProof M Γ₁ f ↔ L.IsProof M Γ₂ f := by
      simp only [LevelAssign.IsProof, VLevel.equiv_def.mp (hR.srt h f) M.ls]
    refine DefFun.ext (funext fun ρ ↦ ?_)
    by_cases hp : L.IsProof M Γ₁ f
    · rw [interp_app_proof M L hp, interp_app_proof M L (hsp.mp hp)]
    · rw [interp_app_type M L hp, interp_app_type M L (fun x ↦ hp (hsp.mpr x)),
        interp_ctxInvariant hR f h, interp_ctxInvariant hR a h]
  | .lam A b, Γ₁, Γ₂, h => by
    have hsp : L.IsProof M (A :: Γ₁) b ↔ L.IsProof M (A :: Γ₂) b := by
      simp only [LevelAssign.IsProof, VLevel.equiv_def.mp (hR.srt (hR.cons h A) b) M.ls]
    refine DefFun.ext (funext fun ρ ↦ ?_)
    by_cases hp : L.IsProof M (A :: Γ₁) b
    · rw [interp_lam_proof M L hp, interp_lam_proof M L (hsp.mp hp)]
    · rw [interp_lam_type M L hp, interp_lam_type M L (fun x ↦ hp (hsp.mpr x)),
        interp_ctxInvariant hR A h, interp_ctxInvariant hR b (hR.cons h A)]
  | .forallE A B, Γ₁, Γ₂, h => by
    have hsp : L.IsProp M (A :: Γ₁) B ↔ L.IsProp M (A :: Γ₂) B := by
      simp only [LevelAssign.IsProp, VLevel.equiv_def.mp (hR.lvl (hR.cons h A) B) M.ls]
    refine DefFun.ext (funext fun ρ ↦ ?_)
    by_cases hp : L.IsProp M (A :: Γ₁) B
    · rw [interp_forallE_prop M L hp, interp_forallE_prop M L (hsp.mp hp),
        interp_ctxInvariant hR A h, interp_ctxInvariant hR B (hR.cons h A)]
    · rw [interp_forallE_type M L hp, interp_forallE_type M L (fun x ↦ hp (hsp.mpr x)),
        interp_ctxInvariant hR A h, interp_ctxInvariant hR B (hR.cons h A)]

end CtxConv

/-! ### The congruence cases -/

section Congruence

variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {env : VEnv} {nv : ℕ} (M : ModelData V) (L : LevelAssign env nv)

/-- **`appDF`, part 4.**  The two splits agree by `srt_congr`, which comes from
`LevelAssign` alone.  No inversion. -/
theorem appDF_sound_eq {Γ : List VExpr} {f f' a a' : VExpr} {ρ : V}
    (hsplit : L.IsProof M Γ f ↔ L.IsProof M Γ f')
    (hf : (interp M L Γ f).toFun ρ = (interp M L Γ f').toFun ρ)
    (ha : (interp M L Γ a).toFun ρ = (interp M L Γ a').toFun ρ) :
    (interp M L Γ (.app f a)).toFun ρ = (interp M L Γ (.app f' a')).toFun ρ := by
  by_cases hp : L.IsProof M Γ f
  · rw [interp_app_proof M L hp, interp_app_proof M L (hsplit.mp hp)]
  · rw [interp_app_type M L hp, interp_app_type M L (fun x ↦ hp (hsplit.mpr x)), hf, ha]

/-- **`appDF`, part 3.**  The induction hypothesis already concerns the right
domain and codomain — `A` and `B` are named in the rule — so nothing is
inverted.  The proof branch uses that `pt ∈ piProp` unfolds to a universally
quantified membership, which is instantiated at the argument. -/
theorem appDF_sound_type (hS : L.Stable) {Γ : List VExpr} {A B f a : VExpr} {ρ : V}
    (hclB : B.ClosedN (Γ.length + 1)) (hcla : a.ClosedN Γ.length)
    (hρ : ρ ∈ interpCtx M L Γ)
    (hf3 : (interp M L Γ f).toFun ρ ∈ (interp M L Γ (.forallE A B)).toFun ρ)
    (ha3 : (interp M L Γ a).toFun ρ ∈ (interp M L Γ A).toFun ρ)
    (hf2 : L.IsProof M Γ f → (interp M L Γ f).toFun ρ = pt)
    (hsplit : L.IsProof M Γ f ↔ L.IsProp M (A :: Γ) B) :
    (interp M L Γ (.app f a)).toFun ρ ∈ (interp M L Γ (B.inst a)).toFun ρ := by
  have hρ₁ : snoc ρ ((interp M L Γ a).toFun ρ) ∈ interpCtx M L (A :: Γ) :=
    (mem_interpCtx_cons M L).mpr ⟨ρ, hρ, _, ha3, rfl⟩
  have hsub : (interp M L Γ (B.inst a)).toFun ρ
      = (interp M L (A :: Γ) B).toFun (snoc ρ ((interp M L Γ a).toFun ρ)) := by
    refine interp_inst M L hS (j := Γ.length) B (Γ₀ := Γ) (A₀ := A) (k := 0)
      Ctx.InstN.zero (by simp) (by simpa using hclB) (by simpa using hcla) hρ hρ₁ ?_
    exact agreeInst_zero M L hρ _ rfl
  by_cases hp : L.IsProof M Γ f
  · rw [interp_app_proof M L hp, hsub]
    rw [interp_forallE_prop M L (hsplit.mp hp)] at hf3
    rw [hf2 hp] at hf3
    exact (mem_mkForallProp_iff.mp hf3).2 _ ha3
  · rw [interp_app_type M L hp, hsub]
    rw [interp_forallE_type M L (fun x ↦ hp (hsplit.mpr x))] at hf3
    obtain ⟨hfn, hval⟩ := mem_mkForallType_iff.mp hf3
    exact hval _ ha3 _ (kpair_value_mem hfn ha3)

/-- **`lamDF`, part 4.**  `hctx` is the context-conversion equality; it is what
`CtxInvariant` supplies. -/
theorem lamDF_sound_eq {Γ : List VExpr} {A A' body body' : VExpr} {ρ : V}
    (hctx : interp M L (A' :: Γ) body' = interp M L (A :: Γ) body')
    (hsplit : L.IsProof M (A :: Γ) body ↔ L.IsProof M (A' :: Γ) body')
    (hA : (interp M L Γ A).toFun ρ = (interp M L Γ A').toFun ρ)
    (hbody : ∀ v, (interp M L (A :: Γ) body).toFun (snoc ρ v)
      = (interp M L (A :: Γ) body').toFun (snoc ρ v)) :
    (interp M L Γ (.lam A body)).toFun ρ = (interp M L Γ (.lam A' body')).toFun ρ := by
  by_cases hp : L.IsProof M (A :: Γ) body
  · rw [interp_lam_proof M L hp, interp_lam_proof M L (hsplit.mp hp)]
  · rw [interp_lam_type M L hp, interp_lam_type M L (fun x ↦ hp (hsplit.mpr x)), hctx]
    ext y
    rw [mem_mkLam_iff, mem_mkLam_iff, hA]
    exact exists_congr fun v ↦ and_congr_right fun _ ↦ by rw [hbody v]

/-- **`forallEDF`, part 4.** -/
theorem forallEDF_sound_eq {Γ : List VExpr} {A A' body body' : VExpr} {ρ : V}
    (hctx : interp M L (A' :: Γ) body' = interp M L (A :: Γ) body')
    (hsplit : L.IsProp M (A :: Γ) body ↔ L.IsProp M (A' :: Γ) body')
    (hA : (interp M L Γ A).toFun ρ = (interp M L Γ A').toFun ρ)
    (hbody : ∀ v, (interp M L (A :: Γ) body).toFun (snoc ρ v)
      = (interp M L (A :: Γ) body').toFun (snoc ρ v)) :
    (interp M L Γ (.forallE A body)).toFun ρ
      = (interp M L Γ (.forallE A' body')).toFun ρ := by
  by_cases hp : L.IsProp M (A :: Γ) body
  · rw [interp_forallE_prop M L hp, interp_forallE_prop M L (hsplit.mp hp), hctx]
    ext z
    rw [mem_mkForallProp_iff, mem_mkForallProp_iff, hA]
    exact and_congr_right fun _ ↦ forall₂_congr fun v _ ↦ by rw [hbody v]
  · rw [interp_forallE_type M L hp, interp_forallE_type M L (fun x ↦ hp (hsplit.mpr x)), hctx]
    ext f
    rw [mem_mkForallType_iff, mem_mkForallType_iff, hA]
    refine and_congr ?_ ?_
    · congr! 2
      ext y
      rw [mem_mkFamUnion_iff, mem_mkFamUnion_iff, hA]
      exact exists_congr fun v ↦ and_congr_right fun _ ↦ by rw [hbody v]
    · exact forall₂_congr fun v _ ↦ forall_congr' fun y ↦ imp_congr_right fun _ ↦ by
        rw [hbody v]

omit [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
/-- The `lam` clause lands in the `forallE` clause, given the values do. -/
theorem mkLam_mem_mkForallType {G : V → V} {hG : ℒₛₑₜ-function₁[V] G}
    {F : V → V → V} {hF : ℒₛₑₜ-function₂[V] F}
    {Fb : V → V → V} {hFb : ℒₛₑₜ-function₂[V] Fb} {ρ : V}
    (h : ∀ v ∈ G ρ, F ρ v ∈ Fb ρ v) :
    mkLam G hG F hF ρ ∈ mkForallType G hG Fb hFb ρ := by
  refine mem_mkForallType_iff.mpr ⟨mem_function.intro (fun p hp ↦ ?_) (fun v hv ↦ ?_), ?_⟩
  · obtain ⟨v, hv, rfl⟩ := mem_mkLam_iff.mp hp
    exact kpair_mem_iff.mpr ⟨hv, mem_mkFamUnion_iff.mpr ⟨v, hv, h v hv⟩⟩
  · refine ExistsUnique.intro (F ρ v) (mem_mkLam_iff.mpr ⟨v, hv, rfl⟩) fun y hy ↦ ?_
    obtain ⟨v', hv', he⟩ := mem_mkLam_iff.mp hy
    obtain ⟨rfl, rfl⟩ := kpair_inj he
    rfl
  · intro v hv y hy
    obtain ⟨v', hv', he⟩ := mem_mkLam_iff.mp hy
    obtain ⟨rfl, rfl⟩ := kpair_inj he
    exact h v hv

/-- **`lamDF`, part 3.**  The proof branch uses that a proof's denotation is `•`
and that it lies in the codomain; the type branch is `mkLam_mem_mkForallType`.
No inversion. -/
theorem lamDF_sound_type {Γ : List VExpr} {A B body : VExpr} {ρ : V}
    (hsplit : L.IsProof M (A :: Γ) body ↔ L.IsProp M (A :: Γ) B)
    (h3 : ∀ v ∈ (interp M L Γ A).toFun ρ,
      (interp M L (A :: Γ) body).toFun (snoc ρ v) ∈ (interp M L (A :: Γ) B).toFun (snoc ρ v))
    (h2 : L.IsProof M (A :: Γ) body → ∀ v ∈ (interp M L Γ A).toFun ρ,
      (interp M L (A :: Γ) body).toFun (snoc ρ v) = pt) :
    (interp M L Γ (.lam A body)).toFun ρ ∈ (interp M L Γ (.forallE A B)).toFun ρ := by
  by_cases hp : L.IsProof M (A :: Γ) body
  · rw [interp_lam_proof M L hp, interp_forallE_prop M L (hsplit.mp hp)]
    refine mem_mkForallProp_iff.mpr ⟨rfl, fun v hv ↦ ?_⟩
    rw [← h2 hp v hv]
    exact h3 v hv
  · rw [interp_lam_type M L hp, interp_forallE_type M L (fun x ↦ hp (hsplit.mpr x))]
    exact mkLam_mem_mkForallType h3

/-- The `forallE` clause lands in a universe.  **This is the second and last
place the universe bound is spent**, and — unlike `sortDF` — it is spent through
the *closure* properties of the stage (`repl_mem_vsetV'`, `sUnion_mem_U`,
`function_mem_U`), not through `U_mem_succ`.  It needs `i < n`. -/
theorem mkForallType_mem_U {n : ℕ} {κ : ℕ → V} (hκ : IsInaccessibleChain n κ) {i : ℕ}
    (hi : i < n) {G : V → V} {hG : ℒₛₑₜ-function₁[V] G} {F : V → V → V}
    {hF : ℒₛₑₜ-function₂[V] F} {ρ : V}
    (hGm : G ρ ∈ U κ (i + 1)) (hFm : ∀ v ∈ G ρ, F ρ v ∈ U κ (i + 1)) :
    mkForallType G hG F hF ρ ∈ U κ (i + 1) := by
  have hk := hκ.inaccessible i hi
  have hko : IsOrdinal (κ i) := hk.isOrdinal
  have hrepl : repl (F ρ) (by definability) (G ρ) ∈ U κ (i + 1) := by
    rw [U_succ] at hGm hFm ⊢
    exact repl_mem_vsetV' hk hGm (F ρ) (by definability) hFm
  have hfam : mkFamUnion G hG F hF ρ ∈ U κ (i + 1) := by
    rw [mkFamUnion]; exact sUnion_mem_U hko hrepl
  exact mem_U_of_subset_of_mem hko sep_subset (function_mem_U hκ hi hGm hfam)

/-- **`forallEDF`, part 3, `Prop` branch.**  A `∀` over a proposition lands in
`U₀` with **no** universe bound at all — this is impredicativity, and it is why
the `Prop` layer of a derivation contributes nothing to `n`. -/
theorem forallEDF_sound_prop {Γ : List VExpr} {A B : VExpr} (hp : L.IsProp M (A :: Γ) B)
    (ρ : V) : (interp M L Γ (.forallE A B)).toFun ρ ∈ (UProp : V) :=
  interp_forallE_prop_mem_UProp M L hp ρ

/-- **`forallEDF`, part 3, type branch.**  `i + 1` is the target universe index
— `(imax u v).eval` when `v.eval ≠ 0` — and `hi : i < n` is the bound. -/
theorem forallEDF_sound_type {n : ℕ} {κ : ℕ → V} (hκ : IsInaccessibleChain n κ) {i : ℕ}
    (hi : i < n) {Γ : List VExpr} {A B : VExpr} {ρ : V} (hp : ¬ L.IsProp M (A :: Γ) B)
    (hA : (interp M L Γ A).toFun ρ ∈ U κ (i + 1))
    (hB : ∀ v ∈ (interp M L Γ A).toFun ρ,
      (interp M L (A :: Γ) B).toFun (snoc ρ v) ∈ U κ (i + 1)) :
    (interp M L Γ (.forallE A B)).toFun ρ ∈ U κ (i + 1) := by
  rw [interp_forallE_type M L hp]
  exact mkForallType_mem_U hκ hi hA hB

end Congruence

/-! ## The constant assignment, and the last two cases

`ModelData.cnst` is supplied rather than computed, which is what made the term
recursion in `SetModel/Interp.lean` structural (`soundness.tex`'s
`|c| = |e| + 1` clause is the reason Carneiro's measure is not).  Discharging it
is what makes that trade honest rather than a relocation: **the well-foundedness
lives here**, in an induction over the declaration list that `VEnv.WF'` already
orders.

Two things make that induction tractable, and both are worth stating.

* **The interpretation is environment-independent.**  `interp M L Γ e` mentions
  `env` only through `L`; it never consults `env.constants` or `env.defeqs`.  So
  as the environment grows along `ds`, earlier terms keep their denotations and
  the induction only ever *extends* `cnst`.  Nothing has to be revisited.
* **Only `cnst` is recursive.**  Everything else in `ModelData` is data.  So the
  recursion to be justified is exactly "a constant's value is the denotation of
  its definition's body", on a list that is already well-ordered by
  `VEnv.WF'`.

What the two cases need from it is packaged as `Coherent`.
-/

section Const

variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {env : VEnv} {nv : ℕ} (M : ModelData V) (L : LevelAssign env nv)

/-- **The obligation on the constant assignment.**  This is the whole of what
`constDF` and `extra` consume, and therefore the specification that the
induction over the declaration list has to meet. -/
structure ModelData.Coherent : Prop where
  /-- a constant's value inhabits its declared type -/
  const_type : ∀ {c : Name} {ci : VConstant} {ls : List VLevel},
    env.constants c = some ci → ls.length = ci.uvars →
    ∀ {Γ : List VExpr} {ρ : V}, ρ ∈ interpCtx M L Γ →
      M.cnst c (ls.map (·.eval M.ls)) ∈ (interp M L Γ (ci.type.instL ls)).toFun ρ
  /-- the environment's definitional equations hold in the model -/
  defeq : ∀ {df : VDefEq} {ls : List VLevel}, env.defeqs df → ls.length = df.uvars →
    ∀ {Γ : List VExpr} {ρ : V}, ρ ∈ interpCtx M L Γ →
      (interp M L Γ (df.lhs.instL ls)).toFun ρ = (interp M L Γ (df.rhs.instL ls)).toFun ρ
  /-- …and both sides inhabit the equated type -/
  defeq_type : ∀ {df : VDefEq} {ls : List VLevel}, env.defeqs df → ls.length = df.uvars →
    ∀ {Γ : List VExpr} {ρ : V}, ρ ∈ interpCtx M L Γ →
      (interp M L Γ (df.lhs.instL ls)).toFun ρ ∈ (interp M L Γ (df.type.instL ls)).toFun ρ

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
theorem map_eval_eq_of_forall₂ : ∀ {ls ls' : List VLevel}, List.Forall₂ (· ≈ ·) ls ls' →
    ls.map (·.eval M.ls) = ls'.map (·.eval M.ls)
  | [], [], _ => rfl
  | _ :: _, _ :: _, .cons h t => by
    simp [VLevel.equiv_def.mp h M.ls, map_eval_eq_of_forall₂ t]

/-- **`constDF`, part 4.**  A constant's denotation depends on the *evaluated*
levels, so equivalent level lists give the same value.  Needs nothing from
`Coherent`. -/
theorem constDF_sound_eq {c : Name} {ls ls' : List VLevel}
    (h : List.Forall₂ (· ≈ ·) ls ls') (Γ : List VExpr) (ρ : V) :
    (interp M L Γ (.const c ls)).toFun ρ = (interp M L Γ (.const c ls')).toFun ρ := by
  rw [interp_const, interp_const, map_eval_eq_of_forall₂ M h]

/-- **`constDF`, part 3.** -/
theorem constDF_sound_type (hC : M.Coherent L) {c : Name} {ci : VConstant} {ls : List VLevel}
    (hc : env.constants c = some ci) (hlen : ls.length = ci.uvars)
    {Γ : List VExpr} {ρ : V} (hρ : ρ ∈ interpCtx M L Γ) :
    (interp M L Γ (.const c ls)).toFun ρ ∈ (interp M L Γ (ci.type.instL ls)).toFun ρ := by
  rw [interp_const]
  exact hC.const_type hc hlen hρ

/-- **`extra`, part 4.**  This is the case the coherence field `defeq` exists
for. -/
theorem extra_sound_eq (hC : M.Coherent L) {df : VDefEq} {ls : List VLevel}
    (hdf : env.defeqs df) (hlen : ls.length = df.uvars)
    {Γ : List VExpr} {ρ : V} (hρ : ρ ∈ interpCtx M L Γ) :
    (interp M L Γ (df.lhs.instL ls)).toFun ρ = (interp M L Γ (df.rhs.instL ls)).toFun ρ :=
  hC.defeq hdf hlen hρ

/-- **`extra`, part 3.** -/
theorem extra_sound_type (hC : M.Coherent L) {df : VDefEq} {ls : List VLevel}
    (hdf : env.defeqs df) (hlen : ls.length = df.uvars)
    {Γ : List VExpr} {ρ : V} (hρ : ρ ∈ interpCtx M L Γ) :
    (interp M L Γ (df.lhs.instL ls)).toFun ρ ∈ (interp M L Γ (df.type.instL ls)).toFun ρ :=
  hC.defeq_type hdf hlen hρ

end Const

/-! ## Towards `cnst`: the two lemmas the construction rests on

`ModelData.cnst` is to be built by induction over the declaration list.  Two
facts make that induction *extend* rather than revisit, and both are made
precise here.
-/

section CnstStep

variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]

/-- `e` mentions only constants on which the two assignments agree. -/
def ConstsAgree (c₁ c₂ : Name → List ℕ → V) (ls : List ℕ) : VExpr → Prop
  | .bvar _ => True
  | .sort _ => True
  | .const n us => c₁ n (us.map (·.eval ls)) = c₂ n (us.map (·.eval ls))
  | .app a b => ConstsAgree c₁ c₂ ls a ∧ ConstsAgree c₁ c₂ ls b
  | .lam a b => ConstsAgree c₁ c₂ ls a ∧ ConstsAgree c₁ c₂ ls b
  | .forallE a b => ConstsAgree c₁ c₂ ls a ∧ ConstsAgree c₁ c₂ ls b

/-- **Environment-independence, made precise.**  The interpretation depends on
the constant assignment only through the constants that actually occur in the
term.  This is the payoff for making `cnst` a parameter instead of unfolding
constants: as the declaration list grows, every term already interpreted keeps
its denotation, so the induction only ever *extends* `cnst`.

Note also that the three proof-splitting decisions do not mention `cnst` at all
— they are `(L.srt Γ ·).eval ls = 0` — so the two sides take the same branch
definitionally, and the proof needs no split-agreement hypothesis. -/
theorem interp_cnst_congr {env : VEnv} {nv : ℕ} (L : LevelAssign env nv)
    {κ : ℕ → V} {ls : List ℕ} {c₁ c₂ : Name → List ℕ → V} :
    ∀ (e : VExpr) (Γ : List VExpr), ConstsAgree c₁ c₂ ls e →
      interp ⟨κ, ls, c₁⟩ L Γ e = interp ⟨κ, ls, c₂⟩ L Γ e
  | .bvar i, Γ, _ => by
    refine DefFun.ext (funext fun ρ ↦ ?_); rw [interp_bvar, interp_bvar]
  | .sort u, Γ, _ => by
    refine DefFun.ext (funext fun ρ ↦ ?_); rw [interp_sort, interp_sort]
  | .const c us, Γ, h => by
    refine DefFun.ext (funext fun ρ ↦ ?_); rw [interp_const, interp_const]; exact h
  | .app f a, Γ, ⟨hf, ha⟩ => by
    refine DefFun.ext (funext fun ρ ↦ ?_)
    by_cases hp : L.IsProof ⟨κ, ls, c₁⟩ Γ f
    · rw [interp_app_proof ⟨κ, ls, c₁⟩ L hp, interp_app_proof ⟨κ, ls, c₂⟩ L hp]
    · rw [interp_app_type ⟨κ, ls, c₁⟩ L hp, interp_app_type ⟨κ, ls, c₂⟩ L hp,
        interp_cnst_congr L f Γ hf, interp_cnst_congr L a Γ ha]
  | .lam A b, Γ, ⟨hA, hb⟩ => by
    refine DefFun.ext (funext fun ρ ↦ ?_)
    by_cases hp : L.IsProof ⟨κ, ls, c₁⟩ (A :: Γ) b
    · rw [interp_lam_proof ⟨κ, ls, c₁⟩ L hp, interp_lam_proof ⟨κ, ls, c₂⟩ L hp]
    · rw [interp_lam_type ⟨κ, ls, c₁⟩ L hp, interp_lam_type ⟨κ, ls, c₂⟩ L hp,
        interp_cnst_congr L A Γ hA, interp_cnst_congr L b (A :: Γ) hb]
  | .forallE A B, Γ, ⟨hA, hB⟩ => by
    refine DefFun.ext (funext fun ρ ↦ ?_)
    by_cases hp : L.IsProp ⟨κ, ls, c₁⟩ (A :: Γ) B
    · rw [interp_forallE_prop ⟨κ, ls, c₁⟩ L hp, interp_forallE_prop ⟨κ, ls, c₂⟩ L hp,
        interp_cnst_congr L A Γ hA, interp_cnst_congr L B (A :: Γ) hB]
    · rw [interp_forallE_type ⟨κ, ls, c₁⟩ L hp, interp_forallE_type ⟨κ, ls, c₂⟩ L hp,
        interp_cnst_congr L A Γ hA, interp_cnst_congr L B (A :: Γ) hB]

/-- A level assignment for a larger environment restricts to one for a smaller.
So a *single* `L` can be fixed for the final environment and used at every stage
of the induction — the assignment never has to be rebuilt as `env` grows. -/
def LevelAssign.mono {env env' : VEnv} {nv : ℕ} (h : env ≤ env')
    (L : LevelAssign env' nv) : LevelAssign env nv where
  lvl := L.lvl
  srt := L.srt
  lvl_wf := L.lvl_wf
  srt_wf := L.srt_wf
  lvl_sound ht := L.lvl_sound (ht.mono h)
  srt_sound ht := L.srt_sound (ht.mono h)

end CnstStep

/-! ## `Coherent` is not provable as stated — axioms have to be validated

Trying to build `cnst` turns up a problem with the target itself, and it is a
real one rather than a technicality.

`Coherent.const_type` says every constant's value inhabits its declared type.
For a **definition** that is discharged by taking the value to be the denotation
of the body.  For an **axiom** there is no body, and `VDecl.WF`'s `.axiom` case
requires only `ci.WF env` — that the declared type *is a type*, not that it is
inhabited.  So

```
axiom bad : False
```

extends a well-formed environment to a well-formed environment, and in the model
`⟦False⟧ρ = ∅`, so no value of `cnst` can satisfy `const_type`.  **`Coherent` is
therefore unprovable for an arbitrary well-formed environment**, and no amount of
care in the induction will fix that.

This is not a defect in the model; it is the correct shape, and it lines up with
the main theorem, which assumes `∀ d ∈ ds, Declaration.IsAxiomFree d` on the
user's declarations and admits only the standard prelude's three axioms — each of
which the model *does* validate:

* `propext` — `propext_of_mem_UProp` (`SetModel/Universe.lean`);
* `Classical.choice` — `exists_choiceFunction_mem_U`, an internal choice function
  living one stage up;
* `Quot.sound` — `eqvClosure`, `setQuotient`, `exists_quotient_lift`.

So the missing hypothesis is exactly "the environment's axioms are validated",
and it is a hypothesis about the *declaration list*, not about the model. -/
section Axioms

variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]

structure AxiomsValidated {env : VEnv} {nv : ℕ} (M : ModelData V)
    (L : LevelAssign env nv) (ds : List VDecl) : Prop where
  axioms : ∀ {ci : VConstVal}, (VDecl.axiom ci) ∈ ds → ∀ {ls : List VLevel},
    ls.length = ci.toVConstant.uvars → ∀ {Γ : List VExpr} {ρ : V}, ρ ∈ interpCtx M L Γ →
      M.cnst ci.name (ls.map (·.eval M.ls))
        ∈ (interp M L Γ (ci.toVConstant.type.instL ls)).toFun ρ

end Axioms

/-!
### What remains of the construction, and what blocks it

With `AxiomsValidated` added, the induction over `ds` splits by `VDecl`:

| Declaration | Value of `cnst` | Status |
|---|---|---|
| `.axiom ci` | supplied by `AxiomsValidated` | ready |
| `.def`, `.opaque`, `.example`, `.mutualDef` | `⟦ci.value⟧` at the earlier assignment | ready |
| `.quot` | `Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind` and `quotDefEq` | `addQuot` is concrete; the model side is in `SetModel/Universe.lean` |
| `.induct` | the constants `addInduct` introduces | **blocked** |

`.induct` is blocked upstream, not here: `VEnv.addInduct` and `VInductDecl.WF`
are still `sorry` *definitions* in `Theory/Inductive.lean`, so the environment
after an inductive declaration is opaque and there is nothing to assign values
to.  The set-theoretic side is ready and waiting — `SetModel/IndStage.lean` and
`SetModel/IndCard.lean` give the family, its constructors, its recursor and its
ι-rule, all as members of the stage — but it cannot be connected until the
abstract spec exists.

So `cnst` is blocked on the same keystone as everything else, and the ledger's
open list is unchanged in length: `sort_inv`, the inductive spec, and now the
axiom-validation hypothesis, which is discharged by the three standard axioms.
-/

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
