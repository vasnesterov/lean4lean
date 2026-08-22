import Lean4Lean.Theory.SetModel.IndCard
import Lean4Lean.Theory.Typing.Basic

/-!
# The interpretation `⟦Γ ⊢ e⟧`, relative to a level assignment

Carneiro's model of Lean's type theory, §6.3: a context is interpreted by its
set of valuations, and a term by a definable function from valuations to values.

The interpretation is blocked on **proof splitting** (`soundness.tex`
§Proof splitting), which is three separate decisions:

* `app f a` — is `f` a *proof*?  Then the application is the proof object `•`
  and the argument is discarded.  Splits on `sort Γ f`.
* `lam A b` — is the body a proof?  Then the lambda is `•`.  Splits on
  `sort (A::Γ) b`.
* `forallE A B` — is `B` a proposition?  Then this is an impredicative `∀`
  (landing in `U₀` for an arbitrary domain), otherwise a dependent product
  `Π` (which is what consumes an inaccessible).  Splits on `lvl (A::Γ) B`.

`lvl` and `sort` rest on unique typing, which in this repository is
`IsDefEqU.sort_inv` — a `sorry` in `Theory/Typing/Injectivity.lean`, gated on
the inductive keystone.  Rather than wait, this file takes them as a
**hypothesis** (`LevelAssign`), so that the whole remaining blocker is the single
obligation "construct a `LevelAssign`".

## What `LevelAssign` actually needs — and what it does not

`LevelAssign` asks only for a canonical level for every type and every term's
type, agreeing with whatever the typing rules give.  That is exactly
`IsDefEqU.sort_inv` in functional form (plus choice), and it is **strictly
weaker than unique typing**: neither `IsDefEqU.forallE_inv` nor
`IsDefEqU.sort_forallE_inv` — the other two `sorry`s in `Injectivity.lean` — is
needed to *define* the interpretation.  See the closing note for where each of
the three is and is not required.

## Two things the recursion does not need

* **There is no `let`.**  `VExpr` is `bvar | sort | const | app | lam | forallE`;
  `let` is elaborated away before this layer.  So the "`let` unfolds by
  substitution" half of Carneiro's non-structural measure does not arise.
* **Constants need not unfold.**  A constant is interpreted by a supplied
  *constant assignment* `cnst : Name → List ℕ → V`, exactly as the universe level
  is supplied by `LevelAssign`.  Constructing the assignment for a well-formed
  environment is a separate induction over the declaration list (`VEnv.WF'`
  already orders it), and it is that induction — not this one — that needs the
  environment's definitions to be well-founded.

With both of those supplied, **the recursion is structural on the term**: no size
measure, no half-integers, no well-founded recursion.  This is the same move the
task brief prescribes for the level assignment, applied once more.

## Definability

Per `docs/model-interface.md` §1, the interpretation is a **bundle** of a
function and its `ℒₛₑₜ`-definability proof (`DefFun`), built simultaneously by
the recursion — definability cannot be bolted on afterwards, because the
set-theoretic combinators (`sep`, `repl`, `piProp`, `PiFun`) *demand* it as an
argument.

A valuation is an internal finite sequence (`snoc` from `IndCard.lean`), so the
interpretation has arity **one** and definability is `ℒₛₑₜ-function₁` throughout,
rather than an arity that grows with the context.
-/

namespace Lean4Lean.SetModel

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LO.FirstOrder.SetTheory.Ordinal (lt_def le_def lt_succ)

variable {V : Type*} [SetStructure V] [Nonempty V]

/-! ## Definable functions, bundled -/

/-- A function `V → V` together with its `ℒₛₑₜ`-definability.  Every
interpretation is presented this way; see `docs/model-interface.md` §1. -/
structure DefFun (V : Type*) [SetStructure V] where
  toFun : V → V
  definable : ℒₛₑₜ-function₁[V] toFun

instance : CoeFun (DefFun V) (fun _ ↦ V → V) := ⟨DefFun.toFun⟩

attribute [instance] DefFun.definable

/-! ## The clause combinators

Each combinator takes the definability of its ingredients up front and comes
with its own definability lemma, proved through the membership characterisation
(`mem_ext_iff`) so that the `autoParam` proofs buried inside `repl`/`sep` never
have to be reasoned about.
-/

section Combinators

variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Extend a valuation by every value in `X`. -/
noncomputable def snocImage (ρ X : V) : V := repl (snoc ρ) (by definability) X

@[simp] lemma mem_snocImage_iff {ρ X y : V} : y ∈ snocImage ρ X ↔ ∃ v ∈ X, y = snoc ρ v :=
  repl_spec _

instance snocImage_definable : ℒₛₑₜ-function₂[V] snocImage := by
  suffices ℒₛₑₜ-relation₃[V] (fun T ρ X ↦ T = snocImage ρ X) by exact this
  have e : ∀ T ρ X : V, T = snocImage ρ X ↔ ∀ y, y ∈ T ↔ ∃ v ∈ X, y = snoc ρ v := by
    intro T ρ X; rw [mem_ext_iff]; simp
  simp only [e]; definability

/-- The valuations of `A :: Γ`: those of `Γ`, each extended by a value of `A`. -/
noncomputable def extendCtx (X : V) (G : V → V) (hG : ℒₛₑₜ-function₁[V] G) : V :=
  ⋃ˢ (repl (fun ρ ↦ snocImage ρ (G ρ)) (by definability) X)

lemma mem_extendCtx_iff {X : V} {G : V → V} {hG : ℒₛₑₜ-function₁[V] G} {r : V} :
    r ∈ extendCtx X G hG ↔ ∃ ρ ∈ X, ∃ v ∈ G ρ, r = snoc ρ v := by
  rw [extendCtx, mem_sUnion_iff]
  constructor
  · rintro ⟨w, hw, hrw⟩
    obtain ⟨ρ, hρ, rfl⟩ := (repl_spec _).mp hw
    obtain ⟨v, hv, rfl⟩ := mem_snocImage_iff.mp hrw
    exact ⟨ρ, hρ, v, hv, rfl⟩
  · rintro ⟨ρ, hρ, v, hv, rfl⟩
    exact ⟨snocImage ρ (G ρ), (repl_spec _).mpr ⟨ρ, hρ, rfl⟩,
      mem_snocImage_iff.mpr ⟨v, hv, rfl⟩⟩

/-- The `lam` clause: the graph of `v ↦ F ρ v` on `G ρ`. -/
noncomputable def mkLam (G : V → V) (_hG : ℒₛₑₜ-function₁[V] G)
    (F : V → V → V) (hF : ℒₛₑₜ-function₂[V] F) (ρ : V) : V :=
  repl (fun v ↦ (⟨v, F ρ v⟩ₖ : V)) (by definability) (G ρ)

lemma mem_mkLam_iff {G : V → V} {hG : ℒₛₑₜ-function₁[V] G} {F : V → V → V}
    {hF : ℒₛₑₜ-function₂[V] F} {ρ y : V} :
    y ∈ mkLam G hG F hF ρ ↔ ∃ v ∈ G ρ, y = ⟨v, F ρ v⟩ₖ := repl_spec _

lemma mkLam_definable (G : V → V) (hG : ℒₛₑₜ-function₁[V] G)
    (F : V → V → V) (hF : ℒₛₑₜ-function₂[V] F) : ℒₛₑₜ-function₁[V] (mkLam G hG F hF) := by
  suffices ℒₛₑₜ-relation[V] (fun T ρ ↦ T = mkLam G hG F hF ρ) by exact this
  have e : ∀ T ρ : V, T = mkLam G hG F hF ρ ↔ ∀ y, y ∈ T ↔ ∃ v ∈ G ρ, y = ⟨v, F ρ v⟩ₖ := by
    intro T ρ; rw [mem_ext_iff]; simp [mem_mkLam_iff]
  simp only [e]; definability

/-- The `forallE` clause when the codomain is a proposition: the impredicative
`∀`, `{•} ∩ ⋂_{v ∈ G ρ} F ρ v`. -/
noncomputable def mkForallProp (G : V → V) (_hG : ℒₛₑₜ-function₁[V] G)
    (F : V → V → V) (hF : ℒₛₑₜ-function₂[V] F) (ρ : V) : V :=
  piProp (G ρ) (F ρ) (by definability)

lemma mem_mkForallProp_iff {G : V → V} {hG : ℒₛₑₜ-function₁[V] G} {F : V → V → V}
    {hF : ℒₛₑₜ-function₂[V] F} {ρ z : V} :
    z ∈ mkForallProp G hG F hF ρ ↔ z = pt ∧ ∀ v ∈ G ρ, z ∈ F ρ v := mem_piProp_iff

lemma mkForallProp_definable (G : V → V) (hG : ℒₛₑₜ-function₁[V] G)
    (F : V → V → V) (hF : ℒₛₑₜ-function₂[V] F) :
    ℒₛₑₜ-function₁[V] (mkForallProp G hG F hF) := by
  suffices ℒₛₑₜ-relation[V] (fun T ρ ↦ T = mkForallProp G hG F hF ρ) by exact this
  have e : ∀ T ρ : V, T = mkForallProp G hG F hF ρ ↔
      ∀ z, z ∈ T ↔ z = pt ∧ ∀ v ∈ G ρ, z ∈ F ρ v := by
    intro T ρ; rw [mem_ext_iff]; simp [mem_mkForallProp_iff]
  simp only [e]; definability

/-- `⋃_{v ∈ G ρ} F ρ v` — the codomain bound of the dependent product. -/
noncomputable def mkFamUnion (G : V → V) (_hG : ℒₛₑₜ-function₁[V] G)
    (F : V → V → V) (hF : ℒₛₑₜ-function₂[V] F) (ρ : V) : V :=
  ⋃ˢ (repl (F ρ) (by definability) (G ρ))

lemma mem_mkFamUnion_iff {G : V → V} {hG : ℒₛₑₜ-function₁[V] G} {F : V → V → V}
    {hF : ℒₛₑₜ-function₂[V] F} {ρ y : V} :
    y ∈ mkFamUnion G hG F hF ρ ↔ ∃ v ∈ G ρ, y ∈ F ρ v := by
  rw [mkFamUnion, mem_sUnion_iff]
  constructor
  · rintro ⟨w, hw, hyw⟩
    obtain ⟨v, hv, rfl⟩ := (repl_spec _).mp hw
    exact ⟨v, hv, hyw⟩
  · rintro ⟨v, hv, hyv⟩
    exact ⟨F ρ v, (repl_spec _).mpr ⟨v, hv, rfl⟩, hyv⟩

lemma mkFamUnion_definable (G : V → V) (hG : ℒₛₑₜ-function₁[V] G)
    (F : V → V → V) (hF : ℒₛₑₜ-function₂[V] F) :
    ℒₛₑₜ-function₁[V] (mkFamUnion G hG F hF) := by
  suffices ℒₛₑₜ-relation[V] (fun T ρ ↦ T = mkFamUnion G hG F hF ρ) by exact this
  have e : ∀ T ρ : V, T = mkFamUnion G hG F hF ρ ↔ ∀ y, y ∈ T ↔ ∃ v ∈ G ρ, y ∈ F ρ v := by
    intro T ρ; rw [mem_ext_iff]; simp [mem_mkFamUnion_iff]
  simp only [e]; definability

/-- The `forallE` clause when the codomain is a proper type: the dependent
product. -/
noncomputable def mkForallType (G : V → V) (hG : ℒₛₑₜ-function₁[V] G)
    (F : V → V → V) (hF : ℒₛₑₜ-function₂[V] F) (ρ : V) : V :=
  {f ∈ ((mkFamUnion G hG F hF ρ) ^ G ρ : V) ;
    ∀ v ∈ G ρ, ∀ y : V, (⟨v, y⟩ₖ : V) ∈ f → y ∈ F ρ v}

lemma mem_mkForallType_iff {G : V → V} {hG : ℒₛₑₜ-function₁[V] G} {F : V → V → V}
    {hF : ℒₛₑₜ-function₂[V] F} {ρ f : V} :
    f ∈ mkForallType G hG F hF ρ ↔
      f ∈ ((mkFamUnion G hG F hF ρ) ^ G ρ : V) ∧
        ∀ v ∈ G ρ, ∀ y : V, (⟨v, y⟩ₖ : V) ∈ f → y ∈ F ρ v := mem_sep_iff

lemma mkForallType_definable (G : V → V) (hG : ℒₛₑₜ-function₁[V] G)
    (F : V → V → V) (hF : ℒₛₑₜ-function₂[V] F) :
    ℒₛₑₜ-function₁[V] (mkForallType G hG F hF) := by
  have hU := mkFamUnion_definable G hG F hF
  suffices ℒₛₑₜ-relation[V] (fun T ρ ↦ T = mkForallType G hG F hF ρ) by exact this
  have e : ∀ T ρ : V, T = mkForallType G hG F hF ρ ↔ ∀ f, f ∈ T ↔
      (f ∈ ((mkFamUnion G hG F hF ρ) ^ G ρ : V) ∧
        ∀ v ∈ G ρ, ∀ y : V, (⟨v, y⟩ₖ : V) ∈ f → y ∈ F ρ v) := by
    intro T ρ; rw [mem_ext_iff]; simp [mem_mkForallType_iff]
  simp only [e]; definability

end Combinators

/-! ## The parameters of the interpretation -/

/-- The set-theoretic data the interpretation runs on: the chain of
inaccessibles giving the universe sequence, the valuation of universe
parameters, and the interpretation of constants.

`cnst` is supplied rather than computed, so that the recursion below need not
unfold constants; see the module docstring. -/
structure ModelData (V : Type*) [SetStructure V] [Nonempty V] where
  κ : ℕ → V
  ls : List ℕ
  cnst : Name → List ℕ → V

/-- **What proof splitting needs.**

Carneiro's `lvl`/`sort` lemma (`soundness.tex` §Proof splitting), packaged.
`lvl Γ A` is the universe level of a *type*; `srt Γ e` is the level of the type
of a *term*, so `srt Γ e = 0` says exactly "`e` is a proof".  Three separate
clauses of the interpretation split on these:

* `app f a` splits on `srt Γ f` — is this a proof application?
* `lam A b` splits on `srt (A::Γ) b` — is this a proof?
* `forallE A B` splits on `lvl (A::Γ) B` — is this a `∀` or a `Π`?

`lvl_sound` is `IsDefEqU.sort_inv` in functional form and `srt_sound` is its
companion for terms; both follow from unique typing, and from them plus choice
one constructs a `LevelAssign`.  Conversely a `LevelAssign` gives back
`sort_inv` for types (`lvl_uniq` below).  **Nothing else about unique typing is
needed to define the interpretation** — in particular neither
`IsDefEqU.forallE_inv` nor `IsDefEqU.sort_forallE_inv`. -/
structure LevelAssign (env : VEnv) (nv : ℕ) where
  /-- the canonical level of a type in a context -/
  lvl : List VExpr → VExpr → VLevel
  /-- the canonical level of the *type of* a term: `srt Γ e = 0` iff `e` is a proof -/
  srt : List VExpr → VExpr → VLevel
  lvl_wf : ∀ Γ A, (lvl Γ A).WF nv
  srt_wf : ∀ Γ e, (srt Γ e).WF nv
  /-- `lvl` agrees with the typing rules wherever they apply -/
  lvl_sound : ∀ {Γ : List VExpr} {A : VExpr} {u : VLevel},
    env.HasType nv Γ A (.sort u) → lvl Γ A ≈ u
  /-- `srt` is the `lvl` of the term's type -/
  srt_sound : ∀ {Γ : List VExpr} {e A : VExpr},
    env.HasType nv Γ e A → srt Γ e ≈ lvl Γ A

namespace LevelAssign

variable {env : VEnv} {nv : ℕ} (L : LevelAssign env nv)

include L in
/-- A `LevelAssign` recovers `sort_inv` for types: two levels of the same type
are equivalent. -/
theorem lvl_uniq {Γ : List VExpr} {A : VExpr} {u v : VLevel}
    (hu : env.HasType nv Γ A (.sort u)) (hv : env.HasType nv Γ A (.sort v)) : u ≈ v :=
  (L.lvl_sound hu).symm.trans (L.lvl_sound hv)

include L in
/-- Definitionally equal types get equivalent levels. -/
theorem lvl_congr {Γ : List VExpr} {A A' : VExpr} {u : VLevel}
    (h : env.IsDefEq nv Γ A A' (.sort u)) : L.lvl Γ A ≈ L.lvl Γ A' :=
  (L.lvl_sound (h.trans h.symm)).trans (L.lvl_sound (h.symm.trans h)).symm

include L in
/-- Definitionally equal *terms* get equivalent sorts — so the case splits in
the interpretation are stable under `≡`, which is what the soundness induction
needs in the compatibility cases. -/
theorem srt_congr {Γ : List VExpr} {e e' A : VExpr} (h : env.IsDefEq nv Γ e e' A) :
    L.srt Γ e ≈ L.srt Γ e' :=
  (L.srt_sound (h.trans h.symm)).trans (L.srt_sound (h.symm.trans h)).symm

/-- Proof splitting, on types: `A` is a *proposition* when its canonical level
evaluates to `0`. -/
def IsProp (M : ModelData V) (Γ : List VExpr) (A : VExpr) : Prop :=
  (L.lvl Γ A).eval M.ls = 0

/-- Proof splitting, on terms: `e` is a *proof* when the level of its type
evaluates to `0`.  Its interpretation is then the single proof object `•`. -/
def IsProof (M : ModelData V) (Γ : List VExpr) (e : VExpr) : Prop :=
  (L.srt Γ e).eval M.ls = 0

instance (M : ModelData V) (Γ : List VExpr) (A : VExpr) : Decidable (L.IsProp M Γ A) :=
  inferInstanceAs (Decidable (_ = _))

instance (M : ModelData V) (Γ : List VExpr) (e : VExpr) : Decidable (L.IsProof M Γ e) :=
  inferInstanceAs (Decidable (_ = _))

end LevelAssign

/-! ## The interpretation -/

section Interp

variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {env : VEnv} {nv : ℕ} (M : ModelData V) (L : LevelAssign env nv)

/-- `⟦Γ ⊢ e⟧` as a bundle of a function on valuations and its definability.

The recursion is **structural on `e`**; the context is a parameter that grows in
the binder cases.  `Γ` feeds the level assignment in the three clauses where
proof splitting happens: `app`, `lam` and `forallE`. -/
noncomputable def interp : List VExpr → VExpr → DefFun V
  | Γ, .bvar i => ⟨fun ρ ↦ ρ ‘ ((Γ.length - 1 - i : ℕ) : V), by definability⟩
  | _, .sort u => ⟨fun _ ↦ U M.κ (u.eval M.ls), by definability⟩
  | _, .const c us => ⟨fun _ ↦ M.cnst c (us.map (·.eval M.ls)), by definability⟩
  | Γ, .app f a =>
    if L.IsProof M Γ f then ⟨fun _ ↦ (pt : V), by definability⟩
    else ⟨fun ρ ↦ ((interp Γ f).toFun ρ) ‘ ((interp Γ a).toFun ρ), by
      have := (interp Γ f).definable
      have := (interp Γ a).definable
      definability⟩
  | Γ, .lam A b =>
    if L.IsProof M (A :: Γ) b then ⟨fun _ ↦ (pt : V), by definability⟩
    else ⟨mkLam (interp Γ A).toFun (interp Γ A).definable
        (fun ρ v ↦ (interp (A :: Γ) b).toFun (snoc ρ v))
        (by have := (interp (A :: Γ) b).definable; definability),
      mkLam_definable _ _ _ _⟩
  | Γ, .forallE A B =>
    if L.IsProp M (A :: Γ) B then
      ⟨mkForallProp (interp Γ A).toFun (interp Γ A).definable
          (fun ρ v ↦ (interp (A :: Γ) B).toFun (snoc ρ v))
          (by have := (interp (A :: Γ) B).definable; definability),
        mkForallProp_definable _ _ _ _⟩
    else
      ⟨mkForallType (interp Γ A).toFun (interp Γ A).definable
          (fun ρ v ↦ (interp (A :: Γ) B).toFun (snoc ρ v))
          (by have := (interp (A :: Γ) B).definable; definability),
        mkForallType_definable _ _ _ _⟩

/-- `⟦Γ⟧`: the set of valuations of the context `Γ`, as internal finite
sequences.  Innermost-first in `Γ` corresponds to last-appended in the
sequence. -/
noncomputable def interpCtx : List VExpr → V
  | [] => {(∅ : V)}
  | A :: Γ => extendCtx (interpCtx Γ) (interp M L Γ A).toFun (interp M L Γ A).definable

lemma interpCtx_nil : interpCtx M L [] = ({∅} : V) := by rw [interpCtx]

lemma mem_interpCtx_cons {A : VExpr} {Γ : List VExpr} {r : V} :
    r ∈ interpCtx M L (A :: Γ) ↔
      ∃ ρ ∈ interpCtx M L Γ, ∃ v ∈ (interp M L Γ A).toFun ρ, r = snoc ρ v := by
  rw [interpCtx]; exact mem_extendCtx_iff

/-! ### The defining equations -/

lemma interp_bvar (Γ : List VExpr) (i : ℕ) (ρ : V) :
    (interp M L Γ (.bvar i)).toFun ρ = ρ ‘ ((Γ.length - 1 - i : ℕ) : V) := by
  rw [interp]

lemma interp_sort (Γ : List VExpr) (u : VLevel) (ρ : V) :
    (interp M L Γ (.sort u)).toFun ρ = U M.κ (u.eval M.ls) := by rw [interp]

lemma interp_const (Γ : List VExpr) (c : Name) (us : List VLevel) (ρ : V) :
    (interp M L Γ (.const c us)).toFun ρ = M.cnst c (us.map (·.eval M.ls)) := by rw [interp]

/-- A proof application is the proof object; the value is discarded. -/
lemma interp_app_proof {Γ : List VExpr} {f a : VExpr} (h : L.IsProof M Γ f) (ρ : V) :
    (interp M L Γ (.app f a)).toFun ρ = pt := by rw [interp, if_pos h]

lemma interp_app_type {Γ : List VExpr} {f a : VExpr} (h : ¬L.IsProof M Γ f) (ρ : V) :
    (interp M L Γ (.app f a)).toFun ρ =
      ((interp M L Γ f).toFun ρ) ‘ ((interp M L Γ a).toFun ρ) := by rw [interp, if_neg h]

/-- A proof lambda is the proof object; the body is discarded. -/
lemma interp_lam_proof {Γ : List VExpr} {A b : VExpr} (h : L.IsProof M (A :: Γ) b) (ρ : V) :
    (interp M L Γ (.lam A b)).toFun ρ = pt := by rw [interp, if_pos h]

lemma interp_lam_type {Γ : List VExpr} {A b : VExpr} (h : ¬L.IsProof M (A :: Γ) b) (ρ : V) :
    (interp M L Γ (.lam A b)).toFun ρ =
      mkLam (interp M L Γ A).toFun (interp M L Γ A).definable
        (fun ρ v ↦ (interp M L (A :: Γ) b).toFun (snoc ρ v))
        (by have := (interp M L (A :: Γ) b).definable; definability) ρ := by
  rw [interp, if_neg h]

lemma mem_interp_lam_iff {Γ : List VExpr} {A b : VExpr} (h : ¬L.IsProof M (A :: Γ) b)
    {ρ y : V} :
    y ∈ (interp M L Γ (.lam A b)).toFun ρ ↔
      ∃ v ∈ (interp M L Γ A).toFun ρ,
        y = ⟨v, (interp M L (A :: Γ) b).toFun (snoc ρ v)⟩ₖ := by
  rw [interp_lam_type M L h]; exact mem_mkLam_iff

/-- **Proof splitting, as an equation.**  A `∀` over a propositional codomain is
the impredicative one, which lands in `U₀` for an arbitrary domain — this is the
clause that makes `Prop` impredicative in the model. -/
lemma interp_forallE_prop {Γ : List VExpr} {A B : VExpr} (h : L.IsProp M (A :: Γ) B) (ρ : V) :
    (interp M L Γ (.forallE A B)).toFun ρ =
      mkForallProp (interp M L Γ A).toFun (interp M L Γ A).definable
        (fun ρ v ↦ (interp M L (A :: Γ) B).toFun (snoc ρ v))
        (by have := (interp M L (A :: Γ) B).definable; definability) ρ := by
  rw [interp, if_pos h]

lemma interp_forallE_type {Γ : List VExpr} {A B : VExpr} (h : ¬L.IsProp M (A :: Γ) B) (ρ : V) :
    (interp M L Γ (.forallE A B)).toFun ρ =
      mkForallType (interp M L Γ A).toFun (interp M L Γ A).definable
        (fun ρ v ↦ (interp M L (A :: Γ) B).toFun (snoc ρ v))
        (by have := (interp M L (A :: Γ) B).definable; definability) ρ := by
  rw [interp, if_neg h]

lemma mem_interp_forallE_prop_iff {Γ : List VExpr} {A B : VExpr} (h : L.IsProp M (A :: Γ) B)
    {ρ z : V} :
    z ∈ (interp M L Γ (.forallE A B)).toFun ρ ↔
      z = pt ∧ ∀ v ∈ (interp M L Γ A).toFun ρ,
        z ∈ (interp M L (A :: Γ) B).toFun (snoc ρ v) := by
  rw [interp_forallE_prop M L h]; exact mem_mkForallProp_iff

/-- **A `∀` over a proposition lands in `U₀` — for an arbitrary domain.**  No
hypothesis on the universe level of `A` appears, which is the model's statement
that impredicativity is free. -/
theorem interp_forallE_prop_mem_UProp {Γ : List VExpr} {A B : VExpr}
    (h : L.IsProp M (A :: Γ) B) (ρ : V) :
    (interp M L Γ (.forallE A B)).toFun ρ ∈ (UProp : V) := by
  rw [interp_forallE_prop M L h, mkForallProp]
  exact piProp_mem_UProp _ _ _

end Interp

end Lean4Lean.SetModel

/-!
## Status

**Done, and compiling.**  `LevelAssign` (the packaged hypothesis), `ModelData`,
`interp` (all six clauses, with the three proof-splitting decisions), `interpCtx`,
every defining equation, and definability throughout — the interpretation is a
`DefFun`, so `ℒₛₑₜ`-definability is produced by the same recursion rather than
bolted on.  Plus `interp_forallE_prop_mem_UProp`: a `∀` over a proposition lands
in `U₀` for an arbitrary domain, which is the model's statement that
impredicativity costs nothing.

**The recursion is structural.**  Carneiro's size measure
(`soundness.tex:127-137`) is non-structural for exactly two reasons —
`|let x:α := e₁ in e₂| = |e₂[e₁/x]| + 1` and `|c| = |e| + 1` for `def c := e` —
and the half-integers exist to make `|Γ ⊢ α| < |Γ, x:α|` strict.  Neither reason
survives here:

* `VExpr` has **no** `let`; it is elaborated away before this layer.
* Constants are supplied by `ModelData.cnst` rather than unfolded.

So there is no size measure, no half-integers, and no well-founded recursion in
this file.  The well-foundedness that Carneiro's `|c| = |e| + 1` clause needs —
which he never states, but which requires the environment to be acyclic — is
displaced into the *construction* of `cnst`, an induction over the declaration
list that `VEnv.WF'` already orders.  That is a genuinely separate obligation and
it is not attempted here.

## What remains

1. **Construct a `LevelAssign`.**  Needs `IsDefEqU.sort_inv` only.  This is the
   headline: the interpretation now waits on one `sorry`, not on three streams.
2. **Construct `cnst`**, by induction over the declaration list, together with
   its coherence (`cnst` validates `env.defeqs`).
3. **Weakening and substitution.**  Carneiro's substitution lemma
   (`soundness.tex:206-214`) is entangled with the main induction: it needs
   `⟦Γ ⊢ e₂⟧_γ ∈ ⟦Γ ⊢ α⟧_γ`, which is soundness for `e₂`.  State it with that as
   an explicit hypothesis, as he does, rather than trying to prove it first.
4. **Soundness**, by induction on `IsDefEq`, in the four-part form
   (`soundness.tex:216`): propositions are subsets of `{•}`; proofs are `•`;
   `⟦e⟧_γ ∈ ⟦α⟧_γ`; and `≡` is equality.  In schema form with the explicit bound
   of `docs/model-interface.md` §3, never `∃ k`.

Where the other two injectivity `sorry`s would be needed, for the record:
`IsDefEqU.forallE_inv` in the `appDF`/`lamDF` congruence cases of soundness (to
know the domains agree), and `IsDefEqU.sort_forallE_inv` to rule out a type being
both a sort and a `∀`.  Neither is needed for anything in this file.
-/
