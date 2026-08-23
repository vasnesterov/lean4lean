import Lean4Lean.Theory.SetModel.PreludeSpec
import Lean4Lean.Theory.Inductive.Decl

/-!
# `interpSig`: handing the model an `IndSignature`

`docs/model-interface.md` §2 asks the syntax side for a function

```lean
def interpSig (D : VInductDecl') (levels : ℕ → ℕ) (params : V) : IndSignature V
```

together with two proofs, `interpSig_stage` and `interpSig_wf`.  §4 settles the
shape: **the signature is unconditional data and every property about it is
`Above`-wrapped**, because `cnstOf`'s `.induct` line feeds a plain
`o : Name → List VLevel → V` while `OracleOK`'s own fields are already wrapped.

This file builds the two primitives the assembly needs, in the order it needs
them.  Both are about *definability*, which is the whole difficulty: an
`IndSignature` bundles four definability proofs, so every component has to be
definable **jointly in all its arguments** before it can be handed over.

## The two primitives

* **`teleFun`** — the dependent sum of a telescope whose entries' domains are
  given by definable families of the valuation so far.  `Idx`, `Fld` and `Pos`
  are all instances of it.  It is *not* stated over a `List VExpr`, and that is
  deliberate: `Fld` must skip the recursive fields, whose types mention the
  block, so its telescope is not the syntactic one.  Taking `List (DefFun V)`
  lets the caller choose each domain — `⟦A⟧` at a non-recursive field, a
  singleton at a recursive one — and keeps this file free of the `NoBlock`
  question entirely.

* **`tagCase`** — a finite case split on a constructor tag.  `Q` is the numeral
  `nmin`, so `Fld`, `Pos`, `posIdx` and `resIdx` are all functions *of the tag*
  and have to dispatch on it definably.

Both are stated so that the definability proof is available at the point of
definition, which is what `mkFamUnion` demands: it takes the fibre map's
definability as an argument, so a bundled `DefFun` result is the only shape in
which the recursion can be written at all.
-/

namespace Lean4Lean.SetModel

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open scoped Classical

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]

/-! ## Telescopes of definable domains

`teleFun Gs ρ` is the set of valuations extending `ρ` by one value from each
`G ∈ Gs` in order, each `G` seeing the valuation built so far.  This is the
dependent sum of the telescope, in the same `snoc`-indexed encoding `interpCtx`
uses, so its elements are usable as `interp` valuations directly. -/

/-- **The dependent sum of a telescope of definable domains.**

Returned as a `DefFun` rather than a bare function because the recursion cannot
be written otherwise: `mkFamUnion` takes the fibre map's definability as an
argument, so each step needs the previous step's definability *at definition
time*.  This is the same reason `interp` is `DefFun`-valued. -/
noncomputable def teleFun : List (DefFun V) → DefFun V
  | [] => ⟨fun ρ ↦ ({ρ} : V), by definability⟩
  | G :: Gs =>
    ⟨mkFamUnion G.toFun G.definable (fun ρ x ↦ (teleFun Gs).toFun (snoc ρ x))
        (by have := (teleFun Gs).definable; definability),
      mkFamUnion_definable _ _ _ _⟩

@[simp] theorem teleFun_nil (ρ : V) : (teleFun ([] : List (DefFun V))).toFun ρ = {ρ} := rfl

theorem mem_teleFun_nil {ρ y : V} :
    y ∈ (teleFun ([] : List (DefFun V))).toFun ρ ↔ y = ρ := by
  rw [teleFun_nil]; exact mem_singleton_iff

theorem mem_teleFun_cons {G : DefFun V} {Gs : List (DefFun V)} {ρ y : V} :
    y ∈ (teleFun (G :: Gs)).toFun ρ ↔
      ∃ x ∈ G.toFun ρ, y ∈ (teleFun Gs).toFun (snoc ρ x) := by
  simp only [teleFun]; exact mem_mkFamUnion_iff

/-- **Elements of a telescope's sum are extensions of the base valuation.**
This is what lets a `teleFun` element be read back with `IsSeq.read_lt` and
`IsSeq.read_top`: it really is a valuation of the extended context. -/
theorem teleFun_isSeq : ∀ (Gs : List (DefFun V)) {ρ σ : V} {n : ℕ},
    IsSeq ρ n → σ ∈ (teleFun Gs).toFun ρ → IsSeq σ (n + Gs.length)
  | [], _, _, _, hρ, hσ => by
    rw [mem_teleFun_nil] at hσ; subst hσ; simpa using hρ
  | G :: Gs, ρ, σ, n, hρ, hσ => by
    obtain ⟨x, -, hx⟩ := mem_teleFun_cons.1 hσ
    have := teleFun_isSeq Gs (hρ.snoc' (v := x)) hx
    simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this

/-- The base valuation is not disturbed: a telescope element agrees with `ρ`
everywhere below `ρ`'s length. -/
theorem teleFun_read : ∀ (Gs : List (DefFun V)) {ρ σ : V} {n j : ℕ},
    IsSeq ρ n → σ ∈ (teleFun Gs).toFun ρ → j < n →
      σ ‘ ((j : ℕ) : V) = ρ ‘ ((j : ℕ) : V)
  | [], _, _, _, _, _, hσ, _ => by rw [mem_teleFun_nil] at hσ; subst hσ; rfl
  | G :: Gs, ρ, σ, n, j, hρ, hσ, hj => by
    obtain ⟨x, -, hx⟩ := mem_teleFun_cons.1 hσ
    rw [teleFun_read Gs (hρ.snoc' (v := x)) hx (by omega), hρ.read_lt hj]

/-! ## Finite case split on a constructor tag

`Q` is the numeral `D.nmin`, so `Fld`, `Pos`, `posIdx` and `resIdx` dispatch on
a tag.  The split has to be *definable*, which rules out `List.get?` and forces
a chain of definable equality tests. -/

/-- A definable two-way split on an equality with a fixed set. -/
theorem ite_eq_definable₁ {c : V} {f g : V → V}
    (hf : ℒₛₑₜ-function₁[V] f) (hg : ℒₛₑₜ-function₁[V] g) :
    ℒₛₑₜ-function₁[V] (fun q ↦ if q = c then f q else g q) := by
  suffices ℒₛₑₜ-relation[V] (fun T q ↦ T = if q = c then f q else g q) by exact this
  have e : ∀ T q : V, (T = if q = c then f q else g q) ↔
      ((q = c → T = f q) ∧ (q ≠ c → T = g q)) := by
    intro T q; by_cases h : q = c <;> simp [h]
  simp only [e]
  definability

theorem ite_eq_definable₂ {c : V} {f g : V → V → V}
    (hf : ℒₛₑₜ-function₂[V] f) (hg : ℒₛₑₜ-function₂[V] g) :
    ℒₛₑₜ-function₂[V] (fun q a ↦ if q = c then f q a else g q a) := by
  suffices ℒₛₑₜ-relation₃[V] (fun T q a ↦ T = if q = c then f q a else g q a) by exact this
  have e : ∀ T q a : V, (T = if q = c then f q a else g q a) ↔
      ((q = c → T = f q a) ∧ (q ≠ c → T = g q a)) := by
    intro T q a; by_cases h : q = c <;> simp [h]
  simp only [e]
  definability

theorem ite_eq_definable₃ {c : V} {f g : V → V → V → V}
    (hf : ℒₛₑₜ-function₃[V] f) (hg : ℒₛₑₜ-function₃[V] g) :
    ℒₛₑₜ-function₃[V] (fun q a b ↦ if q = c then f q a b else g q a b) := by
  suffices ℒₛₑₜ-relation₄[V] (fun T q a b ↦ T = if q = c then f q a b else g q a b) by
    exact this
  have e : ∀ T q a b : V, (T = if q = c then f q a b else g q a b) ↔
      ((q = c → T = f q a b) ∧ (q ≠ c → T = g q a b)) := by
    intro T q a b; by_cases h : q = c <;> simp [h]
  simp only [e]
  definability

/-- **Dispatch on a tag**, one argument.  `tagCase₁ i fs q` is `fs[q - i] q`
when `q` is the numeral of an index in range, and `∅` otherwise. -/
noncomputable def tagCase₁ : ℕ → List (V → V) → V → V
  | _, [], _ => ∅
  | i, f :: fs, q => if q = ((i : ℕ) : V) then f q else tagCase₁ (i + 1) fs q

noncomputable def tagCase₂ : ℕ → List (V → V → V) → V → V → V
  | _, [], _, _ => ∅
  | i, f :: fs, q, a => if q = ((i : ℕ) : V) then f q a else tagCase₂ (i + 1) fs q a

noncomputable def tagCase₃ : ℕ → List (V → V → V → V) → V → V → V → V
  | _, [], _, _, _ => ∅
  | i, f :: fs, q, a, b =>
    if q = ((i : ℕ) : V) then f q a b else tagCase₃ (i + 1) fs q a b

theorem tagCase₁_definable : ∀ (i : ℕ) (fs : List (V → V)),
    (∀ f ∈ fs, ℒₛₑₜ-function₁[V] f) → ℒₛₑₜ-function₁[V] (tagCase₁ i fs)
  | i, [], _ => by
    have h0 : (tagCase₁ i ([] : List (V → V)) : V → V) = fun _ ↦ (∅ : V) := rfl
    rw [h0]; definability
  | i, f :: fs, h => by
    have hf := h f (.head _)
    have hrest := tagCase₁_definable (i + 1) fs fun g hg ↦ h g (.tail _ hg)
    have : (tagCase₁ i (f :: fs) : V → V)
        = fun q ↦ if q = ((i : ℕ) : V) then f q else tagCase₁ (i + 1) fs q := rfl
    rw [this]
    exact ite_eq_definable₁ hf hrest

theorem tagCase₂_definable : ∀ (i : ℕ) (fs : List (V → V → V)),
    (∀ f ∈ fs, ℒₛₑₜ-function₂[V] f) → ℒₛₑₜ-function₂[V] (tagCase₂ i fs)
  | i, [], _ => by
    have h0 : (tagCase₂ i ([] : List (V → V → V)) : V → V → V) = fun _ _ ↦ (∅ : V) := rfl
    rw [h0]; definability
  | i, f :: fs, h => by
    have hf := h f (.head _)
    have hrest := tagCase₂_definable (i + 1) fs fun g hg ↦ h g (.tail _ hg)
    have : (tagCase₂ i (f :: fs) : V → V → V)
        = fun q a ↦ if q = ((i : ℕ) : V) then f q a else tagCase₂ (i + 1) fs q a := rfl
    rw [this]
    exact ite_eq_definable₂ hf hrest

theorem tagCase₃_definable : ∀ (i : ℕ) (fs : List (V → V → V → V)),
    (∀ f ∈ fs, ℒₛₑₜ-function₃[V] f) → ℒₛₑₜ-function₃[V] (tagCase₃ i fs)
  | i, [], _ => by
    have h0 : (tagCase₃ i ([] : List (V → V → V → V)) : V → V → V → V) = fun _ _ _ ↦ (∅ : V) := rfl
    rw [h0]; definability
  | i, f :: fs, h => by
    have hf := h f (.head _)
    have hrest := tagCase₃_definable (i + 1) fs fun g hg ↦ h g (.tail _ hg)
    have : (tagCase₃ i (f :: fs) : V → V → V → V)
        = fun q a b ↦ if q = ((i : ℕ) : V) then f q a b else tagCase₃ (i + 1) fs q a b := rfl
    rw [this]
    exact ite_eq_definable₃ hf hrest

/-! ### Reading the dispatch back

The tags are the numerals `0, …, nmin-1`, and `ofNat_ne_ofNat` makes the chain
of tests decide correctly, so a tag in range selects its own entry. -/

theorem tagCase₁_at : ∀ (i : ℕ) (fs : List (V → V)) (k : ℕ) (f : V → V),
    fs[k]? = some f → tagCase₁ i fs (((i + k : ℕ) : V)) = f (((i + k : ℕ) : V))
  | i, g :: fs, 0, f, h => by
    have hgf : g = f := by simpa using h
    subst hgf
    show (if (((i + 0 : ℕ) : V)) = ((i : ℕ) : V) then _ else _) = _
    rw [if_pos (by simp)]
  | i, g :: fs, k + 1, f, h => by
    show (if (((i + (k + 1) : ℕ) : V)) = ((i : ℕ) : V) then _ else _) = _
    rw [if_neg (ofNat_ne_ofNat (by omega))]
    have ih := tagCase₁_at (i + 1) fs k f (by simpa using h)
    have e : i + 1 + k = i + (k + 1) := by omega
    rw [e] at ih
    exact ih

/-! ## Tagged unions

`Idx` for a mutual block is the disjoint union of the per-type index sets, and
`Pos q a` is the disjoint union over the constructor's recursive fields.
`disjUnion` (`SetModel/Inaccessible.lean`) is binary; both of these are `n`-ary
over a list, and both need to be definable *in the valuation*, so the entries
are given as functions. -/

/-- The `n`-ary tagged union: `⟨numeral k, y⟩ₖ` for `y ∈ As[k - i] a`. -/
noncomputable def tagUnionF : ℕ → List (V → V) → V → V
  | _, [], _ => ∅
  | i, A :: As, a => ((({((i : ℕ) : V)} : V) ×ˢ A a) ∪ tagUnionF (i + 1) As a)

theorem mem_tagUnionF_nil {i : ℕ} {a p : V} :
    p ∈ tagUnionF i ([] : List (V → V)) a ↔ False := by
  show p ∈ (∅ : V) ↔ _; simp

theorem mem_tagUnionF_cons {i : ℕ} {A : V → V} {As : List (V → V)} {a p : V} :
    p ∈ tagUnionF i (A :: As) a ↔
      (∃ y ∈ A a, p = ⟨((i : ℕ) : V), y⟩ₖ) ∨ p ∈ tagUnionF (i + 1) As a := by
  show p ∈ (_ ∪ _ : V) ↔ _
  rw [mem_union_iff]
  refine or_congr_left ?_
  rw [mem_prod_iff]
  exact ⟨fun ⟨x, hx, y, hy, he⟩ ↦ ⟨y, hy, by rw [he, mem_singleton_iff.1 hx]⟩,
    fun ⟨y, hy, he⟩ ↦ ⟨_, mem_singleton_iff.2 rfl, y, hy, he⟩⟩

theorem tagUnionF_definable : ∀ (i : ℕ) (As : List (V → V)),
    (∀ A ∈ As, ℒₛₑₜ-function₁[V] A) → ℒₛₑₜ-function₁[V] (tagUnionF i As)
  | i, [], _ => by
    have h0 : (tagUnionF i ([] : List (V → V)) : V → V) = fun _ ↦ (∅ : V) := rfl
    rw [h0]; definability
  | i, A :: As, h => by
    have hA := h A (.head _)
    have hrest := tagUnionF_definable (i + 1) As fun B hB ↦ h B (.tail _ hB)
    have h0 : (tagUnionF i (A :: As) : V → V)
        = fun a ↦ ((({((i : ℕ) : V)} : V) ×ˢ A a) ∪ tagUnionF (i + 1) As a) := rfl
    rw [h0]; definability

/-! ## Decoding a tagged position

`posIdx q a b` receives `b ∈ Pos q a`, which is `⟨numeral k, x⟩ₖ`, and needs
both `k` and the payload `x`.  Foundation has `kpair` and `kpair_inj` but **no
projection**, and writing one directly needs a bounded search.

It is not needed. `{⟨u, v⟩ₖ}` is already an internal *function* sending `u` to
`v` — Foundation proves `IsFunction ({⟨x, y⟩ₖ} : V)` — so the payload is
`({b} : V) ‘ numeral k`, and definability is `value`'s. Reusing an existing
definable operation beats adding a primitive. -/

/-- The payload of a position tagged `i`. -/
noncomputable def tagPayload (i : ℕ) (b : V) : V := ({b} : V) ‘ ((i : ℕ) : V)

@[simp] theorem tagPayload_kpair (i : ℕ) (x : V) :
    tagPayload i (⟨((i : ℕ) : V), x⟩ₖ : V) = x :=
  value_eq_of_kpair_mem (mem_singleton_iff.2 rfl)

theorem tagPayload_definable (i : ℕ) : ℒₛₑₜ-function₁[V] (tagPayload (V := V) i) := by
  unfold tagPayload; definability

/-- A definable split on a definable *relation*, not just on equality with a
constant — which is what decoding a tag needs. -/
theorem ite_rel_definable₂ {P : V → V → Prop} (hP : ℒₛₑₜ-relation[V] P)
    {f g : V → V → V} (hf : ℒₛₑₜ-function₂[V] f) (hg : ℒₛₑₜ-function₂[V] g) :
    ℒₛₑₜ-function₂[V] (fun a b ↦ if P a b then f a b else g a b) := by
  suffices ℒₛₑₜ-relation₃[V] (fun T a b ↦ T = if P a b then f a b else g a b) by exact this
  have e : ∀ T a b : V, (T = if P a b then f a b else g a b) ↔
      ((P a b → T = f a b) ∧ (¬ P a b → T = g a b)) := by
    intro T a b; by_cases h : P a b <;> simp [h]
  simp only [e]
  definability

/-- **Dispatch on a position's tag.**  `tagSel₂ i ps a b` applies `ps[k - i]` to
`a` and `b`'s payload when `b` carries tag `k` in range. -/
noncomputable def tagSel₂ : ℕ → List (V → V → V) → V → V → V
  | _, [], _, _ => ∅
  | i, p :: ps, a, b =>
    if b = (⟨((i : ℕ) : V), tagPayload i b⟩ₖ : V) then p a (tagPayload i b)
    else tagSel₂ (i + 1) ps a b

/-- "Is `b` the pair tagged `c` with payload `t b`?", as a definable relation.

Stated with `t` **abstract**.  With `tagPayload` written out, `definability`
diverges rather than merely running deep — the documented first failure mode of
`SetModel/Definability.lean`: `tagPayload` unfolds to `value` of a singleton,
and the search chases the unfolding. Abstracting the function is what stops it,
and is cheaper than raising any limit. -/
theorem eq_kpair_definable {t : V → V} (ht : ℒₛₑₜ-function₁[V] t) (c : V) :
    ℒₛₑₜ-relation[V] (fun (_ b : V) ↦ b = (⟨c, t b⟩ₖ : V)) := by definability

theorem tagSel₂_definable : ∀ (i : ℕ) (ps : List (V → V → V)),
    (∀ p ∈ ps, ℒₛₑₜ-function₂[V] p) → ℒₛₑₜ-function₂[V] (tagSel₂ i ps)
  | i, [], _ => by
    have h0 : (tagSel₂ i ([] : List (V → V → V)) : V → V → V) = fun _ _ ↦ (∅ : V) := rfl
    rw [h0]; definability
  | i, p :: ps, h => by
    have hp := h p (.head _)
    have hrest := tagSel₂_definable (i + 1) ps fun r hr ↦ h r (.tail _ hr)
    have htp := tagPayload_definable (V := V) i
    have h0 : (tagSel₂ i (p :: ps) : V → V → V)
        = fun a b ↦ if b = (⟨((i : ℕ) : V), tagPayload i b⟩ₖ : V)
            then p a (tagPayload i b) else tagSel₂ (i + 1) ps a b := rfl
    rw [h0]
    exact ite_rel_definable₂ (P := fun _ b ↦ b = (⟨((i : ℕ) : V), tagPayload i b⟩ₖ : V))
      (eq_kpair_definable htp _) (definable₂_comp₂ hp htp) hrest

theorem tagSel₂_at : ∀ (i : ℕ) (ps : List (V → V → V)) (k : ℕ) (p : V → V → V),
    ps[k]? = some p → ∀ a x : V,
      tagSel₂ i ps a (⟨(((i + k : ℕ)) : V), x⟩ₖ) = p a x
  | i, r :: ps, 0, p, h, a, x => by
    have hrp : r = p := by simpa using h
    subst hrp
    simp only [Nat.add_zero]
    show (if _ = _ then _ else _) = _
    rw [if_pos (by rw [tagPayload_kpair]), tagPayload_kpair]
  | i, r :: ps, k + 1, p, h, a, x => by
    show (if _ = _ then _ else _) = _
    rw [if_neg ?_]
    · have ih := tagSel₂_at (i + 1) ps k p (by simpa using h) a x
      have e : i + 1 + k = i + (k + 1) := by omega
      rw [e] at ih
      exact ih
    · exact fun hc ↦ ofNat_ne_ofNat (by omega : i + (k + 1) ≠ i) (kpair_inj hc).1

/-! ## Syntactic telescopes and argument tuples

The bridge from `VExpr` telescopes to `teleFun`'s `List (DefFun V)`.  Note the
two are *not* interchangeable: `Fld` deliberately does not use `teleDomains`,
because a recursive field's stored type mentions the block. -/

section Syntax

variable {envF : VEnv} {nv : ℕ} (M : ModelData V) (L : LevelAssign envF nv)

/-- The domain list of a syntactic telescope `Δ` (declaration order) over the
context `Γ`: entry `i` is `⟦Δ[i]⟧` in the context extended by the previous
entries, which is exactly where `Δ[i]` is stated. -/
noncomputable def teleDomains : List VExpr → List VExpr → List (DefFun V)
  | _, [] => []
  | Γ, A :: Δ => interp M L Γ A :: teleDomains (A :: Γ) Δ

@[simp] theorem teleDomains_length : ∀ (Γ Δ : List VExpr),
    (teleDomains M L Γ Δ).length = Δ.length
  | _, [] => rfl
  | Γ, A :: Δ => by
    show (teleDomains M L (A :: Γ) Δ).length + 1 = Δ.length + 1
    rw [teleDomains_length]

/-- **Evaluate a list of terms and append the results to a base valuation.**
This is what `resIdx` and `posIdx` are: an index *tuple*, built by extending the
parameter valuation with the interpretations of the stored argument terms. -/
noncomputable def argsVal (Γ : List VExpr) : List VExpr → V → V → V
  | [], _, ρ₀ => ρ₀
  | e :: es, σ, ρ₀ => argsVal Γ es σ (snoc ρ₀ ((interp M L Γ e).toFun σ))

theorem argsVal_definable : ∀ (Γ : List VExpr) (es : List VExpr),
    ℒₛₑₜ-function₂[V] (fun σ ρ₀ ↦ argsVal M L Γ es σ ρ₀)
  | Γ, [] => by
    have h0 : (fun (σ ρ₀ : V) ↦ argsVal M L Γ ([] : List VExpr) σ ρ₀) = fun _ ρ₀ ↦ ρ₀ := rfl
    rw [h0]; definability
  | Γ, e :: es => by
    have hrest := argsVal_definable Γ es
    have hE := (interp M L Γ e).definable
    have h0 : (fun (σ ρ₀ : V) ↦ argsVal M L Γ (e :: es) σ ρ₀)
        = fun σ ρ₀ ↦ argsVal M L Γ es σ (snoc ρ₀ ((interp M L Γ e).toFun σ)) := rfl
    rw [h0]
    definability

end Syntax

/-! ## The builder

`interpSig` factors into two halves that fail for completely different reasons,
so they are kept apart:

* **the assembly** — turn per-constructor data into an `IndSignature`,
  discharging its four bundled definability obligations.  That is this section,
  and it is where all the `tagCase`/`tagUnionF`/`tagSel₂` machinery is spent;
* **the syntactic computation** — read the per-constructor data off a
  `VInductDecl'`.  That is de Bruijn bookkeeping against `Decl.lean`, and it is
  where `NoBlock.indep` is needed.

Splitting them means the assembly is checkable now, and the remaining work is
purely "compute a `CtorData` from a `VIndCtor`". -/

/-- Per-constructor data, in the form the builder consumes.

`flds` is deliberately a `List (DefFun V)` and not a telescope of `VExpr`s: a
recursive field's stored type mentions the block, so the caller supplies `⟦A⟧`
for the block-free `A` at a non-recursive field and a singleton at a recursive
one.  That keeps the block-freeness question out of the assembly entirely. -/
structure CtorData (V : Type*) [SetStructure V] where
  /-- One definable domain per field, in declaration position. -/
  flds : List (DefFun V)
  /-- One recursive-position domain per recursive field, as a function of the
  field valuation. -/
  poss : List (V → V)
  poss_definable : ∀ p ∈ poss, ℒₛₑₜ-function₁[V] p
  /-- The index at which each recursive position recurses, as a function of the
  field valuation and the position's payload. -/
  posIdxs : List (V → V → V)
  posIdxs_definable : ∀ p ∈ posIdxs, ℒₛₑₜ-function₂[V] p
  /-- The result index, as a function of the field valuation. -/
  resIdx : V → V
  resIdx_definable : ℒₛₑₜ-function₁[V] resIdx

/-- **The assembly.**  Tags are `0, …, cs.length - 1`; every component
dispatches on the tag, and all four definability obligations are discharged. -/
noncomputable def mkIndSignature (Idx params : V) (cs : List (CtorData V)) :
    IndSignature V where
  Idx := Idx
  Q := ((cs.length : ℕ) : V)
  Fld := tagCase₁ 0 (cs.map fun c ↦ fun _ ↦ (teleFun c.flds).toFun params)
  Pos := tagCase₂ 0 (cs.map fun c ↦ fun _ a ↦ tagUnionF 0 c.poss a)
  posIdx := tagCase₃ 0 (cs.map fun c ↦ fun _ a b ↦ tagSel₂ 0 c.posIdxs a b)
  resIdx := tagCase₂ 0 (cs.map fun c ↦ fun _ a ↦ c.resIdx a)
  Fld_definable := by
    refine tagCase₁_definable _ _ fun f hf ↦ ?_
    obtain ⟨c, -, rfl⟩ := List.mem_map.1 hf
    definability
  Pos_definable := by
    refine tagCase₂_definable _ _ fun f hf ↦ ?_
    obtain ⟨c, -, rfl⟩ := List.mem_map.1 hf
    exact definable₂_const₁ (tagUnionF_definable 0 c.poss c.poss_definable)
  posIdx_definable := by
    refine tagCase₃_definable _ _ fun f hf ↦ ?_
    obtain ⟨c, -, rfl⟩ := List.mem_map.1 hf
    have := tagSel₂_definable 0 c.posIdxs c.posIdxs_definable
    definability
  resIdx_definable := by
    refine tagCase₂_definable _ _ fun f hf ↦ ?_
    obtain ⟨c, -, rfl⟩ := List.mem_map.1 hf
    exact definable₂_const₁ c.resIdx_definable

/-! ### Reading the assembled signature back

The tag dispatch really does select the intended constructor's data.  These are
what `interpSig_stage` and `interpSig_wf` will be proved from, and they are
unconditional — the `Above` wrapper appears only once the *syntactic* side is
involved. -/

theorem mkIndSignature_Q (Idx params : V) (cs : List (CtorData V)) :
    (mkIndSignature Idx params cs).Q = ((cs.length : ℕ) : V) := rfl

theorem mkIndSignature_Idx (Idx params : V) (cs : List (CtorData V)) :
    (mkIndSignature Idx params cs).Idx = Idx := rfl

theorem mkIndSignature_Fld (Idx params : V) (cs : List (CtorData V))
    {k : ℕ} {c : CtorData V} (h : cs[k]? = some c) :
    (mkIndSignature Idx params cs).Fld ((k : ℕ) : V) = (teleFun c.flds).toFun params := by
  show tagCase₁ 0 (cs.map fun c ↦ fun _ : V ↦ (teleFun c.flds).toFun params)
    ((k : ℕ) : V) = _
  have hat := tagCase₁_at (V := V) 0
    (cs.map fun c ↦ fun _ : V ↦ (teleFun c.flds).toFun params) k
    (fun _ ↦ (teleFun c.flds).toFun params) (by rw [List.getElem?_map, h]; rfl)
  simpa using hat

end Lean4Lean.SetModel
