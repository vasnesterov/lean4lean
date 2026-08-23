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

## Two things to know before adding to this file

**`DefFun`-valued recursion is forced, not stylistic.** `mkFamUnion` takes the
fibre map's definability *as an argument*, so each step of a list-indexed
recursion needs the previous step's definability **at definition time**. A bare
`V → V` recursion cannot be written at all — not "is harder to prove about",
*cannot be written*. This is why `interp` is `DefFun`-valued and why `teleFun`
is, and it will recur in every list-indexed set construction the inductive layer
needs. Reach for `DefFun` first rather than discovering it after a rewrite.

**When `definability` diverges, generalise what it is chasing — the limit is
never the answer.** `tagSel₂_definable` failed with `maximum recursion depth`,
and raising `maxRecDepth` did *not* help. That is `SetModel/Definability.lean`'s
documented **first** failure mode: genuine divergence from unfolding, not
insufficient depth. Here `tagPayload` unfolds to `value` of a singleton and the
search chases the unfolding. The fix is to abstract the offending sub-term into
a hypothesis so the search cannot unfold it — `eq_kpair_definable` is stated
with `t` a *variable* and applied at `tagPayload i`. That is cheaper than any
limit, and the diagnostic is: if raising the limit does not help, the search is
not deep, it is looping.
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

variable {envF : VEnv} {nv : ℕ} (M : ModelData V) (L : PropSplit envF nv)

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

/-! ## `NoBlock.indep`, measured

`docs/model-interface.md` §2 names `NoBlock.indep` as the second obligation
making `interpSig` well defined:

> If `A` is block-free and well-typed in a context containing recursive-field
> variables, then `⟦A⟧` does not depend on the values at those positions.

It splits, and the two halves are of completely different difficulty:

1. **model half** — *if `A` never reads those positions, `⟦A⟧` ignores them.*
   That is `interp_avoids` below. Proved here, unconditionally.
2. **syntactic half** — *a block-free, well-typed field type never reads a
   recursive-field position.* Open, and see the measurement below.

`VExpr.NoConsts` is about constants only (`.bvar _ => True`), so block-freeness
says *nothing* about bound variables on its own; half 2 is where all the content
is.

### The measurement of half 2

It is **true**, and the argument is uniform: suppose block-free well-typed
`A : Sort ℓ` reads a recursive-field variable `r : I p π`. Every way `r` can
occur forces something the environment cannot supply.

* `r` in argument position, `.app f r`: then `f : ∀ _ : I p π, B`, and `f` is a
  block-free subterm of `A`. `f` cannot be a parameter (parameters are typed
  before the block exists), nor an earlier field (its `pos` would have to give
  either a block-free type up to defeq, or the recursive shape
  `∀ ξ, I_j p π` whose `ξ` must be block-free — neither holds), nor an earlier
  constant (typed before the block), nor a `lam` (its binder type mentions the
  block). What is left is a nested application, and the same argument recurses
  on its head.
* `r` as a binder type, `.lam r _` or `.forallE r _`: needs `I p π` to be a
  sort.
* `r` in head position, `.app r x`: needs `I p π` to be a Π.

The last two, and the base of the first, are all **disjointness of a constant
application from the other head forms** — in this repository:

| what half 2 needs | status |
|---|---|
| `IsDefEqU.const_forallE_inv` — a constant application is not a Π | **stated, `sorry`** (`Theory/Typing/Injectivity.lean`) |
| "a constant application is not a sort" | **not stated anywhere** |

So `NoBlock.indep` is not an isolated obligation: it is **another consumer of
`Injectivity.lean`'s disjointness family**, the same family that has resisted
elsewhere, plus one statement nobody has written down. That is the measurement,
and it argues for `model-interface.md` §2's own escape hatch — a monotone
`Fld : V → V → V` over the family's current approximation, which needs no
disjointness at all and costs a redo of the recursor's rank argument. That
trade is now priced on both sides; the decision is not mine to take. -/

/-- `e`, read in a context of length `n`, never reads a position satisfying `S`.

Stated on *positions* rather than de Bruijn indices because that is what
`interp` reads: `.bvar i` in a context of length `n` reads position
`n - 1 - i`. -/
def AvoidsAt (S : ℕ → Prop) : ℕ → VExpr → Prop
  | n, .bvar i => ¬ S (n - 1 - i)
  | _, .sort _ => True
  | _, .const _ _ => True
  | n, .app f a => AvoidsAt S n f ∧ AvoidsAt S n a
  | n, .lam A b => AvoidsAt S n A ∧ AvoidsAt S (n + 1) b
  | n, .forallE A b => AvoidsAt S n A ∧ AvoidsAt S (n + 1) b

theorem value_of_not_mem_domain {f x : V} (h : x ∉ domain f) : f ‘ x = ∅ := by
  ext z
  simp only [value, mem_sep_iff]
  constructor
  · rintro ⟨-, y, -, hy⟩; exact absurd (mem_domain_of_kpair_mem hy) h
  · intro hz; exact absurd hz (by simp)

section Locality

variable {envF : VEnv} {nv : ℕ} {M : ModelData V} {L : PropSplit envF nv}

theorem mkFamUnion_congr_arg {G : V → V} {hG : ℒₛₑₜ-function₁[V] G} {F : V → V → V}
    {hF : ℒₛₑₜ-function₂[V] F} {ρ ρ' : V} (hGe : G ρ = G ρ')
    (hFe : ∀ v ∈ G ρ, F ρ v = F ρ' v) :
    mkFamUnion G hG F hF ρ = mkFamUnion G hG F hF ρ' := by
  ext y
  rw [mem_mkFamUnion_iff, mem_mkFamUnion_iff]
  exact ⟨fun ⟨v, hv, hy⟩ ↦ ⟨v, hGe ▸ hv, (hFe v hv) ▸ hy⟩,
    fun ⟨v, hv, hy⟩ ↦ ⟨v, hGe ▸ hv, (hFe v (hGe ▸ hv)).symm ▸ hy⟩⟩

theorem mkLam_congr_arg {G : V → V} {hG : ℒₛₑₜ-function₁[V] G} {F : V → V → V}
    {hF : ℒₛₑₜ-function₂[V] F} {ρ ρ' : V} (hGe : G ρ = G ρ')
    (hFe : ∀ v ∈ G ρ, F ρ v = F ρ' v) :
    mkLam G hG F hF ρ = mkLam G hG F hF ρ' := by
  ext y
  rw [mem_mkLam_iff, mem_mkLam_iff]
  exact ⟨fun ⟨v, hv, hy⟩ ↦ ⟨v, hGe ▸ hv, by rw [hy, hFe v hv]⟩,
    fun ⟨v, hv, hy⟩ ↦ ⟨v, hGe ▸ hv, by rw [hy, hFe v (hGe ▸ hv)]⟩⟩

theorem mkForallProp_congr_arg {G : V → V} {hG : ℒₛₑₜ-function₁[V] G} {F : V → V → V}
    {hF : ℒₛₑₜ-function₂[V] F} {ρ ρ' : V} (hGe : G ρ = G ρ')
    (hFe : ∀ v ∈ G ρ, F ρ v = F ρ' v) :
    mkForallProp G hG F hF ρ = mkForallProp G hG F hF ρ' := by
  ext y
  rw [mem_mkForallProp_iff, mem_mkForallProp_iff, ← hGe]
  refine and_congr_right fun _ ↦ ⟨fun hh v hv ↦ ?_, fun hh v hv ↦ ?_⟩
  · rw [← hFe v hv]; exact hh v hv
  · rw [hFe v hv]; exact hh v hv

theorem mkForallType_congr_arg {G : V → V} {hG : ℒₛₑₜ-function₁[V] G} {F : V → V → V}
    {hF : ℒₛₑₜ-function₂[V] F} {ρ ρ' : V} (hGe : G ρ = G ρ')
    (hFe : ∀ v ∈ G ρ, F ρ v = F ρ' v) :
    mkForallType G hG F hF ρ = mkForallType G hG F hF ρ' := by
  have hU : mkFamUnion G hG F hF ρ = mkFamUnion G hG F hF ρ' :=
    mkFamUnion_congr_arg hGe hFe
  ext y
  rw [mem_mkForallType_iff, mem_mkForallType_iff, hU, ← hGe]
  refine and_congr_right fun _ ↦ ⟨fun hh v hv z hz ↦ ?_, fun hh v hv z hz ↦ ?_⟩
  · rw [← hFe v hv]; exact hh v hv z hz
  · rw [hFe v hv]; exact hh v hv z hz

/-- **The model half of `NoBlock.indep`.**  `interp` reads a valuation only at
the positions the term does not avoid, so two valuations agreeing off `S` give
the same denotation to any term avoiding `S`. -/
theorem interp_avoids {S : ℕ → Prop} : ∀ (e : VExpr) {Γ : List VExpr} {ρ ρ' : V},
    AvoidsAt S Γ.length e → IsSeq ρ Γ.length → IsSeq ρ' Γ.length →
    (∀ j < Γ.length, ¬ S j → ρ ‘ ((j : ℕ) : V) = ρ' ‘ ((j : ℕ) : V)) →
    (interp M L Γ e).toFun ρ = (interp M L Γ e).toFun ρ'
  | .bvar i, Γ, ρ, ρ', he, hρ, hρ', h => by
    rw [interp_bvar, interp_bvar]
    rcases Nat.eq_zero_or_pos Γ.length with h0 | h0
    · rw [value_of_not_mem_domain (f := ρ) (by rw [hρ.2, h0]; simp [zero_def]),
        value_of_not_mem_domain (f := ρ') (by rw [hρ'.2, h0]; simp [zero_def])]
    · exact h _ (by omega) he
  | .sort _, _, _, _, _, _, _, _ => by rw [interp_sort, interp_sort]
  | .const _ _, _, _, _, _, _, _, _ => by rw [interp_const, interp_const]
  | .app f a, Γ, ρ, ρ', he, hρ, hρ', h => by
    by_cases hp : L.IsProof M Γ f
    · rw [interp_app_proof M L hp, interp_app_proof M L hp]
    · rw [interp_app_type M L hp, interp_app_type M L hp,
        interp_avoids f he.1 hρ hρ' h, interp_avoids a he.2 hρ hρ' h]
  | .lam A b, Γ, ρ, ρ', he, hρ, hρ', h => by
    have hstep : ∀ v : V, ∀ j < Γ.length + 1, ¬ S j →
        (snoc ρ v) ‘ ((j : ℕ) : V) = (snoc ρ' v) ‘ ((j : ℕ) : V) := by
      intro v j hj hS
      rcases Nat.lt_or_ge j Γ.length with hlt | hge
      · rw [hρ.read_lt hlt, hρ'.read_lt hlt]; exact h j hlt hS
      · have : j = Γ.length := by omega
        subst this
        rw [hρ.read_top, hρ'.read_top]
    have hGe := interp_avoids A he.1 hρ hρ' h
    have hFe : ∀ v : V, (interp M L (A :: Γ) b).toFun (snoc ρ v)
        = (interp M L (A :: Γ) b).toFun (snoc ρ' v) := fun v ↦
      interp_avoids b (Γ := A :: Γ) he.2 hρ.snoc' hρ'.snoc' (hstep v)
    by_cases hp : L.IsProof M (A :: Γ) b
    · rw [interp_lam_proof M L hp, interp_lam_proof M L hp]
    · rw [interp_lam_type M L hp, interp_lam_type M L hp]
      exact mkLam_congr_arg hGe fun v _ ↦ hFe v
  | .forallE A b, Γ, ρ, ρ', he, hρ, hρ', h => by
    have hstep : ∀ v : V, ∀ j < Γ.length + 1, ¬ S j →
        (snoc ρ v) ‘ ((j : ℕ) : V) = (snoc ρ' v) ‘ ((j : ℕ) : V) := by
      intro v j hj hS
      rcases Nat.lt_or_ge j Γ.length with hlt | hge
      · rw [hρ.read_lt hlt, hρ'.read_lt hlt]; exact h j hlt hS
      · have : j = Γ.length := by omega
        subst this
        rw [hρ.read_top, hρ'.read_top]
    have hGe := interp_avoids A he.1 hρ hρ' h
    have hFe : ∀ v : V, (interp M L (A :: Γ) b).toFun (snoc ρ v)
        = (interp M L (A :: Γ) b).toFun (snoc ρ' v) := fun v ↦
      interp_avoids b (Γ := A :: Γ) he.2 hρ.snoc' hρ'.snoc' (hstep v)
    by_cases hp : L.IsProp M (A :: Γ) b
    · rw [interp_forallE_prop M L hp, interp_forallE_prop M L hp]
      exact mkForallProp_congr_arg hGe fun v _ ↦ hFe v
    · rw [interp_forallE_type M L hp, interp_forallE_type M L hp]
      exact mkForallType_congr_arg hGe fun v _ ↦ hFe v

end Locality

/-! ### The bridge from `VIndRecArg.BindersIndep` to `AvoidsAt`

`Theory/Inductive/Decl.lean` now records `VIndField.WF.binders_indep`: a
recursive field's binder telescope `ξ` is independent of the *earlier recursive*
fields, stated as `VExpr.Skips 1 (k + t)` per binder.  These two lemmas are the
point where the translation will consume it, and they are here so the clause is
checked against this file's convention rather than against its own docstring.

**The two conventions differ, and the difference is not cosmetic.**  `Skips`
counts de Bruijn indices *relative* to the binder depth (innermost is 0);
`AvoidsAt` names *absolute* positions counted from the outside, because that is
what `interp_avoids` needs — an environment `ρ` is read at absolute index `j`.
Converting one to the other is `j = n - 1 - i`, and with truncated subtraction
that map is only injective on well-scoped terms.  Hence the `ClosedN`
hypothesis in `avoidsAt_of_skips`: without it, a `bvar` out of range collapses
to absolute position `0` and would falsely appear to *read* the outermost slot.
The hypothesis is free at the use site — the field types in question are
well-typed in `r.binders.reverse ++ Γ`, hence closed at that length.

`BindersIndep` gives one `Skips` per earlier recursive field, i.e. a family of
*singleton* avoid-sets, while `interp_avoids` wants one predicate covering all
of them at once.  `avoidsAt_of_forall` performs that union; it is the reason the
clause's per-field shape costs nothing here. -/

/-- `AvoidsAt` in a predicate that is covered by a family of predicates each of
which the term avoids.  Used to turn `BindersIndep`'s per-field `Skips` clauses
into a single avoid-set over all recursive-field positions. -/
theorem avoidsAt_of_forall {T : ℕ → Prop} {P : ℕ → ℕ → Prop}
    (hT : ∀ j, T j → ∃ m, P m j) :
    ∀ (e : VExpr) {n : ℕ}, (∀ m, AvoidsAt (P m) n e) → AvoidsAt T n e
  | .bvar i, _, h => fun hj ↦ let ⟨m, hm⟩ := hT _ hj; h m hm
  | .sort _, _, _ => trivial
  | .const _ _, _, _ => trivial
  | .app f a, _, h =>
    ⟨avoidsAt_of_forall hT f fun m ↦ (h m).1, avoidsAt_of_forall hT a fun m ↦ (h m).2⟩
  | .lam A b, _, h =>
    ⟨avoidsAt_of_forall hT A fun m ↦ (h m).1, avoidsAt_of_forall hT b fun m ↦ (h m).2⟩
  | .forallE A b, _, h =>
    ⟨avoidsAt_of_forall hT A fun m ↦ (h m).1, avoidsAt_of_forall hT b fun m ↦ (h m).2⟩

/-- **`Skips` at relative index `k + d` is `AvoidsAt` at absolute position
`n - 1 - k`.**  `n` is the length of the context the term is scoped in before
the extra `d` binders; `k` is the de Bruijn index, within that context, of the
slot being avoided.  `ClosedN` is what makes the index conversion injective —
see the section comment. -/
theorem avoidsAt_of_skips {n : ℕ} : ∀ (e : VExpr) {d k : ℕ},
    e.ClosedN (n + d) → k < n → e.Skips' 1 (k + d) →
    AvoidsAt (fun j ↦ j = n - 1 - k) (n + d) e
  | .bvar i, d, k, hc, hk, hs => by
    show ¬ (n + d - 1 - i = n - 1 - k)
    simp only [VExpr.ClosedN] at hc
    simp only [VExpr.Skips'] at hs
    omega
  | .sort _, _, _, _, _, _ => trivial
  | .const _ _, _, _, _, _, _ => trivial
  | .app f a, d, k, hc, hk, hs =>
    ⟨avoidsAt_of_skips f hc.1 hk hs.1, avoidsAt_of_skips a hc.2 hk hs.2⟩
  | .lam A b, d, k, hc, hk, hs =>
    ⟨avoidsAt_of_skips A hc.1 hk hs.1,
      (Nat.add_assoc n d 1) ▸ avoidsAt_of_skips (d := d + 1) b
        ((Nat.add_assoc n d 1) ▸ hc.2) hk ((Nat.add_assoc k d 1) ▸ hs.2)⟩
  | .forallE A b, d, k, hc, hk, hs =>
    ⟨avoidsAt_of_skips A hc.1 hk hs.1,
      (Nat.add_assoc n d 1) ▸ avoidsAt_of_skips (d := d + 1) b
        ((Nat.add_assoc n d 1) ▸ hc.2) hk ((Nat.add_assoc k d 1) ▸ hs.2)⟩

/-- The depth-0 corollary: a term that `Skips` a variable has an interpretation
independent of what sits in that slot.

**Use `avoidsAt_of_skips` directly for the binders themselves.**  Binder `k` of
`ξ` is scoped in `(r.binders.take k).reverse ++ Γ`, i.e. at depth `d = k` over
`Γ` — which is exactly why `BindersIndep` writes `Skips 1 (k + t)` rather than
`Skips 1 t`, and why `avoidsAt_of_skips` carries `d`.  Checked against the
clause's own bookkeeping: with `i' + 1 + t = i`, field `i'` sits at de Bruijn
index `t` in `Γ`, i.e. absolute position `|Γ| - 1 - t = D.np + i'` — the
recursive field's slot, as required. -/
theorem interp_indep_of_skips {envF : VEnv} {nv : ℕ} {M : ModelData V}
    {L : PropSplit envF nv} {Γ : List VExpr} {e : VExpr} {k : ℕ} {ρ ρ' : V}
    (hc : e.ClosedN Γ.length) (hk : k < Γ.length)
    (hs : e.Skips 1 k) (hρ : IsSeq ρ Γ.length) (hρ' : IsSeq ρ' Γ.length)
    (h : ∀ j < Γ.length, j ≠ Γ.length - 1 - k → ρ ‘ ((j : ℕ) : V) = ρ' ‘ ((j : ℕ) : V)) :
    (interp M L Γ e).toFun ρ = (interp M L Γ e).toFun ρ' :=
  interp_avoids e
    (avoidsAt_of_skips (n := Γ.length) (d := 0) e hc hk (VExpr.skips_iff.1 hs))
    hρ hρ' h

/-! ## The escape hatch: an approximation-indexed signature

**Ruled in.**  `docs/model-interface.md` §2 offers this as the alternative to
`NoBlock.indep`, and it is the one taken: *generalise the model side rather
than the syntax side.*  `Fld` takes the family's current approximation, so a
non-recursive field's domain may legitimately mention family elements and **no
independence argument is needed at all** — the disjointness family
`NoBlock.indep` bottoms out in is simply never consulted.

The deciding factor was decoupling rather than cost: this lets the model side
progress independently of an obligation that already has three consumers.

### Why this is additive rather than a rewrite

The generalisation is conservative in *both* directions:

* every `IndSignature` is an `IndSignature₂` whose `Fld` ignores the
  approximation (`IndSignature.toTwo`) — nothing already proved is lost;
* every `IndSignature₂` specialises at a fixed approximation to an ordinary
  `IndSignature` (`IndSignature₂.at`) — so `Inductive.lean`, `IndStage.lean`
  and `IndCard.lean` apply **stage-wise, unchanged**.

The bridge is definitional: one step of the generalised operator at `W` *is* one
step of the ordinary operator for the signature specialised at `W`. Every
pointwise fact about `indStep` therefore transfers for free, and the only
genuinely new obligation is monotonicity — which is exactly the one field the
structure adds, and the only place it is spent. -/

/-- A signature whose field data may depend on the family's current
approximation. -/
structure IndSignature₂ (V : Type*) [SetStructure V] where
  Idx : V
  Q : V
  /-- `Fld W q`: the non-recursive field data of `q`, **relative to the current
  approximation `W`**.  This is the whole change. -/
  Fld : V → V → V
  Pos : V → V → V
  posIdx : V → V → V → V
  resIdx : V → V → V
  Fld_definable : ℒₛₑₜ-function₂[V] Fld
  Pos_definable : ℒₛₑₜ-function₂[V] Pos
  posIdx_definable : ℒₛₑₜ-function₃[V] posIdx
  resIdx_definable : ℒₛₑₜ-function₂[V] resIdx
  /-- **The new obligation, and the only one.**  Without it the operator is not
  monotone and the least fixed point does not exist. -/
  Fld_mono : ∀ {W₁ W₂ : V}, W₁ ⊆ W₂ → ∀ q : V, Fld W₁ q ⊆ Fld W₂ q

attribute [instance] IndSignature₂.Fld_definable IndSignature₂.Pos_definable
  IndSignature₂.posIdx_definable IndSignature₂.resIdx_definable

/-- Specialise at a fixed approximation.  This is what lets every existing
result about `IndSignature` be used stage-wise. -/
noncomputable def IndSignature₂.at (S : IndSignature₂ V) (W : V) : IndSignature V where
  Idx := S.Idx
  Q := S.Q
  Fld := S.Fld W
  Pos := S.Pos
  posIdx := S.posIdx
  resIdx := S.resIdx
  Fld_definable := by have := S.Fld_definable; definability
  Pos_definable := S.Pos_definable
  posIdx_definable := S.posIdx_definable
  resIdx_definable := S.resIdx_definable

/-- An ordinary signature is one whose field data ignores the approximation, so
the generalisation loses nothing. -/
noncomputable def IndSignature.toTwo (S : IndSignature V) : IndSignature₂ V where
  Idx := S.Idx
  Q := S.Q
  Fld := fun _ q ↦ S.Fld q
  Pos := S.Pos
  posIdx := S.posIdx
  resIdx := S.resIdx
  Fld_definable := by have := S.Fld_definable; definability
  Pos_definable := S.Pos_definable
  posIdx_definable := S.posIdx_definable
  resIdx_definable := S.resIdx_definable
  Fld_mono := fun _ _ _ hz ↦ hz

/-- The round trip is the identity, on the nose. -/
theorem IndSignature.at_toTwo (S : IndSignature V) (W : V) : S.toTwo.at W = S := rfl

section Operator₂

variable {S : IndSignature₂ V} {D : V}

/-- One step of the generalised operator.  **Definitionally** one step of the
ordinary operator at the signature specialised to the current approximation. -/
noncomputable def indStep₂ (S : IndSignature₂ V) (D W : V) : V := indStep (S.at W) D W

theorem indStep₂_eq (S : IndSignature₂ V) (D W : V) :
    indStep₂ S D W = indStep (S.at W) D W := rfl

theorem mem_indStep₂_iff {W p : V} :
    p ∈ indStep₂ S D W ↔ p ∈ S.Idx ×ˢ D ∧
      ∃ q ∈ S.Q, ∃ a ∈ S.Fld W q, ∃ f ∈ (D ^ S.Pos q a : V),
        (∀ b ∈ S.Pos q a, (⟨S.posIdx q a b, f ‘ b⟩ₖ : V) ∈ W) ∧
        p = ⟨S.resIdx q a, ⟨q, ⟨a, f⟩ₖ⟩ₖ⟩ₖ := mem_indStep_iff' (S.at W) D

theorem indStep₂_definable (S : IndSignature₂ V) (D : V) :
    ℒₛₑₜ-function₁[V] (indStep₂ S D) := by
  suffices ℒₛₑₜ-relation[V] (fun T W ↦ T = indStep₂ S D W) by exact this
  have hF := S.Fld_definable
  have hP := S.Pos_definable
  have hI := S.posIdx_definable
  have hR := S.resIdx_definable
  have e : ∀ T W : V, T = indStep₂ S D W ↔ ∀ p, p ∈ T ↔ p ∈ S.Idx ×ˢ D ∧
      ∃ q ∈ S.Q, ∃ a ∈ S.Fld W q, ∃ f ∈ (D ^ S.Pos q a : V),
        (∀ b ∈ S.Pos q a, (⟨S.posIdx q a b, f ‘ b⟩ₖ : V) ∈ W) ∧
        p = ⟨S.resIdx q a, ⟨q, ⟨a, f⟩ₖ⟩ₖ⟩ₖ := by
    intro T W
    rw [mem_ext_iff]
    simp only [mem_indStep₂_iff]
  simp only [e]
  definability

/-- **The one new obligation, spent.**  `Fld_mono` is used exactly once, to move
the field datum along the approximation; every other clause is monotone for the
same reason it was before. -/
theorem indStep₂_isMonotoneOn (S : IndSignature₂ V) (D : V) :
    IsMonotoneOn (S.Idx ×ˢ D) (indStep₂ S D) where
  mono W₁ W₂ h p hp := by
    rw [mem_indStep₂_iff] at hp ⊢
    obtain ⟨hb, q, hq, a, ha, f, hf, hrec, he⟩ := hp
    exact ⟨hb, q, hq, a, S.Fld_mono h q _ ha, f, hf, fun b hbp ↦ h _ (hrec b hbp), he⟩
  maps := (indStep_isMonotoneOn (S.at (S.Idx ×ˢ D)) D).maps

/-- **The inductive family, over an approximation-indexed signature.**
Formation is unchanged: `lfp` needs only monotonicity and definability. -/
noncomputable def Ind₂ (S : IndSignature₂ V) (D : V) : V :=
  lfp (S.Idx ×ˢ D) (indStep₂ S D) (indStep₂_definable S D)

theorem Ind₂_subset : Ind₂ S D ⊆ S.Idx ×ˢ D := lfp_subset (indStep₂_isMonotoneOn S D)

theorem indStep₂_Ind₂ : indStep₂ S D (Ind₂ S D) = Ind₂ S D :=
  apply_lfp (indStep₂_isMonotoneOn S D)

/-- **The generalisation is conservative on the fixed point too.**  For a
signature that ignores the approximation, the generalised family is the old
one — so nothing built on `Ind` is invalidated. -/
theorem Ind₂_toTwo (S : IndSignature V) (D : V) : Ind₂ S.toTwo D = Ind S D := rfl

/-- Enlarging the approximation only enlarges the step — the signature enters
`indStep` in exactly one place. -/
theorem indStep_at_mono (S : IndSignature₂ V) (D : V) {W₁ W₂ : V} (h : W₁ ⊆ W₂) (X : V) :
    indStep (S.at W₁) D X ⊆ indStep (S.at W₂) D X := by
  intro p hp
  rw [mem_indStep_iff'] at hp ⊢
  obtain ⟨hb, q, hq, a, ha, f, hf, hrec, he⟩ := hp
  exact ⟨hb, q, hq, a, S.Fld_mono h q _ ha, f, hf, hrec, he⟩

theorem Ind_at_subset (S : IndSignature₂ V) (D : V) :
    (Ind (S.at (Ind₂ S D)) D : V) ⊆ (Ind₂ S D : V) := by
  refine lfp_subset_of_prefixed (indStep_isMonotoneOn _ D)
    (Ind₂_subset (S := S) (D := D)) (fun p hp ↦ ?_)
  have h : p ∈ indStep₂ S D (Ind₂ S D) := hp
  rwa [indStep₂_Ind₂ (S := S) (D := D)] at h

set_option maxHeartbeats 1000000 in
/-- **The generalised family is the ordinary family of the signature specialised
at itself.**

This is what makes the escape hatch nearly free.  `Ind₂` is *not* by definition
an instance of `Ind` — its operator's signature moves with the approximation —
but at the fixed point the two coincide, so **every existing theorem about
`Ind` applies to `Ind₂` verbatim**, at `S.at (Ind₂ S D)`: the constructors, no
confusion, the induction principle, the recursor, and the ι-rule.

Both inclusions are leastness arguments, and `Fld_mono` is spent once in each. -/
theorem Ind₂_eq_Ind_at (S : IndSignature₂ V) (D : V) :
    Ind₂ S D = Ind (S.at (Ind₂ S D)) D := by
  refine subset_antisymm ?_ (Ind_at_subset S D)
  refine lfp_subset_of_prefixed (indStep₂_isMonotoneOn S D)
    (Ind_subset (S.at (Ind₂ S D)) D) (fun z hz ↦ ?_)
  have hz' := indStep_at_mono S D (Ind_at_subset S D)
    (Ind (S.at (Ind₂ S D)) D) z hz
  rwa [indStep_Ind (S.at (Ind₂ S D)) D] at hz'

/-! ### The recursor transfers, and the rank argument needs no redoing

`model-interface.md` §2 priced this escape hatch as "what needs redoing is the
rank argument for the recursor, since the non-recursive data `a` would then
itself contain family elements".

**That cost is not incurred.**  The inequality driving the recursion is
`rank_lt_indCtorVal : (⟨b, y⟩ₖ : V) ∈ f → rank y < rank (⟨q, ⟨a, f⟩ₖ⟩ₖ : V)`
(`SetModel/Inductive.lean`), and its proof is
`rank y < rank f < rank ⟨a, f⟩ₖ < rank ⟨q, ⟨a, f⟩ₖ⟩ₖ` — it descends through the
*recursive-position function* `f` and **never inspects `a` at all**.  Whether
`a` contains family elements is irrelevant to it.

Combined with `Ind₂_eq_Ind_at`, the recursor and its ι-rule transfer by
rewriting, as below.  The real adaptation cost of the escape hatch is
`IsStageSignature`, whose `fld_mem` must now be asked of `Fld W q` — bounded,
mechanical, and not a rank argument. -/

theorem indRec₂_mem {S : IndSignature₂ V} {D R : V} {e : V → V → V → V → V}
    {he : ℒₛₑₜ-function₄[V] e}
    (hS : (S.at (Ind₂ S D)).WF) (hD : IsIndCarrier (S.at (Ind₂ S D)) D)
    (hE : IsMinorPremise (S.at (Ind₂ S D)) D R e)
    {p : V} (hp : p ∈ Ind₂ S D) :
    indRec (S.at (Ind₂ S D)) D R e he p ∈ R := by
  rw [Ind₂_eq_Ind_at] at hp
  exact indRec_mem hS hD hE hp

/-! ### The stage and well-formedness conditions

This is the `fld_mem` adaptation §2's escape hatch predicted, and it is the only
adaptation the generalisation actually costs.  `Fld` now moves with the
approximation, so `fld_mem` and `pos_mem` have to be asked of `Fld W q` — and it
is enough to ask it of the approximations that can arise, namely the subsets of
the ambient `S.Idx ×ˢ vsetV k`.

Both conditions specialise to the ordinary ones at any such `W`, which together
with `Ind₂_eq_Ind_at` is what makes every stage theorem transfer. -/

structure IsStageSignature₂ (k : V) (S : IndSignature₂ V) : Prop where
  idx_mem : S.Idx ∈ vsetV k
  q_mem : S.Q ∈ vsetV k
  fld_mem : ∀ W : V, W ⊆ (S.Idx ×ˢ vsetV k : V) → ∀ q ∈ S.Q, S.Fld W q ∈ vsetV k
  pos_mem : ∀ W : V, W ⊆ (S.Idx ×ˢ vsetV k : V) → ∀ q ∈ S.Q, ∀ a ∈ S.Fld W q,
    S.Pos q a ∈ vsetV k

/-- The index maps land in `Idx`, at every approximation. -/
structure IndSignature₂.WF (S : IndSignature₂ V) : Prop where
  resIdx_mem : ∀ W : V, ∀ q ∈ S.Q, ∀ a ∈ S.Fld W q, S.resIdx q a ∈ S.Idx

theorem IsStageSignature₂.at {k : V} {S : IndSignature₂ V} (h : IsStageSignature₂ k S)
    {W : V} (hW : W ⊆ (S.Idx ×ˢ vsetV k : V)) : IsStageSignature k (S.at W) where
  idx_mem := h.idx_mem
  q_mem := h.q_mem
  fld_mem := h.fld_mem W hW
  pos_mem := h.pos_mem W hW

theorem IndSignature₂.WF.at {S : IndSignature₂ V} (h : S.WF) (W : V) :
    (S.at W).WF where
  resIdx_mem := h.resIdx_mem W

/-- **The family lands in the stage.**  `Ind_mem_vsetV`, transferred by one
rewrite — the escape hatch costs nothing here either. -/
theorem Ind₂_mem_vsetV {k : V} {S : IndSignature₂ V} (hk : IsInaccessible k)
    (hS : IsStageSignature₂ k S) (hWF : S.WF) : Ind₂ S (vsetV k) ∈ vsetV k := by
  rw [Ind₂_eq_Ind_at]
  exact Ind_mem_vsetV hk (hS.at Ind₂_subset) (hWF.at _)

/-- **…and in the universe sequence.** -/
theorem Ind₂_mem_U_stage {n i : ℕ} {κ : ℕ → V} {S : IndSignature₂ V}
    (hκ : IsInaccessibleChain n κ) (hi : i < n)
    (hS : IsStageSignature₂ (κ i) S) (hWF : S.WF) :
    Ind₂ S (U κ (i + 1)) ∈ U κ (i + 1) :=
  Ind₂_mem_vsetV (hκ.inaccessible i hi) hS hWF

end Operator₂

/-! ## The port: admissible argument tuples

**Ruled in after `CtorData` failed.**  The obstruction was that `a` and `f` are
quantified *independently*, so nothing ties the recursive arguments actually
supplied to the ones the non-recursive field types were checked against.  The
fix is to let the signature say which pairs it accepts.

### Why the cheap alternative was rejected

There is a tempting design that avoids the port: put a redundant copy of the
recursive fillers inside `a`, accept that the carrier then holds junk pairs
where the copy disagrees with `f`, and note that the interpretation never
produces them.  Formation, the recursor and the ι-rule all survive that.

**It breaks large elimination for subsingletons, in fact and not merely in
proof.**  `IsSubsingletonSignature.fld_det` asks
`resIdx q a = resIdx q a' → a = a'`; with a redundant copy, two fillers give the
same result index and different `a`, so `Ind_subsingleton` becomes *false* — the
family genuinely holds distinct elements at one index.  `Eq`, `Iff` and every
proof-irrelevant family with large elimination go through exactly there, and
`EqSpec` is about one of them.  Ruled out on that ground.

### The shape of the change

`Args W q` is a set of pairs `⟨a, f⟩ₖ`, monotone in the approximation.  Every
consumer of the product shape gains **one conjunct**, not a new shape — which is
why the port's proofs stay short.  There is no identification theorem to be had
here: the old theory is stated over the product, so old theorems are *instances*
of the new ones rather than the reverse, and instances do not prove the general
case.  Do not look for one. -/

structure IndSignature₃ (V : Type*) [SetStructure V] extends IndSignature₂ V where
  /-- Which `⟨a, f⟩ₖ` pairs the constructor accepts.  This is the whole port. -/
  Args : V → V → V
  Args_definable : ℒₛₑₜ-function₂[V] Args
  Args_mono : ∀ {W₁ W₂ : V}, W₁ ⊆ W₂ → ∀ q : V, Args W₁ q ⊆ Args W₂ q

attribute [instance] IndSignature₃.Args_definable

section Operator₃

variable {S : IndSignature₃ V} {D : V}

/-- One step of the operator, with the admissibility conjunct. -/
noncomputable def indStep₃ (S : IndSignature₃ V) (D W : V) : V :=
  {p ∈ S.Idx ×ˢ D ;
    ∃ q ∈ S.Q, ∃ a ∈ S.Fld W q, ∃ f ∈ (D ^ S.Pos q a : V),
      (⟨a, f⟩ₖ : V) ∈ S.Args W q ∧
      (∀ b ∈ S.Pos q a, (⟨S.posIdx q a b, f ‘ b⟩ₖ : V) ∈ W) ∧
      p = ⟨S.resIdx q a, ⟨q, ⟨a, f⟩ₖ⟩ₖ⟩ₖ}

theorem mem_indStep₃_iff {W p : V} :
    p ∈ indStep₃ S D W ↔ p ∈ S.Idx ×ˢ D ∧
      ∃ q ∈ S.Q, ∃ a ∈ S.Fld W q, ∃ f ∈ (D ^ S.Pos q a : V),
        (⟨a, f⟩ₖ : V) ∈ S.Args W q ∧
        (∀ b ∈ S.Pos q a, (⟨S.posIdx q a b, f ‘ b⟩ₖ : V) ∈ W) ∧
        p = ⟨S.resIdx q a, ⟨q, ⟨a, f⟩ₖ⟩ₖ⟩ₖ := mem_sep_iff

theorem indStep₃_definable (S : IndSignature₃ V) (D : V) :
    ℒₛₑₜ-function₁[V] (indStep₃ S D) := by
  suffices ℒₛₑₜ-relation[V] (fun T W ↦ T = indStep₃ S D W) by exact this
  have hF := S.Fld_definable
  have hP := S.Pos_definable
  have hI := S.posIdx_definable
  have hR := S.resIdx_definable
  have hA := S.Args_definable
  have e : ∀ T W : V, T = indStep₃ S D W ↔ ∀ p, p ∈ T ↔ p ∈ S.Idx ×ˢ D ∧
      ∃ q ∈ S.Q, ∃ a ∈ S.Fld W q, ∃ f ∈ (D ^ S.Pos q a : V),
        (⟨a, f⟩ₖ : V) ∈ S.Args W q ∧
        (∀ b ∈ S.Pos q a, (⟨S.posIdx q a b, f ‘ b⟩ₖ : V) ∈ W) ∧
        p = ⟨S.resIdx q a, ⟨q, ⟨a, f⟩ₖ⟩ₖ⟩ₖ := by
    intro T W
    rw [mem_ext_iff]
    simp only [mem_indStep₃_iff]
  simp only [e]
  definability

/-- Monotone, and the two new fields are spent here and only here. -/
theorem indStep₃_isMonotoneOn (S : IndSignature₃ V) (D : V) :
    IsMonotoneOn (S.Idx ×ˢ D) (indStep₃ S D) where
  mono W₁ W₂ h p hp := by
    rw [mem_indStep₃_iff] at hp ⊢
    obtain ⟨hb, q, hq, a, ha, f, hf, hok, hrec, he⟩ := hp
    exact ⟨hb, q, hq, a, S.Fld_mono h q _ ha, f, hf, S.Args_mono h q _ hok,
      fun b hbp ↦ h _ (hrec b hbp), he⟩
  maps := sep_subset

noncomputable def Ind₃ (S : IndSignature₃ V) (D : V) : V :=
  lfp (S.Idx ×ˢ D) (indStep₃ S D) (indStep₃_definable S D)

theorem Ind₃_subset : Ind₃ S D ⊆ S.Idx ×ˢ D := lfp_subset (indStep₃_isMonotoneOn S D)

theorem indStep₃_Ind₃ : indStep₃ S D (Ind₃ S D) = Ind₃ S D :=
  apply_lfp (indStep₃_isMonotoneOn S D)

/-- **The induction principle**, ported.  One extra hypothesis component; the
proof is `Ind_induction`'s, otherwise unchanged — which is the evidence that the
port is an added conjunct rather than a reshape.

Note the step is stated at `P`, not at `Ind₃ S D`: `lfp_subset_of_prefixed`
supplies the approximation, and it is `P`.  The old `Ind_induction` is the same
in this respect; the difference is invisible there only because its `Fld` does
not move. -/
theorem Ind₃_induction {P : V} (hP : P ⊆ S.Idx ×ˢ D)
    (hstep : ∀ q ∈ S.Q, ∀ a ∈ S.Fld P q, ∀ f ∈ (D ^ S.Pos q a : V),
      (⟨a, f⟩ₖ : V) ∈ S.Args P q →
      (∀ b ∈ S.Pos q a, (⟨S.posIdx q a b, f ‘ b⟩ₖ : V) ∈ P) →
      (⟨S.resIdx q a, ⟨q, ⟨a, f⟩ₖ⟩ₖ⟩ₖ : V) ∈ P) :
    Ind₃ S D ⊆ P := by
  refine lfp_subset_of_prefixed (indStep₃_isMonotoneOn S D) hP fun p hp ↦ ?_
  rw [mem_indStep₃_iff] at hp
  obtain ⟨-, q, hq, a, ha, f, hf, hok, hrec, rfl⟩ := hp
  exact hstep q hq a ha f hf hok hrec

/-- **Constructor membership**, ported.  The admissibility conjunct is the one
new hypothesis. -/
theorem ctor_mem_Ind₃ {q a f : V} (hq : q ∈ S.Q)
    (hmem : (⟨S.resIdx q a, ⟨q, ⟨a, f⟩ₖ⟩ₖ⟩ₖ : V) ∈ S.Idx ×ˢ D)
    (ha : a ∈ S.Fld (Ind₃ S D) q) (hf : f ∈ (D ^ S.Pos q a : V))
    (hok : (⟨a, f⟩ₖ : V) ∈ S.Args (Ind₃ S D) q)
    (hrec : ∀ b ∈ S.Pos q a, (⟨S.posIdx q a b, f ‘ b⟩ₖ : V) ∈ Ind₃ S D) :
    (⟨S.resIdx q a, ⟨q, ⟨a, f⟩ₖ⟩ₖ⟩ₖ : V) ∈ Ind₃ S D := by
  rw [← indStep₃_Ind₃ (S := S) (D := D), mem_indStep₃_iff]
  exact ⟨hmem, q, hq, a, ha, f, hf, hok, hrec, rfl⟩

/-! ### Carrier and minor premise, ported

Both quantify over the approximation `W`.  That is not decoration: `Ind₃_induction`
hands its step data at the approximation `lfp_subset_of_prefixed` supplies, which
is *not* the fixed point, so a form fixed at `Ind₃ S D` would not apply inside
the induction.  The old versions have no such parameter only because their `Fld`
does not move. -/

structure IsIndCarrier₃ (S : IndSignature₃ V) (D : V) : Prop where
  ctor_mem : ∀ W : V, ∀ q ∈ S.Q, ∀ a ∈ S.Fld W q, ∀ f ∈ (D ^ S.Pos q a : V),
    (⟨a, f⟩ₖ : V) ∈ S.Args W q → (⟨q, ⟨a, f⟩ₖ⟩ₖ : V) ∈ D

structure IsMinorPremise₃ (S : IndSignature₃ V) (D R : V) (e : V → V → V → V → V) :
    Prop where
  mem : ∀ W : V, ∀ q ∈ S.Q, ∀ a ∈ S.Fld W q, ∀ f ∈ (D ^ S.Pos q a : V),
    ∀ h ∈ (R ^ S.Pos q a : V), (⟨a, f⟩ₖ : V) ∈ S.Args W q → e q a f h ∈ R

/-- The constructor value, tagged with its result index. -/
noncomputable def indCtor₃ (S : IndSignature₃ V) (q a f : V) : V :=
  ⟨S.resIdx q a, indCtorVal q a f⟩ₖ

/-- The bound in `indStep₃` is redundant once the carrier is one. -/
theorem mem_indStep₃_iff_of_carrier (hWF : S.toIndSignature₂.WF)
    (hD : IsIndCarrier₃ S D) {W p : V} :
    p ∈ indStep₃ S D W ↔
      ∃ q ∈ S.Q, ∃ a ∈ S.Fld W q, ∃ f ∈ (D ^ S.Pos q a : V),
        (⟨a, f⟩ₖ : V) ∈ S.Args W q ∧
        (∀ b ∈ S.Pos q a, (⟨S.posIdx q a b, f ‘ b⟩ₖ : V) ∈ W) ∧
        p = indCtor₃ S q a f := by
  rw [mem_indStep₃_iff]
  refine ⟨fun h ↦ h.2, fun h ↦ ⟨?_, h⟩⟩
  obtain ⟨q, hq, a, ha, f, hf, hok, -, rfl⟩ := h
  exact kpair_mem_iff.mpr ⟨hWF.resIdx_mem W q hq a ha, hD.ctor_mem W q hq a ha f hf hok⟩

/-! ### The recursor's graph, ported

The graph is built over the completed family, so its `Fld`/`Args` are read at
`Ind₃ S D`. -/

noncomputable def recStep₃ (S : IndSignature₃ V) (D R : V) (e : V → V → V → V → V)
    (he : ℒₛₑₜ-function₄[V] e) (g : V) : V :=
  {p ∈ (S.Idx ×ˢ D) ×ˢ R ;
    ∃ q ∈ S.Q, ∃ a ∈ S.Fld (Ind₃ S D) q, ∃ f ∈ (D ^ S.Pos q a : V),
      ∃ h ∈ (R ^ S.Pos q a : V),
      (⟨a, f⟩ₖ : V) ∈ S.Args (Ind₃ S D) q ∧
      (∀ b ∈ S.Pos q a, (⟨⟨S.posIdx q a b, f ‘ b⟩ₖ, h ‘ b⟩ₖ : V) ∈ g) ∧
      p = ⟨indCtor₃ S q a f, e q a f h⟩ₖ}

variable {R : V} {e : V → V → V → V → V}

theorem mem_recStep₃_iff' {he : ℒₛₑₜ-function₄[V] e} {g p : V} :
    p ∈ recStep₃ S D R e he g ↔ p ∈ (S.Idx ×ˢ D) ×ˢ R ∧
      ∃ q ∈ S.Q, ∃ a ∈ S.Fld (Ind₃ S D) q, ∃ f ∈ (D ^ S.Pos q a : V),
        ∃ h ∈ (R ^ S.Pos q a : V),
        (⟨a, f⟩ₖ : V) ∈ S.Args (Ind₃ S D) q ∧
        (∀ b ∈ S.Pos q a, (⟨⟨S.posIdx q a b, f ‘ b⟩ₖ, h ‘ b⟩ₖ : V) ∈ g) ∧
        p = ⟨indCtor₃ S q a f, e q a f h⟩ₖ := mem_sep_iff

theorem mem_recStep₃_iff (hWF : S.toIndSignature₂.WF)
    (hD : IsIndCarrier₃ S D) (hE : IsMinorPremise₃ S D R e)
    {he : ℒₛₑₜ-function₄[V] e} {g p : V} :
    p ∈ recStep₃ S D R e he g ↔
      ∃ q ∈ S.Q, ∃ a ∈ S.Fld (Ind₃ S D) q, ∃ f ∈ (D ^ S.Pos q a : V),
        ∃ h ∈ (R ^ S.Pos q a : V),
        (⟨a, f⟩ₖ : V) ∈ S.Args (Ind₃ S D) q ∧
        (∀ b ∈ S.Pos q a, (⟨⟨S.posIdx q a b, f ‘ b⟩ₖ, h ‘ b⟩ₖ : V) ∈ g) ∧
        p = ⟨indCtor₃ S q a f, e q a f h⟩ₖ := by
  rw [mem_recStep₃_iff']
  refine ⟨fun h ↦ h.2, fun h ↦ ⟨?_, h⟩⟩
  obtain ⟨q, hq, a, ha, f, hf, h, hh, hok, -, rfl⟩ := h
  exact kpair_mem_iff.mpr
    ⟨kpair_mem_iff.mpr ⟨hWF.resIdx_mem _ q hq a ha, hD.ctor_mem _ q hq a ha f hf hok⟩,
      hE.mem _ q hq a ha f hf h hh hok⟩

theorem recStep₃_definable (S : IndSignature₃ V) (D R : V) (e : V → V → V → V → V)
    (he : ℒₛₑₜ-function₄[V] e) : ℒₛₑₜ-function₁[V] (recStep₃ S D R e he) := by
  suffices ℒₛₑₜ-relation[V] (fun T g ↦ T = recStep₃ S D R e he g) by exact this
  have hF := S.Fld_definable
  have hP := S.Pos_definable
  have hI := S.posIdx_definable
  have hR := S.resIdx_definable
  have hA := S.Args_definable
  have eq : ∀ T g : V, T = recStep₃ S D R e he g ↔ ∀ p, p ∈ T ↔
      p ∈ (S.Idx ×ˢ D) ×ˢ R ∧
      ∃ q ∈ S.Q, ∃ a ∈ S.Fld (Ind₃ S D) q, ∃ f ∈ (D ^ S.Pos q a : V),
        ∃ h ∈ (R ^ S.Pos q a : V),
        (⟨a, f⟩ₖ : V) ∈ S.Args (Ind₃ S D) q ∧
        (∀ b ∈ S.Pos q a, (⟨⟨S.posIdx q a b, f ‘ b⟩ₖ, h ‘ b⟩ₖ : V) ∈ g) ∧
        p = ⟨indCtor₃ S q a f, e q a f h⟩ₖ := by
    intro T g
    rw [mem_ext_iff]
    simp only [mem_recStep₃_iff']
  simp only [eq, indCtor₃, indCtorVal]
  definability

theorem recStep₃_isMonotoneOn (S : IndSignature₃ V) (D R : V) (e : V → V → V → V → V)
    (he : ℒₛₑₜ-function₄[V] e) :
    IsMonotoneOn ((S.Idx ×ˢ D) ×ˢ R) (recStep₃ S D R e he) where
  mono g₁ g₂ hg p hp := by
    rw [mem_recStep₃_iff'] at hp ⊢
    obtain ⟨hb, q, hq, a, ha, f, hf, h, hh, hok, hrec, heq⟩ := hp
    exact ⟨hb, q, hq, a, ha, f, hf, h, hh, hok, fun b hbp ↦ hg _ (hrec b hbp), heq⟩
  maps := sep_subset

noncomputable def recGraph₃ (S : IndSignature₃ V) (D R : V) (e : V → V → V → V → V)
    (he : ℒₛₑₜ-function₄[V] e) : V :=
  lfp ((S.Idx ×ˢ D) ×ˢ R) (recStep₃ S D R e he) (recStep₃_definable S D R e he)

theorem recGraph₃_subset {he : ℒₛₑₜ-function₄[V] e} :
    recGraph₃ S D R e he ⊆ (S.Idx ×ˢ D) ×ˢ R :=
  lfp_subset (recStep₃_isMonotoneOn S D R e he)

theorem recStep₃_recGraph₃ {he : ℒₛₑₜ-function₄[V] e} :
    recStep₃ S D R e he (recGraph₃ S D R e he) = recGraph₃ S D R e he :=
  apply_lfp (recStep₃_isMonotoneOn S D R e he)

theorem mem_recGraph₃_iff (hWF : S.toIndSignature₂.WF)
    (hD : IsIndCarrier₃ S D) (hE : IsMinorPremise₃ S D R e)
    {he : ℒₛₑₜ-function₄[V] e} {p : V} :
    p ∈ recGraph₃ S D R e he ↔
      ∃ q ∈ S.Q, ∃ a ∈ S.Fld (Ind₃ S D) q, ∃ f ∈ (D ^ S.Pos q a : V),
        ∃ h ∈ (R ^ S.Pos q a : V),
        (⟨a, f⟩ₖ : V) ∈ S.Args (Ind₃ S D) q ∧
        (∀ b ∈ S.Pos q a,
          (⟨⟨S.posIdx q a b, f ‘ b⟩ₖ, h ‘ b⟩ₖ : V) ∈ recGraph₃ S D R e he) ∧
        p = ⟨indCtor₃ S q a f, e q a f h⟩ₖ := by
  conv_lhs => rw [← recStep₃_recGraph₃ (S := S) (D := D) (R := R) (e := e) (he := he)]
  exact mem_recStep₃_iff hWF hD hE

/-! ### Totality, single-valuedness, and the recursor

`recGraph_unique₃` ports with one extra destructured component and nothing else.

`recGraph_total₃` is **the one declaration in the port that needed more than
that**, and the reason is the invariant made visible above: `Ind₃_induction`
hands its step data at the approximation, not at the fixed point, so the old
proof's target set — a `sep` of `S.Idx ×ˢ D` — gives `a ∈ S.Fld P q` where
`mem_recGraph₃_iff` wants `a ∈ S.Fld (Ind₃ S D) q`, and `P ⊄ Ind₃ S D`.

The fix is one word: `sep` over `Ind₃ S D` instead of over `S.Idx ×ˢ D`.  Then
`P ⊆ Ind₃ S D` and `Fld_mono`/`Args_mono` carry the step data across.  Small,
but genuinely more than an added component — recorded here rather than in a
summary, because that is where the estimate would drift if it drifted. -/

section RecursorTotal₃

variable {S : IndSignature₃ V} {D R : V} {e : V → V → V → V → V}
  {he : ℒₛₑₜ-function₄[V] e}
variable (hWF : S.toIndSignature₂.WF) (hD : IsIndCarrier₃ S D)
  (hE : IsMinorPremise₃ S D R e)

include hWF hD hE

theorem recGraph₃_unique : ∀ x i₁ i₂ v₁ v₂ : V,
    (⟨⟨i₁, x⟩ₖ, v₁⟩ₖ : V) ∈ recGraph₃ S D R e he →
    (⟨⟨i₂, x⟩ₖ, v₂⟩ₖ : V) ∈ recGraph₃ S D R e he → v₁ = v₂ := by
  refine rank_induction (fun x ↦ ∀ i₁ i₂ v₁ v₂ : V,
    (⟨⟨i₁, x⟩ₖ, v₁⟩ₖ : V) ∈ recGraph₃ S D R e he →
    (⟨⟨i₂, x⟩ₖ, v₂⟩ₖ : V) ∈ recGraph₃ S D R e he → v₁ = v₂) (by definability) ?_
  intro x ih i₁ i₂ v₁ v₂ h₁ h₂
  obtain ⟨q, hq, a, ha, f, hf, h, hh, -, hrec, heq⟩ :=
    (mem_recGraph₃_iff hWF hD hE).mp h₁
  obtain ⟨q', hq', a', ha', f', hf', h', hh', -, hrec', heq'⟩ :=
    (mem_recGraph₃_iff hWF hD hE).mp h₂
  obtain ⟨hc, rfl⟩ := kpair_inj heq
  obtain ⟨hc', rfl⟩ := kpair_inj heq'
  obtain ⟨-, hx⟩ := kpair_inj hc
  obtain ⟨-, hx'⟩ := kpair_inj hc'
  obtain ⟨rfl, hp⟩ := kpair_inj (hx ▸ hx' : (indCtorVal q a f : V) = indCtorVal q' a' f')
  obtain ⟨rfl, rfl⟩ := kpair_inj hp
  suffices hhh : h = h' by rw [hhh]
  refine function_ext hh hh' fun b hb y hy hyh ↦ ?_
  have hfun : IsFunction h := IsFunction.of_mem hh
  have hval : h ‘ b = y := value_eq_of_kpair_mem hyh
  have hrk : rank (f ‘ b) < rank x := by
    rw [hx]; exact rank_lt_indCtorVal (kpair_value_mem hf hb)
  have := ih (f ‘ b) hrk (S.posIdx q a b) (S.posIdx q a b) (h ‘ b) (h' ‘ b)
    (hrec b hb) (hrec' b hb)
  rw [hval] at this
  rw [this]
  exact kpair_value_mem hh' hb

theorem recGraph₃_total : ∀ p ∈ Ind₃ S D,
    ∃ v : V, (⟨p, v⟩ₖ : V) ∈ recGraph₃ S D R e he := by
  have key : Ind₃ S D ⊆
      {p ∈ Ind₃ S D ; ∃ v : V, (⟨p, v⟩ₖ : V) ∈ recGraph₃ S D R e he} := by
    refine Ind₃_induction (subset_trans sep_subset Ind₃_subset) ?_
    intro q hq a ha f hf hok hrec
    have hPsub : {p ∈ Ind₃ S D ; ∃ v : V, (⟨p, v⟩ₖ : V) ∈ recGraph₃ S D R e he}
        ⊆ Ind₃ S D := sep_subset
    -- the step data, moved from the approximation to the fixed point
    have ha' : a ∈ S.Fld (Ind₃ S D) q := S.Fld_mono hPsub q _ ha
    have hok' : (⟨a, f⟩ₖ : V) ∈ S.Args (Ind₃ S D) q := S.Args_mono hPsub q _ hok
    have hrec' : ∀ b ∈ S.Pos q a, (⟨S.posIdx q a b, f ‘ b⟩ₖ : V) ∈ Ind₃ S D :=
      fun b hb ↦ hPsub _ (hrec b hb)
    obtain ⟨h, hmemh⟩ : ∃ h : V, ∀ p : V, p ∈ h ↔ ∃ b ∈ S.Pos q a, ∃ v : V,
        p = ⟨b, v⟩ₖ ∧ (⟨⟨S.posIdx q a b, f ‘ b⟩ₖ, v⟩ₖ : V) ∈ recGraph₃ S D R e he := by
      refine ⟨sep (S.Pos q a ×ˢ R) (fun p ↦ ∃ b ∈ S.Pos q a, ∃ v : V,
        p = ⟨b, v⟩ₖ ∧ (⟨⟨S.posIdx q a b, f ‘ b⟩ₖ, v⟩ₖ : V) ∈ recGraph₃ S D R e he),
        fun p ↦ ?_⟩
      rw [mem_sep_iff]
      refine ⟨fun h ↦ h.2, fun h ↦ ⟨?_, h⟩⟩
      obtain ⟨b, hb, v, rfl, hv⟩ := h
      exact kpair_mem_iff.mpr ⟨hb, (kpair_mem_iff.mp (recGraph₃_subset _ hv)).2⟩
    have hkp : ∀ b y : V, (⟨b, y⟩ₖ : V) ∈ h ↔ b ∈ S.Pos q a ∧
        (⟨⟨S.posIdx q a b, f ‘ b⟩ₖ, y⟩ₖ : V) ∈ recGraph₃ S D R e he := by
      intro b y
      rw [hmemh]
      refine ⟨?_, fun hy ↦ ⟨b, hy.1, y, rfl, hy.2⟩⟩
      rintro ⟨b', hb', v, hev, hv⟩
      obtain ⟨rfl, rfl⟩ := kpair_inj hev
      exact ⟨hb', hv⟩
    have hhmem : h ∈ (R ^ S.Pos q a : V) := by
      refine mem_function.intro (fun p hp ↦ ?_) (fun b hb ↦ ?_)
      · obtain ⟨b, hb, v, rfl, hv⟩ := hmemh p |>.mp hp
        exact kpair_mem_iff.mpr ⟨hb, (kpair_mem_iff.mp (recGraph₃_subset _ hv)).2⟩
      · obtain ⟨-, v, hv⟩ := mem_sep_iff.mp (hrec b hb)
        refine ExistsUnique.intro v ((hkp b v).mpr ⟨hb, hv⟩) fun v' hv' ↦ ?_
        exact recGraph₃_unique hWF hD hE (f ‘ b) _ _ v' v ((hkp b v').mp hv').2 hv
    refine mem_sep_iff.mpr ⟨ctor_mem_Ind₃ hq ?_ ha' hf hok' hrec', e q a f h,
      (mem_recGraph₃_iff hWF hD hE).mpr
        ⟨q, hq, a, ha', f, hf, h, hhmem, hok', fun b hb ↦ ?_, rfl⟩⟩
    · exact kpair_mem_iff.mpr
        ⟨hWF.resIdx_mem _ q hq a ha', hD.ctor_mem _ q hq a ha' f hf hok'⟩
    · exact ((hkp b (h ‘ b)).mp (kpair_value_mem hhmem hb)).2
  intro p hp
  exact (mem_sep_iff.mp (key p hp)).2

theorem isFunction_recGraph₃ : IsFunction (recGraph₃ S D R e he) := by
  refine isFunction_iff.mpr (mem_function.intro (fun p hp ↦ ?_) (fun x hx ↦ ?_))
  · obtain ⟨q, hq, a, ha, f, hf, h, hh, hok, hrec, rfl⟩ :=
      (mem_recGraph₃_iff hWF hD hE).mp hp
    exact kpair_mem_iff.mpr ⟨mem_domain_of_kpair_mem hp, mem_range_of_kpair_mem hp⟩
  · obtain ⟨v, hv⟩ := mem_domain_iff.mp hx
    refine ExistsUnique.intro v hv fun v' hv' ↦ ?_
    obtain ⟨i, -, y, -, rfl⟩ :=
      mem_prod_iff.mp (kpair_mem_iff.mp (recGraph₃_subset _ hv)).1
    exact recGraph₃_unique hWF hD hE y i i v' v hv' hv

/-- **The recursor.** -/
noncomputable def indRec₃ (S : IndSignature₃ V) (D R : V) (e : V → V → V → V → V)
    (he : ℒₛₑₜ-function₄[V] e) (p : V) : V := (recGraph₃ S D R e he) ‘ p

theorem indRec₃_kpair_mem {p : V} (hp : p ∈ Ind₃ S D) :
    (⟨p, indRec₃ S D R e he p⟩ₖ : V) ∈ recGraph₃ S D R e he := by
  obtain ⟨v, hv⟩ := recGraph₃_total hWF hD hE p hp
  have : IsFunction (recGraph₃ S D R e he) := isFunction_recGraph₃ hWF hD hE
  rw [indRec₃, value_eq_of_kpair_mem hv]
  exact hv

/-- **The recursor lands in the motive.** -/
theorem indRec₃_mem {p : V} (hp : p ∈ Ind₃ S D) : indRec₃ S D R e he p ∈ R :=
  (kpair_mem_iff.mp (recGraph₃_subset _ (indRec₃_kpair_mem hWF hD hE hp))).2

/-! ### The ι-rule, ported

Every declaration here is the old one plus the admissibility component; nothing
needed restructuring. -/

/-- The internal tuple of recursive results. -/
noncomputable def indRecTuple₃ (S : IndSignature₃ V) (D R : V) (e : V → V → V → V → V)
    (he : ℒₛₑₜ-function₄[V] e) (q a f : V) : V :=
  {p ∈ S.Pos q a ×ˢ R ;
    ∃ b ∈ S.Pos q a, p = ⟨b, indRec₃ S D R e he (⟨S.posIdx q a b, f ‘ b⟩ₖ)⟩ₖ}

theorem mem_indRecTuple₃_iff {q a f b y : V}
    (hrec : ∀ b ∈ S.Pos q a, (⟨S.posIdx q a b, f ‘ b⟩ₖ : V) ∈ Ind₃ S D) :
    (⟨b, y⟩ₖ : V) ∈ indRecTuple₃ S D R e he q a f ↔
      b ∈ S.Pos q a ∧ y = indRec₃ S D R e he (⟨S.posIdx q a b, f ‘ b⟩ₖ) := by
  rw [indRecTuple₃, mem_sep_iff]
  constructor
  · rintro ⟨-, b', hb', hev⟩
    obtain ⟨rfl, rfl⟩ := kpair_inj hev
    exact ⟨hb', rfl⟩
  · rintro ⟨hb, rfl⟩
    exact ⟨kpair_mem_iff.mpr ⟨hb, indRec₃_mem hWF hD hE (hrec b hb)⟩, b, hb, rfl⟩

theorem indRecTuple₃_mem_function {q a f : V}
    (hrec : ∀ b ∈ S.Pos q a, (⟨S.posIdx q a b, f ‘ b⟩ₖ : V) ∈ Ind₃ S D) :
    indRecTuple₃ S D R e he q a f ∈ (R ^ S.Pos q a : V) := by
  refine mem_function.intro (fun p hp ↦ ?_) (fun b hb ↦ ?_)
  · obtain ⟨-, b, hb, rfl⟩ := mem_sep_iff.mp hp
    exact kpair_mem_iff.mpr ⟨hb, indRec₃_mem hWF hD hE (hrec b hb)⟩
  · refine ExistsUnique.intro (indRec₃ S D R e he (⟨S.posIdx q a b, f ‘ b⟩ₖ))
      ((mem_indRecTuple₃_iff hWF hD hE hrec).mpr ⟨hb, rfl⟩) fun y hy ↦ ?_
    exact ((mem_indRecTuple₃_iff hWF hD hE hrec).mp hy).2

theorem indRecTuple₃_value {q a f b : V}
    (hrec : ∀ b ∈ S.Pos q a, (⟨S.posIdx q a b, f ‘ b⟩ₖ : V) ∈ Ind₃ S D)
    (hb : b ∈ S.Pos q a) :
    (indRecTuple₃ S D R e he q a f) ‘ b
      = indRec₃ S D R e he (⟨S.posIdx q a b, f ‘ b⟩ₖ) := by
  have hfun : IsFunction (indRecTuple₃ S D R e he q a f) :=
    IsFunction.of_mem (indRecTuple₃_mem_function hWF hD hE hrec)
  exact value_eq_of_kpair_mem ((mem_indRecTuple₃_iff hWF hD hE hrec).mpr ⟨hb, rfl⟩)

/-- **The ι-rule**, ported: `F (ctor q a f) = e q a f (F ∘ f)`.  The one new
hypothesis is admissibility of `⟨a, f⟩ₖ`, which is exactly the fact that was
missing and made `CtorData` unbuildable. -/
theorem indRec₃_indCtor₃ {q a f : V} (hq : q ∈ S.Q) (ha : a ∈ S.Fld (Ind₃ S D) q)
    (hf : f ∈ (D ^ S.Pos q a : V)) (hok : (⟨a, f⟩ₖ : V) ∈ S.Args (Ind₃ S D) q)
    (hrec : ∀ b ∈ S.Pos q a, (⟨S.posIdx q a b, f ‘ b⟩ₖ : V) ∈ Ind₃ S D) :
    indRec₃ S D R e he (indCtor₃ S q a f)
      = e q a f (indRecTuple₃ S D R e he q a f) := by
  have hfun : IsFunction (recGraph₃ S D R e he) := isFunction_recGraph₃ hWF hD hE
  refine value_eq_of_kpair_mem ((mem_recGraph₃_iff hWF hD hE).mpr
    ⟨q, hq, a, ha, f, hf, _, indRecTuple₃_mem_function hWF hD hE hrec, hok,
      fun b hb ↦ ?_, rfl⟩)
  rw [indRecTuple₃_value hWF hD hE hrec hb]
  exact indRec₃_kpair_mem hWF hD hE (hrec b hb)

end RecursorTotal₃

/-! ### Stage membership, without porting `IndCard`

The cardinality argument is 506 lines and does **not** need porting.  Dropping
the admissibility conjunct only enlarges the operator, so `Ind₃` sits inside the
*ordinary* family at the **top** approximation `S.Idx ×ˢ D` — and that
approximation dominates every one the induction can produce, which is what makes
the step's `Fld_mono` fire in the right direction (the wrong one is what broke
`recGraph₃_total`'s first form).

From there `rank_mono` finishes it: a subset of a member of `vsetV k` is a
member.  No new stage structure is needed either — `IsStageSignature₂` applies
to `S.toIndSignature₂`. -/

/-- **Admissibility is not needed for containment.**  `Ind₃_induction` with the
`Args` component dropped — every set closed under the constructors contains the
family, whether or not it tracks admissibility. -/
theorem Ind₃_subset_of {P : V} (hP : P ⊆ S.Idx ×ˢ D)
    (hstep : ∀ q ∈ S.Q, ∀ a ∈ S.Fld P q, ∀ f ∈ (D ^ S.Pos q a : V),
      (∀ b ∈ S.Pos q a, (⟨S.posIdx q a b, f ‘ b⟩ₖ : V) ∈ P) →
      indCtor₃ S q a f ∈ P) :
    Ind₃ S D ⊆ P :=
  Ind₃_induction hP (fun q hq a ha f hf _ hrec ↦ hstep q hq a ha f hf hrec)

/-- **The rank step, which is what the check was for.**  `rank_mono`
(`SetModel/Rank.lean`) exists, so a subset of a member of `vsetV k` is a member,
and `IndCard.lean`'s 506-line cardinality argument does **not** need porting —
`Ind₃` inherits its bound from any containing set already known to be in the
stage. -/
theorem Ind₃_mem_vsetV_of {k X : V} [IsOrdinal k]
    (hX : X ∈ vsetV k) (hsub : Ind₃ S D ⊆ X) : Ind₃ S D ∈ vsetV k := by
  rw [mem_vsetV_iff_mem_Vset] at hX ⊢
  rw [mem_Vset_iff_rank_lt] at hX ⊢
  exact lt_of_le_of_lt (rank_mono hsub) hX

/-- **`Ind₃` sits inside the ordinary family of any dominating signature.**

Stated **schematically**: `S'` is an abstract `IndSignature` related to `S` by
field equations, never the concrete `S.at W₀`.  That is the remedy
`SetModel/Cnst.lean` documents for `mkLam_mem_mkForallType`, and it is needed
for the same reason: `Ind S' D` unfolds to `lfp _ (indStep S' D)
(indStep_definable S' D)`, and with `S'` concrete that definability *proof term*
is large enough to hang `whnf`.  With `S'` a variable it is never unfolded.

Dropping admissibility only enlarges the operator, and `W₀` dominating
`S.Idx ×ˢ D` is what makes `Fld_mono` fire in the right direction — the wrong
one is what broke `recGraph₃_total`'s first form. -/
theorem Ind₃_subset_Ind_of {S' : IndSignature V} {W₀ : V}
    (hIdx : S'.Idx = S.Idx) (hQ : S'.Q = S.Q)
    (hFld : ∀ q : V, S.Fld W₀ q ⊆ S'.Fld q)
    (hPos : ∀ q a : V, S'.Pos q a = S.Pos q a)
    (hPI : ∀ q a b : V, S'.posIdx q a b = S.posIdx q a b)
    (hRI : ∀ q a : V, S'.resIdx q a = S.resIdx q a)
    (hW₀ : (S.Idx ×ˢ D : V) ⊆ W₀)
    (hWF : S'.WF) (hD : IsIndCarrier S' D) :
    Ind₃ S D ⊆ Ind S' D := by
  have hamb : Ind S' D ⊆ (S.Idx ×ˢ D : V) := by
    intro p hp
    have h := Ind_subset S' D p hp
    rwa [hIdx] at h
  refine Ind₃_subset_of hamb (fun q hq a ha f hf hrec ↦ ?_)
  have ha' : a ∈ S'.Fld q :=
    hFld q _ (S.Fld_mono (subset_trans hamb hW₀) q _ ha)
  have hf' : f ∈ (D ^ S'.Pos q a : V) := by rw [hPos]; exact hf
  have hrec' : ∀ b ∈ S'.Pos q a, (⟨S'.posIdx q a b, f ‘ b⟩ₖ : V) ∈ Ind S' D := by
    intro b hb
    rw [hPI]
    exact hrec b (by rwa [hPos] at hb)
  have hq' : q ∈ S'.Q := by rw [hQ]; exact hq
  have := ctor_mem_Ind hWF hD hq' ha' hf' hrec'
  rwa [indCtor, hRI] at this

/-- **The family lands in the stage.**  `IndCard`'s cardinality argument is
inherited rather than ported. -/
theorem Ind₃_mem_vsetV {k : V} (hk : IsInaccessible k)
    (hS : IsStageSignature₂ k S.toIndSignature₂) (hWF : S.toIndSignature₂.WF)
    (hD : IsIndCarrier (S.toIndSignature₂.at (S.Idx ×ˢ vsetV k)) (vsetV k)) :
    Ind₃ S (vsetV k) ∈ vsetV k := by
  haveI : IsOrdinal k := hk.isOrdinal
  have hsub := Ind₃_subset_Ind_of (S := S) (D := vsetV k)
    (S' := S.toIndSignature₂.at (S.Idx ×ˢ vsetV k)) (W₀ := S.Idx ×ˢ vsetV k)
    rfl rfl (fun _ _ h ↦ h) (fun _ _ ↦ rfl) (fun _ _ _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ h ↦ h) (hWF.at _) hD
  exact Ind₃_mem_vsetV_of (Ind_mem_vsetV hk (hS.at (fun _ h ↦ h)) (hWF.at _)) hsub

/-- **…and in the universe sequence.** -/
theorem Ind₃_mem_U_stage {n i : ℕ} {κ : ℕ → V} {S : IndSignature₃ V}
    (hκ : IsInaccessibleChain n κ) (hi : i < n)
    (hS : IsStageSignature₂ (κ i) S.toIndSignature₂) (hWF : S.toIndSignature₂.WF)
    (hD : IsIndCarrier (S.toIndSignature₂.at (S.Idx ×ˢ U κ (i + 1))) (U κ (i + 1))) :
    Ind₃ S (U κ (i + 1)) ∈ U κ (i + 1) :=
  Ind₃_mem_vsetV (hκ.inaccessible i hi) hS hWF hD

end Operator₃

/-! ## The ₃ assembly: `interpSig_stage` and `interpSig_wf`, at the assembly level

These are the two proofs `docs/model-interface.md` §2 asks for.  They belong to
the **assembly** half — per-constructor data to a signature — which the port
closed and which the blocked translation does not gate.

The port changed `Fld` from `V → V` to `V → V → V`, taking the approximation
*first* and the tag *second*.  So the tag dispatch now has to be definable in
the **second** argument, which `tagCase₁` cannot do: hence `tagCaseSnd`. -/

/-- A definable split on an equality with the **second** argument. -/
theorem ite_eq_snd_definable₂ {c : V} {f g : V → V → V}
    (hf : ℒₛₑₜ-function₂[V] f) (hg : ℒₛₑₜ-function₂[V] g) :
    ℒₛₑₜ-function₂[V] (fun w q ↦ if q = c then f w q else g w q) := by
  suffices ℒₛₑₜ-relation₃[V] (fun T w q ↦ T = if q = c then f w q else g w q) by exact this
  have e : ∀ T w q : V, (T = if q = c then f w q else g w q) ↔
      ((q = c → T = f w q) ∧ (q ≠ c → T = g w q)) := by
    intro T w q; by_cases h : q = c <;> simp [h]
  simp only [e]
  definability

/-- Dispatch on the tag, which is the **second** argument.  The entries see only
the approximation, because `Fld W q` does not otherwise depend on `q`. -/
noncomputable def tagCaseSnd : ℕ → List (V → V) → V → V → V
  | _, [], _, _ => ∅
  | i, f :: fs, w, q => if q = ((i : ℕ) : V) then f w else tagCaseSnd (i + 1) fs w q

theorem tagCaseSnd_definable : ∀ (i : ℕ) (fs : List (V → V)),
    (∀ f ∈ fs, ℒₛₑₜ-function₁[V] f) → ℒₛₑₜ-function₂[V] (tagCaseSnd i fs)
  | i, [], _ => by
    have h0 : (tagCaseSnd i ([] : List (V → V)) : V → V → V) = fun _ _ ↦ (∅ : V) := rfl
    rw [h0]; definability
  | i, f :: fs, h => by
    have hf := h f (.head _)
    have hrest := tagCaseSnd_definable (i + 1) fs fun g hg ↦ h g (.tail _ hg)
    have h0 : (tagCaseSnd i (f :: fs) : V → V → V)
        = fun w q ↦ if q = ((i : ℕ) : V) then f w else tagCaseSnd (i + 1) fs w q := rfl
    rw [h0]
    exact ite_eq_snd_definable₂ (by definability) hrest

/-- Monotone in the approximation as soon as every entry is — the test is on the
tag, which does not move. -/
theorem tagCaseSnd_mono : ∀ (i : ℕ) (fs : List (V → V)) {W₁ W₂ : V},
    (∀ f ∈ fs, f W₁ ⊆ f W₂) → ∀ q : V, tagCaseSnd i fs W₁ q ⊆ tagCaseSnd i fs W₂ q
  | _, [], _, _, _, _ => fun _ hz ↦ hz
  | i, f :: fs, W₁, W₂, h, q => by
    show (if q = ((i : ℕ) : V) then _ else _) ⊆ (if q = ((i : ℕ) : V) then _ else _)
    by_cases hq : q = ((i : ℕ) : V)
    · rw [if_pos hq, if_pos hq]; exact h f (.head _)
    · rw [if_neg hq, if_neg hq]
      exact tagCaseSnd_mono (i + 1) fs (fun g hg ↦ h g (.tail _ hg)) q

theorem tagCaseSnd_at : ∀ (i : ℕ) (fs : List (V → V)) (k : ℕ) (f : V → V),
    fs[k]? = some f → ∀ w : V, tagCaseSnd i fs w (((i + k : ℕ)) : V) = f w
  | i, g :: fs, 0, f, h, w => by
    have hgf : g = f := by simpa using h
    subst hgf
    simp only [Nat.add_zero]
    show (if _ = _ then _ else _) = _
    rw [if_pos rfl]
  | i, g :: fs, k + 1, f, h, w => by
    show (if _ = _ then _ else _) = _
    rw [if_neg (ofNat_ne_ofNat (by omega))]
    have ih := tagCaseSnd_at (i + 1) fs k f (by simpa using h) w
    have e : i + 1 + k = i + (k + 1) := by omega
    rw [e] at ih
    exact ih

theorem tagCase₂_at : ∀ (i : ℕ) (fs : List (V → V → V)) (k : ℕ) (f : V → V → V),
    fs[k]? = some f → ∀ a : V,
      tagCase₂ i fs (((i + k : ℕ)) : V) a = f (((i + k : ℕ)) : V) a
  | i, g :: fs, 0, f, h, a => by
    have hgf : g = f := by simpa using h
    subst hgf
    simp only [Nat.add_zero]
    show (if _ = _ then _ else _) = _
    rw [if_pos rfl]
  | i, g :: fs, k + 1, f, h, a => by
    show (if _ = _ then _ else _) = _
    rw [if_neg (ofNat_ne_ofNat (by omega))]
    have ih := tagCase₂_at (i + 1) fs k f (by simpa using h) a
    have e : i + 1 + k = i + (k + 1) := by omega
    rw [e] at ih
    exact ih

/-- The tags really are the numerals below `n`. -/
theorem mem_ofNat_iff : ∀ (n : ℕ) (q : V),
    q ∈ ((n : ℕ) : V) ↔ ∃ k, k < n ∧ q = ((k : ℕ) : V)
  | 0, q => by
    constructor
    · intro h
      rw [show ((0 : ℕ) : V) = ∅ from by simp [zero_def]] at h
      exact absurd h (by simp)
    · rintro ⟨k, hk, -⟩; omega
  | n + 1, q => by
    rw [num_succ_def, mem_succ_iff]
    constructor
    · rintro (rfl | h)
      · exact ⟨n, by omega, rfl⟩
      · obtain ⟨k, hk, rfl⟩ := (mem_ofNat_iff n q).1 h
        exact ⟨k, by omega, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with h | rfl
      · exact Or.inr ((mem_ofNat_iff n _).2 ⟨k, h, rfl⟩)
      · exact Or.inl rfl

/-- Per-constructor data for the ported signature.  `flds` and `args` now take
the approximation and must be monotone in it — the two obligations the port
added, pushed out to the caller where they belong. -/
structure CtorData₃ (V : Type*) [SetStructure V] where
  flds : V → V
  flds_definable : ℒₛₑₜ-function₁[V] flds
  flds_mono : ∀ {W₁ W₂ : V}, W₁ ⊆ W₂ → flds W₁ ⊆ flds W₂
  poss : List (V → V)
  poss_definable : ∀ p ∈ poss, ℒₛₑₜ-function₁[V] p
  posIdxs : List (V → V → V)
  posIdxs_definable : ∀ p ∈ posIdxs, ℒₛₑₜ-function₂[V] p
  resIdx : V → V
  resIdx_definable : ℒₛₑₜ-function₁[V] resIdx
  args : V → V
  args_definable : ℒₛₑₜ-function₁[V] args
  args_mono : ∀ {W₁ W₂ : V}, W₁ ⊆ W₂ → args W₁ ⊆ args W₂

/-- **The ported assembly.**  All six definability obligations and both
monotonicity obligations discharged. -/
noncomputable def mkIndSignature₃ (Idx : V) (cs : List (CtorData₃ V)) :
    IndSignature₃ V where
  Idx := Idx
  Q := ((cs.length : ℕ) : V)
  Fld := tagCaseSnd 0 (cs.map (·.flds))
  Pos := tagCase₂ 0 (cs.map fun c ↦ fun _ a ↦ tagUnionF 0 c.poss a)
  posIdx := tagCase₃ 0 (cs.map fun c ↦ fun _ a b ↦ tagSel₂ 0 c.posIdxs a b)
  resIdx := tagCase₂ 0 (cs.map fun c ↦ fun _ a ↦ c.resIdx a)
  Args := tagCaseSnd 0 (cs.map (·.args))
  Fld_definable := by
    refine tagCaseSnd_definable _ _ fun f hf ↦ ?_
    obtain ⟨c, -, rfl⟩ := List.mem_map.1 hf
    exact c.flds_definable
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
  Fld_mono := by
    refine fun h ↦ tagCaseSnd_mono _ _ fun f hf ↦ ?_
    obtain ⟨c, -, rfl⟩ := List.mem_map.1 hf
    exact c.flds_mono h
  Args_definable := by
    refine tagCaseSnd_definable _ _ fun f hf ↦ ?_
    obtain ⟨c, -, rfl⟩ := List.mem_map.1 hf
    exact c.args_definable
  Args_mono := by
    refine fun h ↦ tagCaseSnd_mono _ _ fun f hf ↦ ?_
    obtain ⟨c, -, rfl⟩ := List.mem_map.1 hf
    exact c.args_mono h

/-- **`interpSig_wf`, at the assembly level.** -/
theorem mkIndSignature₃_wf {Idx : V} {cs : List (CtorData₃ V)}
    (h : ∀ c ∈ cs, ∀ W : V, ∀ a ∈ c.flds W, c.resIdx a ∈ Idx) :
    (mkIndSignature₃ Idx cs).toIndSignature₂.WF where
  resIdx_mem := by
    intro W q hq a ha
    obtain ⟨k, hk, rfl⟩ := (mem_ofNat_iff cs.length q).1 hq
    have hc : cs[k]? = some cs[k] := List.getElem?_eq_getElem hk
    have hfld : (mkIndSignature₃ Idx cs).Fld W ((k : ℕ) : V) = cs[k].flds W := by
      show tagCaseSnd 0 (cs.map (·.flds)) W ((k : ℕ) : V) = _
      have hat := tagCaseSnd_at (V := V) 0 (cs.map (·.flds)) k (cs[k].flds)
        (by rw [List.getElem?_map, hc]; rfl) W
      simpa using hat
    have hres : (mkIndSignature₃ Idx cs).resIdx ((k : ℕ) : V) a = cs[k].resIdx a := by
      show tagCase₂ 0 (cs.map fun c ↦ fun _ a ↦ c.resIdx a) ((k : ℕ) : V) a = _
      have hat := tagCase₂_at (V := V) 0 (cs.map fun c ↦ fun _ a ↦ c.resIdx a) k
        (fun _ a ↦ cs[k].resIdx a) (by rw [List.getElem?_map, hc]; rfl) a
      simpa using hat
    rw [hres]
    exact h cs[k] (List.getElem_mem hk) W a (by rwa [hfld] at ha)

/-- **`interpSig_stage`, at the assembly level.** -/
theorem mkIndSignature₃_stage {k Idx : V} {cs : List (CtorData₃ V)}
    (hIdx : Idx ∈ vsetV k) (hQ : ((cs.length : ℕ) : V) ∈ vsetV k)
    (hfld : ∀ c ∈ cs, ∀ W : V, c.flds W ∈ vsetV k)
    (hpos : ∀ c ∈ cs, ∀ a : V, tagUnionF 0 c.poss a ∈ vsetV k) :
    IsStageSignature₂ k (mkIndSignature₃ Idx cs).toIndSignature₂ where
  idx_mem := hIdx
  q_mem := hQ
  fld_mem := by
    intro W _ q hq
    obtain ⟨j, hj, rfl⟩ := (mem_ofNat_iff cs.length q).1 hq
    have hc : cs[j]? = some cs[j] := List.getElem?_eq_getElem hj
    have hat := tagCaseSnd_at (V := V) 0 (cs.map (·.flds)) j (cs[j].flds)
      (by rw [List.getElem?_map, hc]; rfl) W
    show tagCaseSnd 0 (cs.map (·.flds)) W ((j : ℕ) : V) ∈ vsetV k
    rw [show ((j : ℕ) : V) = ((0 + j : ℕ) : V) from by norm_num, hat]
    exact hfld cs[j] (List.getElem_mem hj) W
  pos_mem := by
    intro W _ q hq a _
    obtain ⟨j, hj, rfl⟩ := (mem_ofNat_iff cs.length q).1 hq
    have hc : cs[j]? = some cs[j] := List.getElem?_eq_getElem hj
    have hat := tagCase₂_at (V := V) 0 (cs.map fun c ↦ fun _ a ↦ tagUnionF 0 c.poss a) j
      (fun _ a ↦ tagUnionF 0 cs[j].poss a) (by rw [List.getElem?_map, hc]; rfl) a
    show tagCase₂ 0 (cs.map fun c ↦ fun _ a ↦ tagUnionF 0 c.poss a) ((j : ℕ) : V) a ∈ vsetV k
    rw [show ((j : ℕ) : V) = ((0 + j : ℕ) : V) from by norm_num, hat]
    exact hpos cs[j] (List.getElem_mem hj) a

/-! ## The `OracleOK` connection: the `.induct` step, assembled

The last `.induct` piece that does not need the translation.  Everything here is
about *shape*: given the per-constant and per-rule obligations in the wrapped
form the model produces, this is the step `VEnv.WF'`'s induction consumes.

**The staging mismatch, and why it is not a problem.**  `VEnv.addInduct'` adds
the block in three `addConstList` steps — types, constructors, recursors — while
`cnstOf`'s `.induct` line performs a single `oracleExtend o D.allNames`.  Chained
naively, each intermediate `OracleOK` would be stated at a *partial* assignment
(the type formers' obligation where the constructors are unassigned), needing
`interp_cnst_congr` to move.  `addConstList_append` collapses the three into one
`addConstList D.allConsts`, so **every obligation is stated at the one assignment
`cnstOf` actually produces**, and `oracleExtend_append` reconciles the names. -/

section InductStep

variable {envF : VEnv} {nv : ℕ} {L : PropSplit envF nv} {κ : ℕ → V} {ls : List ℕ}

/-- `addInduct'` is one constant-list extension followed by the ι-rules.

Stated in the direction the outer induction uses it: it will have `addInduct'`
in hand and need the collapsed form. -/
theorem addConstList_allConsts {env e₃ : VEnv} {D : VInductDecl'}
    {e₁ e₂ : VEnv}
    (h1 : env.addConstList D.typeConsts = some e₁)
    (h2 : e₁.addConstList D.ctorConsts = some e₂)
    (h3 : e₂.addConstList D.recConsts = some e₃) :
    env.addConstList D.allConsts = some e₃ := by
  rw [show D.allConsts = D.typeConsts ++ (D.ctorConsts ++ D.recConsts) from by
    simp [VInductDecl'.allConsts, List.append_assoc]]
  exact (addConstList_append _ _).2 ⟨e₁, h1, (addConstList_append _ _).2 ⟨e₂, h2, h3⟩⟩

/-- **The `.induct` coherence step.**  The constants and the ι-rules, in the
shape `VEnv.WF'`'s induction consumes, with every obligation `Above`-wrapped and
stated at the single assignment `cnstOf` produces. -/
theorem coherentOn_addInduct (L : PropSplit envF nv) (o : Name → List VLevel → V)
    (D : VInductDecl') {env e₁ : VEnv} {c c' : Name → List VLevel → V}
    (hc' : c' = oracleExtend o D.allNames c)
    (hcl : env.ConstsClosed) (hC : CoherentOn ⟨κ, ls, c⟩ L env)
    (hadd : env.addConstList D.allConsts = some e₁)
    (hocc : ∀ p ∈ D.allConsts, p.2.type.ConstsIn env.contains)
    (hok : ∀ p ∈ D.allConsts, OracleOK L κ ls o c' p.1 p.2)
    (hrules : ∀ df ∈ D.iotaRules, ∀ {us : List VLevel}, (∀ l ∈ us, l.WF nv) →
      us.length = df.uvars →
      Above (V := V) ⟨κ, ls, c'⟩
          ((interp ⟨κ, ls, c'⟩ L [] (df.lhs.instL us)).toFun ∅
            = (interp ⟨κ, ls, c'⟩ L [] (df.rhs.instL us)).toFun ∅) ∧
        Above (V := V) ⟨κ, ls, c'⟩
          ((interp ⟨κ, ls, c'⟩ L [] (df.lhs.instL us)).toFun ∅
            ∈ (interp ⟨κ, ls, c'⟩ L [] (df.type.instL us)).toFun ∅)) :
    CoherentOn ⟨κ, ls, c'⟩ L (e₁.addIndRules D) := by
  subst hc'
  exact coherentOn_addDefEqFold D.iotaRules
    (coherentOn_addConstList L o D.allConsts hcl hC hadd hocc hok) hrules

end InductStep

end Lean4Lean.SetModel







