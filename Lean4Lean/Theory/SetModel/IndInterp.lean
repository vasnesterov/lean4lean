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

variable {envF : VEnv} {nv : ℕ} {M : ModelData V} {L : LevelAssign envF nv}

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

end Lean4Lean.SetModel


