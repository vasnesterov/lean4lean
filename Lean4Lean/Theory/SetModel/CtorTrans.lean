import Lean4Lean.Theory.SetModel.IndInterp

/-!
# The `VIndCtor → CtorData₃` translation

The last `.induct` piece: read the per-constructor data of
`Theory/Inductive/Decl.lean`'s record off as an `IndSignature₃`.

## The design, and why it is not the one the ledger last recorded

`SetModel/IndInterp.lean`'s port supplies `Args W q`, a signature-chosen set of
admissible pairs `⟨a, f⟩ₖ`.  With it in hand there are two ways to lay out a
constructor's data, and the choice decides which syntactic side conditions the
translation needs:

* **fillers in `a`** — `a` is a valuation of the *whole* field telescope,
  recursive slots included, and `Args` says the recursive slots agree with the
  curried `f`;
* **fillers out of `a`** — `a` blanks the recursive slots, and `Fld` justifies
  the non-recursive entries by an existential over fillers.

The second is what `docs/soundness-ledger.md` recorded, and it does not close:
`Pos q a` is not the only component evaluated at `a`.  **`posIdx q a b` is
`⟦r.args⟧` and `resIdx q a` is `⟦C.args⟧`, and both live over a context
containing the recursive fields.**  Blanking those slots therefore needs the
independence clause at *three* sites, not one, and only the first
(`VIndField.WF.binders_indep`, for `r.binders`) exists.

The first layout needs **no** independence clause anywhere: every component is
evaluated at a valuation carrying the genuine values.  The ledger rejects it on
the ground that `IsSubsingletonSignature.fld_det` — "the non-recursive data is
determined by the result index" — becomes false.  That is a fact about
`fld_det`'s *statement*, not about `Ind_subsingleton`'s truth: with `Args` in
place the family holds exactly the elements it held before, only with `a`
carrying a copy of `f`'s data, so the subsingleton theorem survives with
`fld_det` restated to quantify over admissible pairs.  `Ind₃_subsingleton`
below is that restatement, proved, and it is the reason this file takes the
first layout.

What the two layouts really trade is *where* the independence facts are spent:
blanking needs them for **every** declaration, at `posIdx` and `resIdx`;
carrying needs them only for a **large-eliminating subsingleton**, as the
`pos_det`/`posIdx_det` fields of `IsSubsingletonSignature₃`.  That is strictly
less, and it is why this file is not blocked where the ledger predicted.

## What `Fld` may over-approximate

A recursive slot of `a` need not be constrained by `Fld` at all beyond being a
function into the carrier: `Args` pins it to the curried `f`, and `indStep₃`'s
own `hrec` conjunct constrains `f`.  So the recursive entries use the plain
function set `Dcar ^ Pos`, which is independent of the approximation `W` —
whence `Fld` and `Args` are *constant* in `W` here and both monotonicity
obligations are trivial.  The approximation-indexing that `IndSignature₂`
introduced is still needed in general; this particular translation does not
spend it.

## Parser hazard, recorded where it bit

`e[k]?` **does not parse when `e` ends in `)`** anywhere Foundation is
imported: `Foundation/FirstOrder/Basic/BinderNotation.lean` declares a syntax
whose token list contains `")["`, so the tokenizer produces a single `)[` token.
The error is

```
unexpected token ')['; expected ')', ',' or ':'
```

which reads as a *binder-group* complaint and points nowhere near the cause —
adding a second layer of parentheses does not help, and the same line parses
fine in a file that does not import Foundation.  Write `getElem? e k` instead.
This belongs next to `docs/foundation-gaps.md`'s other entries; it is recorded
here because that file is not this stream's.
-/

namespace Lean4Lean.SetModel

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open scoped Classical

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]

/-! ## Prefixes of a valuation

`Pos q a` must evaluate `⟦ξ⟧`, which lives over the context of *field `i`*,
while `a` is a valuation of the whole field telescope.  The two differ in
length, and `interp` is length-sensitive — it appends at `|Γ|`, so a longer
valuation would place the `ξ`-binders at the wrong positions.  The prefix is
therefore taken explicitly.

**No new primitive is needed**: Foundation's `restrict` is exactly this
operation on the `snoc`-sequence encoding, and it is already definable. -/

section Prefix

theorem ofNat_subset_ofNat {m n : ℕ} (h : m ≤ n) : ((m : ℕ) : V) ⊆ ((n : ℕ) : V) := by
  intro q hq
  obtain ⟨k, hk, rfl⟩ := (mem_ofNat_iff m q).1 hq
  exact (mem_ofNat_iff n _).2 ⟨k, by omega, rfl⟩

theorem ofNat_inter_ofNat {m n : ℕ} (h : m ≤ n) :
    (((n : ℕ) : V) ∩ ((m : ℕ) : V) : V) = ((m : ℕ) : V) := by
  ext q
  rw [mem_inter_iff]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨ofNat_subset_ofNat (V := V) ‹m ≤ n› _ h, h⟩⟩

/-- Restricting a sequence to its own length is the identity. -/
theorem IsSeq.restrict_self {ρ : V} {n : ℕ} (h : IsSeq ρ n) : (ρ ↾ ((n : ℕ) : V)) = ρ :=
  haveI : IsFunction ρ := h.1
  IsFunction.restrict_eq_self ρ _ (by rw [h.2])

/-- Restricting away the last entry. -/
theorem IsSeq.restrict_snoc {ρ v : V} {n : ℕ} (h : IsSeq ρ n) :
    ((snoc ρ v) ↾ ((n : ℕ) : V)) = ρ := by
  haveI : IsFunction ρ := h.1
  have hdom : domain ρ = ((n : ℕ) : V) := h.2
  ext p
  rw [mem_restrict_iff]
  constructor
  · rintro ⟨hp, x, hx, y, rfl⟩
    rcases mem_snoc_iff.1 hp with he | hp'
    · rw [hdom] at he
      rcases kpair_inj he with ⟨rfl, rfl⟩
      exact absurd hx (mem_irrefl _)
    · exact hp'
  · intro hp
    refine ⟨mem_snoc_iff.2 (Or.inr hp), ?_⟩
    obtain ⟨x, y, rfl⟩ := IsFunction.mem_eq_kpair hp
    exact ⟨x, by rw [← hdom]; exact mem_domain_of_kpair_mem hp, y, rfl⟩

/-- Restricting below the length ignores the last entry. -/
theorem IsSeq.restrict_snoc_le {ρ v : V} {n m : ℕ} (h : IsSeq ρ n) (hm : m ≤ n) :
    ((snoc ρ v) ↾ ((m : ℕ) : V)) = (ρ ↾ ((m : ℕ) : V)) := by
  rw [show ((snoc ρ v) ↾ ((m : ℕ) : V))
      = (((snoc ρ v) ↾ ((n : ℕ) : V)) ↾ ((m : ℕ) : V)) from by
    rw [restrict_restrict_eq_restrict_inter, ofNat_inter_ofNat hm]]
  rw [h.restrict_snoc]

/-- **A telescope element restricts to its base valuation.**  This is what makes
`Pos q a` well defined: the `ξ` of field `i` is evaluated at `a ↾ (np + i)`,
which is exactly the valuation the telescope had built when it chose the field's
domain. -/
theorem teleFun_restrict_le : ∀ (Gs : List (DefFun V)) {ρ σ : V} {n m : ℕ},
    IsSeq ρ n → σ ∈ (teleFun Gs).toFun ρ → m ≤ n →
      (σ ↾ ((m : ℕ) : V)) = (ρ ↾ ((m : ℕ) : V))
  | [], _, _, _, _, _, hσ, _ => by rw [mem_teleFun_nil] at hσ; subst hσ; rfl
  | G :: Gs, ρ, σ, n, m, hρ, hσ, hm => by
    obtain ⟨x, -, hx⟩ := mem_teleFun_cons.1 hσ
    rw [teleFun_restrict_le Gs (n := n + 1) hρ.snoc' hx (by omega), hρ.restrict_snoc_le hm]

theorem teleFun_restrict (Gs : List (DefFun V)) {ρ σ : V} {n : ℕ}
    (hρ : IsSeq ρ n) (hσ : σ ∈ (teleFun Gs).toFun ρ) : (σ ↾ ((n : ℕ) : V)) = ρ := by
  rw [teleFun_restrict_le Gs hρ hσ (le_refl n), hρ.restrict_self]

/-- **A telescope element's `i`-th entry lies in the `i`-th domain**, evaluated
at the prefix that domain was chosen at.  Together with `teleFun_restrict` this
is what ties `Fld`'s recursive slots to `Pos`. -/
theorem teleFun_slot : ∀ (Gs : List (DefFun V)) {ρ σ : V} {n i : ℕ} {G : DefFun V},
    IsSeq ρ n → σ ∈ (teleFun Gs).toFun ρ → Gs[i]? = some G →
      σ ‘ ((n + i : ℕ) : V) ∈ G.toFun (σ ↾ ((n + i : ℕ) : V))
  | [], _, _, _, i, _, _, _, hG => by simp at hG
  | G' :: Gs, ρ, σ, n, 0, G, hρ, hσ, hG => by
    have hGG : G' = G := by simpa using hG
    subst hGG
    obtain ⟨x, hx, hσ'⟩ := mem_teleFun_cons.1 hσ
    have h1 : σ ‘ ((n : ℕ) : V) = x := by
      rw [teleFun_read Gs (n := n + 1) (j := n) hρ.snoc' hσ' (by omega), hρ.read_top]
    have h2 : (σ ↾ ((n : ℕ) : V)) = ρ := by
      rw [teleFun_restrict_le Gs (n := n + 1) hρ.snoc' hσ' (by omega), hρ.restrict_snoc_le
        (le_refl n), hρ.restrict_self]
    rw [Nat.add_zero, h1, h2]
    exact hx
  | G' :: Gs, ρ, σ, n, i + 1, G, hρ, hσ, hG => by
    obtain ⟨x, -, hσ'⟩ := mem_teleFun_cons.1 hσ
    have ih := teleFun_slot Gs (n := n + 1) (i := i) hρ.snoc' hσ' (by simpa using hG)
    rwa [show n + 1 + i = n + (i + 1) from by omega] at ih

end Prefix

/-! ## The design check: subsingletons survive fillers in `a`

`docs/soundness-ledger.md` rules out putting the recursive fillers into `a` on
the ground that `IsSubsingletonSignature.fld_det` becomes false, and names the
family it kills: `Acc`, a large-eliminating subsingleton with a recursive field.

**The objection is about `fld_det`'s statement, not about the theorem.**  With
`Args` forcing the copies to agree with `f`, the family holds exactly the
elements it held before; what changes is that `a` is no longer determined by the
result index *alone* — it is determined by the index **and `f`**.  So the
hypothesis is restated to quantify over admissible pairs, and the two
determinacy facts the proof also needs (`Pos` and `posIdx` at equal result
indices) become fields as well.

`Ind₃_subsingleton` below is `Ind_subsingleton`'s proof with the pinning order
kept: the *domains* are pinned first, then `f` by the rank induction hypothesis,
then `a`.  It is the port of the one theorem the layout decision turns on, and
it goes through. -/

section Subsingleton

variable {S : IndSignature₃ V} {D R : V} {e : V → V → V → V → V}

/-- **No junk**, ported: every element of the family is a constructor
application, with the admissibility conjunct. -/
theorem mem_Ind₃_iff (hWF : S.toIndSignature₂.WF) (hD : IsIndCarrier₃ S D) {p : V} :
    p ∈ Ind₃ S D ↔ ∃ q ∈ S.Q, ∃ a ∈ S.Fld (Ind₃ S D) q, ∃ f ∈ (D ^ S.Pos q a : V),
      (⟨a, f⟩ₖ : V) ∈ S.Args (Ind₃ S D) q ∧
      (∀ b ∈ S.Pos q a, (⟨S.posIdx q a b, f ‘ b⟩ₖ : V) ∈ Ind₃ S D) ∧
      p = indCtor₃ S q a f := by
  conv_lhs => rw [← indStep₃_Ind₃ (S := S) (D := D)]
  exact mem_indStep₃_iff_of_carrier hWF hD

/-- The subsingleton condition, restated for the ported signature.  Each field
is the old one with `a` allowed to carry the fillers: what the result index
determines is the *domains*, and `a` itself is determined by the index together
with `f`. -/
structure IsSubsingletonSignature₃ (S : IndSignature₃ V) (D : V) : Prop where
  single : ∀ q ∈ S.Q, ∀ q' ∈ S.Q, q = q'
  pos_det : ∀ q ∈ S.Q, ∀ a ∈ S.Fld (Ind₃ S D) q, ∀ a' ∈ S.Fld (Ind₃ S D) q,
    S.resIdx q a = S.resIdx q a' → S.Pos q a = S.Pos q a'
  posIdx_det : ∀ q ∈ S.Q, ∀ a ∈ S.Fld (Ind₃ S D) q, ∀ a' ∈ S.Fld (Ind₃ S D) q,
    S.resIdx q a = S.resIdx q a' → ∀ b, S.posIdx q a b = S.posIdx q a' b
  fld_det : ∀ q ∈ S.Q, ∀ a ∈ S.Fld (Ind₃ S D) q, ∀ a' ∈ S.Fld (Ind₃ S D) q, ∀ f f' : V,
    (⟨a, f⟩ₖ : V) ∈ S.Args (Ind₃ S D) q → (⟨a', f'⟩ₖ : V) ∈ S.Args (Ind₃ S D) q →
    S.resIdx q a = S.resIdx q a' → f = f' → a = a'

/-- **The fixed point is a subsingleton at every index**, in the ported theory.
The proof is `Ind_subsingleton`'s with the pinning order preserved. -/
theorem Ind₃_subsingleton (hWF : S.toIndSignature₂.WF) (hD : IsIndCarrier₃ S D)
    (hSub : IsSubsingletonSignature₃ S D) :
    ∀ x i y : V, (⟨i, x⟩ₖ : V) ∈ Ind₃ S D → (⟨i, y⟩ₖ : V) ∈ Ind₃ S D → x = y := by
  refine rank_induction (fun x ↦ ∀ i y : V,
    (⟨i, x⟩ₖ : V) ∈ Ind₃ S D → (⟨i, y⟩ₖ : V) ∈ Ind₃ S D → x = y) (by definability) ?_
  intro x ih i y hx hy
  obtain ⟨q, hq, a, ha, f, hf, hok, hrec, hex⟩ := (mem_Ind₃_iff hWF hD).mp hx
  obtain ⟨q', hq', a', ha', f', hf', hok', hrec', hey⟩ := (mem_Ind₃_iff hWF hD).mp hy
  obtain ⟨hi, hxv⟩ := kpair_inj hex
  obtain ⟨hi', hyv⟩ := kpair_inj hey
  rcases hSub.single q' hq' q hq
  have hres : S.resIdx q a = S.resIdx q a' := by rw [← hi, ← hi']
  have hpos : S.Pos q a = S.Pos q a' := hSub.pos_det q hq a ha a' ha' hres
  have hff : f = f' := by
    refine function_ext hf (hpos ▸ hf') fun b hb z hz hzf ↦ ?_
    have hfun : IsFunction f := IsFunction.of_mem hf
    have hval : f ‘ b = z := value_eq_of_kpair_mem hzf
    have hrk : rank (f ‘ b) < rank x := by
      rw [hxv]; exact rank_lt_indCtorVal (kpair_value_mem hf hb)
    have hb' : b ∈ S.Pos q a' := hpos ▸ hb
    have hrec2 := hrec' b hb'
    rw [← hSub.posIdx_det q hq a ha a' ha' hres b] at hrec2
    have := ih (f ‘ b) hrk (S.posIdx q a b) (f' ‘ b) (hrec b hb) hrec2
    rw [hval] at this
    rw [this]
    exact kpair_value_mem hf' hb'
  have haa : a = a' := hSub.fld_det q hq a ha a' ha' f f' hok hok' hres hff
  rw [hxv, hyv, haa, hff]

/-- **Large elimination is sound for a subsingleton family**, ported: the
recursor's value depends only on the index. -/
theorem indRec₃_indep_of_proof (hWF : S.toIndSignature₂.WF) (hD : IsIndCarrier₃ S D)
    (hSub : IsSubsingletonSignature₃ S D) {he : ℒₛₑₜ-function₄[V] e} {i x y : V}
    (hx : (⟨i, x⟩ₖ : V) ∈ Ind₃ S D) (hy : (⟨i, y⟩ₖ : V) ∈ Ind₃ S D) :
    indRec₃ S D R e he (⟨i, x⟩ₖ) = indRec₃ S D R e he (⟨i, y⟩ₖ) := by
  rw [Ind₃_subsingleton hWF hD hSub x i y hx hy]

end Subsingleton

/-! ## The per-constructor data -/

section Ctor

variable {envF : VEnv} {nv : ℕ} (M : ModelData V) (L : LevelAssign envF nv)
variable (D : VInductDecl')

/-- The context of field `i` of a constructor: the parameters and the *stored*
types of the earlier fields, innermost first.  This is exactly the context
`VIndCtor.WF.fields` types field `i` in. -/
def fldCtx (C : VIndCtor) (i : ℕ) : List VExpr :=
  ((C.fields.take i).map (·.type)).reverse ++ D.params.reverse

theorem fldCtx_length (C : VIndCtor) {i : ℕ} (hi : i ≤ C.fields.length) :
    (fldCtx D C i).length = D.np + i := by
  simp [fldCtx, VInductDecl'.np, Nat.min_eq_left hi, Nat.add_comm]

/-- The one hypothesis the translation's lemmas take about the parameter
valuation, and it is free: every element of `⟦params⟧` is a sequence of length
`np`. -/
theorem isSeq_params {params : V} (h : params ∈ interpCtx M L D.params.reverse) :
    IsSeq params D.np := by
  obtain ⟨hf, hd⟩ := interpCtx_domain M L h
  exact ⟨hf, by simpa using hd⟩

/-- **The domain of one field slot.**

* a non-recursive field contributes `⟦A⟧`, for the block-free `A` that
  `VIndField.WF.pos` supplies — the stored type mentions the block, whose value
  is what this whole construction is defining;
* a recursive field contributes the plain function set `Dcar ^ ⟦ξ⟧`.  It need
  not be constrained further: `Args` pins the slot to the curried `f`, and
  `indStep₃`'s own conjunct constrains `f`.  This is why nothing here depends on
  the approximation `W`. -/
noncomputable def fldDom (Dcar : V) (Γ : List VExpr) (Anr : VExpr) (F : VIndField) :
    DefFun V :=
  match F.recArg with
  | none => interp M L Γ Anr
  | some r =>
    ⟨fun σ ↦ (Dcar ^ (teleFun (teleDomains M L Γ r.binders)).toFun σ : V), by
      have := (teleFun (teleDomains M L Γ r.binders)).definable
      definability⟩

/-- The whole field telescope, in declaration order.  `A i` is the block-free
replacement for field `i`'s type; it is read only at non-recursive fields. -/
noncomputable def fldDoms (Dcar : V) (A : ℕ → VExpr) :
    List VExpr → ℕ → List VIndField → List (DefFun V)
  | _, _, [] => []
  | Γ, i, F :: Fs => fldDom M L Dcar Γ (A i) F :: fldDoms Dcar A (F.type :: Γ) (i + 1) Fs

theorem fldDoms_length (Dcar : V) (A : ℕ → VExpr) :
    ∀ (Γ : List VExpr) (i : ℕ) (Fs : List VIndField),
      (fldDoms M L Dcar A Γ i Fs).length = Fs.length
  | _, _, [] => rfl
  | Γ, i, F :: Fs => by
    show (fldDoms M L Dcar A (F.type :: Γ) (i + 1) Fs).length + 1 = Fs.length + 1
    rw [fldDoms_length]

/-- The entry at a field position really is that field's domain, in that field's
own context. -/
theorem fldDoms_getElem? (Dcar : V) (A : ℕ → VExpr) :
    ∀ (Γ : List VExpr) (i k : ℕ) (Fs : List VIndField) (F : VIndField), Fs[k]? = some F →
      getElem? (fldDoms M L Dcar A Γ i Fs) k =
        some (fldDom M L Dcar (((Fs.take k).map (·.type)).reverse ++ Γ) (A (i + k)) F)
  | _, _, _, [], _, h => by simp at h
  | Γ, i, 0, F' :: Fs, F, h => by
    have : F' = F := by simpa using h
    subst this
    simp [fldDoms]
  | Γ, i, k + 1, F' :: Fs, F, h => by
    have ih := fldDoms_getElem? Dcar A (F'.type :: Γ) (i + 1) k Fs F (by simpa using h)
    rw [show i + 1 + k = i + (k + 1) from by omega] at ih
    simpa [fldDoms, List.append_assoc] using ih

/-- **`Fld`.**  The set of full field valuations, extending the parameters. -/
noncomputable def ctorFldSet (Dcar : V) (A : ℕ → VExpr) (params : V) (C : VIndCtor) : V :=
  (teleFun (fldDoms M L Dcar A D.params.reverse 0 C.fields)).toFun params

/-- **The `Pos` summands with their slots.**  One entry per recursive field:
the absolute position of that field in a valuation, and the `ξ`-telescope of the
field evaluated at the prefix of `a` that field's context sees.

The two are kept together because `Args` has to compare them: the summand types
the filler, and the slot is where `a`'s copy of it sits. -/
noncomputable def slotDoms (C : VIndCtor) : List (ℕ × (V → V)) :=
  C.recFields.map fun p ↦ (D.np + p.1, fun a ↦
    (teleFun (teleDomains M L (fldCtx D C p.1) p.2.binders)).toFun
      (a ↾ ((D.np + p.1 : ℕ) : V)))

noncomputable def posDoms (C : VIndCtor) : List (V → V) :=
  (slotDoms M L D C).map (·.2)

theorem posDoms_definable (C : VIndCtor) :
    ∀ P ∈ posDoms M L D C, ℒₛₑₜ-function₁[V] P := by
  intro P hP
  obtain ⟨p', hp', rfl⟩ := List.mem_map.1 hP
  obtain ⟨p, -, rfl⟩ := List.mem_map.1 hp'
  have h1 := (teleFun (teleDomains M L (fldCtx D C p.1) p.2.binders)).definable
  have h2 : ℒₛₑₜ-function₁[V] (fun a : V ↦ (a ↾ ((D.np + p.1 : ℕ) : V))) := by definability
  definability

/-- **The `posIdx` entries.**  The recursive occurrence's index tuple: the
summand tag `r.idx` of the block, together with `⟦π⟧` evaluated at the position,
which is a valuation of `ξ.reverse ++ (field context)`. -/
noncomputable def posIdxVals (params : V) (C : VIndCtor) : List (V → V → V) :=
  C.recFields.map fun p ↦ fun _a x ↦
    (⟨((p.2.idx : ℕ) : V),
      argsVal M L (p.2.binders.reverse ++ fldCtx D C p.1) p.2.args x params⟩ₖ : V)

theorem posIdxVals_definable (params : V) (C : VIndCtor) :
    ∀ P ∈ posIdxVals M L D params C, ℒₛₑₜ-function₂[V] P := by
  intro P hP
  obtain ⟨p, -, rfl⟩ := List.mem_map.1 hP
  have h1 := argsVal_definable M L (p.2.binders.reverse ++ fldCtx D C p.1) p.2.args
  have h2 : ℒₛₑₜ-function₁[V] (fun x : V ↦
      argsVal M L (p.2.binders.reverse ++ fldCtx D C p.1) p.2.args x params) := by
    definability
  definability

/-- **`resIdx`.**  The constructor's result index tuple, tagged with the block
member it constructs. -/
noncomputable def resIdxVal (params : V) (j : ℕ) (C : VIndCtor) : V → V :=
  fun a ↦ (⟨((j : ℕ) : V),
    argsVal M L ((C.fields.map (·.type)).reverse ++ D.params.reverse) C.args a params⟩ₖ : V)

theorem resIdxVal_definable (params : V) (j : ℕ) (C : VIndCtor) :
    ℒₛₑₜ-function₁[V] (resIdxVal M L D params j C) := by
  have h1 := argsVal_definable M L ((C.fields.map (·.type)).reverse ++ D.params.reverse) C.args
  have h2 : ℒₛₑₜ-function₁[V] (fun a : V ↦
      argsVal M L ((C.fields.map (·.type)).reverse ++ D.params.reverse) C.args a params) := by
    definability
  unfold resIdxVal
  definability

/-! ### `Args`

The whole content of the port, at this translation: the recursive slots of `a`
are *exactly* the curried components of `f`.  Stated as an agreement of values
rather than as a set equation, so that it is a first-order condition on
`⟨a, f⟩ₖ` and needs no `repl`. -/

/-- **The admissibility condition.**  For each recursive field: `a`'s slot holds
a function on that field's positions, and it agrees with `f` on the
correspondingly tagged summand.  `s` counts the summands, matching
`tagUnionF 0`'s tags. -/
def argCond (Dcar : V) : ℕ → List (ℕ × (V → V)) → V → V → Prop
  | _, [], _, _ => True
  | s, p :: rest, a, f =>
    (a ‘ ((p.1 : ℕ) : V)) ∈ (Dcar ^ p.2 a : V) ∧
    (∀ x ∈ p.2 a, (a ‘ ((p.1 : ℕ) : V)) ‘ x = f ‘ (⟨((s : ℕ) : V), x⟩ₖ : V)) ∧
    argCond Dcar (s + 1) rest a f

theorem argCond_definable (Dcar : V) : ∀ (s : ℕ) (l : List (ℕ × (V → V))),
    (∀ p ∈ l, ℒₛₑₜ-function₁[V] p.2) → ℒₛₑₜ-relation[V] (argCond (V := V) Dcar s l)
  | s, [], _ => by
    have h0 : argCond (V := V) Dcar s [] = fun _ _ ↦ True := rfl
    rw [h0]; definability
  | s, p :: rest, h => by
    have hp := h p (.head _)
    have hrest := argCond_definable Dcar (s + 1) rest fun r hr ↦ h r (.tail _ hr)
    have h0 : argCond (V := V) Dcar s (p :: rest) = fun a f ↦
        (a ‘ ((p.1 : ℕ) : V)) ∈ (Dcar ^ p.2 a : V) ∧
        (∀ x ∈ p.2 a, (a ‘ ((p.1 : ℕ) : V)) ‘ x = f ‘ (⟨((s : ℕ) : V), x⟩ₖ : V)) ∧
        argCond Dcar (s + 1) rest a f := rfl
    rw [h0]; definability

/-- A set containing every pair the condition could accept. -/
noncomputable def argBound (Dcar Fld : V) (Pos : V → V)
    (hPos : ℒₛₑₜ-function₁[V] Pos) : V :=
  mkFamUnion (fun _ ↦ Fld) (by definability)
    (fun _ a ↦ (({a} : V) ×ˢ (Dcar ^ Pos a : V))) (by definability) ∅

theorem mem_argBound_iff {Dcar Fld : V} {Pos : V → V} {hPos : ℒₛₑₜ-function₁[V] Pos}
    {p : V} : p ∈ argBound Dcar Fld Pos hPos ↔
      ∃ a ∈ Fld, ∃ f ∈ (Dcar ^ Pos a : V), p = (⟨a, f⟩ₖ : V) := by
  rw [argBound, mem_mkFamUnion_iff]
  refine exists_congr fun a ↦ and_congr_right fun _ ↦ ?_
  rw [mem_prod_iff]
  exact ⟨fun ⟨x, hx, f, hf, he⟩ ↦ ⟨f, hf, by rw [he, mem_singleton_iff.1 hx]⟩,
    fun ⟨f, hf, he⟩ ↦ ⟨_, mem_singleton_iff.2 rfl, f, hf, he⟩⟩

/-- **`Args`.** -/
noncomputable def argSet (Dcar Fld : V) (Pos : V → V) (hPos : ℒₛₑₜ-function₁[V] Pos)
    (l : List (ℕ × (V → V))) (hl : ∀ p ∈ l, ℒₛₑₜ-function₁[V] p.2) : V :=
  sep (argBound Dcar Fld Pos hPos)
    (fun p ↦ ∀ a f : V, p = (⟨a, f⟩ₖ : V) → argCond Dcar 0 l a f)
    (by have := argCond_definable (V := V) Dcar 0 l hl; definability)

theorem mem_argSet_iff {Dcar Fld : V} {Pos : V → V} {hPos : ℒₛₑₜ-function₁[V] Pos}
    {l : List (ℕ × (V → V))} {hl : ∀ p ∈ l, ℒₛₑₜ-function₁[V] p.2} {a f : V} :
    (⟨a, f⟩ₖ : V) ∈ argSet Dcar Fld Pos hPos l hl ↔
      (a ∈ Fld ∧ f ∈ (Dcar ^ Pos a : V) ∧ argCond Dcar 0 l a f) := by
  rw [argSet, mem_sep_iff, mem_argBound_iff]
  constructor
  · rintro ⟨⟨a', ha', f', hf', he⟩, hcond⟩
    obtain ⟨rfl, rfl⟩ := kpair_inj he
    exact ⟨ha', hf', hcond a f rfl⟩
  · rintro ⟨ha, hf, hcond⟩
    exact ⟨⟨a, ha, f, hf, rfl⟩, fun a' f' he ↦ by
      obtain ⟨rfl, rfl⟩ := kpair_inj he; exact hcond⟩

/-- **Reading one field's agreement back out of the condition.**  This is what a
consumer — the constructor's typing obligation, and the ι-rule — needs: the
recursive field's value *is* the curried component of `f`. -/
theorem argCond_at {Dcar a f : V} : ∀ (l : List (ℕ × (V → V))) (s k : ℕ)
    (p : ℕ × (V → V)), argCond Dcar s l a f → l[k]? = some p →
    (a ‘ ((p.1 : ℕ) : V)) ∈ (Dcar ^ p.2 a : V) ∧
    ∀ x ∈ p.2 a, (a ‘ ((p.1 : ℕ) : V)) ‘ x = f ‘ (⟨((s + k : ℕ) : V), x⟩ₖ : V)
  | [], _, k, _, _, hk => by simp at hk
  | p' :: l, s, 0, p, h, hk => by
    have : p' = p := by simpa using hk
    subst this
    exact ⟨h.1, by simpa using h.2.1⟩
  | p' :: l, s, k + 1, p, h, hk => by
    have ih := argCond_at l (s + 1) k p h.2.2 (by simpa using hk)
    rwa [show s + 1 + k = s + (k + 1) from by omega] at ih

/-! ### The joint: `Fld`'s recursive slots really are `Pos`-indexed functions

This is the one place where the two halves of the design have to meet, and it
is what the layout question turns on.  `Fld` chooses a recursive slot's domain
at the *prefix* valuation the telescope had built when it got there; `Pos`
evaluates the same `ξ` at the *finished* valuation restricted back to that
prefix.  `teleFun_restrict` says the two prefixes are the same set, and
`teleFun_slot` says the entry lies in the domain — so `argCond`'s first
conjunct is not a constraint the translation has to arrange, it holds of every
element of `Fld`. -/

theorem fldDom_rec {Dcar : V} {Γ : List VExpr} {Anr : VExpr} {F : VIndField}
    {r : VIndRecArg} (hr : F.recArg = some r) :
    (fldDom M L Dcar Γ Anr F).toFun =
      fun σ ↦ (Dcar ^ (teleFun (teleDomains M L Γ r.binders)).toFun σ : V) := by
  simp only [fldDom, hr]

theorem fldSlot_mem {Dcar params a : V} {A : ℕ → VExpr} {C : VIndCtor} {i : ℕ}
    {F : VIndField} {r : VIndRecArg}
    (hp : IsSeq params D.np) (ha : a ∈ ctorFldSet M L D Dcar A params C)
    (hF : C.fields[i]? = some F) (hr : F.recArg = some r) :
    a ‘ ((D.np + i : ℕ) : V) ∈
      (Dcar ^ (teleFun (teleDomains M L (fldCtx D C i) r.binders)).toFun
        (a ↾ ((D.np + i : ℕ) : V)) : V) := by
  have hG := fldDoms_getElem? M L Dcar A D.params.reverse 0 i C.fields F hF
  rw [Nat.zero_add] at hG
  have hslot := teleFun_slot (fldDoms M L Dcar A D.params.reverse 0 C.fields)
    (n := D.np) (i := i) hp ha hG
  rwa [show (((C.fields.take i).map (·.type)).reverse ++ D.params.reverse)
      = fldCtx D C i from rfl, fldDom_rec M L hr] at hslot

/-! ### `Args` has content: it is inhabited above every field valuation

The failure mode a `Fld`/`Pos` mismatch would produce is an *empty* `Args` —
a signature that typechecks, an operator that is monotone and definable, and a
family that is empty because no pair is ever admissible.  Ruling it out is not
optional, and it is exactly what a blanking layout could not do without the
independence clauses at `posIdx` and `resIdx`.

`uncurrySlots` is the witness: assemble `f` from the slots of `a` by tagging
each slot's graph with its summand index.  Nothing about the syntax enters — the
whole content is that `Fld` chose the slot domains to be the summands of
`Pos`. -/

/-- The tagged uncurrying of `a`'s recursive slots. -/
noncomputable def uncurrySlots (a : V) : ℕ → List (ℕ × (V → V)) → V
  | _, [] => ∅
  | s, p :: rest =>
    (repl (fun x ↦ (⟨(⟨((s : ℕ) : V), x⟩ₖ : V), (a ‘ ((p.1 : ℕ) : V)) ‘ x⟩ₖ : V))
      (by definability) (p.2 a)) ∪ uncurrySlots a (s + 1) rest

theorem mem_uncurrySlots_iff {a : V} : ∀ (l : List (ℕ × (V → V))) (s : ℕ) (y : V),
    y ∈ uncurrySlots a s l ↔ ∃ (k : ℕ) (p : ℕ × (V → V)), l[k]? = some p ∧
      ∃ x ∈ p.2 a, y = (⟨(⟨((s + k : ℕ) : V), x⟩ₖ : V), (a ‘ ((p.1 : ℕ) : V)) ‘ x⟩ₖ : V)
  | [], s, y => by
    show y ∈ (∅ : V) ↔ _
    simp
  | p :: l, s, y => by
    show y ∈ (_ ∪ _ : V) ↔ _
    rw [mem_union_iff, repl_spec, mem_uncurrySlots_iff l (s + 1) y]
    constructor
    · rintro (⟨x, hx, rfl⟩ | ⟨k, p', hk, x, hx, rfl⟩)
      · exact ⟨0, p, rfl, x, hx, by rw [Nat.add_zero]⟩
      · exact ⟨k + 1, p', by simpa using hk, x, hx, by
          rw [show s + 1 + k = s + (k + 1) from by omega]⟩
    · rintro ⟨k, p', hk, x, hx, rfl⟩
      match k with
      | 0 =>
        have : p' = p := by simpa using hk.symm
        subst this
        exact Or.inl ⟨x, hx, by rw [Nat.add_zero]⟩
      | k + 1 =>
        refine Or.inr ⟨k, p', by simpa using hk, x, hx, ?_⟩
        rw [show s + 1 + k = s + (k + 1) from by omega]

theorem kpair_mem_uncurrySlots {a : V} {l : List (ℕ × (V → V))} {s k : ℕ}
    {p : ℕ × (V → V)} {x : V} (hk : l[k]? = some p) (hx : x ∈ p.2 a) :
    (⟨(⟨((s + k : ℕ) : V), x⟩ₖ : V), (a ‘ ((p.1 : ℕ) : V)) ‘ x⟩ₖ : V) ∈ uncurrySlots a s l :=
  (mem_uncurrySlots_iff l s _).2 ⟨k, p, hk, x, hx, rfl⟩

/-- The `n`-ary tagged union, read back. -/
theorem mem_tagUnionF_iff {a : V} : ∀ (As : List (V → V)) (i : ℕ) (b : V),
    b ∈ tagUnionF i As a ↔ ∃ (k : ℕ) (A : V → V), As[k]? = some A ∧
      ∃ y ∈ A a, b = (⟨((i + k : ℕ) : V), y⟩ₖ : V)
  | [], i, b => by rw [mem_tagUnionF_nil]; simp
  | A :: As, i, b => by
    rw [mem_tagUnionF_cons, mem_tagUnionF_iff As (i + 1) b]
    constructor
    · rintro (⟨y, hy, rfl⟩ | ⟨k, A', hk, y, hy, rfl⟩)
      · exact ⟨0, A, rfl, y, hy, by rw [Nat.add_zero]⟩
      · exact ⟨k + 1, A', by simpa using hk, y, hy, by
          rw [show i + 1 + k = i + (k + 1) from by omega]⟩
    · rintro ⟨k, A', hk, y, hy, rfl⟩
      match k with
      | 0 =>
        have : A' = A := by simpa using hk.symm
        subst this
        exact Or.inl ⟨y, hy, by rw [Nat.add_zero]⟩
      | k + 1 =>
        refine Or.inr ⟨k, A', by simpa using hk, y, hy, ?_⟩
        rw [show i + 1 + k = i + (k + 1) from by omega]

/-- The uncurrying is a function on exactly the positions. -/
theorem uncurrySlots_mem_function {Dcar a : V} {l : List (ℕ × (V → V))} {s : ℕ}
    (hslots : ∀ (k : ℕ) (p : ℕ × (V → V)), l[k]? = some p →
      (a ‘ ((p.1 : ℕ) : V)) ∈ (Dcar ^ p.2 a : V)) :
    uncurrySlots a s l ∈ (Dcar ^ tagUnionF s (l.map (·.2)) a : V) := by
  have hmap : ∀ (k : ℕ) (p : ℕ × (V → V)), l[k]? = some p →
      getElem? (l.map (·.2)) k = some p.2 := by
    intro k p hk; rw [List.getElem?_map, hk]; rfl
  refine mem_function.intro (fun y hy ↦ ?_) (fun b hb ↦ ?_)
  · obtain ⟨k, p, hk, x, hx, rfl⟩ := (mem_uncurrySlots_iff l s y).1 hy
    refine kpair_mem_iff.2 ⟨(mem_tagUnionF_iff (l.map (·.2)) s _).2
      ⟨k, p.2, hmap k p hk, x, hx, rfl⟩, ?_⟩
    have hsub := subset_prod_of_mem_function (hslots k p hk)
    have := hsub _ (kpair_value_mem (hslots k p hk) hx)
    exact (kpair_mem_iff.1 this).2
  · obtain ⟨k, A, hk, x, hx, rfl⟩ := (mem_tagUnionF_iff (l.map (·.2)) s b).1 hb
    obtain ⟨p, hp, rfl⟩ : ∃ p, l[k]? = some p ∧ p.2 = A := by
      rcases hl : l[k]? with _ | p
      · rw [List.getElem?_map, hl] at hk; simp at hk
      · rw [List.getElem?_map, hl] at hk
        exact ⟨p, rfl, by simpa using hk⟩
    refine ExistsUnique.intro ((a ‘ ((p.1 : ℕ) : V)) ‘ x)
      (kpair_mem_uncurrySlots hp hx) (fun v hv ↦ ?_)
    obtain ⟨k', p', hk', x', hx', he⟩ := (mem_uncurrySlots_iff l s _).1 hv
    obtain ⟨htag, rfl⟩ := kpair_inj he
    obtain ⟨hs, rfl⟩ := kpair_inj htag
    have : k' = k := by
      by_contra hne
      exact ofNat_ne_ofNat (by omega : s + k ≠ s + k') hs
    subst this
    rw [hk'] at hp
    rw [(Option.some.inj hp : p' = p)]

/-- **The condition is satisfied by the uncurrying.**  Stated over an arbitrary
`f` containing the tagged graphs, because the tail of the recursion has to be
proved for the *whole* `f`, not for the tail's own. -/
theorem argCond_of_kpair_mem {Dcar a f : V} [IsFunction f] :
    ∀ (l : List (ℕ × (V → V))) (s : ℕ),
    (∀ (k : ℕ) (p : ℕ × (V → V)), l[k]? = some p →
      (a ‘ ((p.1 : ℕ) : V)) ∈ (Dcar ^ p.2 a : V)) →
    (∀ (k : ℕ) (p : ℕ × (V → V)) (x : V), l[k]? = some p → x ∈ p.2 a →
      (⟨(⟨((s + k : ℕ) : V), x⟩ₖ : V), (a ‘ ((p.1 : ℕ) : V)) ‘ x⟩ₖ : V) ∈ f) →
    argCond Dcar s l a f
  | [], _, _, _ => trivial
  | p :: l, s, hslots, hmem => by
    refine ⟨hslots 0 p rfl, fun x hx ↦ ?_, ?_⟩
    · have := hmem 0 p x rfl hx
      rw [Nat.add_zero] at this
      exact (value_eq_of_kpair_mem this).symm
    · refine argCond_of_kpair_mem l (s + 1)
        (fun k p' hk ↦ hslots (k + 1) p' (by simpa using hk))
        (fun k p' x hk hx ↦ ?_)
      have := hmem (k + 1) p' x (by simpa using hk) hx
      rwa [show s + (k + 1) = s + 1 + k from by omega] at this

/-- **`Args` is inhabited above every `a`.**  The only hypothesis is that each
slot of `a` is a function on that slot's positions — which `fldSlot_mem` gives
for every element of `Fld`. -/
theorem exists_argCond {Dcar a : V} {l : List (ℕ × (V → V))}
    (hslots : ∀ (k : ℕ) (p : ℕ × (V → V)), l[k]? = some p →
      (a ‘ ((p.1 : ℕ) : V)) ∈ (Dcar ^ p.2 a : V)) :
    ∃ f ∈ (Dcar ^ tagUnionF 0 (l.map (·.2)) a : V), argCond Dcar 0 l a f := by
  refine ⟨uncurrySlots a 0 l, uncurrySlots_mem_function hslots, ?_⟩
  haveI : IsFunction (uncurrySlots a 0 l) := IsFunction.of_mem
    (uncurrySlots_mem_function (Dcar := Dcar) hslots)
  exact argCond_of_kpair_mem l 0 hslots fun k p x hk hx ↦ kpair_mem_uncurrySlots hk hx

/-! ### The assembled `CtorData₃` -/

/-- **The translation.**  `A i` is the block-free replacement for field `i`'s
type, which `VIndField.WF.pos` supplies through a chain-free existential; `j` is
the index of the block member the constructor builds; `Dcar` is the value
carrier of the stage. -/
noncomputable def ctorData (Dcar params : V) (A : ℕ → VExpr) (j : ℕ) (C : VIndCtor) :
    CtorData₃ V where
  flds := fun _ ↦ ctorFldSet M L D Dcar A params C
  flds_definable := by definability
  flds_mono := fun _ ↦ subset_refl _
  poss := posDoms M L D C
  poss_definable := posDoms_definable M L D C
  posIdxs := posIdxVals M L D params C
  posIdxs_definable := posIdxVals_definable M L D params C
  resIdx := resIdxVal M L D params j C
  resIdx_definable := resIdxVal_definable M L D params j C
  args := fun _ ↦ argSet Dcar (ctorFldSet M L D Dcar A params C)
    (fun a ↦ tagUnionF 0 (posDoms M L D C) a)
    (tagUnionF_definable 0 _ (posDoms_definable M L D C))
    (slotDoms M L D C) (fun p hp ↦ posDoms_definable M L D C p.2
      (List.mem_map.2 ⟨p, hp, rfl⟩))
  args_definable := by definability
  args_mono := fun _ ↦ subset_refl _

theorem slotDoms_getElem? (C : VIndCtor) {s i : ℕ} {r : VIndRecArg}
    (h : C.recFields[s]? = some (i, r)) :
    getElem? (slotDoms M L D C) s = some (D.np + i, fun a ↦
      (teleFun (teleDomains M L (fldCtx D C i) r.binders)).toFun
        (a ↾ ((D.np + i : ℕ) : V))) := by
  rw [slotDoms, List.getElem?_map, h]
  rfl

/-- **The recursive field's value is the curried filler.**  `Args` is doing
exactly the job the port introduced it for: it ties the copy of the filler that
sits in `a` — where the non-recursive field types and the result index can see
it — to the `f` that `indStep₃` supplies. -/
theorem recField_eq_curry {Dcar params a f W : V} {A : ℕ → VExpr} {j : ℕ} {C : VIndCtor}
    {s i : ℕ} {r : VIndRecArg} (hs : C.recFields[s]? = some (i, r))
    (hok : (⟨a, f⟩ₖ : V) ∈ (ctorData M L D Dcar params A j C).args W) :
    ∀ x ∈ (teleFun (teleDomains M L (fldCtx D C i) r.binders)).toFun
        (a ↾ ((D.np + i : ℕ) : V)),
      (a ‘ ((D.np + i : ℕ) : V)) ‘ x = f ‘ (⟨((s : ℕ) : V), x⟩ₖ : V) := by
  have hcond := (mem_argSet_iff
    (hl := fun p hp ↦ posDoms_definable M L D C p.2 (List.mem_map.2 ⟨p, hp, rfl⟩))).1 hok |>.2.2
  have := argCond_at (Dcar := Dcar) (a := a) (f := f) (slotDoms M L D C) 0 s _ hcond
    (slotDoms_getElem? M L D C hs)
  simpa using this.2

/-- Reading a recursive-field entry back.  This duplicates
`VIndCtor.mem_recFields` (`Theory/Inductive/Lemmas.lean`) rather than importing
it, to keep this file's dependency at `Decl.lean`. -/
theorem mem_recFields' {C : VIndCtor} {i : ℕ} {r : VIndRecArg}
    (h : (i, r) ∈ C.recFields) : ∃ F, C.fields[i]? = some F ∧ F.recArg = some r := by
  simp only [VIndCtor.recFields, List.mem_filterMap, Option.map_eq_some_iff,
    Prod.mk.injEq] at h
  obtain ⟨⟨F, i'⟩, hF, r', hr, rfl, rfl⟩ := h
  exact ⟨F, List.mk_mem_zipIdx_iff_getElem?.1 hF, hr⟩

/-- **`Args` is inhabited above every element of `Fld`.**  The translation is
not vacuous: for every field valuation the model admits, there is an `f` the
signature accepts — with `a`'s recursive slots exactly its curried components.

This is the statement a `Fld`/`Pos` mismatch would falsify, and it is proved
with no hypothesis about the syntax at all: `fldSlot_mem` supplies the slot
domains and `exists_argCond` supplies the witness. -/
theorem exists_mem_args {Dcar params a W : V} {A : ℕ → VExpr} {j : ℕ} {C : VIndCtor}
    (hp : IsSeq params D.np) (ha : a ∈ ctorFldSet M L D Dcar A params C) :
    ∃ f ∈ (Dcar ^ tagUnionF 0 (posDoms M L D C) a : V),
      (⟨a, f⟩ₖ : V) ∈ (ctorData M L D Dcar params A j C).args W := by
  have hslots : ∀ (k : ℕ) (p : ℕ × (V → V)), getElem? (slotDoms M L D C) k = some p →
      (a ‘ ((p.1 : ℕ) : V)) ∈ (Dcar ^ p.2 a : V) := by
    intro k p hk
    rcases hr : C.recFields[k]? with _ | ⟨i, r⟩
    · rw [slotDoms, List.getElem?_map, hr] at hk; simp at hk
    · obtain ⟨F, hF, hFr⟩ := mem_recFields' (List.mem_of_getElem? hr)
      have hp' : p = (D.np + i, fun a ↦
          (teleFun (teleDomains M L (fldCtx D C i) r.binders)).toFun
            (a ↾ ((D.np + i : ℕ) : V))) := by
        have := slotDoms_getElem? M L D C hr
        rw [hk] at this
        exact (Option.some.inj this)
      subst hp'
      exact fldSlot_mem M L D hp ha hF hFr
  obtain ⟨f, hf, hcond⟩ := exists_argCond (Dcar := Dcar) hslots
  refine ⟨f, hf, (mem_argSet_iff
    (hl := fun p hp ↦ posDoms_definable M L D C p.2 (List.mem_map.2 ⟨p, hp, rfl⟩))).2
    ⟨ha, hf, hcond⟩⟩

/-! ### Where `A` comes from

The translation takes the block-free replacements as a parameter; this is the
lemma that says a well-formed constructor supplies them.  It is choice on
`VIndField.WF.pos`'s `none` branch — a **chain-free** existential, so the result
is unconditional *data*, which is what `cnstOf`'s oracle parameter demands (see
`docs/model-interface.md` §4). -/

theorem exists_blockFreeTypes {env : VEnv} {j : ℕ} {T : VIndType} {C : VIndCtor}
    (h : C.WF env D j T) :
    ∃ A : ℕ → VExpr, ∀ (i : ℕ) (F : VIndField), C.fields[i]? = some F → F.recArg = none →
      D.NoBlock (A i) ∧ env.IsDefEqType D.uvars (fldCtx D C i) F.type (A i) := by
  have key : ∀ i : ℕ, ∃ B : VExpr, ∀ F : VIndField, C.fields[i]? = some F →
      F.recArg = none → D.NoBlock B ∧ env.IsDefEqType D.uvars (fldCtx D C i) F.type B := by
    intro i
    by_cases hF : ∃ F, C.fields[i]? = some F ∧ F.recArg = none
    · obtain ⟨F, hF1, hF2⟩ := hF
      have hpos := (h.fields i F hF1).pos
      rw [hF2] at hpos
      obtain ⟨B, hB1, hB2⟩ := hpos
      refine ⟨B, fun F' hF' _ ↦ ?_⟩
      have : F' = F := by rw [hF1] at hF'; exact (Option.some.inj hF').symm
      subst this
      exact ⟨hB1, hB2⟩
    · exact ⟨default, fun F hF1 hF2 ↦ absurd ⟨F, hF1, hF2⟩ hF⟩
  exact ⟨fun i ↦ (key i).choose, fun i F h1 h2 ↦ (key i).choose_spec F h1 h2⟩

/-- **The translation, off a well-formedness proof.**  Everything the model
needs about one constructor, with no data beyond `VIndCtor.WF`. -/
noncomputable def ctorDataOf {env : VEnv} {j : ℕ} {T : VIndType} {C : VIndCtor}
    (h : C.WF env D j T) (Dcar params : V) : CtorData₃ V :=
  ctorData M L D Dcar params (exists_blockFreeTypes D h).choose j C

/-! ## The block

`Idx` is the disjoint union of the members' index telescopes; nothing in
`SetModel/Inductive.lean` assumes it is indecomposable, and `resIdx`/`posIdx`
tag their tuples with the member they belong to. -/

/-- `Idx`: the tagged union of the block members' index-telescope tuples. -/
noncomputable def idxSet (params : V) : V :=
  tagUnionF 0 (D.types.map fun T ↦ fun _ : V ↦
    (teleFun (teleDomains M L D.params.reverse T.indices)).toFun params) ∅

/-- **`interpSig`, in the ported form.**  One `CtorData₃` per entry of
`ctorsAll`, in kernel order, so the tag `q` of a minor premise is the tag of its
constructor. -/
noncomputable def interpSig₃ (Dcar params : V) (A : ℕ → ℕ → VExpr) : IndSignature₃ V :=
  mkIndSignature₃ (idxSet M L D params)
    (D.ctorsAll.zipIdx.map fun p ↦ ctorData M L D Dcar params (A p.2) p.1.1 p.1.2)

theorem interpSig₃_Idx (Dcar params : V) (A : ℕ → ℕ → VExpr) :
    (interpSig₃ M L D Dcar params A).Idx = idxSet M L D params := rfl

theorem interpSig₃_Q (Dcar params : V) (A : ℕ → ℕ → VExpr) :
    (interpSig₃ M L D Dcar params A).Q = ((D.nmin : ℕ) : V) := by
  show ((_ : ℕ) : V) = _
  rw [List.length_map, List.length_zipIdx]

/-- The tag really selects the constructor's own data. -/
theorem interpSig₃_ctorData (Dcar params : V) (A : ℕ → ℕ → VExpr) {q j : ℕ}
    {C : VIndCtor} (h : D.ctorsAll[q]? = some (j, C)) :
    getElem? (D.ctorsAll.zipIdx.map fun p ↦ ctorData M L D Dcar params (A p.2) p.1.1 p.1.2) q
      = some (ctorData M L D Dcar params (A q) j C) := by
  rw [List.getElem?_map, List.getElem?_zipIdx, h]
  simp

end Ctor

end Lean4Lean.SetModel
