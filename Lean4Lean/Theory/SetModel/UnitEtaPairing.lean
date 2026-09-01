import Lean4Lean.Theory.SetModel.CtorTrans

/-!
# Zero-field surjective pairing, and what it costs at a **mutual** block

`docs/vacuity-ledger.md` row 102a: `VEnv.UnitEta`
(`Theory/Inductive/StructureEta.lean`) is strictly stronger than
`VEnv.StructEta`'s zero-field instance, because it is stated over
`VEnv.IsStructureG` and so fires at a member of a *mutual* block.  Whatever
discharges it must therefore validate surjective pairing there, not only at a
singleton block, and nothing showed that the model does.  This file measures
exactly that, at the set level.

## The answer, in one line

**At zero fields surjective pairing is trivial, and mutuality costs one
`kpair_inj`** — but the theorem that would have delivered it,
`Ind₃_subsingleton`, *cannot* be used, and the reason is worth recording.

## Why `Ind₃_subsingleton` does not apply, and what replaces it

`IsSubsingletonSignature₃.single` (`SetModel/CtorTrans.lean`) reads

```
single : ∀ q ∈ S.Q, ∀ q' ∈ S.Q, q = q'
```

i.e. **one constructor in the whole block**.  At a two-type mutual block whose
members each have one constructor — `MutNonRec.decl2`, the block
`isDefEqUnitLike` actually fires at — `S.Q` is the numeral `2` and `single` is
**false**.  So the existing subsingleton theorem is unavailable at precisely the
configuration row 102a is about, and its failure is *not* an artefact of the
zero-field case: it is the singleton-block assumption, in the model's own
language.

What the fibre argument actually needs is weaker and **local to the index**:

* `ResIdxDetAt S i` — the result index `i` determines the constructor tag.

`IsSubsingletonSignature₃.resIdxDetAt` shows `single` implies it at every `i`, so
nothing is lost; `resIdxDetAt_of_memberTag` shows it holds at a mutual block as
soon as (a) result indices are tagged by the block member — which
`SetModel/CtorTrans.lean`'s `resIdxVal` already does, `resIdxVal M L D params j C
a = ⟨j, …⟩ₖ` **by definition** — and (b) the member in question has exactly one
constructor, which is `VEnv.IsStructureG.ctors : T.ctors = [C]`.

Localising to the index is not decoration.  In
`mutual inductive A | mk : A; inductive B | t : B | f : B end`, `A` is unit-like
and `isDefEqUnitLike` fires at it, while `B` is not; a *global* condition would
be false at that block for the wrong reason.

## What is proved here

* `mem_Ind₃_fibre_iff_of_zero_field` — **surjective pairing at zero fields**, in
  `iff` form, so it carries inhabitation too: the fibre over `S.resIdx q₀ a₀` is
  exactly `{indCtorVal q₀ a₀ ∅}`.  No rank induction, no `IsSubsingletonSignature₃`,
  no bound on the number of block members.
* `mutUnitSig` — the model-side counterpart of `MutNonRec.decl2`: a **two-member**
  signature, both members zero-field, built through `mkIndSignature₃` so the
  definability obligations are real.  Both fibres are singletons
  (`mutUnitSig_fibre_zero`, `mutUnitSig_fibre_one`), they are **distinct**
  (`mutUnitSig_ctorVal_ne`), and the block is genuinely mutual
  (`mutUnitSig_Q_two`, `tags_ne`).
* `zfSig boolIdx [0, 0]` — the same construction with two constructors at **one** member:
  `ResIdxDetAt` is **false** there (`boolSig_not_resIdxDetAt`) and the fibre
  genuinely holds two elements (`boolSig_fibre_two`).  So the hypothesis is
  load-bearing and the positive result is bounded both ways.

## What is **not** proved here, and it is the honest residual

Nothing above links a fibre to `⟦(const S us).mkApp ps⟧`.  That link needs the
`.induct` oracle to be *defined* as `IndFiber ∘ interpSig₃` — `OracleOK`
constrains a type former's denotation by **membership only** (`SetModel/Cnst.lean`,
ledger row 29 for the same defect in `CoherentOn.const_type`), so a model
satisfying `InductOracleOK` may interpret a zero-field structure as a
two-element set and refute eta outright.  **That gap is shared, verbatim, by
singleton blocks**: it is not created by row 99d's widening.

So row 102a's *incremental* cost is nil, and this file says so as plainly as it
would report a difficulty.  The residual it leaves is the pre-existing one —
define the oracle — plus the single `kpair_inj` step above.
-/

namespace Lean4Lean.SetModel

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open scoped Classical

variable {V : Type*} [SetStructure V] [Nonempty V]

/-- **The result index `i` determines the constructor tag.**

This is the *whole* hypothesis zero-field surjective pairing needs, and it is
strictly weaker than `IsSubsingletonSignature₃.single` in two independent ways:
it is local to one index, and it constrains only the tag (not `Fld`, `Pos` or
`posIdx`). -/
def ResIdxDetAt (S : IndSignature₃ V) (i : V) : Prop :=
  ∀ q ∈ S.Q, ∀ q' ∈ S.Q, ∀ a a' : V, S.resIdx q a = i → S.resIdx q' a' = i → q = q'

section
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {S : IndSignature₃ V} {D : V}

/-- Numerals are distinct, so the numeral map is injective.  `ofNat_ne_ofNat`
(`SetModel/InterpSubst.lean`) is the contrapositive. -/
theorem ofNat_inj' {a b : ℕ} (h : ((a : ℕ) : V) = ((b : ℕ) : V)) : a = b := by
  by_contra hc; exact ofNat_ne_ofNat (V := V) hc h

/-- **Nothing is lost by the weakening**: a subsingleton signature has it at
every index. -/
theorem IsSubsingletonSignature₃.resIdxDetAt (h : IsSubsingletonSignature₃ S D)
    (i : V) : ResIdxDetAt S i :=
  fun q hq q' hq' _ _ _ _ ↦ h.single q hq q' hq'

/-- **The mutual-block step, and it is one `kpair_inj`.**

If every result index is tagged by the block member it belongs to — which is
`resIdxVal`'s definition — then `ResIdxDetAt` at an index of member `m` reduces
to "member `m` has exactly one constructor". -/
theorem resIdxDetAt_of_memberTag {memberOf : V → V} {q₀ m y : V}
    (htag : ∀ q ∈ S.Q, ∀ a : V, ∃ z, S.resIdx q a = (⟨memberOf q, z⟩ₖ : V))
    (hone : ∀ q ∈ S.Q, memberOf q = m → q = q₀) :
    ResIdxDetAt S (⟨m, y⟩ₖ : V) := by
  intro q hq q' hq' a a' h h'
  obtain ⟨z, hz⟩ := htag q hq a
  obtain ⟨z', hz'⟩ := htag q' hq' a'
  rw [hz] at h
  rw [hz'] at h'
  rw [hone q hq (kpair_inj h).1, hone q' hq' (kpair_inj h').1]

/-- **Surjective pairing at zero fields.**  The fibre of `Ind₃ S D` over
`S.resIdx q₀ a₀` is exactly `{indCtorVal q₀ a₀ ∅}`.

Stated as an `iff` so that it carries inhabitation as well as uniqueness: `←` is
`ctor_mem_Ind₃`, `→` is `mem_Ind₃_iff` followed by three pinnings — the tag by
`hdet`, the field valuation by `hFld`, and the recursive filler by
`S.Pos q₀ a₀ = ∅`.

**There is no rank induction and no bound on `S.Q`.**  That is the content: with
no fields and no recursive positions the fixed point's no-junk lemma pins the
element outright, so nothing about the block's size or shape enters beyond
`hdet`. -/
theorem mem_Ind₃_fibre_iff_of_zero_field
    (hWF : S.toIndSignature₂.WF) (hD : IsIndCarrier₃ S D)
    {q₀ a₀ : V} (hq₀ : q₀ ∈ S.Q) (ha₀ : a₀ ∈ S.Fld (Ind₃ S D) q₀)
    (hok₀ : (⟨a₀, (∅ : V)⟩ₖ : V) ∈ S.Args (Ind₃ S D) q₀)
    (hdet : ResIdxDetAt S (S.resIdx q₀ a₀))
    (hPos : ∀ a ∈ S.Fld (Ind₃ S D) q₀, S.Pos q₀ a = ∅)
    (hFld : ∀ a ∈ S.Fld (Ind₃ S D) q₀, a = a₀) {x : V} :
    (⟨S.resIdx q₀ a₀, x⟩ₖ : V) ∈ Ind₃ S D ↔ x = indCtorVal q₀ a₀ ∅ := by
  have hf0 : (∅ : V) ∈ (D ^ S.Pos q₀ a₀ : V) := by
    rw [hPos a₀ ha₀]; exact mem_function_iff.mpr ⟨by simp, by simp⟩
  constructor
  · intro hx
    obtain ⟨q, hq, a, ha, f, hf, hok, -, hex⟩ := (mem_Ind₃_iff hWF hD).mp hx
    rw [indCtor₃] at hex
    obtain ⟨hi, hxv⟩ := kpair_inj hex
    have hqq : q = q₀ := hdet q hq q₀ hq₀ a a₀ hi.symm rfl
    subst hqq
    have haa : a = a₀ := hFld a ha
    subst haa
    have hfe : f = ∅ := by
      rw [hPos a ha] at hf; exact eq_empty_of_mem_function_empty hf
    rw [hxv, hfe, indCtorVal]
  · rintro rfl
    exact ctor_mem_Ind₃ (S := S) (D := D) hq₀
      (kpair_mem_iff.mpr ⟨hWF.resIdx_mem _ q₀ hq₀ a₀ ha₀,
        hD.ctor_mem _ q₀ hq₀ a₀ ha₀ ∅ hf0 hok₀⟩)
      ha₀ hf0 hok₀
      (fun b hb ↦ by rw [hPos a₀ ha₀] at hb; exact absurd hb (by simp))

/-- **What `UnitEta` needs of the model, at the set level**: any two inhabitants
of the fibre coincide.  A corollary of the `iff` above, spelled out because it is
the shape the eta rule consumes. -/
theorem Ind₃_fibre_subsingleton_of_zero_field
    (hWF : S.toIndSignature₂.WF) (hD : IsIndCarrier₃ S D)
    {q₀ a₀ : V} (hq₀ : q₀ ∈ S.Q) (ha₀ : a₀ ∈ S.Fld (Ind₃ S D) q₀)
    (hok₀ : (⟨a₀, (∅ : V)⟩ₖ : V) ∈ S.Args (Ind₃ S D) q₀)
    (hdet : ResIdxDetAt S (S.resIdx q₀ a₀))
    (hPos : ∀ a ∈ S.Fld (Ind₃ S D) q₀, S.Pos q₀ a = ∅)
    (hFld : ∀ a ∈ S.Fld (Ind₃ S D) q₀, a = a₀) {x y : V}
    (hx : (⟨S.resIdx q₀ a₀, x⟩ₖ : V) ∈ Ind₃ S D)
    (hy : (⟨S.resIdx q₀ a₀, y⟩ₖ : V) ∈ Ind₃ S D) : x = y := by
  rw [(mem_Ind₃_fibre_iff_of_zero_field hWF hD hq₀ ha₀ hok₀ hdet hPos hFld).1 hx,
    (mem_Ind₃_fibre_iff_of_zero_field hWF hD hq₀ ha₀ hok₀ hdet hPos hFld).1 hy]

end

/-! ## Reading an assembled signature back at a tag

`mkIndSignature₃_wf` proves two of these inline; the four are pulled out here
because the witnesses below need all of them.  Nothing in `IndInterp.lean`
states them. -/

section Readback
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]

theorem mkIndSignature₃_Fld (Idx : V) (cs : List (CtorData₃ V)) {k : ℕ} {c : CtorData₃ V}
    (h : cs[k]? = some c) (W : V) :
    (mkIndSignature₃ Idx cs).Fld W ((k : ℕ) : V) = c.flds W := by
  show tagCaseSnd 0 (cs.map (·.flds)) W ((k : ℕ) : V) = _
  have := tagCaseSnd_at (V := V) 0 (cs.map (·.flds)) k c.flds
    (by rw [List.getElem?_map, h]; rfl) W
  simpa using this

theorem mkIndSignature₃_Args (Idx : V) (cs : List (CtorData₃ V)) {k : ℕ} {c : CtorData₃ V}
    (h : cs[k]? = some c) (W : V) :
    (mkIndSignature₃ Idx cs).Args W ((k : ℕ) : V) = c.args W := by
  show tagCaseSnd 0 (cs.map (·.args)) W ((k : ℕ) : V) = _
  have := tagCaseSnd_at (V := V) 0 (cs.map (·.args)) k c.args
    (by rw [List.getElem?_map, h]; rfl) W
  simpa using this

theorem mkIndSignature₃_resIdx (Idx : V) (cs : List (CtorData₃ V)) {k : ℕ} {c : CtorData₃ V}
    (h : cs[k]? = some c) (a : V) :
    (mkIndSignature₃ Idx cs).resIdx ((k : ℕ) : V) a = c.resIdx a := by
  show tagCase₂ 0 (cs.map fun c ↦ fun _ a ↦ c.resIdx a) ((k : ℕ) : V) a = _
  have := tagCase₂_at (V := V) 0 (cs.map fun c ↦ fun _ a ↦ c.resIdx a) k
    (fun _ a ↦ c.resIdx a) (by rw [List.getElem?_map, h]; rfl) a
  simpa using this

theorem mkIndSignature₃_Pos (Idx : V) (cs : List (CtorData₃ V)) {k : ℕ} {c : CtorData₃ V}
    (h : cs[k]? = some c) (a : V) :
    (mkIndSignature₃ Idx cs).Pos ((k : ℕ) : V) a = tagUnionF 0 c.poss a := by
  show tagCase₂ 0 (cs.map fun c ↦ fun _ a ↦ tagUnionF 0 c.poss a) ((k : ℕ) : V) a = _
  have := tagCase₂_at (V := V) 0 (cs.map fun c ↦ fun _ a ↦ tagUnionF 0 c.poss a) k
    (fun _ a ↦ tagUnionF 0 c.poss a) (by rw [List.getElem?_map, h]; rfl) a
  simpa using this

end Readback

/-! ## The mutual-block step, at the REAL translation

`resIdxDetAt_of_memberTag` above is stated abstractly.  This section discharges its
`htag` hypothesis at `SetModel/CtorTrans.lean`'s actual `VInductDecl' → IndSignature₃`
translation, so the claim "result indices are member-tagged" is machine-checked
rather than read off source.

The residual is then exactly **"member `j` has one constructor"**, which is
`VEnv.IsStructureG.ctors : T.ctors = [C]` — the gate `isDefEqUnitLike` already
tests.  Nothing about the *number of members* is used. -/

section RealTranslation
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ} (M : ModelData V) (L : PropSplit envF nv) (D : VInductDecl')

/-- **`resIdxVal` tags the result index by the block member, by definition.** -/
theorem resIdxVal_tagged (params : V) (j : ℕ) (C : VIndCtor) (a : V) :
    ∃ z, resIdxVal M L D params j C a = (⟨((j : ℕ) : V), z⟩ₖ : V) :=
  ⟨argsVal M L ((C.fields.map (·.type)).reverse ++ D.params.reverse) C.args a params, rfl⟩

/-- …and the assembled signature inherits it at every tag. -/
theorem interpSig₃_resIdx_tagged (Dcar params : V) (A : ℕ → ℕ → VExpr) {q j : ℕ}
    {C : VIndCtor} (h : D.ctorsAll[q]? = some (j, C)) (a : V) :
    ∃ z, (interpSig₃ M L D Dcar params A).resIdx ((q : ℕ) : V) a
      = (⟨((j : ℕ) : V), z⟩ₖ : V) := by
  obtain ⟨z, hz⟩ := resIdxVal_tagged M L D params j C a
  refine ⟨z, ?_⟩
  rw [show (interpSig₃ M L D Dcar params A) = mkIndSignature₃ (idxSet M L D params)
      (D.ctorsAll.zipIdx.map fun p ↦ ctorData M L D Dcar params (A p.2) p.1.1 p.1.2) from rfl,
    mkIndSignature₃_resIdx _ _ (interpSig₃_ctorData M L D Dcar params A h) a]
  exact hz

/-- **`ResIdxDetAt` at the real translation, from a per-member gate.**

`hone` says: among the block's constructors, only tag `q₀` belongs to member `j`.
For a block member declared with `T.ctors = [C]` that is immediate, *whatever the
other members look like* — which is the whole content of row 102a, and it is one
`kpair_inj` plus `ofNat_inj'`. -/
theorem interpSig₃_resIdxDetAt (Dcar params : V) (A : ℕ → ℕ → VExpr) {j q₀ : ℕ} {y : V}
    (hone : ∀ q < D.nmin, ∀ j' C', D.ctorsAll[q]? = some (j', C') → j' = j → q = q₀) :
    ResIdxDetAt (interpSig₃ M L D Dcar params A) (⟨((j : ℕ) : V), y⟩ₖ : V) := by
  intro q hq q' hq' a a' h h'
  rw [interpSig₃_Q] at hq hq'
  obtain ⟨k, hk, rfl⟩ := (mem_ofNat_iff D.nmin q).1 hq
  obtain ⟨k', hk', rfl⟩ := (mem_ofNat_iff D.nmin q').1 hq'
  obtain ⟨jk, Ck, hck⟩ : ∃ jk Ck, D.ctorsAll[k]? = some (jk, Ck) := by
    cases hd : D.ctorsAll[k] with
    | mk jk Ck => exact ⟨jk, Ck, by rw [List.getElem?_eq_getElem hk, hd]⟩
  obtain ⟨jk', Ck', hck'⟩ : ∃ jk' Ck', D.ctorsAll[k']? = some (jk', Ck') := by
    cases hd : D.ctorsAll[k'] with
    | mk jk' Ck' => exact ⟨jk', Ck', by rw [List.getElem?_eq_getElem hk', hd]⟩
  obtain ⟨z, hz⟩ := interpSig₃_resIdx_tagged M L D Dcar params A hck a
  obtain ⟨z', hz'⟩ := interpSig₃_resIdx_tagged M L D Dcar params A hck' a'
  rw [hz] at h
  rw [hz'] at h'
  rw [hone k hk jk Ck hck (ofNat_inj' (kpair_inj h).1),
    hone k' hk' jk' Ck' hck' (ofNat_inj' (kpair_inj h').1)]


/-! ### And the other four hypotheses, also at the real translation

At `C.fields = []` every remaining hypothesis of
`mem_Ind₃_fibre_iff_of_zero_field` is discharged outright from
`SetModel/CtorTrans.lean`'s own definitions: `Fld` collapses to the singleton
`{params}` (`teleFun_nil`), `Pos` to `∅` (no recursive fields), and `Args`'
condition to `True` (`argCond` at the nil slot list).  So at the real translation
the **only** thing zero-field surjective pairing wants is `ResIdxDetAt`. -/

theorem fldDoms_of_no_fields (Dcar : V) (A : ℕ → VExpr) (Γ : List VExpr) (i : ℕ)
    {C : VIndCtor} (h : C.fields = []) : fldDoms M L Dcar A Γ i C.fields = [] := by
  rw [h]; rfl

theorem ctorFldSet_of_no_fields (Dcar params : V) (A : ℕ → VExpr) {C : VIndCtor}
    (h : C.fields = []) : ctorFldSet M L D Dcar A params C = ({params} : V) := by
  rw [ctorFldSet, fldDoms_of_no_fields M L Dcar A _ _ h, teleFun_nil]

theorem recFields_of_no_fields {C : VIndCtor} (h : C.fields = []) : C.recFields = [] := by
  simp [VIndCtor.recFields, h]

theorem slotDoms_of_no_fields {C : VIndCtor} (h : C.fields = []) :
    slotDoms M L D C = [] := by rw [slotDoms, recFields_of_no_fields h]; rfl

theorem posDoms_of_no_fields {C : VIndCtor} (h : C.fields = []) :
    posDoms M L D C = [] := by rw [posDoms, slotDoms_of_no_fields M L D h]; rfl

/-- **Zero-field surjective pairing at the real translation.**

Every premise but `ResIdxDetAt` is discharged from the translation's own
definitions; `ResIdxDetAt` is `interpSig₃_resIdxDetAt`, whose only input is that
member `j` has one constructor.  **The number of block members is never used.**

`hone` is the *only* place mutuality could have bitten, and it is exactly what
`VEnv.IsStructureG.ctors : T.ctors = [C]` gives — the gate `isDefEqUnitLike`
already tests. -/
theorem interpSig₃_fibre_iff_of_no_fields (Dcar params : V) (A : ℕ → ℕ → VExpr)
    (hWF : (interpSig₃ M L D Dcar params A).toIndSignature₂.WF)
    (hD : IsIndCarrier₃ (interpSig₃ M L D Dcar params A) Dcar)
    {q j : ℕ} {C : VIndCtor} (hq : q < D.nmin) (hck : D.ctorsAll[q]? = some (j, C))
    (hnf : C.fields = [])
    (hone : ∀ q' < D.nmin, ∀ j' C', D.ctorsAll[q']? = some (j', C') → j' = j → q' = q)
    {x : V} :
    (⟨(interpSig₃ M L D Dcar params A).resIdx ((q : ℕ) : V) params, x⟩ₖ : V)
        ∈ Ind₃ (interpSig₃ M L D Dcar params A) Dcar ↔
      x = indCtorVal ((q : ℕ) : V) params ∅ := by
  have hcd := interpSig₃_ctorData M L D Dcar params A hck
  have hfld : ∀ W : V, (interpSig₃ M L D Dcar params A).Fld W ((q : ℕ) : V) = ({params} : V) := by
    intro W
    rw [show (interpSig₃ M L D Dcar params A) = mkIndSignature₃ (idxSet M L D params)
        (D.ctorsAll.zipIdx.map fun p ↦ ctorData M L D Dcar params (A p.2) p.1.1 p.1.2) from rfl,
      mkIndSignature₃_Fld _ _ hcd W]
    exact ctorFldSet_of_no_fields M L D Dcar params (A q) hnf
  have hpos : ∀ a : V, (interpSig₃ M L D Dcar params A).Pos ((q : ℕ) : V) a = ∅ := by
    intro a
    rw [show (interpSig₃ M L D Dcar params A) = mkIndSignature₃ (idxSet M L D params)
        (D.ctorsAll.zipIdx.map fun p ↦ ctorData M L D Dcar params (A p.2) p.1.1 p.1.2) from rfl,
      mkIndSignature₃_Pos _ _ hcd a,
      show (ctorData M L D Dcar params (A q) j C).poss = posDoms M L D C from rfl,
      posDoms_of_no_fields M L D hnf]
    rfl
  have hargs : ∀ W : V, (interpSig₃ M L D Dcar params A).Args W ((q : ℕ) : V)
      = argSet Dcar (ctorFldSet M L D Dcar (A q) params C)
        (fun a ↦ tagUnionF 0 (posDoms M L D C) a)
        (tagUnionF_definable 0 _ (posDoms_definable M L D C))
        (slotDoms M L D C) (fun p hp ↦ posDoms_definable M L D C p.2
          (List.mem_map.2 ⟨p, hp, rfl⟩)) := by
    intro W
    rw [show (interpSig₃ M L D Dcar params A) = mkIndSignature₃ (idxSet M L D params)
        (D.ctorsAll.zipIdx.map fun p ↦ ctorData M L D Dcar params (A p.2) p.1.1 p.1.2) from rfl,
      mkIndSignature₃_Args _ _ hcd W]
    rfl
  have hqQ : (((q : ℕ) : V)) ∈ (interpSig₃ M L D Dcar params A).Q := by
    rw [interpSig₃_Q]; exact (mem_ofNat_iff D.nmin _).2 ⟨q, hq, rfl⟩
  have haF : params ∈ (interpSig₃ M L D Dcar params A).Fld
      (Ind₃ (interpSig₃ M L D Dcar params A) Dcar) ((q : ℕ) : V) := by
    rw [hfld]; exact mem_singleton_iff.2 rfl
  have hok : (⟨params, (∅ : V)⟩ₖ : V) ∈ (interpSig₃ M L D Dcar params A).Args
      (Ind₃ (interpSig₃ M L D Dcar params A) Dcar) ((q : ℕ) : V) := by
    rw [hargs]
    refine mem_argSet_iff.2 ⟨?_, ?_, ?_⟩
    · rw [ctorFldSet_of_no_fields M L D Dcar params (A q) hnf]; exact mem_singleton_iff.2 rfl
    · rw [posDoms_of_no_fields M L D hnf]
      show (∅ : V) ∈ (Dcar ^ (∅ : V) : V)
      exact mem_function_iff.mpr ⟨by simp, by simp⟩
    · rw [slotDoms_of_no_fields M L D hnf]; trivial
  obtain ⟨z, hz⟩ := interpSig₃_resIdx_tagged M L D Dcar params A hck params
  refine mem_Ind₃_fibre_iff_of_zero_field hWF hD hqQ haF hok ?_ (fun a _ ↦ hpos a)
    (fun a ha ↦ mem_singleton_iff.1 (by rwa [hfld] at ha))
  rw [hz]
  exact interpSig₃_resIdxDetAt M L D Dcar params A
    (fun q' hq' j' C' hc' he' ↦ hone q' hq' j' C' hc' he')


/-! ### Instrument 7 for the combinatorial premises, at a two-member block

`interpSig₃_fibre_iff_of_no_fields` takes `hWF` and `hD` as hypotheses — they are
the model interface's open `interpSig_wf`/carrier items, shared with singleton
blocks — so the theorem does **not** fire unconditionally today.  Its premises that
*are* about the declaration (`hck`, `hnf`, `hone`) do, and they are the ones
mutuality could have broken, so they are checked here at a two-member block with
one zero-field constructor each.

`zfMutDecl` is the `Theory/`-side shape of `MutNonRec.decl2`
(`Verify/StructureBridge.lean`); it is rebuilt rather than imported because
nothing under `Theory/` imports `Verify/`. -/

section Decl2Premises

/-- Two block members, one zero-field constructor each. -/
def zfMutCtor (n : Lean.Name) : VIndCtor := { name := n, params := [], fields := [], args := [] }

def zfMutType (n cn : Lean.Name) : VIndType :=
  { name := n, type := .sort (.succ .zero), indices := [], ctors := [zfMutCtor cn] }

def zfMutDecl : VInductDecl' :=
  { uvars := 0, params := [], lvl := .succ .zero, isLE := false,
    types := [zfMutType `A `A.mk, zfMutType `B `B.mk] }

theorem zfMutDecl_ctorsAll :
    zfMutDecl.ctorsAll = [(0, zfMutCtor `A.mk), (1, zfMutCtor `B.mk)] := rfl

theorem zfMutDecl_nmin : zfMutDecl.nmin = 2 := rfl

/-- **The premises of `interpSig₃_fibre_iff_of_no_fields` that concern the
declaration, discharged at BOTH members of the two-member block.**  `hone` is the
conjunct mutuality could have broken; it holds because each member has one
constructor, and the other member's tag carries a different `j`. -/
theorem zfMutDecl_premises :
    (zfMutDecl.ctorsAll[0]? = some (0, zfMutCtor `A.mk) ∧ (zfMutCtor `A.mk).fields = [] ∧
      ∀ q' < zfMutDecl.nmin, ∀ j' C', zfMutDecl.ctorsAll[q']? = some (j', C') → j' = 0 → q' = 0) ∧
    (zfMutDecl.ctorsAll[1]? = some (1, zfMutCtor `B.mk) ∧ (zfMutCtor `B.mk).fields = [] ∧
      ∀ q' < zfMutDecl.nmin, ∀ j' C', zfMutDecl.ctorsAll[q']? = some (j', C') → j' = 1 → q' = 1) := by
  refine ⟨⟨rfl, rfl, ?_⟩, ⟨rfl, rfl, ?_⟩⟩ <;>
    intro q' hq' j' C' hc' he' <;>
    rw [zfMutDecl_nmin] at hq' <;>
    match q', hq' with
    | 0, _ => first | rfl | exact absurd (by simpa [zfMutDecl_ctorsAll] using hc') (by simp [he'])
    | 1, _ => first | rfl | exact absurd (by simpa [zfMutDecl_ctorsAll] using hc') (by simp [he'])

end Decl2Premises

end RealTranslation

/-! ## The witnesses: a genuinely two-member block, and the negative control

`zfSig js` is the signature of a block with `js.length` constructors, the `i`-th
belonging to block member `js[i]`, each with **no fields and no recursive
positions** — the shape `isDefEqUnitLike` gates on.  Tagging `resIdx` by the
member index is exactly what `SetModel/CtorTrans.lean`'s `resIdxVal` does.

Two instances are taken:

* `mutUnitSig = zfSig [0, 1]` — **two members, one constructor each**: the
  model-side `MutNonRec.decl2`;
* `boolSig = zfSig [0, 0]` — **one member, two constructors**: the negative
  control, where `ResIdxDetAt` is false and the fibre really does hold two
  elements. -/

section Witness
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]

/-- A zero-field, non-recursive constructor of block member `j`. -/
noncomputable def unitCtorData (j : ℕ) : CtorData₃ V where
  flds := fun _ ↦ ({∅} : V)
  flds_definable := by definability
  flds_mono := fun _ _ hz ↦ hz
  poss := []
  poss_definable := nofun
  posIdxs := []
  posIdxs_definable := nofun
  resIdx := fun _ ↦ (⟨((j : ℕ) : V), ∅⟩ₖ : V)
  resIdx_definable := by definability
  args := fun _ ↦ ({(⟨(∅ : V), (∅ : V)⟩ₖ : V)} : V)
  args_definable := by definability
  args_mono := fun _ _ hz ↦ hz

/-- The block: one zero-field constructor per entry of `js`, at member `js[i]`. -/
noncomputable def zfSig (Idx : V) (js : List ℕ) : IndSignature₃ V :=
  mkIndSignature₃ Idx (js.map unitCtorData)

/-- The carrier: `Q ×ˢ {⟨∅, ∅⟩ₖ}`, the explicit no-recursion carrier of
`isIndCarrier_of_no_recursion` specialised to zero fields.  Finite, so nothing
about inaccessibles or `Above` enters this file at all. -/
noncomputable def zfCar (n : ℕ) : V := ((n : ℕ) : V) ×ˢ ({(⟨(∅ : V), (∅ : V)⟩ₖ : V)} : V)

variable {Idx : V} {js : List ℕ}

theorem zfSig_Q : (zfSig Idx js).Q = ((js.length : ℕ) : V) := by
  show ((_ : ℕ) : V) = _; rw [List.length_map]

theorem zfSig_getElem {k : ℕ} (hk : k < js.length) :
    getElem? (js.map (unitCtorData (V := V))) k = some (unitCtorData js[k]) := by
  rw [List.getElem?_map, List.getElem?_eq_getElem hk]; rfl

theorem zfSig_Fld {k : ℕ} (hk : k < js.length) (W : V) :
    (zfSig Idx js).Fld W ((k : ℕ) : V) = ({∅} : V) :=
  mkIndSignature₃_Fld _ _ (zfSig_getElem hk) W

theorem zfSig_Args {k : ℕ} (hk : k < js.length) (W : V) :
    (zfSig Idx js).Args W ((k : ℕ) : V) = ({(⟨(∅ : V), (∅ : V)⟩ₖ : V)} : V) :=
  mkIndSignature₃_Args _ _ (zfSig_getElem hk) W

theorem zfSig_Pos {k : ℕ} (hk : k < js.length) (a : V) :
    (zfSig Idx js).Pos ((k : ℕ) : V) a = ∅ :=
  mkIndSignature₃_Pos _ _ (zfSig_getElem hk) a

theorem zfSig_resIdx {k : ℕ} (hk : k < js.length) (a : V) :
    (zfSig Idx js).resIdx ((k : ℕ) : V) a = (⟨((js[k] : ℕ) : V), ∅⟩ₖ : V) :=
  mkIndSignature₃_resIdx _ _ (zfSig_getElem hk) a

theorem zfSig_wf (h : ∀ j ∈ js, (⟨((j : ℕ) : V), ∅⟩ₖ : V) ∈ Idx) :
    (zfSig Idx js).toIndSignature₂.WF := by
  refine mkIndSignature₃_wf fun c hc W a _ ↦ ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hc
  exact h j hj

theorem zfSig_carrier : IsIndCarrier₃ (zfSig Idx js) (zfCar js.length : V) := by
  refine ⟨fun W q hq a ha f hf _ ↦ ?_⟩
  rw [zfSig_Q] at hq
  obtain ⟨k, hk, rfl⟩ := (mem_ofNat_iff js.length q).1 hq
  rw [zfSig_Fld hk] at ha
  rw [zfSig_Pos hk] at hf
  rw [mem_singleton_iff.1 ha, eq_empty_of_mem_function_empty hf]
  exact kpair_mem_iff.mpr ⟨(mem_ofNat_iff js.length _).2 ⟨k, hk, rfl⟩, by simp⟩

/-- `ResIdxDetAt` at member `m`, from the two facts that carry it: `resIdx` is
member-tagged (here by construction, in the real translation by `resIdxVal`), and
the member has one constructor. -/
theorem zfSig_resIdxDetAt {m k₀ : ℕ}
    (hone : ∀ k, ∀ hk : k < js.length, js[k] = m → k = k₀) :
    ResIdxDetAt (zfSig Idx js) (⟨((m : ℕ) : V), ∅⟩ₖ : V) := by
  intro q hq q' hq' a a' h h'
  rw [zfSig_Q] at hq hq'
  obtain ⟨k, hk, rfl⟩ := (mem_ofNat_iff js.length q).1 hq
  obtain ⟨k', hk', rfl⟩ := (mem_ofNat_iff js.length q').1 hq'
  rw [zfSig_resIdx hk] at h
  rw [zfSig_resIdx hk'] at h'
  have e : js[k] = m := ofNat_inj' (kpair_inj h).1
  have e' : js[k'] = m := ofNat_inj' (kpair_inj h').1
  rw [hone k hk e, hone k' hk' e']

/-- **Surjective pairing at member `m` of a `zfSig` block.**  Every hypothesis of
`mem_Ind₃_fibre_iff_of_zero_field` is discharged outright, so the fibre is a
singleton.  Nothing here bounds `js.length`: the block may have any number of
members. -/
theorem zfSig_fibre_iff {m k₀ : ℕ} (hIdx : ∀ j ∈ js, (⟨((j : ℕ) : V), ∅⟩ₖ : V) ∈ Idx)
    (hk₀ : k₀ < js.length) (hm : js[k₀] = m)
    (hone : ∀ k, ∀ hk : k < js.length, js[k] = m → k = k₀) {x : V} :
    (⟨(⟨((m : ℕ) : V), (∅ : V)⟩ₖ : V), x⟩ₖ : V) ∈ Ind₃ (zfSig Idx js) (zfCar js.length) ↔
      x = indCtorVal ((k₀ : ℕ) : V) ∅ ∅ := by
  have hq₀ : (((k₀ : ℕ) : V)) ∈ (zfSig Idx js).Q := by
    rw [zfSig_Q]; exact (mem_ofNat_iff js.length _).2 ⟨k₀, hk₀, rfl⟩
  have hres : (zfSig Idx js).resIdx ((k₀ : ℕ) : V) (∅ : V) = (⟨((m : ℕ) : V), (∅ : V)⟩ₖ : V) := by
    rw [zfSig_resIdx hk₀, hm]
  rw [← hres]
  refine mem_Ind₃_fibre_iff_of_zero_field (zfSig_wf hIdx) zfSig_carrier hq₀ ?_ ?_ ?_ ?_ ?_
  · rw [zfSig_Fld hk₀]; exact mem_singleton_iff.2 rfl
  · rw [zfSig_Args hk₀]; exact mem_singleton_iff.2 rfl
  · rw [hres]; exact zfSig_resIdxDetAt hone
  · intro a _; exact zfSig_Pos hk₀ a
  · intro a ha; rw [zfSig_Fld hk₀] at ha; exact mem_singleton_iff.1 ha

/-! ### The two-member mutual block -/

/-- `Idx` for a two-member block: one index tuple per member. -/
noncomputable def mutIdx : V :=
  insert (⟨((0 : ℕ) : V), (∅ : V)⟩ₖ : V) ({(⟨((1 : ℕ) : V), (∅ : V)⟩ₖ : V)} : V)

theorem mutIdx_mem : ∀ j ∈ [0, 1], (⟨((j : ℕ) : V), ∅⟩ₖ : V) ∈ (mutIdx : V) := by
  intro j hj
  rcases List.mem_cons.1 hj with rfl | hj
  · exact mem_insert.2 (Or.inl rfl)
  · rcases List.mem_cons.1 hj with rfl | hj
    · exact mem_insert.2 (Or.inr (mem_singleton_iff.2 rfl))
    · exact absurd hj nofun

/-- **The model-side `MutNonRec.decl2`**: two block members, one zero-field
constructor each, in one `IndSignature₃`. -/
noncomputable def mutUnitSig : IndSignature₃ V := zfSig (mutIdx : V) [0, 1]

/-- **The block really has two constructors**, so
`IsSubsingletonSignature₃.single` is false at it. -/
theorem mutUnitSig_Q_two : (mutUnitSig (V := V)).Q = ((2 : ℕ) : V) :=
  zfSig_Q (Idx := (mutIdx : V)) (js := [0, 1])

theorem tags_ne : (((0 : ℕ) : V)) ≠ (((1 : ℕ) : V)) := ofNat_ne_ofNat (by omega)

theorem mutUnitSig_mem_Q {k : ℕ} (hk : k < 2) : (((k : ℕ) : V)) ∈ (mutUnitSig (V := V)).Q := by
  rw [mutUnitSig_Q_two]; exact (mem_ofNat_iff 2 _).2 ⟨k, hk, rfl⟩

/-- **`IsSubsingletonSignature₃` is unavailable at the two-type block, for every
carrier** — its `single` field demands one constructor in the *whole* block.  This
is the model-side counterpart of `MutNonRec.decl2_not_isStructure`, and the reason
`Ind₃_subsingleton` cannot be the route to zero-field eta at a mutual block. -/
theorem mutUnitSig_not_single {D : V} :
    ¬ IsSubsingletonSignature₃ (mutUnitSig (V := V)) D := fun h ↦
  tags_ne (h.single _ (mutUnitSig_mem_Q (by omega)) _ (mutUnitSig_mem_Q (by omega)))

/-- **Surjective pairing at the FIRST member of the two-type block.**  Every
hypothesis is discharged outright; the fibre is the singleton
`{indCtorVal 0 ∅ ∅}`. -/
theorem mutUnitSig_fibre_zero {x : V} :
    (⟨(⟨((0 : ℕ) : V), (∅ : V)⟩ₖ : V), x⟩ₖ : V) ∈ Ind₃ (mutUnitSig (V := V)) (zfCar 2) ↔
      x = indCtorVal ((0 : ℕ) : V) ∅ ∅ :=
  zfSig_fibre_iff (Idx := (mutIdx : V)) (js := [0, 1]) (m := 0) (k₀ := 0)
    mutIdx_mem (by simp) rfl (by
      intro k hk hjk
      match k, hk with
      | 0, _ => rfl
      | 1, _ => exact absurd hjk (by simp))

/-- …**and at the second**, so the member index really is doing work — the
model-side counterpart of `MutNonRec.decl2Env_IsStructureG_1`. -/
theorem mutUnitSig_fibre_one {x : V} :
    (⟨(⟨((1 : ℕ) : V), (∅ : V)⟩ₖ : V), x⟩ₖ : V) ∈ Ind₃ (mutUnitSig (V := V)) (zfCar 2) ↔
      x = indCtorVal ((1 : ℕ) : V) ∅ ∅ :=
  zfSig_fibre_iff (Idx := (mutIdx : V)) (js := [0, 1]) (m := 1) (k₀ := 1)
    mutIdx_mem (by simp) rfl (by
      intro k hk hjk
      match k, hk with
      | 0, _ => exact absurd hjk (by simp)
      | 1, _ => rfl)

/-- The two fibres are **distinct** singletons: the members are not identified. -/
theorem mutUnitSig_ctorVal_ne :
    (indCtorVal ((0 : ℕ) : V) ∅ ∅) ≠ (indCtorVal ((1 : ℕ) : V) ∅ ∅) :=
  fun h ↦ tags_ne (kpair_inj h).1

/-- Both fibres are **inhabited**, so neither singleton claim is vacuous. -/
theorem mutUnitSig_fibre_zero_mem :
    (⟨(⟨((0 : ℕ) : V), (∅ : V)⟩ₖ : V), indCtorVal ((0 : ℕ) : V) ∅ ∅⟩ₖ : V)
      ∈ Ind₃ (mutUnitSig (V := V)) (zfCar 2) :=
  mutUnitSig_fibre_zero.2 rfl

theorem mutUnitSig_fibre_one_mem :
    (⟨(⟨((1 : ℕ) : V), (∅ : V)⟩ₖ : V), indCtorVal ((1 : ℕ) : V) ∅ ∅⟩ₖ : V)
      ∈ Ind₃ (mutUnitSig (V := V)) (zfCar 2) :=
  mutUnitSig_fibre_one.2 rfl

/-! ### The negative control: two constructors at ONE member

`zfSig boolIdx [0, 0]` is the same construction with both constructors tagged for
member `0` — a `Bool`-shaped block.  `ResIdxDetAt` fails there, and the fibre
genuinely holds two elements, so `mem_Ind₃_fibre_iff_of_zero_field`'s hypothesis is
load-bearing rather than decorative. -/

noncomputable def boolIdx : V := ({(⟨((0 : ℕ) : V), (∅ : V)⟩ₖ : V)} : V)

theorem boolIdx_mem : ∀ j ∈ [0, 0], (⟨((j : ℕ) : V), ∅⟩ₖ : V) ∈ (boolIdx : V) := by
  intro j hj
  rcases List.mem_cons.1 hj with rfl | hj
  · exact mem_singleton_iff.2 rfl
  · rcases List.mem_cons.1 hj with rfl | hj
    · exact mem_singleton_iff.2 rfl
    · exact absurd hj nofun

theorem boolSig_resIdx {k : ℕ} (hk : k < 2) (a : V) :
    (zfSig (boolIdx : V) [0, 0]).resIdx ((k : ℕ) : V) a = (⟨((0 : ℕ) : V), (∅ : V)⟩ₖ : V) := by
  rw [zfSig_resIdx (Idx := (boolIdx : V)) (js := [0, 0]) (k := k) (by simpa using hk) a]
  match k, hk with
  | 0, _ => rfl
  | 1, _ => rfl

theorem boolSig_mem_Q {k : ℕ} (hk : k < 2) :
    (((k : ℕ) : V)) ∈ (zfSig (boolIdx : V) [0, 0]).Q := by
  rw [zfSig_Q (Idx := (boolIdx : V)) (js := [0, 0])]
  exact (mem_ofNat_iff 2 _).2 ⟨k, by simpa using hk, rfl⟩

/-- **`ResIdxDetAt` is FALSE at the `Bool`-shaped block.** -/
theorem boolSig_not_resIdxDetAt :
    ¬ ResIdxDetAt (zfSig (boolIdx : V) [0, 0]) (⟨((0 : ℕ) : V), (∅ : V)⟩ₖ : V) := fun h ↦
  tags_ne (h _ (boolSig_mem_Q (by omega)) _ (boolSig_mem_Q (by omega)) ∅ ∅
    (boolSig_resIdx (by omega) ∅) (boolSig_resIdx (by omega) ∅))

/-- **…and the failure is real, not merely unproved**: the fibre over the single
index holds two distinct elements, so surjective pairing is FALSE there.  This is
what bounds the positive result the other way. -/
theorem boolSig_fibre_two :
    (⟨(⟨((0 : ℕ) : V), (∅ : V)⟩ₖ : V), indCtorVal ((0 : ℕ) : V) ∅ ∅⟩ₖ : V)
        ∈ Ind₃ (zfSig (boolIdx : V) [0, 0]) (zfCar 2) ∧
      (⟨(⟨((0 : ℕ) : V), (∅ : V)⟩ₖ : V), indCtorVal ((1 : ℕ) : V) ∅ ∅⟩ₖ : V)
        ∈ Ind₃ (zfSig (boolIdx : V) [0, 0]) (zfCar 2) ∧
      (indCtorVal ((0 : ℕ) : V) ∅ ∅) ≠ (indCtorVal ((1 : ℕ) : V) ∅ ∅) := by
  have hwf : (zfSig (boolIdx : V) [0, 0]).toIndSignature₂.WF := zfSig_wf boolIdx_mem
  have hcar : IsIndCarrier₃ (zfSig (boolIdx : V) [0, 0]) (zfCar 2) := by
    have := zfSig_carrier (Idx := (boolIdx : V)) (js := [0, 0])
    simpa using this
  have hmk : ∀ k : ℕ, k < 2 →
      (⟨(⟨((0 : ℕ) : V), (∅ : V)⟩ₖ : V), indCtorVal ((k : ℕ) : V) ∅ ∅⟩ₖ : V)
        ∈ Ind₃ (zfSig (boolIdx : V) [0, 0]) (zfCar 2) := by
    intro k hk
    have hq := boolSig_mem_Q (V := V) hk
    have hpos : (zfSig (boolIdx : V) [0, 0]).Pos ((k : ℕ) : V) (∅ : V) = ∅ :=
      zfSig_Pos (Idx := (boolIdx : V)) (js := [0, 0]) (by simpa using hk) ∅
    have hfld : (∅ : V) ∈ (zfSig (boolIdx : V) [0, 0]).Fld
        (Ind₃ (zfSig (boolIdx : V) [0, 0]) (zfCar 2)) ((k : ℕ) : V) := by
      rw [zfSig_Fld (Idx := (boolIdx : V)) (js := [0, 0]) (by simpa using hk)]
      exact mem_singleton_iff.2 rfl
    have hargs : (⟨(∅ : V), (∅ : V)⟩ₖ : V) ∈ (zfSig (boolIdx : V) [0, 0]).Args
        (Ind₃ (zfSig (boolIdx : V) [0, 0]) (zfCar 2)) ((k : ℕ) : V) := by
      rw [zfSig_Args (Idx := (boolIdx : V)) (js := [0, 0]) (by simpa using hk)]
      exact mem_singleton_iff.2 rfl
    have hf0 : (∅ : V) ∈ ((zfCar 2 : V) ^
        (zfSig (boolIdx : V) [0, 0]).Pos ((k : ℕ) : V) (∅ : V) : V) := by
      rw [hpos]; exact mem_function_iff.mpr ⟨by simp, by simp⟩
    have hmem := ctor_mem_Ind₃ (S := zfSig (boolIdx : V) [0, 0]) (D := zfCar 2)
      (q := ((k : ℕ) : V)) (a := ∅) (f := ∅) hq
      (kpair_mem_iff.mpr ⟨hwf.resIdx_mem _ _ hq _ hfld,
        hcar.ctor_mem _ _ hq _ hfld ∅ hf0 hargs⟩)
      hfld hf0 hargs (fun b hb ↦ by rw [hpos] at hb; exact absurd hb (by simp))
    rw [boolSig_resIdx hk] at hmem
    exact hmem
  exact ⟨hmk 0 (by omega), hmk 1 (by omega), mutUnitSig_ctorVal_ne⟩

end Witness

/-! ## Audit

**Axioms.**  Measured with `#print axioms` on **all 56 declarations**, 2026-09-01: every
one is `[propext, Classical.choice, Quot.sound]`, except `recFields_of_no_fields`
(`[propext, Quot.sound]`) and the five `zfMut*` declarations, four of which depend on
**no axioms at all**.  **No `sorryAx` anywhere**, and nothing here mentions a hole:
the file's only import is `SetModel/CtorTrans.lean`.

**Above-freeness.**  The word `Above` does not occur.  Nothing here chooses a `κ`,
because nothing here needs an inaccessible: the carrier is the finite explicit
`zfCar`, and `mem_Ind₃_iff` / `ctor_mem_Ind₃` take `IsIndCarrier₃` as a
hypothesis rather than a stage.  So the trap of `docs/handoff-setmodel.md` §7.8 is
avoided by not entering it.

**Instrument 7, per declaration, because it is not uniform.**

* *Fires today, unconditionally:* `mutUnitSig_fibre_zero`, `mutUnitSig_fibre_one`,
  `mutUnitSig_fibre_zero_mem`, `mutUnitSig_fibre_one_mem`, `mutUnitSig_ctorVal_ne`,
  `mutUnitSig_not_single`, `boolSig_not_resIdxDetAt`, `boolSig_fibre_two`,
  `zfMutDecl_premises`.  Each is hypothesis-free (beyond the ambient `𝗭𝗙`/`𝗔𝗖`
  instances) and its content is a *specific* set equation or non-equation.
* *Degenerate instance is vacuous, deliberately:* `mem_Ind₃_fibre_iff_of_zero_field`,
  `Ind₃_fibre_subsingleton_of_zero_field`, `resIdxDetAt_of_memberTag`,
  `zfSig_fibre_iff`, `interpSig₃_resIdxDetAt`.  At `S.Q = ∅` — the empty block,
  `js = []` — `hq₀` and the `htag`/`hone` quantifiers are empty, so all of them are
  vacuously true there.  **That is why the `mutUnitSig` instance is the acceptance
  criterion and not `empty`-style consistency**, exactly as `VEnv.empty_unitEta` is
  worthless on its own for `UnitEta`.  Every one of them is instantiated at
  `js = [0, 1]` above, where `Q` is the numeral `2`.
* **Does *not* fire today, and this is structural:** `interpSig₃_fibre_iff_of_no_fields`.
  It takes `hWF : (interpSig₃ …).toIndSignature₂.WF` and
  `hD : IsIndCarrier₃ (interpSig₃ …) Dcar`, which are the model interface's open
  `interpSig_wf` / carrier obligations (`mkIndSignature₃_wf`, `mkIndSignature₃_stage`
  reduce them; `docs/model-interface.md` §2).  Its premises that are about the
  *declaration* do fire — `zfMutDecl_premises` discharges `hck`, `hnf` and `hone` at
  both members of a two-member block — and those are the ones mutuality could have
  broken.  `interpSig₃_resIdx_tagged` and `resIdxVal_tagged` are `rfl`-level and
  unconditional.
* `mkIndSignature₃_Fld` / `_Args` / `_resIdx` / `_Pos` fire at every tag in range;
  `zfSig_*` fire at every `k < js.length`.

**`hone` is not automatic, and there is a real declaration where it fails.**
`InductiveDeclExamples.mutDecl` (`Theory/Inductive/DeclExamples.lean`) is the
mutual block `Tree'`/`Forest'`, whose `ctorsAll` is checked there by `example` to be
`[(0, treeNode), (1, forestNil), (1, forestCons)]`.  `forestNil` **has no fields**,
yet member `1` has two constructors, so `hone` fails at `j = 1` — and correctly so:
`isDefEqUnitLike`'s gate `v.ctors = [cn]` rejects `Forest'`.  *(Read off that file's
`example`s, not re-derived here; importing `Theory/Inductive/DeclExamples.lean` into
the model layer to re-check three list entries is the worse trade.)*

**What this file does not do.**  It does not connect a fibre to
`⟦(const S us).mkApp ps⟧`.  `OracleOK` (`SetModel/Cnst.lean`) has exactly two
fields — `congr`, a level-congruence, and `type`, a **membership** — so
`InductOracleOK` pins no type former's denotation to anything, and a model
satisfying it may interpret a zero-field structure as a two-element set.  Closing
that means *defining* the `.induct` oracle to be `IndFiber ∘ interpSig₃` and adding
the equation as an obligation, which is `docs/soundness-ledger.md`'s standing item
and is **identical for singleton and mutual blocks**. -/

end Lean4Lean.SetModel
