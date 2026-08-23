import Lean4Lean.Theory.SetModel.CtorTrans
import Lean4Lean.Theory.Inductive.DeclExamples

/-!
# The translation, at the declarations that have `WF` witnesses

`Theory/Inductive/DeclExamples.lean` carries four `VInductDecl'.WF` witnesses,
three of them with recursive fields.  This file exercises
`SetModel/CtorTrans.lean` against them, for the reason
`docs/soundness-ledger.md` gives for the witnesses themselves: a side condition
that is only *stated* is worth much less than one an instance satisfies.

Two things are checked, and they are different:

* **the hypothesis is inhabited** — `ctorDataOf` takes a `VIndCtor.WF`, and
  `accIntro_WF` supplies one, so the translation is applied rather than merely
  applicable;
* **the position bookkeeping is right** — `slotDoms` names the *absolute*
  position of each recursive field in a valuation, which is `np + i`, and the
  examples below pin it at declarations whose `np` and field layout differ.
  This is the arithmetic the whole file turns on and it is a closed
  computation, so it is checked by `rfl` rather than argued.
-/

namespace Lean4Lean.SetModel

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open Lean4Lean.InductiveDeclExamples
open scoped Classical

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ} (M : ModelData V) (L : PropSplit envF nv)

/-! ## `Acc` -/

/-- The staged environment the constructors of `accDecl` are checked in. -/
theorem accIndTypes_isSome : (VEnv.empty.addIndTypes accDecl).isSome := by decide

/-- **The constructor well-formedness the translation consumes is inhabited.** -/
theorem accIntro_WF_inst : ∃ env₁, VEnv.empty.addIndTypes accDecl = some env₁ ∧
    accIntro.WF env₁ accDecl 0 accType := by
  obtain ⟨env₁, he⟩ := Option.isSome_iff_exists.1 accIndTypes_isSome
  exact ⟨env₁, he, accDecl_WF.ctors env₁ he 0 accType rfl accIntro (by simp [accType])⟩

/-- The translation, applied. -/
noncomputable def accCtorData (Dcar params : V) : CtorData₃ V :=
  ctorDataOf M L accDecl accIntro_WF_inst.choose_spec.2 Dcar params

/-- `Acc.intro` has one recursive field, so `Pos` has one summand. -/
example (Dcar params : V) : (accCtorData M L Dcar params).poss.length = 1 := rfl

/-- …at absolute position `np + i = 2 + 1`, the last of the four slots of a
valuation `⟨α, r, x, h⟩`. -/
example : ((slotDoms M L accDecl accIntro).map (·.1) : List ℕ) = [3] := rfl

/-- The result index is tagged with the block member it builds — here the only
one. -/
example : accIntro.recFields.length = 1 := rfl

/-! ### `IsSubsingletonSignature₃`, exhibited

`Ind₃_subsingleton` (`SetModel/CtorTrans.lean`) is proved *against*
`IsSubsingletonSignature₃`, and `docs/soundness-ledger.md`'s standing warning
about hypotheses with no instances applies to exactly that.  `Acc` is the family
the ledger names as the one a fillers-in-`a` layout would kill, so it is the
instance that has to be exhibited, and this is it.

**What the four fields cost, at `Acc`.**

* `single` — one constructor, so `Q` is the numeral `1`.
* `posIdx_det` — free at *every* declaration (`interpSig₃_posIdx_indep`): the
  entries of `posIdxVals` are `fun _a x ↦ …`, so `posIdx` never reads `a`.
* `pos_det` — `Pos` reads `a` only through `a ↾ (np + 1) = a ↾ 3`, and `Acc`'s
  result index is its field-0 slot, which is what that prefix adds to the
  parameters.  So `resIdx` determines the prefix on the nose.
* `fld_det` — this is the field the ledger says the layout breaks, and it is
  where `Args` earns its place: the `h` slot is a function on `Pos q a`
  agreeing pointwise with `f`, so `f = f'` forces `h = h'` and the valuation is
  pinned.

**No syntactic hypothesis is used**, and in particular the block-free
replacements `A` are left arbitrary: none of the four fields inspects a field
*domain*, only the shape of the valuation.  The one hypothesis is
`IsSeq params 2`, which `isSeq_params` supplies from any element of
`⟦accDecl.params⟧`, and which is separately satisfiable (`isSeq_two`). -/

/-- `Acc.intro`'s recursive field's `ξ`-domain, as `Pos` and `Args` both see it. -/
noncomputable def accPosDom : V → V := fun a ↦
  (teleFun (teleDomains M L (fldCtx accDecl accIntro 1) accIntroRec.binders)).toFun
    (a ↾ ((3 : ℕ) : V))

theorem accSlotDoms : slotDoms M L accDecl accIntro = [(3, accPosDom M L)] := rfl

theorem accPosDoms : posDoms M L accDecl accIntro = [accPosDom M L] := rfl

/-- Field 0's domain: the block-free replacement for `x : α`. -/
noncomputable def accFldDom0 (A : ℕ → VExpr) : DefFun V :=
  interp M L accDecl.params.reverse (A 0)

/-- Field 1's domain: the plain function set into the carrier. -/
noncomputable def accFldDom1 (Dcar : V) : DefFun V :=
  ⟨fun σ ↦ (Dcar ^ (teleFun (teleDomains M L (fldCtx accDecl accIntro 1)
      accIntroRec.binders)).toFun σ : V), by
    have := (teleFun (teleDomains M L (fldCtx accDecl accIntro 1)
      accIntroRec.binders)).definable
    definability⟩

theorem accFldSet_eq (Dcar params : V) (A : ℕ → VExpr) :
    ctorFldSet M L accDecl Dcar A params accIntro
      = (teleFun [accFldDom0 M L A, accFldDom1 M L Dcar]).toFun params := rfl

/-- **The shape of a field valuation of `Acc.intro`**: the parameters, then the
accessible point `x`, then the predecessor function `h`. -/
theorem mem_accFldSet {Dcar params a : V} {A : ℕ → VExpr} :
    a ∈ ctorFldSet M L accDecl Dcar A params accIntro ↔
      ∃ x ∈ (accFldDom0 M L A).toFun params,
        ∃ y ∈ (accFldDom1 M L Dcar).toFun (snoc params x),
          a = snoc (snoc params x) y := by
  rw [accFldSet_eq, mem_teleFun_cons]
  refine exists_congr fun x ↦ and_congr_right fun _ ↦ ?_
  rw [mem_teleFun_cons]
  exact exists_congr fun y ↦ and_congr_right fun _ ↦ mem_teleFun_nil

/-- `IsSeq params 2` is satisfiable, so the hypothesis below is not empty. -/
theorem isSeq_two : IsSeq (snoc (snoc (∅ : V) ∅) ∅) 2 := isSeq_empty.snoc'.snoc'

section AccSubsingleton

variable {Dcar params : V} {A : ℕ → ℕ → VExpr}

/-- The single constructor tag. -/
theorem accSig_Q : (interpSig₃ M L accDecl Dcar params A).Q = ((1 : ℕ) : V) := rfl

theorem accSig_Fld (W : V) :
    (interpSig₃ M L accDecl Dcar params A).Fld W ((0 : ℕ) : V)
      = ctorFldSet M L accDecl Dcar (A 0) params accIntro := by
  show (if (((0 : ℕ) : V)) = (((0 : ℕ) : V)) then _ else _) = _
  rw [if_pos rfl]
  rfl

theorem accSig_Args (W : V) :
    (interpSig₃ M L accDecl Dcar params A).Args W ((0 : ℕ) : V)
      = argSet Dcar (ctorFldSet M L accDecl Dcar (A 0) params accIntro)
          (fun a ↦ tagUnionF 0 (posDoms M L accDecl accIntro) a)
          (tagUnionF_definable 0 _ (posDoms_definable M L accDecl accIntro))
          (slotDoms M L accDecl accIntro)
          (fun p hp ↦ posDoms_definable M L accDecl accIntro p.2
            (List.mem_map.2 ⟨p, hp, rfl⟩)) := by
  show (if (((0 : ℕ) : V)) = (((0 : ℕ) : V)) then _ else _) = _
  rw [if_pos rfl]
  rfl

theorem accSig_resIdx (a : V) :
    (interpSig₃ M L accDecl Dcar params A).resIdx ((0 : ℕ) : V) a
      = (⟨((0 : ℕ) : V), snoc params (a ‘ ((2 : ℕ) : V))⟩ₖ : V) := by
  show (if (((0 : ℕ) : V)) = (((0 : ℕ) : V)) then _ else _) = _
  rw [if_pos rfl]
  rfl

/-- Every tag of the signature is `0`. -/
theorem accSig_tag {q : V} (hq : q ∈ (interpSig₃ M L accDecl Dcar params A).Q) :
    q = ((0 : ℕ) : V) := by
  obtain ⟨k, hk, rfl⟩ := (mem_ofNat_iff 1 q).1 hq
  rw [show k = 0 from by omega]

/-- **The shape of a field valuation**, in the form the four fields consume. -/
theorem accSig_fld_shape {Dc a : V} (hp : IsSeq params 2)
    (ha : a ∈ (interpSig₃ M L accDecl Dcar params A).Fld
      (Ind₃ (interpSig₃ M L accDecl Dcar params A) Dc) ((0 : ℕ) : V)) :
    ∃ x y : V, a = snoc (snoc params x) y ∧
      (a ↾ ((3 : ℕ) : V)) = snoc params x ∧
      a ‘ ((2 : ℕ) : V) = x ∧ a ‘ ((3 : ℕ) : V) = y := by
  rw [accSig_Fld, mem_accFldSet] at ha
  obtain ⟨x, -, y, -, rfl⟩ := ha
  exact ⟨x, y, rfl, hp.snoc'.restrict_snoc,
    (hp.snoc'.read_lt (by omega)).trans hp.read_top, hp.snoc'.read_top⟩

/-- **The result index determines the prefix `Pos` reads.**  This is the whole
of `pos_det` at `Acc`: `resIdx` is `⟨0, params ⌢ x⟩ₖ` and `a ↾ 3` is
`params ⌢ x`. -/
theorem accSig_prefix_det {Dc a a' : V} (hp : IsSeq params 2)
    (ha : a ∈ (interpSig₃ M L accDecl Dcar params A).Fld
      (Ind₃ (interpSig₃ M L accDecl Dcar params A) Dc) ((0 : ℕ) : V))
    (ha' : a' ∈ (interpSig₃ M L accDecl Dcar params A).Fld
      (Ind₃ (interpSig₃ M L accDecl Dcar params A) Dc) ((0 : ℕ) : V))
    (he : (interpSig₃ M L accDecl Dcar params A).resIdx ((0 : ℕ) : V) a
      = (interpSig₃ M L accDecl Dcar params A).resIdx ((0 : ℕ) : V) a') :
    (a ↾ ((3 : ℕ) : V)) = (a' ↾ ((3 : ℕ) : V)) := by
  obtain ⟨x, y, rfl, hr, h2, -⟩ := accSig_fld_shape M L hp ha
  obtain ⟨x', y', rfl, hr', h2', -⟩ := accSig_fld_shape M L hp ha'
  rw [accSig_resIdx, accSig_resIdx] at he
  rw [hr, hr', ← h2, ← h2', (kpair_inj he).2]

/-- **The recursive slot, read off `Args`.**  This is what the port introduced
`Args` for, at the one declaration the ledger says the layout breaks. -/
theorem accSig_slot {Dc b g : V}
    (hb : (⟨b, g⟩ₖ : V) ∈ (interpSig₃ M L accDecl Dcar params A).Args
      (Ind₃ (interpSig₃ M L accDecl Dcar params A) Dc) ((0 : ℕ) : V)) :
    (b ‘ ((3 : ℕ) : V)) ∈ (Dcar ^ accPosDom M L b : V) ∧
      ∀ z ∈ accPosDom M L b,
        (b ‘ ((3 : ℕ) : V)) ‘ z = g ‘ (⟨((0 : ℕ) : V), z⟩ₖ : V) := by
  rw [accSig_Args, mem_argSet_iff] at hb
  have := argCond_at (Dcar := Dcar) (a := b) (f := g)
    (slotDoms M L accDecl accIntro) 0 0 (3, accPosDom M L) hb.2.2 rfl
  simpa using this

/-- **`fld_det`**: with the domains pinned by the result index and the slot
pinned to `f`, the whole valuation is determined. -/
theorem accSig_fld_det {Dc a a' f f' : V} (hp : IsSeq params 2)
    (ha : a ∈ (interpSig₃ M L accDecl Dcar params A).Fld
      (Ind₃ (interpSig₃ M L accDecl Dcar params A) Dc) ((0 : ℕ) : V))
    (ha' : a' ∈ (interpSig₃ M L accDecl Dcar params A).Fld
      (Ind₃ (interpSig₃ M L accDecl Dcar params A) Dc) ((0 : ℕ) : V))
    (hok : (⟨a, f⟩ₖ : V) ∈ (interpSig₃ M L accDecl Dcar params A).Args
      (Ind₃ (interpSig₃ M L accDecl Dcar params A) Dc) ((0 : ℕ) : V))
    (hok' : (⟨a', f'⟩ₖ : V) ∈ (interpSig₃ M L accDecl Dcar params A).Args
      (Ind₃ (interpSig₃ M L accDecl Dcar params A) Dc) ((0 : ℕ) : V))
    (hqres : (interpSig₃ M L accDecl Dcar params A).resIdx ((0 : ℕ) : V) a
      = (interpSig₃ M L accDecl Dcar params A).resIdx ((0 : ℕ) : V) a')
    (hff : f = f') : a = a' := by
  have hpre3 := accSig_prefix_det M L hp ha ha' hqres
  have hdom : accPosDom M L a = accPosDom M L a' := by
    show (teleFun _).toFun (_ ↾ _) = (teleFun _).toFun (_ ↾ _)
    rw [hpre3]
  obtain ⟨hmem, hval⟩ := accSig_slot M L hok
  obtain ⟨hmem', hval'⟩ := accSig_slot M L hok'
  have hmem'' : (a' ‘ ((3 : ℕ) : V)) ∈ (Dcar ^ accPosDom M L a : V) := by
    rw [hdom]; exact hmem'
  have hslot : (a ‘ ((3 : ℕ) : V)) = (a' ‘ ((3 : ℕ) : V)) := by
    refine function_ext hmem hmem'' fun z hz w hw hzw ↦ ?_
    have hyf : IsFunction (a ‘ ((3 : ℕ) : V)) := IsFunction.of_mem hmem
    have hzv : (a ‘ ((3 : ℕ) : V)) ‘ z = w := value_eq_of_kpair_mem hzw
    have hz' : z ∈ accPosDom M L a' := by rw [← hdom]; exact hz
    have hw' : (a' ‘ ((3 : ℕ) : V)) ‘ z = w := by
      rw [hval' z hz', ← hff, ← hval z hz, hzv]
    rw [← hw']
    exact kpair_value_mem hmem'' hz
  obtain ⟨x, y, hax, hr, h2, hy⟩ := accSig_fld_shape M L hp ha
  obtain ⟨x', y', hax', hr', h2', hy'⟩ := accSig_fld_shape M L hp ha'
  have hxx : x = x' := by
    have hs : (snoc params x : V) = snoc params x' := by rw [← hr, ← hr', hpre3]
    calc x = (snoc params x : V) ‘ ((2 : ℕ) : V) := hp.read_top.symm
      _ = (snoc params x' : V) ‘ ((2 : ℕ) : V) := by rw [hs]
      _ = x' := hp.read_top
  have hyy : y = y' := by rw [← hy, ← hy', hslot]
  rw [hax, hax', hxx, hyy]

/-- **`Acc` satisfies the subsingleton condition.**  Nothing about the
block-free replacements `A` is used. -/
theorem accSig_isSubsingleton (hp : IsSeq params 2) (Dc : V) :
    IsSubsingletonSignature₃ (interpSig₃ M L accDecl Dcar params A) Dc where
  single := by
    intro q hq q' hq'
    rw [accSig_tag M L hq, accSig_tag M L hq']
  pos_det := by
    intro q hq a ha a' ha' hqres
    rw [accSig_tag M L hq] at ha ha' hqres ⊢
    refine interpSig₃_Pos_congr M L accDecl Dcar params A ?_ _
    rintro p hp' P hP
    rw [show p = (0, accIntro) from List.mem_singleton.1 (by exact hp')] at hP
    rw [accPosDoms] at hP
    rw [List.mem_singleton.1 hP]
    show (teleFun _).toFun (a ↾ _) = (teleFun _).toFun (a' ↾ _)
    rw [accSig_prefix_det M L hp ha ha' hqres]
  posIdx_det := by
    intro q _ a _ a' _ _ b
    exact interpSig₃_posIdx_indep M L accDecl Dcar params A q a a' b
  fld_det := by
    intro q hq a ha a' ha' f f' hok hok' hqres hff
    rw [accSig_tag M L hq] at ha ha' hok hok' hqres
    exact accSig_fld_det M L hp ha ha' hok hok' hqres hff

/-! ### The instance, *used*

Having a statement is not being able to apply it, so the instance is run
through the two theorems that consume it.  What is still hypothetical here is
only what **every** declaration owes — `S.WF` (`resIdx a ∈ Idx`) and the carrier
equation — neither of which is about subsingletons. -/

/-- **`Ind₃_subsingleton` at `Acc`**, with the subsingleton hypothesis
discharged rather than assumed. -/
theorem accInd_subsingleton (hp : IsSeq params 2) {Dc : V}
    (hWF : (interpSig₃ M L accDecl Dcar params A).toIndSignature₂.WF)
    (hD : IsIndCarrier₃ (interpSig₃ M L accDecl Dcar params A) Dc) :
    ∀ x i y : V, (⟨i, x⟩ₖ : V) ∈ Ind₃ (interpSig₃ M L accDecl Dcar params A) Dc →
      (⟨i, y⟩ₖ : V) ∈ Ind₃ (interpSig₃ M L accDecl Dcar params A) Dc → x = y :=
  Ind₃_subsingleton hWF hD (accSig_isSubsingleton M L hp Dc)

/-- **Large elimination is sound for `Acc`**: the recursor's value depends only
on the index.  This is the fact `LECond`'s second disjunct is there to license,
and at `Acc` it is now unconditional in the subsingleton hypothesis. -/
theorem accIndRec_indep_of_proof (hp : IsSeq params 2) {Dc R : V}
    {e : V → V → V → V → V} {he : ℒₛₑₜ-function₄[V] e}
    (hWF : (interpSig₃ M L accDecl Dcar params A).toIndSignature₂.WF)
    (hD : IsIndCarrier₃ (interpSig₃ M L accDecl Dcar params A) Dc) {i x y : V}
    (hx : (⟨i, x⟩ₖ : V) ∈ Ind₃ (interpSig₃ M L accDecl Dcar params A) Dc)
    (hy : (⟨i, y⟩ₖ : V) ∈ Ind₃ (interpSig₃ M L accDecl Dcar params A) Dc) :
    indRec₃ (interpSig₃ M L accDecl Dcar params A) Dc R e he (⟨i, x⟩ₖ)
      = indRec₃ (interpSig₃ M L accDecl Dcar params A) Dc R e he (⟨i, y⟩ₖ) :=
  indRec₃_indep_of_proof hWF hD (accSig_isSubsingleton M L hp Dc) hx hy

end AccSubsingleton

/-! ### `Fld ≠ ∅` is not a theorem, and must not be

`exists_mem_args` says `Args` is inhabited *above every element of `Fld`*, and
the obvious worry is that it is vacuous.  The honest answer is that **the
antecedent is not always satisfiable and cannot be made so**: a constructor
whose field types are uninhabited has no applications, which is a fact about the
declaration and not a defect of the translation.  `Acc` over an empty `α` is the
witness, and `Foo := | mk : False → Foo` is the same phenomenon with no
parameters at all.

So the two directions are separated and both proved.  What *would* be a defect —
`Fld` inhabited but `Args` empty above it — is exactly what `exists_mem_args`
rules out, and `accArgs_nonempty` below is that at `Acc` with the antecedent
discharged from the two slot domains rather than assumed. -/

section AccNonvacuous

variable {Dcar params : V} {A : ℕ → VExpr}

/-- Empty first slot, empty `Fld` — no soundness involved. -/
theorem not_mem_accFldSet_of_slot_empty {a : V}
    (h : ∀ x : V, x ∉ (accFldDom0 M L A).toFun params) :
    a ∉ ctorFldSet M L accDecl Dcar A params accIntro := by
  rw [mem_accFldSet]
  rintro ⟨x, hx, -⟩
  exact h x hx

/-- Both slots inhabited, `Fld` inhabited. -/
theorem mem_accFldSet_of_slots {x y : V}
    (hx : x ∈ (accFldDom0 M L A).toFun params)
    (hy : y ∈ (accFldDom1 M L Dcar).toFun (snoc params x)) :
    (snoc (snoc params x) y : V) ∈ ctorFldSet M L accDecl Dcar A params accIntro :=
  (mem_accFldSet M L).2 ⟨x, hx, y, hy, rfl⟩

/-- **`exists_mem_args` with its antecedent discharged.**  Given values for the
two slots there really is an admissible `f`, so the translation's admissibility
condition is satisfiable and not merely stated. -/
theorem accArgs_nonempty {x y W : V} (hp : IsSeq params 2)
    (hx : x ∈ (accFldDom0 M L A).toFun params)
    (hy : y ∈ (accFldDom1 M L Dcar).toFun (snoc params x)) :
    ∃ f ∈ (Dcar ^ tagUnionF 0 (posDoms M L accDecl accIntro)
        (snoc (snoc params x) y) : V),
      (⟨(snoc (snoc params x) y : V), f⟩ₖ : V)
        ∈ (ctorData M L accDecl Dcar params A 0 accIntro).args W :=
  exists_mem_args M L accDecl hp (mem_accFldSet_of_slots M L hx hy)

end AccNonvacuous


/-! ### The reduced `wf` obligation, at `Acc`

`interpSig₃_wf` reduces the assembly's `resIdx a ∈ Idx` to one statement per
constructor.  Running that reduction at a declaration is the check that the
statement it leaves behind is the *right* one, and at `Acc` it collapses to
something recognisable: the result index is the field-0 slot and the index
telescope is `α`, so the whole obligation is

> the block-free replacement for field 0's type denotes what `α` denotes

— i.e. `interp_congr` (`SetModel/SoundInduction.lean`, §4 of
`docs/model-interface.md`), and nothing else.  Note in particular that the
*recursive* field contributes nothing: `resIdx` does not read it. -/

section AccWF

variable {Dcar params : V} {A : ℕ → ℕ → VExpr}

/-- **`S.WF` at `Acc`**, from the one congruence the reduction leaves. -/
theorem accSig_wf (hp : IsSeq params 2)
    (hA : ∀ x : V, x ∈ (accFldDom0 M L (A 0)).toFun params → x ∈ params ‘ ((0 : ℕ) : V)) :
    (interpSig₃ M L accDecl Dcar params A).toIndSignature₂.WF := by
  refine interpSig₃_wf M L accDecl ?_
  rintro (_ | q) j C hq
  · have hjC : (0, accIntro) = (j, C) := by
      have hc : getElem? accDecl.ctorsAll 0 = some (0, accIntro) := rfl
      rw [hc] at hq
      exact Option.some.inj hq
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hjC
    refine ⟨accType, rfl, fun a ha ↦ ?_⟩
    obtain ⟨x, hx, y, -, rfl⟩ := (mem_accFldSet M L).1 ha
    have hread : (snoc (snoc params x) y : V) ‘ ((2 : ℕ) : V) = x :=
      (hp.snoc'.read_lt (by omega)).trans hp.read_top
    refine mem_teleFun_cons.2 ⟨(snoc (snoc params x) y : V) ‘ ((2 : ℕ) : V), ?_,
      mem_teleFun_nil.2 rfl⟩
    show _ ∈ params ‘ ((2 - 1 - 1 : ℕ) : V)
    rw [hread]
    exact hA x hx
  · exact absurd hq (by rw [show getElem? accDecl.ctorsAll (q + 1)
      = (none : Option (Nat × VIndCtor)) from rfl]; simp)

/-- **The two results composed.**  `Acc`'s family is a subsingleton at every
index, with *both* signature hypotheses discharged: the subsingleton condition
outright, `S.WF` from the one congruence.  What is left standing is only
`IsIndCarrier₃`, the carrier equation, which is not specific to `Acc` and is
owed by every declaration. -/
theorem accInd_subsingleton_of_congr (hp : IsSeq params 2)
    (hA : ∀ x : V, x ∈ (accFldDom0 M L (A 0)).toFun params → x ∈ params ‘ ((0 : ℕ) : V))
    {Dc : V} (hD : IsIndCarrier₃ (interpSig₃ M L accDecl Dcar params A) Dc) :
    ∀ x i y : V, (⟨i, x⟩ₖ : V) ∈ Ind₃ (interpSig₃ M L accDecl Dcar params A) Dc →
      (⟨i, y⟩ₖ : V) ∈ Ind₃ (interpSig₃ M L accDecl Dcar params A) Dc → x = y :=
  accInd_subsingleton M L hp (accSig_wf M L hp hA) hD

end AccWF

/-! ## `W'`, the configuration with two recursive fields

`wDecl` is `inductive W' (β : Prop) : Prop | mk : W' β → (β → W' β) → W' β`: one
parameter, both fields recursive.  Its slots are therefore `1` and `2`, and the
second field's `ξ` is non-empty — the configuration `binders_indep` was written
for, and the one where a *blanking* layout would have had to consult it. -/

example : ((slotDoms M L wDecl wMk).map (·.1) : List ℕ) = [1, 2] := rfl

example : wMk.recFields.length = 2 := rfl

/-! ## `Tree'`/`Forest'`, the mutual case

`Forest'.cons` has two recursive fields recursing into *different* members of
the block, and no parameters, so the slots are `0` and `1`. -/

example : ((slotDoms M L mutDecl forestCons).map (·.1) : List ℕ) = [0, 1] := rfl

/-- The two summands carry different member tags, which is what makes `Idx` a
tagged union rather than a plain set. -/
example : (forestCons.recFields.map (·.2.idx) : List ℕ) = [0, 1] := rfl

end Lean4Lean.SetModel
