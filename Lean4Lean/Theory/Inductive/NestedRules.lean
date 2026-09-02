import Lean4Lean.Theory.Inductive.RestoreBridge
-- 2026-09-01: for `VEnv.IsDefEq.betaMkLams` / `mkAppDF` / `HasArgs.toDF`, the multi-β
-- judgement §8.8 closes the β-gap with.  StructureClosed imports only Lemmas/RecApp/
-- Structure, so this adds no cycle through the nested cone.
import Lean4Lean.Theory.Inductive.StructureClosed

/-!
# Part 7: the (B) and (C) bridges — the full restoration as one substitution

`Theory/Inductive/RestoreBridge.lean` Part 4b closes obligation **(A)** of
`VEnv.addInductR_ordered'` for a parameterless nested block:

    (C.type D j).substC σ = (C.typeR D R j).substC σ,        σ = R.csubstTy D K

and Part 6 records why (B) and (C) "need strictly more": they are stated against
`σ' = R.csubst D K`, whose domain holds the companion's **constructor** and **recursor**
names as well as its type name, and those are *outside* `D.blockNames`
(`nfn_csubst_dom_escapes_blockNames`), so no `NoBlock` clause of `VIndCtor.WF` reaches them.

This file supplies what was missing.

* §7.1 a `lookup` toolkit for `csubstList` — a `flatMap`, unlike `csubstTyList`, so the
  bespoke induction Part 2 used does not transfer.  One generic `Nodup`-lookup lemma does the
  work instead.
* §7.2 `csubst`'s domain, both ways: `csubst_dom` (no hypotheses) says every name in it is a
  companion member's type, recursor or constructor name; the three `_eq_some` lemmas need only
  that the domain list has no duplicate key.
* §7.3 `VIndRestore.DomSep` — the **separation** side condition, and the derivation of its
  three `= none` clauses from `D.allNames.Nodup`.
* §7.4 the abstract interface `VIndRestore.SubstAt` / `SubstFree`, and the four head equations
  under it: `tyApp'`, `ctorApp'`, the recursor constant, and their `σ`-invariant restored
  counterparts.  The `ctorApp' → ctorAppR` one is the ingredient (B) and (C) share.
* §7.4b `substC` through a `liftTele` (needs `σ.Closed`, which `csubst_closed'` supplies at
  `D.params = []`), and `getElem?`/`getD` agreement below `D.nm`.
* §7.5 obligation **(B)**: `(D.recType j).substC σ' = (D.recTypeR R j).substC σ'`, via the
  motive telescope, the minor telescope and the shared field-telescope lemma
  `substC_atRec_fieldTypes`.
* §7.6 obligation **(C)**: `(D.iotaRule j q C).substC σ' = (D.iotaRuleR R j q C).substC σ'`,
  head by head over `iotaCtx`/`iotaLhs`/`iotaLam`/`ihValues`/`iotaType`.
* §7.7 the two equations at `σ' = R.csubst D K` — the exact `hbridge` shapes
  `VEnv.recConstsR_wf_of_substC` and `VEnv.iotaRulesRS_wf_of_substC` take — and hence
  `VEnv.recConstsR_wf_of_np_zero` / `VEnv.iotaRulesRS_wf_of_np_zero`: **obligations (B) and (C)
  of `VEnv.addInductR_ordered'`, closed for a parameterless nested block**, on the same
  hypotheses (A) closes on plus `DomSep` and `SubstFree`.
* §7.8 every one of those hypotheses discharged at the `NFn`/`PFn` witness, `SubstFree` field
  by field, and the (C) equation checked to be **not** an identity.

Everything here is at `D.params = []`, the same reach Part 4b has: above it the two sides
differ by the β-gap of Part 3 (`substC_tyApp_comp` / `instAll_tyBody`), which is a *typed*
residual and not a syntactic one.

**Ruling 122e landed: §7.5/§7.6 no longer take `hcanon : D.Canonical`.**  They used to, exactly
as Part 4b's (A) bridge did, and the hypothesis is machine-checked **false** at the block level
for every real nested declaration in the running environment
(`MRedex.MRWit.mr_auxNodeB_block_not_canonical`), so the whole layer was *vacuous* there.  The
restatement is over the **stored** telescope — `VIndRestore.substC_atRec_restore`, which has no
side condition at all — and the anti-vacuity certificate is
`Theory/Inductive/StoredIota.lean`: every remaining hypothesis of §7.5/§7.6/§7.7 discharged at
`mrAux mrAuxNodeB`, the block `Canonical` is false at.

**What is still open.**  The index bound `hpos` remains (it *is* true at the redex block —
`MRWit.mrAuxB_pos` — and follows from `D.WF env` by `VIndField.WF.recArg_noBlock`; that
derivation is the consumers' business, not the bridges').  `DomNodup` is still a `decide`-able
side condition (§7.2), and the β-gap above `D.params = []` is untouched.
-/

namespace Lean4Lean

open Lean (Name)
open VExpr (mkPi mkLams mkApp bvars instAll liftTele shift shiftTele)

/-- `instL` on a constant, as a rewrite rule.  (`VInductDecl'.atRec_const` is the `selfLvls`
instance; the general one is not in the import chain at the pin.) -/
theorem VExpr.instL_const' {c : Name} {ls ls' : List VLevel} :
    (VExpr.const c ls).instL ls' = .const c (ls.map (VLevel.inst ls')) := rfl

/-- `VIndRestore.recVal` is a bare constant, so `instL` only moves its level list. -/
theorem VIndRestore.recVal_instL (R : VIndRestore) (D : VInductDecl') (n : Name)
    (ls : List VLevel) :
    (R.recVal D n).instL ls
      = .const (R.recName n) ((VLevel.params D.recUvars).map (VLevel.inst ls)) := rfl

/-! ## §7.1 `List.lookup` at a duplicate-free domain -/

/-- If the keys of an association list are distinct, `lookup` finds any entry.  (Core has the
`isSome`/`mem` directions at the pin but not this one.) -/
theorem List.lookup_eq_some_of_nodup {β : Type _} :
    ∀ {l : List (Name × β)} {n : Name} {v : β},
      (l.map (·.1)).Nodup → (n, v) ∈ l → l.lookup n = some v
  | [], _, _, _, hm => absurd hm nofun
  | (a, b) :: l, n, v, hnd, hm => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [List.lookup_cons]
    rcases List.mem_cons.1 hm with he | hm
    · cases he; simp
    · have hne : n ≠ a := fun h => hnd.1 (h ▸ List.mem_map.2 ⟨(n, v), hm, rfl⟩)
      rw [show (n == a) = false from beq_eq_false_iff_ne.2 hne]
      exact lookup_eq_some_of_nodup hnd.2 hm

/-- A `Nodup`-of-image list has an injective indexing function on its own members. -/
theorem List.nodup_map_inj {α β : Type _} {f : α → β} :
    ∀ {l : List α}, (l.map f).Nodup → ∀ {a b : α}, a ∈ l → b ∈ l → f a = f b → a = b
  | [], _, _, _, ha, _, _ => absurd ha nofun
  | c :: l, hnd, a, b, ha, hb, he => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.1 ha with rfl | ha'
    · rcases List.mem_cons.1 hb with rfl | hb'
      · rfl
      · exact absurd (by rw [he]; exact List.mem_map.2 ⟨b, hb', rfl⟩) hnd.1
    · rcases List.mem_cons.1 hb with rfl | hb'
      · exact absurd (by rw [← he]; exact List.mem_map.2 ⟨a, ha', rfl⟩) hnd.1
      · exact List.nodup_map_inj hnd.2 ha' hb' he

/-! ## §7.2 `csubst`'s domain, both ways

`VIndRestore.csubstList` is a **`flatMap`**: three entries per companion member (its type, its
recursor, each of its constructors).  `csubstTyList` is a `map`, which is why Part 2's bespoke
`lookup_csubstTyList_aux` induction does not transfer — the generic §7.1 lemma is used instead,
against the hypothesis that the *whole* key list is `Nodup`. -/

namespace VIndRestore
variable {R : VIndRestore} {D : VInductDecl'} {K : List Name}

/-- The three entries `csubstList` contributes for one companion member. -/
def csubstEntries (R : VIndRestore) (D : VInductDecl') (T : VIndType) (j : Nat) :
    List (Name × VExpr) :=
  (T.name, R.tyVal D j) ::
  (Lean.mkRecName T.name, R.recVal D (Lean.mkRecName T.name)) ::
  T.ctors.map fun C => (C.name, R.ctorVal D j C)

theorem csubstList_eq (R : VIndRestore) (D : VInductDecl') (K : List Name) :
    R.csubstList D K
      = (D.types.zipIdx.filter fun p => decide (p.1.name ∈ K)).flatMap
          fun (T, j) => R.csubstEntries D T j := rfl

/-- Any entry `csubstList` contributes for a companion member really is in it. -/
theorem mem_csubstList {j : Nat} {T : VIndType} (hT : D.types[j]? = some T) (hK : T.name ∈ K)
    {p : Name × VExpr} (hp : p ∈ R.csubstEntries D T j) : p ∈ R.csubstList D K := by
  rw [csubstList_eq, List.mem_flatMap]
  exact ⟨(T, j), List.mem_filter.2 ⟨List.mk_mem_zipIdx_iff_getElem?.2 hT, decide_eq_true hK⟩, hp⟩

/-- **Every name in `csubst`'s domain belongs to a companion member** — as its own name, its
recursor's name, or one of its constructors' names — and the value is the presented one.  No
hypothesis: this is `List.lookup_mem` unfolded. -/
theorem csubst_dom {n : Name} {v : VExpr} (h : R.csubst D K n = some v) :
    ∃ (j : Nat) (T : VIndType), D.types[j]? = some T ∧ T.name ∈ K ∧
      ((n = T.name ∧ v = R.tyVal D j) ∨
        (n = Lean.mkRecName T.name ∧ v = R.recVal D (Lean.mkRecName T.name)) ∨
        (∃ C ∈ T.ctors, n = C.name ∧ v = R.ctorVal D j C)) := by
  have h := Lean4Lean.List.lookup_mem h
  rw [csubstList_eq, List.mem_flatMap] at h
  obtain ⟨⟨T, j⟩, hmem, hp⟩ := h
  rw [List.mem_filter] at hmem
  obtain ⟨hz, hd⟩ := hmem
  refine ⟨j, T, List.mk_mem_zipIdx_iff_getElem?.1 hz, of_decide_eq_true hd, ?_⟩
  simp only [csubstEntries] at hp
  simp only [List.mem_cons, List.mem_map] at hp
  obtain h | h | ⟨C, hC, h⟩ := hp
  · cases h; exact .inl ⟨rfl, rfl⟩
  · cases h; exact .inr (.inl ⟨rfl, rfl⟩)
  · cases h; exact .inr (.inr ⟨C, hC, rfl, rfl⟩)

/-- **The domain list has no duplicate key.**  Stated separately from `DomSep` below because
it is all the three `_eq_some` lemmas need.

It is **not** derived from `D.allNames.Nodup` here (see `domSep_of_allNames_nodup`): it is
morally a consequence — the three key families `csubstList` interleaves are three sublists of
`allNames` — but the interleaving argument is a permutation-of-`flatMap` fact that is not
written, so this stays a `decide`-able side condition. -/
def DomNodup (R : VIndRestore) (D : VInductDecl') (K : List Name) : Prop :=
  ((R.csubstList D K).map (·.1)).Nodup

theorem csubst_ty_eq_some (hnd : R.DomNodup D K) {j : Nat} {T : VIndType}
    (hT : D.types[j]? = some T) (hK : T.name ∈ K) :
    R.csubst D K T.name = some (R.tyVal D j) :=
  Lean4Lean.List.lookup_eq_some_of_nodup hnd (mem_csubstList hT hK List.mem_cons_self)

theorem csubst_rec_eq_some (hnd : R.DomNodup D K) {j : Nat} {T : VIndType}
    (hT : D.types[j]? = some T) (hK : T.name ∈ K) :
    R.csubst D K (Lean.mkRecName T.name)
      = some (R.recVal D (Lean.mkRecName T.name)) :=
  Lean4Lean.List.lookup_eq_some_of_nodup hnd
    (mem_csubstList hT hK (List.mem_cons_of_mem _ List.mem_cons_self))

theorem csubst_ctor_eq_some (hnd : R.DomNodup D K) {j : Nat} {T : VIndType}
    (hT : D.types[j]? = some T) (hK : T.name ∈ K) {C : VIndCtor} (hC : C ∈ T.ctors) :
    R.csubst D K C.name = some (R.ctorVal D j C) :=
  Lean4Lean.List.lookup_eq_some_of_nodup hnd
    (mem_csubstList hT hK (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_map.2 ⟨C, hC, rfl⟩))))

end VIndRestore

/-! ## §7.3 The separation side condition, and where it comes from

The `_eq_some` lemmas need only `DomNodup`.  The `= none` direction needs more, and the extra
is genuinely about **name separation between the three families**: nothing in `Faithful` +
`OwnId` forbids a *declared* member's recursor name from being literally a *companion*
member's constructor name, in which case `csubst` would rewrite the head of a rule the step
declares under its own name.  `VIndRestore.KeysFree` (`Theory/Inductive/Restore.lean`) is the
same phenomenon one level up, at the restored names.

The separation is packaged as `VIndRestore.DomSep` and its three `= none` clauses are
**derived** from a single fact about the block: `D.allNames.Nodup`, i.e. the auxiliary block's
own type, constructor and recursor names are pairwise distinct.  That is not a new assumption —
it is exactly what `VEnv.addConstList D.allConsts` requires, so any block `addInduct'` could
ever accept has it, and `VEnv.WF'.induct_allNames_nodup` (`Theory/Inductive/Nested.lean`)
extracts it from a declaration history. -/

namespace VInductDecl'
variable (D : VInductDecl')

theorem recConsts_names :
    D.recConsts.map (·.1) = D.types.map (fun T => Lean.mkRecName T.name) := by
  rw [VInductDecl'.recConsts, List.map_map,
    show ((fun c : Name × VConstant => c.1) ∘
        fun p : VIndType × Nat => (Lean.mkRecName p.1.name, (⟨D.recUvars, D.recType p.2⟩ : VConstant)))
      = ((fun T : VIndType => Lean.mkRecName T.name) ∘ Prod.fst) from rfl,
    ← List.map_map, List.zipIdx_map_fst]

theorem ctorConsts_names :
    D.ctorConsts.map (·.1) = D.ctorsAll.map (fun p => p.2.name) := by
  rw [VInductDecl'.ctorConsts, List.map_map]; rfl

theorem blockNames_eq : D.blockNames = D.types.map (·.name) := rfl

end VInductDecl'

namespace VIndRestore
variable {R : VIndRestore} {D : VInductDecl'} {K : List Name}

/-- **The separation the `= none` direction needs.**  Off `K`, none of the block's own three
name families meets `csubst`'s domain. -/
structure DomSep (R : VIndRestore) (D : VInductDecl') (K : List Name) : Prop where
  nodup : R.DomNodup D K
  tyOff : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∉ K →
    R.csubst D K T.name = none
  recOff : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∉ K →
    R.csubst D K (Lean.mkRecName T.name) = none
  ctorOff : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∉ K →
    ∀ C ∈ T.ctors, R.csubst D K C.name = none

/-- At `K = []` there is nothing to separate. -/
theorem domSep_nil (R : VIndRestore) (D : VInductDecl') : R.DomSep D [] where
  nodup := by
    show ((R.csubstList D []).map _).Nodup
    rw [csubstList_eq,
      show (D.types.zipIdx.filter fun p => decide (p.1.name ∈ ([] : List Name))) = [] from
        List.filter_eq_nil_iff.2 (by simp)]
    exact List.nodup_nil
  tyOff _ _ _ _ := by rw [R.csubst_nil D]; rfl
  recOff _ _ _ _ := by rw [R.csubst_nil D]; rfl
  ctorOff _ _ _ _ _ _ := by rw [R.csubst_nil D]; rfl

/-- **The three `= none` clauses are derivable — from the auxiliary block's own `Nodup`.**

`DomNodup` is *not* derived here; the three `= none` clauses are.  **These are not the same
phenomenon as `VIndRestore.KeysFree`**, which is the genuinely non-derivable one: `KeysFree`
is about the **restored** names `R.recName …` / `R.ctorName …`, which no step declares, so
freshness cannot separate them; the clauses below are about the block's **own** three name
families, which `allNames` does contain.  An earlier revision of this docstring conflated the
two.  What discharges them is `D.allNames.Nodup`: the three families it
concatenates are pairwise disjoint and individually duplicate-free, which is exactly the
separation `csubst_dom`'s three-way disjunction has to be refuted with. -/
theorem domSep_of_allNames_nodup (hnd0 : D.allNames.Nodup) (hdn : R.DomNodup D K) :
    R.DomSep D K := by
  have hnd := hnd0
  rw [VInductDecl'.allConsts_names, D.ctorConsts_names, D.recConsts_names,
    VInductDecl'.blockNames_eq] at hnd
  have hABC := List.nodup_append.1 hnd
  have hAB := List.nodup_append.1 hABC.1
  have hB := hAB.2.1
  have hC := hABC.2.1
  have hmA : ∀ {j : Nat} {T : VIndType}, D.types[j]? = some T →
      T.name ∈ D.types.map (fun T : VIndType => T.name) :=
    fun hT => List.mem_map.2 ⟨_, List.mem_of_getElem? hT, rfl⟩
  have hmC : ∀ {j : Nat} {T : VIndType}, D.types[j]? = some T →
      Lean.mkRecName T.name ∈ D.types.map (fun T : VIndType => Lean.mkRecName T.name) :=
    fun hT => List.mem_map.2 ⟨_, List.mem_of_getElem? hT, rfl⟩
  have hmB : ∀ {j : Nat} {T : VIndType} {C' : VIndCtor}, D.types[j]? = some T → C' ∈ T.ctors →
      C'.name ∈ D.ctorsAll.map (fun p : Nat × VIndCtor => p.2.name) :=
    fun hT hC' => List.mem_map.2 ⟨_, VInductDecl'.mem_ctorsAll_of hT hC', rfl⟩
  refine ⟨hdn, ?_, ?_, ?_⟩
  · intro j T hT hK
    cases hc : R.csubst D K T.name with
    | none => rfl
    | some v =>
      obtain ⟨j₀, T₀, hT₀, hK₀, ⟨h, -⟩ | ⟨h, -⟩ | ⟨C₀, hC₀, h, -⟩⟩ := csubst_dom hc
      · exact absurd (by rw [h]; exact hK₀) hK
      · exact (hABC.2.2 _ (List.mem_append_left _ (hmA hT)) _ (hmC hT₀) h).elim
      · exact (hAB.2.2 _ (hmA hT) _ (hmB hT₀ hC₀) h).elim
  · intro j T hT hK
    cases hc : R.csubst D K (Lean.mkRecName T.name) with
    | none => rfl
    | some v =>
      obtain ⟨j₀, T₀, hT₀, hK₀, ⟨h, -⟩ | ⟨h, -⟩ | ⟨C₀, hC₀, h, -⟩⟩ := csubst_dom hc
      · exact (hABC.2.2 _ (List.mem_append_left _ (hmA hT₀)) _ (hmC hT) h.symm).elim
      · have : T = T₀ :=
          Lean4Lean.List.nodup_map_inj hC (List.mem_of_getElem? hT) (List.mem_of_getElem? hT₀) h
        exact absurd (this ▸ hK₀) hK
      · exact (hABC.2.2 _ (List.mem_append_right _ (hmB hT₀ hC₀)) _ (hmC hT) h.symm).elim
  · intro j T hT hK C' hC'
    cases hc : R.csubst D K C'.name with
    | none => rfl
    | some v =>
      obtain ⟨j₀, T₀, hT₀, hK₀, ⟨h, -⟩ | ⟨h, -⟩ | ⟨C₀, hC₀, h, -⟩⟩ := csubst_dom hc
      · exact (hAB.2.2 _ (hmA hT₀) _ (hmB hT hC') h.symm).elim
      · exact (hABC.2.2 _ (List.mem_append_right _ (hmB hT hC')) _ (hmC hT₀) h).elim
      · have hpair : ((j, C') : Nat × VIndCtor) = (j₀, C₀) :=
          Lean4Lean.List.nodup_map_inj hB (VInductDecl'.mem_ctorsAll_of hT hC')
            (VInductDecl'.mem_ctorsAll_of hT₀ hC₀) h
        cases hpair
        rw [hT] at hT₀; cases hT₀
        exact absurd hK₀ hK

end VIndRestore


/-! ## §7.4 The substitution interface, and the head equations

Part 4b's head equations are stated at `R.csubstTy D K` and use `csubstTy_eq_some` /
`csubstTy_eq_none` directly.  (B) and (C) need the same equations at `R.csubst D K`, so the six
facts a bridge actually consumes are isolated as `VIndRestore.SubstAt` and the invariance of the
*restored* heads as `VIndRestore.SubstFree`.  `DomSep.substAt` instantiates the first at
`csubst`; `SubstFree` is the `hnn`/`hna` pair of Part 4b together with the two clauses of
`VIndRestore.KeysFree`. -/

namespace VIndRestore
variable {R : VIndRestore} {D : VInductDecl'} {K : List Name} {σ : CSubst}

/-- **What a bridge proof uses about the substitution**: on a companion member it is the
presented value, off `K` it is undefined — for each of the three name families. -/
structure SubstAt (R : VIndRestore) (D : VInductDecl') (K : List Name) (σ : CSubst) : Prop where
  tySome : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K →
    σ T.name = some (R.tyVal D j)
  tyNone : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∉ K → σ T.name = none
  recSome : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K →
    σ (Lean.mkRecName T.name) = some (R.recVal D (Lean.mkRecName T.name))
  recNone : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∉ K →
    σ (Lean.mkRecName T.name) = none
  ctorSome : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K →
    ∀ C ∈ T.ctors, σ C.name = some (R.ctorVal D j C)
  ctorNone : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∉ K →
    ∀ C ∈ T.ctors, σ C.name = none

/-- `DomSep` is exactly `SubstAt` at the real substitution. -/
theorem DomSep.substAt (h : R.DomSep D K) : R.SubstAt D K (R.csubst D K) where
  tySome _ _ hT hK := csubst_ty_eq_some h.nodup hT hK
  tyNone := h.tyOff
  recSome _ _ hT hK := csubst_rec_eq_some h.nodup hT hK
  recNone := h.recOff
  ctorSome _ _ hT hK _ hC := csubst_ctor_eq_some h.nodup hT hK hC
  ctorNone := h.ctorOff

/-- **The restoration's own heads escape the substitution.**

`tyName`/`tyArgs` are Part 4b's `hnn`/`hna`.  `recName`/`ctorName` are the two clauses of
`VIndRestore.KeysFree` — and this is a second, independent consumer of them: `KeysFree` was
introduced for `VInductDecl'.key_iotaRuleR_substC`, but the (C) *bridge* needs it too, because
`iotaLhsR`/`ihValuesR`/`iotaTypeR` are headed by the restored recursor and constructor and the
right-hand side of the bridge carries a `substC σ`.

**`recName` here is quantified over every member `j`, not over `D.ctorsAll`.**
`VIndRestore.KeysFree` quantifies over `D.ctorsAll`, so it says nothing about a member with no
constructors — and `VInductDecl'.ihValuesR` calls the renamed recursor of `r.idx`, a
*recursive field's target*, which need not have constructors.  So the bridge needs a strictly
stronger clause than `KeysFree` supplies. -/
structure SubstFree (R : VIndRestore) (D : VInductDecl') (σ : CSubst) : Prop where
  tyName : ∀ j, σ (R.tyName j) = none
  tyArgs : ∀ j, ∀ a ∈ R.tyArgs j, a.NoCSubst σ
  recName : ∀ j, σ (R.recName (Lean.mkRecName (D.types.getD j default).name)) = none
  ctorName : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → ∀ C ∈ T.ctors,
    σ (R.ctorName C.name) = none

/-- `SubstFree`'s two name clauses imply `KeysFree` at the same `σ = R.csubst D K`. -/
theorem SubstFree.keysFree (h : R.SubstFree D (R.csubst D K)) : R.KeysFree D K := by
  intro p hp
  obtain ⟨T, hT, hC⟩ := VInductDecl'.mem_ctorsAll hp
  exact ⟨h.recName p.1, h.ctorName p.1 T hT p.2 hC⟩

/-! ### The `OwnId` collapses at the recursor's universe numbering -/

theorem OwnId.tyAppR'_eq (h : R.OwnId D K) {j : Nat} {T : VIndType}
    (hT : D.types[j]? = some T) (hK : T.name ∉ K) (k : Nat) (args : List VExpr) :
    D.tyAppR' R j k args = D.tyApp' j k args := by
  have hg : D.types.getD j default = T := by rw [List.getD_eq_getElem?_getD, hT]; rfl
  rw [VInductDecl'.tyAppR', h.tyName j T hT hK, h.tyLvls j T hT hK, h.tyArgs j T hT hK,
    VInductDecl'.ownLvls_inst_selfLvls, VInductDecl'.atRecTele, VExpr.map_instL_bvars,
    ← hg, VInductDecl'.tyAppH_bvars']

theorem OwnId.ctorAppR_eq (h : R.OwnId D K) {j : Nat} {T : VIndType}
    (hT : D.types[j]? = some T) (hK : T.name ∉ K) {C : VIndCtor} (hC : C ∈ T.ctors)
    (k : Nat) (args : List VExpr) :
    D.ctorAppR R j C k args = D.ctorApp' C k args := by
  rw [VInductDecl'.ctorAppR, h.ctorName j T hT hK C hC, h.tyLvls j T hT hK,
    h.tyArgs j T hT hK, VInductDecl'.ownLvls_inst_selfLvls, VInductDecl'.atRecTele,
    VExpr.map_instL_bvars, VExpr.map_liftN_bvars_lo (Nat.le_refl 0), Nat.add_zero,
    VInductDecl'.ctorApp']

/-! ### The four head equations

`hp : D.params = []` is the absence of the β-gap, exactly as in Part 4b; `hcl0` is the
closedness of the presented spine that makes the `liftN` in `tyAppH` disappear. -/

section
variable (hp : D.params = []) (hown : R.OwnId D K) (hat : R.SubstAt D K σ)
  (hcl0 : ∀ i, ∀ a ∈ R.tyArgs i, a.ClosedN 0)

include hp hown hat hcl0

/-- **The `tyApp'` head equation**, at the recursor's universe numbering.  Compare
`substC_tyApp_eq_tyAppR_map`: no `LevelWF` hypothesis is needed here, because the value is
re-instantiated at `D.selfLvls` and `tyAppR'` is defined at exactly that instantiation. -/
theorem substC_tyApp'_eq_tyAppR' {j : Nat} {T : VIndType} (hT : D.types[j]? = some T)
    (k : Nat) (args : List VExpr) :
    (D.tyApp' j k args).substC σ = D.tyAppR' R j k (args.map (VExpr.substC · σ)) := by
  have hnp : D.np = 0 := by rw [show D.np = D.params.length from rfl, hp]; rfl
  have hg : (D.types.getD j default).name = T.name := by
    rw [List.getD_eq_getElem?_getD, hT]; rfl
  have hid : ((D.atRecTele (R.tyArgs j)).map fun x => x.liftN k)
      = D.atRecTele (R.tyArgs j) := by
    rw [show ((D.atRecTele (R.tyArgs j)).map fun x => x.liftN k)
          = (D.atRecTele (R.tyArgs j)).map id from
        List.map_congr_left fun a ha => by
          obtain ⟨a₀, ha₀, rfl⟩ := List.mem_map.1 ha
          exact ((hcl0 j a₀ ha₀).instL).liftN_eq (Nat.zero_le _),
      List.map_id]
  rw [VInductDecl'.tyApp', VExpr.substC_mkApp, List.map_append, VExpr.map_substC_bvars,
    hnp, VExpr.bvars_zero, List.nil_append]
  by_cases hK : T.name ∈ K
  · rw [VExpr.substC_const_some (by rw [hg]; exact hat.tySome j T hT hK), tyVal_eq, hp,
      VExpr.mkLams_nil, tyBody, VExpr.instL_mkApp, VExpr.instL_const',
      VInductDecl'.tyAppR', VInductDecl'.tyAppH, ← VExpr.mkApp_append, hid,
      VInductDecl'.atRecTele]
  · rw [VExpr.substC_const_none (by rw [hg]; exact hat.tyNone j T hT hK),
      hown.tyAppR'_eq hT hK, VInductDecl'.tyApp', hnp, VExpr.bvars_zero, List.nil_append]

/-- **The `ctorApp'` head equation** — the ingredient (B) and (C) share. -/
theorem substC_ctorApp'_eq_ctorAppR {j : Nat} {T : VIndType} (hT : D.types[j]? = some T)
    {C : VIndCtor} (hC : C ∈ T.ctors) (k : Nat) (args : List VExpr) :
    (D.ctorApp' C k args).substC σ = D.ctorAppR R j C k (args.map (VExpr.substC · σ)) := by
  have hnp : D.np = 0 := by rw [show D.np = D.params.length from rfl, hp]; rfl
  have hid : ((D.atRecTele (R.tyArgs j)).map fun x => x.liftN k)
      = D.atRecTele (R.tyArgs j) := by
    rw [show ((D.atRecTele (R.tyArgs j)).map fun x => x.liftN k)
          = (D.atRecTele (R.tyArgs j)).map id from
        List.map_congr_left fun a ha => by
          obtain ⟨a₀, ha₀, rfl⟩ := List.mem_map.1 ha
          exact ((hcl0 j a₀ ha₀).instL).liftN_eq (Nat.zero_le _),
      List.map_id]
  rw [VInductDecl'.ctorApp', VExpr.substC_mkApp, List.map_append, VExpr.map_substC_bvars,
    hnp, VExpr.bvars_zero, List.nil_append]
  by_cases hK : T.name ∈ K
  · rw [VExpr.substC_const_some (hat.ctorSome j T hT hK C hC), ctorVal, hp,
      VExpr.mkLams_nil, VExpr.instL_mkApp, VExpr.instL_const',
      VInductDecl'.ctorAppR, ← VExpr.mkApp_append, hid, VInductDecl'.atRecTele]
  · rw [VExpr.substC_const_none (hat.ctorNone j T hT hK C hC),
      hown.ctorAppR_eq hT hK hC, VInductDecl'.ctorApp', hnp, VExpr.bvars_zero,
      List.nil_append]

omit hp hcl0 in
/-- **The recursor-constant head equation.**  `mkAuxRecNameMap` only renames, so this is the
one head where the substitution's value is a constant rather than an application. -/
theorem substC_recConst {j : Nat} {T : VIndType} (hT : D.types[j]? = some T) :
    (VExpr.const (Lean.mkRecName (D.types.getD j default).name)
        (VLevel.params D.recUvars)).substC σ
      = .const (R.recName (Lean.mkRecName (D.types.getD j default).name))
          (VLevel.params D.recUvars) := by
  have hg : D.types.getD j default = T := by rw [List.getD_eq_getElem?_getD, hT]; rfl
  by_cases hK : T.name ∈ K
  · rw [VExpr.substC_const_some (by rw [hg]; exact hat.recSome j T hT hK),
      recVal_instL, VLevel.inst_map_id VLevel.params_length, hg]
  · rw [VExpr.substC_const_none (by rw [hg]; exact hat.recNone j T hT hK), hg,
      hown.recName j T hT hK]

end

/-! ### …and the restored heads are `σ`-invariant -/

section
variable (hfr : R.SubstFree D σ) (hcl0 : ∀ i, ∀ a ∈ R.tyArgs i, a.ClosedN 0)

include hfr

theorem substC_tyAppR' (j k : Nat) (args : List VExpr) :
    (D.tyAppR' R j k args).substC σ = D.tyAppR' R j k (args.map (VExpr.substC · σ)) := by
  rw [VInductDecl'.tyAppR', VInductDecl'.tyAppH, VExpr.substC_mkApp,
    VExpr.substC_const_none (hfr.tyName j), List.map_append, List.map_map]
  congr 2
  refine List.map_congr_left fun a ha => ?_
  obtain ⟨a₀, ha₀, rfl⟩ := List.mem_map.1 ha
  exact (((hfr.tyArgs j a₀ ha₀).instL).liftN).substC_eq

theorem substC_ctorAppR {j : Nat} {T : VIndType} (hT : D.types[j]? = some T)
    {C : VIndCtor} (hC : C ∈ T.ctors) (k : Nat) (args : List VExpr) :
    (D.ctorAppR R j C k args).substC σ
      = D.ctorAppR R j C k (args.map (VExpr.substC · σ)) := by
  rw [VInductDecl'.ctorAppR, VExpr.substC_mkApp,
    VExpr.substC_const_none (hfr.ctorName j T hT C hC), List.map_append, List.map_map]
  congr 2
  refine List.map_congr_left fun a ha => ?_
  obtain ⟨a₀, ha₀, rfl⟩ := List.mem_map.1 ha
  exact (((hfr.tyArgs j a₀ ha₀).instL).liftN).substC_eq

theorem substC_recConstR (j : Nat) :
    (VExpr.const (R.recName (Lean.mkRecName (D.types.getD j default).name))
        (VLevel.params D.recUvars)).substC σ
      = .const (R.recName (Lean.mkRecName (D.types.getD j default).name))
          (VLevel.params D.recUvars) :=
  VExpr.substC_const_none (hfr.recName j)

end

end VIndRestore

/-! ## §7.4b Three small facts the two bridges need

`substC` commutes with `liftN` **only** because `csubst`'s values are closed
(`VExpr.substC_liftN`), and the recursor construction splices every stored telescope through
`liftTele`, so the commutation has to be lifted to telescopes.  `csubst_closed'` is
`VIndRestore.csubst_closed` (`Theory/Typing/ConstSubstNested.lean`) at the reach §7.4 works
in. -/

namespace VExpr

/-- `substC` through a `liftTele`.  `σ.Closed` is not decoration: at a non-closed value the
equation fails at the first binder. -/
theorem map_substC_liftTele {σ : CSubst} (hσ : σ.Closed) : ∀ {As : List VExpr} {n k : Nat},
    (liftTele n As k).map (VExpr.substC · σ) = liftTele n (As.map (VExpr.substC · σ)) k
  | [], _, _ => rfl
  | A :: As, n, k => by
    rw [VExpr.liftTele_cons, List.map_cons, List.map_cons, VExpr.liftTele_cons,
      substC_liftN hσ, map_substC_liftTele hσ (As := As)]

end VExpr

namespace VInductDecl'

/-- `D.types.getD` and `D.types[·]?` agree below `D.nm` — the shape the §7.4 head equations
want their `hT` in when the index comes from `List.range D.nm`. -/
theorem getElem?_types_getD {D : VInductDecl'} {t : Nat} (h : t < D.nm) :
    D.types[t]? = some (D.types.getD t default) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl

/-- **The trigger only reports members that exist.**  `uniformOcc?` reads its index off
`memberIdx`, which is a lookup in `D.blockNames`, so `hT` — the hypothesis every §7.4 head
equation wants — comes *free* with the trigger firing.  This is what lets §7.5's field
telescope drop `hcanon` **and** `hpos`'s index bound (ledger ruling 122e). -/
theorem uniformOcc?_types {D : VInductDecl'} {k : Nat} {e : VExpr} {j : Nat}
    {rest : List VExpr} (h : D.uniformOcc? k e = some (j, rest)) :
    ∃ T, D.types[j]? = some T := by
  rw [VInductDecl'.uniformOcc?] at h
  split at h
  · split at h
    · next j' hj =>
      split at h
      · obtain ⟨rfl, -⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
        obtain ⟨T, hT, -⟩ := VInductDecl'.memberIdx_spec' hj
        exact ⟨T, hT⟩
      · exact absurd h nofun
    · exact absurd h nofun
  · exact absurd h nofun

/-- `atRec` carries the *restored* head `tyAppR` to `tyAppR'` — the `tyAppR` twin of
`VInductDecl'.atRec_tyApp`, and an instance of `atRec_tyAppH`. -/
theorem atRec_tyAppR (D : VInductDecl') (R : VIndRestore) (j k : Nat) (args : List VExpr) :
    D.atRec (D.tyAppR R j k args) = D.tyAppR' R j k (D.atRecTele args) :=
  VInductDecl'.atRec_tyAppH D

end VInductDecl'

namespace VIndRestore
variable {R : VIndRestore} {D : VInductDecl'} {K : List Name} {σ : CSubst}

/-- `VIndRestore.csubst_closed` at the reach §7.4 works in: `D.params = []` and a closed
presented spine. -/
theorem csubst_closed' (hp : D.params = []) (hcl0 : ∀ i, ∀ a ∈ R.tyArgs i, a.ClosedN 0) :
    (R.csubst D K).Closed :=
  csubst_closed R D K (by rw [hp]; exact trivial)
    (fun j a ha => by rw [show D.np = D.params.length from rfl, hp]; exact hcl0 j a ha)

/-! ## §7.5 Obligation (B): the recursor's restored type

    (D.recType j).substC σ = (D.recTypeR R j).substC σ

Three moving parts — the motives, the minors and the major premise's head — and the shared
ingredient with (C) is the field telescope, `substC_atRec_fieldTypes`.  Nothing here needs a
`LevelWF` hypothesis (Part 4b's `hlw`): `atRec` is kept *inside* the substitution, so only the
**primed** head equations of §7.4 are used, and those are stated at exactly the instantiation
`tyAppR'` is defined at.

`hpos` is the index bound of `VIndField.WF.pos`, read off by `VIndField.WF.recArg_noBlock`.  It
used to be accompanied by `hcanon : D.Canonical`; ruling 122e removed that, because the stored
telescope needs no canonicity (`substC_atRec_restore`) and `Canonical` is false at the blocks
this layer has to describe. -/

section
variable (hp : D.params = []) (hnd : D.blockNames.Nodup) (hown : R.OwnId D K)
  (hat : R.SubstAt D K σ)
  (hcl0 : ∀ i, ∀ a ∈ R.tyArgs i, a.ClosedN 0) (hfr : R.SubstFree D σ)
include hp hnd hown hat hcl0 hfr

/-- **Wherever the trigger fires, the two heads meet under `σ`** — with *no* side condition.

`uniformOcc?_sound` says the subterm the trigger fired on **was** `D.tyApp j k rest`, and
`uniformOcc?_types` says member `j` exists, which is the only hypothesis §7.4's `tyApp'`
head equation wanted.  So the restoration's head and the block's head are the same expression
after `σ`, at every occurrence, canonical or not. -/
theorem substC_atRec_uniformOcc {k : Nat} {e : VExpr} {j : Nat} {rest : List VExpr}
    (h : D.uniformOcc? k e = some (j, rest)) :
    (D.atRec (D.tyAppR R j k rest)).substC σ = (D.atRec e).substC σ := by
  obtain ⟨T, hT⟩ := VInductDecl'.uniformOcc?_types h
  rw [← VInductDecl'.uniformOcc?_sound h, VInductDecl'.atRec_tyAppR,
    VInductDecl'.atRec_tyApp, substC_tyAppR' hfr,
    substC_tyApp'_eq_tyAppR' hp hown hat hcl0 hT]
  simp only [VInductDecl'.atRecTele]
  rfl

/-- **The restoration is invisible to the substitution — at every subterm, unconditionally.**

This is ruling 122e's engine, and the one-layer-out analogue of `VIndRestore.restore_id`:
where the trigger fires, `substC_atRec_uniformOcc`; where it does not, congruence.

Compare what it replaces.  The old proof of `substC_atRec_fieldTypes` went through
`VIndRestore.typeR_canonical`, which demands `F.type = r.canonType D i` **on the nose** —
`VIndCtor.Canonical` — and that is machine-checked **false** at the block level for every
real nested declaration in the running environment: `Lean.Json`, `Lean.PrefixTreeNode` and
`MRedex.MRWit.MJ` (`MRedex.MRWit.mr_auxNodeB_block_not_canonical`,
`Theory/Inductive/MemberRedex.lean`).  Restoring the **stored** type needs none of it, so
`hcanon` disappears from §7.5/§7.6 rather than being weakened — exactly as it disappeared from
`NestedHead.lean` Part 3 under ruling 116d. -/
theorem substC_atRec_restore (k : Nat) (e : VExpr) :
    (D.atRec (R.restore D k e)).substC σ = (D.atRec e).substC σ := by
  induction e generalizing k with
  | bvar => rfl
  | sort => rfl
  | const n ls =>
    rw [restore]
    split
    · next j rest h => exact substC_atRec_uniformOcc hp hnd hown hat hcl0 hfr h
    · rfl
  | app f a ihf iha =>
    rw [restore]
    split
    · next j rest h => exact substC_atRec_uniformOcc hp hnd hown hat hcl0 hfr h
    · simp only [VInductDecl'.atRec_app, VExpr.substC_app, ihf, iha]
  | lam A b ihA ihb =>
    rw [restore]
    simp only [VInductDecl'.atRec_lam, VExpr.substC_lam, ihA, ihb]
  | forallE A b ihA ihb =>
    rw [restore]
    simp only [VInductDecl'.atRec_forallE, VExpr.substC_forallE, ihA, ihb]

/-- **The field telescope, at the recursor's numbering.**  This is Part 4b's `hfl` at
`R.csubst`, with `atRec` kept *inside* the substitution so that only the **primed** head
equations of §7.4 are needed — no `LevelWF` hypothesis.

**Ruling 122e: `hcanon` and `hpos` are both gone**, and the statement is unchanged.  The old
proof rewrote a recursive field's restored type to `r.canonTypeR` and then compared canonical
head with canonical head; the new one never looks at `r` at all — `substC_atRec_restore`
handles the stored type whatever shape it has, so neither `C.Canonical D` (false at the three
redex blocks) nor the index bound is needed. -/
theorem substC_atRec_fieldTypes {C : VIndCtor} :
    (D.atRecTele (C.fields.map (·.type))).map (VExpr.substC · σ)
      = (D.atRecTele (C.fieldTypesR D R)).map (VExpr.substC · σ) := by
  have key : ∀ (Fs : List VIndField) (i : Nat),
      Fs.map (fun F => (D.atRec F.type).substC σ)
        = (Fs.zipIdx i).map (fun p => (D.atRec (p.1.typeR D R p.2)).substC σ) := by
    intro Fs
    induction Fs with
    | nil => intro _; rfl
    | cons F Fs ih =>
      intro i
      rw [List.zipIdx_cons, List.map_cons, List.map_cons, ih (i+1)]
      congr 1
      cases hr : F.recArg with
      | none => rw [show F.typeR D R i = F.type from by rw [VIndField.typeR, hr]]
      | some r =>
        rw [show F.typeR D R i = R.restore D i F.type from by rw [VIndField.typeR, hr]]
        exact (substC_atRec_restore hp hnd hown hat hcl0 hfr i F.type).symm
  rw [VInductDecl'.atRecTele, VInductDecl'.atRecTele, VIndCtor.fieldTypesR,
    List.map_map, List.map_map, List.map_map, List.map_map]
  exact key C.fields 0

/-- **The motive telescope.**  One `tyApp'` head per motive, and nothing else moves. -/
theorem substC_motives :
    D.motives.map (VExpr.substC · σ) = (D.motivesR R).map (VExpr.substC · σ) := by
  rw [VInductDecl'.motives, VInductDecl'.motivesR, List.map_map, List.map_map]
  refine List.map_congr_left fun t ht => ?_
  have hT := VInductDecl'.getElem?_types_getD (D := D) (List.mem_range.1 ht)
  simp only [Function.comp_def, VInductDecl'.motiveType, VInductDecl'.motiveTypeR,
    VExpr.substC_mkPi, VExpr.substC_forallE]
  rw [substC_tyApp'_eq_tyAppR' hp hown hat hcl0 hT, substC_tyAppR' hfr]

/-- **The minor-premise telescope.**  Two moving parts: the restored field telescope, and the
`ctorApp'` head of the minor's conclusion. -/
theorem substC_minors (hσ : σ.Closed) :
    D.minors.map (VExpr.substC · σ) = (D.minorsR R).map (VExpr.substC · σ) := by
  rw [VInductDecl'.minors, VInductDecl'.minorsR, List.map_map, List.map_map]
  refine List.map_congr_left fun p hp' => ?_
  obtain ⟨⟨t, C⟩, q⟩ := p
  have hmem : (t, C) ∈ D.ctorsAll :=
    List.mem_of_getElem? (List.mk_mem_zipIdx_iff_getElem?.1 hp')
  obtain ⟨T, hT, hC⟩ := VInductDecl'.mem_ctorsAll hmem
  simp only [Function.comp_def, VInductDecl'.minorType, VInductDecl'.minorTypeR,
    VExpr.substC_mkPi, VExpr.substC_mkApp, List.map_append, List.map_cons, List.map_nil]
  rw [VExpr.map_substC_liftTele (σ := σ) hσ, VExpr.map_substC_liftTele (σ := σ) hσ,
    substC_atRec_fieldTypes hp hnd hown hat hcl0 hfr,
    substC_ctorApp'_eq_ctorAppR hp hown hat hcl0 hT hC, substC_ctorAppR hfr hT hC]

/-! ### §7.5 Obligation (B) -/

/-- **Obligation (B) for a parameterless nested block.**

    (D.recType j).substC σ = (D.recTypeR R j).substC σ

The three moving parts are the motives, the minors and the major premise's `tyApp'` head;
the parameter telescope, the index telescope, the induction-hypothesis telescope and the
conclusion are literally the same expression on both sides. -/
theorem substC_recType_eq (hσ : σ.Closed)
    {j : Nat} {T : VIndType} (hT : D.types[j]? = some T) :
    (D.recType j).substC σ = (D.recTypeR R j).substC σ := by
  have hg : D.types.getD j default = T := by rw [List.getD_eq_getElem?_getD, hT]; rfl
  simp only [VInductDecl'.recType, VInductDecl'.recTypeR, VExpr.substC_mkPi,
    VExpr.substC_forallE, VExpr.substC_mkApp, List.map_append, hg]
  rw [substC_motives hp hnd hown hat hcl0 hfr,
    substC_minors hp hnd hown hat hcl0 hfr hσ,
    substC_tyApp'_eq_tyAppR' hp hown hat hcl0 hT, substC_tyAppR' hfr]

/-! ### §7.6 Obligation (C) -/

/-- The ι-rule's binder context, both restorations agreeing under `σ`. -/
theorem substC_iotaCtx (hσ : σ.Closed)
    {j : Nat} {T : VIndType} (hT : D.types[j]? = some T) {C : VIndCtor} (hC : C ∈ T.ctors) :
    (D.iotaCtx C).map (VExpr.substC · σ) = (D.iotaCtxR R C).map (VExpr.substC · σ) := by
  have hmem : (j, C) ∈ D.ctorsAll := VInductDecl'.mem_ctorsAll_of hT hC
  simp only [VInductDecl'.iotaCtx, VInductDecl'.iotaCtxR, List.map_append]
  rw [substC_motives hp hnd hown hat hcl0 hfr,
    substC_minors hp hnd hown hat hcl0 hfr hσ,
    VExpr.map_substC_liftTele (σ := σ) hσ, VExpr.map_substC_liftTele (σ := σ) hσ,
    substC_atRec_fieldTypes hp hnd hown hat hcl0 hfr]

/-- …and therefore the two contexts have the same length, which is what the η-expanded
right-hand side of the rule applies its `bvars` run to. -/
theorem iotaCtx_length_eq (hσ : σ.Closed)
    {j : Nat} {T : VIndType} (hT : D.types[j]? = some T) {C : VIndCtor} (hC : C ∈ T.ctors) :
    (D.iotaCtx C).length = (D.iotaCtxR R C).length := by
  have := congrArg List.length (substC_iotaCtx hp hnd hown hat hcl0 hfr hσ hT hC)
  rwa [List.length_map, List.length_map] at this

omit hp hnd hcl0 in
/-- **The induction-hypothesis values.**  Their heads are the *renamed* recursors of the
recursive fields' targets — the one place `SubstFree.recName`'s quantification over every
member (rather than `KeysFree`'s over `D.ctorsAll`) is used. -/
theorem substC_ihValues {C : VIndCtor}
    (hpos : ∀ (i : Nat) (F : VIndField) (r : VIndRecArg), C.fields[i]? = some F →
      F.recArg = some r → r.idx < D.nm) :
    (D.ihValues C).map (VExpr.substC · σ) = (D.ihValuesR R C).map (VExpr.substC · σ) := by
  simp only [VInductDecl'.ihValues, VInductDecl'.ihValuesR, List.map_map]
  refine List.map_congr_left fun p hp' => ?_
  obtain ⟨i, r⟩ := p
  obtain ⟨F, hF, hr⟩ := VIndCtor.mem_recFields hp'
  obtain ⟨T', hT'⟩ : ∃ T', D.types[r.idx]? = some T' :=
    ⟨_, List.getElem?_eq_getElem (hpos i F r hF hr)⟩
  simp only [Function.comp_def, VExpr.substC_mkLams, VExpr.substC_mkApp, List.map_append]
  rw [substC_recConst hown hat hT', substC_recConstR hfr]

/-- The ι-rule's left-hand side: the recursor head is renamed by `σ`, and the major premise's
constructor head restored. -/
theorem substC_iotaLhs {j : Nat} {T : VIndType} (hT : D.types[j]? = some T)
    {C : VIndCtor} (hC : C ∈ T.ctors) :
    (D.iotaLhs j C).substC σ = (D.iotaLhsR R j C).substC σ := by
  simp only [VInductDecl'.iotaLhs, VInductDecl'.iotaLhsR, VExpr.substC_mkApp,
    List.map_append, List.map_cons, List.map_nil]
  rw [substC_recConst hown hat hT, substC_recConstR hfr,
    substC_ctorApp'_eq_ctorAppR hp hown hat hcl0 hT hC, substC_ctorAppR hfr hT hC]

/-- The ι-rule's type. -/
theorem substC_iotaType {j : Nat} {T : VIndType} (hT : D.types[j]? = some T)
    {C : VIndCtor} (hC : C ∈ T.ctors) :
    (D.iotaType j C).substC σ = (D.iotaTypeR R j C).substC σ := by
  simp only [VInductDecl'.iotaType, VInductDecl'.iotaTypeR, VExpr.substC_mkApp,
    List.map_append, List.map_cons, List.map_nil]
  rw [substC_ctorApp'_eq_ctorAppR hp hown hat hcl0 hT hC, substC_ctorAppR hfr hT hC]

/-- The ι-rule's right-hand side, before the η-expansion. -/
theorem substC_iotaLam (hσ : σ.Closed)
    (hpos : ∀ (t : Nat) (C : VIndCtor), (t, C) ∈ D.ctorsAll →
      ∀ (i : Nat) (F : VIndField) (r : VIndRecArg), C.fields[i]? = some F →
        F.recArg = some r → r.idx < D.nm ∧ ∀ B ∈ r.binders, D.NoBlock B)
    {j : Nat} {T : VIndType} (hT : D.types[j]? = some T) {C : VIndCtor} (hC : C ∈ T.ctors)
    (q : Nat) :
    (D.iotaLam q C).substC σ = (D.iotaLamR R q C).substC σ := by
  have hmem : (j, C) ∈ D.ctorsAll := VInductDecl'.mem_ctorsAll_of hT hC
  simp only [VInductDecl'.iotaLam, VInductDecl'.iotaLamR, VExpr.substC_mkLams,
    VExpr.substC_mkApp, List.map_append]
  rw [substC_iotaCtx hp hnd hown hat hcl0 hfr hσ hT hC,
    substC_ihValues hown hat hfr (fun i F r hF hr => (hpos j C hmem i F r hF hr).1)]

/-- **Obligation (C) for a parameterless nested block.**

    (D.iotaRule j q C).substC σ = (D.iotaRuleR R j q C).substC σ

head by head over `iotaCtx`/`iotaLhs`/`iotaLam`/`ihValues`/`iotaType`. -/
theorem substC_iotaRule_eq (hσ : σ.Closed)
    (hpos : ∀ (t : Nat) (C : VIndCtor), (t, C) ∈ D.ctorsAll →
      ∀ (i : Nat) (F : VIndField) (r : VIndRecArg), C.fields[i]? = some F →
        F.recArg = some r → r.idx < D.nm ∧ ∀ B ∈ r.binders, D.NoBlock B)
    {j : Nat} {T : VIndType} (hT : D.types[j]? = some T) {C : VIndCtor} (hC : C ∈ T.ctors)
    (q : Nat) :
    (D.iotaRule j q C).substC σ = (D.iotaRuleR R j q C).substC σ := by
  have hctx := substC_iotaCtx hp hnd hown hat hcl0 hfr hσ hT hC
  have hlen := iotaCtx_length_eq hp hnd hown hat hcl0 hfr hσ hT hC
  simp only [VDefEq.substC, VInductDecl'.iotaRule, VInductDecl'.iotaRuleR,
    VExpr.substC_mkLams, VExpr.substC_mkPi, VExpr.substC_mkApp, VExpr.map_substC_bvars,
    hctx, hlen, substC_iotaLhs hp hnd hown hat hcl0 hfr hT hC,
    substC_iotaLam hp hnd hown hat hcl0 hfr hσ hpos hT hC q,
    substC_iotaType hp hnd hown hat hcl0 hfr hT hC]


end

/-! ## §7.7 …at the real substitution, and the two obligations closed

`VEnv.recConstsR_wf_of_substC` and `VEnv.iotaRulesRS_wf_of_substC`
(`Theory/Typing/ConstSubstNested.lean`) already reduce obligations (B) and (C) of
`VEnv.addInductR_ordered'` to one bridge equation each.  §7.5 and §7.6 are those equations, so
the two obligations close for a parameterless nested block on exactly the hypotheses (A) closes
on — plus `SubstFree`, which is `VIndRestore.KeysFree` strengthened at the recursor clause
(`SubstFree.keysFree`), and `DomSep`, whose `= none` half `domSep_of_allNames_nodup` derives
from `D.allNames.Nodup`. -/

section
variable (hp : D.params = []) (hnd : D.blockNames.Nodup) (hown : R.OwnId D K)
  (hsep : R.DomSep D K)
  (hcl0 : ∀ i, ∀ a ∈ R.tyArgs i, a.ClosedN 0) (hfr : R.SubstFree D (R.csubst D K))
  (hpos : ∀ (t : Nat) (C : VIndCtor), (t, C) ∈ D.ctorsAll →
    ∀ (i : Nat) (F : VIndField) (r : VIndRecArg), C.fields[i]? = some F →
      F.recArg = some r → r.idx < D.nm ∧ ∀ B ∈ r.binders, D.NoBlock B)
include hp hnd hown hsep hcl0 hfr hpos

omit hpos in
/-- **(B) at the real substitution** — the exact `hbridge` `VEnv.recConstsR_wf_of_substC`
takes.

**`hpos` is gone too** (ruling 122e): the field telescope no longer reads a recursive field's
`recArg` at all, so obligation (B) for a parameterless nested block now carries **no per-field
side condition whatever**.  (C) still needs it, through `substC_ihValues`, whose heads are the
renamed recursors of the recursive fields' targets. -/
theorem csubst_recType_eq (j : Nat) (T : VIndType) (hT : D.types[j]? = some T) :
    (D.recType j).substC (R.csubst D K) = (D.recTypeR R j).substC (R.csubst D K) :=
  substC_recType_eq hp hnd hown hsep.substAt hcl0 hfr (csubst_closed' hp hcl0) hT

/-- **(C) at the real substitution, at the list level** — the exact `hbridge`
`VEnv.iotaRulesRS_wf_of_substC` takes.  Note which way round it points: the *un*-restored
rules, substituted, are the rules the step registers. -/
theorem csubst_iotaRules_eq :
    D.iotaRules.map (·.substC (R.csubst D K)) = D.iotaRulesRS R K := by
  rw [VInductDecl'.iotaRules, VInductDecl'.iotaRulesRS, VInductDecl'.iotaRulesR,
    List.map_map, List.map_map]
  refine List.map_congr_left fun p hp' => ?_
  obtain ⟨⟨j, C⟩, q⟩ := p
  obtain ⟨T, hT, hC⟩ :=
    VInductDecl'.mem_ctorsAll (List.mem_of_getElem? (List.mk_mem_zipIdx_iff_getElem?.1 hp'))
  exact substC_iotaRule_eq hp hnd hown hsep.substAt hcl0 hfr (csubst_closed' hp hcl0)
    hpos hT hC q

end

end VIndRestore

/-- **Obligation (B) of `VEnv.addInductR_ordered'`, closed for a parameterless nested
block.**  `hsrc` and `hσ` are the two hypotheses the non-nested recursor stage already
supplies; everything else is a syntactic side condition on the block or the restoration. -/
theorem VEnv.recConstsR_wf_of_np_zero {E₂ e₂ : VEnv} {D : VInductDecl'} {R : VIndRestore}
    {K : List Name}
    (hsrc : ∀ c ∈ D.recConsts, VConstant.WF E₂ c.2)
    (hσ : (R.csubst D K).WF E₂ e₂ D.recUvars)
    (hp : D.params = []) (hnd : D.blockNames.Nodup) (hown : R.OwnId D K)
    (hsep : R.DomSep D K)
    (hcl0 : ∀ i, ∀ a ∈ R.tyArgs i, a.ClosedN 0)
    (hfr : R.SubstFree D (R.csubst D K)) :
    ∀ c ∈ D.recConstsR R K, VConstant.WF e₂ c.2 :=
  VEnv.recConstsR_wf_of_substC hsrc hσ
    (VIndRestore.csubst_recType_eq hp hnd hown hsep hcl0 hfr)

/-- **Obligation (C) of `VEnv.addInductR_ordered'`, closed for a parameterless nested
block.** -/
theorem VEnv.iotaRulesRS_wf_of_np_zero {E₃ e₃ : VEnv} {D : VInductDecl'} {R : VIndRestore}
    {K : List Name}
    (hsrc : ∀ df ∈ D.iotaRules, VDefEq.WF E₃ df)
    (hσ : ∀ df ∈ D.iotaRules, (R.csubst D K).WF E₃ e₃ df.uvars)
    (hp : D.params = []) (hnd : D.blockNames.Nodup) (hown : R.OwnId D K)
    (hsep : R.DomSep D K)
    (hcl0 : ∀ i, ∀ a ∈ R.tyArgs i, a.ClosedN 0)
    (hfr : R.SubstFree D (R.csubst D K))
    (hpos : ∀ (t : Nat) (C : VIndCtor), (t, C) ∈ D.ctorsAll →
      ∀ (i : Nat) (F : VIndField) (r : VIndRecArg), C.fields[i]? = some F →
        F.recArg = some r → r.idx < D.nm ∧ ∀ B ∈ r.binders, D.NoBlock B) :
    ∀ df ∈ D.iotaRulesRS R K, VDefEq.WF e₃ df :=
  VEnv.iotaRulesRS_wf_of_substC hsrc hσ
    (VIndRestore.csubst_iotaRules_eq hp hnd hown hsep hcl0 hfr hpos)

/-! ## §7.8 The two bridges are not vacuous

`docs/vacuity-ledger.md` §5: a bridge nothing satisfies is not a bridge.  Every hypothesis of
§7.5 and §7.6 is discharged here at the `NFn`/`PFn` witness — the genuine nested block with a
recursive field carrying a non-empty binder telescope.  `SubstFree` is discharged **field by
field** (four separate theorems) rather than as a structure, because a structure-level `decide`
can be vacuous on one field.

**These are not new facts about `nfnAux`.**  `InductiveDeclExamples.nfn_recType_substC_0/1` and
`nfn_iotaRules_substC` (`Theory/Typing/ConstSubstNested.lean`) already had (B) and (C) at this
witness by `rfl`, and in the *stronger* form with the right-hand side unsubstituted
(`nfnAux_iotaRulesRS_noop`, `Theory/Inductive/RestoreBridge.lean`, is why the two forms agree
there).  What §7.8 is for is the opposite direction: it certifies that §7.5/§7.6's hypothesis
bundle is *satisfiable at a real nested block*, so the general theorems are not vacuous.
`nfnAux_iotaRules_keys_move` adds that the (C) equation transports a rule across a rename
rather than restating `rfl`. -/

namespace InductiveDeclExamples

theorem nfnRestore_domNodup : nfnRestore.DomNodup nfnAux nfnK := by
  show ((nfnRestore.csubstList nfnAux nfnK).map (·.1)).Nodup
  show ([`_nested.PFn_1, `_nested.PFn_1.rec, `_nested.PFn_1.mk] : List Name).Nodup
  decide

/-- The domain is the three auxiliary names, and it is *not* empty — so `SubstAt`'s `some`
clauses have something to say. -/
theorem nfn_csubstList_dom :
    (nfnRestore.csubstList nfnAux nfnK).map (·.1)
      = [`_nested.PFn_1, `_nested.PFn_1.rec, `_nested.PFn_1.mk] := rfl

theorem nfnAux_allNames_nodup : nfnAux.allNames.Nodup := by decide

theorem nfnRestore_domSep : nfnRestore.DomSep nfnAux nfnK :=
  VIndRestore.domSep_of_allNames_nodup nfnAux_allNames_nodup nfnRestore_domNodup

theorem nfnRestore_tyArgs_closed0 : ∀ i, ∀ a ∈ nfnRestore.tyArgs i, a.ClosedN 0 := by
  intro i a ha
  by_cases h : i = 1
  · rw [show nfnRestore.tyArgs i = [.const ``NFn []] from by simp [nfnRestore, h]] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    subst ha; trivial
  · rw [show nfnRestore.tyArgs i = [] from by simp [nfnRestore, h]] at ha
    exact absurd ha nofun

/-! ### `SubstFree`, field by field -/

theorem nfn_substFree_tyName :
    ∀ j, nfnRestore.csubst nfnAux nfnK (nfnRestore.tyName j) = none := by
  intro j; by_cases h : j = 1 <;> simp only [nfnRestore, h] <;> rfl

theorem nfn_substFree_tyArgs : ∀ j, ∀ a ∈ nfnRestore.tyArgs j,
    a.NoCSubst (nfnRestore.csubst nfnAux nfnK) := by
  intro j a ha
  by_cases h : j = 1
  · rw [show nfnRestore.tyArgs j = [.const ``NFn []] from by simp [nfnRestore, h]] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    subst ha; exact (rfl : nfnRestore.csubst nfnAux nfnK ``NFn = none)
  · rw [show nfnRestore.tyArgs j = [] from by simp [nfnRestore, h]] at ha
    exact absurd ha nofun

/-- The clause `VIndRestore.KeysFree` does **not** supply: quantified over every member index,
including the junk ones above `nfnAux.nm`. -/
theorem nfn_substFree_recName : ∀ j, nfnRestore.csubst nfnAux nfnK
    (nfnRestore.recName (Lean.mkRecName (nfnAux.types.getD j default).name)) = none := by
  rintro (_ | _ | j)
  · rfl
  · rfl
  · exact (rfl : nfnRestore.csubst nfnAux nfnK
      (nfnRestore.recName (Lean.mkRecName (default : VIndType).name)) = none)

theorem nfn_substFree_ctorName : ∀ (j : Nat) (T : VIndType), nfnAux.types[j]? = some T →
    ∀ C ∈ T.ctors, nfnRestore.csubst nfnAux nfnK (nfnRestore.ctorName C.name) = none := by
  rintro (_ | _ | j) T hT C hC
  · cases hT
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
    subst hC; rfl
  · cases hT
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
    subst hC; rfl
  · simp [nfnAux] at hT

theorem nfnRestore_substFree : nfnRestore.SubstFree nfnAux (nfnRestore.csubst nfnAux nfnK) :=
  ⟨nfn_substFree_tyName, nfn_substFree_tyArgs, nfn_substFree_recName, nfn_substFree_ctorName⟩

/-! ### `Canonical` and the index bound -/

theorem nfnAux_ctorsAll_eq : nfnAux.ctorsAll = [(0, nfnNode), (1, pfnAuxMk)] := rfl

theorem nfnNode_canonical : nfnNode.Canonical nfnAux := by
  rintro (_ | i) F r hF hr
  · cases hF; cases hr; rfl
  · simp [nfnNode] at hF

theorem pfnAuxMk_canonical : pfnAuxMk.Canonical nfnAux := by
  rintro (_ | _ | i) F r hF hr
  · cases hF; cases hr; rfl
  · cases hF; cases hr; rfl
  · simp [pfnAuxMk] at hF

theorem nfnAux_canonical : nfnAux.Canonical := by
  intro j C h
  rw [nfnAux_ctorsAll_eq] at h
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := h
  · exact nfnNode_canonical
  · exact pfnAuxMk_canonical

/-- The index bound **and** the recursive binders' block-freeness.  The second conjunct is new
under ruling 116d — `VIndRestore.typeR_canonical` needs it, because `VIndField.typeR` now
*restores* the stored type instead of replacing it — and it is a `VIndField.WF.pos` conjunct, so
no consumer with `D.WF env` in hand pays anything for it (`VIndField.WF.recArg_noBlock`). -/
theorem nfnAux_pos : ∀ (t : Nat) (C : VIndCtor), (t, C) ∈ nfnAux.ctorsAll →
    ∀ (i : Nat) (F : VIndField) (r : VIndRecArg), C.fields[i]? = some F →
      F.recArg = some r → r.idx < nfnAux.nm ∧ ∀ B ∈ r.binders, nfnAux.NoBlock B := by
  intro t C h
  rw [nfnAux_ctorsAll_eq] at h
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := h
  · rintro (_ | i) F r hF hr
    · cases hF; cases hr
      exact ⟨by decide, by simp [VInductDecl'.NoBlock, VExpr.NoConsts]⟩
    · simp [nfnNode] at hF
  · rintro (_ | _ | i) F r hF hr
    · cases hF; cases hr
      exact ⟨by decide, by simp [VInductDecl'.NoBlock, VExpr.NoConsts]⟩
    · cases hF; cases hr
      exact ⟨by decide, by simp [VInductDecl'.NoBlock, VExpr.NoConsts]⟩
    · simp [pfnAuxMk] at hF

theorem nfnAux_blockNames_nodup' : nfnAux.blockNames.Nodup := by decide

/-! ### …and the two bridges, instantiated -/

/-- **(B) at the witness.** -/
theorem nfnAux_recTypeR_bridge (j : Nat) (T : VIndType) (hT : nfnAux.types[j]? = some T) :
    (nfnAux.recType j).substC (nfnRestore.csubst nfnAux nfnK)
      = (nfnAux.recTypeR nfnRestore j).substC (nfnRestore.csubst nfnAux nfnK) :=
  VIndRestore.csubst_recType_eq rfl nfnAux_blockNames_nodup' nfnRestore_ownId nfnRestore_domSep
    nfnRestore_tyArgs_closed0 nfnRestore_substFree j T hT

/-- **(C) at the witness.** -/
theorem nfnAux_iotaRules_substC_bridge :
    nfnAux.iotaRules.map (·.substC (nfnRestore.csubst nfnAux nfnK))
      = nfnAux.iotaRulesRS nfnRestore nfnK :=
  VIndRestore.csubst_iotaRules_eq rfl nfnAux_blockNames_nodup' nfnRestore_ownId
    nfnRestore_domSep
    nfnRestore_tyArgs_closed0 nfnRestore_substFree nfnAux_pos

/-- **…and it is not an identity.**  The auxiliary block's own ι-rule is keyed on
`_nested.PFn_1.rec`/`_nested.PFn_1.mk`; the rule the step registers is keyed on
`NFn.rec_1`/`PFn.mk`.  So the (C) equation above transports a rule across a rename, which is
exactly the content `nfnAux_iotaRulesRS_noop` (`Theory/Inductive/RestoreBridge.lean`) does
*not* have: that one says the substitution is the identity on the already-**restored** list. -/
theorem nfnAux_iotaRules_keys_move :
    nfnAux.iotaRules.map VDefEq.key
      ≠ (nfnAux.iotaRulesRS nfnRestore nfnK).map VDefEq.key := by decide

/-! ### …and bounded the other way: `OwnId` is load-bearing

`docs/vacuity-ledger.md` §5 again.  `nfnJunkRestore` is `nfnRestore` with **one field changed**
— the *declared* member `NFn` is presented as `Nat` — and it satisfies every hypothesis of §7.5
except `VIndRestore.OwnId`: `D.params = []`, `DomSep`, the closed spine, all four `SubstFree`
clauses, `Canonical` and the index bound are the same proofs or hold at the same values.  The
(B) equation is then **false**, so the hypothesis is not decoration.

This is the `pfnJunkRestore` configuration (`Theory/Inductive/NestedBuild.lean`) moved to a
**parameterless** block, which `pfnDecl` is not — so `pfnJunkRestore` could not have witnessed
this: `hp : D.params = []` fails for it before `OwnId` gets a chance to. -/

def nfnJunkRestore : VIndRestore :=
  { nfnRestore with tyName := fun j => if j = 1 then ``PFn else ``Nat }

theorem nfnJunk_not_ownId : ¬ nfnJunkRestore.OwnId nfnAux nfnK := by
  intro h
  have := h.tyName 0 _ rfl (by decide)
  exact absurd this (by decide)

theorem nfnJunk_domNodup : nfnJunkRestore.DomNodup nfnAux nfnK := by
  show ((nfnJunkRestore.csubstList nfnAux nfnK).map (·.1)).Nodup
  show ([`_nested.PFn_1, `_nested.PFn_1.rec, `_nested.PFn_1.mk] : List Name).Nodup
  decide

theorem nfnJunk_domSep : nfnJunkRestore.DomSep nfnAux nfnK :=
  VIndRestore.domSep_of_allNames_nodup nfnAux_allNames_nodup nfnJunk_domNodup

theorem nfnJunk_tyArgs_eq : nfnJunkRestore.tyArgs = nfnRestore.tyArgs := rfl

theorem nfnJunk_substFree :
    nfnJunkRestore.SubstFree nfnAux (nfnJunkRestore.csubst nfnAux nfnK) where
  tyName j := by by_cases h : j = 1 <;> simp only [nfnJunkRestore, nfnRestore, h] <;> rfl
  tyArgs j a ha := by
    rw [nfnJunk_tyArgs_eq] at ha
    by_cases h : j = 1
    · rw [show nfnRestore.tyArgs j = [.const ``NFn []] from by simp [nfnRestore, h]] at ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      subst ha; exact (rfl : nfnJunkRestore.csubst nfnAux nfnK ``NFn = none)
    · rw [show nfnRestore.tyArgs j = [] from by simp [nfnRestore, h]] at ha
      exact absurd ha nofun
  recName := by
    rintro (_ | _ | j)
    · rfl
    · rfl
    · exact (rfl : nfnJunkRestore.csubst nfnAux nfnK
        (nfnJunkRestore.recName (Lean.mkRecName (default : VIndType).name)) = none)
  ctorName := by
    rintro (_ | _ | j) T hT C hC
    · cases hT
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
      subst hC; rfl
    · cases hT
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
      subst hC; rfl
    · simp [nfnAux] at hT

/-- **The (B) equation fails at the junk restoration.**  Everything but `OwnId` holds. -/
theorem nfnJunk_recTypeR_bridge_false :
    (nfnAux.recType 0).substC (nfnJunkRestore.csubst nfnAux nfnK)
      ≠ (nfnAux.recTypeR nfnJunkRestore 0).substC (nfnJunkRestore.csubst nfnAux nfnK) := by
  decide

/-! ### `SubstFree` also holds at the **parameterised** witness

Evidence that §7.4's interface is not secretly tied to `D.params = []`: `SubstFree` is about
names only, and it holds at `ntreeRestore`/`ntreeAux` — where `hcl0` *fails*, which is exactly
why §7.5 and §7.6 do not reach that block.  This is the fact the item-4 refactor
(making `SubstFree` a clause of `VInductDecl'.Built` / `VEnv.AddNested` rather than a
hypothesis) would need at both witnesses. -/

theorem ntree_csubstList_dom :
    (ntreeRestore.csubstList ntreeAux ntreeK).map (·.1)
      = [`_nested.List_1, `_nested.List_1.rec, `_nested.List_1.nil, `_nested.List_1.cons] := rfl

theorem ntree_substFree_tyName :
    ∀ j, ntreeRestore.csubst ntreeAux ntreeK (ntreeRestore.tyName j) = none := by
  intro j; by_cases h : j = 1 <;> simp only [ntreeRestore, h] <;> rfl

theorem ntree_substFree_tyArgs : ∀ j, ∀ a ∈ ntreeRestore.tyArgs j,
    a.NoCSubst (ntreeRestore.csubst ntreeAux ntreeK) := by
  intro j a ha
  by_cases h : j = 1
  · rw [show ntreeRestore.tyArgs j = [.app (.const ``NTree [.param 0]) (.bvar 0)] from by
      simp [ntreeRestore, h]] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    subst ha
    exact ⟨(rfl : ntreeRestore.csubst ntreeAux ntreeK ``NTree = none), trivial⟩
  · rw [show ntreeRestore.tyArgs j = [.bvar 0] from by simp [ntreeRestore, h]] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    subst ha; trivial

theorem ntree_substFree_recName : ∀ j, ntreeRestore.csubst ntreeAux ntreeK
    (ntreeRestore.recName (Lean.mkRecName (ntreeAux.types.getD j default).name)) = none := by
  rintro (_ | _ | j)
  · rfl
  · rfl
  · exact (rfl : ntreeRestore.csubst ntreeAux ntreeK
      (ntreeRestore.recName (Lean.mkRecName (default : VIndType).name)) = none)

theorem ntree_substFree_ctorName : ∀ (j : Nat) (T : VIndType), ntreeAux.types[j]? = some T →
    ∀ C ∈ T.ctors, ntreeRestore.csubst ntreeAux ntreeK (ntreeRestore.ctorName C.name) = none := by
  rintro (_ | _ | j) T hT C hC
  · cases hT
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
    subst hC; rfl
  · cases hT
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
    obtain rfl | rfl := hC <;> rfl
  · simp [ntreeAux] at hT

theorem ntreeRestore_substFree :
    ntreeRestore.SubstFree ntreeAux (ntreeRestore.csubst ntreeAux ntreeK) :=
  ⟨ntree_substFree_tyName, ntree_substFree_tyArgs, ntree_substFree_recName,
   ntree_substFree_ctorName⟩

/-- …but `hcl0` fails at the parameterised witness, which is why §7.5/§7.6 do not reach it. -/
theorem ntree_not_tyArgs_closed0 : ¬ (∀ i, ∀ a ∈ ntreeRestore.tyArgs i, a.ClosedN 0) := by
  intro h
  have := h 0 (.bvar 0) (by decide)
  exact absurd (show (0 : Nat) < 0 from this) (Nat.lt_irrefl 0)

theorem ntreeAux_np : ntreeAux.np = 1 := by decide

/-- **…but `ClosedN D.np` does hold there.**  §8.9's β-*defeqs* ask only for this, so `hcl0`
is not a second obstruction hiding behind `hp`: the closedness §7.4's head *equations* need is
strictly stronger than the closedness the typed route needs, and only the former is refuted at
the parameterised witness. -/
theorem ntree_tyArgs_closedN_np :
    ∀ i, ∀ a ∈ ntreeRestore.tyArgs i, a.ClosedN ntreeAux.np := by
  intro i a ha
  rw [ntreeAux_np]
  simp only [ntreeRestore] at ha
  split at ha
  · simp only [List.mem_singleton] at ha; subst ha; exact ⟨trivial, Nat.zero_lt_one⟩
  · simp only [List.mem_singleton] at ha; subst ha; exact Nat.zero_lt_one


end InductiveDeclExamples

end Lean4Lean

/-! # §8 `(R.csubst D K).WF` — the shared remainder, derived down to one clause

§7 closes obligations (A), (B) and (C) for a parameterless nested block *given* a
`CSubst.WF` for the restoration, which was previously supplied only per-witness
(`Theory/Typing/ConstSubstNested.lean`'s `nfnSubst_WF`, a `CSubst.one`).  This section
derives it in general, and isolates what cannot be derived.

**First, a correction to how the remainder is usually described.**  It is *not* one statement
shared by the three obligations.  Reading the three signatures:

* `VEnv.ctorConstsCR_wf_of_np_zero'` takes `(R.csubstTy D K).WF env₃ e₁ D.uvars` — the
  **type-only** substitution;
* `VEnv.recConstsR_wf_of_np_zero` takes `(R.csubst D K).WF E₂ e₂ D.recUvars`;
* `VEnv.iotaRulesRS_wf_of_np_zero` takes `(R.csubst D K).WF E₃ e₃ df.uvars` for each rule.

`csubstTy` and `csubst` are different substitutions with different domains — `csubst` also
replaces the companion members' **constructor** and **recursor** names — so (A)'s hypothesis is
strictly weaker than (B)'s and (C)'s, and the three sit at three different environment pairs.

**Second, the dependency runs one way.**  `VIndRestore.substC_ctorType_csubst_eq_csubstTy`
below shows that on a *declared* constructor's stored type the two substitutions agree, so the
`const` clause of `(R.csubst D K).WF E₂ e₂` reduces to **obligation (A)'s own bridge equation**
(`hbridge` of `csubst_WF_const`).  (B) and (C) therefore do not sit "at (A)'s reach": their
hypothesis *contains* (A)'s conclusion.  `csubst_WF` additionally needs `e₂.Ordered`, which is
what `addConstList_ordered` gives once (A) has been discharged.  So closing the β-gap is
necessary for all three but sufficient for none of (B), (C) on its own.

**Third, three of the four `CSubst.WF` fields are derivable and the fourth is not.**
`closed` is `csubst_closed`; `const` and `defeq` are `csubst_WF_const` / `csubst_WF_defeq`,
from `Ordered.noCSubst` plus freshness that the staging successes already give
(`csubst_freshIn`).  `val` is not: `csubst_val_cases` reduces it to two `HasType` obligations,
`tyVal_hasType_of_faithful` reduces the first to `hsplit` + `hargs`, and
`instAt_indep_of_tyArgs` shows `Faithful` cannot supply `hargs` — see its docstring. -/

namespace Lean4Lean

/-- **Two constant substitutions agreeing on every constant an expression mentions give the
same result.**  `δ` witnesses the disagreement set: wherever `δ` is undefined the two agree,
and `e` mentions nothing in `δ`'s domain. -/
theorem VExpr.substC_congr {σ₁ σ₂ δ : CSubst} (hδ : ∀ c, δ c = none → σ₁ c = σ₂ c) :
    ∀ {e : VExpr}, e.NoCSubst δ → e.substC σ₁ = e.substC σ₂
  | .bvar _, _ | .sort _, _ => rfl
  | .const c _, h => by rw [substC, substC, hδ c h]
  | .app .., h | .lam .., h | .forallE .., h => by
    simp [substC, substC_congr hδ h.1, substC_congr hδ h.2]

namespace VIndRestore
variable {R : VIndRestore} {D : VInductDecl'} {K : List Name}
variable {env E₁ E₂ E₃ e₁ e₂ : VEnv} {n : Name}

/-! ## §8.1 Freshness, from the staging successes

`csubst`'s domain is the block's own type, constructor and recursor names at the companion
members.  `addConst` fails on a duplicate, so the three staging successes — the auxiliary block
declared as an ordinary block, which is exactly what `ElimNestedInductive` really does — say
every one of those names was fresh in the history.  No new side condition. -/

theorem csubst_freshIn
    (h₁ : env.addIndTypes D = some E₁) (h₂ : E₁.addIndCtors D = some E₂)
    (h₃ : E₂.addIndRecs D = some E₃) : (R.csubst D K).FreshIn env := by
  intro c ci hc
  cases hn : R.csubst D K c with
  | none => rfl
  | some v =>
    have le₁ : env ≤ E₁ := VEnv.addConstList_le h₁
    obtain ⟨j, T, hT, hK, ⟨he, -⟩ | ⟨he, -⟩ | ⟨C, hC, he, -⟩⟩ := csubst_dom hn
    · subst he
      have := (VEnv.addConstList_fresh h₁).1 T.name (by
        rw [VInductDecl'.typeConsts_names]
        exact List.mem_map.2 ⟨_, List.mem_of_getElem? hT, rfl⟩)
      rw [this] at hc; exact absurd hc nofun
    · subst he
      have := (VEnv.addConstList_fresh h₃).1 (Lean.mkRecName T.name) (by
        rw [D.recConsts_names]; exact List.mem_map.2 ⟨_, List.mem_of_getElem? hT, rfl⟩)
      rw [(VEnv.addConstList_le h₂).constants (le₁.constants hc)] at this
      exact absurd this nofun
    · subst he
      have := (VEnv.addConstList_fresh h₂).1 C.name (by
        rw [D.ctorConsts_names]
        exact List.mem_map.2 ⟨(j, C), VInductDecl'.mem_ctorsAll_of hT hC, rfl⟩)
      rw [le₁.constants hc] at this; exact absurd this nofun

/-! ## §8.2 `csubst` versus `csubstTy`

The extra domain — the companion members' constructor and recursor names — is what makes (A)'s
hypothesis weaker than (B)'s.  It is also invisible to anything the block *declares*, and that
is a theorem rather than a side condition: a constructor's stored type is checked in the
environment carrying only the block's **types**, where the constructor and recursor names are
all still fresh. -/

/-- The part of `csubst` that `csubstTy` does not carry. -/
def csubstCR (R : VIndRestore) (D : VInductDecl') (K : List Name) : CSubst :=
  fun n => match R.csubstTy D K n with
    | some _ => none
    | none => R.csubst D K n

theorem csubst_eq_csubstTy_of_csubstCR_none (hdn : R.DomNodup D K)
    (c : Name) (h : R.csubstCR D K c = none) : R.csubst D K c = R.csubstTy D K c := by
  unfold csubstCR at h
  split at h
  case h_1 t hTy =>
    rw [hTy]
    have hm := Lean4Lean.List.lookup_mem hTy
    rw [csubstTyList, List.mem_map] at hm
    obtain ⟨⟨T, jj⟩, hmem, hpair⟩ := hm
    rw [List.mem_filter] at hmem
    obtain ⟨hz, hdk⟩ := hmem
    cases hpair
    exact csubst_ty_eq_some hdn (List.mk_mem_zipIdx_iff_getElem?.1 hz) (of_decide_eq_true hdk)
  case h_2 hTy => rw [h, hTy]

theorem csubstCR_freshIn
    (h₁ : env.addIndTypes D = some E₁) (h₂ : E₁.addIndCtors D = some E₂)
    (h₃ : E₂.addIndRecs D = some E₃) : (R.csubstCR D K).FreshIn E₁ := by
  have hnd : D.blockNames.Nodup := by
    have := (VEnv.addConstList_fresh h₁).2; rwa [VInductDecl'.typeConsts_names] at this
  intro c ci hc
  cases hn : R.csubstCR D K c with
  | none => rfl
  | some v =>
    unfold csubstCR at hn
    split at hn
    · exact absurd hn nofun
    case h_2 hTy =>
    obtain ⟨j, T, hT, hK, ⟨he, -⟩ | ⟨he, -⟩ | ⟨C, hC, he, -⟩⟩ := csubst_dom hn
    · subst he; rw [csubstTy_eq_some hnd hT hK] at hTy; exact absurd hTy nofun
    · subst he
      have := (VEnv.addConstList_fresh h₃).1 (Lean.mkRecName T.name) (by
        rw [D.recConsts_names]; exact List.mem_map.2 ⟨_, List.mem_of_getElem? hT, rfl⟩)
      rw [(VEnv.addConstList_le h₂).constants hc] at this; exact absurd this nofun
    · subst he
      have := (VEnv.addConstList_fresh h₂).1 C.name (by
        rw [D.ctorConsts_names]
        exact List.mem_map.2 ⟨(j, C), VInductDecl'.mem_ctorsAll_of hT hC, rfl⟩)
      rw [hc] at this; exact absurd this nofun

/-- **A declared constructor's stored type does not see `csubst`'s extra domain.**  Hence
substituting `csubst` through it is the same as substituting `csubstTy` — which is what turns
the `const` clause of `(R.csubst D K).WF E₂ e₂` into obligation (A)'s own bridge equation. -/
theorem substC_ctorType_csubst_eq_csubstTy (hE₁ : E₁.Ordered) (hdn : R.DomNodup D K)
    (h₁ : env.addIndTypes D = some E₁) (h₂ : E₁.addIndCtors D = some E₂)
    (h₃ : E₂.addIndRecs D = some E₃)
    (hD : D.WF env) {j : Nat} {T : VIndType} (hT : D.types[j]? = some T)
    {C : VIndCtor} (hC : C ∈ T.ctors) :
    (C.type D j).substC (R.csubst D K) = (C.type D j).substC (R.csubstTy D K) := by
  have hfr : (R.csubstCR D K).FreshIn E₁ := csubstCR_freshIn h₁ h₂ h₃
  obtain ⟨u, hu⟩ := (hD.ctors E₁ h₁ j T hT C hC).constant_wf hE₁
  exact VExpr.substC_congr (csubst_eq_csubstTy_of_csubstCR_none hdn)
    (VEnv.IsDefEq.noCSubst' (hE₁.noCSubst hfr) hfr hu nofun).1

/-- …and a **type** member's stored type is checked in `env` itself, so `csubst` is outright
the identity on it. -/
theorem substC_tyType_eq (henv : env.Ordered) (hD : D.WF env)
    (h₁ : env.addIndTypes D = some E₁) (h₂ : E₁.addIndCtors D = some E₂)
    (h₃ : E₂.addIndRecs D = some E₃)
    {T : VIndType} (hT : T ∈ D.types) : T.type.substC (R.csubst D K) = T.type := by
  have hfr : (R.csubst D K).FreshIn env := csubst_freshIn h₁ h₂ h₃
  obtain ⟨u, hu⟩ := (hD.types T hT).constant_wf
  exact (VEnv.IsDefEq.noCSubst' (henv.noCSubst hfr) hfr hu nofun).1.substC_eq

/-! ## §8.3 The name bookkeeping the `const` clause needs -/

theorem mem_typeConstsC_names (h : n ∈ (D.typeConstsC K).map (·.1)) : n ∈ D.blockNames := by
  rw [VInductDecl'.typeConstsC, List.mem_map] at h
  obtain ⟨p, hp, rfl⟩ := h
  rw [List.mem_filterMap] at hp
  obtain ⟨q, hq, hqe⟩ := hp
  rw [← VInductDecl'.typeConsts_names]
  split at hqe
  · exact absurd hqe nofun
  · cases hqe; exact List.mem_map.2 ⟨_, hq, rfl⟩

theorem mem_ctorConstsCR_names (hown : R.OwnId D K)
    (h : n ∈ (D.ctorConstsCR R K).map (·.1)) : n ∈ D.ctorConsts.map (·.1) := by
  rw [VInductDecl'.ctorConstsCR, List.mem_map] at h
  obtain ⟨p, hp, rfl⟩ := h
  rw [List.mem_filterMap] at hp
  obtain ⟨⟨j, C⟩, hq, hqe⟩ := hp
  simp only [] at hqe
  split at hqe
  · exact absurd hqe nofun
  case isFalse hK =>
  cases hqe
  obtain ⟨T, hT, hC⟩ := VInductDecl'.mem_ctorsAll hq
  have hTe : D.types.getD j default = T := by rw [List.getD_eq_getElem?_getD, hT]; rfl
  rw [hTe] at hK
  rw [D.ctorConsts_names, hown.ctorName j T hT hK C hC]
  exact List.mem_map.2 ⟨(j, C), hq, rfl⟩

/-! ## §8.4 The `const` and `defeq` clauses, derived

`hbridge` below is **exactly** obligation (A)'s bridge equation — the hypothesis of
`VEnv.ctorConstsCR_wf_of_substC`, which `VIndRestore.ctorType_substC_eq_typeR_substC` supplies
for a parameterless block.  That is the precise sense in which (B) and (C) are downstream of
(A) rather than beside it. -/

theorem csubst_WF_const (henv : env.Ordered) (hE₁ : E₁.Ordered) (hD : D.WF env)
    (hown : R.OwnId D K) (hdn : R.DomNodup D K)
    (h₁ : env.addIndTypes D = some E₁) (h₂ : E₁.addIndCtors D = some E₂)
    (h₃ : E₂.addIndRecs D = some E₃)
    (f₁ : env.addConstList (D.typeConstsC K) = some e₁)
    (f₂ : e₁.addConstList (D.ctorConstsCR R K) = some e₂)
    (hbridge : ∀ (j : Nat) (T : VIndType) (C : VIndCtor), D.types[j]? = some T →
      T.name ∉ K → C ∈ T.ctors →
      (C.type D j).substC (R.csubstTy D K) = (C.typeR D R j).substC (R.csubstTy D K))
    {c : Name} {ci : VConstant} (hn : R.csubst D K c = none) (hc : E₂.constants c = some ci) :
    e₂.constants c = some ⟨ci.uvars, ci.type.substC (R.csubst D K)⟩ := by
  by_cases hct : c ∈ D.ctorConsts.map (·.1)
  · rw [VInductDecl'.ctorConsts, List.map_map, List.mem_map] at hct
    obtain ⟨⟨j, C⟩, hjC, hce⟩ := hct
    replace hce : C.name = c := hce
    obtain ⟨T, hT, hC⟩ := VInductDecl'.mem_ctorsAll hjC
    have hE : E₂.constants C.name = some ⟨D.uvars, C.type D j⟩ :=
      VEnv.addConstList_constants h₂ (C.name, ⟨D.uvars, C.type D j⟩)
        (by rw [VInductDecl'.ctorConsts, List.mem_map]; exact ⟨(j, C), hjC, rfl⟩)
    subst hce
    rw [hE] at hc; cases hc
    have hK : T.name ∉ K := fun hK => by
      rw [csubst_ctor_eq_some hdn hT hK hC] at hn; exact absurd hn nofun
    have hTe : D.types.getD j default = T := by rw [List.getD_eq_getElem?_getD, hT]; rfl
    have hmem :
        (R.ctorName C.name, (⟨D.uvars, (C.typeR D R j).substC (R.csubstTy D K)⟩ : VConstant))
          ∈ D.ctorConstsCR R K := by
      rw [VInductDecl'.ctorConstsCR, List.mem_filterMap]
      exact ⟨(j, C), hjC, by simp only []; rw [if_neg (by rw [hTe]; exact hK)]⟩
    have := VEnv.addConstList_constants f₂ _ hmem
    rw [hown.ctorName j T hT hK C hC] at this
    rw [this]
    congr 1
    exact congrArg _ ((substC_ctorType_csubst_eq_csubstTy hE₁ hdn h₁ h₂ h₃ hD hT hC).trans
      (hbridge j T C hT hK hC)).symm
  · by_cases hbn : c ∈ D.blockNames
    · rw [VInductDecl'.blockNames_eq, List.mem_map] at hbn
      obtain ⟨T, hTm, rfl⟩ := hbn
      obtain ⟨j, hT⟩ := List.getElem?_of_mem hTm
      have hK : T.name ∉ K := fun hK => by
        rw [csubst_ty_eq_some hdn hT hK] at hn; exact absurd hn nofun
      have hE : E₁.constants T.name = some ⟨D.uvars, T.type⟩ :=
        VEnv.addConstList_constants h₁ (T.name, ⟨D.uvars, T.type⟩)
          (by rw [VInductDecl'.typeConsts, List.mem_map]; exact ⟨T, hTm, rfl⟩)
      rw [VEnv.addConstList_constants_of_not_mem h₂ hct, hE] at hc
      cases hc
      have h1 : e₁.constants T.name = some ⟨D.uvars, T.type⟩ :=
        VEnv.addConstList_constants f₁ (T.name, ⟨D.uvars, T.type⟩)
          (by rw [VInductDecl'.typeConstsC, List.mem_filterMap]
              exact ⟨(T.name, ⟨D.uvars, T.type⟩),
                by rw [VInductDecl'.typeConsts, List.mem_map]; exact ⟨T, hTm, rfl⟩,
                by rw [if_neg hK]⟩)
      rw [VEnv.addConstList_constants_of_not_mem f₂
        (fun hm => hct (mem_ctorConstsCR_names hown hm)), h1]
      exact congrArg _ (by rw [substC_tyType_eq henv hD h₁ h₂ h₃ hTm])
    · rw [VEnv.addConstList_constants_of_not_mem h₂ hct,
        VEnv.addConstList_constants_of_not_mem h₁
          (by rw [VInductDecl'.typeConsts_names]; exact hbn)] at hc
      rw [VEnv.addConstList_constants_of_not_mem f₂
          (fun hm => hct (mem_ctorConstsCR_names hown hm)),
        VEnv.addConstList_constants_of_not_mem f₁ (fun hm => hbn (mem_typeConstsC_names hm)), hc]
      exact congrArg _ (by rw [(henv.noCSubstC (csubst_freshIn h₁ h₂ h₃) hc).substC_eq])

theorem csubst_WF_defeq (henv : env.Ordered)
    (h₁ : env.addIndTypes D = some E₁) (h₂ : E₁.addIndCtors D = some E₂)
    (h₃ : E₂.addIndRecs D = some E₃)
    (f₁ : env.addConstList (D.typeConstsC K) = some e₁)
    (f₂ : e₁.addConstList (D.ctorConstsCR R K) = some e₂)
    {df : VDefEq} (hdf : E₂.defeqs df) : e₂.defeqs (df.substC (R.csubst D K)) := by
  rw [VEnv.addConstList_defeqs h₂, VEnv.addConstList_defeqs h₁] at hdf
  rw [(henv.noCSubstD (csubst_freshIn h₁ h₂ h₃) hdf).substC_eq,
    VEnv.addConstList_defeqs f₂, VEnv.addConstList_defeqs f₁]
  exact hdf

/-! ## §8.5 The `val` clause: two positions, not three

At the second stage the companion members' **recursor** entries of `csubst`'s domain impose
nothing, because `E₂` does not declare them yet and `CSubst.WF.val` is guarded by
`env₀.constants c = some ci`.  So `val` is exactly two `HasType` obligations here.  At the
third stage (`E₃`, what obligation (C) needs) the recursor entry becomes live — a third
obligation that (C) faces and (B) does not. -/

theorem csubst_val_cases
    (h₁ : env.addIndTypes D = some E₁) (h₂ : E₁.addIndCtors D = some E₂)
    (h₃ : E₂.addIndRecs D = some E₃)
    (hty : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K →
      e₂.HasType D.uvars [] (R.tyVal D j) (T.type.substC (R.csubst D K)))
    (hctor : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K → ∀ C ∈ T.ctors,
      e₂.HasType D.uvars [] (R.ctorVal D j C) ((C.type D j).substC (R.csubst D K)))
    {c : Name} {t : VExpr} {ci : VConstant}
    (hσ : R.csubst D K c = some t) (hc : E₂.constants c = some ci) :
    e₂.HasType ci.uvars [] t (ci.type.substC (R.csubst D K)) := by
  obtain ⟨j, T, hT, hK, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨C, hC, rfl, rfl⟩⟩ := csubst_dom hσ
  · have hE : E₂.constants T.name = some ⟨D.uvars, T.type⟩ :=
      (VEnv.addConstList_le h₂).constants
        (VEnv.addConstList_constants h₁ (T.name, ⟨D.uvars, T.type⟩)
          (by rw [VInductDecl'.typeConsts, List.mem_map]
              exact ⟨T, List.mem_of_getElem? hT, rfl⟩))
    rw [hE] at hc; cases hc
    exact hty j T hT hK
  · exact absurd (((VEnv.addConstList_fresh h₃).1 (Lean.mkRecName T.name)
      (by rw [D.recConsts_names]
          exact List.mem_map.2 ⟨_, List.mem_of_getElem? hT, rfl⟩)) ▸ hc) nofun
  · have hE : E₂.constants C.name = some ⟨D.uvars, C.type D j⟩ :=
      VEnv.addConstList_constants h₂ (C.name, ⟨D.uvars, C.type D j⟩)
        (by rw [VInductDecl'.ctorConsts, List.mem_map]
            exact ⟨(j, C), VInductDecl'.mem_ctorsAll_of hT hC, rfl⟩)
    rw [hE] at hc; cases hc
    exact hctor j T hT hK C hC

/-! ## §8.6 The packaged reduction -/

/-- **`(R.csubst D K).WF E₂ e₂ U`, with only the `val` clause left.**

`closed`, `const` and `defeq` are discharged; `hval` is the residual.  Note the three
hypotheses that make (B) strictly downstream of (A): `he₂` (`e₂.Ordered`, which
`addConstList_ordered` gives from (A)'s conclusion), `hbridge` (obligation (A)'s bridge), and
`hval`.  The statement is `U`-polymorphic — `CSubst.val_of_hasType` absorbed the level
clause — so the same instance serves `D.recUvars` for (B) and each `df.uvars` for (C). -/
theorem csubst_WF (henv : env.Ordered) (hE₁ : E₁.Ordered) (he₂ : e₂.Ordered) (hD : D.WF env)
    (hown : R.OwnId D K) (hdn : R.DomNodup D K)
    (h₁ : env.addIndTypes D = some E₁) (h₂ : E₁.addIndCtors D = some E₂)
    (h₃ : E₂.addIndRecs D = some E₃)
    (f₁ : env.addConstList (D.typeConstsC K) = some e₁)
    (f₂ : e₁.addConstList (D.ctorConstsCR R K) = some e₂)
    (hclp : VExpr.ClosedTele D.params 0)
    (hcla : ∀ j, ∀ a ∈ R.tyArgs j, a.ClosedN D.np)
    (hbridge : ∀ (j : Nat) (T : VIndType) (C : VIndCtor), D.types[j]? = some T →
      T.name ∉ K → C ∈ T.ctors →
      (C.type D j).substC (R.csubstTy D K) = (C.typeR D R j).substC (R.csubstTy D K))
    (hval : ∀ {c : Name} {t : VExpr} {ci : VConstant}, R.csubst D K c = some t →
      E₂.constants c = some ci →
      e₂.HasType ci.uvars [] t (ci.type.substC (R.csubst D K))) :
    (R.csubst D K).WF E₂ e₂ U :=
  CSubst.WF_of_hasType he₂ (csubst_closed R D K hclp hcla)
    (fun hs hc => hval hs hc)
    (fun hs hc => csubst_WF_const henv hE₁ hD hown hdn h₁ h₂ h₃ f₁ f₂ hbridge hs hc)
    (fun hdf => csubst_WF_defeq henv h₁ h₂ h₃ f₁ f₂ hdf)

/-! ## §8.7 What `Faithful` gives, and what it cannot

`VIndRestore.Faithful.ty_agree` is a **syntactic** instantiation equation; the `val` clause is a
**typing** judgement.  §8.7 measures the gap exactly. -/

variable {npJ : Nat → Nat}

/-- **The `val` clause at a companion member's type, reduced.**  The two hypotheses are the
whole gap between `Faithful.ty_agree` and a typing derivation: `hsplit` says the presented head
really has `npJ j` leading binders, `hargs` says the presented spine is well typed against
them. -/
theorem tyVal_hasType_of_faithful (hfa : R.Faithful D env K npJ) (hle : env ≤ e₂)
    (hparams : OnCtx D.params.reverse (e₂.IsType D.uvars))
    {j : Nat} {T : VIndType} (hT : D.types[j]? = some T) (hK : T.name ∈ K)
    (hlvl : ∀ l ∈ R.tyLvls j, l.WF D.uvars)
    (hsplit : ∀ ci : VConstant, env.constants (R.tyName j) = some ci →
      ci.type.instL (R.tyLvls j)
        = VExpr.mkPi (VExpr.splitPis (npJ j) (ci.type.instL (R.tyLvls j))).1
            (VExpr.splitPis (npJ j) (ci.type.instL (R.tyLvls j))).2)
    (hargs : ∀ ci : VConstant, env.constants (R.tyName j) = some ci →
      e₂.HasArgs D.uvars D.params.reverse
        (VExpr.splitPis (npJ j) (ci.type.instL (R.tyLvls j))).1 (R.tyArgs j)) :
    e₂.HasType D.uvars [] (R.tyVal D j) T.type := by
  obtain ⟨ci, hci, huv, heq⟩ := hfa.ty_agree j T hT hK
  rw [← heq, VIndRestore.instAt, tyVal]
  refine VEnv.HasType.mkLams (by simpa using hparams) ?_
  rw [List.append_nil]
  have hconst : e₂.HasType D.uvars D.params.reverse (.const (R.tyName j) (R.tyLvls j))
      (ci.type.instL (R.tyLvls j)) := VEnv.HasType.const (hle.constants hci) hlvl huv.symm
  rw [hsplit ci hci] at hconst
  exact VEnv.HasType.mkApp' (hargs ci hci) hconst

/-- **…and `Faithful` cannot supply `hargs`: `instAt` does not always read the spine.**

`VIndRestore.instAt` substitutes the presented spine into the **body** of the head's type after
`npJ j` binders have been split off.  When that body is closed the substitution is the identity,
so `instAt` — and therefore `Faithful`'s `ty_agree` and `ctor_agree`, which are equations
*about* `instAt` — takes the same value for **every** spine whatsoever, including one that is
not typeable at all.  So `hargs` is not a lemma waiting to be proved from `Faithful`: no
restoration-independent argument can produce it, and it has to be supplied as data.

The configuration is not exotic: a member presented as a block whose stored type does not
mention its own parameters (`Foo : Type → Type 1`, body `sort 2` after one split) has exactly
this shape. -/
theorem instAt_indep_of_tyArgs {e : VExpr} {npJ' j : Nat}
    (hcl : (VExpr.splitPis npJ' (e.instL (R.tyLvls j))).2.ClosedN 0) (R' : VIndRestore)
    (hn : R'.tyLvls j = R.tyLvls j) :
    R'.instAt D npJ' j e
      = VExpr.mkPi D.params (VExpr.splitPis npJ' (e.instL (R.tyLvls j))).2 := by
  rw [VIndRestore.instAt, hn]
  congr 1
  clear hn
  induction R'.tyArgs j generalizing npJ' with
  | nil => rfl
  | cons a as ih => rw [VExpr.instAll_cons, hcl.instN_eq (Nat.zero_le _)]; exact ih hcl

end VIndRestore

/-! ## §8.8 The β-gap: closed, with machinery that already existed

The standing account of the β-gap was that `Theory/Typing/ChurchRosser.lean`'s `ParRedS.defeq`
is the right machinery but is gated behind `class VEnv.Params`, whose `henv : env.WF` field is
circular through `addInduct_WF` — leaving "a direct typed-β lemma avoiding it" open.

The `henv : env.WF` reading of `Params` is correct (`ChurchRosser.lean:12`).  The conclusion is
not: **the direct typed-β lemma already exists.**  `VEnv.IsDefEq.betaMkLams`
(`Theory/Inductive/StructureClosed.lean:305`) is exactly "the multi-β judgement for a saturated
`mkLams`", it takes `env.Ordered` and nothing more, and it is sorry-free.  `IsDefEq` has `beta`
as a *primitive constructor* (`Theory/Typing/Basic.lean:45`), so one typed β-step never needed
confluence at all; `betaMkLams` is the iteration, and `VEnv.IsDefEq.mkAppDF` carries it under
the arguments past the parameter telescope.

What is left after that is `hbody` below — and `hbody` is *the same statement* as §8.7's
`hargs`, the residual of the `val` clause.  So the β-gap and the `CSubst.WF` remainder are one
obligation. -/

namespace VIndRestore
variable {R : VIndRestore} {D : VInductDecl'} {K : List Name} {e : VEnv}

/-- **The β-gap head equation, as a `IsDefEq`, with no bound on `D.np`.**

`substC_tyApp_comp` says a companion head becomes a saturated `D.np`-fold redex;
`instAll_tyBody` says its contractum is `VInductDecl'.tyAppR`.  The missing step was never
Church–Rosser: `VEnv.IsDefEq.betaMkLams` (`Theory/Inductive/StructureClosed.lean`) is the
multi-β judgement for a saturated `mkLams` and needs only `env.Ordered` — not `env.WF`, so
not `VEnv.Params`, so **not circular through `addInduct_WF`**.  Composed with
`VEnv.IsDefEq.mkAppDF` for the arguments past the parameters, that is this lemma.

The residual is `hbody`: the presented head applied to the presented spine must be **well
typed**.  That is the *same* residual as the `val` clause of `(R.csubst D K).WF` (§8.7's
`hargs`), so the β-gap and the `CSubst.WF` remainder are one obligation, not two. -/
theorem substC_tyApp_defeq_tyAppR_comp (hnd : D.blockNames.Nodup)
    (hlw : ∀ i, (R.tyVal D i).LevelWF D.uvars)
    (hcl : ∀ i, ∀ a ∈ R.tyArgs i, a.ClosedN D.np) (henv : e.Ordered)
    {j : Nat} {T : VIndType} (hT : D.types[j]? = some T) (hK : T.name ∈ K)
    {k : Nat} {args Γ As : List VExpr} {B B' : VExpr}
    (hargs : ∀ a ∈ args, a.NoCSubst (R.csubstTy D K))
    (hOn : OnCtx (D.params.reverse ++ Γ) (e.IsType D.uvars))
    (hbv : e.HasArgs D.uvars Γ D.params (VExpr.bvars k D.np))
    (hbody : e.HasType D.uvars (D.params.reverse ++ Γ) (R.tyBody D j) B)
    (hpi : VExpr.instAll B (VExpr.bvars k D.np) = VExpr.mkPi As B')
    (hAs : e.HasArgs D.uvars Γ As args) :
    e.IsDefEq D.uvars Γ ((D.tyApp j k args).substC (R.csubstTy D K))
      (D.tyAppR R j k args) (VExpr.instAll B' args) := by
  have hbeta := VEnv.IsDefEq.betaMkLams henv hOn hbv hbody
  rw [hpi] at hbeta
  have hstep := VEnv.IsDefEq.mkAppDF hAs.toDF hbeta
  rw [instAll_tyBody (hcl j) k args] at hstep
  rwa [substC_tyApp_comp hnd hT hK (hlw j) hargs, VExpr.mkApp_append]

/-- **…and both head positions at once.**  Off `K` the head does not move at all
(`substC_tyApp_own`), so this is the `IsDefEqU` form of
`VIndRestore.substC_tyApp_eq_tyAppR` with the `D.params = []` hypothesis **removed**. -/
theorem substC_tyApp_defeqU_tyAppR (hnd : D.blockNames.Nodup) (hown : R.OwnId D K)
    (hlw : ∀ i, (R.tyVal D i).LevelWF D.uvars)
    (hcl : ∀ i, ∀ a ∈ R.tyArgs i, a.ClosedN D.np) (henv : e.Ordered)
    {j : Nat} {T : VIndType} (hT : D.types[j]? = some T)
    {k : Nat} {args Γ : List VExpr}
    (hargs : ∀ a ∈ args, a.NoCSubst (R.csubstTy D K))
    (hcomp : T.name ∈ K → ∃ (As : List VExpr) (B B' : VExpr),
      OnCtx (D.params.reverse ++ Γ) (e.IsType D.uvars) ∧
      e.HasArgs D.uvars Γ D.params (VExpr.bvars k D.np) ∧
      e.HasType D.uvars (D.params.reverse ++ Γ) (R.tyBody D j) B ∧
      VExpr.instAll B (VExpr.bvars k D.np) = VExpr.mkPi As B' ∧
      e.HasArgs D.uvars Γ As args)
    (hown' : T.name ∉ K → e.IsDefEqU D.uvars Γ (D.tyAppR R j k args) (D.tyAppR R j k args)) :
    e.IsDefEqU D.uvars Γ ((D.tyApp j k args).substC (R.csubstTy D K))
      (D.tyAppR R j k args) := by
  by_cases hK : T.name ∈ K
  · obtain ⟨As, B, B', hOn, hbv, hbody, hpi, hAs⟩ := hcomp hK
    exact ⟨_, substC_tyApp_defeq_tyAppR_comp hnd hlw hcl henv hT hK hargs hOn hbv hbody hpi hAs⟩
  · rw [substC_tyApp_own hown hT hK hargs]; exact hown' hK


/-! ## §8.9 The β-gap at the *recursor's* level numbering, and at `csubst`

§8.8 closes the β-gap for `VInductDecl'.tyApp` at `R.csubstTy D K` — the head obligation (A)
consumes.  Obligations (B) and (C) consume three other heads, and none of them is an instance
of §8.8:

* `VInductDecl'.tyApp'` and `VInductDecl'.ctorApp'` — the **primed** heads, instantiated at
  `D.selfLvls` rather than `D.ownLvls` (`Theory/Inductive/Decl.lean`), which is where the whole
  recursor construction lives;
* the recursor constant, which `R.recVal` only **renames** — a `substC` value with no `mkLams`,
  hence no β-gap at all (`substC_recConst` already has it, with no bound on `D.np`).

So the primed pair is what is missing, and this section supplies it.  Each is the same three
steps as §8.8 — compute the redex (`substC_tyApp'_comp` / `substC_ctorApp'_comp`), identify the
contractum (`instAll_tyBody'` / `instAll_ctorBody'`), and run `VEnv.IsDefEq.betaMkLams` under
`VEnv.IsDefEq.mkAppDF` — and each is stated at a **general** `σ` satisfying
`VIndRestore.SubstAt`, so `R.csubst D K` is an instance via `DomSep.substAt`.

Two things are worth stating plainly about the reach of this.

**`hcl` is `ClosedN D.np`, not `ClosedN 0`.**  §7.4's head *equations* need
`hcl0 : ∀ a ∈ R.tyArgs i, a.ClosedN 0`, which the parameterised witness **refutes**
(`InductiveDeclExamples.ntree_not_tyArgs_closed0`).  The defeqs here need only
`ClosedN D.np` — the hypothesis `csubst_WF` already carries as `hcla` — so `hcl0` is not a
second obstruction hiding behind `hp`.  `InductiveDeclExamples.ntree_tyArgs_closedN_np` is that
same witness satisfying the weaker hypothesis.

**`hp : D.params = []` enters §7.5/§7.6 at three sites, not two.**  Two are the head equations
`substC_tyApp'_eq_tyAppR'` and `substC_ctorApp'_eq_ctorAppR`, via `hnp : D.np = 0`.  The third
is `csubst_closed' hp hcl0`, whose `σ.Closed` conclusion `VExpr.map_substC_liftTele` needs in
`substC_minors` and `substC_iotaCtx`.  That third one is **not** an obstruction: `σ.Closed` is
`VIndRestore.csubst_closed`, which asks for `VExpr.ClosedTele D.params 0` and
`ClosedN D.np` — both available above `D.np = 0`, and both already hypotheses of `csubst_WF`.
It is only `csubst_closed'`, the convenience instance, that routes through `hp`. -/

/-- The body of `R.ctorVal D j C`, the constructor counterpart of `VIndRestore.tyBody`. -/
def ctorBody (R : VIndRestore) (_D : VInductDecl') (j : Nat) (C : VIndCtor) : VExpr :=
  (VExpr.const (R.ctorName C.name) (R.tyLvls j)).mkApp (R.tyArgs j)

section
variable {R : VIndRestore} {D : VInductDecl'} {K : List Name} {σ : CSubst} {e : VEnv}
variable {U j : Nat} {T : VIndType} {C : VIndCtor}

theorem ctorVal_eq (R : VIndRestore) (D : VInductDecl') (j : Nat) (C : VIndCtor) :
    R.ctorVal D j C = VExpr.mkLams D.params (R.ctorBody D j C) := rfl

theorem tyVal_instL_selfLvls :
    (R.tyVal D j).instL D.selfLvls
      = VExpr.mkLams (D.atRecTele D.params) (D.atRec (R.tyBody D j)) := by
  rw [tyVal_eq, VExpr.instL_mkLams, VInductDecl'.atRecTele, VInductDecl'.atRec]

theorem ctorVal_instL_selfLvls :
    (R.ctorVal D j C).instL D.selfLvls
      = VExpr.mkLams (D.atRecTele D.params) (D.atRec (R.ctorBody D j C)) := by
  rw [ctorVal_eq, VExpr.instL_mkLams, VInductDecl'.atRecTele, VInductDecl'.atRec]

/-- **The contractum of the substituted primed type head is `tyAppR'`, exactly.**  The
`instL D.selfLvls` version of `instAll_tyBody`; `ClosedN` survives `instL`, which is why no
extra hypothesis appears. -/
theorem instAll_tyBody' (hcl : ∀ a ∈ R.tyArgs j, a.ClosedN D.np) (k : Nat)
    (args : List VExpr) :
    (VExpr.instAll (D.atRec (R.tyBody D j)) (VExpr.bvars k D.np)).mkApp args
      = D.tyAppR' R j k args := by
  rw [VInductDecl'.atRec, tyBody, VExpr.instL_mkApp, VExpr.instL_const',
    VExpr.instAll_mkApp, VExpr.instAll_const, VInductDecl'.tyAppR',
    VInductDecl'.tyAppH, ← VExpr.mkApp_append, VInductDecl'.atRecTele, List.map_map,
    List.map_map]
  congr 2
  exact List.map_congr_left fun a ha =>
    VExpr.instAll_bvars_lift (by simpa using (hcl a ha).instL)

/-- …and of the substituted constructor head is `ctorAppR`. -/
theorem instAll_ctorBody' (hcl : ∀ a ∈ R.tyArgs j, a.ClosedN D.np) (k : Nat)
    (args : List VExpr) :
    (VExpr.instAll (D.atRec (R.ctorBody D j C)) (VExpr.bvars k D.np)).mkApp args
      = D.ctorAppR R j C k args := by
  rw [VInductDecl'.atRec, ctorBody, VExpr.instL_mkApp, VExpr.instL_const',
    VExpr.instAll_mkApp, VExpr.instAll_const, VInductDecl'.ctorAppR,
    ← VExpr.mkApp_append, VInductDecl'.atRecTele, List.map_map, List.map_map]
  congr 2
  exact List.map_congr_left fun a ha =>
    VExpr.instAll_bvars_lift (by simpa using (hcl a ha).instL)

/-- **A companion primed type head becomes a saturated `D.np`-fold redex.**  Unlike
`substC_tyApp_comp` this needs no `LevelWF` hypothesis: the value is re-instantiated at
`D.selfLvls` and `tyAppR'` is defined at exactly that instantiation. -/
theorem substC_tyApp'_comp (hat : R.SubstAt D K σ) (hT : D.types[j]? = some T)
    (hK : T.name ∈ K) (k : Nat) (args : List VExpr) :
    (D.tyApp' j k args).substC σ
      = (VExpr.mkLams (D.atRecTele D.params) (D.atRec (R.tyBody D j))).mkApp
          (VExpr.bvars k D.np ++ args.map (VExpr.substC · σ)) := by
  have hg : (D.types.getD j default).name = T.name := by
    rw [List.getD_eq_getElem?_getD, hT]; rfl
  rw [VInductDecl'.tyApp', VExpr.substC_mkApp, List.map_append, VExpr.map_substC_bvars,
    VExpr.substC_const_some (by rw [hg]; exact hat.tySome j T hT hK),
    tyVal_instL_selfLvls]

/-- …and so does a companion constructor head. -/
theorem substC_ctorApp'_comp (hat : R.SubstAt D K σ) (hT : D.types[j]? = some T)
    (hK : T.name ∈ K) (hC : C ∈ T.ctors) (k : Nat) (args : List VExpr) :
    (D.ctorApp' C k args).substC σ
      = (VExpr.mkLams (D.atRecTele D.params) (D.atRec (R.ctorBody D j C))).mkApp
          (VExpr.bvars k D.np ++ args.map (VExpr.substC · σ)) := by
  rw [VInductDecl'.ctorApp', VExpr.substC_mkApp, List.map_append, VExpr.map_substC_bvars,
    VExpr.substC_const_some (hat.ctorSome j T hT hK C hC), ctorVal_instL_selfLvls]

/-- **§8.8 for the primed type head, at a general `σ`: no bound on `D.np`.**

The residual is again `hbody` + `hAs` — the presented head applied to the presented spine,
well typed — i.e. §8.7's `hargs`.  `U` is free, so `D.recUvars` (what (B) and (C) need) is as
available as `D.uvars`. -/
theorem substC_tyApp'_defeq_tyAppR'_comp (hat : R.SubstAt D K σ)
    (hcl : ∀ a ∈ R.tyArgs j, a.ClosedN D.np) (henv : e.Ordered)
    (hT : D.types[j]? = some T) (hK : T.name ∈ K)
    {k : Nat} {args Γ As : List VExpr} {B B' : VExpr}
    (hOn : OnCtx ((D.atRecTele D.params).reverse ++ Γ) (e.IsType U))
    (hbv : e.HasArgs U Γ (D.atRecTele D.params) (VExpr.bvars k D.np))
    (hbody : e.HasType U ((D.atRecTele D.params).reverse ++ Γ)
      (D.atRec (R.tyBody D j)) B)
    (hpi : VExpr.instAll B (VExpr.bvars k D.np) = VExpr.mkPi As B')
    (hAs : e.HasArgs U Γ As (args.map (VExpr.substC · σ))) :
    e.IsDefEq U Γ ((D.tyApp' j k args).substC σ)
      (D.tyAppR' R j k (args.map (VExpr.substC · σ)))
      (VExpr.instAll B' (args.map (VExpr.substC · σ))) := by
  have hbeta := VEnv.IsDefEq.betaMkLams henv hOn hbv hbody
  rw [hpi] at hbeta
  have hstep := VEnv.IsDefEq.mkAppDF hAs.toDF hbeta
  rw [instAll_tyBody' (R := R) (D := D) (j := j) hcl k (args.map (VExpr.substC · σ))] at hstep
  rwa [substC_tyApp'_comp hat hT hK, VExpr.mkApp_append]

/-- **…and for the constructor head — the ingredient (B) and (C) share.** -/
theorem substC_ctorApp'_defeq_ctorAppR_comp (hat : R.SubstAt D K σ)
    (hcl : ∀ a ∈ R.tyArgs j, a.ClosedN D.np) (henv : e.Ordered)
    (hT : D.types[j]? = some T) (hK : T.name ∈ K) (hC : C ∈ T.ctors)
    {k : Nat} {args Γ As : List VExpr} {B B' : VExpr}
    (hOn : OnCtx ((D.atRecTele D.params).reverse ++ Γ) (e.IsType U))
    (hbv : e.HasArgs U Γ (D.atRecTele D.params) (VExpr.bvars k D.np))
    (hbody : e.HasType U ((D.atRecTele D.params).reverse ++ Γ)
      (D.atRec (R.ctorBody D j C)) B)
    (hpi : VExpr.instAll B (VExpr.bvars k D.np) = VExpr.mkPi As B')
    (hAs : e.HasArgs U Γ As (args.map (VExpr.substC · σ))) :
    e.IsDefEq U Γ ((D.ctorApp' C k args).substC σ)
      (D.ctorAppR R j C k (args.map (VExpr.substC · σ)))
      (VExpr.instAll B' (args.map (VExpr.substC · σ))) := by
  have hbeta := VEnv.IsDefEq.betaMkLams henv hOn hbv hbody
  rw [hpi] at hbeta
  have hstep := VEnv.IsDefEq.mkAppDF hAs.toDF hbeta
  rw [instAll_ctorBody' (R := R) (D := D) (j := j) (C := C) hcl k
    (args.map (VExpr.substC · σ))] at hstep
  rwa [substC_ctorApp'_comp hat hT hK hC, VExpr.mkApp_append]

/-! ### The join, on one entry of the recursor telescope

The point of §8.9 together with `VEnv.recConstsR_wf_of_substC'` is that the chain
*head defeq → entry defeq → telescope defeq → obligation* now composes above `D.np = 0`.  The
motive entry is the shortest instance where it does, so it is checked here.

What this measures is where the remaining work is.  The entry defeq needs the entry's own
`OnCtx` in the substituted environment; that is `VInductDecl'.motives`' typing, which for the
whole recursor telescope (`atRecTele D.params ++ motives ++ minors ++ indices`) is the D-series
of `Theory/Inductive/Lemmas.lean`, restated at `e₂`.  It is **not** a further β-gap.

**The verdict, stated plainly: the two bridges are necessary for lifting (B)/(C) off
`D.np = 0` and they are not sufficient.**  With `recConstsR_wf_of_substC'` /
`iotaRulesRS_wf_of_substC'` and §8.9 in place, three things stand between
`VEnv.recConstsR_wf_of_np_zero` / `iotaRulesRS_wf_of_np_zero` and their parameterised
analogues, and none of them is a bridge:

1. **The same data residual as §8.8 and §8.7.**  Each head defeq's `hbody` + `hAs` is the
   presented head applied to the presented spine, well typed — §8.7's `hargs`.  So
   `instAt_indep_of_tyArgs`' lower bound transports verbatim: `VIndRestore.Faithful` cannot
   supply it for (B) or (C) either, for exactly the reason it cannot for the `val` clause.
2. **Telescope typing at the *substituted* environment.**  Every `TeleDefEq.rfl` and every
   `mkPi_congrU`/`mkLams_congr` step needs `OnCtx` of the substituted binder context in `e₂`
   (for (B)) or `e₃` (for (C)).  That is `Theory/Inductive/Lemmas.lean`'s D-series moved across
   the substitution — bulk, not depth.
3. **A `TeleDefEq` in place of `substC_atRec_fieldTypes`' equality**, and a nested
   `mkPi_congrU` inside `VIndRecArg.canonTypeR`, because a *recursive field*'s companion head
   sits under the field's own `ξ`-telescope.  Same three ingredients as (1) and (2), one binder
   layer deeper.

What is *not* on the list: `hcl0` (see above), `σ.Closed` (see above), and any appeal to
confluence or to `VEnv.Params`. -/

/-- **One motive entry of the recursor telescope, at `D.np > 0`.**

Both sides' index telescope is literally the same list once `σ.Closed` moves the `substC`
through `liftTele`, so the whole entry defeq is `mkPi_congrU` over a reflexive `TeleDefEq`
with `forallEDF` at the body — and the domain defeq is
`substC_tyApp'_defeq_tyAppR'_comp` at `Γ = the index telescope`. -/
theorem substC_motiveType_defeq_of_head {t : Nat} (hσ : σ.Closed) (hfr : R.SubstFree D σ)
    (helim : D.elimLvl.WF U) (hg : D.types.getD t default = T) {w : VLevel}
    (hOn : OnCtx (VExpr.liftTele t ((D.atRecTele T.indices).map (VExpr.substC · σ)) 0).reverse
      (e.IsType U))
    (hhead : e.IsDefEq U
      (VExpr.liftTele t ((D.atRecTele T.indices).map (VExpr.substC · σ)) 0).reverse
      ((D.tyApp' t (T.indices.length + t) (VExpr.bvars 0 T.indices.length)).substC σ)
      (D.tyAppR' R t (T.indices.length + t) (VExpr.bvars 0 T.indices.length))
      (.sort w)) :
    ∃ u, e.IsDefEq U [] ((D.motiveType t).substC σ)
      ((D.motiveTypeR R t).substC σ) (.sort u) := by
  simp only [VInductDecl'.motiveType, VInductDecl'.motiveTypeR, hg,
    VExpr.substC_mkPi, VExpr.substC_forallE, VExpr.substC_sort,
    VExpr.map_substC_liftTele hσ, substC_tyAppR' hfr, VExpr.map_substC_bvars]
  have key := VEnv.IsDefEq.forallEDF hhead
    (.sortDF (l := D.elimLvl) (l' := D.elimLvl) helim helim rfl)
  exact VEnv.IsDefEq.mkPi_congrU (As' := VExpr.liftTele t
    ((D.atRecTele T.indices).map (VExpr.substC · σ)) 0) .refl (by simpa using hOn)
    ⟨_, by simpa using key⟩

/-- **…and the join itself, machine-checked.**  `substC_tyApp'_defeq_tyAppR'_comp` feeding
`substC_motiveType_defeq_of_head`: the chain from §8.9's head defeq to a recursor-telescope
entry defeq closes, with **no bound on `D.np`**.  The `substC` on the presented spine
disappears because that spine is `bvars` (`VExpr.map_substC_bvars`).

The hypotheses left are exactly the three the §8.9 verdict note lists: `hbody`/`hAs` (the
`hargs` data residual), `hOn`/`hOnp`/`hbv` (telescope typing at the substituted environment),
and `hpi`/`hsort` (the head's type is a pi that lands in a sort — a shape fact about the
companion's stored type, not a β-fact). -/
theorem substC_motiveType_defeq (hσ : σ.Closed) (hfr : R.SubstFree D σ)
    (hat : R.SubstAt D K σ) (hcl : ∀ a ∈ R.tyArgs t, a.ClosedN D.np) (henv : e.Ordered)
    (helim : D.elimLvl.WF U) (hT : D.types[t]? = some T) (hK : T.name ∈ K)
    (hg : D.types.getD t default = T)
    {As : List VExpr} {B B' : VExpr} {w : VLevel}
    (hOn : OnCtx (VExpr.liftTele t ((D.atRecTele T.indices).map (VExpr.substC · σ)) 0).reverse
      (e.IsType U))
    (hOnp : OnCtx ((D.atRecTele D.params).reverse ++
      (VExpr.liftTele t ((D.atRecTele T.indices).map (VExpr.substC · σ)) 0).reverse)
      (e.IsType U))
    (hbv : e.HasArgs U
      (VExpr.liftTele t ((D.atRecTele T.indices).map (VExpr.substC · σ)) 0).reverse
      (D.atRecTele D.params) (VExpr.bvars (T.indices.length + t) D.np))
    (hbody : e.HasType U ((D.atRecTele D.params).reverse ++
      (VExpr.liftTele t ((D.atRecTele T.indices).map (VExpr.substC · σ)) 0).reverse)
      (D.atRec (R.tyBody D t)) B)
    (hpi : VExpr.instAll B (VExpr.bvars (T.indices.length + t) D.np) = VExpr.mkPi As B')
    (hAs : e.HasArgs U
      (VExpr.liftTele t ((D.atRecTele T.indices).map (VExpr.substC · σ)) 0).reverse
      As (VExpr.bvars 0 T.indices.length))
    (hsort : VExpr.instAll B' (VExpr.bvars 0 T.indices.length) = .sort w) :
    ∃ u, e.IsDefEq U [] ((D.motiveType t).substC σ)
      ((D.motiveTypeR R t).substC σ) (.sort u) := by
  refine substC_motiveType_defeq_of_head hσ hfr helim hg (w := w) hOn ?_
  have := substC_tyApp'_defeq_tyAppR'_comp (R := R) (D := D) (K := K) (σ := σ) (U := U)
    (j := t) (T := T) hat hcl henv hT hK (k := T.indices.length + t)
    (args := VExpr.bvars 0 T.indices.length) hOnp hbv hbody hpi
    (by rwa [VExpr.map_substC_bvars])
  rwa [VExpr.map_substC_bvars, hsort] at this

end
end VIndRestore
end Lean4Lean
