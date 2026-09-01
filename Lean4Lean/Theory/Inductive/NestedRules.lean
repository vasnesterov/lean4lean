import Lean4Lean.Theory.Inductive.RestoreBridge

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
* §7.5 obligation **(B)**: `(D.recType j).substC σ' = (D.recTypeR R j).substC σ'`.
* §7.6 obligation **(C)**: `(D.iotaRule j q C).substC σ' = (D.iotaRuleR R j q C).substC σ'`,
  head by head over `iotaCtx`/`iotaLhs`/`iotaLam`/`ihValues`/`iotaType`.

Everything here is at `D.params = []`, the same reach Part 4b has: above it the two sides
differ by the β-gap of Part 3 (`substC_tyApp_comp` / `instAll_tyBody`), which is a *typed*
residual and not a syntactic one.
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

`DomNodup` is *not* derived here; the three `= none` clauses are, and they are the ones the
brief called not derivable.  What discharges them is `D.allNames.Nodup`: the three families it
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

end Lean4Lean
