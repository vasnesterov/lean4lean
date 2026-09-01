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

**What is still open.**  §7.5/§7.6 take `hcanon : D.Canonical` and the index bound `hpos` as
hypotheses, exactly as Part 4b's (A) bridge does; both follow from `D.WF env`
(`VIndField.WF.recArg_noBlock` for the second) but that derivation is the consumers' business,
not the bridges'.  `DomNodup` is still a `decide`-able side condition (§7.2), and the β-gap
above `D.params = []` is untouched.
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

`hcanon`/`hpos` are the two block-level side conditions (A) also carries, and both come from
`D.WF env`: `hcanon` is `VInductDecl'.Canonical` (`Theory/Inductive/Restore.lean` explains why
a *stored* recursive field is only definitionally canonical) and `hpos` is the index bound of
`VIndField.WF.pos`, read off by `VIndField.WF.recArg_noBlock`. -/

section
variable (hp : D.params = []) (hown : R.OwnId D K) (hat : R.SubstAt D K σ)
  (hcl0 : ∀ i, ∀ a ∈ R.tyArgs i, a.ClosedN 0) (hfr : R.SubstFree D σ)
include hp hown hat hcl0 hfr

/-- **The field telescope, at the recursor's numbering.**  This is Part 4b's `hfl` at
`R.csubst`, with `atRec` kept *inside* the substitution so that only the **primed** head
equations of §7.4 are needed — no `LevelWF` hypothesis. -/
theorem substC_atRec_fieldTypes {C : VIndCtor} (hcanon : C.Canonical D)
    (hpos : ∀ (i : Nat) (F : VIndField) (r : VIndRecArg), C.fields[i]? = some F →
      F.recArg = some r → r.idx < D.nm) :
    (D.atRecTele (C.fields.map (·.type))).map (VExpr.substC · σ)
      = (D.atRecTele (C.fieldTypesR D R)).map (VExpr.substC · σ) := by
  have key : ∀ (Fs : List VIndField) (i : Nat),
      (∀ (k : Nat) (F : VIndField) (r : VIndRecArg), Fs[k]? = some F → F.recArg = some r →
        F.type = r.canonType D (i + k) ∧ r.idx < D.nm) →
      Fs.map (fun F => (D.atRec F.type).substC σ)
        = (Fs.zipIdx i).map (fun p => (D.atRec (p.1.typeR D R p.2)).substC σ) := by
    intro Fs
    induction Fs with
    | nil => intro _ _; rfl
    | cons F Fs ih =>
      intro i hs
      rw [List.zipIdx_cons, List.map_cons, List.map_cons,
        ih (i+1) (fun k F' r hF' hr => by
          rw [show i + 1 + k = i + (k+1) from by omega]
          exact hs (k+1) F' r (by simpa using hF') hr)]
      congr 1
      cases hr : F.recArg with
      | none => rw [show F.typeR D R i = F.type from by rw [VIndField.typeR, hr]]
      | some r =>
        obtain ⟨hct, hlt⟩ := hs 0 F r rfl hr
        obtain ⟨T', hT'⟩ : ∃ T', D.types[r.idx]? = some T' := ⟨_, List.getElem?_eq_getElem hlt⟩
        rw [show F.typeR D R i = r.canonTypeR D R i from by rw [VIndField.typeR, hr],
          show i + 0 = i from rfl] at *
        rw [hct, VIndRecArg.canonType, VIndRecArg.canonTypeR]
        simp only [VInductDecl'.atRec, VExpr.instL_mkPi]
        rw [VExpr.substC_mkPi, VExpr.substC_mkPi,
          VIndRecArg.canonResult, VIndRecArg.canonResultR,
          show (D.tyApp r.idx (r.binders.length + i) r.args).instL D.selfLvls
              = D.tyApp' r.idx (r.binders.length + i) (D.atRecTele r.args) from
            VInductDecl'.atRec_tyApp D,
          show (D.tyAppR R r.idx (r.binders.length + i) r.args).instL D.selfLvls
              = D.tyAppR' R r.idx (r.binders.length + i) (D.atRecTele r.args) from
            VInductDecl'.atRec_tyAppH D,
          substC_tyApp'_eq_tyAppR' hp hown hat hcl0 hT',
          substC_tyAppR' hfr]
  rw [VInductDecl'.atRecTele, VInductDecl'.atRecTele, VIndCtor.fieldTypesR,
    List.map_map, List.map_map, List.map_map, List.map_map]
  exact key C.fields 0 (fun k F r hF hr => ⟨by simpa using hcanon k F r hF hr, hpos k F r hF hr⟩)

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
theorem substC_minors (hσ : σ.Closed) (hcanon : D.Canonical)
    (hpos : ∀ (t : Nat) (C : VIndCtor), (t, C) ∈ D.ctorsAll →
      ∀ (i : Nat) (F : VIndField) (r : VIndRecArg), C.fields[i]? = some F →
        F.recArg = some r → r.idx < D.nm) :
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
    substC_atRec_fieldTypes hp hown hat hcl0 hfr (hcanon t C hmem) (hpos t C hmem),
    substC_ctorApp'_eq_ctorAppR hp hown hat hcl0 hT hC, substC_ctorAppR hfr hT hC]

/-! ### §7.5 Obligation (B) -/

/-- **Obligation (B) for a parameterless nested block.**

    (D.recType j).substC σ = (D.recTypeR R j).substC σ

The three moving parts are the motives, the minors and the major premise's `tyApp'` head;
the parameter telescope, the index telescope, the induction-hypothesis telescope and the
conclusion are literally the same expression on both sides. -/
theorem substC_recType_eq (hσ : σ.Closed) (hcanon : D.Canonical)
    (hpos : ∀ (t : Nat) (C : VIndCtor), (t, C) ∈ D.ctorsAll →
      ∀ (i : Nat) (F : VIndField) (r : VIndRecArg), C.fields[i]? = some F →
        F.recArg = some r → r.idx < D.nm)
    {j : Nat} {T : VIndType} (hT : D.types[j]? = some T) :
    (D.recType j).substC σ = (D.recTypeR R j).substC σ := by
  have hg : D.types.getD j default = T := by rw [List.getD_eq_getElem?_getD, hT]; rfl
  simp only [VInductDecl'.recType, VInductDecl'.recTypeR, VExpr.substC_mkPi,
    VExpr.substC_forallE, VExpr.substC_mkApp, List.map_append, hg]
  rw [substC_motives hp hown hat hcl0 hfr,
    substC_minors hp hown hat hcl0 hfr hσ hcanon hpos,
    substC_tyApp'_eq_tyAppR' hp hown hat hcl0 hT, substC_tyAppR' hfr]

/-! ### §7.6 Obligation (C) -/

/-- The ι-rule's binder context, both restorations agreeing under `σ`. -/
theorem substC_iotaCtx (hσ : σ.Closed) (hcanon : D.Canonical)
    (hpos : ∀ (t : Nat) (C : VIndCtor), (t, C) ∈ D.ctorsAll →
      ∀ (i : Nat) (F : VIndField) (r : VIndRecArg), C.fields[i]? = some F →
        F.recArg = some r → r.idx < D.nm)
    {j : Nat} {T : VIndType} (hT : D.types[j]? = some T) {C : VIndCtor} (hC : C ∈ T.ctors) :
    (D.iotaCtx C).map (VExpr.substC · σ) = (D.iotaCtxR R C).map (VExpr.substC · σ) := by
  have hmem : (j, C) ∈ D.ctorsAll := VInductDecl'.mem_ctorsAll_of hT hC
  simp only [VInductDecl'.iotaCtx, VInductDecl'.iotaCtxR, List.map_append]
  rw [substC_motives hp hown hat hcl0 hfr,
    substC_minors hp hown hat hcl0 hfr hσ hcanon hpos,
    VExpr.map_substC_liftTele (σ := σ) hσ, VExpr.map_substC_liftTele (σ := σ) hσ,
    substC_atRec_fieldTypes hp hown hat hcl0 hfr (hcanon j C hmem) (hpos j C hmem)]

/-- …and therefore the two contexts have the same length, which is what the η-expanded
right-hand side of the rule applies its `bvars` run to. -/
theorem iotaCtx_length_eq (hσ : σ.Closed) (hcanon : D.Canonical)
    (hpos : ∀ (t : Nat) (C : VIndCtor), (t, C) ∈ D.ctorsAll →
      ∀ (i : Nat) (F : VIndField) (r : VIndRecArg), C.fields[i]? = some F →
        F.recArg = some r → r.idx < D.nm)
    {j : Nat} {T : VIndType} (hT : D.types[j]? = some T) {C : VIndCtor} (hC : C ∈ T.ctors) :
    (D.iotaCtx C).length = (D.iotaCtxR R C).length := by
  have := congrArg List.length (substC_iotaCtx hp hown hat hcl0 hfr hσ hcanon hpos hT hC)
  rwa [List.length_map, List.length_map] at this

omit hp hcl0 in
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
theorem substC_iotaLam (hσ : σ.Closed) (hcanon : D.Canonical)
    (hpos : ∀ (t : Nat) (C : VIndCtor), (t, C) ∈ D.ctorsAll →
      ∀ (i : Nat) (F : VIndField) (r : VIndRecArg), C.fields[i]? = some F →
        F.recArg = some r → r.idx < D.nm)
    {j : Nat} {T : VIndType} (hT : D.types[j]? = some T) {C : VIndCtor} (hC : C ∈ T.ctors)
    (q : Nat) :
    (D.iotaLam q C).substC σ = (D.iotaLamR R q C).substC σ := by
  have hmem : (j, C) ∈ D.ctorsAll := VInductDecl'.mem_ctorsAll_of hT hC
  simp only [VInductDecl'.iotaLam, VInductDecl'.iotaLamR, VExpr.substC_mkLams,
    VExpr.substC_mkApp, List.map_append]
  rw [substC_iotaCtx hp hown hat hcl0 hfr hσ hcanon hpos hT hC,
    substC_ihValues hown hat hfr (hpos j C hmem)]

/-- **Obligation (C) for a parameterless nested block.**

    (D.iotaRule j q C).substC σ = (D.iotaRuleR R j q C).substC σ

head by head over `iotaCtx`/`iotaLhs`/`iotaLam`/`ihValues`/`iotaType`. -/
theorem substC_iotaRule_eq (hσ : σ.Closed) (hcanon : D.Canonical)
    (hpos : ∀ (t : Nat) (C : VIndCtor), (t, C) ∈ D.ctorsAll →
      ∀ (i : Nat) (F : VIndField) (r : VIndRecArg), C.fields[i]? = some F →
        F.recArg = some r → r.idx < D.nm)
    {j : Nat} {T : VIndType} (hT : D.types[j]? = some T) {C : VIndCtor} (hC : C ∈ T.ctors)
    (q : Nat) :
    (D.iotaRule j q C).substC σ = (D.iotaRuleR R j q C).substC σ := by
  have hctx := substC_iotaCtx hp hown hat hcl0 hfr hσ hcanon hpos hT hC
  have hlen := iotaCtx_length_eq hp hown hat hcl0 hfr hσ hcanon hpos hT hC
  simp only [VDefEq.substC, VInductDecl'.iotaRule, VInductDecl'.iotaRuleR,
    VExpr.substC_mkLams, VExpr.substC_mkPi, VExpr.substC_mkApp, VExpr.map_substC_bvars,
    hctx, hlen, substC_iotaLhs hp hown hat hcl0 hfr hT hC,
    substC_iotaLam hp hown hat hcl0 hfr hσ hcanon hpos hT hC q,
    substC_iotaType hp hown hat hcl0 hfr hT hC]


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
variable (hp : D.params = []) (hown : R.OwnId D K) (hsep : R.DomSep D K)
  (hcl0 : ∀ i, ∀ a ∈ R.tyArgs i, a.ClosedN 0) (hfr : R.SubstFree D (R.csubst D K))
  (hcanon : D.Canonical)
  (hpos : ∀ (t : Nat) (C : VIndCtor), (t, C) ∈ D.ctorsAll →
    ∀ (i : Nat) (F : VIndField) (r : VIndRecArg), C.fields[i]? = some F →
      F.recArg = some r → r.idx < D.nm)
include hp hown hsep hcl0 hfr hcanon hpos

/-- **(B) at the real substitution** — the exact `hbridge` `VEnv.recConstsR_wf_of_substC`
takes. -/
theorem csubst_recType_eq (j : Nat) (T : VIndType) (hT : D.types[j]? = some T) :
    (D.recType j).substC (R.csubst D K) = (D.recTypeR R j).substC (R.csubst D K) :=
  substC_recType_eq hp hown hsep.substAt hcl0 hfr (csubst_closed' hp hcl0) hcanon hpos hT

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
  exact substC_iotaRule_eq hp hown hsep.substAt hcl0 hfr (csubst_closed' hp hcl0)
    hcanon hpos hT hC q

end

end VIndRestore

/-- **Obligation (B) of `VEnv.addInductR_ordered'`, closed for a parameterless nested
block.**  `hsrc` and `hσ` are the two hypotheses the non-nested recursor stage already
supplies; everything else is a syntactic side condition on the block or the restoration. -/
theorem VEnv.recConstsR_wf_of_np_zero {E₂ e₂ : VEnv} {D : VInductDecl'} {R : VIndRestore}
    {K : List Name}
    (hsrc : ∀ c ∈ D.recConsts, VConstant.WF E₂ c.2)
    (hσ : (R.csubst D K).WF E₂ e₂ D.recUvars)
    (hp : D.params = []) (hown : R.OwnId D K) (hsep : R.DomSep D K)
    (hcl0 : ∀ i, ∀ a ∈ R.tyArgs i, a.ClosedN 0)
    (hfr : R.SubstFree D (R.csubst D K)) (hcanon : D.Canonical)
    (hpos : ∀ (t : Nat) (C : VIndCtor), (t, C) ∈ D.ctorsAll →
      ∀ (i : Nat) (F : VIndField) (r : VIndRecArg), C.fields[i]? = some F →
        F.recArg = some r → r.idx < D.nm) :
    ∀ c ∈ D.recConstsR R K, VConstant.WF e₂ c.2 :=
  VEnv.recConstsR_wf_of_substC hsrc hσ
    (VIndRestore.csubst_recType_eq hp hown hsep hcl0 hfr hcanon hpos)

/-- **Obligation (C) of `VEnv.addInductR_ordered'`, closed for a parameterless nested
block.** -/
theorem VEnv.iotaRulesRS_wf_of_np_zero {E₃ e₃ : VEnv} {D : VInductDecl'} {R : VIndRestore}
    {K : List Name}
    (hsrc : ∀ df ∈ D.iotaRules, VDefEq.WF E₃ df)
    (hσ : ∀ df ∈ D.iotaRules, (R.csubst D K).WF E₃ e₃ df.uvars)
    (hp : D.params = []) (hown : R.OwnId D K) (hsep : R.DomSep D K)
    (hcl0 : ∀ i, ∀ a ∈ R.tyArgs i, a.ClosedN 0)
    (hfr : R.SubstFree D (R.csubst D K)) (hcanon : D.Canonical)
    (hpos : ∀ (t : Nat) (C : VIndCtor), (t, C) ∈ D.ctorsAll →
      ∀ (i : Nat) (F : VIndField) (r : VIndRecArg), C.fields[i]? = some F →
        F.recArg = some r → r.idx < D.nm) :
    ∀ df ∈ D.iotaRulesRS R K, VDefEq.WF e₃ df :=
  VEnv.iotaRulesRS_wf_of_substC hsrc hσ
    (VIndRestore.csubst_iotaRules_eq hp hown hsep hcl0 hfr hcanon hpos)

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

theorem nfnAux_pos : ∀ (t : Nat) (C : VIndCtor), (t, C) ∈ nfnAux.ctorsAll →
    ∀ (i : Nat) (F : VIndField) (r : VIndRecArg), C.fields[i]? = some F →
      F.recArg = some r → r.idx < nfnAux.nm := by
  intro t C h
  rw [nfnAux_ctorsAll_eq] at h
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := h
  · rintro (_ | i) F r hF hr
    · cases hF; cases hr; decide
    · simp [nfnNode] at hF
  · rintro (_ | _ | i) F r hF hr
    · cases hF; cases hr; decide
    · cases hF; cases hr; decide
    · simp [pfnAuxMk] at hF

/-! ### …and the two bridges, instantiated -/

/-- **(B) at the witness.** -/
theorem nfnAux_recTypeR_bridge (j : Nat) (T : VIndType) (hT : nfnAux.types[j]? = some T) :
    (nfnAux.recType j).substC (nfnRestore.csubst nfnAux nfnK)
      = (nfnAux.recTypeR nfnRestore j).substC (nfnRestore.csubst nfnAux nfnK) :=
  VIndRestore.csubst_recType_eq rfl nfnRestore_ownId nfnRestore_domSep
    nfnRestore_tyArgs_closed0 nfnRestore_substFree nfnAux_canonical nfnAux_pos j T hT

/-- **(C) at the witness.** -/
theorem nfnAux_iotaRules_substC_bridge :
    nfnAux.iotaRules.map (·.substC (nfnRestore.csubst nfnAux nfnK))
      = nfnAux.iotaRulesRS nfnRestore nfnK :=
  VIndRestore.csubst_iotaRules_eq rfl nfnRestore_ownId nfnRestore_domSep
    nfnRestore_tyArgs_closed0 nfnRestore_substFree nfnAux_canonical nfnAux_pos

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


end InductiveDeclExamples

end Lean4Lean
