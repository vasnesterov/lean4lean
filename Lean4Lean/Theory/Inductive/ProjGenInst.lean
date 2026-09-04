import Lean4Lean.Theory.Inductive.ProjGenLift

/-!
# Block A for `projCoreG`: commutation with `inst` and with `instL`

`ProjGenLift.lean` did the `lift'` half of block A.  This file does the other two halves,
mirroring `Theory/Inductive/Structure.lean:373–460` (`projCore_instN`, `projArgs_instN`,
`projTerm_instN`) and `:112–152` (`projCore_instL`, `projArgs_instL`, `projTerm_instL`) at
the **generalised** term `projCoreG`, whose motive and minor blocks are full length.

Two different hypothesis regimes, and the difference is real:

* the `instN` family carries `VInductDecl'.ProjClosedG` for exactly the reason the `lift'`
  family does — `padMinor`/`realMinor` splice the constructor's field *and induction
  hypothesis* telescope in with `instAll`, and an entry not closed at the spine arity keeps
  a variable that the substitution reaches on one side of the equation and not the other;
* the `instL` family carries **no closedness hypothesis at all**, because `instL` does not
  move de Bruijn indices.  `Structure.lean`'s header records the same asymmetry for the
  narrow term.  What has to be checked instead is that the level data stored inside
  `projCoreG` — `D.projLvls`, the `us` in `.const T.name us`, and the `instL us` applied to
  each stored field type — is moved consistently; `projLvls_inst` is that step.
-/

namespace Lean4Lean

open VExpr

/-! ## A weakening whose cut is at the bottom, crossed by a substitution

`(x.liftN n).inst e₀ (k + n) = (x.inst e₀ k).liftN n`.  This is `VExpr.liftN_instN_lo` at
`k := 0`, packaged in the orientation every `instN` proof below rewrites with; the three
copies of the same `List.map_congr_left fun x _ => by rw [Nat.add_comm k n]; …` block in
`Structure.lean:412/434/454` are this lemma. -/
theorem VExpr.inst_liftN_add {n k : Nat} (x e₀ : VExpr) :
    (x.liftN n).inst e₀ (k + n) = (x.inst e₀ k).liftN n := by
  rw [Nat.add_comm k n]; exact (VExpr.liftN_instN_lo n x e₀ k 0 (Nat.zero_le _)).symm

theorem VExpr.map_inst_liftN_add {n k : Nat} (e₀ : VExpr) (l : List VExpr) :
    l.map (fun x => (x.liftN n).inst e₀ (k + n)) = l.map (fun x => (x.inst e₀ k).liftN n) :=
  List.map_congr_left fun x _ => VExpr.inst_liftN_add x e₀

namespace VInductDecl'

/-! ## The two minor shapes, under a substitution -/

/-- **The padding minor commutes with a substitution.**  Same `ClosedTele` premise as
`padMinor_lift'`: it is what stops an entry of the minor's declared telescope — a field
type, or the `ξ`/`π` of a recursive field — from reaching past `spine` into the region the
substitution renumbers. -/
theorem padMinor_instN (D : VInductDecl') (lvls : List VLevel)
    {spine : List VExpr} {X e₀ : VExpr} {q k : Nat} {C' : VIndCtor}
    (hcl : VExpr.ClosedTele ((D.minorBinders q C').map (VExpr.instL lvls)) spine.length) :
    (D.padMinor lvls spine X q C').inst e₀ k
      = D.padMinor lvls (spine.map (·.inst e₀ k)) (X.inst e₀ k) q C' := by
  simp only [VInductDecl'.padMinor]
  rw [VExpr.inst_mkLams, VExpr.inst_instAllTele₀ hcl]
  simp only [VExpr.length_instAllTele, VExpr.inst, VExpr.instVar]
  rw [if_pos (show 0 < k + ((D.minorBinders q C').map (VExpr.instL lvls)).length + 1 from
    by omega), VExpr.inst_liftN_add]

/-- **The real minor commutes with a substitution.**  Same premise; the body is a bound
variable inside the telescope, so the substitution's cut sits strictly above it. -/
theorem realMinor_instN (D : VInductDecl') (lvls : List VLevel)
    {spine : List VExpr} {e₀ : VExpr} {i q k : Nat} {C' : VIndCtor}
    (hi : i < C'.fields.length)
    (hcl : VExpr.ClosedTele ((D.minorBinders q C').map (VExpr.instL lvls)) spine.length) :
    (D.realMinor lvls spine i q C').inst e₀ k
      = D.realMinor lvls (spine.map (·.inst e₀ k)) i q C' := by
  have hlen : ((D.minorBinders q C').map (VExpr.instL lvls)).length
      = C'.fields.length + (D.ihTypes q C').length := by
    rw [List.length_map, D.length_minorBinders]
  simp only [VInductDecl'.realMinor]
  rw [VExpr.inst_mkLams, VExpr.inst_instAllTele₀ hcl]
  simp only [VExpr.length_instAllTele, VExpr.inst, VExpr.instVar]
  rw [if_pos (show ((D.minorBinders q C').map (VExpr.instL lvls)).length - 1 - i
    < k + ((D.minorBinders q C').map (VExpr.instL lvls)).length from by omega)]

/-! ## The two motive shapes, under a substitution -/

/-- **The padding motive commutes with a substitution.**  The `liftN` version is
`padMotive_liftN` and the `Lift` version `padMotive_lift'`; this is the third. -/
theorem padMotive_instN (D : VInductDecl') (T' : VIndType) (us : List VLevel)
    {ps : List VExpr} {X e₀ : VExpr} {k : Nat}
    (hcl : VExpr.ClosedTele (T'.indices.map (VExpr.instL us)) ps.length) :
    (D.padMotive T' us ps X).inst e₀ k
      = D.padMotive T' us (ps.map (·.inst e₀ k)) (X.inst e₀ k) := by
  have hbv : (bvars 0 T'.indices.length).map (·.inst e₀ (k + T'.indices.length))
      = bvars 0 T'.indices.length := VExpr.inst_bvars (by omega)
  simp only [VInductDecl'.padMotive]
  rw [VExpr.inst_mkLams, VExpr.inst_instAllTele₀ hcl]
  simp only [VExpr.length_instAllTele, List.length_map, VExpr.inst, VExpr.inst_mkApp,
    List.map_append, hbv]
  refine congrArg _ ?_
  congr 1
  · exact congrArg _ (by
      simp only [List.map_map, Function.comp_def, VExpr.inst_liftN_add])
  · congr 1
    · rw [show k + T'.indices.length + 1 = k + (T'.indices.length + 1) from by omega,
        VExpr.inst_liftN_add]
    · rw [show k + T'.indices.length + 1 + 1 = k + (T'.indices.length + 2) from by omega,
        VExpr.inst_liftN_add]

end VInductDecl'

/-- **The real motive commutes with a substitution.**  The fragment of
`VInductDecl'.projCore_instN` (`Theory/Inductive/Structure.lean`) that concerns the motive,
split out so `projCoreG_instN` can use it at the projected index.  Note the `earlier`
telescope moves at cut `k + |is| + 1`: it sits under the index binders and the major
premise's binder. -/
theorem VIndType.projMotive_instN (T : VIndType) (C : VIndCtor) (us : List VLevel)
    {ps is earlier : List VExpr} {e₀ : VExpr} {i k : Nat}
    (hidx : VExpr.ClosedTele (T.indices.map (VExpr.instL us)) ps.length)
    (hftype : ((C.fields.getD i default).type.instL us).ClosedN
      ((ps.map (·.liftN (is.length+1)) ++ earlier).length))
    (his : is.length = T.indices.length) :
    (T.projMotive C us ps is i earlier).inst e₀ k
      = T.projMotive C us (ps.map (·.inst e₀ k)) (is.map (·.inst e₀ k)) i
          (earlier.map (·.inst e₀ (k + is.length + 1))) := by
  have e3 : (VExpr.instAll ((C.fields.getD i default).type.instL us)
        (ps.map (·.liftN (is.length+1)) ++ earlier)).inst e₀ (k + is.length + 1)
      = VExpr.instAll ((C.fields.getD i default).type.instL us)
        ((ps.map (·.liftN (is.length+1)) ++ earlier).map (·.inst e₀ (k + is.length + 1))) :=
    VExpr.inst_instAll (m := k + is.length + 1) (j := 0) (by simpa using hftype)
  have e4 : (bvars 0 is.length).map (·.inst e₀ (k + is.length)) = bvars 0 is.length :=
    VExpr.inst_bvars (by omega)
  simp only [VIndType.projMotive]
  rw [VExpr.inst_mkLams, VExpr.length_instAllTele, List.length_map, ← his,
    VExpr.inst_instAllTele₀ hidx]
  simp only [VExpr.inst, VExpr.inst_mkApp, List.map_append, e4, List.length_map]
  rw [e3, show k + is.length + 1 = k + (is.length + 1) from by omega]
  simp only [List.map_append, List.map_map, Function.comp_def, VExpr.inst_liftN_add]

namespace VInductDecl'

/-! ## The motive block -/

/-- **The motive block commutes with a substitution**: the real motive by
`projMotive_instN`, every padding motive by `padMotive_instN`. -/
theorem padMotives_instN (D : VInductDecl') (T : VIndType) (C : VIndCtor) (us : List VLevel)
    (H : D.ProjClosedG) {ps is earlier : List VExpr} {e e₀ : VExpr} {i j k : Nat}
    (hTj : D.types[j]? = some T) (hC : C ∈ T.ctors)
    (hps : ps.length = D.np) (his : is.length = T.indices.length)
    (hearlier : earlier.length = i) (hi : i < C.fields.length) :
    (D.padMotives T C us ps is i j earlier e).map (·.inst e₀ k)
      = D.padMotives T C us (ps.map (·.inst e₀ k)) (is.map (·.inst e₀ k)) i j
          (earlier.map (·.inst e₀ (k + is.length + 1))) (e.inst e₀ k) := by
  have hmot := T.projMotive_instN C us (ps := ps) (is := is) (earlier := earlier) (i := i)
    (e₀ := e₀) (k := k) (by rw [hps]; exact VExpr.ClosedTele.map_instL (H.indices j T hTj))
    (H.hftype hTj hC hps hearlier hi) his
  simp only [VInductDecl'.padMotives, List.map_map, Function.comp_def]
  refine List.map_congr_left fun m hm => ?_
  have hmlt : m < D.nm := List.mem_range.1 hm
  by_cases hmj : m = j
  · rw [if_pos hmj, if_pos hmj, hmot]
  · rw [if_neg hmj, if_neg hmj,
      D.padMotive_instN (D.types.getD m default) us (H.hidx hmlt hps),
      VExpr.inst_mkApp, hmot]
    simp

/-! ## The minor block -/

/-- **The minor block commutes with a substitution**, entry by entry.  As in the `lift'`
version, `acc.length = q` is what ties the accumulator to the minor index, so that
`closedTele_minorBinders`' bound `D.np + D.nm + q` is the spine's actual length. -/
theorem padMinorsAux_instN (D : VInductDecl') (lvls : List VLevel) (H : D.ProjClosedG)
    {ps mots : List VExpr} {X e₀ : VExpr} {i j k : Nat}
    (hps : ps.length = D.np) (hmots : mots.length = D.nm) :
    ∀ (l : List (Nat × VIndCtor)) (q : Nat) (acc : List VExpr), acc.length = q →
      (∀ tC ∈ l, ∃ T', D.types[tC.1]? = some T' ∧ tC.2 ∈ T'.ctors) →
      (∀ tC ∈ l, tC.1 = j → i < tC.2.fields.length) →
      (D.padMinorsAux lvls ps mots X i j l q acc).map (·.inst e₀ k)
        = D.padMinorsAux lvls (ps.map (·.inst e₀ k)) (mots.map (·.inst e₀ k)) (X.inst e₀ k)
            i j l q (acc.map (·.inst e₀ k))
  | [], _, _, _, _, _ => rfl
  | (t, C') :: rest, q, acc, hacc, hmem, hfld => by
    obtain ⟨T', hT', hC'⟩ := hmem (t, C') List.mem_cons_self
    have hlen : (ps ++ mots ++ acc).length = D.np + D.nm + q := by
      rw [List.length_append, List.length_append, hps, hmots, hacc]
    have hcl : VExpr.ClosedTele ((D.minorBinders q C').map (VExpr.instL lvls))
        (ps ++ mots ++ acc).length := by
      rw [hlen]; exact D.closedTele_minorBinders H hT' hC' q lvls
    have hmap : ((ps ++ mots ++ acc).map (·.inst e₀ k))
        = ps.map (·.inst e₀ k) ++ mots.map (·.inst e₀ k) ++ acc.map (·.inst e₀ k) := by simp
    have hm : (if t = j then D.realMinor lvls (ps ++ mots ++ acc) i q C'
          else D.padMinor lvls (ps ++ mots ++ acc) X q C').inst e₀ k
        = if t = j then D.realMinor lvls
              (ps.map (·.inst e₀ k) ++ mots.map (·.inst e₀ k) ++ acc.map (·.inst e₀ k)) i q C'
          else D.padMinor lvls
              (ps.map (·.inst e₀ k) ++ mots.map (·.inst e₀ k) ++ acc.map (·.inst e₀ k))
              (X.inst e₀ k) q C' := by
      by_cases htj : t = j
      · rw [if_pos htj, if_pos htj,
          D.realMinor_instN lvls (hfld (t, C') List.mem_cons_self htj) hcl, hmap]
      · rw [if_neg htj, if_neg htj, D.padMinor_instN lvls hcl, hmap]
    rw [VInductDecl'.padMinorsAux, VInductDecl'.padMinorsAux,
      padMinorsAux_instN D lvls H hps hmots rest (q+1) (acc ++ [_]) (by simp [hacc])
        (fun tC h => hmem tC (List.mem_cons_of_mem _ h))
        (fun tC h => hfld tC (List.mem_cons_of_mem _ h))]
    simp only [List.map_append, List.map_cons, List.map_nil, hm]

theorem padMinors_instN (D : VInductDecl') (lvls : List VLevel) (H : D.ProjClosedG)
    {ps mots : List VExpr} {X e₀ : VExpr} {i j k : Nat}
    (hps : ps.length = D.np) (hmots : mots.length = D.nm)
    (hfld : ∀ tC ∈ D.ctorsAll, tC.1 = j → i < tC.2.fields.length) :
    (D.padMinors lvls ps mots X i j).map (·.inst e₀ k)
      = D.padMinors lvls (ps.map (·.inst e₀ k)) (mots.map (·.inst e₀ k)) (X.inst e₀ k) i j := by
  rw [VInductDecl'.padMinors, VInductDecl'.padMinors,
    D.padMinorsAux_instN lvls H hps hmots D.ctorsAll 0 [] rfl
      (fun tC h => VInductDecl'.mem_ctorsAll h) hfld]
  rfl

/-! ## The generalised projection core, under a substitution -/

/-- **`projCoreG` commutes with a substitution.**  The generalisation of
`VInductDecl'.projCore_instN` (`Theory/Inductive/Structure.lean`) to a padded motive and
minor block. -/
theorem projCoreG_instN (D : VInductDecl') (T : VIndType) (C : VIndCtor) (us : List VLevel)
    (H : D.ProjClosedG) {ps is earlier : List VExpr} {e e₀ : VExpr} {i j k : Nat}
    (hTj : D.types[j]? = some T) (hctors : T.ctors = [C])
    (hps : ps.length = D.np) (his : is.length = T.indices.length)
    (hearlier : earlier.length = i) (hi : i < C.fields.length) :
    (D.projCoreG T C us ps is i j earlier e).inst e₀ k
      = D.projCoreG T C us (ps.map (·.inst e₀ k)) (is.map (·.inst e₀ k)) i j
          (earlier.map (·.inst e₀ (k + is.length + 1))) (e.inst e₀ k) := by
  have hC : C ∈ T.ctors := by rw [hctors]; exact List.mem_singleton_self _
  have hmot := T.projMotive_instN C us (ps := ps) (is := is) (earlier := earlier) (i := i)
    (e₀ := e₀) (k := k) (by rw [hps]; exact VExpr.ClosedTele.map_instL (H.indices j T hTj))
    (H.hftype hTj hC hps hearlier hi) his
  have hmots := D.padMotives_instN T C us H (ps := ps) (is := is) (earlier := earlier)
    (e := e) (e₀ := e₀) (i := i) (j := j) (k := k) hTj hC hps his hearlier hi
  have hX : ((T.projMotive C us ps is i earlier).mkApp (is ++ [e])).inst e₀ k
      = (T.projMotive C us (ps.map (·.inst e₀ k)) (is.map (·.inst e₀ k)) i
          (earlier.map (·.inst e₀ (k + is.length + 1)))).mkApp
          (is.map (·.inst e₀ k) ++ [e.inst e₀ k]) := by
    rw [VExpr.inst_mkApp, hmot]; simp
  rw [VInductDecl'.projCoreG, VInductDecl'.projCoreG, VExpr.inst_mkApp]
  simp only [List.map_append, List.map_cons, List.map_nil, VExpr.inst]
  rw [D.padMinors_instN (D.projLvls C us i) H hps
      (D.length_padMotives T C us ps is i j earlier e)
      (projected_fields_lt hTj hctors hi),
    hmots, hX]

theorem projArgsG_instN (D : VInductDecl') (T : VIndType) (C : VIndCtor) (us : List VLevel)
    (H : D.ProjClosedG) {j : Nat} (hTj : D.types[j]? = some T) (hctors : T.ctors = [C]) :
    ∀ {i : Nat} {ps is : List VExpr} {e₀ : VExpr} {k : Nat},
    ps.length = D.np → is.length = T.indices.length → i ≤ C.fields.length → 1 ≤ k →
    (D.projArgsG T C us ps is j i).map (·.inst e₀ k)
      = D.projArgsG T C us (ps.map (·.inst e₀ k)) (is.map (·.inst e₀ k)) j i
  | 0, _, _, _, _, _, _, _, _ => rfl
  | i+1, ps, is, e₀, k, hps, his, hi, hk => by
    have hinner := projArgsG_instN D T C us H hTj hctors (i := i)
      (ps := ps.map (·.liftN (is.length+1))) (is := bvars 1 is.length)
      (e₀ := e₀) (k := k + is.length + 1)
      (by simpa using hps) (by simpa using his) (by omega) (by omega)
    have hbv : (bvars 1 is.length).map (·.inst e₀ (k + is.length + 1)) = bvars 1 is.length :=
      VExpr.inst_bvars (by omega)
    have e5 : ∀ (l : List VExpr),
        l.map (fun x => (x.liftN (is.length+1)).inst e₀ (k + is.length + 1))
          = l.map (fun x => (x.inst e₀ k).liftN (is.length+1)) := fun l => by
      rw [show k + is.length + 1 = k + (is.length + 1) from by omega]
      exact VExpr.map_inst_liftN_add e₀ l
    simp only [VInductDecl'.projArgsG, List.map_append, List.map_cons, List.map_nil]
    rw [projArgsG_instN D T C us H hTj hctors hps his (by omega) hk,
      D.projCoreG_instN T C us H hTj hctors hps his (D.length_projArgsG T C us j) (by omega),
      hinner, hbv]
    simp only [VExpr.inst, VExpr.instVar, if_pos (show 0 < k from by omega),
      List.map_map, Function.comp_def, e5, List.length_map]

theorem projTermG_instN (D : VInductDecl') (T : VIndType) (C : VIndCtor) (us : List VLevel)
    (H : D.ProjClosedG) {ps is : List VExpr} {e e₀ : VExpr} {i j k : Nat}
    (hTj : D.types[j]? = some T) (hctors : T.ctors = [C])
    (hps : ps.length = D.np) (his : is.length = T.indices.length)
    (hi : i < C.fields.length) :
    (D.projTermG T C us ps is i j e).inst e₀ k
      = D.projTermG T C us (ps.map (·.inst e₀ k)) (is.map (·.inst e₀ k)) i j (e.inst e₀ k) := by
  have hbv : (bvars 1 is.length).map (·.inst e₀ (k + is.length + 1)) = bvars 1 is.length :=
    VExpr.inst_bvars (by omega)
  have e5 : ∀ (l : List VExpr),
      l.map (fun x => (x.liftN (is.length+1)).inst e₀ (k + is.length + 1))
        = l.map (fun x => (x.inst e₀ k).liftN (is.length+1)) := fun l => by
    rw [show k + is.length + 1 = k + (is.length + 1) from by omega]
    exact VExpr.map_inst_liftN_add e₀ l
  simp only [VInductDecl'.projTermG]
  rw [D.projCoreG_instN T C us H hTj hctors hps his (D.length_projArgsG T C us j) hi,
    D.projArgsG_instN T C us H hTj hctors (i := i)
      (ps := ps.map (·.liftN (is.length+1))) (is := bvars 1 is.length)
      (e₀ := e₀) (k := k + is.length + 1)
      (by simpa using hps) (by simpa using his) (by omega) (by omega),
    hbv]
  simp only [List.map_map, Function.comp_def, e5, List.length_map]

/-! ## Commutation with universe instantiation

No closedness hypothesis: `instL` rewrites level data and leaves every de Bruijn index
alone.  The one thing that has to be checked is that the stored levels move consistently —
`projLvls_inst` below — which is the generalised analogue of the `split <;> simp
[VLevel.inst_inst]` at the end of `projCore_instL`. -/

/-- The recursor's level arguments commute with a level substitution. -/
theorem projLvls_inst (D : VInductDecl') (C : VIndCtor) (us ls : List VLevel) (i : Nat) :
    (D.projLvls C us i).map (VLevel.inst ls) = D.projLvls C (us.map (VLevel.inst ls)) i := by
  simp only [VInductDecl'.projLvls]
  split <;> simp [VLevel.inst_inst]

theorem padMinor_instL (D : VInductDecl') (lvls ls : List VLevel)
    (spine : List VExpr) (X : VExpr) (q : Nat) (C' : VIndCtor) :
    (D.padMinor lvls spine X q C').instL ls
      = D.padMinor (lvls.map (VLevel.inst ls)) (spine.map (VExpr.instL ls)) (X.instL ls)
          q C' := by
  simp [VInductDecl'.padMinor, VExpr.instL, VExpr.instL_instAllTele, List.map_map,
    Function.comp_def, VExpr.instL_instL]

theorem realMinor_instL (D : VInductDecl') (lvls ls : List VLevel)
    (spine : List VExpr) (i q : Nat) (C' : VIndCtor) :
    (D.realMinor lvls spine i q C').instL ls
      = D.realMinor (lvls.map (VLevel.inst ls)) (spine.map (VExpr.instL ls)) i q C' := by
  simp [VInductDecl'.realMinor, VExpr.instL, VExpr.instL_instAllTele, List.map_map,
    Function.comp_def, VExpr.instL_instL]

theorem padMotive_instL (D : VInductDecl') (T' : VIndType) (us ls : List VLevel)
    (ps : List VExpr) (X : VExpr) :
    (D.padMotive T' us ps X).instL ls
      = D.padMotive T' (us.map (VLevel.inst ls)) (ps.map (VExpr.instL ls)) (X.instL ls) := by
  simp [VInductDecl'.padMotive, VExpr.instL, VExpr.instL_instAllTele, List.map_map,
    Function.comp_def, VExpr.instL_instL]

end VInductDecl'

theorem VIndType.projMotive_instL (T : VIndType) (C : VIndCtor) (us ls : List VLevel)
    (ps is : List VExpr) (i : Nat) (earlier : List VExpr) :
    (T.projMotive C us ps is i earlier).instL ls
      = T.projMotive C (us.map (VLevel.inst ls)) (ps.map (VExpr.instL ls))
          (is.map (VExpr.instL ls)) i (earlier.map (VExpr.instL ls)) := by
  simp [VIndType.projMotive, VExpr.instL, VExpr.instL_instAllTele, VExpr.instL_instAll,
    List.map_map, Function.comp_def, VExpr.instL_instL]

namespace VInductDecl'

theorem padMotives_instL (D : VInductDecl') (T : VIndType) (C : VIndCtor) (us ls : List VLevel)
    (ps is : List VExpr) (i j : Nat) (earlier : List VExpr) (e : VExpr) :
    (D.padMotives T C us ps is i j earlier e).map (VExpr.instL ls)
      = D.padMotives T C (us.map (VLevel.inst ls)) (ps.map (VExpr.instL ls))
          (is.map (VExpr.instL ls)) i j (earlier.map (VExpr.instL ls)) (e.instL ls) := by
  simp only [VInductDecl'.padMotives, List.map_map, Function.comp_def]
  refine List.map_congr_left fun m _ => ?_
  by_cases hmj : m = j
  · rw [if_pos hmj, if_pos hmj, T.projMotive_instL]
  · rw [if_neg hmj, if_neg hmj, D.padMotive_instL, VExpr.instL_mkApp, T.projMotive_instL]
    simp

theorem padMinorsAux_instL (D : VInductDecl') (lvls ls : List VLevel)
    (ps mots : List VExpr) (X : VExpr) (i j : Nat) :
    ∀ (l : List (Nat × VIndCtor)) (q : Nat) (acc : List VExpr),
      (D.padMinorsAux lvls ps mots X i j l q acc).map (VExpr.instL ls)
        = D.padMinorsAux (lvls.map (VLevel.inst ls)) (ps.map (VExpr.instL ls))
            (mots.map (VExpr.instL ls)) (X.instL ls) i j l q (acc.map (VExpr.instL ls))
  | [], _, _ => rfl
  | (t, C') :: rest, q, acc => by
    have hmap : ((ps ++ mots ++ acc).map (VExpr.instL ls))
        = ps.map (VExpr.instL ls) ++ mots.map (VExpr.instL ls) ++ acc.map (VExpr.instL ls) := by
      simp
    have hm : (if t = j then D.realMinor lvls (ps ++ mots ++ acc) i q C'
          else D.padMinor lvls (ps ++ mots ++ acc) X q C').instL ls
        = if t = j then D.realMinor (lvls.map (VLevel.inst ls))
              (ps.map (VExpr.instL ls) ++ mots.map (VExpr.instL ls) ++ acc.map (VExpr.instL ls))
              i q C'
          else D.padMinor (lvls.map (VLevel.inst ls))
              (ps.map (VExpr.instL ls) ++ mots.map (VExpr.instL ls) ++ acc.map (VExpr.instL ls))
              (X.instL ls) q C' := by
      by_cases htj : t = j
      · rw [if_pos htj, if_pos htj, D.realMinor_instL, hmap]
      · rw [if_neg htj, if_neg htj, D.padMinor_instL, hmap]
    rw [VInductDecl'.padMinorsAux, VInductDecl'.padMinorsAux,
      padMinorsAux_instL D lvls ls ps mots X i j rest (q+1) (acc ++ [_])]
    simp only [List.map_append, List.map_cons, List.map_nil, hm]

theorem padMinors_instL (D : VInductDecl') (lvls ls : List VLevel)
    (ps mots : List VExpr) (X : VExpr) (i j : Nat) :
    (D.padMinors lvls ps mots X i j).map (VExpr.instL ls)
      = D.padMinors (lvls.map (VLevel.inst ls)) (ps.map (VExpr.instL ls))
          (mots.map (VExpr.instL ls)) (X.instL ls) i j := by
  rw [VInductDecl'.padMinors, VInductDecl'.padMinors,
    D.padMinorsAux_instL lvls ls ps mots X i j D.ctorsAll 0 []]
  rfl

/-- **`projCoreG` commutes with a universe instantiation**, with no side condition — the
generalisation of `VInductDecl'.projCore_instL`.  As there, this is the equation that would
be **false** without the `instL us` inside `projMotive`: the stored field type would keep a
universe parameter of the block, which `instL ls` would rewrite on the left while
`us.map (·.inst ls)` on the right would not reach it. -/
theorem projCoreG_instL (D : VInductDecl') (T : VIndType) (C : VIndCtor) (us ls : List VLevel)
    (ps is : List VExpr) (i j : Nat) (earlier : List VExpr) (e : VExpr) :
    (D.projCoreG T C us ps is i j earlier e).instL ls
      = D.projCoreG T C (us.map (VLevel.inst ls)) (ps.map (VExpr.instL ls))
          (is.map (VExpr.instL ls)) i j (earlier.map (VExpr.instL ls)) (e.instL ls) := by
  rw [VInductDecl'.projCoreG, VInductDecl'.projCoreG, VExpr.instL_mkApp]
  simp only [List.map_append, List.map_cons, List.map_nil, VExpr.instL]
  rw [D.padMinors_instL _ ls, D.padMotives_instL T C us ls, D.projLvls_inst C us ls i,
    VExpr.instL_mkApp, T.projMotive_instL]
  simp

theorem projArgsG_instL (D : VInductDecl') (T : VIndType) (C : VIndCtor) (us ls : List VLevel)
    (j : Nat) : ∀ (i : Nat) (ps is : List VExpr),
    (D.projArgsG T C us ps is j i).map (VExpr.instL ls)
      = D.projArgsG T C (us.map (VLevel.inst ls)) (ps.map (VExpr.instL ls))
          (is.map (VExpr.instL ls)) j i
  | 0, _, _ => rfl
  | i+1, ps, is => by
    simp only [VInductDecl'.projArgsG, List.map_append, List.map_cons, List.map_nil]
    rw [projArgsG_instL D T C us ls j i ps is, D.projCoreG_instL T C us ls,
      projArgsG_instL D T C us ls j i (ps.map (·.liftN (is.length+1))) (bvars 1 is.length)]
    simp [VExpr.instL, List.map_map, Function.comp_def]

theorem projTermG_instL (D : VInductDecl') (T : VIndType) (C : VIndCtor) (us ls : List VLevel)
    (ps is : List VExpr) (i j : Nat) (e : VExpr) :
    (D.projTermG T C us ps is i j e).instL ls
      = D.projTermG T C (us.map (VLevel.inst ls)) (ps.map (VExpr.instL ls))
          (is.map (VExpr.instL ls)) i j (e.instL ls) := by
  simp only [VInductDecl'.projTermG]
  rw [D.projCoreG_instL T C us ls, D.projArgsG_instL T C us ls j i]
  simp [List.map_map, Function.comp_def]

end VInductDecl'

end Lean4Lean
