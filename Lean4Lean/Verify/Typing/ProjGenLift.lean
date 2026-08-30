import Lean4Lean.Verify.Typing.ProjClosedG

/-!
# Block A for `projCoreG`: commutation with `lift'`

`Theory/Inductive/Structure.lean:296–450` proves `projCore_lift'`, `projArgs_lift'`,
`projTerm_lift'` and their `instN` counterparts; these are what `TrProj.mono`, `TrProj.instL`
and `TrProj.weak'` run on.  This file is the same development for the **generalised** term
`projCoreG` (`ProjGen.lean`), whose motive and minor blocks are full length.

The hypothesis is `VInductDecl'.ProjClosedG` (`ProjClosedG.lean`) rather than `ProjClosed`:
each padding minor binds a constructor's *induction hypotheses* as well as its fields, and
`VExpr.lift'_instAllTele` needs that whole telescope closed at the spine arity.  Three fields
do not give it — `ProjClosedGap.projClosedG_needs_recArgs` (`ProjGenWitness.lean`) is the
counterexample, and `ProjClosedGap.badCtor_not_projClosedG` (`ProjClosedGWitness.lean`) is
that counterexample re-run against this file's hypothesis.
-/

namespace Lean4Lean

open VExpr

namespace VInductDecl'

/-! ## The two minor shapes -/

/-- **The padding minor commutes with a lift.**  Its only free variables come from `spine`
and `X`; the `ClosedTele` premise is what stops an entry of the minor's declared telescope —
a field type, or the `ξ`/`π` of a recursive field — from reaching past them. -/
theorem padMinor_lift' (D : VInductDecl') (lvls : List VLevel)
    {spine : List VExpr} {X : VExpr} {q : Nat} {C' : VIndCtor} {ρ : Lift}
    (hcl : VExpr.ClosedTele ((D.minorBinders q C').map (VExpr.instL lvls)) spine.length) :
    (D.padMinor lvls spine X q C').lift' ρ
      = D.padMinor lvls (spine.map (·.lift' ρ)) (X.lift' ρ) q C' := by
  simp only [VInductDecl'.padMinor]
  rw [VExpr.lift'_mkLams, VExpr.lift'_instAllTele₀ hcl]
  simp only [VExpr.length_instAllTele, VExpr.lift']
  rw [VExpr.liftN_lift',
    show (ρ.consN ((D.minorBinders q C').map (VExpr.instL lvls)).length).cons
      = ρ.consN (((D.minorBinders q C').map (VExpr.instL lvls)).length + 1) from rfl,
    Lift.consN_fixes.liftVar_eq (Nat.succ_pos _)]

/-- **The real minor commutes with a lift.**  Same premise; the body is a bound variable
inside the telescope, which the lift fixes. -/
theorem realMinor_lift' (D : VInductDecl') (lvls : List VLevel)
    {spine : List VExpr} {i q : Nat} {C' : VIndCtor} {ρ : Lift}
    (hi : i < C'.fields.length)
    (hcl : VExpr.ClosedTele ((D.minorBinders q C').map (VExpr.instL lvls)) spine.length) :
    (D.realMinor lvls spine i q C').lift' ρ
      = D.realMinor lvls (spine.map (·.lift' ρ)) i q C' := by
  have hlen : ((D.minorBinders q C').map (VExpr.instL lvls)).length
      = C'.fields.length + (D.ihTypes q C').length := by
    rw [List.length_map, D.length_minorBinders]
  simp only [VInductDecl'.realMinor]
  rw [VExpr.lift'_mkLams, VExpr.lift'_instAllTele₀ hcl]
  simp only [VExpr.length_instAllTele, VExpr.lift']
  rw [Lift.consN_fixes.liftVar_eq (k := ((D.minorBinders q C').map (VExpr.instL lvls)).length)
    (by omega)]

/-! ## The two motive shapes -/

/-- **The padding motive commutes with a lift.**  The `liftN` version is
`VInductDecl'.padMotive_liftN` (`ProjGen.lean`); this is the `Lift` version, which is what
`projCoreG_lift'` needs. -/
theorem padMotive_lift' (D : VInductDecl') (T' : VIndType) (us : List VLevel)
    {ps : List VExpr} {X : VExpr} {ρ : Lift}
    (hcl : VExpr.ClosedTele (T'.indices.map (VExpr.instL us)) ps.length) :
    (D.padMotive T' us ps X).lift' ρ
      = D.padMotive T' us (ps.map (·.lift' ρ)) (X.lift' ρ) := by
  have hbv : (bvars 0 T'.indices.length).map (·.lift' (ρ.consN T'.indices.length))
      = bvars 0 T'.indices.length :=
    VExpr.lift'_bvars (lo := 0) (n := T'.indices.length) (by simpa using Lift.consN_fixes)
  simp only [VInductDecl'.padMotive]
  rw [VExpr.lift'_mkLams, VExpr.lift'_instAllTele₀ hcl]
  simp only [VExpr.length_instAllTele, List.length_map, VExpr.lift', VExpr.lift'_mkApp,
    List.map_append, hbv]
  refine congrArg _ ?_
  congr 1
  · exact congrArg _ (by simp only [List.map_map, Function.comp_def, VExpr.liftN_lift'])
  · rw [show (ρ.consN T'.indices.length).cons = ρ.consN (T'.indices.length + 1) from rfl,
      show (ρ.consN (T'.indices.length + 1)).cons = ρ.consN (T'.indices.length + 2) from rfl,
      VExpr.liftN_lift', VExpr.liftN_lift']

end VInductDecl'

/-- **The real motive commutes with a lift.**  This is the fragment of
`VInductDecl'.projCore_lift'` (`Theory/Inductive/Structure.lean`) that concerns the motive,
split out so `projCoreG_lift'` can use it at the projected index. -/
theorem VIndType.projMotive_lift' (T : VIndType) (C : VIndCtor) (us : List VLevel)
    {ps is earlier : List VExpr} {i : Nat} {ρ : Lift}
    (hidx : VExpr.ClosedTele (T.indices.map (VExpr.instL us)) ps.length)
    (hftype : ((C.fields.getD i default).type.instL us).ClosedN
      ((ps.map (·.liftN (is.length+1)) ++ earlier).length))
    (his : is.length = T.indices.length) :
    (T.projMotive C us ps is i earlier).lift' ρ
      = T.projMotive C us (ps.map (·.lift' ρ)) (is.map (·.lift' ρ)) i
          (earlier.map (·.lift' (ρ.consN (is.length+1)))) := by
  have e3 : (VExpr.instAll ((C.fields.getD i default).type.instL us)
        (ps.map (·.liftN (is.length+1)) ++ earlier)).lift' (ρ.consN is.length).cons
      = VExpr.instAll ((C.fields.getD i default).type.instL us)
        ((ps.map (·.liftN (is.length+1)) ++ earlier).map (·.lift' (ρ.consN (is.length+1)))) :=
    VExpr.lift'_instAll (ρ := ρ.consN (is.length+1)) (k := 0) (by simpa using hftype)
  have e4 : (bvars 0 is.length).map (·.lift' (ρ.consN is.length)) = bvars 0 is.length :=
    VExpr.lift'_bvars (lo := 0) (n := is.length) (ρ := ρ.consN is.length)
      (by simpa using Lift.consN_fixes)
  simp only [VIndType.projMotive]
  rw [VExpr.lift'_mkLams, VExpr.length_instAllTele, List.length_map, ← his,
    VExpr.lift'_instAllTele₀ hidx]
  simp only [VExpr.lift', VExpr.lift'_mkApp, List.map_append, e4, List.length_map]
  rw [e3]
  simp only [List.map_append, List.map_map, Function.comp_def, VExpr.liftN_lift']

namespace VInductDecl'

/-! ## The motive block -/

/-- The projected field's type is closed at `np + i`, in the form `projMotive_lift'` wants. -/
theorem ProjClosedG.hftype {D : VInductDecl'} (H : D.ProjClosedG) {j : Nat} {T : VIndType}
    (hTj : D.types[j]? = some T) {C : VIndCtor} (hC : C ∈ T.ctors) {us : List VLevel}
    {ps earlier : List VExpr} {i n : Nat} (hps : ps.length = D.np) (hearlier : earlier.length = i)
    (hi : i < C.fields.length) :
    ((C.fields.getD i default).type.instL us).ClosedN
      ((ps.map (·.liftN n) ++ earlier).length) := by
  have hget : (C.fields.map (·.type))[i]? = some (C.fields.getD i default).type := by
    rw [List.getElem?_map, List.getElem?_eq_getElem hi]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  have := (VExpr.ClosedTele.getElem? (H.fields j T hTj C hC) hget).instL (ls := us)
  simpa [hps, hearlier] using this

/-- Every block member's index telescope is closed at the parameter spine's length. -/
theorem ProjClosedG.hidx {D : VInductDecl'} (H : D.ProjClosedG) {k : Nat} (hk : k < D.nm)
    {us : List VLevel} {ps : List VExpr} (hps : ps.length = D.np) :
    VExpr.ClosedTele (((D.types.getD k default).indices).map (VExpr.instL us)) ps.length := by
  have hTk : D.types[k]? = some (D.types.getD k default) := by
    rw [List.getElem?_eq_getElem hk]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  rw [hps]
  exact VExpr.ClosedTele.map_instL (H.indices k _ hTk)

/-- **The motive block commutes with a lift**: the real motive by `projMotive_lift'`, every
padding motive by `padMotive_lift'`. -/
theorem padMotives_lift' (D : VInductDecl') (T : VIndType) (C : VIndCtor) (us : List VLevel)
    (H : D.ProjClosedG) {ps is earlier : List VExpr} {e : VExpr} {i j : Nat} {ρ : Lift}
    (hTj : D.types[j]? = some T) (hC : C ∈ T.ctors)
    (hps : ps.length = D.np) (his : is.length = T.indices.length)
    (hearlier : earlier.length = i) (hi : i < C.fields.length) :
    (D.padMotives T C us ps is i j earlier e).map (·.lift' ρ)
      = D.padMotives T C us (ps.map (·.lift' ρ)) (is.map (·.lift' ρ)) i j
          (earlier.map (·.lift' (ρ.consN (is.length+1)))) (e.lift' ρ) := by
  have hjlt : j < D.nm := (List.getElem?_eq_some_iff.1 hTj).1
  have hmot := T.projMotive_lift' C us (ps := ps) (is := is) (earlier := earlier) (i := i)
    (ρ := ρ) (by rw [hps]; exact VExpr.ClosedTele.map_instL (H.indices j T hTj))
    (H.hftype hTj hC hps hearlier hi) his
  simp only [VInductDecl'.padMotives, List.map_map, Function.comp_def]
  refine List.map_congr_left fun k hk => ?_
  have hklt : k < D.nm := List.mem_range.1 hk
  by_cases hkj : k = j
  · rw [if_pos hkj, if_pos hkj, hmot]
  · rw [if_neg hkj, if_neg hkj,
      D.padMotive_lift' (D.types.getD k default) us (H.hidx hklt hps),
      VExpr.lift'_mkApp, hmot]
    simp

/-! ## The minor block -/

/-- **The minor block commutes with a lift**, entry by entry.  `acc.length = q` is what ties
the accumulator to the minor index, so that `closedTele_minorBinders`' bound
`D.np + D.nm + q` is the spine's actual length. -/
theorem padMinorsAux_lift' (D : VInductDecl') (lvls : List VLevel) (H : D.ProjClosedG)
    {ps mots : List VExpr} {X : VExpr} {i j : Nat} {ρ : Lift}
    (hps : ps.length = D.np) (hmots : mots.length = D.nm) :
    ∀ (l : List (Nat × VIndCtor)) (q : Nat) (acc : List VExpr), acc.length = q →
      (∀ tC ∈ l, ∃ T', D.types[tC.1]? = some T' ∧ tC.2 ∈ T'.ctors) →
      (∀ tC ∈ l, tC.1 = j → i < tC.2.fields.length) →
      (D.padMinorsAux lvls ps mots X i j l q acc).map (·.lift' ρ)
        = D.padMinorsAux lvls (ps.map (·.lift' ρ)) (mots.map (·.lift' ρ)) (X.lift' ρ) i j l q
            (acc.map (·.lift' ρ))
  | [], _, _, _, _, _ => rfl
  | (t, C') :: rest, q, acc, hacc, hmem, hfld => by
    obtain ⟨T', hT', hC'⟩ := hmem (t, C') List.mem_cons_self
    have hlen : (ps ++ mots ++ acc).length = D.np + D.nm + q := by
      rw [List.length_append, List.length_append, hps, hmots, hacc]
    have hcl : VExpr.ClosedTele ((D.minorBinders q C').map (VExpr.instL lvls))
        (ps ++ mots ++ acc).length := by
      rw [hlen]; exact D.closedTele_minorBinders H hT' hC' q lvls
    have hmap : ((ps ++ mots ++ acc).map (·.lift' ρ))
        = ps.map (·.lift' ρ) ++ mots.map (·.lift' ρ) ++ acc.map (·.lift' ρ) := by simp
    have hm : (if t = j then D.realMinor lvls (ps ++ mots ++ acc) i q C'
          else D.padMinor lvls (ps ++ mots ++ acc) X q C').lift' ρ
        = if t = j then D.realMinor lvls
              (ps.map (·.lift' ρ) ++ mots.map (·.lift' ρ) ++ acc.map (·.lift' ρ)) i q C'
          else D.padMinor lvls
              (ps.map (·.lift' ρ) ++ mots.map (·.lift' ρ) ++ acc.map (·.lift' ρ))
              (X.lift' ρ) q C' := by
      by_cases htj : t = j
      · rw [if_pos htj, if_pos htj,
          D.realMinor_lift' lvls (hfld (t, C') List.mem_cons_self htj) hcl, hmap]
      · rw [if_neg htj, if_neg htj, D.padMinor_lift' lvls hcl, hmap]
    rw [VInductDecl'.padMinorsAux, VInductDecl'.padMinorsAux,
      padMinorsAux_lift' D lvls H hps hmots rest (q+1) (acc ++ [_]) (by simp [hacc])
        (fun tC h => hmem tC (List.mem_cons_of_mem _ h))
        (fun tC h => hfld tC (List.mem_cons_of_mem _ h))]
    simp only [List.map_append, List.map_cons, List.map_nil, hm]

theorem padMinors_lift' (D : VInductDecl') (lvls : List VLevel) (H : D.ProjClosedG)
    {ps mots : List VExpr} {X : VExpr} {i j : Nat} {ρ : Lift}
    (hps : ps.length = D.np) (hmots : mots.length = D.nm)
    (hfld : ∀ tC ∈ D.ctorsAll, tC.1 = j → i < tC.2.fields.length) :
    (D.padMinors lvls ps mots X i j).map (·.lift' ρ)
      = D.padMinors lvls (ps.map (·.lift' ρ)) (mots.map (·.lift' ρ)) (X.lift' ρ) i j := by
  rw [VInductDecl'.padMinors, VInductDecl'.padMinors,
    D.padMinorsAux_lift' lvls H hps hmots D.ctorsAll 0 [] rfl
      (fun tC h => VInductDecl'.mem_ctorsAll h) hfld]
  rfl

/-! ## The generalised projection core -/

theorem length_projArgsG (D : VInductDecl') (T : VIndType) (C : VIndCtor) (us : List VLevel)
    (j : Nat) : ∀ {i : Nat} {ps is : List VExpr}, (D.projArgsG T C us ps is j i).length = i
  | 0, _, _ => rfl
  | i+1, ps, is => by
    rw [VInductDecl'.projArgsG, List.length_append,
      length_projArgsG D T C us j (i := i) (ps := ps) (is := is)]
    rfl

/-- At the projected index every constructor of the block is `C`, so the real minor's field
index is in range wherever `padMinorsAux` builds one. -/
theorem projected_fields_lt {D : VInductDecl'} {T : VIndType} {C : VIndCtor} {i j : Nat}
    (hTj : D.types[j]? = some T) (hctors : T.ctors = [C]) (hi : i < C.fields.length) :
    ∀ tC ∈ D.ctorsAll, tC.1 = j → i < tC.2.fields.length := by
  rintro ⟨t, C'⟩ hmem rfl
  obtain ⟨T'', hT'', hC''⟩ := VInductDecl'.mem_ctorsAll hmem
  obtain rfl : T = T'' := Option.some.inj (hTj ▸ hT'')
  rw [hctors] at hC''
  obtain rfl : C' = C := List.mem_singleton.1 hC''
  exact hi

/-- **`projCoreG` commutes with a lift.**  The generalisation of
`VInductDecl'.projCore_lift'` (`Theory/Inductive/Structure.lean`) to a padded motive and
minor block.  `ProjClosed` is replaced by `ProjClosedG` — see this file's header. -/
theorem projCoreG_lift' (D : VInductDecl') (T : VIndType) (C : VIndCtor) (us : List VLevel)
    (H : D.ProjClosedG) {ps is earlier : List VExpr} {e : VExpr} {i j : Nat} {ρ : Lift}
    (hTj : D.types[j]? = some T) (hctors : T.ctors = [C])
    (hps : ps.length = D.np) (his : is.length = T.indices.length)
    (hearlier : earlier.length = i) (hi : i < C.fields.length) :
    (D.projCoreG T C us ps is i j earlier e).lift' ρ
      = D.projCoreG T C us (ps.map (·.lift' ρ)) (is.map (·.lift' ρ)) i j
          (earlier.map (·.lift' (ρ.consN (is.length+1)))) (e.lift' ρ) := by
  have hC : C ∈ T.ctors := by rw [hctors]; exact List.mem_singleton_self _
  have hmot := T.projMotive_lift' C us (ps := ps) (is := is) (earlier := earlier) (i := i)
    (ρ := ρ) (by rw [hps]; exact VExpr.ClosedTele.map_instL (H.indices j T hTj))
    (H.hftype hTj hC hps hearlier hi) his
  have hmots := D.padMotives_lift' T C us H (ps := ps) (is := is) (earlier := earlier)
    (e := e) (i := i) (j := j) (ρ := ρ) hTj hC hps his hearlier hi
  have hX : ((T.projMotive C us ps is i earlier).mkApp (is ++ [e])).lift' ρ
      = (T.projMotive C us (ps.map (·.lift' ρ)) (is.map (·.lift' ρ)) i
          (earlier.map (·.lift' (ρ.consN (is.length+1))))).mkApp
          (is.map (·.lift' ρ) ++ [e.lift' ρ]) := by
    rw [VExpr.lift'_mkApp, hmot]; simp
  rw [VInductDecl'.projCoreG, VInductDecl'.projCoreG, VExpr.lift'_mkApp]
  simp only [List.map_append, List.map_cons, List.map_nil, VExpr.lift']
  rw [D.padMinors_lift' (D.projLvls C us i) H hps (D.length_padMotives T C us ps is i j earlier e)
      (projected_fields_lt hTj hctors hi),
    hmots, hX]

theorem projArgsG_lift' (D : VInductDecl') (T : VIndType) (C : VIndCtor) (us : List VLevel)
    (H : D.ProjClosedG) {j : Nat} (hTj : D.types[j]? = some T) (hctors : T.ctors = [C]) :
    ∀ {i : Nat} {ps is : List VExpr} {ρ : Lift},
    ps.length = D.np → is.length = T.indices.length → i ≤ C.fields.length → ρ.Fixes 1 →
    (D.projArgsG T C us ps is j i).map (·.lift' ρ)
      = D.projArgsG T C us (ps.map (·.lift' ρ)) (is.map (·.lift' ρ)) j i
  | 0, _, _, _, _, _, _, _ => rfl
  | i+1, ps, is, ρ, hps, his, hi, hρ => by
    have hinner := projArgsG_lift' D T C us H hTj hctors (i := i)
      (ps := ps.map (·.liftN (is.length+1))) (is := bvars 1 is.length)
      (ρ := ρ.consN (is.length+1)) (by simpa using hps) (by simpa using his)
      (by omega) (Lift.consN_fixes.le (by omega))
    have hbv : (bvars 1 is.length).map (·.lift' (ρ.consN (is.length+1))) = bvars 1 is.length :=
      VExpr.lift'_bvars (lo := 1) (n := is.length) (ρ := ρ.consN (is.length+1))
        (by rw [Nat.add_comm]; exact Lift.consN_fixes)
    simp only [VInductDecl'.projArgsG, List.map_append, List.map_cons, List.map_nil]
    rw [projArgsG_lift' D T C us H hTj hctors hps his (by omega) hρ,
      D.projCoreG_lift' T C us H hTj hctors hps his
        (D.length_projArgsG T C us j) (by omega),
      hinner, hbv]
    simp only [VExpr.lift', hρ.liftVar_eq (show 0 < 1 by omega),
      List.map_map, Function.comp_def, VExpr.liftN_lift', List.length_map]

theorem projTermG_lift' (D : VInductDecl') (T : VIndType) (C : VIndCtor) (us : List VLevel)
    (H : D.ProjClosedG) {ps is : List VExpr} {e : VExpr} {i j : Nat} {ρ : Lift}
    (hTj : D.types[j]? = some T) (hctors : T.ctors = [C])
    (hps : ps.length = D.np) (his : is.length = T.indices.length)
    (hi : i < C.fields.length) :
    (D.projTermG T C us ps is i j e).lift' ρ
      = D.projTermG T C us (ps.map (·.lift' ρ)) (is.map (·.lift' ρ)) i j (e.lift' ρ) := by
  have hbv : (bvars 1 is.length).map (·.lift' (ρ.consN (is.length+1))) = bvars 1 is.length :=
    VExpr.lift'_bvars (lo := 1) (n := is.length) (ρ := ρ.consN (is.length+1))
      (by rw [Nat.add_comm]; exact Lift.consN_fixes)
  simp only [VInductDecl'.projTermG]
  rw [D.projCoreG_lift' T C us H hTj hctors hps his (D.length_projArgsG T C us j) hi,
    D.projArgsG_lift' T C us H hTj hctors (i := i)
      (ps := ps.map (·.liftN (is.length+1))) (is := bvars 1 is.length)
      (ρ := ρ.consN (is.length+1)) (by simpa using hps) (by simpa using his)
      (by omega) (Lift.consN_fixes.le (by omega)),
    hbv]
  simp only [List.map_map, Function.comp_def, VExpr.liftN_lift', List.length_map]

/-! ## The `liftN` corollary the *real* minor's typing lemma needs

`docs/handoff-projections.md` §0.6 item 2 — the typing lemma for `realMinor` — needs the
analogue of `VInductDecl'.padMotive_liftN` at the **real** motive: the minor's body applies
motive `t` *weakened past the minor's own binders*, so the motive has to commute with that
weakening before `betaMkLams` can fire.  For the padding motive that is `padMotive_liftN`
(`ProjGen.lean`); for the real one it is this, and it is a corollary of `projMotive_lift'`
because `liftN n = lift' (skipN refl n)` (`VExpr.liftN_eq_lift'`). -/
theorem _root_.Lean4Lean.VIndType.projMotive_liftN (T : VIndType) (C : VIndCtor)
    (us : List VLevel) {ps is earlier : List VExpr} {i n : Nat}
    (hidx : VExpr.ClosedTele (T.indices.map (VExpr.instL us)) ps.length)
    (hftype : ((C.fields.getD i default).type.instL us).ClosedN
      ((ps.map (·.liftN (is.length+1)) ++ earlier).length))
    (his : is.length = T.indices.length) :
    (T.projMotive C us ps is i earlier).liftN n
      = T.projMotive C us (ps.map (·.liftN n)) (is.map (·.liftN n)) i
          (earlier.map (·.liftN n (is.length+1))) := by
  have h := T.projMotive_lift' C us (ps := ps) (is := is) (earlier := earlier) (i := i)
    (ρ := .skipN .refl n) hidx hftype his
  simp only [← VExpr.liftN_eq_lift', VExpr.lift'_consN_skipN] at h
  exact h

end VInductDecl'

end Lean4Lean
