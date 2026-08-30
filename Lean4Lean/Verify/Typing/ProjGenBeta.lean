import Lean4Lean.Verify.Typing.ProjGenInst

/-!
# Ingredient (b) of `realMinor_hasType_gen`: the motive's body, saturated

`docs/handoff-projections.md` §0.6 item 1(b) names "a block-index generalisation of
`projMotiveBody_instAll`" as one of the three things the *real* minor's typing lemma needs.
That is this file.

**Correction to the handoff.**  §0.6 located `projMotiveBody_instAll` in
`Verify/Typing/Lemmas.lean`.  It is *used* there (lines 1296 and 1361); it is **declared** in
`Theory/Inductive/StructureClosed.lean:1298`, together with the two lemmas it runs on —
`VInductDecl'.projTerm_instAll` and `VInductDecl'.projArgs_eq_map`
(`Theory/Inductive/Structure.lean:585,600`) — and `ftype_closedN`
(`StructureClosed.lean:1226`).  All four are narrow: they take `D.ProjClosed T C`, and
`projTerm`/`projArgs` rather than `projTermG`/`projArgsG`.  So the generalisation is four
lemmas, not one.

Nothing here is edited in place: the narrow four keep their statements, and these are
separate declarations at the generalised term, exactly as `projCoreG` is separate from
`projCore`.

What is *not* here: ingredient (c), the field-variable lookup through the ih block, whose
bulk is `projMinor_hasType`'s `ProjHasType` strong induction.  This file is deliberately the
part that does **not** need that induction, so that when the induction is attempted it is
the only thing open.
-/

namespace Lean4Lean

open VExpr

namespace VInductDecl'

/-- **`ftype_closedN`, at an arbitrary block member.**  Field `i`'s stored type, at the use
site's levels, is closed at `np + i`.  `ProjClosed.fields` is about *the* constructor `C`;
`ProjClosedG.fields` quantifies over every `(t, C')` of the block, so the index and the
constructor have to be supplied. -/
theorem ProjClosedG.ftype_closedN {D : VInductDecl'} (H : D.ProjClosedG) {j : Nat}
    {T : VIndType} (hTj : D.types[j]? = some T) {C : VIndCtor} (hC : C ∈ T.ctors)
    {us : List VLevel} {i : Nat} (hi : i < C.fields.length) :
    ((C.fields.getD i default).type.instL us).ClosedN (D.np + i) := by
  have hget : (C.fields.map (·.type))[i]? = some (C.fields.getD i default).type := by
    rw [List.getElem?_map, List.getElem?_eq_getElem hi]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  exact (VExpr.ClosedTele.getElem? (H.fields j T hTj C hC) hget).instL

/-- **`projTerm_instAll`, generalised**: `projTermG_instN` iterated over a whole spine.

Note there is **no `1 ≤ k` side condition**, and there could not be: the iteration
instantiates at cut `0` on every step (`VExpr.instAll_cons` then `Nat.zero_add`).  The narrow
`projTerm_instN` has no such premise either — only `projArgs_instN` does, and `projTerm_instN`
discharges it because it calls `projArgs_instN` at `k + |is| + 1`.  `projTermG_instN` was
stated with a `1 ≤ k` premise when it was first written; it was removed, because this lemma
is exactly where it would have been unsatisfiable. -/
theorem projTermG_instAll (D : VInductDecl') (T : VIndType) (C : VIndCtor)
    (us : List VLevel) (H : D.ProjClosedG) {j : Nat} (hTj : D.types[j]? = some T)
    (hctors : T.ctors = [C]) {i : Nat} (hi : i < C.fields.length) :
    ∀ {M ps is : List VExpr} {e : VExpr}, ps.length = D.np →
      is.length = T.indices.length →
      VExpr.instAll (D.projTermG T C us ps is i j e) M
        = D.projTermG T C us (ps.map (VExpr.instAll · M)) (is.map (VExpr.instAll · M)) i j
            (VExpr.instAll e M)
  | [], _, _, _, _, _ => by simp
  | _ :: M, ps, is, e, hps, his => by
    rw [VExpr.instAll_cons, Nat.zero_add,
      D.projTermG_instN T C us H hTj hctors hps his hi,
      D.projTermG_instAll T C us H hTj hctors hi (M := M)
        (by simpa using hps) (by simpa using his)]
    simp only [List.map_map, Function.comp_def, VExpr.instAll_cons, Nat.zero_add]

/-- **`projArgs_eq_map`, generalised**: `projArgsG` is the list of the earlier generalised
projections of `.bvar 0`.  Unconditional, as the narrow one is. -/
theorem projArgsG_eq_map (D : VInductDecl') (T : VIndType) (C : VIndCtor)
    (us : List VLevel) (ps is : List VExpr) (j : Nat) :
    ∀ i, D.projArgsG T C us ps is j i
      = (List.range i).map (fun k => D.projTermG T C us ps is k j (.bvar 0))
  | 0 => rfl
  | i+1 => by
    rw [VInductDecl'.projArgsG, D.projArgsG_eq_map T C us ps is j i, List.range_succ,
      List.map_append]
    rfl

/-- **`projMotiveBody_instAll`, generalised.**  The real motive's body, saturated by index
terms and a major premise, is field `i`'s type with the parameters and the earlier
*generalised* projections of that major premise substituted.

The narrow lemma's `hcl : D.ProjClosed T C` becomes `D.ProjClosedG` plus the two
`IsStructureG` fields `hTj`/`hctors`; the latter are needed only because `projTermG_instN`
needs them (they are what makes `projected_fields_lt` hold).  Everything else is the same
proof: `instAll_instAll` at the closedness bound, then `instAll_liftN` cancels the parameter
half and `projTermG_instAll` rewrites each of the `i` earlier projections. -/
theorem projMotiveBodyG_instAll (D : VInductDecl') (T : VIndType) (C : VIndCtor)
    (us : List VLevel) (H : D.ProjClosedG) {j : Nat} (hTj : D.types[j]? = some T)
    (hctors : T.ctors = [C]) {i : Nat} (hi : i < C.fields.length)
    {ps js : List VExpr} {x : VExpr} (hps : ps.length = D.np)
    (hjs : js.length = T.indices.length) :
    VExpr.instAll
      (VExpr.instAll ((C.fields.getD i default).type.instL us)
        (ps.map (·.liftN (T.indices.length+1))
          ++ D.projArgsG T C us (ps.map (·.liftN (T.indices.length+1)))
              (bvars 1 T.indices.length) j i))
      (js ++ [x])
      = VExpr.instAll ((C.fields.getD i default).type.instL us)
          (ps ++ (List.range i).map fun k => D.projTermG T C us ps js k j x) := by
  have hC : C ∈ T.ctors := by rw [hctors]; exact List.mem_singleton_self _
  have hlen : (js ++ [x]).length = T.indices.length + 1 := by simp [hjs]
  have hL : (ps.map (·.liftN (T.indices.length+1))
      ++ D.projArgsG T C us (ps.map (·.liftN (T.indices.length+1)))
          (bvars 1 T.indices.length) j i).length = D.np + i := by
    simp [hps, D.length_projArgsG]
  have hcancel : ∀ p : VExpr,
      VExpr.instAll (p.liftN (T.indices.length+1)) (js ++ [x]) 0 = p := by
    intro p; rw [← hlen]; exact VExpr.instAll_liftN _ _ _
  rw [VExpr.instAll_instAll (by rw [hL]; exact H.ftype_closedN hTj hC hi)]
  congr 1
  rw [List.map_append]
  congr 1
  · simp [List.map_map, Function.comp_def, hcancel]
  · rw [D.projArgsG_eq_map, List.map_map]
    refine List.map_congr_left fun k hk => ?_
    simp only [Function.comp_def]
    rw [D.projTermG_instAll T C us H hTj hctors (by simp at hk; omega)
      (by simp [hps]) (by simp)]
    congr 1
    · simp [List.map_map, Function.comp_def, hcancel]
    · exact VExpr.map_instAll_bvars_mid hjs
    · exact VExpr.instAll_bvar_zero

end VInductDecl'

end Lean4Lean
