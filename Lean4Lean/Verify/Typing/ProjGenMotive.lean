import Lean4Lean.Verify.Typing.ProjGenMinor

/-!
# The motive of the generalised projection, and `ProjHasTypeG`

`docs/handoff-projections.md` §0*.7 item 1 lists eleven lemmas of `projMinor_hasType`'s
ι-law/swap/β chain (`Verify/Typing/Lemmas.lean:984–1306`), every one of them stated at
`VEnv.IsStructure`, that the residual premise `hiota` of `realMinor_hasType_gen'` needs in an
`IsStructureG` form.  This file is the **swap-free** half of that list: the motive term at an
arbitrary block member, its `liftN` commutation, the predicate the strong induction runs on,
and the two context facts.

Everything here has an **empty hole cone**, deliberately.  The other half —
`swapData`, `projArgs_hasArgs_swapped`, `projMotiveBody_hasType_swapped`,
`projMotiveTerm_hasType_swapped`, `projMotiveBody_hasType_guarded` — goes through
`VEnv.HasType.swapCtx`, whose cone is `{weakN_iff, forallE_inv_stratified}`; it lives in
`ProjGenSwap.lean` for that reason, exactly as `ProjGenMinorNarrow.lean` is kept apart from
`ProjGenMinor.lean`.

## What is *not* generalised, because it did not need to be

`VIndCtor.instAll_swap_eq` and `VIndCtor.instAll_take_swap_eq` (`ProjSkip.lean`) are stated
with `C.FieldUsed D 0`, but the block index is **invisible** to `FieldUsed`
(`VIndCtor.fieldUsed_index_irrel`, `ProjGen.lean`), so they are already the general
statements and are used unchanged.  So is `VExpr.swapSpine_exists`.
-/

namespace Lean4Lean

open VExpr

variable {env : VEnv} {U : Nat} {S : Lean.Name} {D : VInductDecl'} {T : VIndType}
  {C : VIndCtor} {us : List VLevel}

/-! ## The motive term -/

/-- `projCoreG`'s motive for field `i` of block member `j`, at parameter spine `ps`, spelled
out.  The generalisation of `projMotiveTerm` (`Theory/Inductive/StructureClosed.lean:1196`):
the only change is `projArgs` ↦ `projArgsG` in the body's spine, which is where the block
index enters. -/
def projMotiveTermG (D : VInductDecl') (T : VIndType) (C : VIndCtor) (us : List VLevel)
    (ps : List VExpr) (i j : Nat) : VExpr :=
  VExpr.mkLams (VExpr.instAllTele (T.indices.map (VExpr.instL us)) ps)
    (.lam ((VExpr.const T.name us).mkApp
        (ps.map (·.liftN T.indices.length) ++ bvars 0 T.indices.length))
      (VExpr.instAll ((C.fields.getD i default).type.instL us)
        (ps.map (·.liftN (T.indices.length+1))
          ++ D.projArgsG T C us (ps.map (·.liftN (T.indices.length+1)))
              (bvars 1 T.indices.length) j i)))

/-- `VIndType.projMotive_eq'`, generalised: `projCoreG`'s motive at its own `earlier` spine
**is** `projMotiveTermG`. -/
theorem VIndType.projMotiveG_eq' (D : VInductDecl') (T : VIndType) (C : VIndCtor)
    (us : List VLevel) {ps is : List VExpr} {i j : Nat}
    (h : is.length = T.indices.length) :
    T.projMotive C us ps is i
        (D.projArgsG T C us (ps.map (·.liftN (is.length+1))) (bvars 1 is.length) j i)
      = projMotiveTermG D T C us ps i j := by
  rw [VIndType.projMotive, h, projMotiveTermG]

/-- **At a narrow block the generalised motive is the old one**, on the nose — the collapse
test for the definition above, the analogue of `projTermG_eq_projTerm`. -/
theorem projMotiveTermG_eq_projMotiveTerm (D : VInductDecl') (T : VIndType) (C : VIndCtor)
    (us : List VLevel) (ps : List VExpr) (i : Nat)
    (htypes : D.types = [T]) (hctors : T.ctors = [C]) (hrec : C.recFields = [])
    (hus : us.length = D.uvars) :
    projMotiveTermG D T C us ps i 0 = projMotiveTerm D T C us ps i := by
  rw [projMotiveTermG, projMotiveTerm,
    D.projArgsG_eq_projArgs T C us htypes hctors hrec hus]

/-! ## The `liftN` commutation

The port of `projMotive_liftN` (`Theory/Inductive/StructureClosed.lean:1234`) with
`projArgs` ↦ `projArgsG` and `D.ProjClosed T C` ↦ `D.ProjClosedG`.  Both of the narrow
proof's ingredients already have generalised forms: `ProjClosedG.ftype_closedN`
(`ProjGenBeta.lean`) and `projArgsG_lift'` (`ProjGenLift.lean`). -/

theorem projMotiveG_liftN (D : VInductDecl') (T : VIndType) (C : VIndCtor) (us : List VLevel)
    (H : D.ProjClosedG) {j : Nat} (hTj : D.types[j]? = some T) (hctors : T.ctors = [C])
    {i : Nat} (hi : i < C.fields.length) {ps : List VExpr} {n : Nat}
    (hps : ps.length = D.np) :
    (projMotiveTermG D T C us ps i j).liftN n
      = projMotiveTermG D T C us (ps.map (·.liftN n)) i j := by
  have hC : C ∈ T.ctors := by rw [hctors]; exact List.mem_singleton_self _
  have hclI : VExpr.ClosedTele (T.indices.map (VExpr.instL us)) ps.length := by
    rw [hps]; exact VExpr.ClosedTele.map_instL (H.indices j T hTj)
  have hpmap : ∀ m : Nat,
      (ps.map (·.liftN (T.indices.length + m))).map (·.liftN n (T.indices.length + m))
        = (ps.map (·.liftN n)).map (·.liftN (T.indices.length + m)) := by
    intro m
    rw [List.map_map, List.map_map]
    refine List.map_congr_left fun p _ => ?_
    simp only [Function.comp_def]
    rw [VExpr.liftN'_liftN' (Nat.zero_le _) (Nat.le_add_right _ _), VExpr.liftN_liftN,
      Nat.add_comm]
  simp only [projMotiveTermG]
  rw [VExpr.liftN_mkLams, VExpr.liftTele_instAllTele₀ hclI, VExpr.length_instAllTele,
    List.length_map, Nat.zero_add]
  refine congrArg _ ?_
  simp only [VExpr.liftN]
  congr 1
  · rw [VExpr.liftN_mkApp, VExpr.liftN, List.map_append, VExpr.map_liftN_bvars_hi (by omega)]
    congr 2
    simpa using hpmap 0
  · have hL : (ps.map (·.liftN (T.indices.length+1))
        ++ D.projArgsG T C us (ps.map (·.liftN (T.indices.length+1)))
            (bvars 1 T.indices.length) j i).length = D.np + i := by
      simp [hps, D.length_projArgsG]
    have hclosed : ((C.fields.getD i default).type.instL us).ClosedN
        (0 + (ps.map (·.liftN (T.indices.length+1))
          ++ D.projArgsG T C us (ps.map (·.liftN (T.indices.length+1)))
              (bvars 1 T.indices.length) j i).length) := by
      rw [Nat.zero_add, hL]; exact H.ftype_closedN hTj hC hi
    have h0 := VExpr.lift'_instAll
      (A := (C.fields.getD i default).type.instL us)
      (ρ := (Lift.skipN .refl n).consN (T.indices.length + 1))
      (as := ps.map (·.liftN (T.indices.length+1))
        ++ D.projArgsG T C us (ps.map (·.liftN (T.indices.length+1)))
            (bvars 1 T.indices.length) j i)
      (k := 0) hclosed
    rw [Lift.consN_consN, Nat.add_zero, VExpr.lift'_consN_skipN] at h0
    rw [h0, List.map_append]
    congr 2
    · simp only [VExpr.lift'_consN_skipN]
      exact hpmap 1
    · rw [D.projArgsG_lift' T C us H hTj hctors (i := i)
        (ps := ps.map (·.liftN (T.indices.length+1))) (is := bvars 1 T.indices.length)
        (ρ := (Lift.skipN .refl n).consN (T.indices.length + 1))
        (by simp [hps]) (by simp) (Nat.le_of_lt hi)
        (Lift.consN_fixes.le (by omega))]
      simp only [VExpr.lift'_consN_skipN]
      rw [VExpr.map_liftN_bvars_hi (by omega), hpmap 1]

/-! ## The predicate the strong induction runs on -/

/-- **`ProjHasType` at an arbitrary block member.**  The conclusion of the generalised
projection's typing lemma at one field index, as a named predicate; the strong induction
quantifies `Γ`, `ps`, `ιs`, `e` *after* the index, so the induction hypothesis has to be
applied at several different contexts.

The block index `j` is a **parameter**, not something the predicate existentially supplies —
`projTermG` reads it to pick the motive slot, and a version that quantified it would be
satisfiable at the wrong slot. -/
def ProjHasTypeG (env : VEnv) (U : Nat) (S : Lean.Name) (D : VInductDecl') (T : VIndType)
    (C : VIndCtor) (us : List VLevel) (j k : Nat) : Prop :=
  ∀ {Γ ps ιs : List VExpr} {e : VExpr}, OnCtx Γ (env.IsType U) →
    env.HasType U Γ e ((VExpr.const S us).mkApp (ps ++ ιs)) →
    ps.length = D.np → ιs.length = T.indices.length →
    env.HasArgs U Γ (D.params.map (VExpr.instL us)) ps →
    env.HasArgs U Γ (VExpr.instAllTele (T.indices.map (VExpr.instL us)) ps) ιs →
    env.HasType U Γ (D.projTermG T C us ps ιs k j e)
      (VExpr.instAll ((C.fields.getD k default).type.instL us)
        (ps ++ (List.range k).map fun m => D.projTermG T C us ps ιs m j e))

/-- **At a narrow block the generalised predicate is the old one**, on the nose. -/
theorem projHasTypeG_eq (env : VEnv) (U : Nat) (S : Lean.Name) (D : VInductDecl')
    (T : VIndType) (C : VIndCtor) (us : List VLevel) (k : Nat)
    (htypes : D.types = [T]) (hctors : T.ctors = [C]) (hrec : C.recFields = [])
    (hus : us.length = D.uvars) :
    ProjHasTypeG env U S D T C us 0 k = ProjHasType env U S D T C us k := by
  simp only [ProjHasTypeG, ProjHasType,
    D.projTermG_eq_projTerm T C us _ _ _ _ htypes hctors hrec hus]

/-! ## The two context facts -/

/-- **`ftype_hasType` at an arbitrary block member.**  Field `i`'s stored type, moved to the
use site's levels and weakened into any context below the constructor's parameter-and-field-
prefix telescope.  `IsStructure`'s `types`/`ctors` become the two explicit facts
`hTj`/`hC`, and `D.ProjClosed T C` becomes `D.ProjClosedG`; nothing else changes. -/
theorem ftype_hasTypeG (henv : env.Ordered) (hI : D.IotaCtx env)
    (H : D.ProjClosedG) {j : Nat} (hTj : D.types[j]? = some T) (hC : C ∈ T.ctors)
    (h7 : ∀ l ∈ us, l.WF U) {i : Nat} (hi : i < C.fields.length) (Γ'' : List VExpr) :
    env.HasType U
      ((D.params.map (VExpr.instL us) ++
        (C.fields.take i).map (fun F => F.type.instL us)).reverse ++ Γ'')
      ((C.fields.getD i default).type.instL us)
      (.sort ((C.fields.getD i default).lvl.inst us)) := by
  have hCwf := hI.toRecCtx.ctors j T hTj C hC
  have hget : C.fields[i]? = some (C.fields.getD i default) := by
    rw [List.getElem?_eq_getElem hi]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  have hf := (hCwf.fields i _ hget).hasType
  have hf2 := VEnv.HasType.instL (ls := us) (U' := U) h7 hf
  have hctx : ((((C.fields.take i).map (·.type)).reverse ++ D.params.reverse).map
        (VExpr.instL us))
      = (D.params.map (VExpr.instL us) ++
          (C.fields.take i).map (fun F => F.type.instL us)).reverse := by
    simp [List.map_reverse, List.map_map, Function.comp_def]
  rw [hctx] at hf2
  have hcltele : VExpr.ClosedTele (D.params.map (VExpr.instL us) ++
      (C.fields.take i).map (fun F => F.type.instL us)) 0 := by
    refine VExpr.closedTele_append.2 ⟨VExpr.ClosedTele.map_instL H.params, ?_⟩
    have : VExpr.ClosedTele ((C.fields.map (·.type)).take i) D.np :=
      VExpr.ClosedTele.take (H.fields j T hTj C hC)
    have := VExpr.ClosedTele.map_instL (ls := us) this
    simpa [List.map_take, List.map_map, Function.comp_def, List.length_map] using this
  have hcc : CtxClosed ((D.params.map (VExpr.instL us) ++
      (C.fields.take i).map (fun F => F.type.instL us)).reverse) := by
    have := VExpr.ClosedTele.ctxClosed (Γ := []) (As := D.params.map (VExpr.instL us) ++
      (C.fields.take i).map (fun F => F.type.instL us)) (by simpa using hcltele) trivial
    rwa [List.append_nil] at this
  have := VEnv.IsDefEq.weakR henv hcc hf2 Γ''
  simp only [VExpr.instL] at this
  exact this

/-- **`motiveCtx_wf` at an arbitrary block member**, packaged as the single `OnCtx` the
consumers actually use: the motive's own binder context is the index telescope with the
major-premise binder on top.

This is `padMotiveCtx_wf` (`ProjGen.lean`) at `t := j`, `T' := T`, re-associated.  The
narrow lemma derives its `hspine` from `hpsA` alone because `j = 0` leaves no earlier
motives; at `j > 0` the earlier motives are genuinely part of the spine that instantiates
`D.motiveType j`, and the consumer (`projCoreG`'s motive block, whose prefix is all
*padding* motives — `padMotives_getElem_ne`) is where they are typed. -/
theorem motiveCtxG_wf (henv : env.Ordered) (hI : D.IotaCtx env)
    (h7 : ∀ l ∈ us, l.WF U) (h3 : us.length = D.uvars) {j : Nat} (hjle : j ≤ D.nm)
    (hTj : D.types[j]? = some T) {i : Nat} {Γ ps ms : List VExpr}
    (hΓ : OnCtx Γ (env.IsType U)) (hps : ps.length = D.np) (hms : ms.length = j)
    (hspine : env.HasArgs U Γ
      ((D.atRecTele D.params).map (VExpr.instL (D.projLvls C us i))
        ++ ((List.range j).map D.motiveType).map (VExpr.instL (D.projLvls C us i)))
      (ps ++ ms)) :
    OnCtx (((VExpr.const T.name us).mkApp
        (ps.map (·.liftN T.indices.length) ++ bvars 0 T.indices.length))
      :: ((VExpr.instAllTele (T.indices.map (VExpr.instL us)) ps).reverse ++ Γ))
      (env.IsType U) :=
  let ⟨h1, h2⟩ := padMotiveCtx_wf (C := C) (T' := T) henv hI h7 h3 hjle hTj
    hΓ hps hms hspine
  ⟨h1, h2⟩

end Lean4Lean
