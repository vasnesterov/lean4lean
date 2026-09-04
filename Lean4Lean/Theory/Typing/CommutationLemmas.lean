import Lean4Lean.Verify.TypeChecker.EtaStructG
import Lean4Lean.Theory.Inductive.ProjGenLift
import Lean4Lean.Theory.Inductive.ProjGenInst
import Lean4Lean.Theory.Inductive.ProjClosedG

/-!
# η-expansion commutes with weakening and with level instantiation

`Theory/Typing/StructEtaPrice.lean:53` prices the fourteenth `IsDefEq` constructor and names
**five** missing commutation lemmas that its ~40 congruence/stability sites would need:
`projTerm_weakN`, `projTermG_weakN`, `etaExpansion_weakN`, `etaExpansionG_weakN` and
`etaExpansionG_instL`.

**Two of the five were already in the tree.**  That claim was made by a *name* search
(`scripts/exists.lean`, on `_weakN`), and this tree spells the syntactic weakening of a `VExpr`
`liftN`/`lift'`, never `weakN` — `weakN` here is a *judgement*-level suffix
(`VEnv.HasType.weakN`, `VEnv.IsDefEqU.weakN_iff`).  A conclusion-shape scan
(`scripts/shape.lean`, `HEADS="Lean4Lean.VInductDecl'.projTerm Lean4Lean.VExpr.lift'"`, and the
`projTermG` analogue) reports:

* `projTerm_weakN`  = `VInductDecl'.projTerm_lift'`  (`Theory/Inductive/Structure.lean:357`) — **present**
* `projTermG_weakN` = `VInductDecl'.projTermG_lift'` (`Theory/Inductive/ProjGenLift.lean:289`) — **present**

The other three are genuinely absent (0 hits for `etaExpansion`/`etaExpansionG` against both
`VExpr.lift'` and `VExpr.liftN`, and the 13 hits for `etaExpansionG`+`VExpr.instL` are all
`IsDefEqSE`/`HasArgsSE` recursors plus `StructEtaG.congrProj_at_projAllG`), and this file proves
them.  See `docs/handoff-commutation.md` for every instrument call.

## What is here

§1 `projAll_lift'`, `etaExpansion_lift'`, `etaExpansion_liftN` (= the brief's `etaExpansion_weakN`)
§2 `projAllG_lift'`, `etaExpansionG_lift'`, `etaExpansionG_liftN` (= `etaExpansionG_weakN`)
§3 `projAllG_instL`, `etaExpansionG_instL`
§4 firings at two real structures, so none of the above is admired rather than instantiated.

## The one non-ordinary thing, named precisely

All three are ordinary structural work — a `List.map_congr_left` over `List.range` on top of the
existing `projTerm(G)` lemma — with **one** asymmetry that is not a proof artefact:

> the two `liftN`/`lift'` lemmas need `T.indices = []`; `etaExpansionG_instL` needs nothing.

`projAll(G)` calls `projTerm(G)` at `is := []`, and `projTerm_lift'`/`projTermG_lift'` carry
`his : is.length = T.indices.length`, so `is := []` forces `T.indices = []`.  `projTerm_instL`
and `projTermG_instL` carry no such hypothesis, so the `instL` lemma is unconditional.  This is
not a gap: `T.indices = []` is already a clause of `VEnv.StructEta` and `VEnv.StructEtaG`
(structure eta applies only to an index-free block, mirroring the C++ `isNonRecStructure`'s
`numIndices = 0` test), so it is free at every site that would consume these lemmas.  The
weakening lemmas additionally carry `ProjClosed`/`ProjClosedG` and `ps.length = D.np`, inherited
from `projTerm(G)_lift'` for the reason documented at `VInductDecl'.ProjClosed`; both are
likewise already available at a `StructEta`/`StructEtaG` site
(`VEnv.IsStructure.projClosed`, `VEnv.IsStructureG.projClosedG`, and the `HasArgs` clause).
-/

namespace Lean4Lean

open VExpr

namespace VInductDecl'

variable (D : VInductDecl') (T : VIndType) (C : VIndCtor) (us : List VLevel)

/-! ## §1 The narrow η-expansion commutes with weakening -/

/-- `projAll` commutes with `lift'`.  The companion to `projAll_instL`
(`Theory/Inductive/StructureEta.lean:139`), which needs no hypotheses; this one inherits
`ProjClosed`, `ps.length = D.np` and — because `projAll` fixes `is := []` — `T.indices = []`. -/
theorem projAll_lift' (hcl : D.ProjClosed T C) {ps : List VExpr} {e : VExpr} {ρ : Lift}
    (hps : ps.length = D.np) (hidx : T.indices = []) :
    (D.projAll T C us ps e).map (·.lift' ρ)
      = D.projAll T C us (ps.map (·.lift' ρ)) (e.lift' ρ) := by
  simp only [projAll, List.map_map, Function.comp_def]
  refine List.map_congr_left fun i hi => ?_
  simpa using D.projTerm_lift' T C us hcl (ps := ps) (is := []) (e := e) (i := i) (ρ := ρ)
    hps (by simp [hidx]) (List.mem_range.1 hi)

/-- **The η-expansion commutes with `lift'`.** -/
theorem etaExpansion_lift' (hcl : D.ProjClosed T C) {ps : List VExpr} {e : VExpr} {ρ : Lift}
    (hps : ps.length = D.np) (hidx : T.indices = []) :
    (D.etaExpansion T C us ps e).lift' ρ
      = D.etaExpansion T C us (ps.map (·.lift' ρ)) (e.lift' ρ) := by
  rw [etaExpansion, etaExpansion, VExpr.lift'_mkApp, List.map_append,
    D.projAll_lift' T C us hcl hps hidx]
  rfl

/-- **`etaExpansion_weakN`**: the `liftN` form, which is the one the `weakN` congruence sites
want, since `VEnv.IsDefEq.weakN` (`Theory/Typing/Lemmas.lean:531`) is stated over
`e.liftN n k`.  A corollary of `etaExpansion_lift'` via `VExpr.lift'_consN_skipN`. -/
theorem etaExpansion_liftN (hcl : D.ProjClosed T C) {ps : List VExpr} {e : VExpr} {n k : Nat}
    (hps : ps.length = D.np) (hidx : T.indices = []) :
    (D.etaExpansion T C us ps e).liftN n k
      = D.etaExpansion T C us (ps.map (·.liftN n k)) (e.liftN n k) := by
  simp only [← VExpr.lift'_consN_skipN]
  exact D.etaExpansion_lift' T C us hcl hps hidx

/-- The pricing document's spelling of `etaExpansion_liftN`, so that a name search for the
lemma `StructEtaPrice.lean:53` asks for actually resolves. -/
theorem etaExpansion_weakN (hcl : D.ProjClosed T C) {ps : List VExpr} {e : VExpr} {n k : Nat}
    (hps : ps.length = D.np) (hidx : T.indices = []) :
    (D.etaExpansion T C us ps e).liftN n k
      = D.etaExpansion T C us (ps.map (·.liftN n k)) (e.liftN n k) :=
  D.etaExpansion_liftN T C us hcl hps hidx

/-! ## §2 The generalised η-expansion commutes with weakening -/

/-- `projAllG` commutes with `lift'`. -/
theorem projAllG_lift' (H : D.ProjClosedG) {ps : List VExpr} {e : VExpr} {j : Nat} {ρ : Lift}
    (hTj : D.types[j]? = some T) (hctors : T.ctors = [C])
    (hps : ps.length = D.np) (hidx : T.indices = []) :
    (D.projAllG T C us ps j e).map (·.lift' ρ)
      = D.projAllG T C us (ps.map (·.lift' ρ)) j (e.lift' ρ) := by
  simp only [projAllG, List.map_map, Function.comp_def]
  refine List.map_congr_left fun i hi => ?_
  simpa using D.projTermG_lift' T C us H (ps := ps) (is := []) (e := e) (i := i) (j := j)
    (ρ := ρ) hTj hctors hps (by simp [hidx]) (List.mem_range.1 hi)

/-- **The generalised η-expansion commutes with `lift'`.** -/
theorem etaExpansionG_lift' (H : D.ProjClosedG) {ps : List VExpr} {e : VExpr} {j : Nat}
    {ρ : Lift} (hTj : D.types[j]? = some T) (hctors : T.ctors = [C])
    (hps : ps.length = D.np) (hidx : T.indices = []) :
    (D.etaExpansionG T C us ps j e).lift' ρ
      = D.etaExpansionG T C us (ps.map (·.lift' ρ)) j (e.lift' ρ) := by
  rw [etaExpansionG, etaExpansionG, VExpr.lift'_mkApp, List.map_append,
    D.projAllG_lift' T C us H hTj hctors hps hidx]
  rfl

/-- **`etaExpansionG_weakN`**: the `liftN` form. -/
theorem etaExpansionG_liftN (H : D.ProjClosedG) {ps : List VExpr} {e : VExpr} {j n k : Nat}
    (hTj : D.types[j]? = some T) (hctors : T.ctors = [C])
    (hps : ps.length = D.np) (hidx : T.indices = []) :
    (D.etaExpansionG T C us ps j e).liftN n k
      = D.etaExpansionG T C us (ps.map (·.liftN n k)) j (e.liftN n k) := by
  simp only [← VExpr.lift'_consN_skipN]
  exact D.etaExpansionG_lift' T C us H hTj hctors hps hidx

/-- The pricing document's spelling of `etaExpansionG_liftN`. -/
theorem etaExpansionG_weakN (H : D.ProjClosedG) {ps : List VExpr} {e : VExpr} {j n k : Nat}
    (hTj : D.types[j]? = some T) (hctors : T.ctors = [C])
    (hps : ps.length = D.np) (hidx : T.indices = []) :
    (D.etaExpansionG T C us ps j e).liftN n k
      = D.etaExpansionG T C us (ps.map (·.liftN n k)) j (e.liftN n k) :=
  D.etaExpansionG_liftN T C us H hTj hctors hps hidx

/-! ## §3 The generalised η-expansion commutes with level instantiation

Unconditionally, exactly as `etaExpansion_instL` does in the narrow case: `projTermG_instL`
(`Theory/Inductive/ProjGenInst.lean:414`) carries no side conditions, so neither do these. -/

/-- `projAllG` commutes with `instL`.  Companion to `projAll_instL`. -/
theorem projAllG_instL {ps : List VExpr} {j : Nat} {e : VExpr} {ls : List VLevel} :
    (D.projAllG T C us ps j e).map (VExpr.instL ls)
      = D.projAllG T C (us.map (VLevel.inst ls)) (ps.map (VExpr.instL ls)) j (e.instL ls) := by
  simp [projAllG, List.map_map, Function.comp_def, projTermG_instL]

/-- **`etaExpansionG_instL`**, the third of the five. -/
theorem etaExpansionG_instL {ps : List VExpr} {j : Nat} {e : VExpr} {ls : List VLevel} :
    (D.etaExpansionG T C us ps j e).instL ls
      = D.etaExpansionG T C (us.map (VLevel.inst ls)) (ps.map (VExpr.instL ls)) j
          (e.instL ls) := by
  simp [etaExpansionG, VExpr.instL_mkApp, VExpr.instL, List.map_append,
    D.projAllG_instL T C us]

end VInductDecl'

/-! ## §4 Firings

Each of the three new results is instantiated at a real structure, so none of them is stated
without being used.  The two structures are the ones the eta work already uses as witnesses:
`bazDecl` (`Theory/Inductive/StructureEta.lean:577`), an index-free **two**-field structure in
`Prop`, and `MutField.decl` (`Verify/TypeChecker/EtaStructG.lean:385`), a two-type mutual block
in `Type` whose member `B` has **one** field — so neither firing is the zero-field degenerate
case, and `projAll(G)` is a non-empty list in both. -/

/-- `bazDecl`'s telescopes are closed at their declared arities.  Direct, rather than through
`VEnv.IsStructure.projClosed`, which would drag `bazEnv.Ordered` in. -/
theorem bazDecl_projClosed : bazDecl.ProjClosed bazType bazCtor where
  params := by simp [bazDecl]
  indices := by simp [bazType]
  fields := by simp [bazCtor, bazField, bazDecl, VExpr.ClosedTele, VExpr.ClosedN]

/-- `MutField.decl`'s telescopes are closed, at every member of the block. -/
theorem MutField.decl_projClosedG : MutField.decl.ProjClosedG where
  params := by simp [MutField.decl]
  indices := by
    intro t T' hT
    match t, hT with
    | 0, h => cases h; simp [MutField.aTy]
    | 1, h => cases h; simp [MutField.bTy]
  fields := by
    intro t T' hT C' hC
    match t, hT with
    | 0, h =>
      cases h; simp [MutField.aTy] at hC; subst hC
      simp [MutField.aCtor, MutField.decl]
    | 1, h =>
      cases h; simp [MutField.bTy] at hC; subst hC
      simp [MutField.bCtor, bazField, MutField.decl, VExpr.ClosedTele, VExpr.ClosedN]
  recArgs := by
    intro t T' hT C' hC
    match t, hT with
    | 0, h =>
      cases h; simp [MutField.aTy] at hC; subst hC
      simp [MutField.aCtor, VIndCtor.recFields]
    | 1, h =>
      cases h; simp [MutField.bTy] at hC; subst hC
      simp [MutField.bCtor, VIndCtor.recFields, bazField]

/-- **`etaExpansion_liftN` fires**, at `bazDecl`'s two-field structure: weakening the subject
`.bvar 0` past one binder weakens the whole η-expansion, projections included. -/
theorem etaExpansion_liftN_fires :
    (bazDecl.etaExpansion bazType bazCtor [] [] (.bvar 0)).liftN 1 0
      = bazDecl.etaExpansion bazType bazCtor [] [] (.bvar 1) := by
  simpa [VExpr.liftN, liftVar] using bazDecl.etaExpansion_liftN bazType bazCtor []
    bazDecl_projClosed (ps := []) (e := .bvar 0) (n := 1) (k := 0) rfl rfl

/-- …and the firing is **not vacuous**: the two sides of `etaExpansion_liftN_fires` are
different terms, so the lemma moved something.  (`projAll` here has length 2, and both entries
are genuine `projTerm`s — `bazEnv_etaExpansion_eq`.) -/
theorem etaExpansion_liftN_fires_nontrivial :
    (bazDecl.etaExpansion bazType bazCtor [] [] (.bvar 0)).liftN 1 0
      ≠ bazDecl.etaExpansion bazType bazCtor [] [] (.bvar 0) := by
  rw [etaExpansion_liftN_fires]
  simp only [VInductDecl'.etaExpansion, VInductDecl'.projAll, VInductDecl'.projTerm,
    show List.range bazCtor.fields.length = [0, 1] from rfl, List.map_cons, List.map_nil,
    List.nil_append, VExpr.mkApp, VInductDecl'.projCore_eq]
  simp

/-- **`etaExpansionG_liftN` fires**, at `MutField.decl`'s positive-field member `B`, block
index `1` — the block where `projCore` is arity-wrong and only `projCoreG` works
(`MutField.projCore_arity_wrong_here`).  So the G lemma is exercised somewhere the narrow one
provably cannot reach. -/
theorem etaExpansionG_liftN_fires :
    (MutField.decl.etaExpansionG MutField.bTy MutField.bCtor [] [] 1 (.bvar 0)).liftN 1 0
      = MutField.decl.etaExpansionG MutField.bTy MutField.bCtor [] [] 1 (.bvar 1) := by
  simpa [VExpr.liftN, liftVar] using MutField.decl.etaExpansionG_liftN MutField.bTy
    MutField.bCtor [] MutField.decl_projClosedG (ps := []) (e := .bvar 0) (j := 1)
    (n := 1) (k := 0) rfl rfl rfl rfl

/-- **`etaExpansionG_instL` fires**, and at a level substitution that actually does something:
`us = [.param 0]` and `ls = [.succ .zero]`, with the subject `.sort (.param 0)` rewritten too.
No well-formedness hypothesis is needed, which is the §3 asymmetry made concrete — `decl` is
`uvars = 0`, so this instance is *not* available to the `liftN` lemmas' `ProjClosed` route and
does not need to be. -/
theorem etaExpansionG_instL_fires :
    (MutField.decl.etaExpansionG MutField.bTy MutField.bCtor [.param 0] [] 1
        (.sort (.param 0))).instL [.succ .zero]
      = MutField.decl.etaExpansionG MutField.bTy MutField.bCtor [.succ .zero] [] 1
          (.sort (.succ .zero)) := by
  simpa [VExpr.instL, VLevel.inst] using MutField.decl.etaExpansionG_instL MutField.bTy
    MutField.bCtor [.param 0] (ps := []) (j := 1) (e := .sort (.param 0))
    (ls := [.succ .zero])

end Lean4Lean
