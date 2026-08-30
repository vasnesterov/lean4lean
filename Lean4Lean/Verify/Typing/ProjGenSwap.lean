import Lean4Lean.Verify.Typing.ProjGenMotive
import Lean4Lean.Verify.Typing.ProjSkip

/-!
# The swap half of the ι-law chain, at an arbitrary block member

The companion of `ProjGenMotive.lean`: the five lemmas of `docs/handoff-projections.md`
§0*.7 item 1 that route through `VExpr.SwapCtx`, generalised from `VEnv.IsStructure` to the
two facts `IsStructureG` actually carries (`D.types[j]? = some T`, `C ∈ T.ctors`) plus
`D.ProjClosedG`.

**This module inherits a hole cone, by design and unavoidably.**  `VEnv.HasType.swapCtx`
runs on `VEnv.HasType.weakN_iff`, backed by `Theory/Typing/UniqueTyping.lean`'s `weakN_iff`
`sorry`; the narrow chain (`ProjSkip.lean`, `Verify/Typing/Lemmas.lean`) has exactly the same
dependency, and `ProjGenMinorNarrow.lean` is kept separate for the same reason.  Measured
cone: `{weakN_iff, forallE_inv_stratified}`.  `ProjGenMotive.lean`'s cone is empty and stays
that way.

## The one structural change

The narrow lemmas obtain the motive's binder context from `motiveCtx_wf`, which at `j = 0`
needs only the parameter spine.  At `j > 0` the *earlier motives* are part of the spine that
instantiates `D.motiveType j`, so the context fact is taken here as an explicit premise
`hΔ` — exactly `motiveCtxG_wf`'s conclusion (`ProjGenMotive.lean`), which the consumer
discharges from the padding-motive block.  Carrying the conclusion rather than
`padMotiveCtx_wf`'s `hspine` keeps the five statements independent of how the motive block
is built.
-/

namespace Lean4Lean

open VExpr

variable {env : VEnv} {U : Nat} {S : Lean.Name} {D : VInductDecl'} {T : VIndType}
  {C : VIndCtor} {us : List VLevel}

/-! ## The swap data -/

/-- `onCtxFields_instL` at an arbitrary block member. -/
theorem onCtxFields_instLG (henv : env.Ordered) (hI : D.IotaCtx env)
    {j : Nat} (hTj : D.types[j]? = some T) (hC : C ∈ T.ctors)
    (h7 : ∀ l ∈ us, l.WF U) {Δ : List VExpr} (hΔ : OnCtx Δ (env.IsType U)) (i : Nat) :
    OnCtx ((D.params.map (VExpr.instL us)
      ++ (C.fields.take i).map (fun F => F.type.instL us)).reverse ++ Δ) (env.IsType U) := by
  have hCwf := hI.toRecCtx.ctors j T hTj C hC
  have h0 := OnCtx.instL (env := env) (ls := us) (U' := U) h7 (hCwf.onCtxFields henv i)
  rw [List.map_append, List.map_reverse, List.map_reverse, ← List.reverse_append] at h0
  simp only [List.map_map, Function.comp_def] at h0
  exact OnCtx.appendR henv hΔ (OnCtx.ctxClosed henv h0) h0

/-- `ftype_hasType_swapped` at an arbitrary block member. -/
theorem ftype_hasType_swappedG (henv : VEnv.WF env) (hI : D.IotaCtx env)
    (H : D.ProjClosedG) {j : Nat} (hTj : D.types[j]? = some T) (hC : C ∈ T.ctors)
    (h7 : ∀ l ∈ us, l.WF U) {i : Nat} (hi : i < C.fields.length) {Γ'' : List VExpr}
    (hΓ : OnCtx ((D.params.map (VExpr.instL us)
      ++ (C.fields.take i).map (fun F => F.type.instL us)).reverse ++ Γ'') (env.IsType U))
    {Fs' : List VExpr}
    (hsw : VExpr.SwapCtx ((C.fields.getD i default).type.instL us)
        (.sort ((C.fields.getD i default).lvl.inst us))
        ((C.fields.take i).map (fun F => F.type.instL us)) Fs') :
    env.HasType U ((D.params.map (VExpr.instL us) ++ Fs').reverse ++ Γ'')
      ((C.fields.getD i default).type.instL us)
      (.sort ((C.fields.getD i default).lvl.inst us)) :=
  VEnv.HasType.swapCtx henv (hsw.appendKeep (D.params.map (VExpr.instL us))) hΓ
    (ftype_hasTypeG henv.ordered hI H hTj hC h7 hi Γ'')

/-- **`VIndCtor.swapData` at an arbitrary block member.**  Verbatim the narrow proof with
`IsStructure` replaced by `hTj`/`hC`/`ProjClosedG`; `C.not_fieldUsed_skips` is already stated
at an arbitrary block index, and `VIndCtor.fieldUsed_index_irrel` (`ProjGen.lean`) says the
`FieldUsed D 0` written here is the same predicate as `FieldUsed D j`. -/
theorem VIndCtor.swapDataG (henv : VEnv.WF env) (hI : D.IotaCtx env)
    (H : D.ProjClosedG) {j : Nat} (hTj : D.types[j]? = some T) (hC : C ∈ T.ctors)
    (h7 : ∀ l ∈ us, l.WF U) {i : Nat} (hi : i < C.fields.length)
    {Δ : List VExpr} (hΔ : OnCtx Δ (env.IsType U))
    (qs es : List VExpr) (hes : es.length = i) :
    ∃ Fs' es' : List VExpr, Fs'.length = i ∧ es'.length = i ∧
      (∀ k, k < i → C.FieldUsed D 0 k →
        Fs'.getD k default = (C.fields.getD k default).type.instL us
        ∧ es'.getD k default = es.getD k default) ∧
      (∀ k, k < i → ¬ C.FieldUsed D 0 k →
        Fs'.getD k default = VExpr.swapUnit ∧ es'.getD k default = VExpr.sort .zero) ∧
      VExpr.instAll ((C.fields.getD i default).type.instL us) (qs ++ es) 0
        = VExpr.instAll ((C.fields.getD i default).type.instL us) (qs ++ es') 0 ∧
      env.HasType U ((D.params.map (VExpr.instL us) ++ Fs').reverse ++ Δ)
        ((C.fields.getD i default).type.instL us)
        (.sort ((C.fields.getD i default).lvl.inst us)) ∧
      OnCtx ((D.params.map (VExpr.instL us) ++ Fs').reverse ++ Δ) (env.IsType U) := by
  have hFlen : ((C.fields.take i).map (fun F => F.type.instL us)).length = i := by
    simp; omega
  have hget : ∀ k, k < i → ((C.fields.take i).map (fun F => F.type.instL us)).getD k default
      = (C.fields.getD k default).type.instL us := by
    intro k hk
    have hk' : k < C.fields.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_take_of_lt hk,
      List.getElem?_eq_getElem hk', List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hk']
    rfl
  obtain ⟨Fs', es', hsw, hlenF, hlenE, hkeep, hswap⟩ :=
    VExpr.SwapCtx.buildPair (b := (C.fields.getD i default).type.instL us)
      (B := .sort ((C.fields.getD i default).lvl.inst us))
      (fun j => ¬ C.FieldUsed D 0 j) (VExpr.sort .zero)
      ((C.fields.take i).map (fun F => F.type.instL us)) es (by rw [hFlen, hes]) (by
        intro j' hj hP
        rw [hFlen] at hj
        refine ⟨fun j'' hj' hj'' => ?_, ?_, ?_⟩
        · rw [hFlen] at hj''
          rw [hget j'' hj'']
          have := C.not_fieldUsed_skips (D := D) (j := 0) hP hj' (by omega)
          rw [show j'' - 1 - j' = j'' - j' - 1 from by omega] at this
          exact (VExpr.skips_iff.2 this).instL'
        · rw [hFlen]
          have := C.not_fieldUsed_skips (D := D) (j := 0) hP hj hi
          rw [show i - 1 - j' = i - j' - 1 from by omega] at this
          exact (VExpr.skips_iff.2 this).instL'
        · exact VExpr.skips_iff_exists.2
            ⟨.sort ((C.fields.getD i default).lvl.inst us), rfl⟩)
  rw [hFlen] at hlenF
  rw [hes] at hlenE
  refine ⟨Fs', es', hlenF, hlenE, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk hu
    obtain ⟨h1, h2⟩ := hkeep k (not_not_intro hu)
    exact ⟨by rw [h1, hget k hk], h2⟩
  · intro k hk hu
    exact hswap k hu (by rw [hFlen]; exact hk)
  · rw [VExpr.instAll_append, VExpr.instAll_append, hlenE, hes]
    refine VExpr.instAll_congr_of_skip (VExpr.InstAllSkip.build (by omega) ?_)
    intro m hm hne
    have hmu : ¬ C.FieldUsed D 0 m := by
      intro hu
      exact hne (hkeep m (not_not_intro hu)).2.symm
    have hmi : m < i := by omega
    have hsk := (VExpr.skips_iff.2
      (C.not_fieldUsed_skips (D := D) (j := 0) hmu hmi hi)).instL'
      (ls := us)
    rw [show i - 1 - m = 0 + es.length - 1 - m from by omega] at hsk
    exact hsk.instAll_of_lt (by omega)
  · exact ftype_hasType_swappedG henv hI H hTj hC h7 hi
      (onCtxFields_instLG henv.ordered hI hTj hC h7 hΔ i) hsw
  · exact OnCtx.swapCtx henv (hsw.appendKeep (D.params.map (VExpr.instL us)))
      (onCtxFields_instLG henv.ordered hI hTj hC h7 hΔ i)

/-! ## The swapped induction hypothesis and the motive -/

/-- `projArgs_hasArgs_swapped` at an arbitrary block member.  `motiveCtx_wf`'s output becomes
the premise `hΔ`; everything else is the narrow proof with `projTerm` ↦ `projTermG`.

Three of the narrow lemma's hypotheses are **dropped, not carried**: `hI : D.IotaCtx env`,
`hC : C ∈ T.ctors` and `h7` are unused once the context fact is a premise, and keeping them
would have over-hypothesised the statement.  `hTj` survives because `ProjClosedG.indices`
needs it. -/
theorem projArgsG_hasArgs_swapped (henv : env.Ordered)
    (H : D.ProjClosedG) {j : Nat} (hTj : D.types[j]? = some T)
    (hname : T.name = S) {i : Nat} (hi : i < C.fields.length)
    (IH : ∀ k, k < i → C.FieldUsed D 0 k → ProjHasTypeG env U S D T C us j k)
    {Γ ps : List VExpr} (hps : ps.length = D.np)
    (hpsA : env.HasArgs U Γ (D.params.map (VExpr.instL us)) ps)
    (hΔ : OnCtx (((VExpr.const T.name us).mkApp
        (ps.map (·.liftN T.indices.length) ++ bvars 0 T.indices.length))
      :: ((VExpr.instAllTele (T.indices.map (VExpr.instL us)) ps).reverse ++ Γ))
      (env.IsType U))
    {Fs' es' : List VExpr}
    (hlenF : Fs'.length = i) (hlenE : es'.length = i)
    (hused : ∀ k, k < i → C.FieldUsed D 0 k →
      Fs'.getD k default = (C.fields.getD k default).type.instL us
      ∧ es'.getD k default = D.projTermG T C us (ps.map (·.liftN (T.indices.length+1)))
          (bvars 1 T.indices.length) k j (.bvar 0))
    (hunused : ∀ k, k < i → ¬ C.FieldUsed D 0 k →
      Fs'.getD k default = VExpr.swapUnit ∧ es'.getD k default = VExpr.sort .zero) :
    env.HasArgs U
      (((VExpr.const T.name us).mkApp
          (ps.map (·.liftN T.indices.length) ++ bvars 0 T.indices.length))
        :: ((VExpr.instAllTele (T.indices.map (VExpr.instL us)) ps).reverse ++ Γ))
      (VExpr.instAllTele Fs' (ps.map (·.liftN (T.indices.length+1)))) es' := by
  obtain ⟨hOnΔ1, hctorTy⟩ := hΔ
  have hclI : VExpr.ClosedTele (T.indices.map (VExpr.instL us)) ps.length := by
    rw [hps]; exact VExpr.ClosedTele.map_instL (H.indices j T hTj)
  have hW : Ctx.LiftN (T.indices.length + 1) 0 Γ
      (((VExpr.const T.name us).mkApp
          (ps.map (·.liftN T.indices.length) ++ bvars 0 T.indices.length))
        :: ((VExpr.instAllTele (T.indices.map (VExpr.instL us)) ps).reverse ++ Γ)) := by
    have := Ctx.LiftN.zero (Γ := Γ) (n := T.indices.length + 1)
      (((VExpr.const T.name us).mkApp
          (ps.map (·.liftN T.indices.length) ++ bvars 0 T.indices.length))
        :: (VExpr.instAllTele (T.indices.map (VExpr.instL us)) ps).reverse) (by simp)
    simpa using this
  have hqs := VEnv.HasArgs.weakN henv hW hpsA
  rw [VExpr.liftTele_eq_self (VExpr.ClosedTele.map_instL H.params) (Nat.zero_le _)] at hqs
  have hjs := VEnv.HasArgs.bvars (env := env) (U := U)
    (Δ := [(VExpr.const T.name us).mkApp
      (ps.map (·.liftN T.indices.length) ++ bvars 0 T.indices.length)])
    (As := VExpr.instAllTele (T.indices.map (VExpr.instL us)) ps) (Γ₀ := Γ)
  rw [List.length_cons, List.length_nil, VExpr.length_instAllTele, List.length_map,
    show 0 + 1 = 1 from rfl, Nat.add_comm 1 T.indices.length,
    VExpr.liftTele_instAllTele₀ hclI, List.singleton_append] at hjs
  have hbv0 : env.HasType U
      (((VExpr.const T.name us).mkApp
          (ps.map (·.liftN T.indices.length) ++ bvars 0 T.indices.length))
        :: ((VExpr.instAllTele (T.indices.map (VExpr.instL us)) ps).reverse ++ Γ))
      (.bvar 0)
      ((VExpr.const S us).mkApp
        (ps.map (·.liftN (T.indices.length+1)) ++ bvars 1 T.indices.length)) := by
    have h := VEnv.HasType.bvar (env := env) (U := U) (Lookup.zero
      (Γ := (VExpr.instAllTele (T.indices.map (VExpr.instL us)) ps).reverse ++ Γ)
      (ty := (VExpr.const T.name us).mkApp
        (ps.map (·.liftN T.indices.length) ++ bvars 0 T.indices.length)))
    rw [VExpr.lift, VExpr.liftN_mkApp, VExpr.liftN, List.map_append, List.map_map,
      Function.comp_def, VExpr.map_liftN_bvars_lo (Nat.zero_le _)] at h
    simp only [VExpr.liftN_liftN] at h
    rw [← hname]
    exact h
  have hΔ' : OnCtx
      (((VExpr.const T.name us).mkApp
          (ps.map (·.liftN T.indices.length) ++ bvars 0 T.indices.length))
        :: ((VExpr.instAllTele (T.indices.map (VExpr.instL us)) ps).reverse ++ Γ))
      (env.IsType U) := ⟨hOnΔ1, hctorTy⟩
  have hFtake : Fs'.take i = Fs' := List.take_of_length_le (by omega)
  rw [← hFtake]
  refine VEnv.HasArgs.ofGetD (by omega) hlenE fun k hk => ?_
  by_cases hu : C.FieldUsed D 0 k
  · obtain ⟨hF, hE⟩ := hused k hk hu
    rw [hF, hE]
    have hIHk := IH k hk hu hΔ' hbv0 (by simp [hps]) (by simp) hqs hjs
    have heq : VExpr.instAll ((C.fields.getD k default).type.instL us)
        ((ps.map (·.liftN (T.indices.length+1)))
          ++ (List.range k).map (fun m => D.projTermG T C us
              (ps.map (·.liftN (T.indices.length+1))) (bvars 1 T.indices.length) m j
              (.bvar 0))) 0
        = VExpr.instAll ((C.fields.getD k default).type.instL us)
            ((ps.map (·.liftN (T.indices.length+1))) ++ es'.take k) 0 := by
      refine C.instAll_swap_eq D us (by omega) (by simp; omega) (by simp) ?_
      intro m hm hmu
      have hmk : m < k := by simpa using hm
      obtain ⟨-, hEm⟩ := hused m (by omega) hmu
      rw [show ((List.range k).map (fun m => D.projTermG T C us
            (ps.map (·.liftN (T.indices.length+1))) (bvars 1 T.indices.length) m j
            (.bvar 0))).getD m default
          = D.projTermG T C us (ps.map (·.liftN (T.indices.length+1)))
              (bvars 1 T.indices.length) m j (.bvar 0) from by
          rw [List.getD_eq_getElem?_getD, List.getElem?_map,
            List.getElem?_range (by omega)]; rfl,
        show (es'.take k).getD m default = es'.getD m default from by
          rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
            List.getElem?_take_of_lt hmk],
        hEm]
    rw [← heq]
    exact hIHk
  · obtain ⟨hF, hE⟩ := hunused k hk hu
    rw [hF, hE]
    simp only [VExpr.swapUnit, VExpr.instAll_sort]
    exact VExpr.swapUnit_inhabited

/-- `projMotiveBody_hasType_swapped` at an arbitrary block member. -/
theorem projMotiveBodyG_hasType_swapped (henv : env.Ordered)
    (H : D.ProjClosedG) (h7 : ∀ l ∈ us, l.WF U) {i : Nat}
    (hlv : (C.fields.getD i default).lvl.inst us ≈ D.elimLvl.inst (D.projLvls C us i))
    {Γ ps : List VExpr}
    (hpsA : env.HasArgs U Γ (D.params.map (VExpr.instL us)) ps)
    {earlier es' Fs' : List VExpr}
    (hes' : env.HasArgs U
      (((VExpr.const T.name us).mkApp
          (ps.map (·.liftN T.indices.length) ++ bvars 0 T.indices.length))
        :: ((VExpr.instAllTele (T.indices.map (VExpr.instL us)) ps).reverse ++ Γ))
      (VExpr.instAllTele Fs' (ps.map (·.liftN (T.indices.length+1)))) es')
    (hty : env.HasType U ((D.params.map (VExpr.instL us) ++ Fs').reverse ++
        (((VExpr.const T.name us).mkApp
            (ps.map (·.liftN T.indices.length) ++ bvars 0 T.indices.length))
          :: ((VExpr.instAllTele (T.indices.map (VExpr.instL us)) ps).reverse ++ Γ)))
      ((C.fields.getD i default).type.instL us)
      (.sort ((C.fields.getD i default).lvl.inst us)))
    (heq : VExpr.instAll ((C.fields.getD i default).type.instL us)
        (ps.map (·.liftN (T.indices.length+1)) ++ earlier) 0
      = VExpr.instAll ((C.fields.getD i default).type.instL us)
          (ps.map (·.liftN (T.indices.length+1)) ++ es') 0) :
    env.HasType U
      (((VExpr.const T.name us).mkApp
          (ps.map (·.liftN T.indices.length) ++ bvars 0 T.indices.length))
        :: ((VExpr.instAllTele (T.indices.map (VExpr.instL us)) ps).reverse ++ Γ))
      (VExpr.instAll ((C.fields.getD i default).type.instL us)
        (ps.map (·.liftN (T.indices.length+1)) ++ earlier))
      (.sort (D.elimLvl.inst (D.projLvls C us i))) := by
  have hW : Ctx.LiftN (T.indices.length + 1) 0 Γ
      (((VExpr.const T.name us).mkApp
          (ps.map (·.liftN T.indices.length) ++ bvars 0 T.indices.length))
        :: ((VExpr.instAllTele (T.indices.map (VExpr.instL us)) ps).reverse ++ Γ)) := by
    have := Ctx.LiftN.zero (Γ := Γ) (n := T.indices.length + 1)
      (((VExpr.const T.name us).mkApp
          (ps.map (·.liftN T.indices.length) ++ bvars 0 T.indices.length))
        :: (VExpr.instAllTele (T.indices.map (VExpr.instL us)) ps).reverse) (by simp)
    simpa using this
  have hqs := VEnv.HasArgs.weakN henv hW hpsA
  rw [VExpr.liftTele_eq_self (VExpr.ClosedTele.map_instL H.params) (Nat.zero_le _)] at hqs
  have hbody := instAll_field_isType_swapped henv hqs hes' hty heq
  exact VEnv.IsDefEq.defeqDF
    (VEnv.IsDefEq.sortDF (VLevel.WF.inst h7)
      (VLevel.WF.inst (VInductDecl'.projLvls_wf (C := C) h7 i)) hlv) hbody

/-- **`projMotiveBody_hasType_guarded` at an arbitrary block member.**  The swap data is built
internally, so the caller supplies only the used-index induction hypothesis and the motive's
binder context. -/
theorem projMotiveBodyG_hasType_guarded (henv : VEnv.WF env) (hI : D.IotaCtx env)
    (H : D.ProjClosedG) {j : Nat} (hTj : D.types[j]? = some T) (hC : C ∈ T.ctors)
    (hname : T.name = S) (h7 : ∀ l ∈ us, l.WF U) {i : Nat} (hi : i < C.fields.length)
    (hlvi : (C.fields.getD i default).lvl.inst us ≈ D.elimLvl.inst (D.projLvls C us i))
    (hIH : ∀ k, k < i → C.FieldUsed D 0 k → ProjHasTypeG env U S D T C us j k)
    {Γ ps : List VExpr} (hps : ps.length = D.np)
    (hpsA : env.HasArgs U Γ (D.params.map (VExpr.instL us)) ps)
    (hΔ : OnCtx (((VExpr.const T.name us).mkApp
        (ps.map (·.liftN T.indices.length) ++ bvars 0 T.indices.length))
      :: ((VExpr.instAllTele (T.indices.map (VExpr.instL us)) ps).reverse ++ Γ))
      (env.IsType U)) :
    env.HasType U
      (((VExpr.const T.name us).mkApp
          (ps.map (·.liftN T.indices.length) ++ bvars 0 T.indices.length))
        :: ((VExpr.instAllTele (T.indices.map (VExpr.instL us)) ps).reverse ++ Γ))
      (VExpr.instAll ((C.fields.getD i default).type.instL us)
        (ps.map (·.liftN (T.indices.length+1))
          ++ D.projArgsG T C us (ps.map (·.liftN (T.indices.length+1)))
              (bvars 1 T.indices.length) j i))
      (.sort (D.elimLvl.inst (D.projLvls C us i))) := by
  have hord := henv.ordered
  obtain ⟨Fs', es', hlenF, hlenE, hused, hunused, heq, hty, -⟩ :=
    C.swapDataG henv hI H hTj hC h7 hi hΔ (ps.map (·.liftN (T.indices.length+1)))
      (D.projArgsG T C us (ps.map (·.liftN (T.indices.length+1)))
        (bvars 1 T.indices.length) j i)
      (D.length_projArgsG T C us j)
  have hgetArgs : ∀ k, k < i →
      (D.projArgsG T C us (ps.map (·.liftN (T.indices.length+1)))
        (bvars 1 T.indices.length) j i).getD k default
      = D.projTermG T C us (ps.map (·.liftN (T.indices.length+1)))
          (bvars 1 T.indices.length) k j (.bvar 0) := by
    intro k hk
    rw [D.projArgsG_eq_map, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range hk]
    rfl
  have hes' := projArgsG_hasArgs_swapped hord H hTj hname hi hIH hps hpsA hΔ
    hlenF hlenE
    (fun k hk hu => ⟨(hused k hk hu).1, by rw [(hused k hk hu).2, hgetArgs k hk]⟩)
    hunused
  exact projMotiveBodyG_hasType_swapped hord H h7 hlvi hpsA hes' hty heq

/-- **`projMotiveTerm_hasType_swapped` at an arbitrary block member**: the generalised motive
inhabits the recursor's `j`-th motive binder, instantiated at the parameter spine and the
`j` earlier motives. -/
theorem projMotiveTermG_hasType_swapped (henv : VEnv.WF env) (hI : D.IotaCtx env)
    (H : D.ProjClosedG) {j : Nat} (hTj : D.types[j]? = some T) (hC : C ∈ T.ctors)
    (hname : T.name = S) (h3 : us.length = D.uvars) (h7 : ∀ l ∈ us, l.WF U)
    {i : Nat} (hi : i < C.fields.length)
    (hlvi : (C.fields.getD i default).lvl.inst us ≈ D.elimLvl.inst (D.projLvls C us i))
    (hIH : ∀ k, k < i → C.FieldUsed D 0 k → ProjHasTypeG env U S D T C us j k)
    {Γ ps ms : List VExpr} (hps : ps.length = D.np) (hms : ms.length = j)
    (hpsA : env.HasArgs U Γ (D.params.map (VExpr.instL us)) ps)
    (hΔ : OnCtx (((VExpr.const T.name us).mkApp
        (ps.map (·.liftN T.indices.length) ++ bvars 0 T.indices.length))
      :: ((VExpr.instAllTele (T.indices.map (VExpr.instL us)) ps).reverse ++ Γ))
      (env.IsType U)) :
    env.HasType U Γ (projMotiveTermG D T C us ps i j)
      (VExpr.instAll ((D.motiveType j).instL (D.projLvls C us i)) (ps ++ ms)) := by
  obtain ⟨hOnΔ1, uc, hctorTy⟩ := hΔ
  have hΔ' : OnCtx
      (((VExpr.const T.name us).mkApp
          (ps.map (·.liftN T.indices.length) ++ bvars 0 T.indices.length))
        :: ((VExpr.instAllTele (T.indices.map (VExpr.instL us)) ps).reverse ++ Γ))
      (env.IsType U) := ⟨hOnΔ1, uc, hctorTy⟩
  rw [projMotiveTermG,
    motiveType_instL_instAll_gen D T C (by rw [List.getD_eq_getElem?_getD, hTj]; rfl)
      h3 hps hms]
  exact VEnv.HasType.mkLams hOnΔ1 (VEnv.HasType.lam hctorTy
    (projMotiveBodyG_hasType_guarded henv hI H hTj hC hname h7 hi hlvi hIH hps hpsA hΔ'))

/-- **The same, packaged at `IsStructureG`.**  Written to check that the widened shape
predicate really supplies everything the five lemmas above ask for: `types`, `ctors` and
`name` are its own fields, and `D.ProjClosedG` comes from `decl` by
`IsStructureG.projClosedG`.  Nothing else is needed — in particular no `nm = 1`, no
`nmin = 1`, no `noRec`.

The `hΔ` and `hms` premises stay, because they are about the *motive block* the consumer
builds, not about the shape of the declaration; `motiveCtxG_wf` discharges the first from
`padMotiveCtx_wf`. -/
theorem VEnv.IsStructureG.projMotiveTermG_hasType_swapped (henv : VEnv.WF env)
    (hI : D.IotaCtx env) {j : Nat} (H : env.IsStructureG S D j T C)
    (h3 : us.length = D.uvars) (h7 : ∀ l ∈ us, l.WF U)
    {i : Nat} (hi : i < C.fields.length)
    (hlvi : (C.fields.getD i default).lvl.inst us ≈ D.elimLvl.inst (D.projLvls C us i))
    (hIH : ∀ k, k < i → C.FieldUsed D 0 k → ProjHasTypeG env U S D T C us j k)
    {Γ ps ms : List VExpr} (hps : ps.length = D.np) (hms : ms.length = j)
    (hpsA : env.HasArgs U Γ (D.params.map (VExpr.instL us)) ps)
    (hΔ : OnCtx (((VExpr.const T.name us).mkApp
        (ps.map (·.liftN T.indices.length) ++ bvars 0 T.indices.length))
      :: ((VExpr.instAllTele (T.indices.map (VExpr.instL us)) ps).reverse ++ Γ))
      (env.IsType U)) :
    env.HasType U Γ (projMotiveTermG D T C us ps i j)
      (VExpr.instAll ((D.motiveType j).instL (D.projLvls C us i)) (ps ++ ms)) :=
  _root_.Lean4Lean.projMotiveTermG_hasType_swapped henv hI (H.projClosedG henv.ordered) H.types
    (by rw [H.ctors]; exact List.mem_singleton_self _) H.name h3 h7 hi hlvi hIH hps hms
    hpsA hΔ

end Lean4Lean
