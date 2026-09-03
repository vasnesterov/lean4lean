import Lean4Lean.Verify.Typing.ProjGenBlock

/-!
# Wall 2: `projTermG_hasType`

Work in progress.
-/

namespace Lean4Lean

open VExpr

variable {env : VEnv} {U : Nat} {S : Lean.Name} {D : VInductDecl'} {T : VIndType}
  {C : VIndCtor} {us : List VLevel} {j : Nat}

/-- `VEnv.IsStructure.iotaCtx` at an arbitrary block member.  The narrow proof never reads
`types`/`ctors`/`noRec`, only `decl`, so the widened statement is the same proof. -/
theorem VEnv.IsStructureG.iotaCtx (henv : env.Ordered) (H : env.IsStructureG S D j T C) :
    D.IotaCtx env := by
  obtain ⟨env₀, envF, hWF, hadd, hle⟩ := H.decl
  obtain ⟨env₁, env₂, env₃, h1, h2, h3, hF⟩ := VInductDecl'.addInduct'_stages hadd
  have hle₂ : env₂ ≤ env :=
    ((VEnv.addIndRecs_le h3).trans (hF ▸ VEnv.addIndRules_le)).trans hle
  refine ⟨hWF.recCtx h1 h2 hle₂ henv, fun t T' hT' => ?_⟩
  refine hle.constants (VEnv.addInduct'_constants hadd
    (Lean.mkRecName T'.name, ⟨D.recUvars, D.recType t⟩) ?_)
  simp only [VInductDecl'.allConsts, VInductDecl'.recConsts, List.mem_append, List.mem_map]
  exact .inr ⟨(T', t), List.mk_mem_zipIdx_iff_getElem?.2 hT', rfl⟩

/-- `VEnv.IsStructure.iotaDefeq` at an arbitrary constructor of an arbitrary block member:
the ι-rule of *any* entry of `ctorsAll` is in the environment.  The narrow version computes
`ctorsAll` from `types`/`ctors`; here `iotaRule_mem` does the same job from `hqC`. -/
theorem VEnv.IsStructureG.iotaDefeq (H : env.IsStructureG S D j T C) {q : Nat}
    {C' : VIndCtor} (hqC : D.ctorsAll[q]? = some (j, C')) :
    env.defeqs (D.iotaRule j q C') := by
  obtain ⟨env₀, envF, hWF, hadd, hle⟩ := H.decl
  exact hle.defeqs (VEnv.addInduct'_defeqs hadd _ (D.iotaRule_mem hqC))


/-- `args_closedN` at an arbitrary block member: the narrow proof reads `H` only through
`H.types0`/`H.memCtor`. -/
theorem args_closedN_gen (henv : env.Ordered) (hI : D.IotaCtx env)
    {t : Nat} {T' : VIndType} {C' : VIndCtor}
    (hT : D.types[t]? = some T') (hC : C' ∈ T'.ctors) :
    ∀ a ∈ C'.args, VExpr.ClosedN a (C'.fields.length + D.np) := by
  have hCwf : VIndCtor.WF env D t T' C' := hI.toRecCtx.ctors t T' hT C' hC
  have hcc : CtxClosed ((C'.fields.map (·.type)).reverse ++ D.params.reverse) :=
    OnCtx.ctxClosed henv (hCwf.onCtxAllFields henv)
  have hlen : ((C'.fields.map (·.type)).reverse ++ D.params.reverse).length
      = C'.fields.length + D.np := by simp [VInductDecl'.np]
  have h := VEnv.IsDefEq.closedN henv hCwf.result hcc
  rw [hlen, VIndCtor.canonResult, VInductDecl'.tyApp, VExpr.closedN_mkApp] at h
  intro a ha
  exact h.2 _ (List.mem_append_right _ ha)

/-- **The conclusion defeq of `realMinor_hasType_gen'`, at an arbitrary block member.**

This is the tail of `projMinor_hasType` (`Verify/Typing/Lemmas.lean`) — its `hFL`/`hFR`,
`swapData`, `hr`/`hDFearlier`, `hcong`, `hbetaQ` and assembly — generalised from
`VEnv.IsStructure` to `hTj`/`hctors`/`hname` plus `D.ProjClosedG`, with `projTerm` ↦
`projTermG … j` throughout.  The two facts about *earlier* fields that the narrow proof
derives inline are premises here, because that is exactly where the recursion sits:

* `hIH` — `ProjHasTypeG … j k` at `k < i`, and
* `hiotaK` — the ι law at `k < i`: the `k`-th generalised projection of the constructor
  applied to its own field variables is the `k`-th field variable.

Everything else is discharged. -/
theorem projGen_hiota (henv : VEnv.WF env) (hI : D.IotaCtx env) (H : D.ProjClosedG)
    (hTj : D.types[j]? = some T) (hctors : T.ctors = [C]) (hname : T.name = S)
    (hCall : (j, C) ∈ D.ctorsAll)
    (h3 : us.length = D.uvars) (h7 : ∀ l ∈ us, l.WF U)
    {i : Nat} (hi : i < C.fields.length)
    (hlv : ∀ k, k ≤ i → (k = i ∨ C.FieldUsed D 0 k) →
      (C.fields.getD k default).lvl.inst us ≈ D.elimLvl.inst (D.projLvls C us k))
    (hIH : ∀ k, k < i → C.FieldUsed D 0 k → ProjHasTypeG env U S D T C us j k)
    {Γ ps : List VExpr} (hps : ps.length = D.np)
    (hpsA : env.HasArgs U Γ (D.params.map (VExpr.instL us)) ps)
    (hOnΔF : OnCtx
      ((VExpr.instAllTele (C.fields.map fun F => F.type.instL us) ps).reverse ++ Γ)
      (env.IsType U))
    (hiotaK : ∀ k, k < i → C.FieldUsed D 0 k → env.IsDefEqU U
      ((VExpr.instAllTele (C.fields.map fun F => F.type.instL us) ps).reverse ++ Γ)
      (D.projTermG T C us (ps.map (·.liftN C.fields.length))
        (C.args.map fun a => VExpr.instAll (a.instL us) ps C.fields.length) k j
        ((VExpr.const C.name us).mkApp
          (ps.map (·.liftN C.fields.length) ++ bvars 0 C.fields.length)))
      (.bvar (C.fields.length - 1 - k))) :
    env.IsDefEq U
      ((VExpr.instAllTele (C.fields.map fun F => F.type.instL us) ps).reverse ++ Γ)
      (VExpr.instAll ((C.fields.getD i default).type.instL us)
        (ps.map (·.liftN C.fields.length)
          ++ (List.range i).map fun m => VExpr.bvar (C.fields.length - 1 - m)))
      (((projMotiveTermG D T C us ps i j).liftN C.fields.length).mkApp
        ((C.args.map fun a => VExpr.instAll (a.instL us) ps C.fields.length)
          ++ [(VExpr.const C.name us).mkApp
                (ps.map (·.liftN C.fields.length) ++ bvars 0 C.fields.length)]))
      (.sort (D.elimLvl.inst (D.projLvls C us i))) := by
  have hord := henv.ordered
  have hC : C ∈ T.ctors := by rw [hctors]; exact List.mem_singleton_self _
  have hCwf : VIndCtor.WF env D j T C := hI.toRecCtx.ctors j T hTj C hC
  have hlvi := hlv i (Nat.le_refl _) (.inl rfl)
  have hqsl : (ps.map (·.liftN C.fields.length)).length = D.np := by simp [hps]
  have hargsl : (C.args.map fun a =>
      VExpr.instAll (a.instL us) ps C.fields.length).length = T.indices.length := by
    simp [hCwf.args_len]
  have hWF : Ctx.LiftN C.fields.length 0 Γ
      ((VExpr.instAllTele (C.fields.map fun F => F.type.instL us) ps).reverse ++ Γ) :=
    Ctx.LiftN.zero _ (by simp)
  have hqsA := VEnv.HasArgs.weakN hord hWF hpsA
  rw [VExpr.liftTele_eq_self (VExpr.ClosedTele.map_instL H.params) (Nat.zero_le _)] at hqsA
  have hclI : VExpr.ClosedTele (T.indices.map (VExpr.instL us)) ps.length := by
    rw [hps]; exact VExpr.ClosedTele.map_instL (H.indices j T hTj)
  have hfeq : (C.fields.map fun F => F.type.instL us)
      = (C.fields.map (·.type)).map (VExpr.instL us) := by
    simp [List.map_map, Function.comp_def]
  have hclF : VExpr.ClosedTele (C.fields.map fun F => F.type.instL us) ps.length := by
    rw [hps, hfeq]; exact VExpr.ClosedTele.map_instL (H.fields j T hTj C hC)
  have hargsA := ctorArgs_hasArgs_gen hord hI h7 hTj hC hpsA
  rw [VExpr.liftTele_instAllTele₀ hclI] at hargsA
  have hctorT := ctorApp_hasType_gen hord hI h3 h7 hTj hC hCall hps hpsA
  have hfieldsA : env.HasArgs U
      ((VExpr.instAllTele (C.fields.map fun F => F.type.instL us) ps).reverse ++ Γ)
      (VExpr.instAllTele (C.fields.map fun F => F.type.instL us)
        (ps.map (·.liftN C.fields.length))) (bvars 0 C.fields.length) := by
    have h := VEnv.HasArgs.bvars (env := env) (U := U) (Δ := [])
      (As := VExpr.instAllTele (C.fields.map fun F => F.type.instL us) ps) (Γ₀ := Γ)
    rw [List.length_nil, VExpr.length_instAllTele, List.length_map, Nat.zero_add,
      VExpr.liftTele_instAllTele₀ hclF, List.nil_append] at h
    exact h
  -- the induction hypothesis, at the constructor's spine
  have hIHc : ∀ k, k < i → C.FieldUsed D 0 k → env.HasType U
      ((VExpr.instAllTele (C.fields.map fun F => F.type.instL us) ps).reverse ++ Γ)
      (D.projTermG T C us (ps.map (·.liftN C.fields.length))
        (C.args.map fun a => VExpr.instAll (a.instL us) ps C.fields.length) k j
        ((VExpr.const C.name us).mkApp
          (ps.map (·.liftN C.fields.length) ++ bvars 0 C.fields.length)))
      (VExpr.instAll ((C.fields.getD k default).type.instL us)
        (ps.map (·.liftN C.fields.length)
          ++ (List.range k).map fun m => D.projTermG T C us
              (ps.map (·.liftN C.fields.length))
              (C.args.map fun a => VExpr.instAll (a.instL us) ps C.fields.length) m j
              ((VExpr.const C.name us).mkApp
                (ps.map (·.liftN C.fields.length) ++ bvars 0 C.fields.length)))) :=
    fun k hk hu => hIH k hk hu hOnΔF (by rw [← hname]; exact hctorT) hqsl hargsl hqsA hargsA
  -- the right spine: the minor premise's own field variables
  have hrgt : ∀ k, k < C.fields.length → env.HasType U
      ((VExpr.instAllTele (C.fields.map fun F => F.type.instL us) ps).reverse ++ Γ)
      (.bvar (C.fields.length - 1 - k))
      (VExpr.instAll ((C.fields.getD k default).type.instL us)
        (ps.map (·.liftN C.fields.length)
          ++ (List.range k).map fun m => VExpr.bvar (C.fields.length - 1 - m))) :=
    fun k hk => D.realMinor_field_hasType H hTj hC hk hps
  -- the swap: the *unused* earlier fields never had to be typed
  have hFL : ∀ k, k < i →
      ((List.range i).map fun m => D.projTermG T C us (ps.map (·.liftN C.fields.length))
        (C.args.map fun a => VExpr.instAll (a.instL us) ps C.fields.length) m j
        ((VExpr.const C.name us).mkApp
          (ps.map (·.liftN C.fields.length) ++ bvars 0 C.fields.length))).getD k default
      = D.projTermG T C us (ps.map (·.liftN C.fields.length))
          (C.args.map fun a => VExpr.instAll (a.instL us) ps C.fields.length) k j
          ((VExpr.const C.name us).mkApp
            (ps.map (·.liftN C.fields.length) ++ bvars 0 C.fields.length)) := by
    intro k hk
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]; rfl
  have hFR : ∀ k, k < i →
      ((List.range i).map fun m => VExpr.bvar (C.fields.length - 1 - m)).getD k default
      = VExpr.bvar (C.fields.length - 1 - k) := by
    intro k hk
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]; rfl
  obtain ⟨Fs', ls', hlenF, hlenL, husedL, hunusedL, heqL, hty, hΓ'sw⟩ :=
    C.swapDataG henv hI H hTj hC h7 hi hOnΔF (ps.map (·.liftN C.fields.length))
      ((List.range i).map fun m => D.projTermG T C us (ps.map (·.liftN C.fields.length))
        (C.args.map fun a => VExpr.instAll (a.instL us) ps C.fields.length) m j
        ((VExpr.const C.name us).mkApp
          (ps.map (·.liftN C.fields.length) ++ bvars 0 C.fields.length)))
      (by simp)
  obtain ⟨rs', hlenR, hkeepR, hswapR⟩ :=
    VExpr.swapSpine_exists (fun j => ¬ C.FieldUsed D 0 j) (VExpr.sort .zero)
      ((List.range i).map fun m => VExpr.bvar (C.fields.length - 1 - m))
  rw [List.length_map, List.length_range] at hlenR
  have hlsU : ∀ k, k < i → C.FieldUsed D 0 k → ls'.getD k default
      = D.projTermG T C us (ps.map (·.liftN C.fields.length))
          (C.args.map fun a => VExpr.instAll (a.instL us) ps C.fields.length) k j
          ((VExpr.const C.name us).mkApp
            (ps.map (·.liftN C.fields.length) ++ bvars 0 C.fields.length)) :=
    fun k hk hu => by rw [(husedL k hk hu).2, hFL k hk]
  have hrsU : ∀ k, k < i → C.FieldUsed D 0 k →
      rs'.getD k default = VExpr.bvar (C.fields.length - 1 - k) :=
    fun k hk hu => by rw [hkeepR k (not_not_intro hu), hFR k hk]
  have hrsN : ∀ k, k < i → ¬ C.FieldUsed D 0 k → rs'.getD k default = VExpr.sort .zero :=
    fun k hk hu => hswapR k hu (by simp; omega)
  have hr := VEnv.HasArgs.ofGetD (env := env) (U := U)
    (Γ := (VExpr.instAllTele (C.fields.map fun F => F.type.instL us) ps).reverse ++ Γ)
    (As := Fs') (as := ps.map (·.liftN C.fields.length)) (es := rs')
    (i := i) (by omega) hlenR (fun k hk => by
      by_cases hu : C.FieldUsed D 0 k
      · rw [(husedL k hk hu).1, hrsU k hk hu,
          ← C.instAll_take_swap_eq D us (k := k) (by omega) (ts := rs')
            (f := fun m => VExpr.bvar (C.fields.length - 1 - m)) (by omega)
            (fun m hm hmu => hrsU m (by omega) hmu)]
        exact hrgt k (by omega)
      · rw [(hunusedL k hk hu).1, hrsN k hk hu]
        simp only [VExpr.swapUnit, VExpr.instAll_sort]
        exact VExpr.swapUnit_inhabited)
  rw [List.take_of_length_le (by omega)] at hr
  have hDFearlier := VEnv.HasArgsDF.ofGetD (env := env) (U := U)
    (Γ := (VExpr.instAllTele (C.fields.map fun F => F.type.instL us) ps).reverse ++ Γ)
    (As := Fs') (as := ps.map (·.liftN C.fields.length)) (es := ls') (fs := rs')
    (i := i) (by omega) hlenL hlenR (fun k hk => by
      by_cases hu : C.FieldUsed D 0 k
      · rw [(husedL k hk hu).1, hlsU k hk hu, hrsU k hk hu,
          ← C.instAll_take_swap_eq D us (k := k) (by omega) (ts := ls')
            (f := fun m => D.projTermG T C us (ps.map (·.liftN C.fields.length))
              (C.args.map fun a => VExpr.instAll (a.instL us) ps C.fields.length) m j
              ((VExpr.const C.name us).mkApp
                (ps.map (·.liftN C.fields.length) ++ bvars 0 C.fields.length)))
            (by omega) (fun m hm hmu => hlsU m (by omega) hmu)]
        exact VEnv.IsDefEqU.of_l henv hOnΔF (hiotaK k hk hu) (hIHc k hk hu)
      · rw [(hunusedL k hk hu).1, (hunusedL k hk hu).2, hrsN k hk hu]
        simp only [VExpr.swapUnit, VExpr.instAll_sort]
        exact VExpr.swapUnit_inhabited)
  rw [List.take_of_length_le (by omega)] at hDFearlier
  have hDF := VEnv.HasArgsDF.append hqsA.toDF hDFearlier
  have hrfull := VEnv.HasArgs.append hqsA hr
  have heqR : VExpr.instAll ((C.fields.getD i default).type.instL us)
      (ps.map (·.liftN C.fields.length)
        ++ (List.range i).map fun m => VExpr.bvar (C.fields.length - 1 - m)) 0
      = VExpr.instAll ((C.fields.getD i default).type.instL us)
          (ps.map (·.liftN C.fields.length) ++ rs') 0 := by
    have := C.instAll_take_swap_eq D us (k := i) hi (ts := rs')
      (f := fun m => VExpr.bvar (C.fields.length - 1 - m))
      (qs := ps.map (·.liftN C.fields.length)) (by omega)
      (fun m hm hmu => hrsU m hm hmu)
    rwa [List.take_of_length_le (by omega)] at this
  have hcong0 := VEnv.IsDefEq.instAllCongrSort hord hDF hrfull hΓ'sw hty
  have hcong : env.IsDefEq U
      ((VExpr.instAllTele (C.fields.map fun F => F.type.instL us) ps).reverse ++ Γ)
      (VExpr.instAll ((C.fields.getD i default).type.instL us)
        (ps.map (·.liftN C.fields.length)
          ++ (List.range i).map fun m => D.projTermG T C us
              (ps.map (·.liftN C.fields.length))
              (C.args.map fun a => VExpr.instAll (a.instL us) ps C.fields.length) m j
              ((VExpr.const C.name us).mkApp
                (ps.map (·.liftN C.fields.length) ++ bvars 0 C.fields.length))))
      (VExpr.instAll ((C.fields.getD i default).type.instL us)
        (ps.map (·.liftN C.fields.length)
          ++ (List.range i).map fun m => VExpr.bvar (C.fields.length - 1 - m)))
      (.sort ((C.fields.getD i default).lvl.inst us)) := by
    rw [heqL, heqR]; exact hcong0
  -- the β-reduction of the lifted motive
  have hΔQ := motiveCtxG_wf' hord hI h7 h3 hTj C i hOnΔF hqsl hqsA
  have hbodyQ := projMotiveBodyG_hasType_guarded henv hI H hTj hC hname h7 hi hlvi hIH
    hqsl hqsA hΔQ
  obtain ⟨hOnQ, hctorTyQ⟩ := hΔQ
  have hctorInstQ : VExpr.instAll ((VExpr.const T.name us).mkApp
      ((ps.map (·.liftN C.fields.length)).map (·.liftN T.indices.length)
        ++ bvars 0 T.indices.length))
      (C.args.map fun a => VExpr.instAll (a.instL us) ps C.fields.length) 0
      = (VExpr.const T.name us).mkApp (ps.map (·.liftN C.fields.length)
        ++ C.args.map fun a => VExpr.instAll (a.instL us) ps C.fields.length) := by
    have hcancel : ∀ p : VExpr, VExpr.instAll (p.liftN T.indices.length)
        (C.args.map fun a => VExpr.instAll (a.instL us) ps C.fields.length) 0 = p := by
      intro p; rw [← hargsl]; exact VExpr.instAll_liftN _ _ _
    rw [VExpr.instAll_mkApp, VExpr.instAll_const, List.map_append, List.map_map,
      VExpr.map_instAll_bvars' hargsl]
    simp [Function.comp_def, hcancel]
  have hArgsQ := VEnv.HasArgs.concat hargsA
    (show env.HasType U _ _ _ by rw [hctorInstQ]; exact hctorT)
  have hbetaQ := VEnv.IsDefEq.betaMkLams hord
    (as := (C.args.map fun a => VExpr.instAll (a.instL us) ps C.fields.length)
      ++ [(VExpr.const C.name us).mkApp
        (ps.map (·.liftN C.fields.length) ++ bvars 0 C.fields.length)])
    (by simp only [List.reverse_append, List.reverse_cons, List.reverse_nil,
          List.nil_append, List.cons_append]
        exact ⟨hOnQ, hctorTyQ⟩)
    hArgsQ
    (by simp only [List.reverse_append, List.reverse_cons, List.reverse_nil,
          List.nil_append, List.cons_append]
        exact hbodyQ)
  rw [VExpr.mkLams_append, VExpr.instAll_sort,
    D.projMotiveBodyG_instAll T C us H hTj hctors hi
      (ps := ps.map (·.liftN C.fields.length))
      (js := C.args.map fun a => VExpr.instAll (a.instL us) ps C.fields.length)
      (x := (VExpr.const C.name us).mkApp
        (ps.map (·.liftN C.fields.length) ++ bvars 0 C.fields.length)) hqsl hargsl] at hbetaQ
  -- assemble
  rw [projMotiveG_liftN D T C us H hTj hctors hi hps, projMotiveTermG]
  exact (hbetaQ.trans (VEnv.IsDefEq.defeqDF (VEnv.IsDefEq.sortDF (VLevel.WF.inst h7)
    (VLevel.WF.inst (VInductDecl'.projLvls_wf (C := C) h7 i)) hlvi) hcong)).symm

/-- **The real minor's typing, at field index `k`, as a named predicate.**

Literally `projCoreG_hasType_of_hreal`'s `hreal` premise (`ProjGenBlock.lean`), quantified
over the same data `ProjHasTypeG` quantifies over.  It is what the strong induction on the
field index actually carries: `hreal` at field `k` is needed *inside* the ι-law step at every
later field, in a **different** context (the constructor's own field telescope), which is why
`Γ`, `ps`, `ιs` and `e` have to be quantified here rather than fixed. -/
def ProjRealMinorG (env : VEnv) (U : Nat) (S : Lean.Name) (D : VInductDecl') (T : VIndType)
    (C : VIndCtor) (us : List VLevel) (j k : Nat) : Prop :=
  ∀ {Γ ps ιs : List VExpr} {e : VExpr}, OnCtx Γ (env.IsType U) →
    env.HasType U Γ e ((VExpr.const S us).mkApp (ps ++ ιs)) →
    ps.length = D.np → ιs.length = T.indices.length →
    env.HasArgs U Γ (D.params.map (VExpr.instL us)) ps →
    env.HasArgs U Γ (VExpr.instAllTele (T.indices.map (VExpr.instL us)) ps) ιs →
    ∀ q C', D.ctorsAll[q]? = some (j, C') →
      env.HasType U Γ
        (D.realMinor (D.projLvls C us k)
          (ps ++ D.padMotives T C us ps ιs k j
              (D.projArgsG T C us (ps.map (·.liftN (ιs.length+1)))
                (bvars 1 ιs.length) j k) e
            ++ (D.padMinors (D.projLvls C us k) ps
                (D.padMotives T C us ps ιs k j
                  (D.projArgsG T C us (ps.map (·.liftN (ιs.length+1)))
                    (bvars 1 ιs.length) j k) e)
                ((T.projMotive C us ps ιs k
                  (D.projArgsG T C us (ps.map (·.liftN (ιs.length+1)))
                    (bvars 1 ιs.length) j k)).mkApp (ιs ++ [e])) k j).take q) k q C')
        (VExpr.instAll ((D.minorType q j C').instL (D.projLvls C us k))
          (ps ++ D.padMotives T C us ps ιs k j
              (D.projArgsG T C us (ps.map (·.liftN (ιs.length+1)))
                (bvars 1 ιs.length) j k) e
            ++ (D.padMinors (D.projLvls C us k) ps
                (D.padMotives T C us ps ιs k j
                  (D.projArgsG T C us (ps.map (·.liftN (ιs.length+1)))
                    (bvars 1 ιs.length) j k) e)
                ((T.projMotive C us ps ιs k
                  (D.projArgsG T C us (ps.map (·.liftN (ιs.length+1)))
                    (bvars 1 ιs.length) j k)).mkApp (ιs ++ [e])) k j).take q))

/-- **The type side: `projCoreG_hasType_of_hreal`'s conclusion, retyped.**

`projCoreG_hasType_of_hreal` types the recursor application at the *motive applied to the
index spine and the major premise*; `ProjHasTypeG` asks for it at field `i`'s stored type with
the parameters and the earlier generalised projections substituted.  The two are joined by one
β-reduction of the motive (`projMotiveBodyG_instAll`), exactly as `projTerm_hasType`'s "step 4"
joins them at a narrow block. -/
theorem projTermG_hasType_of_hreal (henv : VEnv.WF env) (hI : D.IotaCtx env)
    (H : D.ProjClosedG) (hTj : D.types[j]? = some T) (hctors : T.ctors = [C])
    (hname : T.name = S) (h3 : us.length = D.uvars) (h7 : ∀ l ∈ us, l.WF U)
    {i : Nat} (hi : i < C.fields.length)
    (hlvi : (C.fields.getD i default).lvl.inst us ≈ D.elimLvl.inst (D.projLvls C us i))
    (hIH : ∀ k, k < i → C.FieldUsed D 0 k → ProjHasTypeG env U S D T C us j k)
    (hreal : ProjRealMinorG env U S D T C us j i) :
    ProjHasTypeG env U S D T C us j i := by
  have hord := henv.ordered
  have hC : C ∈ T.ctors := by rw [hctors]; exact List.mem_singleton_self _
  intro Γ ps ιs e hΓ he hps hιs hpsA hιsA
  have hcore := projCoreG_hasType_of_hreal henv hI H hTj hC hname h3 h7 hi hlvi hIH
    hΓ hps hιs hpsA hιsA he (hreal hΓ he hps hιs hpsA hιsA)
  have hΔQ := motiveCtxG_wf' hord hI h7 h3 hTj C i hΓ hps hpsA
  have hbodyT := projMotiveBodyG_hasType_guarded henv hI H hTj hC hname h7 hi hlvi hIH
    hps hpsA hΔQ
  obtain ⟨hOnΔ1, hctorTyIT⟩ := hΔQ
  have hctorInst : VExpr.instAll ((VExpr.const T.name us).mkApp
      (ps.map (·.liftN T.indices.length) ++ bvars 0 T.indices.length)) ιs 0
      = (VExpr.const S us).mkApp (ps ++ ιs) := by
    have hcancel : ∀ p : VExpr, VExpr.instAll (p.liftN T.indices.length) ιs 0 = p := by
      intro p; rw [← hιs]; exact VExpr.instAll_liftN _ _ _
    rw [VExpr.instAll_mkApp, VExpr.instAll_const, List.map_append, List.map_map,
      VExpr.map_instAll_bvars' hιs, hname]
    simp [Function.comp_def, hcancel]
  have hArgs : env.HasArgs U Γ
      (VExpr.instAllTele (T.indices.map (VExpr.instL us)) ps
        ++ [(VExpr.const T.name us).mkApp
              (ps.map (·.liftN T.indices.length) ++ bvars 0 T.indices.length)])
      (ιs ++ [e]) := VEnv.HasArgs.concat hιsA (by rw [hctorInst]; exact he)
  have hbeta := VEnv.IsDefEq.betaMkLams hord (as := ιs ++ [e])
    (by simp only [List.reverse_append, List.reverse_cons, List.reverse_nil,
          List.nil_append, List.cons_append]
        exact ⟨hOnΔ1, hctorTyIT⟩)
    hArgs
    (by simp only [List.reverse_append, List.reverse_cons, List.reverse_nil,
          List.nil_append, List.cons_append]
        exact hbodyT)
  rw [VExpr.mkLams_append, VExpr.instAll_sort,
    D.projMotiveBodyG_instAll T C us H hTj hctors hi (x := e) hps hιs] at hbeta
  rw [projMotiveTermG] at hcore
  exact VEnv.IsDefEq.defeqDF hbeta hcore

/-- **The ι law at field `k`, at an arbitrary block member.**

`projMinor_hasType`'s `hiota` (`Verify/Typing/Lemmas.lean`), generalised: the `k`-th
generalised projection of the constructor applied to its own field variables *is* the `k`-th
field variable.  This is where the recursion lives — the ι rule's `hspine` is the whole
recursor telescope, whose minor block needs the real minor at field `k`, i.e. `hrealk`. -/
theorem projGen_iota_step (henv : VEnv.WF env) (hI : D.IotaCtx env) (H : D.ProjClosedG)
    (hTj : D.types[j]? = some T) (hctors : T.ctors = [C]) (hname : T.name = S)
    (hrec : C.recFields = [])
    {q : Nat} (hqC : D.ctorsAll[q]? = some (j, C)) (hdefeq : env.defeqs (D.iotaRule j q C))
    (h3 : us.length = D.uvars) (h7 : ∀ l ∈ us, l.WF U)
    {k : Nat} (hk : k < C.fields.length)
    (hlvk : (C.fields.getD k default).lvl.inst us ≈ D.elimLvl.inst (D.projLvls C us k))
    (hIH : ∀ m, m < k → C.FieldUsed D 0 m → ProjHasTypeG env U S D T C us j m)
    (hrealk : ProjRealMinorG env U S D T C us j k)
    {Γ ps : List VExpr} (hps : ps.length = D.np)
    (hpsA : env.HasArgs U Γ (D.params.map (VExpr.instL us)) ps)
    (hOnΔF : OnCtx
      ((VExpr.instAllTele (C.fields.map fun F => F.type.instL us) ps).reverse ++ Γ)
      (env.IsType U)) :
    env.IsDefEqU U
      ((VExpr.instAllTele (C.fields.map fun F => F.type.instL us) ps).reverse ++ Γ)
      (D.projTermG T C us (ps.map (·.liftN C.fields.length))
        (C.args.map fun a => VExpr.instAll (a.instL us) ps C.fields.length) k j
        ((VExpr.const C.name us).mkApp
          (ps.map (·.liftN C.fields.length) ++ bvars 0 C.fields.length)))
      (.bvar (C.fields.length - 1 - k)) := by
  have hord := henv.ordered
  have hC : C ∈ T.ctors := by rw [hctors]; exact List.mem_singleton_self _
  have hCall : (j, C) ∈ D.ctorsAll := List.mem_of_getElem? hqC
  have hCwf : VIndCtor.WF env D j T C := hI.toRecCtx.ctors j T hTj C hC
  have hqsl : (ps.map (·.liftN C.fields.length)).length = D.np := by simp [hps]
  have hargsl : (C.args.map fun a =>
      VExpr.instAll (a.instL us) ps C.fields.length).length = T.indices.length := by
    simp [hCwf.args_len]
  have hWF : Ctx.LiftN C.fields.length 0 Γ
      ((VExpr.instAllTele (C.fields.map fun F => F.type.instL us) ps).reverse ++ Γ) :=
    Ctx.LiftN.zero _ (by simp)
  have hqsA := VEnv.HasArgs.weakN hord hWF hpsA
  rw [VExpr.liftTele_eq_self (VExpr.ClosedTele.map_instL H.params) (Nat.zero_le _)] at hqsA
  have hclI : VExpr.ClosedTele (T.indices.map (VExpr.instL us)) ps.length := by
    rw [hps]; exact VExpr.ClosedTele.map_instL (H.indices j T hTj)
  have hfeq : (C.fields.map fun F => F.type.instL us)
      = (C.fields.map (·.type)).map (VExpr.instL us) := by
    simp [List.map_map, Function.comp_def]
  have hclF : VExpr.ClosedTele (C.fields.map fun F => F.type.instL us) ps.length := by
    rw [hps, hfeq]; exact VExpr.ClosedTele.map_instL (H.fields j T hTj C hC)
  have hargsA := ctorArgs_hasArgs_gen hord hI h7 hTj hC hpsA
  rw [VExpr.liftTele_instAllTele₀ hclI] at hargsA
  have hctorT := ctorApp_hasType_gen hord hI h3 h7 hTj hC hCall hps hpsA
  have hfieldsA : env.HasArgs U
      ((VExpr.instAllTele (C.fields.map fun F => F.type.instL us) ps).reverse ++ Γ)
      (VExpr.instAllTele (C.fields.map fun F => F.type.instL us)
        (ps.map (·.liftN C.fields.length))) (bvars 0 C.fields.length) := by
    have h := VEnv.HasArgs.bvars (env := env) (U := U) (Δ := [])
      (As := VExpr.instAllTele (C.fields.map fun F => F.type.instL us) ps) (Γ₀ := Γ)
    rw [List.length_nil, VExpr.length_instAllTele, List.length_map, Nat.zero_add,
      VExpr.liftTele_instAllTele₀ hclF, List.nil_append] at h
    exact h
  have hOnMk : OnCtx ((VExpr.instAllTele (C.fields.map fun F => F.type.instL us)
        (ps.map (·.liftN C.fields.length))).reverse
      ++ ((VExpr.instAllTele (C.fields.map fun F => F.type.instL us) ps).reverse ++ Γ))
      (env.IsType U) := by
    have h := VEnv.OnCtx.weakTele hord hWF hOnΔF
      (As := VExpr.instAllTele (C.fields.map fun F => F.type.instL us) ps) hOnΔF
    rwa [VExpr.liftTele_instAllTele₀ hclF] at h
  have hctorTS : env.HasType U
      ((VExpr.instAllTele (C.fields.map fun F => F.type.instL us) ps).reverse ++ Γ)
      ((VExpr.const C.name us).mkApp
        (ps.map (·.liftN C.fields.length) ++ bvars 0 C.fields.length))
      ((VExpr.const S us).mkApp ((ps.map (·.liftN C.fields.length))
        ++ C.args.map fun a => VExpr.instAll (a.instL us) ps C.fields.length)) := by
    rw [← hname]; exact hctorT
  -- the recursor's motive and minor blocks, at field index `k`
  have hX := projMotiveG_app_hasType henv hI H hTj hC hname h3 h7 hk hlvk hIH
    hOnΔF hqsl hargsl hqsA hargsA hctorTS
  have hmotA := padMotives_hasArgs henv hI H hTj hC hname h3 h7 hk hlvk hIH
    hOnΔF hqsl hargsl hqsA hargsA hctorTS
  have hqlt : q < D.nmin := (List.getElem?_eq_some_iff.1 hqC).1
  have hblock := padMinors_hasArgs (C := C) (i := k) hord hI H h7 h3 hOnΔF hqsl
    (D.length_padMotives ..)
    (hmotsNe := by
      intro t T'' htlt htj hT''
      rw [D.padMotives_getElem_ne T C us _ _ k j _ _ htlt htj,
        show D.types.getD t default = T'' from by rw [List.getD_eq_getElem?_getD, hT'']; rfl])
    hqsA
    (hX := by rw [VIndType.projMotiveG_eq' D T C us hargsl] at hX ⊢; exact hX)
    hmotA (hrealk hOnΔF hctorTS hqsl hargsl hqsA hargsA)
  have hspine := iotaCtx_hasArgs (C := C) (i := k) (C' := C) h3
    (D.length_padMotives ..) (D.length_padMinors ..) hblock hfieldsA
  have hself : D.selfLvls.map (VLevel.inst (D.projLvls C us k)) = us := by
    rw [VInductDecl'.projLvls]; exact D.selfLvls_inst _ h3
  have hiota0 := iota_law_gen_norec hord hI hTj hC hqC hdefeq hself hrec hOnΔF hqsl
    (D.length_padMotives ..) (D.length_padMinors ..) (by simp)
    (minor := C.projMinor us (ps.map (·.liftN C.fields.length)) k)
    (hminor := by
      rw [D.padMinors_getElem_eq (C := C) (D.projLvls C us k) _ _ _ k j q hqC,
        D.realMinor_norec (us := us) hrec (D.length_padMotives ..)
          (by rw [List.length_take, D.length_padMinors]; omega) hself])
    (VInductDecl'.projLvls_wf h7 k) (VInductDecl'.projLvls_length (C := C) h3 k) hspine
  have hargsEqk : (C.args.map fun a => VExpr.instAll
        (VExpr.instAll (a.instL us) (ps.map (·.liftN C.fields.length)) C.fields.length)
        (bvars 0 C.fields.length))
      = C.args.map fun a => VExpr.instAll (a.instL us) ps C.fields.length := by
    refine List.map_congr_left fun a ha => ?_
    have hsp := VExpr.instAll_append (as := ps.map (·.liftN C.fields.length))
      (bs := bvars 0 C.fields.length) (e := a.instL us) (k := 0)
    rw [VExpr.length_bvars, Nat.zero_add] at hsp
    rw [← hsp]
    exact VExpr.instAll_map_liftN_bvars
      (by simpa [hps, Nat.add_comm] using (args_closedN_gen hord hI hTj hC a ha).instL)
  rw [hargsEqk] at hiota0
  have hbvark := Lookup.tele_getElem
    (As := VExpr.instAllTele (C.fields.map fun F => F.type.instL us)
      (ps.map (·.liftN C.fields.length)))
    (Γ := (VExpr.instAllTele (C.fields.map fun F => F.type.instL us) ps).reverse ++ Γ)
    (i := k) (by simp [hk])
  rw [VExpr.length_instAllTele, List.length_map] at hbvark
  have hminapp := projMinor_app hord (C := C) (us := us)
    (ps := ps.map (·.liftN C.fields.length)) (k := k) hk (by simp) hOnMk hfieldsA
    (VEnv.HasType.bvar hbvark)
  rw [bvars_getD hk, Nat.zero_add] at hminapp
  simp only [VInductDecl'.projTermG, VInductDecl'.projCoreG]
  exact VEnv.IsDefEqU.trans henv hOnΔF ⟨_, hiota0⟩ ⟨_, hminapp⟩

/-- **The minor block as a spine, with the real entry discharged.**

`padMinors_hasArgs_take` (`ProjGenBlock.lean`) takes the real minor's typing as the premise
`hreal`; this is the same induction with that premise *replaced by its ingredients* — the
ι-law/swap/β defeq `hiota`, which does not depend on the minor slot `q`.  That independence is
what breaks the apparent circle: the block spine at `take q` is what types the entry at slot
`q`, and the entry at the projected slot needs only `hiota` on top of that spine.

`hctors` is what makes the projected slot's constructor *be* `C`; `hrec` is what makes its
minor telescope the field telescope. -/
theorem padMinors_hasArgs_take_of_hiota (henv : env.Ordered) (hI : D.IotaCtx env)
    (H : D.ProjClosedG) (hTj : D.types[j]? = some T) (hctors : T.ctors = [C])
    (h7 : ∀ l ∈ us, l.WF U) (hus : us.length = D.uvars)
    {i : Nat} (hi : i < C.fields.length) (hjlt : j < D.nm)
    {Γ ps ιs earlier : List VExpr} {e : VExpr} {ℓ : VLevel}
    (hΓ : OnCtx Γ (env.IsType U)) (hps : ps.length = D.np)
    (hpsA : env.HasArgs U Γ (D.params.map (VExpr.instL us)) ps)
    (hX : env.HasType U Γ ((T.projMotive C us ps ιs i earlier).mkApp (ιs ++ [e]))
      (.sort (D.elimLvl.inst (D.projLvls C us i))))
    (hmotA : env.HasArgs U Γ
      ((D.atRecTele D.params).map (VExpr.instL (D.projLvls C us i))
        ++ D.motives.map (VExpr.instL (D.projLvls C us i)))
      (ps ++ D.padMotives T C us ps ιs i j earlier e))
    (hiota : env.IsDefEq U
      ((VExpr.instAllTele (C.fields.map fun F => F.type.instL us) ps).reverse ++ Γ)
      (VExpr.instAll ((C.fields.getD i default).type.instL us)
        (ps.map (·.liftN C.fields.length)
          ++ (List.range i).map fun m => VExpr.bvar (C.fields.length - 1 - m)))
      (((T.projMotive C us ps ιs i earlier).liftN C.fields.length).mkApp
        ((C.args.map fun a => VExpr.instAll (a.instL us) ps C.fields.length)
          ++ [(VExpr.const C.name us).mkApp
                (ps.map (·.liftN C.fields.length) ++ bvars 0 C.fields.length)]))
      (.sort ℓ)) :
    ∀ q, q ≤ D.nmin →
      env.HasArgs U Γ
        ((D.atRecTele D.params).map (VExpr.instL (D.projLvls C us i))
          ++ D.motives.map (VExpr.instL (D.projLvls C us i))
          ++ (D.minors.take q).map (VExpr.instL (D.projLvls C us i)))
        (ps ++ D.padMotives T C us ps ιs i j earlier e
          ++ (D.padMinors (D.projLvls C us i) ps (D.padMotives T C us ps ιs i j earlier e)
              ((T.projMotive C us ps ιs i earlier).mkApp (ιs ++ [e])) i j).take q)
  | 0, _ => by simpa using hmotA
  | q+1, hq => by
    have hC : C ∈ T.ctors := by rw [hctors]; exact List.mem_singleton_self _
    have hself : D.selfLvls.map (VLevel.inst (D.projLvls C us i)) = us := by
      rw [VInductDecl'.projLvls]; exact D.selfLvls_inst _ hus
    have hmotsNe : ∀ t T'', t < D.nm → t ≠ j → D.types[t]? = some T'' →
        (D.padMotives T C us ps ιs i j earlier e)[t]?
          = some (D.padMotive T'' us ps
              ((T.projMotive C us ps ιs i earlier).mkApp (ιs ++ [e]))) := by
      intro t T'' htlt htj hT''
      rw [D.padMotives_getElem_ne T C us ps ιs i j earlier e htlt htj,
        show D.types.getD t default = T'' from by rw [List.getD_eq_getElem?_getD, hT'']; rfl]
    have hIHq := padMinors_hasArgs_take_of_hiota henv hI H hTj hctors h7 hus hi hjlt
      hΓ hps hpsA hX hmotA hiota q (by omega)
    have hqlt : q < D.nmin := by omega
    obtain ⟨⟨t, C'⟩, hqC⟩ : ∃ tC, D.ctorsAll[q]? = some tC :=
      ⟨_, List.getElem?_eq_getElem hqlt⟩
    obtain ⟨T'', hT'', hC'⟩ := VInductDecl'.mem_ctorsAll (List.mem_of_getElem? hqC)
    have htlt : t < D.nm := (List.getElem?_eq_some_iff.1 hT'').1
    have hblen : (D.padMinors (D.projLvls C us i) ps (D.padMotives T C us ps ιs i j earlier e)
        ((T.projMotive C us ps ιs i earlier).mkApp (ιs ++ [e])) i j).length = D.nmin :=
      D.length_padMinors ..
    have hacc : ((D.padMinors (D.projLvls C us i) ps
        (D.padMotives T C us ps ιs i j earlier e)
        ((T.projMotive C us ps ιs i earlier).mkApp (ιs ++ [e])) i j).take q).length = q := by
      rw [List.length_take, hblen]; omega
    have htake : (D.padMinors (D.projLvls C us i) ps
          (D.padMotives T C us ps ιs i j earlier e)
          ((T.projMotive C us ps ιs i earlier).mkApp (ιs ++ [e])) i j).take (q+1)
        = (D.padMinors (D.projLvls C us i) ps (D.padMotives T C us ps ιs i j earlier e)
            ((T.projMotive C us ps ιs i earlier).mkApp (ιs ++ [e])) i j).take q
          ++ [(D.padMinors (D.projLvls C us i) ps
              (D.padMotives T C us ps ιs i j earlier e)
              ((T.projMotive C us ps ιs i earlier).mkApp (ιs ++ [e])) i j).getD q default] := by
      have hlt : q < (D.padMinors (D.projLvls C us i) ps
          (D.padMotives T C us ps ιs i j earlier e)
          ((T.projMotive C us ps ιs i earlier).mkApp (ιs ++ [e])) i j).length := by
        rw [hblen]; omega
      rw [List.take_add_one, List.getElem?_eq_getElem hlt]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
    have hminA : (D.minors.getD q default) = D.minorType q t C' := by
      rw [List.getD_eq_getElem?_getD, D.minors_getElem? q, hqC]; rfl
    have hdecl := minor_declType_isType_gen (C := C) (i := i) henv hI h7 hT'' htlt hC'
      (List.mem_of_getElem? hqC) (by omega) hIHq
    have hentry : env.HasType U Γ
        ((D.padMinors (D.projLvls C us i) ps (D.padMotives T C us ps ιs i j earlier e)
          ((T.projMotive C us ps ιs i earlier).mkApp (ιs ++ [e])) i j).getD q default)
        (VExpr.instAll ((D.minorType q t C').instL (D.projLvls C us i))
          (ps ++ D.padMotives T C us ps ιs i j earlier e
            ++ (D.padMinors (D.projLvls C us i) ps
                (D.padMotives T C us ps ιs i j earlier e)
                ((T.projMotive C us ps ιs i earlier).mkApp (ιs ++ [e])) i j).take q)) := by
      by_cases htj : t = j
      · subst htj
        have hTT : T'' = T := Option.some_inj.1 (hT''.symm.trans hTj)
        subst hTT
        have hCC : C' = C := by rw [hctors] at hC'; simpa using hC'
        rw [hCC, List.getD_eq_getElem?_getD,
          D.padMinors_getElem_eq (D.projLvls C us i) ps _ _ i t q (hCC ▸ hqC),
          Option.getD_some]
        exact D.realMinor_hasType_atPadMotives henv H hTj hC hus hps hacc hjlt hi hΓ
          (hCC ▸ hdecl) hiota
      · rw [List.getD_eq_getElem?_getD,
          D.padMinors_getElem_ne (D.projLvls C us i) ps _ _ i j q t C' hqC htj,
          Option.getD_some]
        exact padMinor_hasType_gen' (C := C) (i := i) henv hI H h7 hus hT'' htlt hC'
          (List.mem_of_getElem? hqC) hself (hmotsNe t T'' htlt htj hT'') hps
          (D.length_padMotives ..) hacc hΓ hdecl hX hpsA
    have hcat := VEnv.HasArgs.concat hIHq
      (A := (D.minorType q t C').instL (D.projLvls C us i)) (by simpa using hentry)
    have hmintake : D.minors.take (q+1) = D.minors.take q ++ [D.minorType q t C'] := by
      have hlt : q < D.minors.length := by rw [VInductDecl'.length_minors]; omega
      rw [List.take_add_one, List.getElem?_eq_getElem hlt]
      simp only [Option.toList_some, ← hminA, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hlt, Option.getD_some]
    rw [hmintake, List.map_append, htake]
    simpa [List.append_assoc] using hcat

/-- `(j, C) ∈ D.ctorsAll` from the two facts `IsStructureG` carries. -/
theorem VInductDecl'.mem_ctorsAll_gen (D : VInductDecl') {j : Nat} {T : VIndType}
    {C : VIndCtor} (hTj : D.types[j]? = some T) (hC : C ∈ T.ctors) :
    (j, C) ∈ D.ctorsAll :=
  List.mem_flatMap.2 ⟨(T, j), List.mk_mem_zipIdx_iff_getElem?.2 hTj,
    List.mem_map.2 ⟨C, hC, rfl⟩⟩

/-- **Wall 2, as a single strong induction on the field index.**

The motive is the *conjunction* of `ProjHasTypeG` and `ProjRealMinorG` at the same index —
`docs/vacuity-ledger.md` row 114c — because the two are entangled: the real minor at field `i`
needs the ι law at every earlier field, the ι law at field `k` needs the whole recursor spine
there, and that spine's projected slot is the real minor at `k`.  Splitting the induction into
"prove the ι law, then the block" circles; carrying both together does not. -/
theorem projTermG_hasType_aux (henv : VEnv.WF env) (hI : D.IotaCtx env) (H : D.ProjClosedG)
    (hTj : D.types[j]? = some T) (hctors : T.ctors = [C]) (hname : T.name = S)
    (hrec : C.recFields = [])
    {q : Nat} (hqC : D.ctorsAll[q]? = some (j, C)) (hdefeq : env.defeqs (D.iotaRule j q C))
    (h3 : us.length = D.uvars) (h7 : ∀ l ∈ us, l.WF U) :
    ∀ i, i < C.fields.length →
      (∀ k, k ≤ i → (k = i ∨ C.FieldUsed D 0 k) → (C.fields.getD k default).lvl.inst us
          ≈ D.elimLvl.inst (D.projLvls C us k)) →
      ProjHasTypeG env U S D T C us j i ∧ ProjRealMinorG env U S D T C us j i := by
  have hord := henv.ordered
  have hC : C ∈ T.ctors := by rw [hctors]; exact List.mem_singleton_self _
  have hCall : (j, C) ∈ D.ctorsAll := D.mem_ctorsAll_gen hTj hC
  have hjlt : j < D.nm := (List.getElem?_eq_some_iff.1 hTj).1
  have hself : ∀ i, D.selfLvls.map (VLevel.inst (D.projLvls C us i)) = us := fun i => by
    rw [VInductDecl'.projLvls]; exact D.selfLvls_inst _ h3
  intro i
  induction i using Nat.strongRecOn with
  | _ i IH =>
  intro hi hlv
  have hmono : ∀ k, k < i → C.FieldUsed D 0 k → ∀ m, m ≤ k → (m = k ∨ C.FieldUsed D 0 m) →
      (C.fields.getD m default).lvl.inst us ≈ D.elimLvl.inst (D.projLvls C us m) :=
    fun k hk hu m hm hg => hlv m (by omega) (by
      rcases hg with rfl | hg
      · exact .inr hu
      · exact .inr hg)
  have hIH : ∀ k, k < i → C.FieldUsed D 0 k → ProjHasTypeG env U S D T C us j k :=
    fun k hk hu => (IH k hk (by omega) (hmono k hk hu)).1
  have hrealIH : ∀ k, k < i → C.FieldUsed D 0 k → ProjRealMinorG env U S D T C us j k :=
    fun k hk hu => (IH k hk (by omega) (hmono k hk hu)).2
  have hlvi := hlv i (Nat.le_refl _) (.inl rfl)
  have hreal : ProjRealMinorG env U S D T C us j i := by
    intro Γ ps ιs e hΓ he hps hιs hpsA hιsA q' C'' hq'
    have hX := projMotiveG_app_hasType henv hI H hTj hC hname h3 h7 hi hlvi hIH
      hΓ hps hιs hpsA hιsA he
    have hmotA := padMotives_hasArgs henv hI H hTj hC hname h3 h7 hi hlvi hIH
      hΓ hps hιs hpsA hιsA he
    -- the field telescope's context, from the motive block alone (slot `0`, empty accumulator)
    have hdecl0 := minor_declType_isType_gen (C := C) (i := i) (acc := []) hord hI h7 hTj
      hjlt hC hCall (Nat.zero_le _) (by simpa using hmotA)
    have hsplit : VExpr.instAll ((D.minorType 0 j C).instL (D.projLvls C us i))
          (ps ++ D.padMotives T C us ps ιs i j
            (D.projArgsG T C us (ps.map (·.liftN (ιs.length+1)))
              (bvars 1 ιs.length) j i) e ++ [])
        = VExpr.mkPi
            (VExpr.instAllTele ((D.minorBinders 0 C).map (VExpr.instL (D.projLvls C us i)))
              (ps ++ D.padMotives T C us ps ιs i j
                (D.projArgsG T C us (ps.map (·.liftN (ιs.length+1)))
                  (bvars 1 ιs.length) j i) e ++ []))
            (VExpr.instAll ((D.minorBody 0 j C).instL (D.projLvls C us i))
              (ps ++ D.padMotives T C us ps ιs i j
                (D.projArgsG T C us (ps.map (·.liftN (ιs.length+1)))
                  (bvars 1 ιs.length) j i) e ++ [])
              ((D.minorBinders 0 C).map (VExpr.instL (D.projLvls C us i))).length) := by
      rw [D.minorType_eq_mkPi 0 j C, VExpr.instL_mkPi, VExpr.instAll_mkPi, Nat.zero_add]
    rw [hsplit, D.minorTele_norec (us := us) (acc := []) (q := 0) hrec
      (D.length_padMotives ..) List.length_nil (hself i)] at hdecl0
    obtain ⟨hOnΔF, -⟩ := VEnv.IsType.mkPi_inv hord hΓ hdecl0
    -- the ι law at every earlier field
    have hiotaK : ∀ k, k < i → C.FieldUsed D 0 k → env.IsDefEqU U
        ((VExpr.instAllTele (C.fields.map fun F => F.type.instL us) ps).reverse ++ Γ)
        (D.projTermG T C us (ps.map (·.liftN C.fields.length))
          (C.args.map fun a => VExpr.instAll (a.instL us) ps C.fields.length) k j
          ((VExpr.const C.name us).mkApp
            (ps.map (·.liftN C.fields.length) ++ bvars 0 C.fields.length)))
        (.bvar (C.fields.length - 1 - k)) :=
      fun k hk hu => projGen_iota_step henv hI H hTj hctors hname hrec hqC hdefeq h3 h7
        (by omega) (hlv k (by omega) (.inr hu)) (fun m hm hmu => hIH m (by omega) hmu)
        (hrealIH k hk hu) hps hpsA hOnΔF
    have hiota := projGen_hiota henv hI H hTj hctors hname hCall h3 h7 hi hlv hIH
      hps hpsA hOnΔF hiotaK
    have hiota' : env.IsDefEq U
        ((VExpr.instAllTele (C.fields.map fun F => F.type.instL us) ps).reverse ++ Γ)
        (VExpr.instAll ((C.fields.getD i default).type.instL us)
          (ps.map (·.liftN C.fields.length)
            ++ (List.range i).map fun m => VExpr.bvar (C.fields.length - 1 - m)))
        (((T.projMotive C us ps ιs i
            (D.projArgsG T C us (ps.map (·.liftN (ιs.length+1)))
              (bvars 1 ιs.length) j i)).liftN C.fields.length).mkApp
          ((C.args.map fun a => VExpr.instAll (a.instL us) ps C.fields.length)
            ++ [(VExpr.const C.name us).mkApp
                  (ps.map (·.liftN C.fields.length) ++ bvars 0 C.fields.length)]))
        (.sort (D.elimLvl.inst (D.projLvls C us i))) := by
      rw [VIndType.projMotiveG_eq' D T C us hιs]; exact hiota
    -- the block spine at the slot, then the entry
    have hq'lt : q' < D.nmin := (List.getElem?_eq_some_iff.1 hq').1
    obtain ⟨T₀, hT₀, hC₀⟩ := VInductDecl'.mem_ctorsAll (List.mem_of_getElem? hq')
    have hTT : T₀ = T := Option.some_inj.1 (hT₀.symm.trans hTj)
    have hCC : C'' = C := by rw [hTT, hctors] at hC₀; simpa using hC₀
    have hspineTake := padMinors_hasArgs_take_of_hiota hord hI H hTj hctors h7 h3 hi hjlt
      hΓ hps hpsA hX hmotA hiota' q' (by omega)
    have hacc : ((D.padMinors (D.projLvls C us i) ps
        (D.padMotives T C us ps ιs i j
          (D.projArgsG T C us (ps.map (·.liftN (ιs.length+1))) (bvars 1 ιs.length) j i) e)
        ((T.projMotive C us ps ιs i
          (D.projArgsG T C us (ps.map (·.liftN (ιs.length+1)))
            (bvars 1 ιs.length) j i)).mkApp (ιs ++ [e])) i j).take q').length = q' := by
      rw [List.length_take, D.length_padMinors]; omega
    rw [hCC]
    exact D.realMinor_hasType_atPadMotives hord H hTj hC h3 hps hacc hjlt hi hΓ
      (minor_declType_isType_gen (C := C) (i := i) hord hI h7 hTj hjlt hC hCall
        (by omega) hspineTake) hiota'
  exact ⟨projTermG_hasType_of_hreal henv hI H hTj hctors hname h3 h7 hi hlvi hIH hreal,
    hreal⟩

/-- **Wall 2.**  `projTerm_hasType` (`Verify/Typing/Lemmas.lean`) at an arbitrary member of an
arbitrary block: `VEnv.IsStructure` is replaced by `VEnv.IsStructureG`, so the `types = [T]`
field is gone and a block index `j` appears.  `C.recFields = []` is carried as an explicit
premise — exactly as `EtaStructSpineG` (`Verify/TypeChecker/EtaStructG.lean`) already carries
it, `IsStructureG` having dropped it. -/
theorem VEnv.IsStructureG.projTermG_hasType (henv : VEnv.WF env)
    (Hs : env.IsStructureG S D j T C) (hrec : C.recFields = [])
    (h3 : us.length = D.uvars) (h7 : ∀ l ∈ us, l.WF U) :
    ∀ i, i < C.fields.length →
      (∀ k, k ≤ i → (k = i ∨ C.FieldUsed D 0 k) → (C.fields.getD k default).lvl.inst us
          ≈ D.elimLvl.inst (D.projLvls C us k)) →
      ProjHasTypeG env U S D T C us j i := by
  have hI := Hs.iotaCtx henv.ordered
  have hC : C ∈ T.ctors := by rw [Hs.ctors]; exact List.mem_singleton_self _
  obtain ⟨q, hqC⟩ := List.mem_iff_getElem?.1 (D.mem_ctorsAll_gen Hs.types hC)
  intro i hi hlv
  exact (projTermG_hasType_aux henv hI (Hs.projClosedG henv.ordered) Hs.types Hs.ctors
    Hs.name hrec hqC (Hs.iotaDefeq hqC) h3 h7 i hi hlv).1

/-- **Collapse test: the narrow `projTerm_hasType` is this lemma at a narrow block.**

Hypothesis for hypothesis `projTerm_hasType`'s statement (`Verify/Typing/Lemmas.lean`),
derived from the general one at `j = 0` through `projHasTypeG_eq`.  This is what makes the
result a *generalisation* rather than a differently-shaped statement: the narrow lemma's
`VEnv.IsStructure` supplies `types`, `ctors`, `noRec` and `decl`, and `noRec` is exactly the
premise the general form carries explicitly.

Note the narrow lemma takes `henv : VEnv.WF env` and derives `IotaCtx`/`ProjClosed` from `H`;
so does this. -/
theorem projTerm_hasType_of_G (henv : VEnv.WF env) (H : env.IsStructure S D T C)
    (h3 : us.length = D.uvars) (h7 : ∀ l ∈ us, l.WF U) :
    ∀ i, i < C.fields.length →
      (∀ k, k ≤ i → (k = i ∨ C.FieldUsed D 0 k) → (C.fields.getD k default).lvl.inst us
          ≈ D.elimLvl.inst (D.projLvls C us k)) →
      ProjHasType env U S D T C us i := by
  intro i hi hlv
  rw [← projHasTypeG_eq env U S D T C us i H.types H.ctors H.noRec h3]
  exact H.toG.projTermG_hasType henv H.noRec h3 h7 i hi hlv

end Lean4Lean
