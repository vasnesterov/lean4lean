import Lean4Lean.Theory.Inductive.Lemmas
import Lean4Lean.Theory.Inductive.Structure

/-!
# `VInductDecl'.ProjClosed` is a theorem, not a hypothesis

`TrProj.weak'`/`.instN`/`.weak'_inv` need the structure's stored telescopes closed at their
declared arities (`VInductDecl'.ProjClosed`).  This file derives that from
`VEnv.IsStructure` together with `VEnv.Ordered env`, which those lemmas already have — so
nothing is assumed.

## Why this is a separate file

The derivation needs `Theory/Inductive/Lemmas.lean` (`addInduct'_le`, `addInduct'_constants`,
`Ordered.closedC`), which is large and belongs to the inductive-keystone workstream.
`Structure.lean` deliberately imports only `Decl.lean` so that the definition of `TrProj`
and its `instL` theory do not depend on a file under active development; only this bridge
does.

## The two halves

*Field types* come from the **constructor constant**: `addInduct'_constants` puts
`⟨D.uvars, C.type D j⟩` into the environment, `Ordered.closedC` says a constant's type is
closed, and `closedN_mkPi` peels the binder telescope.  This needs `Ordered` only for the
*final* environment.

*Index telescopes* have no such constant to read off — `T.type` is only **definitionally**
`mkPi (params ++ indices) (sort lvl)` (F1), so `ClosedN T.type 0` says nothing about the
decomposition.  They come instead from `VIndType.WF.indices`, a judgement in the *earlier*
environment `env₀`, where `Ordered` is not available.  The step that makes this work is
that `VEnv.OnTypes` is **antitone** (`OnTypes.mono`): closedness of every constant's type
in `env` restricts to `env₀ ≤ env`.  Hence the `₀`-suffixed variants below, which are
`Inductive/Lemmas.lean`'s `OnCtx.ctxClosed` / `ClosedTele.of_onCtx` with `Ordered env`
weakened to the `OnTypes` fact they actually consume.
-/

namespace Lean4Lean

open VExpr VEnv

variable {env : VEnv} {U : Nat}

/-- `OnCtx.ctxClosed` with `Ordered env` weakened to the `OnTypes` fact it consumes. -/
theorem OnCtx.ctxClosed₀ (hc : OnTypes env fun _ e A => e.ClosedN ∧ A.ClosedN) :
    ∀ {Γ}, OnCtx Γ (env.IsType U) → CtxClosed Γ
  | [], _ => trivial
  | _ :: _, ⟨h1, h2⟩ =>
    ⟨h1.ctxClosed₀ hc, (h2.choose_spec.closedN' hc (h1.ctxClosed₀ hc)).1⟩

/-- `VExpr.ClosedTele.of_onCtx` with the same weakening. -/
theorem VExpr.ClosedTele.of_onCtx₀ (hc : OnTypes env fun _ e A => e.ClosedN ∧ A.ClosedN) :
    ∀ {As Γ : List VExpr}, OnCtx (As.reverse ++ Γ) (env.IsType U) →
      VExpr.ClosedTele As Γ.length
  | [], _, _ => trivial
  | A :: As, Γ, h => by
    rw [VExpr.tele_ctx_cons] at h
    have hΓ : OnCtx (A :: Γ) (env.IsType U) := OnCtx.append_right h
    refine ⟨(hΓ.2.choose_spec.closedN' hc (hΓ.1.ctxClosed₀ hc)).1, ?_⟩
    simpa using VExpr.ClosedTele.of_onCtx₀ (As := As) (Γ := A :: Γ) hc h

/-- `addInduct'` runs `addIndTypes` first, so its success is available. -/
theorem VInductDecl'.addIndTypes_of_addInduct' {D : VInductDecl'} {env env' : VEnv}
    (h : env.addInduct' D = some env') : ∃ env₁, env.addIndTypes D = some env₁ := by
  rw [VEnv.addInduct'_eq, Option.map_eq_some_iff] at h
  obtain ⟨e₁, h1, _⟩ := h
  simp only [VInductDecl'.allConsts, VEnv.addConstList_append, Option.bind_eq_some_iff] at h1
  obtain ⟨_, ⟨e₃, h3, _⟩, _⟩ := h1
  exact ⟨e₃, h3⟩

variable {S : Lean.Name} {D : VInductDecl'} {T : VIndType} {C : VIndCtor}

/-- **`ProjClosed` is derivable**: no field on `IsStructure`, no added hypothesis.
`Ordered env` is what `TrProj.weak'`/`.instN`/`.weak'_inv` already carry. -/
theorem VEnv.IsStructure.projClosed (henv : env.Ordered) (H : env.IsStructure S D T C) :
    D.ProjClosed T C := by
  obtain ⟨env₀, env₁, hWF, hadd, hle⟩ := H.decl
  have hle₀ : env₀ ≤ env := (VEnv.addInduct'_le hadd).trans hle
  have hc₀ : OnTypes env₀ (fun _ e A => e.ClosedN ∧ A.ClosedN) :=
    henv.closed.mono hle₀ id
  have hT : T ∈ D.types := by rw [H.types]; exact List.mem_singleton_self _
  refine ⟨?_, ?_, ?_⟩
  · -- parameters: `VInductDecl'.WF.params`, again in `env₀`
    have := VExpr.ClosedTele.of_onCtx₀ (Γ := []) hc₀ (by simpa using hWF.params)
    simpa using this
  · -- indices: from `VIndType.WF.indices`, a judgement in `env₀`
    have := VExpr.ClosedTele.of_onCtx₀ hc₀ (hWF.types T hT).indices
    simpa [VInductDecl'.np] using this
  · -- field types: from the constructor *constant*, which lives in `env`
    obtain ⟨env₁', hadd₁⟩ := VInductDecl'.addIndTypes_of_addInduct' hadd
    have hTj : D.types[0]? = some T := by rw [H.types]; rfl
    have hC : C ∈ T.ctors := by rw [H.ctors]; exact List.mem_singleton_self _
    have hCwf := hWF.ctors env₁' hadd₁ 0 T hTj C hC
    have hmem : (C.name, (⟨D.uvars, C.type D 0⟩ : VConstant)) ∈ D.allConsts := by
      simp [VInductDecl'.allConsts, VInductDecl'.ctorConsts, VInductDecl'.ctorsAll,
        H.types, H.ctors]
    have hconst : env.constants C.name = some ⟨D.uvars, C.type D 0⟩ :=
      hle.constants (VEnv.addInduct'_constants hadd _ hmem)
    have hcl : VExpr.ClosedN (C.type D 0) 0 := henv.closedC hconst
    rw [VIndCtor.type] at hcl
    have := (VExpr.closedTele_append.1 (VExpr.closedN_mkPi.1 hcl).1).2
    simpa [hCwf.params_len, VInductDecl'.np] using this

/-! ## `HasArgs` transport

`Theory/Inductive/Lemmas.lean` has `HasArgs.instL`, `.weakN` and `.mono`; `TrProj`'s
recorded spine premises additionally need the `Ctx.Lift'` and `Ctx.InstN` versions. -/

theorem VEnv.HasArgs.weak' {env : VEnv} {U} {l : Lift} {Γ Γ' : List VExpr}
    (henv : VEnv.Ordered env) (W : Ctx.Lift' l Γ Γ') :
    ∀ {As as}, env.HasArgs U Γ As as →
      env.HasArgs U Γ' (VExpr.liftTele' l As) (as.map (·.lift' l))
  | _, _, .nil => .nil
  | A :: As, a :: as, .cons ha h => by
    refine .cons (ha.weak' henv W) ?_
    have ih := VEnv.HasArgs.weak' henv W h
    have hcomm : VExpr.liftTele' l (VExpr.instTele a As)
        = VExpr.instTele (a.lift' l) (VExpr.liftTele' l.cons As) :=
      VExpr.liftTele'_instTele (As := As) (a := a) (ρ := l) (j := 0)
    rwa [hcomm] at ih

theorem VEnv.HasArgs.instN {env : VEnv} {U k} {Γ₀ Γ₁ Γ : List VExpr} {e₀ A₀ : VExpr}
    (henv : VEnv.Ordered env) (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ)
    (t₀ : env.HasType U Γ₀ e₀ A₀) :
    ∀ {As as}, env.HasArgs U Γ₁ As as →
      env.HasArgs U Γ (VExpr.instTele e₀ As k) (as.map (·.inst e₀ k))
  | _, _, .nil => .nil
  | A :: As, a :: as, .cons ha h => by
    refine .cons (ha.instN henv W t₀) ?_
    have ih := VEnv.HasArgs.instN henv W t₀ h
    have hcomm : VExpr.instTele e₀ (VExpr.instTele a As) k
        = VExpr.instTele (a.inst e₀ k) (VExpr.instTele e₀ As (k+1)) :=
      VExpr.instTele_instTele (As := As) (a := a) (b := e₀) (m := k) (j := 0)
    rwa [hcomm] at ih

/-! ## `IotaCtx` from `IsStructure`

`VInductDecl'.WF.recCtx` takes `(hle : env₂ ≤ env₃) (henv₃ : env₃.Ordered)`, so it produces
`RecCtx` at *any* environment above the staged one — no `Ordered env₀` is needed, and the
recursor constants transport along `≤` from `addInduct'_constants`. -/

theorem VInductDecl'.addInduct'_stages {D : VInductDecl'} {env env' : VEnv}
    (h : env.addInduct' D = some env') :
    ∃ env₁ env₂ env₃, env.addIndTypes D = some env₁ ∧ env₁.addIndCtors D = some env₂ ∧
      env₂.addIndRecs D = some env₃ ∧ env₃.addIndRules D = env' := by
  rw [VEnv.addInduct'_eq, Option.map_eq_some_iff] at h
  obtain ⟨eF, h1, hF⟩ := h
  simp only [VInductDecl'.allConsts, VEnv.addConstList_append, Option.bind_eq_some_iff] at h1
  obtain ⟨e₂, ⟨e₁, ha, hb⟩, hc⟩ := h1
  exact ⟨e₁, e₂, eF, ha, hb, hc, hF⟩

theorem VEnv.IsStructure.iotaCtx (henv : env.Ordered) (H : env.IsStructure S D T C) :
    D.IotaCtx env := by
  obtain ⟨env₀, envF, hWF, hadd, hle⟩ := H.decl
  obtain ⟨env₁, env₂, env₃, h1, h2, h3, hF⟩ := VInductDecl'.addInduct'_stages hadd
  have hle₂ : env₂ ≤ env :=
    ((VEnv.addIndRecs_le h3).trans (hF ▸ VEnv.addIndRules_le)).trans hle
  refine ⟨hWF.recCtx h1 h2 hle₂ henv, fun j T' hT' => ?_⟩
  refine hle.constants (VEnv.addInduct'_constants hadd
    (Lean.mkRecName T'.name, ⟨D.recUvars, D.recType j⟩) ?_)
  simp only [VInductDecl'.allConsts, VInductDecl'.recConsts, List.mem_append, List.mem_map]
  exact .inr ⟨(T', j), List.mk_mem_zipIdx_iff_getElem?.2 hT', rfl⟩

/-! ## `IsDefEq` at a spine

`Theory/Inductive/Lemmas.lean:604` has `HasType.mkApp'`; there is no `IsDefEq` counterpart.
Same small gap as `Telescope.lean` having every `liftN` lemma and no `lift'` one.  This is
what applies an ι-rule, which `IsDefEq.extra` delivers λ-abstracted, to a concrete spine. -/

theorem VEnv.IsDefEq.mkApp' {env : VEnv} {U : Nat} :
    ∀ {As as Γ f g B}, env.HasArgs U Γ As as → env.IsDefEq U Γ f g (VExpr.mkPi As B) →
      env.IsDefEq U Γ (f.mkApp as) (g.mkApp as) (VExpr.instAll B as)
  | _, _, _, _, _, _, .nil, hf => hf
  | A :: As, a :: as, Γ, f, g, B, .cons ha has, hf => by
    have h1 := hf.appDF ha
    rw [VExpr.inst_mkPi_zero] at h1
    have hlen : as.length = As.length := has.length_eq.symm.trans VExpr.length_instTele
    rw [VExpr.mkApp_cons, VExpr.mkApp_cons, VExpr.instAll_cons, Nat.zero_add, hlen]
    exact VEnv.IsDefEq.mkApp' has h1

/-! ## The motive's declared type

`recApp_hasType''`'s `hspine` asks for the motive at `instAll ((D.motiveType 0).instL ls) ps`.
This computes that to the type `HasType.mkLams` produces for `VIndType.projMotive`. -/

theorem motiveType_instL_instAll (D : VInductDecl') (T : VIndType) (C : VIndCtor)
    {us : List VLevel} {ps : List VExpr} {i : Nat}
    (hT : D.types.getD 0 default = T)
    (hus : us.length = D.uvars) (hps : ps.length = D.np) :
    VExpr.instAll ((D.motiveType 0).instL (D.projLvls C us i)) ps
      = VExpr.mkPi (VExpr.instAllTele (T.indices.map (VExpr.instL us)) ps)
          (.forallE ((VExpr.const T.name us).mkApp
              (ps.map (·.liftN T.indices.length) ++ VExpr.bvars 0 T.indices.length))
            (.sort (D.elimLvl.inst (D.projLvls C us i)))) := by
  have hself : D.selfLvls.map (VLevel.inst (D.projLvls C us i)) = us := by
    rw [VInductDecl'.projLvls]; exact D.selfLvls_inst _ hus
  simp only [VInductDecl'.motiveType, hT, VExpr.liftTele_zero, VInductDecl'.atRecTele,
    VExpr.instL_mkPi, VInductDecl'.tyApp', VExpr.instL_mkApp, VExpr.instL,
    VExpr.map_instL_bvars, List.map_append, VExpr.instAll_mkPi, VExpr.instAll_forallE,
    VExpr.instAll_sort, VExpr.instAll_mkApp, VExpr.instAll_const,
    List.map_map, Function.comp_def, VExpr.instL_instL, hself,
    List.length_map, Nat.zero_add, Nat.add_zero]
  rw [VExpr.map_instAll_bvars_top (Nat.le_refl _) (by simp [hps]),
    VExpr.map_instAll_bvars_lt (Nat.le_of_eq (Nat.zero_add _)),
    List.take_of_length_le (by simp [hps])]

/-- A term weakened by one binder, then saturated by a spine whose last argument fills that
binder, is unchanged: the extra argument is discarded. -/
theorem VExpr.instAll_liftN_snoc {X b : VExpr} {as : List VExpr} {k : Nat} :
    VExpr.instAll (VExpr.liftN 1 X k) (as ++ [b]) k = VExpr.instAll X as k := by
  rw [VExpr.instAll_append, show ([b] : List VExpr).length = 1 from rfl,
    VExpr.liftN_instAll (n := 1) (as := as) (X := X) (k := k),
    VExpr.instAll_cons, List.length_nil, Nat.add_zero, VExpr.inst_liftN, VExpr.instAll_nil]

/-- The telescope version.  This is what collapses the minor premise's field telescope,
which `minorType` states over `params ++ motives`. -/
theorem VExpr.instAllTele_liftTele_snoc : ∀ {As as : List VExpr} {b : VExpr} {k : Nat},
    VExpr.instAllTele (VExpr.liftTele 1 As k) (as ++ [b]) k = VExpr.instAllTele As as k
  | [], _, _, _ => rfl
  | A :: As, as, b, k => by
    rw [VExpr.liftTele_cons, VExpr.instAllTele_cons, VExpr.instAllTele_cons,
      VExpr.instAll_liftN_snoc,
      VExpr.instAllTele_liftTele_snoc (As := As) (as := as) (b := b) (k := k+1)]

/-! ## The minor premise's declared type -/

theorem minorType_instL_instAll (D : VInductDecl') (C : VIndCtor)
    {us : List VLevel} {ps : List VExpr} {i : Nat} {mot : VExpr}
    (hnm : D.nm = 1) (hrec : C.recFields = [])
    (hus : us.length = D.uvars) (hps : ps.length = D.np) :
    VExpr.instAll ((D.minorType 0 0 C).instL (D.projLvls C us i)) (ps ++ [mot])
      = mkPi (VExpr.instAllTele (C.fields.map fun F => F.type.instL us) ps)
          ((mot.liftN C.fields.length).mkApp
            (C.args.map (fun a => VExpr.instAll (a.instL us) ps C.fields.length) ++
              [(VExpr.const C.name us).mkApp
                (ps.map (·.liftN C.fields.length) ++ bvars 0 C.fields.length)])) := by
  have hself : D.selfLvls.map (VLevel.inst (D.projLvls C us i)) = us := by
    rw [VInductDecl'.projLvls]; exact D.selfLvls_inst _ hus
  simp only [VInductDecl'.minorType, VInductDecl'.ihTypes, hrec, hnm, VInductDecl'.atRecTele,
    VInductDecl'.atRec, VInductDecl'.ctorApp', List.zipIdx_nil, List.map_nil, List.length_nil,
    List.append_nil, Nat.zero_add, Nat.add_zero, Nat.sub_self,
    VExpr.instL_mkPi, VExpr.instL_liftTele, VExpr.instL_mkApp, VExpr.instL,
    VExpr.map_instL_bvars, List.map_map, Function.comp_def, VExpr.instL_instL, hself,
    VExpr.instAll_mkPi, VExpr.instAll_mkApp, VExpr.length_liftTele, List.length_map,
    List.map_append, VExpr.shift, VExpr.liftN_zero, VExpr.instL_liftN,
    List.map_cons, VExpr.instAllTele_liftTele_snoc, VExpr.instAll_liftN_snoc]
  rw [VExpr.instAll_bvar_get (t := ps.length) (a := mot)
      (by simp [List.getElem?_append_right]) (by simp [hps]; omega),
    VExpr.map_instAll_bvars_top (Nat.le_succ _) (by simp [hps]; omega),
    VExpr.map_instAll_bvars_lt (Nat.le_of_eq (Nat.zero_add _)),
    List.take_left' hps]
  simp only [VExpr.instAll_const]

/-! ## Substituting a whole telescope

`HasType.mkApp'` (`Inductive/Lemmas.lean:604`) applies a function to a spine; its dual —
substituting a spine into a term typed in the spine's own context — is what types
`projMotive`'s body, and does not exist upstream.  Building it needs a `Ctx.InstN` for a
whole telescope, which in turn needs `instTele` restated in context order (`instCtx`),
because `Ctx.InstN` peels the *innermost* binder while `instTele` indexes from the
outermost. -/

namespace VExpr

/-- `instTele` in context order (innermost binder first). -/
def instCtx (a : VExpr) : List VExpr → List VExpr
  | [] => []
  | B :: Δ => B.inst a Δ.length :: instCtx a Δ

@[simp] theorem instCtx_nil : instCtx a [] = [] := rfl
@[simp] theorem instCtx_cons : instCtx a (B :: Δ) = B.inst a Δ.length :: instCtx a Δ := rfl

@[simp] theorem length_instCtx : ∀ {Δ : List VExpr} {a}, (instCtx a Δ).length = Δ.length
  | [], _ => rfl
  | _ :: _, _ => congrArg Nat.succ length_instCtx

theorem instCtx_reverse_append : ∀ {As Δ : List VExpr} {a : VExpr},
    instCtx a (As.reverse ++ Δ) = (instTele a As Δ.length).reverse ++ instCtx a Δ
  | [], _, _ => rfl
  | B :: As, Δ, a => by
    rw [List.reverse_cons, List.append_assoc, List.singleton_append,
      instCtx_reverse_append (As := As) (Δ := B :: Δ), instTele_cons, List.reverse_cons,
      List.append_assoc, instCtx_cons, List.length_cons, List.singleton_append]

theorem instCtx_reverse {As : List VExpr} {a : VExpr} :
    instCtx a As.reverse = (instTele a As).reverse := by
  simpa using instCtx_reverse_append (As := As) (Δ := []) (a := a)


theorem Ctx.instN_ctx (Γ₀ : List VExpr) (a A : VExpr) : ∀ (Δ : List VExpr),
    Ctx.InstN Γ₀ a A Δ.length (Δ ++ A :: Γ₀) (VExpr.instCtx a Δ ++ Γ₀)
  | [] => .zero
  | B :: Δ => (Ctx.instN_ctx Γ₀ a A Δ).succ

theorem Ctx.instN_tele (Γ₀ : List VExpr) (a A : VExpr) (As : List VExpr) :
    Ctx.InstN Γ₀ a A As.length (As.reverse ++ A :: Γ₀) ((VExpr.instTele a As).reverse ++ Γ₀) := by
  have := Ctx.instN_ctx Γ₀ a A As.reverse
  rwa [List.length_reverse, VExpr.instCtx_reverse] at this
end VExpr

/-! ## β-reduction of a saturated `mkLams` -/

/-- **β-reduction of a saturated `mkLams`.**  `instAll` is documented as the β-normal form
of `(mkLams As b).mkApp as`; this is that statement as a judgement. -/
theorem VEnv.IsDefEq.betaMkLams {env : VEnv} {U : Nat} (henv : env.Ordered) :
    ∀ {As as : List VExpr} {Γ : List VExpr} {b B : VExpr},
      OnCtx (As.reverse ++ Γ) (env.IsType U) →
      env.HasArgs U Γ As as → env.HasType U (As.reverse ++ Γ) b B →
      env.IsDefEq U Γ ((mkLams As b).mkApp as) (VExpr.instAll b as) (VExpr.instAll B as)
  | [], [], _, _, _, _, .nil, hb => hb
  | A :: As, a :: as, Γ, b, B, hAs, .cons ha has, hb => by
    have hAs' : OnCtx (As.reverse ++ A :: Γ) (env.IsType U) := by
      rwa [List.reverse_cons, List.append_assoc, List.singleton_append] at hAs
    have hb' : env.HasType U (As.reverse ++ A :: Γ) b B := by
      rwa [List.reverse_cons, List.append_assoc, List.singleton_append] at hb
    have hlam : env.HasType U (A :: Γ) (mkLams As b) (mkPi As B) :=
      VEnv.HasType.mkLams hAs' hb'
    have hbeta : env.IsDefEq U Γ ((VExpr.lam A (mkLams As b)).app a)
        ((mkLams As b).inst a) ((mkPi As B).inst a) := VEnv.IsDefEq.beta hlam ha
    rw [VExpr.inst_mkLams_zero] at hbeta
    have hlen : as.length = As.length := has.length_eq.symm.trans VExpr.length_instTele
    have hstep := VEnv.IsDefEq.mkApp' has (by rwa [VExpr.inst_mkPi_zero] at hbeta)
    have hih := VEnv.IsDefEq.betaMkLams henv (As := VExpr.instTele a As) (as := as)
      (b := b.inst a As.length) (B := B.inst a As.length)
      ((Ctx.instN_tele Γ a A As).wf henv ha hAs').2 has
      (VEnv.HasType.instN henv (Ctx.instN_tele Γ a A As) hb' ha)
    rw [VExpr.mkLams_cons, VExpr.mkApp_cons, VExpr.instAll_cons, VExpr.instAll_cons,
      Nat.zero_add, hlen]
    exact hstep.trans hih

namespace VExpr

/-- **Composing two saturated substitutions.**  If `X` is closed at `|L|`, substituting `L`
and then `M` is substituting `L`'s entries already `M`-substituted. -/
theorem instAll_instAll {X : VExpr} {L : List VExpr} (h : X.ClosedN L.length) :
    ∀ {M : List VExpr}, instAll (instAll X L) M = instAll X (L.map (instAll · M))
  | [] => by simp
  | b :: M => by
    rw [instAll_cons, Nat.zero_add, show M.length = M.length + 0 from rfl,
      inst_instAll (m := M.length) (j := 0) (by simpa using h),
      instAll_instAll (X := X) (L := L.map (·.inst b M.length)) (by simpa using h) (M := M)]
    simp only [List.map_map, Function.comp_def, instAll_cons, Nat.zero_add]

end VExpr

end Lean4Lean
