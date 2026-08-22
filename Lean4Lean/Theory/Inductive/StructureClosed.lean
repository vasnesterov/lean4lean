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

/-! ## Contexts from telescopes -/

/-- A telescope closed at its declared arities gives a closed context when reversed onto a
closed one. -/
theorem VExpr.ClosedTele.ctxClosed : ∀ {As Γ : List VExpr},
    VExpr.ClosedTele As Γ.length → CtxClosed Γ → CtxClosed (As.reverse ++ Γ)
  | [], _, _, hΓ => hΓ
  | A :: As, Γ, h, hΓ => by
    have : CtxClosed (A :: Γ) := ⟨hΓ, h.1⟩
    have := VExpr.ClosedTele.ctxClosed (As := As) (Γ := A :: Γ) (by simpa using h.2) this
    simpa using this

/-- A telescope closed at `0` is fixed by `liftTele`, which is what carries the parameter
block through a weakening. -/
theorem VExpr.liftTele_eq_self : ∀ {As : List VExpr} {n k j : Nat},
    VExpr.ClosedTele As j → j ≤ k → VExpr.liftTele n As k = As
  | [], _, _, _, _, _ => rfl
  | A :: As, n, k, j, h, hk => by
    rw [VExpr.liftTele_cons, h.1.liftN_eq hk,
      VExpr.liftTele_eq_self (As := As) (n := n) (k := k+1) (j := j+1) h.2 (by omega)]

/-- `ClosedTele` restricts to a prefix. -/
theorem VExpr.ClosedTele.take : ∀ {As : List VExpr} {k i : Nat},
    VExpr.ClosedTele As k → VExpr.ClosedTele (As.take i) k
  | [], _, _, _ => by simp [VExpr.ClosedTele]
  | _ :: _, _, 0, _ => by simp [VExpr.ClosedTele]
  | A :: As, k, i+1, h => ⟨h.1, VExpr.ClosedTele.take (As := As) (i := i) h.2⟩

/-! ## The projected field's type is a type

Field `i`'s stored type, moved to the use site's levels and weakened into any context below
the constructor's parameter-and-field-prefix telescope.  This is what `projMotive`'s body is
built from. -/

theorem ftype_hasType {env : VEnv} {U : Nat} {S : Lean.Name}
    {D : VInductDecl'} {T : VIndType} {C : VIndCtor} {us : List VLevel}
    (henv : env.Ordered) (H : env.IsStructure S D T C) (hI : D.IotaCtx env)
    (h3 : us.length = D.uvars) (h7 : ∀ l ∈ us, l.WF U)
    (hcl : D.ProjClosed T C) {i : Nat} (hi : i < C.fields.length) (Γ'' : List VExpr) :
    env.HasType U
      ((D.params.map (VExpr.instL us) ++
        (C.fields.take i).map (fun F => F.type.instL us)).reverse ++ Γ'')
      ((C.fields.getD i default).type.instL us)
      (.sort ((C.fields.getD i default).lvl.inst us)) := by
  have hT0 : D.types[0]? = some T := by rw [H.types]; rfl
  have hC : C ∈ T.ctors := by rw [H.ctors]; exact List.mem_singleton_self _
  have hCwf := hI.toRecCtx.ctors 0 T hT0 C hC
  have hget : C.fields[i]? = some (C.fields.getD i default) := by
    rw [List.getElem?_eq_getElem hi]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  have hf := (hCwf.fields i _ hget).hasType
  have hf2 := VEnv.HasType.instL (ls := us) (U' := U) h7 hf
  -- the context, normalised
  have hctx : ((((C.fields.take i).map (·.type)).reverse ++ D.params.reverse).map
        (VExpr.instL us))
      = (D.params.map (VExpr.instL us) ++
          (C.fields.take i).map (fun F => F.type.instL us)).reverse := by
    simp [List.map_reverse, List.map_map, Function.comp_def]
  rw [hctx] at hf2
  -- closedness of that context
  have hcltele : VExpr.ClosedTele (D.params.map (VExpr.instL us) ++
      (C.fields.take i).map (fun F => F.type.instL us)) 0 := by
    refine VExpr.closedTele_append.2 ⟨VExpr.ClosedTele.map_instL hcl.params, ?_⟩
    have : VExpr.ClosedTele ((C.fields.map (·.type)).take i) D.np :=
      VExpr.ClosedTele.take hcl.fields
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

/-- Build a `HasArgs` over an initial segment of a telescope from pointwise typings, where
each entry's type is stated with the *earlier entries of the spine* already substituted —
which is the form a recursive construction like `projArgs` produces. -/
theorem VEnv.HasArgs.ofMap {env : VEnv} {U : Nat} {Γ : List VExpr}
    {As as : List VExpr} {f : Nat → VExpr} : ∀ {i : Nat}, i ≤ As.length →
      (∀ k, k < i → env.HasType U Γ (f k)
        (VExpr.instAll (As.getD k default) (as ++ (List.range k).map f))) →
      env.HasArgs U Γ (VExpr.instAllTele (As.take i) as) ((List.range i).map f)
  | 0, _, _ => by simp; exact .nil
  | i+1, hi, h => by
    have hlt : i < As.length := by omega
    have htake : As.take (i+1) = As.take i ++ [As.getD i default] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hlt]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
    rw [List.range_succ, List.map_append, htake, VExpr.instAllTele_append]
    refine VEnv.HasArgs.append (VEnv.HasArgs.ofMap (by omega) fun k hk => h k (by omega)) ?_
    have hlen : ((List.range i).map f).length = i := by simp
    simp only [List.length_take, Nat.zero_add, Nat.min_def]
    rw [if_pos (by omega)]
    simp only [VExpr.instAllTele_cons, VExpr.instAllTele_nil, List.map_cons, List.map_nil]
    refine .cons ?_ .nil
    have := h i (by omega)
    rwa [VExpr.instAll_append, hlen, Nat.zero_add] at this

/-! ## The ι-rule, and substituting definitionally equal spines -/





/-- The block's single ι-rule is in the environment. -/
theorem VEnv.IsStructure.iotaDefeq (H : env.IsStructure S D T C) :
    env.defeqs (D.iotaRule 0 0 C) := by
  obtain ⟨env₀, envF, hWF, hadd, hle⟩ := H.decl
  refine hle.defeqs (VEnv.addInduct'_defeqs hadd _ ?_)
  simp [VInductDecl'.iotaRules, VInductDecl'.ctorsAll, H.types, H.ctors]



/-- `HasArgs` with the spine allowed to vary up to definitional equality.  The telescope
is instantiated by the *left* spine, matching `HasArgs`. -/
inductive VEnv.HasArgsDF (env : VEnv) (U : Nat) (Γ : List VExpr) :
    List VExpr → List VExpr → List VExpr → Prop
  | nil : HasArgsDF env U Γ [] [] []
  | cons {A As a a' as as'} :
    env.IsDefEq U Γ a a' A → HasArgsDF env U Γ (VExpr.instTele a As) as as' →
    HasArgsDF env U Γ (A :: As) (a :: as) (a' :: as')

theorem VEnv.HasArgsDF.left {env : VEnv} {U : Nat} {Γ : List VExpr} :
    ∀ {As as as'}, env.HasArgsDF U Γ As as as' → env.HasArgs U Γ As as
  | _, _, _, .nil => .nil
  | _, _, _, .cons ha h => .cons ha.hasType.1 h.left

theorem VEnv.HasArgsDF.length_eq {env : VEnv} {U : Nat} {Γ : List VExpr} :
    ∀ {As as as'}, env.HasArgsDF U Γ As as as' → as.length = as'.length
  | _, _, _, .nil => rfl
  | _, _, _, .cons _ h => congrArg Nat.succ h.length_eq

/-- Spine congruence with the arguments varying too. -/
theorem VEnv.IsDefEq.mkAppDF {env : VEnv} {U : Nat} :
    ∀ {As as as' Γ f g B}, env.HasArgsDF U Γ As as as' →
      env.IsDefEq U Γ f g (VExpr.mkPi As B) →
      env.IsDefEq U Γ (f.mkApp as) (g.mkApp as') (VExpr.instAll B as)
  | _, _, _, _, _, _, _, .nil, hf => hf
  | A :: As, a :: as, a' :: as', Γ, f, g, B, .cons ha has, hf => by
    have h1 := hf.appDF ha
    rw [VExpr.inst_mkPi_zero] at h1
    have hlen : as.length = As.length := has.left.length_eq.symm.trans VExpr.length_instTele
    rw [VExpr.mkApp_cons, VExpr.mkApp_cons, VExpr.instAll_cons, Nat.zero_add, hlen]
    exact VEnv.IsDefEq.mkAppDF has h1



/-- **Substituting definitionally equal spines into a type gives definitionally equal
types.**  Both spines must be `HasArgs`-typed: `HasArgsDF` instantiates the telescope by the
*left* spine, so the right one needs its own chain (in practice `HasArgs.ofMap` supplies it).
Specialised to a sort codomain, and **the specialisation is what makes it provable**: the
general statement would need `instAll B as ≡ instAll B as'` to even state its conclusion —
the same congruence one level up.  With `B = .sort l` both sides are literally `.sort l`,
the circularity dissolves, and the two `betaMkLams` steps have no type drift.

This cuts against the "state the general version first" heuristic that holds elsewhere in
this development (see the settled-rule note in `TelescopeLift.lean`).  It is not a
counterexample to the heuristic so much as a case where **the generality buys nothing**: the
only consumer is `projMotive`'s body, which is always a type, so restricting to a sort
codomain costs no applicability at all.  Where generality is free, take it; where it is what
creates the circularity and buys nothing, do not. -/
theorem VEnv.IsDefEq.instAllCongrSort {env : VEnv} {U : Nat} (henv : env.Ordered)
    {Γ As as as' : List VExpr} {b : VExpr} {l : VLevel}
    (hDF : env.HasArgsDF U Γ As as as') (hr : env.HasArgs U Γ As as')
    (hΓ : OnCtx (As.reverse ++ Γ) (env.IsType U))
    (hb : env.HasType U (As.reverse ++ Γ) b (.sort l)) :
    env.IsDefEq U Γ (VExpr.instAll b as) (VExpr.instAll b as') (.sort l) := by
  have hL := VEnv.IsDefEq.betaMkLams henv (As := As) (as := as) hΓ hDF.left hb
  have hR := VEnv.IsDefEq.betaMkLams henv (As := As) (as := as') hΓ hr hb
  rw [VExpr.instAll_sort] at hL hR
  have hmid : env.IsDefEq U Γ ((mkLams As b).mkApp as) ((mkLams As b).mkApp as') (.sort l) := by
    have := VEnv.IsDefEq.mkAppDF hDF (VEnv.HasType.mkLams hΓ hb)
    rwa [VExpr.instAll_sort] at this
  exact hL.symm.trans (hmid.trans hR)

/-! ## The ι-rule at a concrete spine -/

theorem VLevel.params_inst {ls : List VLevel} {n : Nat} (h : ls.length = n) :
    (VLevel.params n).map (VLevel.inst ls) = ls := by
  subst h
  simp only [VLevel.params, List.map_map, Function.comp_def, VLevel.inst]
  exact map_getD_range

theorem VExpr.map_instAll_bvars_bot {as bs : List VExpr} {n : Nat} (h : bs.length = n) :
    (bvars 0 n).map (VExpr.instAll · (as ++ bs) 0) = bs := by
  have e1 : (bvars 0 n).map (VExpr.instAll · (as ++ bs) 0)
      = ((bvars 0 n).map (VExpr.instAll · as bs.length)).map (VExpr.instAll · bs 0) := by
    simp [List.map_map, Function.comp_def, VExpr.instAll_append]
  rw [e1, VExpr.map_instAll_bvars_lt (by omega), VExpr.map_instAll_bvars' h]

/-- **The ι-rule's left-hand side at a concrete spine.**  `iotaLhs` is the recursor applied
to the ι-context's own variables; substituting `ps`, the motive, the minor premise and the
constructor's fields turns it into exactly the recursor application `projCore` builds, with
the major premise the constructor applied to `ps` and `fs`.

**This equality is load-bearing and is not routine.**  `projCore` (`Structure.lean`) and
`iotaLhs` (`Decl.lean`) were written independently, by different streams, for different
purposes — one to *encode* `Expr.proj`, the other to state the ι-rule — and they meet here
on the nose, with no transport.  That is what makes `TrProj`'s encoding *the same object*
the kernel's ι-rule reduces, rather than merely a term with the same type.  Had the two
drifted by even one lift, every use of the minor-premise obligation would have needed a
transport lemma. -/
theorem VInductDecl'.iotaLhs_instAll (D : VInductDecl') (T : VIndType) (C : VIndCtor)
    {us : List VLevel} {ps fs : List VExpr} {k : Nat} {mot minor : VExpr}
    (hnm : D.nm = 1) (hnmin : D.nmin = 1) (hTd : D.types.getD 0 default = T)
    (hus : us.length = D.uvars) (hps : ps.length = D.np)
    (hfs : fs.length = C.fields.length)
    (hlvl : (D.projLvls C us k).length = D.recUvars) :
    VExpr.instAll ((D.iotaLhs 0 C).instL (D.projLvls C us k))
        (ps ++ [mot, minor] ++ fs)
      = (VExpr.const (Lean.mkRecName T.name) (D.projLvls C us k)).mkApp
          (ps ++ [mot, minor]
            ++ C.args.map (fun a =>
                 VExpr.instAll (VExpr.instAll (a.instL us) ps C.fields.length) fs)
            ++ [(VExpr.const C.name us).mkApp (ps ++ fs)]) := by
  have hself : D.selfLvls.map (VLevel.inst (D.projLvls C us k)) = us := by
    rw [VInductDecl'.projLvls]; exact D.selfLvls_inst _ hus
  have hlen : (ps ++ ([mot, minor] ++ fs)).length = D.np + 1 + 1 + C.fields.length := by
    simp [hps, hfs]; omega
  have hA : ps ++ ([mot, minor] ++ fs) = (ps ++ [mot, minor]) ++ fs := by simp
  -- 1. the parameter block
  have e1 : (bvars (C.fields.length + (1+1)) D.np).map
      (VExpr.instAll · (ps ++ ([mot, minor] ++ fs)) 0) = ps := by
    rw [VExpr.map_instAll_bvars_top (Nat.zero_le _) (by rw [hlen]; omega),
      List.take_left' hps]
    simp
  -- 2, 3. the motive and minor
  have e2 : (bvars (C.fields.length + 1) 1).map
      (VExpr.instAll · (ps ++ ([mot, minor] ++ fs)) 0) = [mot] := by
    simp only [VExpr.bvars, List.map_cons, List.map_nil]
    rw [VExpr.instAll_bvar_get (t := ps.length) (a := mot)
      (by simp [List.getElem?_append_right]) (by rw [hlen, hps]; omega)]
    simp
  have e3 : (bvars C.fields.length 1).map
      (VExpr.instAll · (ps ++ ([mot, minor] ++ fs)) 0) = [minor] := by
    simp only [VExpr.bvars, List.map_cons, List.map_nil]
    rw [VExpr.instAll_bvar_get (t := ps.length + 1) (a := minor)
      (by simp [List.getElem?_append_right, hps]) (by rw [hlen, hps]; omega)]
    simp
  -- 5. the field block inside the constructor application
  have e5 : (bvars 0 C.fields.length).map
      (VExpr.instAll · (ps ++ ([mot, minor] ++ fs)) 0) = fs := by
    rw [hA]; exact VExpr.map_instAll_bvars_bot hfs
  -- 4. the constructor's result indices
  have e4 : ∀ a : VExpr,
      (VExpr.liftN (1+1) (a.instL us) C.fields.length).instAll (ps ++ ([mot, minor] ++ fs))
        = VExpr.instAll (VExpr.instAll (a.instL us) ps C.fields.length) fs := by
    intro a
    rw [hA, VExpr.instAll_append, hfs, VExpr.instAll_append]
    congr 1
    simp only [Nat.zero_add, List.length_cons, List.length_nil]
    rw [VExpr.liftN_instAll (n := 1+1) (as := ps) (X := a.instL us) (k := C.fields.length)]
    exact VExpr.instAll_liftN [mot, minor] _ _
  simp only [VInductDecl'.iotaLhs, hnm, hnmin, hTd, VInductDecl'.ctorApp',
    VInductDecl'.atRec, VExpr.instL_mkApp, VExpr.instL, List.map_append, List.map_map,
    Function.comp_def, VExpr.instL_instL, hself, VExpr.map_instL_bvars,
    VExpr.instAll_mkApp, VExpr.instAll_const, VExpr.instL_liftN,
    VLevel.params_inst hlvl, List.map_cons, List.map_nil, List.append_assoc]
  rw [e1, e2, e3, e5]
  simp only [e4]
  simp

/-- The ι-rule's right-hand side is the η-expansion `λ Γ'. iotaLam Γ'`; at a saturated spine
the wrapper collapses and only `iotaLam` applied to the spine survives. -/
theorem VInductDecl'.iotaRhsBody_instAll (D : VInductDecl') (C : VIndCtor)
    {ls : List VLevel} {spine : List VExpr} (hcl : VExpr.ClosedN (D.iotaLam 0 C) 0)
    (hn : spine.length = (D.iotaCtx C).length) :
    VExpr.instAll (((D.iotaLam 0 C).mkApp (bvars 0 (D.iotaCtx C).length)).instL ls) spine
      = ((D.iotaLam 0 C).instL ls).mkApp spine := by
  rw [VExpr.instL_mkApp, VExpr.map_instL_bvars, VExpr.instAll_mkApp,
    (hcl.instL (ls := ls)).instAll_eq, VExpr.map_instAll_bvars' hn]

/-- `iotaLam`'s body applied to the spine: the minor premise applied to the fields. -/
theorem VInductDecl'.iotaLamBody_instAll (D : VInductDecl') (C : VIndCtor)
    {ls : List VLevel} {ps fs : List VExpr} {mot minor : VExpr}
    (hrec : C.recFields = []) (hps : ps.length = D.np)
    (hfs : fs.length = C.fields.length) :
    VExpr.instAll
        (((VExpr.bvar C.fields.length).mkApp (bvars 0 C.fields.length ++ D.ihValues C)).instL ls)
        (ps ++ [mot, minor] ++ fs)
      = minor.mkApp fs := by
  have hlen : (ps ++ [mot, minor] ++ fs).length = D.np + 1 + 1 + C.fields.length := by
    simp [hps, hfs]; omega
  simp only [VInductDecl'.ihValues, hrec, List.map_nil, List.append_nil,
    VExpr.instL_mkApp, VExpr.instL, VExpr.map_instL_bvars, VExpr.instAll_mkApp]
  rw [VExpr.instAll_bvar_get (t := ps.length + 1) (a := minor)
      (by simp [List.getElem?_append_right, hps]) (by rw [hlen, hps]; omega),
    VExpr.map_instAll_bvars_bot hfs]
  simp

namespace VExpr

/-- A term weakened past `n` binders, then saturated by a spine whose last `n` arguments
fill them, is unchanged.  Generalises `instAll_liftN_snoc` from one binder to `n`. -/
theorem instAll_liftN_append {X : VExpr} {as bs : List VExpr} {k n : Nat} (h : bs.length = n) :
    instAll (liftN n X k) (as ++ bs) k = instAll X as k := by
  rw [instAll_append, h, liftN_instAll, ← h, instAll_liftN]

/-- The telescope version.  This is what collapses the recursor's index telescope, which
`recType` states over `params ++ motives ++ minors`. -/
theorem instAllTele_liftTele_append : ∀ {As as bs : List VExpr} {k n : Nat}, bs.length = n →
    instAllTele (liftTele n As k) (as ++ bs) k = instAllTele As as k
  | [], _, _, _, _, _ => rfl
  | A :: As, as, bs, k, n, h => by
    rw [liftTele_cons, instAllTele_cons, instAllTele_cons, instAll_liftN_append h,
      instAllTele_liftTele_append (As := As) (as := as) (bs := bs) (k := k+1) h]

end VExpr

/-- `recApp_hasType''`'s index obligation, reduced to `TrProj`'s recorded one: the index
telescope is stated over `params ++ motives ++ minors`, and the motive/minor block is
discarded by the lift. -/
theorem VInductDecl'.idxTele_collapse (D : VInductDecl') (T : VIndType) (C : VIndCtor)
    {us : List VLevel} {ps : List VExpr} {k : Nat} {mot minor : VExpr}
    (hnm : D.nm = 1) (hnmin : D.nmin = 1) (hus : us.length = D.uvars) :
    VExpr.instAllTele
        (VExpr.liftTele (D.nm + D.nmin)
          ((D.atRecTele T.indices).map (VExpr.instL (D.projLvls C us k))))
        (ps ++ ([mot] ++ [minor]))
      = VExpr.instAllTele (T.indices.map (VExpr.instL us)) ps := by
  have hself : D.selfLvls.map (VLevel.inst (D.projLvls C us k)) = us := by
    rw [VInductDecl'.projLvls]; exact D.selfLvls_inst _ hus
  simp only [VInductDecl'.atRecTele, List.map_map, Function.comp_def,
    VExpr.instL_instL, hself, hnm, hnmin, List.singleton_append]
  exact VExpr.instAllTele_liftTele_append (bs := [mot, minor]) rfl

/-- A closed, well-formed telescope stays well-formed over any well-formed context.  The
`instL` counterpart already exists as `OnCtx.instL` (`Theory/Typing/Lemmas.lean:628`). -/
theorem OnCtx.appendR {env : VEnv} {U : Nat} {Γ : List VExpr} (henv : env.Ordered)
    (hΓ : OnCtx Γ (env.IsType U)) :
    ∀ {Δ : List VExpr}, CtxClosed Δ → OnCtx Δ (env.IsType U) → OnCtx (Δ ++ Γ) (env.IsType U)
  | [], _, _ => hΓ
  | _ :: _, hcl, ⟨h1, h2⟩ =>
    ⟨OnCtx.appendR henv hΓ hcl.1 h1, h2.imp fun _ h => VEnv.IsDefEq.weakR henv hcl.1 h Γ⟩

/-! ## The ι law

`projCore`'s recursor application at a *constructor* major premise reduces to the minor
premise applied to the fields.  This is the one piece of `TrProj`'s metatheory with genuine
semantic content: everything else is de Bruijn arithmetic.

The chain is `IsDefEq.extra` (the rule) → `IsDefEq.mkApp'` (apply it at the spine) → three
`betaMkLams` (peel the rule's two `mkLams` wrappers and `iotaLam`'s own), with
`iotaLhs_instAll`, `iotaRhsBody_instAll` and `iotaLamBody_instAll` computing each reduct. -/

theorem iota_law {env : VEnv} {U : Nat} {S : Lean.Name}
    {D : VInductDecl'} {T : VIndType} {C : VIndCtor} {us : List VLevel}
    (henv : env.Ordered) (hI : D.IotaCtx env) (H : env.IsStructure S D T C)
    (h3 : us.length = D.uvars) (h7 : ∀ l ∈ us, l.WF U)
    (hnm : D.nm = 1) (hnmin : D.nmin = 1) (hrec : C.recFields = [])
    {k : Nat}
    {Γ ps fs : List VExpr} {mot minor : VExpr}
    (hΓ : OnCtx Γ (env.IsType U))
    (hps : ps.length = D.np) (hfs : fs.length = C.fields.length)
    (hlsWF : ∀ l ∈ D.projLvls C us k, l.WF U)
    (hlslen : (D.projLvls C us k).length = D.recUvars)
    (hTd : D.types.getD 0 default = T)
    (hspine : env.HasArgs U Γ ((D.iotaCtx C).map (VExpr.instL (D.projLvls C us k)))
      (ps ++ [mot, minor] ++ fs)) :
    env.IsDefEq U Γ
      ((VExpr.const (Lean.mkRecName T.name) (D.projLvls C us k)).mkApp
        (ps ++ [mot, minor]
          ++ C.args.map (fun a =>
               VExpr.instAll (VExpr.instAll (a.instL us) ps C.fields.length) fs)
          ++ [(VExpr.const C.name us).mkApp (ps ++ fs)]))
      (minor.mkApp fs)
      (VExpr.instAll ((D.iotaType 0 C).instL (D.projLvls C us k))
        (ps ++ [mot, minor] ++ fs)) := by
  have hT0 : D.types[0]? = some T := by rw [H.types]; rfl
  have hC : C ∈ T.ctors := by rw [H.ctors]; exact List.mem_singleton_self _
  have hqC : D.ctorsAll[0]? = some (0, C) := by
    simp [VInductDecl'.ctorsAll, H.types, H.ctors]
  have hCall : ((0 : Nat), C) ∈ D.ctorsAll := List.mem_of_getElem? hqC
  have hj : (0 : Nat) < D.nm := by omega
  have hclosed : VExpr.ClosedN (D.iotaLam 0 C) 0 :=
    (VInductDecl'.iotaLam_hasType hI hT0 hj hC hqC).closedN henv trivial
  have hn : (ps ++ [mot, minor] ++ fs).length = (D.iotaCtx C).length := by
    simp [VInductDecl'.iotaCtx, VInductDecl'.atRecTele, VInductDecl'.motives,
      VInductDecl'.minors, hps, hfs, hnm, hnmin, VInductDecl'.np]
    omega
  have hIotaOn : OnCtx ((D.iotaCtx C).reverse) (env.IsType D.recUvars) := by
    rw [D.iotaCtx_reverse' C]; exact VInductDecl'.onCtxIota hI.toRecCtx hT0 hC
  have hOn' : OnCtx (((D.iotaCtx C).map (VExpr.instL (D.projLvls C us k))).reverse)
      (env.IsType U) := by
    rw [← List.map_reverse]; exact OnCtx.instL hlsWF hIotaOn
  have hcc : CtxClosed (((D.iotaCtx C).map (VExpr.instL (D.projLvls C us k))).reverse) :=
    OnCtx.ctxClosed henv hOn'
  have hOnCtx : OnCtx (((D.iotaCtx C).map (VExpr.instL (D.projLvls C us k))).reverse ++ Γ)
      (env.IsType U) := OnCtx.appendR henv hΓ hcc hOn'
  have hlhsTy : env.HasType U
      (((D.iotaCtx C).map (VExpr.instL (D.projLvls C us k))).reverse ++ Γ)
      ((D.iotaLhs 0 C).instL (D.projLvls C us k))
      ((D.iotaType 0 C).instL (D.projLvls C us k)) := by
    have h0 := VInductDecl'.iotaLhs_hasType hI hT0 hj hC hCall
    rw [← D.iotaCtx_reverse' C] at h0
    have h1 := VEnv.HasType.instL (ls := D.projLvls C us k) (U' := U) hlsWF h0
    rw [List.map_reverse] at h1
    exact VEnv.IsDefEq.weakR henv hcc h1 Γ
  have hlamTy : env.HasType U
      (((D.iotaCtx C).map (VExpr.instL (D.projLvls C us k))).reverse ++ Γ)
      (((VExpr.bvar (C.fields.length + (D.nmin - 1 - 0))).mkApp
        (bvars 0 C.fields.length ++ D.ihValues C)).instL (D.projLvls C us k))
      ((D.iotaType 0 C).instL (D.projLvls C us k)) := by
    have h0 := VInductDecl'.iotaLamBody_hasType hI hT0 hC hqC
    have h1 := VEnv.HasType.instL (ls := D.projLvls C us k) (U' := U) hlsWF h0
    rw [List.map_reverse] at h1
    exact VEnv.IsDefEq.weakR henv hcc h1 Γ
  have hrhsTy : env.HasType U
      (((D.iotaCtx C).map (VExpr.instL (D.projLvls C us k))).reverse ++ Γ)
      (((D.iotaLam 0 C).mkApp (bvars 0 (D.iotaCtx C).length)).instL (D.projLvls C us k))
      ((D.iotaType 0 C).instL (D.projLvls C us k)) := by
    have h0 := VInductDecl'.iotaLam_hasType hI hT0 hj hC hqC
    have h1 := VEnv.HasType.instL (ls := D.projLvls C us k) (U' := U) hlsWF h0
    simp only [List.map_nil, VExpr.instL_mkPi] at h1
    have h2 := VEnv.IsDefEq.weak0 (Γ := Γ) henv h1
    have h3 := VEnv.HasType.appBVars henv hOnCtx h2
    rw [(hclosed.instL (ls := D.projLvls C us k)).liftN_eq (Nat.zero_le _)] at h3
    simpa [VExpr.instL_mkApp, VExpr.map_instL_bvars] using h3
  -- the chain
  have hextra := VEnv.IsDefEq.extra (Γ := Γ) H.iotaDefeq hlsWF hlslen
  simp only [VInductDecl'.iotaRule, VExpr.instL_mkLams, VExpr.instL_mkPi] at hextra
  have hstep := VEnv.IsDefEq.mkApp' hspine hextra
  have hL := VEnv.IsDefEq.betaMkLams henv hOnCtx hspine hlhsTy
  have hR := VEnv.IsDefEq.betaMkLams henv hOnCtx hspine hrhsTy
  have hLam := VEnv.IsDefEq.betaMkLams henv hOnCtx hspine hlamTy
  rw [D.iotaLhs_instAll T C hnm hnmin hTd h3 hps hfs hlslen] at hL
  rw [D.iotaRhsBody_instAll C hclosed hn] at hR
  rw [show C.fields.length + (D.nmin - 1 - 0) = C.fields.length by simp [hnmin]] at hLam
  rw [D.iotaLamBody_instAll C hrec hps hfs] at hLam
  have hlamEq : (D.iotaLam 0 C).instL (D.projLvls C us k)
      = mkLams ((D.iotaCtx C).map (VExpr.instL (D.projLvls C us k)))
          (((VExpr.bvar C.fields.length).mkApp (bvars 0 C.fields.length ++ D.ihValues C)).instL
            (D.projLvls C us k)) := by
    simp only [VInductDecl'.iotaLam, VExpr.instL_mkLams]
    rw [show C.fields.length + (D.nmin - 1 - 0) = C.fields.length by simp [hnmin]]
  rw [← hlamEq] at hLam
  exact hL.symm.trans (hstep.trans (hR.trans hLam))

/-- **Part 2 of the ι step.**  The minor premise `fun f₀ … f_{n-1} => fᵢ` applied to the
fields β-reduces to the `k`-th field.  Together with `iota_law` this gives
`proj_k (C.mk ps fs) ≡ fs[k]`. -/
theorem projMinor_app {env : VEnv} {U : Nat} (henv : env.Ordered)
    {Γ ps fs : List VExpr} {C : VIndCtor} {us : List VLevel} {k : Nat} {B : VExpr}
    (hk : k < C.fields.length) (hfs : fs.length = C.fields.length)
    (hOn : OnCtx ((VExpr.instAllTele (C.fields.map fun F => F.type.instL us) ps).reverse ++ Γ)
      (env.IsType U))
    (hA : env.HasArgs U Γ (VExpr.instAllTele (C.fields.map fun F => F.type.instL us) ps) fs)
    (hb : env.HasType U
      ((VExpr.instAllTele (C.fields.map fun F => F.type.instL us) ps).reverse ++ Γ)
      (.bvar (C.fields.length - 1 - k)) B) :
    env.IsDefEq U Γ ((C.projMinor us ps k).mkApp fs) (fs.getD k default)
      (VExpr.instAll B fs) := by
  have hget : fs[k]? = some (fs.getD k default) := by
    have : k < fs.length := by omega
    rw [List.getElem?_eq_getElem this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem this]
  have h := VEnv.IsDefEq.betaMkLams henv hOn hA hb
  rw [VExpr.instAll_bvar_get hget (by rw [hfs]; omega)] at h
  simpa [VIndCtor.projMinor] using h

/-- **The dual of `HasType.mkApp'`.**  Substituting a whole telescope of well-typed
arguments into a term typed in that telescope's context. -/
theorem VEnv.HasType.instAll {env : VEnv} {U : Nat} (henv : env.Ordered) {Γ : List VExpr} :
    ∀ {As as : List VExpr} {b B : VExpr}, env.HasArgs U Γ As as →
      env.HasType U (As.reverse ++ Γ) b B →
      env.HasType U Γ (VExpr.instAll b as) (VExpr.instAll B as)
  | [], [], _, _, .nil, hb => hb
  | A :: As, a :: as, b, B, .cons ha has, hb => by
    have hW := Ctx.instN_tele Γ a A As
    have hb2 : env.HasType U (As.reverse ++ A :: Γ) b B := by
      rwa [List.reverse_cons, List.append_assoc, List.singleton_append] at hb
    have hb' := VEnv.HasType.instN henv hW hb2 ha
    have hlen : as.length = As.length := has.length_eq.symm.trans VExpr.length_instTele
    rw [VExpr.instAll_cons, VExpr.instAll_cons, Nat.zero_add, hlen]
    exact VEnv.HasType.instAll henv has hb'

/-- **`projMotive`'s body is a type.**  Field `i`'s stored type, with the parameters and the
earlier fields' spine substituted, is a type at the field's recorded sort.  The caller
supplies the two `HasArgs`: the parameters, and the earlier projections (which come from the
induction hypothesis via `HasArgs.ofMap`). -/
theorem instAll_field_isType {env : VEnv} {U : Nat} {S : Lean.Name}
    {D : VInductDecl'} {T : VIndType} {C : VIndCtor} {us : List VLevel}
    (henv : env.Ordered) (H : env.IsStructure S D T C) (hI : D.IotaCtx env)
    (h3 : us.length = D.uvars) (h7 : ∀ l ∈ us, l.WF U) (hcl : D.ProjClosed T C)
    {i : Nat} (hi : i < C.fields.length)
    {Δ qs earlier : List VExpr}
    (hqs : env.HasArgs U Δ (D.params.map (VExpr.instL us)) qs)
    (hearlier : env.HasArgs U Δ
      (VExpr.instAllTele ((C.fields.take i).map (fun F => F.type.instL us)) qs) earlier) :
    env.HasType U Δ
      (VExpr.instAll ((C.fields.getD i default).type.instL us) (qs ++ earlier))
      (.sort ((C.fields.getD i default).lvl.inst us)) := by
  have := VEnv.HasType.instAll henv (VEnv.HasArgs.append hqs hearlier)
    (ftype_hasType henv H hI h3 h7 hcl hi Δ)
  rwa [VExpr.instAll_sort] at this

end Lean4Lean
