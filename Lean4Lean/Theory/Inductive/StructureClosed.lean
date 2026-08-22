import Lean4Lean.Theory.Inductive.Lemmas
import Lean4Lean.Theory.Inductive.RecApp
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

/-! # Typing `VInductDecl'.projTerm`

Everything `TrProj.wf` needs about the projection term, except the two steps that need
`VEnv.WF` (`IsDefEqU.trans`/`.of_l`) and therefore live in `Verify/Typing/Lemmas.lean`
next to `TrProj.wf` itself.

The argument is a strong induction on the field index — `projCore`'s motive for field `i`
mentions the projections of fields `< i`, so the statement has to be available at every
smaller index and at several different contexts, which is what `ProjHasType` packages.

The pieces, in the order the induction uses them:

* `projArgs_hasArgs` — the earlier projections inhabit the field-prefix telescope: the
  induction hypothesis, packaged as a `HasArgs`;
* `projMotive_hasType` / `projMotiveBody_hasType` — the motive inhabits the recursor's
  motive binder;
* `projCore_hasType` — the plumbing of `recApp_hasType''` with the motive and the minor
  premise left abstract;
* `projMotiveBody_instAll` — the type side: the motive applied to the index terms and the
  major premise *is* the projected field's type.

The minor arm (`projMinor_hasType`, in `Verify/Typing/Lemmas.lean`) is the one with
semantic content: the minor premise's declared codomain is the motive applied to the
constructor, which β-reduces to `Aᵢ[ps, proj₀ (mk ps fs), …]`, and each of those
projections is `fₖ` **by the ι rule** (`iota_law` + `projMinor_app`).
-/

section


variable {env : VEnv} {U : Nat}

/-- Peel a whole `mkPi` telescope out of an `IsType`. -/
theorem VEnv.IsType.mkPi_inv (henv : env.Ordered) :
    ∀ {As : List VExpr} {B Γ}, OnCtx Γ (env.IsType U) → env.IsType U Γ (VExpr.mkPi As B) →
      OnCtx (As.reverse ++ Γ) (env.IsType U) ∧ env.IsType U (As.reverse ++ Γ) B := by
  intro As
  induction As with
  | nil => intro B Γ hΓ h; exact ⟨hΓ, h⟩
  | cons A As ih =>
    intro B Γ hΓ h
    obtain ⟨hA, hB⟩ := (h : env.IsType U Γ (.forallE A (VExpr.mkPi As B))).forallE_inv henv
    have := ih (B := B) (Γ := A :: Γ) ⟨hΓ, hA⟩ hB
    simpa using this


namespace VExpr

/-- The index block of a saturated substitution `as ++ [b]`: `bvars 1 n` picks out `as`. -/
theorem map_instAll_bvars_mid {as : List VExpr} {b : VExpr} {n : Nat} (h : as.length = n) :
    (bvars 1 n).map (VExpr.instAll · (as ++ [b]) 0) = as := by
  rw [← map_liftN_bvars_one, List.map_map]
  have hx : ∀ x : VExpr, instAll (x.liftN 1 0) (as ++ [b]) 0 = instAll x as 0 :=
    fun x => VExpr.instAll_liftN_snoc (k := 0)
  simp only [Function.comp_def, hx]
  exact map_instAll_bvars' h

/-- The identity spine below a lifted prefix: substituting `as` weakened past the `k`
binders it sits above, together with those binders' own variables, is substituting `as`
at cut `k`. -/
theorem instAll_map_liftN_bvars {X : VExpr} {as : List VExpr} {k : Nat}
    (h : X.ClosedN (k + as.length)) :
    instAll X (as.map (·.liftN k) ++ bvars 0 k) 0 = instAll X as k := by
  have h1 : instAll X (as.map (·.liftN k)) k = (instAll X as k).liftN k k := by
    have h0 := lift'_instAll (A := X) (ρ := Lift.skipN .refl k) (as := as) (k := k) h
    rw [lift'_consN_skipN] at h0
    rw [h0]
    exact congrArg (instAll X · k)
      (List.map_congr_left fun x _ => liftN_eq_lift' (e := x) (k := k))
  rw [instAll_append, VExpr.length_bvars, Nat.zero_add, h1]
  simpa using instAll_liftN_bvars k 0 (instAll X as k)

/-- The split used to identify the minor premise's field variable with the projected type. -/
theorem instAll_split_bvars {X : VExpr} {as : List VExpr} {k n : Nat} (hkn : k ≤ n)
    (h : X.ClosedN (k + as.length)) :
    instAll X (as.map (·.liftN n) ++ bvars (n - k) k) 0 = (instAll X as k).liftN (n - k) 0 := by
  have e1 : as.map (·.liftN n) = (as.map (·.liftN k)).map (·.liftN (n - k) 0) := by
    rw [List.map_map]
    refine List.map_congr_left fun p _ => ?_
    simp only [Function.comp_def]
    rw [liftN'_liftN' (n1 := k) (n2 := n - k) (k1 := 0) (k2 := 0) (Nat.le_refl _)
      (Nat.zero_le _), show k + (n - k) = n from by omega]
  have e2 : bvars (n - k) k = (bvars 0 k).map (·.liftN (n - k) 0) := by
    rw [map_liftN_bvars_lo (Nat.le_refl 0), Nat.add_zero]
  rw [e1, e2, ← List.map_append]
  have h0 := lift'_instAll (A := X) (ρ := Lift.skipN .refl (n - k))
    (as := as.map (·.liftN k) ++ bvars 0 k) (k := 0) (by simpa [Nat.add_comm] using h)
  simp only [Lift.consN] at h0
  simp only [← liftN_eq_lift'] at h0
  rw [instAll_map_liftN_bvars h] at h0
  exact h0.symm

/-- The last entry of a saturated substitution. -/
theorem instAll_bvar_zero {as : List VExpr} {b : VExpr} :
    VExpr.instAll (.bvar 0) (as ++ [b]) 0 = b := by
  have hget : (as ++ [b])[as.length]? = some b := by simp
  have := VExpr.instAll_bvar_get (k := 0) (B := 0) hget (by simp; omega)
  simpa using this

end VExpr

/-- The de Bruijn index of the `i`-th entry of a telescope, in the telescope's own
context. -/
theorem Lookup.tele_getElem : ∀ {As Γ : List VExpr} {i : Nat}, i < As.length →
    Lookup (As.reverse ++ Γ) (As.length - 1 - i)
      ((As.getD i default).liftN (As.length - i)) := by
  intro As Γ i hi
  have hget : As.getD i default = As[i] := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  have hsplit : As = As.take i ++ As[i] :: As.drop (i+1) := by
    rw [← List.drop_eq_getElem_cons hi, List.take_append_drop]
  have hrev0 : As.reverse = (As.drop (i+1)).reverse ++ As[i] :: (As.take i).reverse := by
    simp
  have hlen : (As.drop (i+1)).reverse.length = As.length - 1 - i := by simp; omega
  rw [hget, hrev0, List.append_assoc, List.cons_append]
  have h := Lookup.append (As.drop (i+1)).reverse (A := As[i])
    (Γ := (As.take i).reverse ++ Γ)
  rw [hlen, show As.length - 1 - i + 1 = As.length - i from by omega] at h
  exact h

variable {env : VEnv} {U : Nat}

theorem VEnv.HasArgs.toDF {Γ : List VExpr} :
    ∀ {As as}, env.HasArgs U Γ As as → env.HasArgsDF U Γ As as as
  | _, _, .nil => .nil
  | _, _, .cons ha h => .cons ha h.toDF

theorem VEnv.HasArgsDF.append {Γ : List VExpr} :
    ∀ {As as as' Bs bs bs' : List VExpr}, env.HasArgsDF U Γ As as as' →
      env.HasArgsDF U Γ (VExpr.instAllTele Bs as 0) bs bs' →
      env.HasArgsDF U Γ (As ++ Bs) (as ++ bs) (as' ++ bs')
  | _, _, _, _, _, _, .nil, h => by rwa [VExpr.instAllTele_nil_args] at h
  | A₀ :: As, a₀ :: as, a₀' :: as', Bs, bs, bs', .cons h0 h, hB => by
    refine .cons h0 ?_
    show env.HasArgsDF U Γ (VExpr.instTele a₀ (As ++ Bs)) (as ++ bs) (as' ++ bs')
    rw [VExpr.instTele_append, Nat.zero_add]
    refine VEnv.HasArgsDF.append h ?_
    rw [VExpr.instAllTele_cons_args, Nat.zero_add] at hB
    rwa [show As.length = as.length from by
      have h2 := h.left.length_eq; rwa [VExpr.length_instTele] at h2]

theorem VEnv.HasArgsDF.ofMap {Γ : List VExpr} {As as : List VExpr} {f g : Nat → VExpr} :
    ∀ {i : Nat}, i ≤ As.length →
      (∀ k, k < i → env.IsDefEq U Γ (f k) (g k)
        (VExpr.instAll (As.getD k default) (as ++ (List.range k).map f))) →
      env.HasArgsDF U Γ (VExpr.instAllTele (As.take i) as)
        ((List.range i).map f) ((List.range i).map g)
  | 0, _, _ => by simp; exact .nil
  | i+1, hi, h => by
    have hlt : i < As.length := by omega
    have htake : As.take (i+1) = As.take i ++ [As.getD i default] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hlt]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
    rw [List.range_succ, List.map_append, List.map_append, htake, VExpr.instAllTele_append]
    refine VEnv.HasArgsDF.append (VEnv.HasArgsDF.ofMap (by omega) fun k hk => h k (by omega)) ?_
    have hlen : ((List.range i).map f).length = i := by simp
    simp only [List.length_take, Nat.zero_add, Nat.min_def]
    rw [if_pos (by omega)]
    simp only [VExpr.instAllTele_cons, VExpr.instAllTele_nil, List.map_cons, List.map_nil]
    refine .cons ?_ .nil
    have := h i (by omega)
    rwa [VExpr.instAll_append, hlen, Nat.zero_add] at this

/-- `IsDefEq.weakR` for a whole spine. -/
theorem VEnv.HasArgs.weakR (henv : env.Ordered) {Δ Γ : List VExpr} (hcc : CtxClosed Δ) :
    ∀ {As as}, env.HasArgs U Δ As as → env.HasArgs U (Δ ++ Γ) As as
  | _, _, .nil => .nil
  | _, _, .cons ha h => .cons (VEnv.IsDefEq.weakR henv hcc ha Γ) (VEnv.HasArgs.weakR henv hcc h)

/-- **Partial saturated substitution.**  `HasType.instAll` substitutes a spine for the whole
context above `Γ`; this substitutes it for the *outer* block `As` only, leaving the inner
block `Bs` as binders. -/
theorem VEnv.HasType.instAllUnder (henv : env.Ordered) {Γ : List VExpr} :
    ∀ {As as Bs : List VExpr} {b B : VExpr}, env.HasArgs U Γ As as →
      env.HasType U ((As ++ Bs).reverse ++ Γ) b B →
      env.HasType U ((VExpr.instAllTele Bs as).reverse ++ Γ)
        (VExpr.instAll b as Bs.length) (VExpr.instAll B as Bs.length)
  | [], [], Bs, b, B, .nil, hb => by
    simpa [VExpr.instAllTele_nil_args] using hb
  | A :: As, a :: as, Bs, b, B, .cons ha has, hb => by
    have hlen : as.length = As.length := has.length_eq.symm.trans VExpr.length_instTele
    have hb' : env.HasType U ((As ++ Bs).reverse ++ A :: Γ) b B := by simpa using hb
    have hW := VExpr.Ctx.instN_tele Γ a A (As ++ Bs)
    have h1 := VEnv.HasType.instN henv hW hb' ha
    rw [VExpr.instTele_append, Nat.zero_add] at h1
    have ih := VEnv.HasType.instAllUnder henv (As := VExpr.instTele a As) (as := as)
      (Bs := VExpr.instTele a Bs As.length) has h1
    rw [VExpr.instAllTele_cons_args, Nat.zero_add, hlen, VExpr.instAll_cons, VExpr.instAll_cons,
      hlen]
    simpa [VExpr.length_instTele, List.length_append, Nat.add_comm] using ih

theorem VEnv.HasArgs.instAllUnder (henv : env.Ordered) {Γ : List VExpr} :
    ∀ {As as Bs Xs xs : List VExpr}, env.HasArgs U Γ As as →
      env.HasArgs U ((As ++ Bs).reverse ++ Γ) Xs xs →
      env.HasArgs U ((VExpr.instAllTele Bs as).reverse ++ Γ)
        (VExpr.instAllTele Xs as Bs.length) (xs.map (VExpr.instAll · as Bs.length))
  | [], [], Bs, Xs, xs, .nil, hX => by
    simpa [VExpr.instAllTele_nil_args] using hX
  | A :: As, a :: as, Bs, Xs, xs, .cons ha has, hX => by
    have hlen : as.length = As.length := has.length_eq.symm.trans VExpr.length_instTele
    have hX' : env.HasArgs U ((As ++ Bs).reverse ++ A :: Γ) Xs xs := by simpa using hX
    have hW := VExpr.Ctx.instN_tele Γ a A (As ++ Bs)
    have h1 := VEnv.HasArgs.instN henv hW ha hX'
    rw [VExpr.instTele_append, Nat.zero_add] at h1
    have ih := VEnv.HasArgs.instAllUnder henv (As := VExpr.instTele a As) (as := as)
      (Bs := VExpr.instTele a Bs As.length) has h1
    rw [VExpr.instAllTele_cons_args, Nat.zero_add, hlen, VExpr.instAllTele_cons_args, hlen]
    have hmap : (xs.map (VExpr.instAll · (a :: as) Bs.length))
        = (xs.map (·.inst a (Bs.length + as.length))).map (VExpr.instAll · as Bs.length) := by
      simp [List.map_map, Function.comp_def]
    rw [hmap, hlen]
    simpa [VExpr.length_instTele, List.length_append, Nat.add_comm] using ih

section
variable {env : VEnv} {U : Nat} {S : Lean.Name} {D : VInductDecl'} {T : VIndType}
  {C : VIndCtor} {us : List VLevel}

theorem VEnv.IsStructure.types0 (H : env.IsStructure S D T C) : D.types[0]? = some T := by
  rw [H.types]; rfl

theorem VEnv.IsStructure.typesD (H : env.IsStructure S D T C) :
    D.types.getD 0 default = T := by rw [H.types]; rfl

theorem VEnv.IsStructure.memCtor (H : env.IsStructure S D T C) : C ∈ T.ctors := by
  rw [H.ctors]; exact List.mem_singleton_self _

theorem VEnv.IsStructure.memCtorsAll (H : env.IsStructure S D T C) : (0, C) ∈ D.ctorsAll := by
  simp [VInductDecl'.ctorsAll, H.types, H.ctors]

theorem VInductDecl'.projLvls_wf (h7 : ∀ l ∈ us, l.WF U) (k : Nat) :
    ∀ l ∈ D.projLvls C us k, l.WF U := by
  unfold VInductDecl'.projLvls
  cases D.isLE <;> simp
  · exact h7
  · exact ⟨VLevel.WF.inst h7, h7⟩

theorem VInductDecl'.projLvls_length (h3 : us.length = D.uvars) (k : Nat) :
    (D.projLvls C us k).length = D.recUvars := by
  unfold VInductDecl'.projLvls VInductDecl'.recUvars
  cases D.isLE <;> simp [h3]

theorem VInductDecl'.selfLvls_projLvls (h3 : us.length = D.uvars) (k : Nat) :
    D.selfLvls.map (VLevel.inst (D.projLvls C us k)) = us := by
  rw [VInductDecl'.projLvls]; exact D.selfLvls_inst _ h3

theorem VInductDecl'.atRec_instL (h3 : us.length = D.uvars) (k : Nat) (e : VExpr) :
    (D.atRec e).instL (D.projLvls C us k) = e.instL us := by
  simp only [VInductDecl'.atRec, VExpr.instL_instL,
    VInductDecl'.selfLvls_projLvls (C := C) h3 k]

theorem VInductDecl'.atRecTele_instL (h3 : us.length = D.uvars) (k : Nat) (As : List VExpr) :
    (D.atRecTele As).map (VExpr.instL (D.projLvls C us k)) = As.map (VExpr.instL us) := by
  simp only [VInductDecl'.atRecTele, List.map_map, Function.comp_def, VExpr.instL_instL,
    VInductDecl'.selfLvls_projLvls (C := C) h3 k]

theorem VInductDecl'.atRecTele_params_instL (h3 : us.length = D.uvars) (k : Nat) :
    (D.atRecTele D.params).map (VExpr.instL (D.projLvls C us k)) = D.params.map (VExpr.instL us) :=
  VInductDecl'.atRecTele_instL (C := C) h3 k _


/-- The parameter context, moved to the use site. -/
theorem onCtxParams_instL (henv : env.Ordered) (hI : D.IotaCtx env)
    (h7 : ∀ l ∈ us, l.WF U) :
    OnCtx ((D.params.map (VExpr.instL us)).reverse) (env.IsType U) := by
  have := OnCtx.instL (env := env) (ls := us) (U' := U) h7 hI.toRecCtx.params
  rwa [List.map_reverse] at this

theorem motive_declType_isType (henv : env.Ordered) (hI : D.IotaCtx env)
    (H : env.IsStructure S D T C) (h3 : us.length = D.uvars) (h7 : ∀ l ∈ us, l.WF U)
    {Γ ps : List VExpr}
    (hpsA : env.HasArgs U Γ (D.params.map (VExpr.instL us)) ps) {k : Nat} :
    env.IsType U Γ (VExpr.instAll ((D.motiveType 0).instL (D.projLvls C us k)) ps) := by
  have hR := hI.toRecCtx
  obtain ⟨u, hmot0⟩ := VInductDecl'.motiveType_isType hR H.types0 (M := []) (by simp)
    (by simpa using hR.onCtxParams)
  have h1 := VEnv.HasType.instL (ls := D.projLvls C us k) (U' := U)
    (VInductDecl'.projLvls_wf h7 k) hmot0
  simp only [List.nil_append] at h1
  rw [List.map_reverse, VInductDecl'.atRecTele_params_instL h3] at h1
  simp only [VExpr.instL] at h1
  have hOn := onCtxParams_instL (D := D) (us := us) henv hI h7
  have h2 := VEnv.IsDefEq.weakR henv (OnCtx.ctxClosed henv hOn) h1 Γ
  have h4 := VEnv.HasType.instAll henv hpsA h2
  rw [VExpr.instAll_sort] at h4
  exact ⟨_, h4⟩

theorem minor_declType_isType (henv : env.Ordered) (hI : D.IotaCtx env)
    (H : env.IsStructure S D T C) (h3 : us.length = D.uvars) (h7 : ∀ l ∈ us, l.WF U)
    {Γ ps : List VExpr} {mot : VExpr} {k : Nat}
    (hspine : env.HasArgs U Γ ((D.atRecTele D.params).map (VExpr.instL (D.projLvls C us k))
        ++ D.motives.map (VExpr.instL (D.projLvls C us k))) (ps ++ [mot])) :
    env.IsType U Γ
      (VExpr.instAll ((D.minorType 0 0 C).instL (D.projLvls C us k)) (ps ++ [mot])) := by
  have hR := hI.toRecCtx
  have hnm : (0:Nat) < D.nm := by rw [H.nm_eq]; omega
  obtain ⟨u, hmin0⟩ := VInductDecl'.minorType_isType hR H.types0 hnm H.memCtor H.memCtorsAll
    (q := 0) (M := []) (by simp) (by simpa using VInductDecl'.onCtxMotives hR)
  have h1 := VEnv.HasType.instL (ls := D.projLvls C us k) (U' := U)
    (VInductDecl'.projLvls_wf h7 k) hmin0
  simp only [List.nil_append, List.map_append, List.map_reverse] at h1
  simp only [VExpr.instL] at h1
  rw [← List.reverse_append] at h1
  have hOn : OnCtx (((D.atRecTele D.params).map (VExpr.instL (D.projLvls C us k))
      ++ D.motives.map (VExpr.instL (D.projLvls C us k))).reverse) (env.IsType U) := by
    have := OnCtx.instL (env := env) (ls := D.projLvls C us k) (U' := U)
      (VInductDecl'.projLvls_wf h7 k)
      (by simpa using VInductDecl'.onCtxMotives (D := D) (env := env) hR)
    rw [← List.reverse_append, List.map_reverse, List.map_append] at this
    exact this
  have h2 := VEnv.IsDefEq.weakR henv (OnCtx.ctxClosed henv hOn) h1 Γ
  have h4 := VEnv.HasType.instAll henv hspine h2
  rw [VExpr.instAll_sort] at h4
  exact ⟨_, h4⟩

/-- `projCore`'s motive for field `i` at parameter spine `ps`, spelled out. -/
def projMotiveTerm (D : VInductDecl') (T : VIndType) (C : VIndCtor) (us : List VLevel)
    (ps : List VExpr) (i : Nat) : VExpr :=
  VExpr.mkLams (VExpr.instAllTele (T.indices.map (VExpr.instL us)) ps)
    (.lam ((VExpr.const T.name us).mkApp
        (ps.map (·.liftN T.indices.length) ++ bvars 0 T.indices.length))
      (VExpr.instAll ((C.fields.getD i default).type.instL us)
        (ps.map (·.liftN (T.indices.length+1))
          ++ D.projArgs T C us (ps.map (·.liftN (T.indices.length+1)))
              (bvars 1 T.indices.length) i)))

theorem VIndType.projMotive_eq' (D : VInductDecl') (T : VIndType) (C : VIndCtor)
    (us : List VLevel) {ps is : List VExpr} {i : Nat}
    (h : is.length = T.indices.length) :
    T.projMotive C us ps is i
        (D.projArgs T C us (ps.map (·.liftN (is.length+1))) (bvars 1 is.length) i)
      = projMotiveTerm D T C us ps i := by
  rw [VIndType.projMotive, h, projMotiveTerm]

theorem VIndType.projMotive_eq (T : VIndType) (C : VIndCtor) (us : List VLevel)
    {ps is : List VExpr} {i : Nat} {earlier : List VExpr}
    (h : is.length = T.indices.length) :
    T.projMotive C us ps is i earlier
      = VExpr.mkLams (VExpr.instAllTele (T.indices.map (VExpr.instL us)) ps)
          (.lam ((VExpr.const T.name us).mkApp
              (ps.map (·.liftN T.indices.length) ++ bvars 0 T.indices.length))
            (VExpr.instAll ((C.fields.getD i default).type.instL us)
              (ps.map (·.liftN (T.indices.length+1)) ++ earlier))) := by
  rw [VIndType.projMotive, h]

/-- Field `i`'s stored type, at the use site's levels, is closed at `np + i`. -/
theorem ftype_closedN (hcl : D.ProjClosed T C) {i : Nat} (hi : i < C.fields.length) :
    ((C.fields.getD i default).type.instL us).ClosedN (D.np + i) := by
  have hget : (C.fields.map (·.type))[i]? = some (C.fields.getD i default).type := by
    rw [List.getElem?_map, List.getElem?_eq_getElem hi]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  exact (VExpr.ClosedTele.getElem? hcl.fields hget).instL

/-- `projCore`'s motive commutes with a weakening of the parameter block. -/
theorem projMotive_liftN (D : VInductDecl') (T : VIndType) (C : VIndCtor) (us : List VLevel)
    (hcl : D.ProjClosed T C) {i : Nat} (hi : i < C.fields.length)
    {ps : List VExpr} {n : Nat} (hps : ps.length = D.np) :
    (VExpr.mkLams (VExpr.instAllTele (T.indices.map (VExpr.instL us)) ps)
      (.lam ((VExpr.const T.name us).mkApp
          (ps.map (·.liftN T.indices.length) ++ bvars 0 T.indices.length))
        (VExpr.instAll ((C.fields.getD i default).type.instL us)
          (ps.map (·.liftN (T.indices.length+1))
            ++ D.projArgs T C us (ps.map (·.liftN (T.indices.length+1)))
                (bvars 1 T.indices.length) i)))).liftN n
    = VExpr.mkLams (VExpr.instAllTele (T.indices.map (VExpr.instL us)) (ps.map (·.liftN n)))
      (.lam ((VExpr.const T.name us).mkApp
          ((ps.map (·.liftN n)).map (·.liftN T.indices.length) ++ bvars 0 T.indices.length))
        (VExpr.instAll ((C.fields.getD i default).type.instL us)
          ((ps.map (·.liftN n)).map (·.liftN (T.indices.length+1))
            ++ D.projArgs T C us ((ps.map (·.liftN n)).map (·.liftN (T.indices.length+1)))
                (bvars 1 T.indices.length) i))) := by
  have hclI : VExpr.ClosedTele (T.indices.map (VExpr.instL us)) ps.length := by
    rw [hps]; exact VExpr.ClosedTele.map_instL hcl.indices
  have hpmap : ∀ m : Nat, (ps.map (·.liftN (T.indices.length + m))).map (·.liftN n (T.indices.length + m))
      = (ps.map (·.liftN n)).map (·.liftN (T.indices.length + m)) := by
    intro m
    rw [List.map_map, List.map_map]
    refine List.map_congr_left fun p _ => ?_
    simp only [Function.comp_def]
    rw [VExpr.liftN'_liftN' (Nat.zero_le _) (Nat.le_add_right _ _), VExpr.liftN_liftN,
      Nat.add_comm]
  rw [VExpr.liftN_mkLams, VExpr.liftTele_instAllTele₀ hclI, VExpr.length_instAllTele,
    List.length_map, Nat.zero_add]
  refine congrArg _ ?_
  simp only [VExpr.liftN]
  congr 1
  · rw [VExpr.liftN_mkApp, VExpr.liftN, List.map_append, VExpr.map_liftN_bvars_hi (by omega)]
    congr 2
    simpa using hpmap 0
  · have hL : (ps.map (·.liftN (T.indices.length+1))
        ++ D.projArgs T C us (ps.map (·.liftN (T.indices.length+1)))
            (bvars 1 T.indices.length) i).length = D.np + i := by
      simp [hps, D.length_projArgs]
    have hclosed : ((C.fields.getD i default).type.instL us).ClosedN
        (0 + (ps.map (·.liftN (T.indices.length+1))
          ++ D.projArgs T C us (ps.map (·.liftN (T.indices.length+1)))
              (bvars 1 T.indices.length) i).length) := by
      rw [Nat.zero_add, hL]; exact ftype_closedN hcl hi
    have h0 := VExpr.lift'_instAll
      (A := (C.fields.getD i default).type.instL us)
      (ρ := (Lift.skipN .refl n).consN (T.indices.length + 1))
      (as := ps.map (·.liftN (T.indices.length+1))
        ++ D.projArgs T C us (ps.map (·.liftN (T.indices.length+1)))
            (bvars 1 T.indices.length) i)
      (k := 0) hclosed
    rw [Lift.consN_consN, Nat.add_zero, VExpr.lift'_consN_skipN] at h0
    rw [h0, List.map_append]
    congr 2
    · simp only [VExpr.lift'_consN_skipN]
      exact hpmap 1
    · rw [D.projArgs_lift' T C us hcl (by simp [hps]) (by simp) (Nat.le_of_lt hi)
        (Lift.consN_fixes.le (by omega))]
      simp only [VExpr.lift'_consN_skipN]
      rw [VExpr.map_liftN_bvars_hi (by omega), hpmap 1]

/-- **Step 4, the type side.**  The motive's body, saturated by index terms and a major
premise, is field `i`'s type with the parameters and the earlier projections of that major
premise substituted. -/
theorem projMotiveBody_instAll (D : VInductDecl') (T : VIndType) (C : VIndCtor)
    (us : List VLevel) (hcl : D.ProjClosed T C) {i : Nat} (hi : i < C.fields.length)
    {ps js : List VExpr} {x : VExpr} (hps : ps.length = D.np)
    (hjs : js.length = T.indices.length) :
    VExpr.instAll
      (VExpr.instAll ((C.fields.getD i default).type.instL us)
        (ps.map (·.liftN (T.indices.length+1))
          ++ D.projArgs T C us (ps.map (·.liftN (T.indices.length+1)))
              (bvars 1 T.indices.length) i))
      (js ++ [x])
      = VExpr.instAll ((C.fields.getD i default).type.instL us)
          (ps ++ (List.range i).map fun k => D.projTerm T C us ps js k x) := by
  have hlen : (js ++ [x]).length = T.indices.length + 1 := by simp [hjs]
  have hL : (ps.map (·.liftN (T.indices.length+1))
      ++ D.projArgs T C us (ps.map (·.liftN (T.indices.length+1)))
          (bvars 1 T.indices.length) i).length = D.np + i := by
    simp [hps, D.length_projArgs]
  have hcancel : ∀ p : VExpr,
      VExpr.instAll (p.liftN (T.indices.length+1)) (js ++ [x]) 0 = p := by
    intro p; rw [← hlen]; exact VExpr.instAll_liftN _ _ _
  rw [VExpr.instAll_instAll (by rw [hL]; exact ftype_closedN hcl hi)]
  congr 1
  rw [List.map_append]
  congr 1
  · simp [List.map_map, Function.comp_def, hcancel]
  · rw [D.projArgs_eq_map, List.map_map]
    refine List.map_congr_left fun k hk => ?_
    simp only [Function.comp_def]
    rw [D.projTerm_instAll T C us hcl (by simp at hk; omega) (by simp [hps]) (by simp)]
    congr 1
    · simp [List.map_map, Function.comp_def, hcancel]
    · exact VExpr.map_instAll_bvars_mid hjs
    · exact VExpr.instAll_bvar_zero

/-- The conclusion of `projTerm_hasType` at one field index, as a named predicate: the
strong induction quantifies `Γ`, `ps`, `ιs`, `e` *after* the index, so the induction
hypothesis has to be applied at several different contexts. -/
def ProjHasType (env : VEnv) (U : Nat) (S : Lean.Name) (D : VInductDecl') (T : VIndType)
    (C : VIndCtor) (us : List VLevel) (k : Nat) : Prop :=
  ∀ {Γ ps ιs : List VExpr} {e : VExpr}, OnCtx Γ (env.IsType U) →
    env.HasType U Γ e ((VExpr.const S us).mkApp (ps ++ ιs)) →
    ps.length = D.np → ιs.length = T.indices.length →
    env.HasArgs U Γ (D.params.map (VExpr.instL us)) ps →
    env.HasArgs U Γ (VExpr.instAllTele (T.indices.map (VExpr.instL us)) ps) ιs →
    env.HasType U Γ (D.projTerm T C us ps ιs k e)
      (VExpr.instAll ((C.fields.getD k default).type.instL us)
        (ps ++ (List.range k).map fun m => D.projTerm T C us ps ιs m e))

/-- The motive's own binder context: the index telescope and the major-premise binder. -/
theorem motiveCtx_wf (henv : env.Ordered) (hI : D.IotaCtx env)
    (H : env.IsStructure S D T C) (h3 : us.length = D.uvars) (h7 : ∀ l ∈ us, l.WF U)
    {Γ ps : List VExpr} (hΓ : OnCtx Γ (env.IsType U)) (hps : ps.length = D.np)
    (hpsA : env.HasArgs U Γ (D.params.map (VExpr.instL us)) ps) :
    OnCtx ((VExpr.instAllTele (T.indices.map (VExpr.instL us)) ps).reverse ++ Γ)
        (env.IsType U) ∧
      env.IsType U ((VExpr.instAllTele (T.indices.map (VExpr.instL us)) ps).reverse ++ Γ)
        ((VExpr.const T.name us).mkApp
          (ps.map (·.liftN T.indices.length) ++ bvars 0 T.indices.length)) := by
  have hmotIT := motive_declType_isType henv hI H h3 h7 hpsA (k := 0)
  rw [motiveType_instL_instAll D T C H.typesD h3 hps] at hmotIT
  obtain ⟨hOnΔ1, hfa⟩ := VEnv.IsType.mkPi_inv henv hΓ hmotIT
  exact ⟨hOnΔ1, (hfa.forallE_inv henv).1⟩

theorem fields_getD_map (hk : k < C.fields.length) :
    (C.fields.map fun F => F.type.instL us).getD k default
      = (C.fields.getD k default).type.instL us := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hk,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  rfl

/-- **The earlier projections inhabit the field prefix telescope.**  This is the induction
hypothesis packaged as a `HasArgs`, in the motive's own binder context. -/
theorem projArgs_hasArgs (henv : env.Ordered) (hI : D.IotaCtx env)
    (H : env.IsStructure S D T C) (h3 : us.length = D.uvars) (h7 : ∀ l ∈ us, l.WF U)
    (hcl : D.ProjClosed T C) {i : Nat} (hi : i ≤ C.fields.length)
    (IH : ∀ k, k < i → ProjHasType env U S D T C us k)
    {Γ ps : List VExpr} (hΓ : OnCtx Γ (env.IsType U)) (hps : ps.length = D.np)
    (hpsA : env.HasArgs U Γ (D.params.map (VExpr.instL us)) ps) :
    env.HasArgs U
      (((VExpr.const T.name us).mkApp
          (ps.map (·.liftN T.indices.length) ++ bvars 0 T.indices.length))
        :: ((VExpr.instAllTele (T.indices.map (VExpr.instL us)) ps).reverse ++ Γ))
      (VExpr.instAllTele ((C.fields.take i).map fun F => F.type.instL us)
        (ps.map (·.liftN (T.indices.length+1))))
      (D.projArgs T C us (ps.map (·.liftN (T.indices.length+1)))
        (bvars 1 T.indices.length) i) := by
  obtain ⟨hOnΔ1, hctorTy⟩ := motiveCtx_wf henv hI H h3 h7 hΓ hps hpsA
  have hclI : VExpr.ClosedTele (T.indices.map (VExpr.instL us)) ps.length := by
    rw [hps]; exact VExpr.ClosedTele.map_instL hcl.indices
  have hΔ : OnCtx
      (((VExpr.const T.name us).mkApp
          (ps.map (·.liftN T.indices.length) ++ bvars 0 T.indices.length))
        :: ((VExpr.instAllTele (T.indices.map (VExpr.instL us)) ps).reverse ++ Γ))
      (env.IsType U) := ⟨hOnΔ1, hctorTy⟩
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
  rw [VExpr.liftTele_eq_self (VExpr.ClosedTele.map_instL hcl.params) (Nat.zero_le _)] at hqs
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
    rw [VExpr.lift, VExpr.liftN_mkApp, VExpr.liftN, List.map_append, List.map_map, Function.comp_def,
      VExpr.map_liftN_bvars_lo (Nat.zero_le _)] at h
    simp only [VExpr.liftN_liftN] at h
    rw [← H.name]
    exact h
  rw [D.projArgs_eq_map, List.map_take]
  refine VEnv.HasArgs.ofMap (by simp; omega) fun k hk => ?_
  have hk' : k < C.fields.length := by omega
  have := IH k hk hΔ hbv0 (by simp [hps]) (by simp) hqs hjs
  rwa [fields_getD_map hk']

/-- **The motive's body is a type**, at the recursor's elimination level. -/
theorem projMotiveBody_hasType (henv : env.Ordered) (hI : D.IotaCtx env)
    (H : env.IsStructure S D T C) (h3 : us.length = D.uvars) (h7 : ∀ l ∈ us, l.WF U)
    (hcl : D.ProjClosed T C) {i : Nat} (hi : i < C.fields.length)
    (hlv : (C.fields.getD i default).lvl.inst us ≈ D.elimLvl.inst (D.projLvls C us i))
    {Γ ps : List VExpr} (hps : ps.length = D.np)
    (hpsA : env.HasArgs U Γ (D.params.map (VExpr.instL us)) ps)
    {earlier : List VExpr}
    (hearlier : env.HasArgs U
      (((VExpr.const T.name us).mkApp
          (ps.map (·.liftN T.indices.length) ++ bvars 0 T.indices.length))
        :: ((VExpr.instAllTele (T.indices.map (VExpr.instL us)) ps).reverse ++ Γ))
      (VExpr.instAllTele ((C.fields.take i).map fun F => F.type.instL us)
        (ps.map (·.liftN (T.indices.length+1))))
      earlier) :
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
  rw [VExpr.liftTele_eq_self (VExpr.ClosedTele.map_instL hcl.params) (Nat.zero_le _)] at hqs
  have hbody := instAll_field_isType henv H hI h3 h7 hcl hi hqs hearlier
  exact VEnv.IsDefEq.defeqDF
    (VEnv.IsDefEq.sortDF (VLevel.WF.inst h7)
      (VLevel.WF.inst (VInductDecl'.projLvls_wf (C := C) h7 i)) hlv) hbody

/-- **Step 1's motive arm.**  `projCore`'s motive inhabits the recursor's motive binder. -/
theorem projMotive_hasType (henv : env.Ordered) (hI : D.IotaCtx env)
    (H : env.IsStructure S D T C) (h3 : us.length = D.uvars) (h7 : ∀ l ∈ us, l.WF U)
    (hcl : D.ProjClosed T C) {i : Nat} (hi : i < C.fields.length)
    (hlv : (C.fields.getD i default).lvl.inst us ≈ D.elimLvl.inst (D.projLvls C us i))
    {Γ ps : List VExpr} (hΓ : OnCtx Γ (env.IsType U)) (hps : ps.length = D.np)
    (hpsA : env.HasArgs U Γ (D.params.map (VExpr.instL us)) ps)
    {earlier : List VExpr}
    (hearlier : env.HasArgs U
      (((VExpr.const T.name us).mkApp
          (ps.map (·.liftN T.indices.length) ++ bvars 0 T.indices.length))
        :: ((VExpr.instAllTele (T.indices.map (VExpr.instL us)) ps).reverse ++ Γ))
      (VExpr.instAllTele ((C.fields.take i).map fun F => F.type.instL us)
        (ps.map (·.liftN (T.indices.length+1))))
      earlier) :
    env.HasType U Γ
      (VExpr.mkLams (VExpr.instAllTele (T.indices.map (VExpr.instL us)) ps)
        (.lam ((VExpr.const T.name us).mkApp
            (ps.map (·.liftN T.indices.length) ++ bvars 0 T.indices.length))
          (VExpr.instAll ((C.fields.getD i default).type.instL us)
            (ps.map (·.liftN (T.indices.length+1)) ++ earlier))))
      (VExpr.instAll ((D.motiveType 0).instL (D.projLvls C us i)) ps) := by
  obtain ⟨hOnΔ1, uc, hctorTy⟩ := motiveCtx_wf henv hI H h3 h7 hΓ hps hpsA
  rw [motiveType_instL_instAll D T C H.typesD h3 hps]
  exact VEnv.HasType.mkLams hOnΔ1 (VEnv.HasType.lam hctorTy
    (projMotiveBody_hasType henv hI H h3 h7 hcl hi hlv hps hpsA hearlier))

/-- The constructor's index arguments, at the use site, over the field telescope. -/
theorem ctorArgs_hasArgs (henv : env.Ordered) (hI : D.IotaCtx env)
    (H : env.IsStructure S D T C) (h7 : ∀ l ∈ us, l.WF U)
    {Γ ps : List VExpr}
    (hpsA : env.HasArgs U Γ (D.params.map (VExpr.instL us)) ps) :
    env.HasArgs U
      ((VExpr.instAllTele (C.fields.map fun F => F.type.instL us) ps).reverse ++ Γ)
      (VExpr.liftTele C.fields.length
        (VExpr.instAllTele (T.indices.map (VExpr.instL us)) ps))
      (C.args.map fun a => VExpr.instAll (a.instL us) ps C.fields.length) := by
  have hR := hI.toRecCtx
  have hCwf : VIndCtor.WF env D 0 T C := hR.ctors 0 T H.types0 C H.memCtor
  have hOn0 : OnCtx (((C.fields.map (·.type)).reverse ++ D.params.reverse).map (VExpr.instL us))
      (env.IsType U) := OnCtx.instL h7 (hCwf.onCtxAllFields henv)
  have h1 := VEnv.HasArgs.instL (U' := U) (ls := us) h7 hCwf.args_ty
  simp only [List.map_append, List.map_reverse, VExpr.instL_liftTele, List.map_map,
    Function.comp_def] at h1 hOn0
  rw [← List.reverse_append] at h1 hOn0
  have h2 := VEnv.HasArgs.weakR (Γ := Γ) henv (OnCtx.ctxClosed henv hOn0) h1
  have h3 := VEnv.HasArgs.instAllUnder henv hpsA h2
  rw [List.length_map, VExpr.instAllTele_liftTele₀ (n := C.fields.length)
      (As := T.indices.map (VExpr.instL us)) (as := ps)] at h3
  simpa [List.map_map, Function.comp_def] using h3

/-- The constructor applied to the parameters and its own field variables. -/
theorem ctorApp_hasType (henv : env.Ordered) (hI : D.IotaCtx env)
    (H : env.IsStructure S D T C) (h3 : us.length = D.uvars) (h7 : ∀ l ∈ us, l.WF U)
    {Γ ps : List VExpr} (hps : ps.length = D.np)
    (hpsA : env.HasArgs U Γ (D.params.map (VExpr.instL us)) ps) :
    env.HasType U
      ((VExpr.instAllTele (C.fields.map fun F => F.type.instL us) ps).reverse ++ Γ)
      ((VExpr.const C.name us).mkApp
        (ps.map (·.liftN C.fields.length) ++ bvars 0 C.fields.length))
      ((VExpr.const T.name us).mkApp (ps.map (·.liftN C.fields.length)
        ++ C.args.map fun a => VExpr.instAll (a.instL us) ps C.fields.length)) := by
  have hR := hI.toRecCtx
  have hCwf : VIndCtor.WF env D 0 T C := hR.ctors 0 T H.types0 C H.memCtor
  have h0 := VInductDecl'.ctorApp'_hasType hR H.types0 H.memCtor H.memCtorsAll
    (m := 0) (Δ := []) rfl (by simpa using hR.onCtxParams)
  simp only [VExpr.liftTele_zero, List.nil_append, VExpr.liftN_zero, Nat.add_zero] at h0
  have hOn0 : OnCtx (((C.fields.map (·.type)).reverse ++ D.params.reverse).map (VExpr.instL us))
      (env.IsType U) := OnCtx.instL h7 (hCwf.onCtxAllFields henv)
  simp only [List.map_append, List.map_reverse, List.map_map, Function.comp_def] at hOn0
  rw [← List.reverse_append] at hOn0
  have h1 := VEnv.HasType.instL (U' := U) (ls := D.projLvls C us 0)
    (VInductDecl'.projLvls_wf h7 0) h0
  rw [List.map_append, List.map_reverse, List.map_reverse,
    VInductDecl'.atRecTele_instL (C := C) h3 0, VInductDecl'.atRecTele_instL (C := C) h3 0,
    ← List.reverse_append, VInductDecl'.atRec_instL (C := C) h3 0] at h1
  simp only [VInductDecl'.ctorApp', VExpr.instL_mkApp, VExpr.instL, VExpr.map_instL_bvars,
    List.map_append, VInductDecl'.selfLvls_projLvls (C := C) h3 0,
    VIndCtor.canonResult, VInductDecl'.tyApp, H.typesD, VInductDecl'.ownLvls,
    VLevel.params_inst h3, List.map_map, Function.comp_def] at h1
  have h2 := VEnv.IsDefEq.weakR henv (OnCtx.ctxClosed henv hOn0) h1 Γ
  have h3' := VEnv.HasType.instAllUnder henv hpsA h2
  rw [List.length_map] at h3'
  rw [VExpr.instAll_mkApp, VExpr.instAll_const, VExpr.instAll_mkApp, VExpr.instAll_const,
    List.map_append, List.map_append,
    VExpr.map_instAll_bvars_top (Nat.le_refl _) (by simp [hps]),
    VExpr.map_instAll_bvars_lt (Nat.le_of_eq (Nat.zero_add _)),
    List.take_of_length_le (by simp [hps])] at h3'
  simpa [List.map_map, Function.comp_def] using h3'

/-- The constructor's result indices are closed over `params ++ fields`. -/
theorem args_closedN (henv : env.Ordered) (hI : D.IotaCtx env)
    (H : env.IsStructure S D T C) :
    ∀ a ∈ C.args, VExpr.ClosedN a (C.fields.length + D.np) := by
  have hCwf : VIndCtor.WF env D 0 T C := hI.toRecCtx.ctors 0 T H.types0 C H.memCtor
  have hcc : CtxClosed ((C.fields.map (·.type)).reverse ++ D.params.reverse) :=
    OnCtx.ctxClosed henv (hCwf.onCtxAllFields henv)
  have hlen : ((C.fields.map (·.type)).reverse ++ D.params.reverse).length
      = C.fields.length + D.np := by simp [VInductDecl'.np]
  have h := VEnv.IsDefEq.closedN henv hCwf.result hcc
  rw [hlen, VIndCtor.canonResult, VInductDecl'.tyApp, VExpr.closedN_mkApp] at h
  intro a ha
  exact h.2 _ (List.mem_append_right _ ha)

theorem projMotiveTerm_liftN (henv : env.Ordered) (H : env.IsStructure S D T C)
    (hcl : D.ProjClosed T C) {i : Nat} (hi : i < C.fields.length)
    {ps : List VExpr} {n : Nat} (hps : ps.length = D.np) :
    (projMotiveTerm D T C us ps i).liftN n = projMotiveTerm D T C us (ps.map (·.liftN n)) i := by
  rw [projMotiveTerm, projMotiveTerm, projMotive_liftN D T C us hcl hi hps]

theorem projMotiveTerm_hasType (henv : env.Ordered) (hI : D.IotaCtx env)
    (H : env.IsStructure S D T C) (h3 : us.length = D.uvars) (h7 : ∀ l ∈ us, l.WF U)
    (hcl : D.ProjClosed T C) {i : Nat} (hi : i < C.fields.length)
    (hlvi : (C.fields.getD i default).lvl.inst us ≈ D.elimLvl.inst (D.projLvls C us i))
    (hIH : ∀ k, k < i → ProjHasType env U S D T C us k)
    {Γ ps : List VExpr} (hΓ : OnCtx Γ (env.IsType U)) (hps : ps.length = D.np)
    (hpsA : env.HasArgs U Γ (D.params.map (VExpr.instL us)) ps) :
    env.HasType U Γ (projMotiveTerm D T C us ps i)
      (VExpr.instAll ((D.motiveType 0).instL (D.projLvls C us i)) ps) := by
  rw [projMotiveTerm]
  exact projMotive_hasType henv hI H h3 h7 hcl hi hlvi hΓ hps hpsA
    (projArgs_hasArgs henv hI H h3 h7 hcl (Nat.le_of_lt hi) hIH hΓ hps hpsA)

theorem VInductDecl'.motives_eq (H : env.IsStructure S D T C) : D.motives = [D.motiveType 0] := by
  rw [VInductDecl'.motives, H.nm_eq]; rfl

theorem VInductDecl'.minors_eq (H : env.IsStructure S D T C) :
    D.minors = [D.minorType 0 0 C] := by
  simp [VInductDecl'.minors, VInductDecl'.ctorsAll, H.types, H.ctors]

/-- **The plumbing of `recApp_hasType''`**, with the motive and the minor premise abstract:
`projCore`'s spine, re-associated, at any motive and minor inhabiting the recursor's
declared binders. -/
theorem projCore_hasType (henv : env.Ordered) (hI : D.IotaCtx env)
    (H : env.IsStructure S D T C) (h3 : us.length = D.uvars) (h7 : ∀ l ∈ us, l.WF U)
    {i : Nat} {Γ ps ιs : List VExpr} {e mot minor B : VExpr}
    (hps : ps.length = D.np) (hιs : ιs.length = T.indices.length)
    (he : env.HasType U Γ e ((VExpr.const S us).mkApp (ps ++ ιs)))
    (hpsA : env.HasArgs U Γ (D.params.map (VExpr.instL us)) ps)
    (hιsA : env.HasArgs U Γ (VExpr.instAllTele (T.indices.map (VExpr.instL us)) ps) ιs)
    (hmotT : env.HasType U Γ mot
      (VExpr.instAll ((D.motiveType 0).instL (D.projLvls C us i)) ps))
    (hminT : env.HasType U Γ minor
      (VExpr.instAll ((D.minorType 0 0 C).instL (D.projLvls C us i)) (ps ++ [mot])))
    (hconv : ∃ u, env.IsDefEq U Γ (mot.mkApp (ιs ++ [e])) B (.sort u)) :
    env.HasType U Γ
      ((VExpr.const (Lean.mkRecName T.name) (D.projLvls C us i)).mkApp
        (ps ++ [mot, minor] ++ ιs ++ [e])) B := by
  have hnm := H.nm_eq
  have hnmin := H.nmin_eq
  have hP : env.HasArgs U Γ
      ((D.atRecTele D.params).map (VExpr.instL (D.projLvls C us i))) ps := by
    rw [VInductDecl'.atRecTele_params_instL (C := C) h3]; exact hpsA
  have hM : env.HasArgs U Γ
      (VExpr.instAllTele (D.motives.map (VExpr.instL (D.projLvls C us i))) ps 0) [mot] := by
    rw [VInductDecl'.motives_eq H]; exact .cons hmotT .nil
  have hMinB : env.HasArgs U Γ
      (VExpr.instAllTele (D.minors.map (VExpr.instL (D.projLvls C us i))) (ps ++ [mot]) 0)
      [minor] := by
    rw [VInductDecl'.minors_eq H]; exact .cons hminT .nil
  have hspine := VEnv.HasArgs.append (VEnv.HasArgs.append hP hM) hMinB
  rw [List.append_assoc ps] at hspine
  have hidx : env.HasArgs U Γ
      (VExpr.instAllTele
        (liftTele (D.nm + D.nmin) ((D.atRecTele T.indices).map
          (VExpr.instL (D.projLvls C us i))))
        (ps ++ ([mot] ++ [minor])) 0) ιs := by
    rw [D.idxTele_collapse T C hnm hnmin h3]; exact hιsA
  have he' : env.HasType U Γ e
      ((VExpr.const T.name (D.selfLvls.map (VLevel.inst (D.projLvls C us i)))).mkApp
        (ps ++ ιs)) := by
    rw [VInductDecl'.selfLvls_projLvls (C := C) h3, H.name]; exact he
  have hmain := VInductDecl'.recApp_hasType'' hI H.types0 (by omega)
    (VInductDecl'.projLvls_wf h7 i) (VInductDecl'.projLvls_length (C := C) h3 i) hps
    (by simp [hnm]) (by simp [hnmin]) hspine rfl hιs hidx he'
  obtain ⟨u, hconv⟩ := hconv
  have hmain' : env.HasType U Γ
      ((VExpr.const (Lean.mkRecName T.name) (D.projLvls C us i)).mkApp
        (ps ++ [mot, minor] ++ ιs ++ [e])) (mot.mkApp (ιs ++ [e])) := by
    simpa [List.append_assoc] using hmain
  exact VEnv.IsDefEq.defeqDF hconv hmain'


end

end

end Lean4Lean
