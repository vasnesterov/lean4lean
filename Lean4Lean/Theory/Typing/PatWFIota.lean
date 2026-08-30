import Lean4Lean.Theory.Typing.PatWF

/-!
# `VEnv.PatWF`'s ι case

`Theory/Typing/PatWF.lean` closes the quotient case; this file is the ι case, following the
same five steps at general telescopes.  See `docs/handoff-patwf.md` §4 for the decomposition.
-/

namespace Lean4Lean

open VExpr (mkPi mkLams mkApp bvars instAll instAllTele instTele liftTele)

namespace VEnv

variable {env : VEnv} {U : Nat} {Γ : List VExpr}

/-- **`HasArgs.append`, inverted** (handoff obligation 2): splitting a spine at an arbitrary
point.  `HasArgs.concat_inv` is the special case of a one-entry tail. -/
theorem HasArgs.append_inv :
    ∀ {As as Bs bs : List VExpr}, as.length = As.length →
      env.HasArgs U Γ (As ++ Bs) (as ++ bs) →
      env.HasArgs U Γ As as ∧ env.HasArgs U Γ (instAllTele Bs as 0) bs
  | [], as, Bs, bs, hlen, h => by
    cases List.eq_nil_of_length_eq_zero hlen
    exact ⟨.nil, by rwa [VExpr.instAllTele_nil_args]⟩
  | A₀ :: As, as, Bs, bs, hlen, h => by
    match as, hlen with
    | a₀ :: as, hlen =>
      have hlen : as.length = As.length := by simpa using hlen
      let .cons h0 h' := h
      simp only [List.append_eq] at h'
      rw [VExpr.instTele_append, Nat.zero_add] at h'
      obtain ⟨ih1, ih2⟩ := HasArgs.append_inv (As := instTele a₀ As) (by simpa using hlen) h'
      refine ⟨.cons h0 ih1, ?_⟩
      rwa [VExpr.instAllTele_cons_args, Nat.zero_add, hlen]

end VEnv

namespace VInductDecl'

variable (D : VInductDecl')

/-- The block of binders shared by every recursor type and every ι-context: the parameters,
the motives and the minor premises.  Handoff obligation 1 is that this really is a shared
*syntactic* prefix, which `peelPis_recType` and `iotaCtx_eq` state. -/
def preTele : List VExpr := D.atRecTele D.params ++ D.motives ++ D.minors

@[simp] theorem length_preTele : D.preTele.length = D.np + D.nm + D.nmin := by
  simp [preTele, length_atRecTele, length_motives, length_minors]
  exact (Nat.add_assoc ..).symm

theorem iotaCtx_eq (C : VIndCtor) :
    D.iotaCtx C
      = D.preTele ++ liftTele (D.nm + D.nmin) (D.atRecTele (C.fields.map (·.type))) := rfl

theorem peelPis_recType (j : Nat) :
    (VExpr.peelPis (D.recType j)).1
      = (D.preTele ++ liftTele (D.nm + D.nmin)
            (D.atRecTele (D.types.getD j default).indices))
        ++ [D.tyApp' j ((D.types.getD j default).indices.length + D.nmin + D.nm)
              (bvars 0 (D.types.getD j default).indices.length)] := by
  rw [VInductDecl'.recType, VExpr.peelPis_mkPi, VExpr.peelPis_forallE]
  simp [VExpr.mkApp_concat, VExpr.peelPis, preTele]

theorem peelPis_recType_body (j : Nat) :
    (VExpr.peelPis (D.recType j)).2
      = (VExpr.bvar (1 + (D.types.getD j default).indices.length + D.nmin
            + (D.nm - 1 - j))).mkApp
          (bvars 1 (D.types.getD j default).indices.length ++ [.bvar 0]) := by
  rw [VInductDecl'.recType, VExpr.peelPis_mkPi, VExpr.peelPis_forallE]
  simp [VExpr.mkApp_concat, VExpr.peelPis]

end VInductDecl'

theorem VIndCtor.peelPis_type (C : VIndCtor) (D : VInductDecl') (j : Nat) :
    (VExpr.peelPis (C.type D j)).1 = C.params ++ C.fields.map (·.type) := by
  rw [VIndCtor.type, VExpr.peelPis_mkPi, VIndCtor.canonResult, VInductDecl'.tyApp]
  cases h : bvars C.fields.length D.np ++ C.args with
  | nil => simp [VExpr.mkApp, VExpr.peelPis]
  | cons a as =>
    have : VExpr.mkApp (VExpr.const (D.types.getD j default).name D.ownLvls) (a :: as)
        = _ := rfl
    simp [VExpr.peelPis_mkApp_app]


namespace VEnv

variable {env : VEnv} {U : Nat} {Γ : List VExpr}

/-- Build a `HasArgsDF` from a `HasArgs` and an entrywise `IsDefEqU`. -/
theorem HasArgsDF.ofForall₂ (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U)) :
    ∀ {As as as' : List VExpr}, env.HasArgs U Γ As as →
      List.Forall₂ (env.IsDefEqU U Γ) as as' → env.HasArgsDF U Γ As as as'
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons ha h, .cons hd hr =>
    .cons (IsDefEqU.of_l henv hΓ hd ha) (HasArgsDF.ofForall₂ henv hΓ h hr)

/-- **Every argument of a typed application spine is typed.**  `HasType.mkApp_arg` gives this
for the *first* argument only; the iteration is what reads a stored constant's result
indices back out of its declared type. -/
theorem HasType.mkApp_mem (henv : Ordered env) (hΓ : OnCtx Γ (env.IsType U)) :
    ∀ (as : List VExpr) {f A : VExpr}, env.HasType U Γ (f.mkApp as) A →
      ∀ a ∈ as, ∃ B, env.HasType U Γ a B
  | [], _, _, _, a, ha => absurd ha (by simp)
  | a₀ :: as, f, A, h, a, ha => by
    rw [VExpr.mkApp_cons] at h
    rcases List.mem_cons.1 ha with rfl | ha
    · obtain ⟨A₀, B₀, -, ha'⟩ := HasType.mkApp_arg henv hΓ as h
      exact ⟨_, ha'⟩
    · exact HasType.mkApp_mem henv hΓ as h a ha

/-- **The constructor's spine, retyped at the recursor's parameters and levels.**

Handoff obligations 3 and 5, in the form the ι case actually needs them.  The matched major
premise is `C.{ls'} cps fs`; the ι-rule's context states the field telescope at the
*recursor's* parameters `ps` and at the recursor's level numbering `σ`.  The check supplies
`cps ≡ ps` and `ls' ≈ σ`, and this lemma cashes both in at once — the whole spine is moved by
one `mkAppDF`, and the moved spine is re-inverted by `HasArgs.of_mkApp'`.

**No `VIndCtor.WF` is used**, and in particular no F3 transport: the parameter *telescope*
`C.params` is never compared with `D.params`.  Only the parameter *terms* are, and their
typing comes from the two spines separately. -/
theorem ctor_spine_retyped (henv : env.WF) (hpi : env.PiInv U) (hΓ : OnCtx Γ (env.IsType U))
    {D : VInductDecl'} {j : Nat} {C : VIndCtor} {ls' σ : List VLevel}
    {cps fs ps : List VExpr} {Amaj : VExpr}
    (hctor : env.constants C.name = some ⟨D.uvars, C.type D j⟩)
    (hls' : ∀ l ∈ ls', l.WF U) (hls'len : ls'.length = D.uvars)
    (hσ : ∀ l ∈ σ, l.WF U) (hσlen : σ.length = D.uvars)
    (heq : List.Forall₂ (· ≈ ·) ls' σ)
    (hnp : C.params.length = D.np)
    (hcps : cps.length = D.np) (hfs : fs.length = C.fields.length)
    (hmaj : env.HasType U Γ ((VExpr.const C.name ls').mkApp (cps ++ fs)) Amaj)
    (hpseq : List.Forall₂ (env.IsDefEqU U Γ) cps ps) :
    env.HasArgs U Γ ((C.params ++ C.fields.map (·.type)).map (VExpr.instL σ)) (ps ++ fs) ∧
      env.IsDefEqU U Γ ((VExpr.const C.name ls').mkApp (cps ++ fs))
        ((VExpr.const C.name σ).mkApp (ps ++ fs)) := by
  have hps : ps.length = D.np := by
    rw [← hcps]; exact (List.Forall₂.length_eq hpseq).symm
  have hlen : (cps ++ fs).length
      = ((C.params ++ C.fields.map (·.type)).map (VExpr.instL ls')).length := by
    simp [hcps, hfs, hnp]
  have hlen2 : (ps ++ fs).length
      = ((C.params ++ C.fields.map (·.type)).map (VExpr.instL σ)).length := by
    simp [hps, hfs, hnp]
  have hty : ∀ l : List VLevel, (C.type D j).instL l
      = mkPi ((C.params ++ C.fields.map (·.type)).map (VExpr.instL l))
          ((C.canonResult D j).instL l) := by
    intro l; rw [VIndCtor.type, VExpr.instL_mkPi]
  have hconst : env.HasType U Γ (.const C.name ls')
      (mkPi ((C.params ++ C.fields.map (·.type)).map (VExpr.instL ls'))
        ((C.canonResult D j).instL ls')) := by
    have h := HasType.const (env := env) (U := U) (Γ := Γ) hctor hls' hls'len
    rwa [show (VConstant.mk D.uvars (C.type D j)).type = C.type D j from rfl, hty] at h
  have hbs := HasArgs.of_mkApp' henv hpi hΓ (cps ++ fs) hlen hconst hmaj
  rw [List.map_append] at hbs
  obtain ⟨hcpsA, hfsA⟩ := HasArgs.append_inv (by simp [hcps, hnp]) hbs
  have hDF : env.HasArgsDF U Γ
      ((C.params ++ C.fields.map (·.type)).map (VExpr.instL ls')) (cps ++ fs) (ps ++ fs) := by
    rw [List.map_append]
    exact HasArgsDF.append (HasArgsDF.ofForall₂ henv hΓ hcpsA hpseq) hfsA.toDF
  have hconstDF : env.IsDefEq U Γ (.const C.name ls') (.const C.name σ)
      (mkPi ((C.params ++ C.fields.map (·.type)).map (VExpr.instL ls'))
        ((C.canonResult D j).instL ls')) := by
    have h := VEnv.IsDefEq.constDF (env := env) (uvars := U) (Γ := Γ) hctor hls' hσ hls'len heq
    rwa [show (VConstant.mk D.uvars (C.type D j)).type = C.type D j from rfl, hty] at h
  have hmajDF := VEnv.IsDefEq.mkAppDF hDF hconstDF
  refine ⟨?_, ⟨_, hmajDF⟩⟩
  have hconstσ : env.HasType U Γ (.const C.name σ)
      (mkPi ((C.params ++ C.fields.map (·.type)).map (VExpr.instL σ))
        ((C.canonResult D j).instL σ)) := by
    have h := HasType.const (env := env) (U := U) (Γ := Γ) hctor hσ hσlen
    rwa [show (VConstant.mk D.uvars (C.type D j)).type = C.type D j from rfl, hty] at h
  exact HasArgs.of_mkApp' henv hpi hΓ (ps ++ fs) hlen2 hconstσ hmajDF.hasType.2


/-- **The constructor's stored type, unpacked.**  `env.WF` makes the *stored* type a type in
the empty context, and that alone gives the field telescope's well-formedness and the typing
of every result index — no `VIndCtor.WF`, hence no appeal to the block that declared `C`. -/
theorem ctor_type_wf (henv : env.WF) {D : VInductDecl'} {j : Nat} {C : VIndCtor}
    (hctor : env.constants C.name = some ⟨D.uvars, C.type D j⟩) :
    OnCtx ((C.params ++ C.fields.map (·.type)).reverse) (env.IsType D.uvars) ∧
      ∀ a ∈ C.args, ∃ A,
        env.HasType D.uvars ((C.params ++ C.fields.map (·.type)).reverse) a A := by
  have hci : env.IsType D.uvars [] (C.type D j) := henv.ordered.constWF hctor
  rw [VIndCtor.type] at hci
  obtain ⟨hOn, hres⟩ := VEnv.IsType.mkPi_inv henv.ordered (Γ := []) trivial hci
  rw [List.append_nil] at hOn hres
  refine ⟨hOn, fun a ha => ?_⟩
  obtain ⟨u, hu⟩ := hres
  rw [VIndCtor.canonResult, VInductDecl'.tyApp] at hu
  exact HasType.mkApp_mem henv.ordered hOn _ hu a (List.mem_append_right _ ha)

/-- **The index clause, in the direction `PatWF` needs it** (handoff obligation 4).

`VInductDecl'.iota_index_clause` (`Theory/Typing/PatternRules.lean`) proves this at the
rule's *own* match, where the matched arguments are the rule's own variables; here the match
is arbitrary, so the two sides differ by the parameter spine *and* the level list, and the
bridge is one `mkAppDF` followed by one `betaMkLams`.  The `liftN`/`instAll` arithmetic that
`iota_index_clause` does with `instAll_bvars₂` is done instead by `iota_index_slot_eq` below,
on the recursor's side. -/
theorem iota_index_clause_at (henv : env.WF) (hpi : env.PiInv U)
    (hΓ : OnCtx Γ (env.IsType U))
    {D : VInductDecl'} {j : Nat} {C : VIndCtor} {ls' σ : List VLevel}
    {cps fs ps : List VExpr}
    (hctor : env.constants C.name = some ⟨D.uvars, C.type D j⟩)
    (hls' : ∀ l ∈ ls', l.WF U) (hσ : ∀ l ∈ σ, l.WF U)
    (heq : List.Forall₂ (· ≈ ·) ls' σ)
    (hfs : fs.length = C.fields.length)
    (hargsls' : env.HasArgs U Γ
      ((C.params ++ C.fields.map (·.type)).map (VExpr.instL ls')) (cps ++ fs))
    (hargsσ : env.HasArgs U Γ
      ((C.params ++ C.fields.map (·.type)).map (VExpr.instL σ)) (ps ++ fs))
    (hcps : cps.length = D.np) (hnp : C.params.length = D.np)
    (hpseq : List.Forall₂ (env.IsDefEqU U Γ) cps ps)
    {a : VExpr} (ha : a ∈ C.args) :
    env.IsDefEqU U Γ
      (((mkLams (C.params ++ C.fields.map (·.type)) a).instL ls').mkApp (cps ++ fs))
      (VExpr.instAll (VExpr.instAll (a.instL σ) ps C.fields.length) fs 0) := by
  obtain ⟨hOn0, hargsT⟩ := ctor_type_wf henv hctor
  obtain ⟨A, haT⟩ := hargsT a ha
  -- the λ-abstracted index, typed in the empty context
  have hlamT : env.HasType D.uvars [] (mkLams (C.params ++ C.fields.map (·.type)) a)
      (mkPi (C.params ++ C.fields.map (·.type)) A) :=
    HasType.mkLams (Γ := []) (by simpa using hOn0) (by simpa using haT)
  -- the level move, at the whole λ-term
  have hlamDF : env.IsDefEq U Γ
      ((mkLams (C.params ++ C.fields.map (·.type)) a).instL ls')
      ((mkLams (C.params ++ C.fields.map (·.type)) a).instL σ)
      ((mkPi (C.params ++ C.fields.map (·.type)) A).instL ls') := by
    have h := VEnv.IsDefEq.instL_r (env := env) (U := U) (U' := D.uvars) (Γ := [])
      henv.ordered trivial hls' hσ heq hlamT
    exact (show env.IsDefEq U [] _ _ _ from h).weak0 henv.ordered
  rw [VExpr.instL_mkPi] at hlamDF
  -- the parameter move, at the spine
  have hargsls'' : env.HasArgs U Γ
      (C.params.map (VExpr.instL ls') ++ (C.fields.map (·.type)).map (VExpr.instL ls'))
      (cps ++ fs) := by rw [← List.map_append]; exact hargsls'
  obtain ⟨hcpsA, hfsA⟩ := HasArgs.append_inv (by simp [hcps, hnp]) hargsls''
  have hDF : env.HasArgsDF U Γ
      ((C.params ++ C.fields.map (·.type)).map (VExpr.instL ls')) (cps ++ fs) (ps ++ fs) := by
    rw [List.map_append]
    exact HasArgsDF.append (HasArgsDF.ofForall₂ henv hΓ hcpsA hpseq) hfsA.toDF
  have hstep1 := VEnv.IsDefEq.mkAppDF hDF hlamDF
  -- β-reduce the moved redex
  have hcc : CtxClosed (((C.params ++ C.fields.map (·.type)).map (VExpr.instL σ)).reverse) := by
    rw [← List.map_reverse]
    exact OnCtx.ctxClosed henv.ordered (OnCtx.instL hσ hOn0)
  have hOnσ : OnCtx (((C.params ++ C.fields.map (·.type)).map (VExpr.instL σ)).reverse ++ Γ)
      (env.IsType U) :=
    OnCtx.appendR henv.ordered hΓ hcc (by rw [← List.map_reverse]; exact OnCtx.instL hσ hOn0)
  have hbodyσ : env.HasType U
      (((C.params ++ C.fields.map (·.type)).map (VExpr.instL σ)).reverse ++ Γ)
      (a.instL σ) (A.instL σ) := by
    have h := HasType.instL (env := env) (U' := U) hσ haT
    rw [List.map_reverse] at h
    exact VEnv.IsDefEq.weakR henv.ordered hcc h Γ
  have hbeta := VEnv.IsDefEq.betaMkLams henv.ordered hOnσ hargsσ hbodyσ
  rw [← VExpr.instL_mkLams] at hbeta
  simp only [VExpr.instAll_append, Nat.zero_add, hfs] at hbeta
  exact IsDefEqU.trans henv hΓ ⟨_, hstep1⟩ ⟨_, hbeta⟩

end VEnv

namespace VInductDecl'

/-- **The ι-rule's left-hand side at a general concrete spine.**  `iotaLhs_instAll`
(`Theory/Inductive/StructureClosed.lean`) is this at `nm = nmin = 1`, which is all `TrProj`
needs; the ι case of `PatWF` needs it at the block's real motive and minor counts, and with
the motive/minor block opaque. -/
theorem iotaLhs_instAll' (D : VInductDecl') (j : Nat) (C : VIndCtor)
    {ls : List VLevel} {ps mid fs : List VExpr}
    (hlen : ls.length = D.recUvars)
    (hps : ps.length = D.np) (hmid : mid.length = D.nm + D.nmin)
    (hfs : fs.length = C.fields.length) :
    VExpr.instAll ((D.iotaLhs j C).instL ls) (ps ++ mid ++ fs) 0
      = (VExpr.const (Lean.mkRecName (D.types.getD j default).name) ls).mkApp
          ((ps ++ mid)
            ++ C.args.map (fun a =>
                 VExpr.instAll (VExpr.instAll (a.instL (D.selfLvls.map (VLevel.inst ls)))
                   ps C.fields.length) fs 0)
            ++ [(VExpr.const C.name (D.selfLvls.map (VLevel.inst ls))).mkApp (ps ++ fs)]) := by
  have hsslen : (ps ++ mid ++ fs).length = D.np + D.nm + D.nmin + C.fields.length := by
    simp [hps, hmid, hfs]; omega
  have hAssoc : ps ++ mid ++ fs = ps ++ (mid ++ fs) := by simp
  -- the parameter/motive/minor block
  have e1 : (bvars C.fields.length (D.np + D.nm + D.nmin)).map
      (VExpr.instAll · (ps ++ mid ++ fs) 0) = ps ++ mid := by
    rw [VExpr.map_instAll_bvars_top (Nat.zero_le _) (by rw [hsslen]; omega),
      List.take_left' (by simp [hps, hmid]; omega)]
    simp
  -- the parameter block alone, inside the constructor application
  have e2 : (bvars (C.fields.length + (D.nm + D.nmin)) D.np).map
      (VExpr.instAll · (ps ++ mid ++ fs) 0) = ps := by
    rw [VExpr.map_instAll_bvars_top (Nat.zero_le _) (by rw [hsslen]; omega), hAssoc,
      List.take_left' hps]
    simp
  -- the field block
  have e3 : (bvars 0 C.fields.length).map
      (VExpr.instAll · (ps ++ mid ++ fs) 0) = fs := VExpr.map_instAll_bvars_bot hfs
  -- the result indices
  have e4 : ∀ a : VExpr,
      VExpr.instAll
          (((a.instL (D.selfLvls.map (VLevel.inst ls))).liftN (D.nm + D.nmin)
            C.fields.length)) (ps ++ mid ++ fs) 0
        = VExpr.instAll (VExpr.instAll (a.instL (D.selfLvls.map (VLevel.inst ls)))
            ps C.fields.length) fs 0 := by
    intro a
    rw [VExpr.instAll_append, Nat.zero_add, hfs,
      VExpr.instAll_liftN_append (as := ps) (bs := mid) hmid]
  rw [D.instL_iotaLhs j C hlen, D.iotaLhs_args_split C]
  simp only [VExpr.instAll_mkApp, VExpr.instAll_const, List.map_append, List.map_cons,
    List.map_nil, e1, e2, e3]
  refine congrArg _ (congrArg (· ++ _) (congrArg _ ?_))
  rw [List.map_map]
  refine List.map_congr_left fun a _ => ?_
  show VExpr.instAll (((D.atRec a).liftN (D.nm + D.nmin) C.fields.length).instL ls)
    (ps ++ mid ++ fs) 0 = _
  rw [VInductDecl'.atRec, VExpr.instL_liftN, VExpr.instL_instL]
  exact e4 a

/-- The ι-rule's right-hand side at a saturated spine, at a general minor index `q`.
`iotaRhsBody_instAll` is this at `q = 0`. -/
theorem iotaRhsBody_instAll' (D : VInductDecl') (q : Nat) (C : VIndCtor)
    {ls : List VLevel} {spine : List VExpr} (hcl : (D.iotaLam q C).Closed)
    (hn : spine.length = (D.iotaCtx C).length) :
    VExpr.instAll (((D.iotaLam q C).mkApp (bvars 0 (D.iotaCtx C).length)).instL ls) spine 0
      = ((D.iotaLam q C).instL ls).mkApp spine := by
  rw [VExpr.instL_mkApp, VExpr.map_instL_bvars, VExpr.instAll_mkApp,
    (hcl.instL (ls := ls)).instAll_eq, VExpr.map_instAll_bvars' hn]

/-- `peelPis`' inverse, the companion of `mkLams_peelLams`. -/
theorem _root_.Lean4Lean.VExpr.mkPi_peelPis : ∀ e : VExpr,
    mkPi (VExpr.peelPis e).1 (VExpr.peelPis e).2 = e
  | .forallE A B => by rw [VExpr.peelPis_forallE, VExpr.mkPi_cons, VExpr.mkPi_peelPis B]
  | .bvar _ | .sort _ | .const .. | .app .. | .lam .. => rfl

theorem _root_.Lean4Lean.VExpr.instL_eq_mkPi_peelPis (e : VExpr) (ls : List VLevel) :
    e.instL ls = mkPi ((VExpr.peelPis e).1.map (VExpr.instL ls))
      ((VExpr.peelPis e).2.instL ls) := by
  rw [← VExpr.instL_mkPi, VExpr.mkPi_peelPis]

end VInductDecl'

/-! ## Small list lemmas -/

theorem List.forall₂_map_of_zip {α β : Type _} {f : α → VExpr} {g : β → VExpr}
    {R : VExpr → VExpr → Prop} : ∀ {P : List α} {Q : List β}, P.length = Q.length →
      (∀ xy ∈ P.zip Q, R (f xy.1) (g xy.2)) → List.Forall₂ R (P.map f) (Q.map g)
  | [], [], _, _ => .nil
  | a :: P, b :: Q, hlen, h => by
    rw [List.zip_cons_cons] at h
    exact .cons (h (a, b) (.head _))
      (List.forall₂_map_of_zip (by simpa using hlen) fun xy hxy => h xy (.tail _ hxy))

theorem List.forall₂_equiv_of_getD : ∀ {l1 l2 : List VLevel}, l1.length = l2.length →
    (∀ i, i < l1.length → l1.getD i .zero ≈ l2.getD i .zero) → List.Forall₂ (· ≈ ·) l1 l2
  | [], [], _, _ => .nil
  | a :: l1, b :: l2, hlen, h => by
    refine .cons (by simpa using h 0 (by simp)) (List.forall₂_equiv_of_getD (by simpa using hlen)
      fun i hi => ?_)
    have := h (i+1) (by simpa using hi)
    simpa using this

namespace VEnv

variable {env : VEnv} {U : Nat} {Γ : List VExpr}

theorem forall₂_isDefEqU_symm : ∀ {l1 l2 : List VExpr},
    List.Forall₂ (env.IsDefEqU U Γ) l1 l2 → List.Forall₂ (env.IsDefEqU U Γ) l2 l1
  | _, _, .nil => .nil
  | _, _, .cons h hr => .cons h.symm (forall₂_isDefEqU_symm hr)

theorem forall₂_isDefEqU_trans (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U)) :
    ∀ {l1 l2 l3 : List VExpr}, List.Forall₂ (env.IsDefEqU U Γ) l1 l2 →
      List.Forall₂ (env.IsDefEqU U Γ) l2 l3 → List.Forall₂ (env.IsDefEqU U Γ) l1 l3
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons h hr, .cons h' hr' =>
    .cons (IsDefEqU.trans henv hΓ h h') (forall₂_isDefEqU_trans henv hΓ hr hr')

/-! ## The ι case of `PatWF` -/

open Pattern (argPaths)

/-- **The ι case of `VEnv.PatWF`.**  The five steps of `patWF_quot` at general telescopes:
invert the match, invert the two typings, rebuild the spine that saturates the rule's own
context, fire the rule, and bridge back by one spine congruence.

Every one of `iotaCheck`'s three clause groups is consumed, and each at exactly one place:
the parameter clauses in `ctor_spine_retyped` (the field telescope has to be read at the
recursor's parameters, not the constructor's), the index clauses in `iota_index_clause_at`,
and the level clauses in both (`ls' ≈ σ`). -/
theorem patWF_iota (henv : env.WF) (hpi : env.PiInv U)
    {D : VInductDecl'} {j q : Nat} {T : VIndType} {C : VIndCtor}
    (hcl : (D.iotaLam q C).Closed)
    (hargsCl : ∀ a ∈ C.args, (mkLams (C.params ++ C.fields.map (·.type)) a).Closed)
    (hTj : D.types[j]? = some T)
    (hdf : env.defeqs (D.iotaRule j q C))
    (hrec : env.constants (Lean.mkRecName T.name) = some ⟨D.recUvars, D.recType j⟩)
    (hctor : env.constants C.name = some ⟨D.uvars, C.type D j⟩)
    (hnp : C.params.length = D.np) (hal : C.args.length = T.indices.length)
    {e A : VExpr} {m1 m2} (hm : (D.iotaPat T C).Matches e m1 m2)
    (hΓ : OnCtx Γ (env.IsType U)) (hT : env.HasType U Γ e A)
    (hck : (D.iotaCheckOf T C hargsCl).OK (env.IsDefEqU U Γ) m1 m2) :
    env.IsDefEqU U Γ e ((D.iotaRHSOf j q T C hcl).apply m1 m2) := by
  have hTd : D.types.getD j default = T := VInductDecl'.getD_types hTj
  -- **step 1**: invert the match
  obtain ⟨ls, ls', as, bs, haslen, hbslen, rfl, hm1l, hm1r, hasr, hbsr⟩ :=
    Pattern.matches_iota_inv (Lean.mkRecName T.name) C.name
      (m := D.np + D.nm + D.nmin + T.indices.length) (n := D.np + C.fields.length) hm
  obtain ⟨ps, mid, idxs, rfl, hpslen, hmidlen, hidxlen⟩ :
      ∃ ps mid idxs, as = ps ++ mid ++ idxs ∧ ps.length = D.np ∧
        mid.length = D.nm + D.nmin ∧ idxs.length = T.indices.length := by
    refine ⟨as.take D.np, (as.drop D.np).take (D.nm + D.nmin),
      (as.drop D.np).drop (D.nm + D.nmin), ?_, ?_, ?_, ?_⟩
    · rw [List.append_assoc, List.take_append_drop, List.take_append_drop]
    · simp [haslen]; omega
    · simp [haslen]; omega
    · simp [haslen]; omega
  obtain ⟨cps, fs, rfl, hcpslen, hfslen⟩ :
      ∃ cps fs, bs = cps ++ fs ∧ cps.length = D.np ∧ fs.length = C.fields.length := by
    refine ⟨bs.take D.np, bs.drop D.np, (List.take_append_drop ..).symm, ?_, ?_⟩
    · simp [hbslen]
    · simp [hbslen]
  -- **step 2**: the recursor's level list and declared telescope
  obtain ⟨T0, hT0⟩ := HasType.mkApp_head henv.ordered hΓ _ _ _ hT
  obtain ⟨ci, hci, hlsWF, hlslen⟩ := HasType.const_inv henv.ordered hΓ hT0
  rw [hrec] at hci; cases hci
  have hrecPi : (D.recType j).instL ls
      = mkPi ((VExpr.peelPis (D.recType j)).1.map (VExpr.instL ls))
          ((VExpr.peelPis (D.recType j)).2.instL ls) :=
    VExpr.instL_eq_mkPi_peelPis _ _
  have hfun : env.HasType U Γ (.const (Lean.mkRecName T.name) ls)
      (mkPi ((VExpr.peelPis (D.recType j)).1.map (VExpr.instL ls))
        ((VExpr.peelPis (D.recType j)).2.instL ls)) := by
    have h := HasType.const (env := env) (U := U) (Γ := Γ) hrec hlsWF hlslen
    rwa [show (VConstant.mk D.recUvars (D.recType j)).type = D.recType j from rfl,
      hrecPi] at h
  have hteleEq : (VExpr.peelPis (D.recType j)).1
      = (D.preTele ++ VExpr.liftTele (D.nm + D.nmin) (D.atRecTele T.indices))
        ++ [D.tyApp' j (T.indices.length + D.nmin + D.nm) (bvars 0 T.indices.length)] := by
    rw [D.peelPis_recType j, hTd]
  have hlenRec : ((ps ++ mid ++ idxs)
        ++ [(VExpr.const C.name ls').mkApp (cps ++ fs)]).length
      = ((VExpr.peelPis (D.recType j)).1.map (VExpr.instL ls)).length := by
    rw [List.length_map, hteleEq]
    simp [hpslen, hmidlen, hidxlen, VInductDecl'.length_atRecTele]
    omega
  have hargsRec := HasArgs.of_mkApp' henv hpi hΓ _ hlenRec hfun hT
  rw [hteleEq, List.map_append, List.map_cons, List.map_nil] at hargsRec
  obtain ⟨hAs, hmaj⟩ := HasArgs.concat_inv (env := env) (U := U) (Γ := Γ)
    (As := (D.preTele ++ VExpr.liftTele (D.nm + D.nmin) (D.atRecTele T.indices)).map
      (VExpr.instL ls))
    (as := ps ++ mid ++ idxs)
    (by rw [List.length_map]; simp [hpslen, hmidlen, hidxlen, VInductDecl'.length_atRecTele];
        omega)
    hargsRec
  rw [List.map_append] at hAs
  obtain ⟨hPre, hIdx⟩ := HasArgs.append_inv (env := env) (U := U) (Γ := Γ)
    (As := D.preTele.map (VExpr.instL ls)) (as := ps ++ mid)
    (by simp [hpslen, hmidlen]; omega) hAs
  -- **step 3**: the constructor's level list
  obtain ⟨T1, hT1⟩ := HasType.mkApp_head henv.ordered hΓ _ _ _ hmaj
  obtain ⟨ci', hci', hls'WF, hls'len⟩ := HasType.const_inv henv.ordered hΓ hT1
  rw [hctor] at hci'; cases hci'
  -- **step 4**: the three clause groups
  rw [VInductDecl'.iotaCheckOf] at hck
  obtain ⟨hpar, hidxck, hlev⟩ := iotaCheck_OK.1 hck
  have hA : ((argPaths (.const (Lean.mkRecName T.name))
        (D.np + D.nm + D.nmin + T.indices.length)).take D.np).map
        (fun p => m2 (Sum.inl p)) = ps := by
    rw [List.map_take, hasr, List.append_assoc, List.take_left' hpslen]
  have hB : ((argPaths (.const C.name) (D.np + C.fields.length)).take D.np).map
        (fun p => m2 (Sum.inr p)) = cps := by
    rw [List.map_take, hbsr, List.take_left' hcpslen]
  have hpseq : List.Forall₂ (env.IsDefEqU U Γ) cps ps := by
    refine forall₂_isDefEqU_symm ?_
    rw [← hA, ← hB]
    refine List.forall₂_map_of_zip ?_ hpar
    simp [hpslen, hcpslen]
    omega
  -- levels
  have hσlen : (D.selfLvls.map (VLevel.inst ls)).length = D.uvars := by
    simp [VInductDecl'.selfLvls]
  have hσWF : ∀ l ∈ D.selfLvls.map (VLevel.inst ls), l.WF U := by
    intro l hl
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 hl
    exact VLevel.WF.inst hlsWF
  have hlvls : List.Forall₂ (· ≈ ·) ls' (D.selfLvls.map (VLevel.inst ls)) := by
    refine List.forall₂_equiv_of_getD (by rw [hls'len, hσlen]) fun i hi => ?_
    rw [hls'len] at hi
    have h := hlev (if D.isLE then i + 1 else i, i) (by
      simp only [VInductDecl'.iotaLevelPairs, List.mem_map, List.mem_range]
      exact ⟨i, hi, rfl⟩)
    have e1 : m1 (Pattern.LPath.head (SimplePattern.iota (Lean.mkRecName T.name)
        (D.np + D.nm + D.nmin + T.indices.length) C.name (D.np + C.fields.length)).toPattern)
        = ls := hm1l _
    have e2 : m1 (iotaLeafCtor (Lean.mkRecName T.name) C.name
        (D.np + D.nm + D.nmin + T.indices.length) (D.np + C.fields.length)) = ls' := hm1r _
    rw [e1, e2] at h
    have h3 : (D.selfLvls.map (VLevel.inst ls)).getD i .zero ≈ ls'.getD i .zero := by
      rw [show ((D.selfLvls.map (VLevel.inst ls)).getD i .zero)
          = ls.getD (if D.isLE then i + 1 else i) .zero from by
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, VInductDecl'.selfLvls,
          List.getElem?_map, List.getElem?_range hi]
        rfl]
      exact h
    exact h3.symm
  -- **step 5**: the constructor spine, retyped
  obtain ⟨hargsσ, hmajEq⟩ := ctor_spine_retyped henv hpi hΓ hctor hls'WF hls'len hσWF hσlen
    hlvls hnp hcpslen hfslen hmaj hpseq
  have hargsls' : env.HasArgs U Γ
      ((C.params ++ C.fields.map (·.type)).map (VExpr.instL ls')) (cps ++ fs) := by
    have hty : ∀ l : List VLevel, (C.type D j).instL l
        = mkPi ((C.params ++ C.fields.map (·.type)).map (VExpr.instL l))
            ((C.canonResult D j).instL l) := by
      intro l; rw [VIndCtor.type, VExpr.instL_mkPi]
    have h := HasType.const (env := env) (U := U) (Γ := Γ) hctor hls'WF hls'len
    rw [show (VConstant.mk D.uvars (C.type D j)).type = C.type D j from rfl, hty] at h
    exact HasArgs.of_mkApp' henv hpi hΓ _ (by simp [hcpslen, hfslen, hnp]) h hmaj
  -- **step 6**: the index clauses
  have hI1 : ((argPaths (.const (Lean.mkRecName T.name))
        (D.np + D.nm + D.nmin + T.indices.length)).drop (D.np + D.nm + D.nmin)).map
        (fun p => m2 (Sum.inl p)) = idxs := by
    rw [List.map_drop, hasr, List.drop_left' (by simp [hpslen, hmidlen]; omega)]
  have hI2 : (D.iotaComputed T C hargsCl).map (Pattern.RHS.apply m1 m2)
      = C.args.map (fun a =>
          ((mkLams (C.params ++ C.fields.map (·.type)) a).instL ls').mkApp (cps ++ fs)) := by
    rw [VInductDecl'.iotaComputed]
    refine List.map_pmap_eq_map _ _ _ (fun a hcla => ?_) _ _
    refine (Pattern.RHS.apply_mkApp _ _).trans ?_
    rw [VInductDecl'.ctorArgRHS]
    refine congr (congrArg VExpr.mkApp ?_) ((List.map_map ..).trans hbsr)
    exact congrArg (fun l => VExpr.instL l (mkLams (C.params ++ C.fields.map (·.type)) a))
      (hm1r (Pattern.LPath.head _))
  have hidxeq : List.Forall₂ (env.IsDefEqU U Γ) idxs
      (C.args.map (fun a =>
        ((mkLams (C.params ++ C.fields.map (·.type)) a).instL ls').mkApp (cps ++ fs))) := by
    rw [← hI1, ← hI2]
    refine List.forall₂_map_of_zip ?_ hidxck
    have h1 := congrArg List.length hI1
    have h2 := congrArg List.length hI2
    simp only [List.length_map] at h1 h2
    rw [h1, h2, hidxlen, hal]
  have hidxFinal : List.Forall₂ (env.IsDefEqU U Γ) idxs
      (C.args.map (fun a => VExpr.instAll
        (VExpr.instAll (a.instL (D.selfLvls.map (VLevel.inst ls))) ps C.fields.length) fs 0)) :=
    forall₂_isDefEqU_trans henv hΓ hidxeq
      (List.forall₂_map_map fun a ha =>
        iota_index_clause_at henv hpi hΓ hctor hls'WF hσWF hlvls hfslen hargsls' hargsσ
          hcpslen hnp hpseq ha)
  -- **step 7**: the spine that saturates the rule's own context
  obtain ⟨-, hfieldσ⟩ := HasArgs.append_inv (env := env) (U := U) (Γ := Γ)
    (As := C.params.map (VExpr.instL (D.selfLvls.map (VLevel.inst ls)))) (as := ps)
    (by simp [hpslen, hnp]) (by rw [← List.map_append]; exact hargsσ)
  have hFieldTele : VExpr.instAllTele
        ((VExpr.liftTele (D.nm + D.nmin)
          (D.atRecTele (C.fields.map (·.type)))).map (VExpr.instL ls)) (ps ++ mid) 0
      = VExpr.instAllTele ((C.fields.map (·.type)).map
          (VExpr.instL (D.selfLvls.map (VLevel.inst ls)))) ps 0 := by
    rw [VExpr.instL_liftTele,
      show (D.atRecTele (C.fields.map (·.type))).map (VExpr.instL ls)
        = (C.fields.map (·.type)).map (VExpr.instL (D.selfLvls.map (VLevel.inst ls))) from by
        rw [VInductDecl'.atRecTele, List.map_map]
        exact List.map_congr_left fun _ _ => VExpr.instL_instL]
    exact VExpr.instAllTele_liftTele_append hmidlen
  have hSpine : env.HasArgs U Γ ((D.iotaCtx C).map (VExpr.instL ls)) ((ps ++ mid) ++ fs) := by
    rw [D.iotaCtx_eq C, List.map_append]
    exact HasArgs.append hPre (by rw [hFieldTele]; exact hfieldσ)
  -- **step 8**: fire the rule
  have hrule := VEnv.IsDefEq.extra_applied' henv hpi hΓ hdf hlsWF hlslen
    (As := D.iotaCtx C) (lhs := D.iotaLhs j C)
    (rhs := (D.iotaLam q C).mkApp (bvars 0 (D.iotaCtx C).length))
    (ty := D.iotaType j C) rfl rfl rfl hSpine
  rw [D.iotaLhs_instAll' j C hlslen hpslen hmidlen hfslen, hTd,
    D.iotaRhsBody_instAll' q C hcl (by simp [hpslen, hmidlen, hfslen]; omega)] at hrule
  -- **step 9**: the congruence back to `e`
  have hDF1 := VEnv.HasArgsDF.append hPre.toDF
    (VEnv.HasArgsDF.ofForall₂ henv hΓ hIdx hidxFinal)
  have hDFmaj : env.HasArgsDF U Γ
      (VExpr.instAllTele
        [(D.tyApp' j (T.indices.length + D.nmin + D.nm)
          (bvars 0 T.indices.length)).instL ls] (ps ++ mid ++ idxs) 0)
      [(VExpr.const C.name ls').mkApp (cps ++ fs)]
      [(VExpr.const C.name (D.selfLvls.map (VLevel.inst ls))).mkApp (ps ++ fs)] :=
    .cons (IsDefEqU.of_l henv hΓ hmajEq hmaj) .nil
  have hDFrec : env.HasArgsDF U Γ
      ((VExpr.peelPis (D.recType j)).1.map (VExpr.instL ls))
      ((ps ++ mid ++ idxs) ++ [(VExpr.const C.name ls').mkApp (cps ++ fs)])
      ((ps ++ mid ++ C.args.map (fun a => VExpr.instAll
          (VExpr.instAll (a.instL (D.selfLvls.map (VLevel.inst ls))) ps C.fields.length) fs 0))
        ++ [(VExpr.const C.name (D.selfLvls.map (VLevel.inst ls))).mkApp (ps ++ fs)]) := by
    rw [hteleEq, List.map_append, List.map_cons, List.map_nil]
    exact VEnv.HasArgsDF.append (by rw [← List.map_append] at hDF1; exact hDF1) hDFmaj
  have hcong := VEnv.IsDefEq.mkAppDF hDFrec hfun
  -- **step 10**: read the right-hand side back
  have hgoal : (D.iotaRHSOf j q T C hcl).apply m1 m2
      = ((D.iotaLam q C).instL ls).mkApp ((ps ++ mid) ++ fs) := by
    have h : (D.iotaRHSOf j q T C hcl).apply m1 m2
        = ((D.iotaLam q C).instL (m1 (Pattern.LPath.head
            (SimplePattern.iota (Lean.mkRecName T.name)
              (D.np + D.nm + D.nmin + T.indices.length) C.name
              (D.np + C.fields.length)).toPattern))).mkApp
          ((ps ++ mid ++ idxs).take (D.np + D.nm + D.nmin) ++ (cps ++ fs).drop D.np) :=
      iotaRHS_apply hasr hbsr
    have hhead : m1 (Pattern.LPath.head (SimplePattern.iota (Lean.mkRecName T.name)
        (D.np + D.nm + D.nmin + T.indices.length) C.name (D.np + C.fields.length)).toPattern)
        = ls := hm1l _
    rw [h, hhead, List.take_left' (by simp [hpslen, hmidlen]; omega),
      List.drop_left' hcpslen]
  rw [hgoal]
  exact ⟨_, IsDefEq.trans_l henv hΓ hcong hrule⟩

/-! ## `PatWF`, and `Params`, at an arbitrary well-formed environment

`Pat`'s three constructors are δ, ι and quot; `patWF_delta` (`ParamsBuild.lean`),
`patWF_iota` above and `patWF_quot` (`PatWF.lean`) cover them, so `PatWF` now holds at
**every** `VEnv.WF` environment, with `PiInv` as the only extra hypothesis.

`VEnv.IotaFree` and `patWF_of_iotaFree` (`PatWF.lean`) are subsumed; they are kept because
they carry no `PiInv`-free content that this does not. -/

/-- **`VEnv.PatWF` at an arbitrary well-formed environment**, from `PiInv`. -/
theorem patWF (henv : env.WF) (hpi : env.PiInv U) : env.PatWF U := by
  intro p r e A m1 m2 Γ hp hm hΓ hT hck
  cases hp with
  | delta hv hrule => exact patWF_delta henv hv hrule hm hΓ hT
  | iota hcl hargsCl hTj _hCT hdf hrec hctor hnp hal =>
    exact patWF_iota henv hpi hcl hargsCl hTj hdf hrec hctor hnp hal hm hΓ hT hck
  | quot hdf hlift hmk => exact patWF_quot henv hpi hdf hlift hmk hm hΓ hT hck

/-- **`VEnv.Params` at an arbitrary well-formed environment**, from `PiInv`.

This is what `Theory/Typing/ChurchRosser.lean` and `Theory/Typing/HeadReduction.lean` are
stated against, so every one of their results becomes a statement about an arbitrary
`VEnv.WF` environment. -/
@[instance_reducible] def paramsOfPiInv {env : VEnv} (henv : env.WF) (U : Nat)
    (hpi : env.PiInv U) : Params :=
  paramsOfWF henv U (patWF henv hpi)

/-! ## Non-vacuity of the ι case

Two questions, kept apart exactly as `PatWF.lean` keeps them for the quot case.

**The conclusion is not a reflexivity.**  `patWF_iota_nontrivial` below is stronger than the
quot file's one-witness check: it is universally quantified over the block, and says that at
*every* match of *every* ι-pattern whose block has at least one motive and whose constructor
does not have exactly one field more than the type has indices, the right-hand side is
syntactically different from the matched term -- their application arities differ.  So
`patWF_iota` is not discharged by `IsDefEqU.rfl` at its own hypotheses, and not for one
hand-picked block.

**A full witness is still NOT constructed.**  Nothing here builds a `VEnv.WF` environment
that registers an ι-rule *together with* a well-typed redex; that needs `addInduct'` run to
`WF` and is `Verify/`'s business (`VInductDecl'.WF.iotaCtx` supplies the rule's side
conditions there).  Do not cite this file as establishing it, and do not read
`patWF_iota_nontrivial`'s `hcl` hypothesis as evidence that one exists -- it is a hypothesis,
discharged at the call site by `Pat.iota`'s own field. -/

theorem patWF_iota_nontrivial (D : VInductDecl') (T : VIndType) (C : VIndCtor) (j q : Nat)
    (hcl : (D.iotaLam q C).Closed) (hnm : D.nm ≠ 0)
    (hnf : C.fields.length ≠ T.indices.length + 1)
    (ls ls' : List VLevel) (as bs : List VExpr)
    (hlen : as.length = D.np + D.nm + D.nmin + T.indices.length)
    (hlen' : bs.length = D.np + C.fields.length) :
    ∃ e m1 m2, (D.iotaPat T C).Matches e m1 m2 ∧
      (D.iotaRHSOf j q T C hcl).apply m1 m2 ≠ e := by
  obtain ⟨m1, m2, hm, hml, hmr, ha, hb⟩ :=
    matches_iota_paths (Lean.mkRecName T.name) C.name ls ls' as bs hlen hlen'
  refine ⟨_, m1, m2, hm, ?_⟩
  have hrhs : (D.iotaRHSOf j q T C hcl).apply m1 m2
      = ((D.iotaLam q C).instL (m1 (Pattern.LPath.head
          (SimplePattern.iota (Lean.mkRecName T.name)
            (D.np + D.nm + D.nmin + T.indices.length) C.name
            (D.np + C.fields.length)).toPattern))).mkApp
        (as.take (D.np + D.nm + D.nmin) ++ bs.drop D.np) := iotaRHS_apply ha hb
  intro h0
  have h := hrhs.symm.trans h0
  -- the right-hand side's head is a `mkLams` over a non-empty telescope, hence a `lam`
  have hlam : ((D.iotaLam q C).instL (m1 (Pattern.LPath.head
      (SimplePattern.iota (Lean.mkRecName T.name)
        (D.np + D.nm + D.nmin + T.indices.length) C.name
        (D.np + C.fields.length)).toPattern))).appArity = 0 := by
    rw [VInductDecl'.iotaLam, VExpr.instL_mkLams]
    match hh : (D.iotaCtx C).map (VExpr.instL (m1 (Pattern.LPath.head _))) with
    | [] =>
      have := congrArg List.length hh
      simp only [List.length_map, VInductDecl'.length_iotaCtx, List.length_nil] at this
      omega
    | A :: As => rfl
  have harity := congrArg VExpr.appArity h
  rw [VExpr.appArity_mkApp, VExpr.appArity_mkApp, hlam,
    show (VExpr.const (Lean.mkRecName T.name) ls).appArity = 0 from rfl] at harity
  simp only [List.length_append, List.length_take, List.length_drop, List.length_cons,
    List.length_nil, hlen, hlen'] at harity
  omega

/-! ### …and its hypotheses are jointly satisfiable

`patWF_iota_nontrivial` is universally quantified, so it could in principle be vacuous.  It
is not: the smallest block -- one type, one constructor, no parameters, no indices, no
fields -- satisfies all of it, and the closedness side condition is *decided*, not assumed. -/

section Witness

private def decClosedN : ∀ (e : VExpr) (k : Nat), Decidable (e.ClosedN k)
  | .bvar i, k => inferInstanceAs (Decidable (i < k))
  | .sort _, _ => inferInstanceAs (Decidable True)
  | .const .., _ => inferInstanceAs (Decidable True)
  | .app f a, k => @instDecidableAnd _ _ (decClosedN f k) (decClosedN a k)
  | .lam t b, k => @instDecidableAnd _ _ (decClosedN t k) (decClosedN b (k+1))
  | .forallE t b, k => @instDecidableAnd _ _ (decClosedN t k) (decClosedN b (k+1))

attribute [local instance] decClosedN

def nvCtor : VIndCtor := ⟨`K, [], [], []⟩
def nvType : VIndType := ⟨`I, .sort .zero, [], [nvCtor]⟩
def nvDecl : VInductDecl' := ⟨0, [], .zero, [nvType], false⟩

theorem nvClosed : (nvDecl.iotaLam 0 nvCtor).Closed := by decide

/-- The ι-case's conclusion is **not** a reflexivity, at a machine-checked concrete block. -/
theorem patWF_iota_fires :
    ∃ e m1 m2, (nvDecl.iotaPat nvType nvCtor).Matches e m1 m2 ∧
      (nvDecl.iotaRHSOf 0 0 nvType nvCtor nvClosed).apply m1 m2 ≠ e :=
  patWF_iota_nontrivial nvDecl nvType nvCtor 0 0 nvClosed (by decide) (by decide)
    [] [] [.sort .zero, .sort .zero] [] rfl rfl

end Witness

end VEnv
end Lean4Lean
