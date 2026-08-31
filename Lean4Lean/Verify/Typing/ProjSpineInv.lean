import Lean4Lean.Verify.Typing.ConstSpineWF
import Lean4Lean.Verify.Typing.RecTypePeel
import Lean4Lean.Theory.Typing.StructureRuleFree
import Lean4Lean.Verify.Typing.Expr

/-!
# `TrProj.uniq`, reduced to a congruence

`TrProj.uniq` (`Verify/Typing/Lemmas.lean`) carried four obligations.  Three are now
discharged, and this file discharges the last *environment-side* one, leaving a single
residual that mentions no environment invariant at all:

| # | obligation | status |
|---|---|---|
| 1 | `IsStructure` uniqueness (ledger G4) | `VEnv.WF.structureUniq` (`Verify/Typing/RecTypePeel.lean`) |
| 2 | (B) `IsDefEqU.const_app_inv` at the two recorded typings | **here**, `VEnv.IsStructure.spine_inv` |
| 3 | (D) no-confusion, i.e. `s₁ = s₂` | **here**, same lemma |
| 4 | congruence for `VInductDecl'.projTerm` | open — `VEnv.ProjTermCongr` below |

(2) and (3) were blocked on one thing: `VEnv.RuleFreeHead env s` at a structure name.
`Theory/Typing/StructureRuleFree.lean` now proves it from `VEnv.WF env` and `IsStructure` as
it stands — see that file's header for why the earlier rounds' "not derivable" verdict was
wrong — so both fall out of `VEnv.constApp_inv_of_wf` in one application.

What is left, `VEnv.ProjTermCongr`, is deliberately stated at **one** context and **one**
structure name: transporting the second derivation across `hΓ` and identifying the two names
is exactly the part this file does.  It is *not* a weakened restatement of `uniq` — it is
`uniq` minus every use of an environment invariant.

## Why the residual is stated over two `TrProj` derivations rather than over the agreements

The tempting form is "`StructureAgree` + `us₁ ≈ us₂` + `ps₁ ≡ ps₂` + `ιs₁ ≡ ιs₂` + `e₁ ≡ e₂`
implies the `projTerm`s are defeq", and `VEnv.IsStructure.projData_uniq` below produces
exactly that data.  It is the wrong statement to hand to whoever proves it: a `projTerm`
congruence needs both sides *well-typed* (every step is `IsDefEq.mkAppDF`, `betaMkLams`,
`instAllCongrSort`, each of which types its subject), and the agreements alone do not give
that.  Taking the two `TrProj` derivations keeps `TrProj.wf`'s typing route available, and
costs nothing: `projData_uniq` recovers the agreements from them.
-/

namespace Lean4Lean

/-! ## 1. Obligations (B) and (D)

One application of `VEnv.constApp_inv_of_wf`, with both `RuleFreeHead` side conditions
supplied by `VEnv.IsStructure.ruleFreeHead`.  Note what is *not* needed: no `VEnv.PatWF`
(discharged in `Verify/Typing/ConstSpineWF.lean`), no `VEnv.Params`, and no hypothesis
relating `S₁` to `S₂` — the names being equal is a *conclusion*. -/

/-- **Injectivity of a structure's recorded typing.**  Two terms of two structures' types,
definitionally equal, force the structure names equal, the recorded levels equivalent, and
the recorded spines definitionally equal pointwise. -/
theorem VEnv.IsStructure.spine_inv {env : VEnv} {U : Nat} {Γ : List VExpr}
    {S₁ S₂ : Lean.Name} {D₁ D₂ : VInductDecl'} {T₁ T₂ : VIndType} {C₁ C₂ : VIndCtor}
    {us₁ us₂ : List VLevel} {as₁ as₂ : List VExpr} {e₁ e₂ : VExpr}
    (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (h₁ : env.IsStructure S₁ D₁ T₁ C₁) (h₂ : env.IsStructure S₂ D₂ T₂ C₂)
    (ht₁ : env.HasType U Γ e₁ ((VExpr.const S₁ us₁).mkApp as₁))
    (ht₂ : env.HasType U Γ e₂ ((VExpr.const S₂ us₂).mkApp as₂))
    (H : env.IsDefEqU U Γ e₁ e₂) :
    S₁ = S₂ ∧ List.Forall₂ (· ≈ ·) us₁ us₂ ∧ List.Forall₂ (env.IsDefEqU U Γ) as₁ as₂ :=
  VEnv.constApp_inv_of_wf henv U hΓ (h₁.ruleFreeHead henv) (h₂.ruleFreeHead henv)
    (ht₁.isType henv hΓ) ((H.of_l henv hΓ ht₁).uniqU henv hΓ ht₂)

/-- **Everything `TrProj.uniq` can extract about the two derivations' data.**  The name, the
block records (up to the slack `addInduct'` genuinely loses), the levels, and the two spines
split at the parameter/index boundary.

The split is where the two `length` fields of `TrProj.mk` are spent: `Forall₂` over an append
does not split without knowing the left lengths agree, and they agree only because both
derivations record `ps.length = D.np` and `StructureAgree` equates the parameter
telescopes. -/
theorem VEnv.IsStructure.projData_uniq {env : VEnv} {U : Nat} {Γ : List VExpr}
    {S₁ S₂ : Lean.Name} {D₁ D₂ : VInductDecl'} {T₁ T₂ : VIndType} {C₁ C₂ : VIndCtor}
    {us₁ us₂ : List VLevel} {ps₁ ps₂ ιs₁ ιs₂ : List VExpr} {e₁ e₂ : VExpr}
    (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (h₁ : env.IsStructure S₁ D₁ T₁ C₁) (h₂ : env.IsStructure S₂ D₂ T₂ C₂)
    (ht₁ : env.HasType U Γ e₁ ((VExpr.const S₁ us₁).mkApp (ps₁ ++ ιs₁)))
    (ht₂ : env.HasType U Γ e₂ ((VExpr.const S₂ us₂).mkApp (ps₂ ++ ιs₂)))
    (hp₁ : ps₁.length = D₁.np) (hp₂ : ps₂.length = D₂.np)
    (H : env.IsDefEqU U Γ e₁ e₂) :
    S₁ = S₂ ∧ StructureAgree D₁ T₁ C₁ D₂ T₂ C₂ ∧ StructureLvlAgree D₁ C₁ D₂ C₂ ∧
      List.Forall₂ (· ≈ ·) us₁ us₂ ∧
      List.Forall₂ (env.IsDefEqU U Γ) ps₁ ps₂ ∧ List.Forall₂ (env.IsDefEqU U Γ) ιs₁ ιs₂ := by
  obtain ⟨hS, hus, has⟩ := h₁.spine_inv henv hΓ h₂ ht₁ ht₂ H
  subst hS
  obtain ⟨hag, hlvl⟩ := henv.structureUniq _ _ _ _ _ _ _ h₁ h₂
  have hlen : ps₁.length = ps₂.length := by rw [hp₁, hp₂, VInductDecl'.np, hag.params]
  obtain ⟨hps, hιs⟩ := (List.Forall₂.append_of_left hlen).1 has
  exact ⟨rfl, hag, hlvl, hus, hps, hιs⟩

/-! ## 2. The residual, and the reduction -/

/-- **The one open obligation of `TrProj.uniq`.**  Congruence for the projection encoding, at
a single context and a single structure name.

Everything environment-shaped has been stripped: this asks only that `VInductDecl'.projTerm`
respects definitional equality of its subject and of the arguments the two derivations
recorded.  `VEnv.IsStructure.projData_uniq` says what that difference can be — the records
agree except for `VInductDecl'.lvl` and `VIndField.lvl` (which are `≈`), the levels are `≈`,
and the parameter/index spines are pointwise `IsDefEqU`.

Scope of the remaining work, for whoever takes it: the `≈`-in-levels half goes through
`VEnv.IsDefEq.instL_r`; the spine half is `VEnv.IsDefEq.mkAppDF` at the recursor's telescope,
whose motive and minor arguments contain `ps` *under binders* and, through
`VInductDecl'.projArgs`, contain the earlier projections — so it recurses on `i` exactly as
`projArgs` does, and each step needs the typing the `Verify/Typing/ProjGen*` family provides
for `TrProj.wf`.  It is mechanical and it is not small. -/
def VEnv.ProjTermCongr (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {S : Lean.Name} {i : Nat} {e₁ e₂ e₁' e₂' : VExpr},
    OnCtx Γ (env.IsType U) →
    TrProj env U Γ S i e₁ e₁' → TrProj env U Γ S i e₂ e₂' →
    env.IsDefEqU U Γ e₁ e₂ → env.IsDefEqU U Γ e₁' e₂'

/-- **`TrProj.uniq` from the residual.**  The two things this adds to `ProjTermCongr` are the
two the residual is not asked to do: moving the second derivation across the definitionally
equal context, and *proving the two structure names equal* rather than assuming it.

The transport is `TrProj.mk`'s fields one at a time — deliberately inline rather than via
`TrProj.defeqDFC_target` (`Verify/Typing/DefEqCtx.lean`), which is the same three lines but
sits *downstream* of `Verify/Typing/Lemmas.lean`; this file must stay upstream of it so that
`TrProj.uniq` itself can be closed here-from once the residual lands. -/
theorem TrProj.uniq_of_projTermCongr {env : VEnv} {U : Nat} {Γ₁ Γ₂ : List VExpr}
    {s₁ s₂ : Lean.Name} {i : Nat} {e₁ e₂ e₁' e₂' : VExpr}
    (henv : VEnv.WF env) (hΓ : env.IsDefEqCtx U [] Γ₁ Γ₂)
    (hcongr : env.ProjTermCongr U)
    (H1 : TrProj env U Γ₁ s₁ i e₁ e₁') (H2 : TrProj env U Γ₂ s₂ i e₂ e₂')
    (H : env.IsDefEqU U Γ₁ e₁ e₂) :
    env.IsDefEqU U Γ₁ e₁' e₂' := by
  have hΓ₁ := hΓ.isType
  -- move the second derivation into `Γ₁`, target and all
  have H2' : TrProj env U Γ₁ s₂ i e₂ e₂' := by
    let .mk hS hty hus hps hιs hi hlv hargs hιargs hF17 := H2
    exact .mk hS (hty.defeqDFC henv.ordered (hΓ.symm henv.ordered)) hus hps hιs hi hlv
      (hargs.defeqDFC henv.ordered (hΓ.symm henv.ordered))
      (hιargs.defeqDFC henv.ordered (hΓ.symm henv.ordered)) hF17
  -- the names are equal: obligation (D)
  have hname : s₁ = s₂ := by
    let .mk hS1 hty1 _ _ _ _ _ _ _ _ := H1
    let .mk hS2 hty2 _ _ _ _ _ _ _ _ := H2'
    exact (hS1.spine_inv henv hΓ₁ hS2 hty1 hty2 H).1
  subst hname
  exact hcongr hΓ₁ H1 H2' H

/-! ## 3. Splitting the residual: subject versus data

`ProjTermCongr` varies two things at once — the *subject* (`e₁ ≡ e₂`) and the *data* the two
derivations recorded (`us/ps/ιs/D/T/C`).  The subject half is cheap and is proved here; what
remains is the data half at a **fixed** subject, `VEnv.ProjDataCongr`.

The reason the subject half is cheap is structural: `VInductDecl'.projTerm` uses its subject
exactly once, as the *last* argument of the recursor spine (`projTerm_eq_app`).  So subject
congruence is one `IsDefEq.appDF` against a reflexive function part, and the only input it
needs is that the encoded term is well typed at all — which is `TrProj.wf`.  Nothing about
motives, minor premises or `projArgs` is touched. -/

/-- **`projTerm` is an application, and its subject is the argument.**  `rfl` after
reassociating the spine: `projCore`'s spine ends in `[e]`. -/
theorem VInductDecl'.projTerm_eq_app (D : VInductDecl') (T : VIndType) (C : VIndCtor)
    (us : List VLevel) (ps ιs : List VExpr) (i : Nat) (e : VExpr) :
    D.projTerm T C us ps ιs i e =
      .app ((VExpr.const (Lean.mkRecName T.name) (D.projLvls C us i)).mkApp
        (ps ++ [T.projMotive C us ps ιs i
            (D.projArgs T C us (ps.map (·.liftN (ιs.length+1))) (VExpr.bvars 1 ιs.length) i),
          C.projMinor us ps i] ++ ιs)) e := by
  rw [VInductDecl'.projTerm, VInductDecl'.projCore_eq, VExpr.mkApp_append]; rfl

/-- **The subject half of the residual, discharged.**  Definitionally equal subjects give
definitionally equal projections, at fixed recorded data.

The only hypothesis beyond `VEnv.WF` is that the projection of *one* subject is well typed;
every caller has it from `TrProj.wf`.  No `IsStructure`, no level condition, no `ProjGen*`
machinery: `projTerm`'s subject is a single spine argument, so this is `appDF` at a reflexive
function part. -/
theorem VInductDecl'.projTerm_congr_subject {env : VEnv} {U : Nat} {Γ : List VExpr}
    {D : VInductDecl'} {T : VIndType} {C : VIndCtor} {us : List VLevel}
    {ps ιs : List VExpr} {i : Nat} {e₁ e₂ : VExpr}
    (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (hwf : VExpr.WF env U Γ (D.projTerm T C us ps ιs i e₁))
    (hdf : env.IsDefEqU U Γ e₁ e₂) :
    env.IsDefEqU U Γ (D.projTerm T C us ps ιs i e₁) (D.projTerm T C us ps ιs i e₂) := by
  obtain ⟨X, hX⟩ := hwf
  simp only [VInductDecl'.projTerm_eq_app] at hX ⊢
  obtain ⟨A, B, hf, ha⟩ := VEnv.HasType.app_inv henv.ordered hΓ hX
  exact ⟨_, .appDF hf (hdf.of_l henv hΓ ha)⟩

/-- **What is left of `ProjTermCongr` once the subject is fixed**: `TrProj` is a function up
to definitional equality.  Two derivations at *the same* subject can still differ in the
`VInductDecl'`/`VIndType`/`VIndCtor` records they found and in the levels and spines they read
off its type; `VEnv.IsStructure.projData_uniq` bounds that difference.

This is strictly weaker than `ProjTermCongr` (`ProjDataCongr.projTermCongr`), and it is where
the `≈`-levels/`instL_r` and `mkAppDF`-at-the-recursor-telescope work actually lives. -/
def VEnv.ProjDataCongr (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {S : Lean.Name} {i : Nat} {e e₁' e₂' : VExpr},
    OnCtx Γ (env.IsType U) →
    TrProj env U Γ S i e e₁' → TrProj env U Γ S i e e₂' → env.IsDefEqU U Γ e₁' e₂'

/-- **`ProjTermCongr` from `ProjDataCongr`.**  The subject is moved first: a derivation
transports to a definitionally equal subject with every field but the subject's typing reused
(nothing else in `TrProj.mk` mentions the subject), and `projTerm_congr_subject` compares the
two projections of the two subjects at the *same* data.  Then `ProjDataCongr` compares the two
data at the same subject.

`hwf` is `TrProj.wf`'s statement, taken as a parameter because `TrProj.wf` lives downstream in
`Verify/Typing/Lemmas.lean`; at the use site it is `TrProj.wf` itself. -/
theorem VEnv.ProjDataCongr.projTermCongr {env : VEnv} {U : Nat} (henv : VEnv.WF env)
    (hwf : ∀ {Γ : List VExpr} {s : Lean.Name} {i : Nat} {e e' : VExpr},
      OnCtx Γ (env.IsType U) → TrProj env U Γ s i e e' → VExpr.WF env U Γ e →
      VExpr.WF env U Γ e')
    (H : env.ProjDataCongr U) : env.ProjTermCongr U := by
  intro Γ S i e₁ e₂ e₁' e₂' hΓ H1 H2 hdf
  obtain @⟨_, D, T, C, us, ps, ιs, _, _, _, HS, hty, h3, h4, h5, hi, h7, hpsA, hιsA, hF⟩ := H1
  have hty₂ : env.HasType U Γ e₂ ((VExpr.const S us).mkApp (ps ++ ιs)) :=
    (hdf.of_l henv hΓ hty).hasType.2
  have H1' : TrProj env U Γ S i e₂ (D.projTerm T C us ps ιs i e₂) :=
    .mk HS hty₂ h3 h4 h5 hi h7 hpsA hιsA hF
  have hwf₁ : VExpr.WF env U Γ (D.projTerm T C us ps ιs i e₁) :=
    hwf hΓ (.mk HS hty h3 h4 h5 hi h7 hpsA hιsA hF) ⟨_, hty⟩
  exact (D.projTerm_congr_subject henv hΓ hwf₁ hdf).trans henv hΓ (H hΓ H1' H2)

/-! ## 4. The record dependence of `projTerm`

`ProjDataCongr` compares two `projTerm`s built from *different* records `D T C`.  The records
are not arbitrary: `projData_uniq` pins them to `StructureAgree` (everything `addInduct'`
writes) plus `StructureLvlAgree` (the `lvl` fields, up to `≈`).  This section shows that the
`StructureAgree` half is enough to make the two encodings **syntactically identical**, so the
only record-shaped slack left anywhere in the residual is the `≈` in the level fields — which
enters exactly one place, `projLvls`, i.e. the recursor's level arguments.

Everything here is equational: no typing, no environment, no holes. -/

theorem VIndField.Agree.getD_type : ∀ {l₁ l₂ : List VIndField},
    List.Forall₂ VIndField.Agree l₁ l₂ → ∀ k : Nat,
    (l₁.getD k default).type = (l₂.getD k default).type
  | [], [], _, _ => rfl
  | _ :: _, _ :: _, .cons h t, k => by
    match k with
    | 0 => exact h.type
    | _+1 => exact VIndField.Agree.getD_type t _

theorem StructureAgree.field_type {D₁ D₂ : VInductDecl'} {T₁ T₂ : VIndType} {C₁ C₂ : VIndCtor}
    (hag : StructureAgree D₁ T₁ C₁ D₂ T₂ C₂) (k : Nat) :
    (C₁.fields.getD k default).type = (C₂.fields.getD k default).type :=
  VIndField.Agree.getD_type hag.fields k

theorem StructureAgree.fields_map_instL {D₁ D₂ : VInductDecl'} {T₁ T₂ : VIndType}
    {C₁ C₂ : VIndCtor} (hag : StructureAgree D₁ T₁ C₁ D₂ T₂ C₂) (us : List VLevel) :
    C₁.fields.map (fun F => F.type.instL us) = C₂.fields.map (fun F => F.type.instL us) := by
  have e : ∀ l : List VIndField, l.map (fun F => F.type.instL us)
      = (l.map (·.type)).map (fun t => VExpr.instL us t) := by
    intro l; simp [List.map_map, Function.comp_def]
  rw [e, e, hag.fields_map]

/-- The motive depends on the records only through `T.name`, `T.indices` and the `i`-th field's
*type* — all three pinned by `StructureAgree`. -/
theorem VIndType.projMotive_congr {D₁ D₂ : VInductDecl'} {T₁ T₂ : VIndType} {C₁ C₂ : VIndCtor}
    (hag : StructureAgree D₁ T₁ C₁ D₂ T₂ C₂) (us : List VLevel) (ps is : List VExpr) (i : Nat)
    (earlier : List VExpr) :
    T₁.projMotive C₁ us ps is i earlier = T₂.projMotive C₂ us ps is i earlier := by
  simp only [VIndType.projMotive, hag.tyName, hag.indices, hag.field_type i]

/-- The minor premise depends on the records only through the field *types* and their number. -/
theorem VIndCtor.projMinor_congr {D₁ D₂ : VInductDecl'} {T₁ T₂ : VIndType} {C₁ C₂ : VIndCtor}
    (hag : StructureAgree D₁ T₁ C₁ D₂ T₂ C₂) (us : List VLevel) (ps : List VExpr) (i : Nat) :
    C₁.projMinor us ps i = C₂.projMinor us ps i := by
  simp only [VIndCtor.projMinor, hag.fields_map_instL us, hag.fields_length]

/-- **The level arguments are the only place the records can still differ.**  With the `lvl`
fields *equal* the level lists coincide; `StructureLvlAgree` gives them only up to `≈`, and
that slack is what `ProjDataCongr`'s level half must still absorb. -/
theorem VInductDecl'.projLvls_congr {D₁ D₂ : VInductDecl'} {T₁ T₂ : VIndType} {C₁ C₂ : VIndCtor}
    (hag : StructureAgree D₁ T₁ C₁ D₂ T₂ C₂)
    (hl : ∀ k : Nat, (C₁.fields.getD k default).lvl = (C₂.fields.getD k default).lvl)
    (us : List VLevel) (i : Nat) : D₁.projLvls C₁ us i = D₂.projLvls C₂ us i := by
  simp only [VInductDecl'.projLvls, hag.isLE, hl i]

theorem VInductDecl'.projCore_congr {D₁ D₂ : VInductDecl'} {T₁ T₂ : VIndType} {C₁ C₂ : VIndCtor}
    (hag : StructureAgree D₁ T₁ C₁ D₂ T₂ C₂)
    (hl : ∀ k : Nat, (C₁.fields.getD k default).lvl = (C₂.fields.getD k default).lvl)
    (us : List VLevel) (ps is : List VExpr) (i : Nat) (earlier : List VExpr) (e : VExpr) :
    D₁.projCore T₁ C₁ us ps is i earlier e = D₂.projCore T₂ C₂ us ps is i earlier e := by
  rw [VInductDecl'.projCore_eq, VInductDecl'.projCore_eq, hag.tyName,
    D₁.projLvls_congr hag hl us i, T₁.projMotive_congr hag us ps is i earlier,
    C₁.projMinor_congr hag us ps i]

theorem VInductDecl'.projArgs_congr {D₁ D₂ : VInductDecl'} {T₁ T₂ : VIndType} {C₁ C₂ : VIndCtor}
    (hag : StructureAgree D₁ T₁ C₁ D₂ T₂ C₂)
    (hl : ∀ k : Nat, (C₁.fields.getD k default).lvl = (C₂.fields.getD k default).lvl)
    (us : List VLevel) : ∀ (i : Nat) (ps is : List VExpr),
    D₁.projArgs T₁ C₁ us ps is i = D₂.projArgs T₂ C₂ us ps is i
  | 0, _, _ => rfl
  | i+1, ps, is => by
    rw [VInductDecl'.projArgs, VInductDecl'.projArgs, projArgs_congr hag hl us i ps is,
      projArgs_congr hag hl us i _ _, VInductDecl'.projCore_congr hag hl]

/-- **The whole encoding, up to the level fields.**  Two structure records that agree
syntactically *and* on the `lvl` fields produce literally the same projection term.  So in
`ProjDataCongr` the record quantifiers collapse: what is left to prove is congruence in `us`,
`ps`, `ιs` (pointwise `IsDefEqU`) and in the `lvl`s (pointwise `≈`), at one fixed record. -/
theorem VInductDecl'.projTerm_congr_records {D₁ D₂ : VInductDecl'} {T₁ T₂ : VIndType}
    {C₁ C₂ : VIndCtor} (hag : StructureAgree D₁ T₁ C₁ D₂ T₂ C₂)
    (hl : ∀ k : Nat, (C₁.fields.getD k default).lvl = (C₂.fields.getD k default).lvl)
    (us : List VLevel) (ps ιs : List VExpr) (i : Nat) (e : VExpr) :
    D₁.projTerm T₁ C₁ us ps ιs i e = D₂.projTerm T₂ C₂ us ps ιs i e := by
  rw [VInductDecl'.projTerm, VInductDecl'.projTerm,
    VInductDecl'.projArgs_congr hag hl, VInductDecl'.projCore_congr hag hl]

/-! ## 5. Non-vacuity

`ProjTermCongr` is not trivially satisfiable-by-accident and not trivially false:

* it is **implied by** `TrProj.uniq` (take `Γ₁ = Γ₂ = Γ`, `hΓ := IsDefEqCtx.refl`), so
  assuming it assumes nothing beyond the goal — no hypothesis has been smuggled in;
* it is **not vacuous**, because `TrProj` derivations exist at real environments:
  `Verify/StructureBridge.lean` builds them, and `Verify/Typing/ProjLevelWitness.lean`'s
  `barEnv_IsStructure` supplies the `IsStructure` they need.

A reflexivity check on the statement is *not* available in this file: it needs `TrProj.wf`
to know the encoded term is well-typed, and `wf` lives downstream in
`Verify/Typing/Lemmas.lean`.  That is a fact about file order, not about the statement. -/

end Lean4Lean
