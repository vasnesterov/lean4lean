import Lean4Lean.Verify.EqSafety

/-!
# R10: `AddInduct`'s constructor, its non-vacuity, and the `Eq` obligation

`AddInduct` (`Verify/Environment/Basic.lean`) has no constructors, and `AddInductStages`
in the same file is what it is meant to be.  This file is everything that flip needs which
is *not* already in the tree, proved against `AddInductStages` so that substituting it for
`AddInduct` is a definitional change and nothing here has to move.

* §1 — the two stage lemmas the flip's `TrEnv'` inductions still lack.
* §2 — **non-vacuity.**  `TrEnv'.induct` carries two premises, `decl.WF env` and
  `AddInduct …`.  §2 machine-checks that neither makes the other vacuous, and in
  particular that the constructor half of `VInductDecl'.WF` really fires.  This is the
  check `Theory/Inductive/Companion.lean`'s `fooComp_inconsistent` demands: a block whose
  constructor obligations are vacuously satisfied yields an inconsistency.
* §3 — the `htr` premise of `checkEqType.WF_quotReady` (`Verify/EqSafety.lean`), reduced
  to a statement about `Eq`'s *stored type* with no mention of `AddInduct` at all.
-/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

/-! ## 1. The stage lemmas the flip still lacks -/

/-- Every constant a stage adds is present in the environment it produces. -/
theorem AddIndConsts.constants_of_mem {S cs m env m₂ env₂} {n ci'}
    (H : AddIndConsts S cs m env m₂ env₂) (h : (n, ci') ∈ cs) :
    env₂.constants n = some ci' := by
  induction H with
  | nil => cases h
  | cons _ _ _ _ hadd hrest ih =>
    cases h with
    | head => exact hrest.le.constants (VEnv.addConst_self hadd)
    | tail _ h => exact ih h

/-- **No extra entries.**  A stage changes the map only at the names of its own list.

This is the anti-lie half of the relation, and it is what makes `AddInduct` a *definition* of
the map rather than a *check* on it (the shape `Theory/Inductive/CompanionResolve.lean`'s
`resolveC` argues for): `m₂` is `m₁` with exactly the block's constants inserted, so a
`VInductDecl'` that under-reports its constructors cannot be paired with a constant map that
contains them. -/
theorem AddIndConsts.find?_of_not_mem {S cs m env m₂ env₂} {n : Name}
    (H : AddIndConsts S cs m env m₂ env₂) (hwf : m.WF) (h : n ∉ cs.map (·.1)) :
    m₂.find? n = m.find? n := by
  induction H with
  | nil => rfl
  | @cons ci n₀ ci' cs m _ _ _ _ hname _ _ hfr _ _ ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at h
    rw [ih (hwf.insert _ _ hfr) h.2, hwf.find?_insert]
    simp [Ne.symm h.1]

theorem AddInductStages.find?_of_not_mem {m₁ m₂ : ConstMap} {env₁ env₂ : VEnv}
    {D : VInductDecl'} {n : Name}
    (H : AddInductStages m₁ env₁ D m₂ env₂) (hwf : m₁.WF) (h : n ∉ D.allNames) :
    m₂.find? n = m₁.find? n := by
  simp only [VInductDecl'.allNames, VInductDecl'.allConsts, List.map_append,
    List.mem_append, not_or] at h
  obtain ⟨mt, et, mc, ec, e₃, h1, h2, h3, -⟩ := H
  rw [h3.find?_of_not_mem (h2.map_wf (h1.map_wf hwf)) h.2,
    h2.find?_of_not_mem (h1.map_wf hwf) h.1.2, h1.find?_of_not_mem hwf h.1.1]

/-- The block's type constants, read off the composed stages. -/
theorem AddInductStages.constants_of_type {m₁ m₂ : ConstMap} {env₁ env₂ : VEnv}
    {D : VInductDecl'} {T : VIndType} (H : AddInductStages m₁ env₁ D m₂ env₂)
    (hT : T ∈ D.types) : env₂.constants T.name = some ⟨D.uvars, T.type⟩ :=
  VEnv.addInduct'_types H.to_addInduct hT

/-- **The induct arm of `TrEnv'.of_value`.**  An inductive block introduces no δ-rule:
every name it adds carries an `.inductInfo`/`.ctorInfo`/`.recInfo`, all three of which have
`deltaValue? = none`.  So a name with a delta value was already in the map. -/
theorem AddInductStages.of_value_arm {m₁ m₂ : ConstMap} {env₁ env₂ : VEnv} {D : VInductDecl'}
    {name ci v} (H : AddInductStages m₁ env₁ D m₂ env₂) (hwf : m₁.WF)
    (h : m₂.find? name = some ci) (hv : ci.deltaValue? = some v) :
    m₁.find? name = some ci := by
  rcases H.find?_shape hwf h with h | ⟨(⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩), -⟩
  · exact h
  all_goals simp [ConstantInfo.deltaValue?_ind, ConstantInfo.deltaValue?_ctor,
    ConstantInfo.deltaValue?_rec] at hv

/-! ## 2. Non-vacuity

`TrEnv'.induct` will carry two premises, `decl.WF env` and `AddInduct C env decl C' env'`.
`Theory/Inductive/Companion.lean`'s `fooComp_inconsistent` is the standing warning that an
inductive block admitted with *vacuously satisfied* constructor obligations is not merely
weak but **inconsistent**: `fooCompDecl` claims `Foo` has no constructors, satisfies
`VInductDecl'.WF`, and its recursor `∀ (C : Foo → Prop) (m : Foo), C m` inhabits
`falseProp`.  The mechanism there is that `VInductDecl'.WF.ctors` is staged over
`env.addIndTypes D = some env₁`, which is `none` for a block re-declaring an existing type,
so the whole constructor half of `WF` is discharged by `absurd`.

This section machine-checks that `AddInduct`'s constructor closes that door: the relation
*itself* provides the `addIndTypes = some _` that `WF.ctors` is waiting for, so the two
premises of `TrEnv'.induct` are jointly non-vacuous rather than mutually excusing. -/

/-- The stages produce the very `addIndTypes` success `VInductDecl'.WF.ctors` is staged over. -/
theorem AddInductStages.addIndTypes {m₁ m₂ : ConstMap} {env₁ env₂ : VEnv} {D : VInductDecl'}
    (H : AddInductStages m₁ env₁ D m₂ env₂) : ∃ et, env₁.addIndTypes D = some et := by
  obtain ⟨mt, et, mc, ec, e₃, h1, -, -, -⟩ := H
  exact ⟨et, h1.to_addConstList⟩

/-- **`VInductDecl'.WF`'s constructor half is not vacuous under `AddInduct`.**

Contrast `fooComp_WF` (`Theory/Inductive/Companion.lean`), where the same field is
discharged by `absurd` precisely because `addIndTypes` returns `none`.  A block that
`AddInduct` accepts cannot be in that position. -/
theorem AddInductStages.ctors_wf {m₁ m₂ : ConstMap} {env₁ env₂ : VEnv} {D : VInductDecl'}
    (H : AddInductStages m₁ env₁ D m₂ env₂) (hwf : D.WF env₁) :
    ∃ et, env₁.addIndTypes D = some et ∧
      ∀ j (T : VIndType), D.types[j]? = some T → ∀ (C : VIndCtor), C ∈ T.ctors →
        C.WF et D j T := by
  obtain ⟨et, het⟩ := H.addIndTypes
  exact ⟨et, het, fun j T hT C hC => hwf.ctors et het j T hT C hC⟩

/-- **`AddInduct` refuses a companion block outright.**  Every name the block introduces —
its types included — must be *fresh*, because each stage goes through `VEnv.addConst`.  So
the `fooCompDecl` shape (a block re-declaring an already-declared type in order to lie about
its constructors) is not merely ill-formed under `AddInduct`; it has no instance. -/
theorem AddInductStages.type_fresh {m₁ m₂ : ConstMap} {env₁ env₂ : VEnv} {D : VInductDecl'}
    {T : VIndType} (H : AddInductStages m₁ env₁ D m₂ env₂) (hT : T ∈ D.types) :
    env₁.constants T.name = none :=
  (VEnv.addInduct'_eq_some_iff.1 ⟨_, H.to_addInduct⟩).1 _ <| by
    simp only [VInductDecl'.allNames, VInductDecl'.allConsts, VInductDecl'.typeConsts,
      List.map_append, List.map_map, List.mem_append, List.mem_map]
    exact .inl (.inl ⟨T, hT, rfl⟩)

namespace R10.Wit

/-- **The witness's declaration is well-formed**, and its constructor obligation is
discharged *for real*: `VEnv.empty.addIndTypes decl` succeeds, so `WF.ctors`'s hypothesis is
inhabited and `VIndCtor.WF` for `U.unit` is a genuine obligation, met here. -/
theorem decl_WF : decl.WF VEnv.empty where
  types_ne := by simp [decl]
  params := trivial
  types := by
    rintro T hT
    simp [decl] at hT
    subst hT
    exact { indices := trivial
            isType := ⟨_, .sortDF trivial trivial (.refl _)⟩
            canon := ⟨_, .sortDF trivial trivial (.refl _)⟩ }
  ctors := by
    intro env₁ h j T hT C hC
    have hU : env₁.constants `R10.Wit.U = some ⟨0, .sort (.succ .zero)⟩ :=
      VEnv.addConstList_constants h (`R10.Wit.U, ⟨0, .sort (.succ .zero)⟩) (List.Mem.head _)
    match j, hT with
    | 0, hT =>
      simp [decl] at hT
      subst hT
      simp at hC
      subst hC
      exact { params_len := rfl
              params_eq := .zero
              fields := nofun
              args_len := rfl
              args_fresh := nofun
              args_ty := .nil
              result := VEnv.HasType.const (U := 0) hU nofun rfl }
  isLE := nofun

/-- **`TrEnv'.induct`'s two premises are jointly satisfiable, and neither excuses the
other.**  This is the replay item 4 of the brief asks for, at the concrete witness:

* both premises hold at once (`decl.WF VEnv.empty` and `AddInductStages`);
* the block is *not* of the companion shape — its one type really has a constructor, so
  `fooComp_inconsistent`'s mechanism (a recursor `∀ (C : I → Prop) (m : I), C m` with no
  minor premise) does not arise;  `R10.Wit.decl`'s recursor carries its minor premise, as
  the `decl.recConsts` computation in `Verify/Environment/Basic.lean` records;
* the constructor obligation is **discharged, not dodged**: `addIndTypes` succeeds, so
  `WF.ctors` fires and `VIndCtor.WF` for `U.unit` is a real proof. -/
theorem induct_premises_wit {m : ConstMap} (hwf : m.WF) (hfr : ∀ n, m.find? n = none) :
    ∃ m' env',
      decl.WF VEnv.empty ∧
      AddInductStages m VEnv.empty decl m' env' ∧
      (∀ T ∈ decl.types, T.ctors ≠ []) ∧
      ∃ et, VEnv.empty.addIndTypes decl = some et ∧
        ∀ j (T : VIndType), decl.types[j]? = some T → ∀ (C : VIndCtor), C ∈ T.ctors →
          C.WF et decl j T := by
  obtain ⟨m', env', H, -, -, -, -, -⟩ := addInductStages_wit hwf hfr
  refine ⟨m', env', decl_WF, H, ?_, H.ctors_wf decl_WF⟩
  rintro T hT
  simp [decl] at hT
  subst hT
  simp

end R10.Wit

/-! ## 3. The `htr` premise, with `AddInduct` taken out of it

`checkEqType.WF_quotReady` (`Verify/EqSafety.lean`) reduces `addQuot.WF`'s
`VEnv.QuotReady` obligation to one premise, `htr`: *a safe inductive `Eq` present in the
kernel environment translates to `eqConst`*.  `docs/handoff-eq-safety.md` §3 records that as
"the `AddInduct` obligation and nothing else".

That is **too pessimistic**, and this section is the correction.  `TrEnv.find?` already
hands back the model's constant at a *visible* name together with its `TrConstant`, for
every `TrEnv'` step and with no reference to which step introduced it.  What is missing is
therefore not `AddInduct` at all: it is the *identity* of the translated type, and
`TrExprS.unique` supplies that from a translation witness plus the absence of `.proj`.

So `htr` reduces to a statement about `Eq`'s **stored type**, provable — when it is
provable — from `checkEqType`'s own structural comparison, with no inductive machinery. -/

/-- **`htr`, with `AddInduct` eliminated.**  Given `Eq` visible at `safety` and a witness
that its stored type translates to `eqConst.type`, the model's `Eq` *is* `eqConst`. -/
theorem TrEnv.quotReady_of_eq_type {env : Environment} {venv : VEnv} {ci : ConstantInfo}
    (H : TrEnv safety env venv) (hfind : env.find? ``Eq = some ci) (hs : safety ≤ ci.safety)
    (hlp : ci.levelParams.length = 1)
    (huniq : TrExprS.IsUnique ci.type)
    (htr : TrExprS venv ci.levelParams [] ci.type eqConst.type) :
    venv.QuotReady := by
  obtain ⟨ci', hci', -, hlen, htrS⟩ := H.find? hfind hs
  have htype : eqConst.type = ci'.type := TrExprS.unique huniq htr htrS
  have huv : ci'.uvars = eqConst.uvars := by rw [← hlen, hlp]; rfl
  show venv.constants ``Eq = some eqConst
  rw [hci']
  cases ci'
  cases htype
  cases huv
  rfl

/-! ### 3.1 `mkForall` over a one-entry local context

`checkEqType` compares `Eq`'s stored type against `lctx.mkForall #[α] …` for a `lctx`
holding exactly the `withLocalDecl`-bound `α`.  `docs/handoff-eq-safety.md` §4 deferred
turning that into a closed `Expr`; `Lean.LocalContext.mkBinding_eq`
(`Verify/LocalContext.lean`) is the missing step, and this is its one-binder instance. -/

open Lean4Lean.LocalContext in
theorem _root_.Lean4Lean.LocalContext.mkForall_single {lctx : LocalContext} {fv : FVarId}
    {idx n ty bi kind b}
    (hfind : lctx.find? fv = some (.cdecl idx fv n ty bi kind))
    (hb : b.looseBVarRange' = 0) (hty : ty.looseBVarRange' = 0) :
    lctx.mkForall #[.fvar fv] b = .forallE n ty (b.abstract1 fv) bi := by
  show mkBinding false lctx ⟨([fv] : List FVarId).map (.fvar ·)⟩ b = _
  rw [mkBinding_eq hb (by simp) ?hlc, mkBindingList_cons (by simp) (by simp)]
  · simp [mkBindingList1, hfind]
  case hlc =>
    rintro x hx d hd
    simp at hx; subst hx
    rw [hfind] at hd; cases hd
    exact ⟨hty, by simp [Lean.LocalDecl.value?]⟩

theorem _root_.Lean4Lean.LocalContext.wf_empty : ({} : LocalContext).WF := .nil

theorem _root_.Lean4Lean.LocalContext.toList_empty : ({} : LocalContext).toList = [] := rfl

theorem _root_.Lean4Lean.LocalContext.find?_empty {fv} : ({} : LocalContext).find? fv = none := by
  rw [LocalContext.wf_empty.find?_eq_find?_toList, LocalContext.toList_empty]; rfl

theorem _root_.Lean4Lean.LocalContext.find?_mkLocalDecl_empty {fv n ty bi kind} :
    (({} : LocalContext).mkLocalDecl fv n ty bi kind).find? fv =
      some (.cdecl 0 fv n ty bi kind) := by
  rw [(LocalContext.wf_empty.mkLocalDecl LocalContext.find?_empty).find?_eq_find?_toList,
    LocalContext.mkLocalDecl_toList, LocalContext.toList_empty]
  simp [Lean.LocalDecl.fvarId]

/-! ### 3.2 The type equation `checkEqType` establishes -/

/-- The closed `Expr` `checkEqType` pins `Eq`'s stored type to, up to `==`. -/
def eqStoredType (u : Name) : Expr :=
  .forallE `α (.sort (.param u))
    (.forallE `a (.bvar 0) (.forallE `a (.bvar 1) (.sort .zero) .default) .default) .implicit

theorem mkForall_eqStoredType {fv : FVarId} {u : Name} :
    (({} : LocalContext).mkLocalDecl fv `α (.sort (.param u)) .implicit).mkForall
      #[.fvar fv] ((Expr.fvar fv).arrow ((Expr.fvar fv).arrow Expr.prop)) = eqStoredType u := by
  rw [Lean4Lean.LocalContext.mkForall_single LocalContext.find?_mkLocalDecl_empty rfl rfl]
  simp [eqStoredType, Expr.arrow, Expr.abstract1, Expr.prop]

theorem checkEqType.WF_type {env : Environment} :
    (checkEqType env).WF fun _ => ∃ (info : InductiveVal) (u : Name),
      env.find? ``Eq = some (.inductInfo info) ∧ info.levelParams = [u] ∧
      info.isUnsafe = false ∧ (info.type == eqStoredType u) := by
  intro _ h
  unfold checkEqType at h
  simp only [Environment.get] at h
  split at h <;> try contradiction
  rename_i ci hfind
  cases ci with
  | inductInfo info =>
    have hu : info.isUnsafe = false := by
      cases hu : info.isUnsafe with
      | false => rfl
      | true => simp [hu, ( · >>= · ), Except.bind, pure, Pure.pure, Except.pure] at h
    simp [hu, ( · >>= · ), Except.bind, pure, Pure.pure, Except.pure] at h
    split at h
    case h_2 => simp at h
    case h_1 u hlp =>
    split at h
    case h_2 => simp at h
    case h_1 eqRefl hct =>
    refine ⟨info, u, hfind, hlp, hu, ?_⟩
    simp only [ExprBuildT.run, ReaderT.bind, withLocalDecl, withFreshId,
      MonadLocalNameGenerator.withFreshId, withReader, MonadWithReaderOf.withReader,
      ReaderT.read, read, MonadReaderOf.read, liftM, monadLift,
      MonadLift.monadLift, withTheReader, readThe, pure_bind,
      mkForall_eqStoredType] at h
    by_cases hb : (info.type == eqStoredType u) = true
    · exact hb
    · exfalso
      simp only [bne, hb, Bool.not_false, ↓reduceIte] at h
      simp [( · >>= · ), Except.bind, ReaderT.bind] at h
  | _ => simp_all [( · >>= · ), Except.bind, pure, Pure.pure, Except.pure]

/-! ### 3.3 The translation of `Eq`'s stored type -/

theorem TrExprS.IsUnique.of_eqv {e₁ e₂ : Expr} : e₁ == e₂ → IsUnique e₂ → IsUnique e₁ := by
  simp [(· == ·)]
  induction e₁ generalizing e₂ <;> (cases e₂ <;> try change false = _ → _; rintro ⟨⟩)
  all_goals simp [Expr.eqv']; intros; subst_vars; revert ‹IsUnique ..›; simp [IsUnique]
  all_goals grind

theorem isUnique_eqStoredType {u : Name} : TrExprS.IsUnique (eqStoredType u) := by
  exact ⟨⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩⟩

theorem trExprS_eqStoredType {venv : VEnv} {u : Name} :
    TrExprS venv [u] [] (eqStoredType u) eqConst.type := by
  have hlvl : VLevel.ofLevel [u] (.param u) = some (.param 0) := by
    simp [VLevel.ofLevel]
  have hsort : ∀ Γ : List VExpr, venv.IsType 1 Γ (.sort (.param 0)) := fun _ =>
    ⟨_, .sortDF (by decide) (by decide) (.refl _)⟩
  have hBd : ∀ Γ : List VExpr, venv.IsDefEq 1 (VExpr.bvar 0 :: VExpr.sort (.param 0) :: Γ)
      ((VExpr.bvar 1).forallE (.sort .zero)) ((VExpr.bvar 1).forallE (.sort .zero))
      (.sort (.imax (.param 0) (.succ .zero))) := fun _ =>
    .forallEDF (.bvar (.succ .zero)) (.sortDF trivial trivial (.refl _))
  refine .forallE (hsort _) ⟨_, .forallEDF (.bvar .zero) (hBd [])⟩ (.sort hlvl) ?_
  refine .forallE ⟨_, .bvar .zero⟩ ⟨_, hBd []⟩ (.bvar rfl) ?_
  exact .forallE ⟨_, .bvar (.succ .zero)⟩ ⟨_, .sortDF trivial trivial (.refl _)⟩
    (.bvar rfl) (.sort rfl)

theorem _root_.Lean.Expr.eqv_symm {e₁ e₂ : Expr} (h : e₁ == e₂) : e₂ == e₁ :=
  Lean.Expr.eqv_euc h (Lean.Expr.eqv_refl e₁)

/-! ### 3.4 `htr`, discharged

Everything `checkEqType.WF_quotReady` (`Verify/EqSafety.lean`) was waiting for.  Note what
does *not* appear in the proof: `AddInduct`, `TrEnv'.induct`, `VInductDecl'`, or any
inductive machinery at all.  The `Eq` gap was never an `AddInduct` obligation. -/

theorem checkEqType.WF_quotReady_closed {env : Environment} {ves : VEnvs} (wf : ves.WF env) :
    (checkEqType env).WF fun _ => ∀ safety, (ves.venv safety).QuotReady := by
  refine (checkEqType.WF_type (env := env)).mono fun _ h safety => ?_
  obtain ⟨info, u, hfind, hlp, hu, heq⟩ := h
  have hsafe : safety ≤ (ConstantInfo.inductInfo info).safety := by
    rw [ConstantInfo.safety_inductInfo, hu]; exact DefinitionSafety.le_safe
  refine TrEnv.quotReady_of_eq_type (wf.tr (safety := safety)) hfind hsafe ?_ ?_ ?_
  · show info.levelParams.length = 1
    rw [hlp]; rfl
  · exact TrExprS.IsUnique.of_eqv heq isUnique_eqStoredType
  · show TrExprS _ info.levelParams [] info.type eqConst.type
    rw [hlp]
    exact trExprS_eqStoredType.eqv (Lean.Expr.eqv_symm heq)

/-! ## 4. G4: every ι-rule the step emits is keyed to a constant the step declares

`Theory/Inductive/CompanionResolve.lean` records **G4**: `VEnv.addInductC` threads its
recursor renaming into `recConstsC` but not into `addIndRules`, so a companion block declares
`rn (mkRecName J)` while emitting its ι-rules under `mkRecName J` — a constant it never
declared (`VInductDecl'.key_iotaRule_ne_renamed`).

`AddInduct` is built on `VEnv.addInduct'`, which has no renaming, so the defect cannot arise
here.  That is not an argument, it is the theorem below.

The statement is in the shape `VDefEq.key` consumes without naming it: `VDefEq.key` lives in
`Theory/Typing/DeltaUnique.lean`, which **cannot be imported into `Verify/`** (it and
`Verify/Environment/Lemmas.lean` both declare `VEnv.addDefEqs_le`).  Composing the two by
hand: `VInductDecl'.key_iotaRule` (`DeltaUnique.lean`) gives
`(D.iotaRule j q C).key = [Lean.mkRecName (D.types.getD j default).name, C.name]`, and
`hgetD` below identifies `D.types.getD j default` with `T`; so the two constants named here
are exactly the two names of the rule's key, and both are declared by this step. -/

theorem AddInductStages.iotaRule_declared {m₁ m₂ : ConstMap} {env₁ env₂ : VEnv}
    {D : VInductDecl'} {df : VDefEq}
    (H : AddInductStages m₁ env₁ D m₂ env₂) (hdf : df ∈ D.iotaRules) :
    ∃ (j q : Nat) (T : VIndType) (C : VIndCtor),
      D.types[j]? = some T ∧ C ∈ T.ctors ∧
      D.types.getD j default = T ∧
      df = D.iotaRule j q C ∧
      env₂.constants (Lean.mkRecName T.name) = some ⟨D.recUvars, D.recType j⟩ ∧
      env₂.constants C.name = some ⟨D.uvars, C.type D j⟩ := by
  simp only [VInductDecl'.iotaRules, List.mem_map] at hdf
  obtain ⟨⟨⟨j, C⟩, q⟩, hmem, rfl⟩ := hdf
  have hCall : (j, C) ∈ D.ctorsAll := by
    have := List.mem_map_of_mem (f := Prod.fst) hmem
    simpa using this
  obtain ⟨T, hT, hC⟩ := VInductDecl'.mem_ctorsAll hCall
  have hgetD : D.types.getD j default = T := by
    rw [List.getD_eq_getElem?_getD, hT]; rfl
  have hzip : (T, j) ∈ D.types.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?]; simpa using hT
  exact ⟨j, q, T, C, hT, hC, hgetD, rfl,
    VEnv.addInduct'_recs H.to_addInduct hzip, VEnv.addInduct'_ctors H.to_addInduct hCall⟩

/-! ## 5. What the emptiness costs, stated sharply

`Verify/Bridge.lean`'s `PreludeBridge` records that "`TrEnv` provably contains no inductive
declaration at all".  Spelled at the `VEnvs` level it is stronger than a gap: the refinement
layer's model relation is **unsatisfiable** for any kernel environment holding an inductive,
so `addDecl.WF`'s `inductDecl` branch (`Verify/Environment.lean`, `sorry`) is not an open
statement — it is a **false** one, for every declaration whose success inserts an
`.inductInfo`.  The same is true of every use of `addDecl.WF` after a `.inductDecl` step.

This is the precise price of `AddInduct`'s emptiness, and it is why the flip is not optional
cleanup. -/
theorem VEnvs.WF.no_inductInfo {ves : VEnvs} {env : Environment} (wf : ves.WF env) {n v} :
    env.constants.find? n ≠ some (.inductInfo v) :=
  (wf.tr (safety := .unsafe)).no_inductInfo

end Lean4Lean
