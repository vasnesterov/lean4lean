import Lean4Lean.Theory.SetModel.CnstRecursion

/-!
# Audit of the `.induct` residual: `InductOracleOK.staged` is refuted, not open

`SetModel/CnstRecursion.lean` reduces the whole declaration-list recursion to one
residual, `InductOracleOK`, and `docs/vacuity-ledger.md` row 11 records it as
*bounded both ways* on the strength of `not_inductOracleOK_falseProp` (not
trivially true) and `inductOracleOK_empty` (not plainly false).

**The positive bound is at the empty block, and it is the only block where the
first of the three fields holds for a non-trivial reason.**  This file measures
the field:

    staged : ∀ {env env' : VEnv}, env.addInduct' D = some env' → StagedOcc env D.allConsts

The `∀ env` is the defect signature `Theory/SetModel/CoherentWitness.lean:109`
names: nothing pins `env`.  `addInduct'` performs three `addConstList`s and one
`addDefEq` fold, and **checks no types at all** — so `VEnv.empty.addInduct' D`
succeeds for *every* `D` whose names are pairwise distinct
(`VEnv.addInduct'_eq_some_iff`).  Instantiating the field at `VEnv.empty`
therefore forces `StagedOcc VEnv.empty D.allConsts`, i.e.

> every type the block declares mentions **no constant outside the block** — and for the
> *first* type former, no constant at all, since no block name is available yet.  That last
> form is what is machine-checked here (`stagedOcc_empty_head`), and it is already enough.

`VInductDecl'.WF` demands nothing of the sort: it asks each declared type to be a
type *in the environment the block is declared over*, which is exactly where the
block's external constants live.  So the residual is **unsatisfiable at every
block one of whose declared types mentions a constant of the ambient
environment** — `inductive Box : Prop | mk : Ext → Box` over an environment
holding `Ext` is enough, and `boxDecl` below is that block with `VDecl.WF` and a
two-declaration `VEnv.WF'` history machine-checked.

Consequences, in order of severity:

1. Ledger row 11's "bounded both ways" is too kind: the residual is *refuted* at
   ordinary blocks, so no proof of it can exist and the reduction it sits in is
   vacuous exactly where inductives have content.
2. `coherentOn_cnstOf`'s `.induct` case is therefore **vacuous** for any
   declaration list containing such a block, because `OracleFits` carries
   `InductOracleOK` as a conjunct.  This is `docs/vacuity-ledger.md` row 6
   recurring *inside its own repair*: row 6 fixed an occurrence hypothesis stated
   at the wrong environment, and `staged` states one at *every* environment.
3. The repair is local and is given here as `InductOracleOK'`: keep `consts` and
   `rules`, and replace `staged` by the environment-relative field the recursion
   actually consumes.  `inductOracleOK'_of_inductOracleOK` and
   `stagedOcc_of_ordered_stages` show nothing is lost and that the new field is
   *discharged* — not assumed — for the type-former and constructor stages of
   every well-formed block.

Nothing in `CnstRecursion.lean` is edited.
-/

namespace Lean4Lean.SetModel

open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-! ## 1. `StagedOcc` plumbing -/

/-- If every member of the block is checkable at the *initial* environment, the staged
condition holds: `ConstsIn` is monotone and each `addConst` only grows the environment. -/
theorem stagedOcc_of_forall {env : VEnv} :
    ∀ {_cs : List (Name × VConstant)}, (∀ p ∈ _cs, p.2.type.ConstsIn env.contains) →
      StagedOcc env _cs
  | [], _ => trivial
  | p :: _, h => ⟨h p (.head _), fun _ hadd ↦
      stagedOcc_of_forall fun q hq ↦
        (h q (.tail _ hq)).mono fun _ ↦ (VEnv.addConst_le hadd).contains⟩

/-- Splitting the staged condition along an append: check the first block at `env`, the
second at whatever `addConstList` produces. -/
theorem stagedOcc_append {env : VEnv} :
    ∀ {cs ds : List (Name × VConstant)}, StagedOcc env cs →
      (∀ env₁, env.addConstList cs = some env₁ → StagedOcc env₁ ds) →
      StagedOcc env (cs ++ ds)
  | [], _, _, h2 => h2 _ (by simp [VEnv.addConstList])
  | p :: cs, ds, ⟨h1, h2⟩, h3 => ⟨h1, fun env₁ hadd ↦
      stagedOcc_append (h2 _ hadd) fun env₂ hadd₂ ↦ h3 env₂ (addConstList_cons.2 ⟨_, hadd, hadd₂⟩)⟩



/-! ## 2. `addInduct'` checks no types, so `staged` is a demand at `VEnv.empty`

The whole measurement is this: `env.addInduct' D = some env'` says only that the block's
names are fresh for `env` and pairwise distinct, and at `VEnv.empty` the freshness half is
free. -/

namespace SetModelAudit

/-- **`addInduct'` succeeds at the empty environment for any block it succeeds at anywhere.**
The three `addConstList`s check name freshness; nothing checks a type. -/
theorem addInduct'_empty {env env' : VEnv} {D : VInductDecl'}
    (he : env.addInduct' D = some env') : ∃ e, VEnv.empty.addInduct' D = some e :=
  VEnv.addInduct'_eq_some_iff.2 ⟨fun _ _ ↦ rfl, (VEnv.addInduct'_eq_some_iff.1 ⟨_, he⟩).2⟩

@[simp] theorem empty_contains {n : Name} : ¬ VEnv.empty.contains n := nofun

end SetModelAudit

section Refute

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ} {κ : ℕ → V} {ls : List ℕ}

/-- **The residual's first field is a demand at the empty environment.**  `staged`
quantifies over *all* `env`, and `addInduct'` never inspects a type, so the field is
instantiable at `VEnv.empty` for any block that is declarable anywhere. -/
theorem InductOracleOK.stagedOcc_empty {L : PropSplit envF nv} {o c : Name → List VLevel → V}
    {D : VInductDecl'} {env env' : VEnv} (h : InductOracleOK L κ ls o c D)
    (he : env.addInduct' D = some env') : StagedOcc VEnv.empty D.allConsts :=
  h.staged (SetModelAudit.addInduct'_empty he).choose_spec

/-- Consequently **the block's first type former must mention no constant at all** — not
even one of the ambient environment, which is where a real block's external constants live.
`VInductDecl'.WF.types` asks only that `T.type` be a type *over `env`*. -/
theorem stagedOcc_empty_head {D : VInductDecl'} {T : VIndType} {Ts : List VIndType}
    (hT : D.types = T :: Ts) (h : StagedOcc VEnv.empty D.allConsts) :
    T.type.ConstsIn fun _ ↦ False := by
  have : D.allConsts = (T.name, ⟨D.uvars, T.type⟩) ::
      (Ts.map fun T => (T.name, (⟨D.uvars, T.type⟩ : VConstant)) ) ++
        (D.ctorConsts ++ D.recConsts) := by
    simp [VInductDecl'.allConsts, VInductDecl'.typeConsts, hT]
  rw [this] at h
  exact h.1.mono fun _ hn ↦ SetModelAudit.empty_contains hn

/-- **The refutation, in general form.**  A block whose first type former's stored type
mentions any constant has no `InductOracleOK` — at any oracle, any assignment, any split. -/
theorem not_inductOracleOK_of_head_const {L : PropSplit envF nv} {o c : Name → List VLevel → V}
    {D : VInductDecl'} {T : VIndType} {Ts : List VIndType} {env env' : VEnv}
    (hT : D.types = T :: Ts) (he : env.addInduct' D = some env')
    (hc : ¬ T.type.ConstsIn fun _ ↦ False) :
    ¬ InductOracleOK L κ ls o c D :=
  fun h ↦ hc (stagedOcc_empty_head hT (h.stagedOcc_empty he))

end Refute

/-! ## 3. The witness: an ordinary block the residual rejects

`inductive Box (e : Ext) : Prop | mk : Box e` over an environment holding `axiom Ext : Prop`.
Nothing exotic: one parameter, one type former, one constructor with **no fields**.  The only
feature that matters is that the parameter's type is a constant of the ambient environment,
which is the normal situation for every inductive that is not primitive.

`Ext` is a `Prop` rather than a `Type` only to keep the `WF` witness to fifteen lines
(`VIndCtor.WF.result` is then a single `appDF`).  The refutation itself is
`not_inductOracleOK_of_head_const`, which is general: it covers `Fin : Nat → Type`, `Vector`,
and every parameterised inductive whose parameter or index types name an ambient constant. -/

namespace SetModelAudit

/-- `axiom Ext : Prop`. -/
def extAx : VConstVal := { name := `Ext, uvars := 0, type := .sort .zero }

/-- The environment after that one axiom, written in the shape `addConst` produces. -/
def extEnv : VEnv where
  constants n := if `Ext = n then some ⟨0, .sort .zero⟩ else none
  defeqs _ := False

theorem extEnv_add : VEnv.empty.addConst extAx.name extAx.toVConstant = some extEnv := rfl

theorem extEnv_Ext : extEnv.constants `Ext = some ⟨0, .sort .zero⟩ := rfl

theorem extAx_WF : extAx.toVConstant.WF VEnv.empty :=
  ⟨_, .sortDF trivial trivial (.refl _)⟩

/-- The one axiom is a well-formed declaration step. -/
theorem extAx_decl_WF : VDecl.WF VEnv.empty (.axiom extAx) extEnv :=
  .axiom extAx_WF extEnv_add

/-- `inductive Box (e : Ext) : Prop | mk : Box e`. -/
def boxDecl : VInductDecl' where
  uvars := 0
  params := [.const `Ext []]
  lvl := .zero
  isLE := false
  types := [{ name := `Box, type := .forallE (.const `Ext []) (.sort .zero), indices := [],
              ctors := [{ name := `Box.mk, params := [.const `Ext []], fields := [],
                          args := [] }] }]

theorem boxDecl_allConsts :
    boxDecl.allConsts =
      [(`Box, ⟨0, .forallE (.const `Ext []) (.sort .zero)⟩),
       (`Box.mk, ⟨0, .forallE (.const `Ext []) (.app (.const `Box []) (.bvar 0))⟩),
       (Lean.mkRecName `Box, ⟨0, boxDecl.recType 0⟩)] := rfl

/-- `Ext` occurs in the type former's stored type — this is the whole of the refutation. -/
theorem boxDecl_head_const :
    ¬ (VExpr.forallE (.const `Ext []) (.sort .zero)).ConstsIn fun _ ↦ False := fun h ↦ h.1

theorem boxDecl_names : boxDecl.allNames = [`Box, `Box.mk, Lean.mkRecName `Box] := rfl

/-- The block is declarable over `extEnv`: its three names are fresh and distinct. -/
theorem boxDecl_add : ∃ env₁, extEnv.addInduct' boxDecl = some env₁ := by
  refine VEnv.addInduct'_eq_some_iff.2 ⟨?_, ?_⟩
  · rw [boxDecl_names]
    intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    obtain rfl | rfl | rfl := hn <;> rfl
  · rw [boxDecl_names]; decide

theorem extEnv_Box_none : extEnv.constants `Box = none := rfl

/-- The type constant, in the staged environment. -/
theorem boxDecl_Box_staged {env₁ : VEnv} (he : extEnv.addIndTypes boxDecl = some env₁) :
    env₁.constants `Box = some ⟨0, .forallE (.const `Ext []) (.sort .zero)⟩ :=
  VEnv.addConstList_constants (cs := boxDecl.typeConsts) he
    (`Box, ⟨0, .forallE (.const `Ext []) (.sort .zero)⟩) (by simp [boxDecl,
      VInductDecl'.typeConsts])

theorem boxDecl_Ext_staged {env₁ : VEnv} (he : extEnv.addIndTypes boxDecl = some env₁) :
    env₁.constants `Ext = some ⟨0, .sort .zero⟩ :=
  (VEnv.addConstList_le (cs := boxDecl.typeConsts) he).constants extEnv_Ext

/-- **`boxDecl` is a well-formed inductive declaration over `extEnv`.** -/
theorem boxDecl_WF : boxDecl.WF extEnv where
  types_ne := by simp [boxDecl]
  params := ⟨trivial, _, .constDF extEnv_Ext nofun nofun rfl .nil⟩
  types := by
    intro T hT
    simp only [boxDecl, List.mem_cons, List.not_mem_nil, or_false] at hT
    subst hT
    exact { indices := ⟨trivial, _, .constDF extEnv_Ext nofun nofun rfl .nil⟩
            isType := ⟨_, .forallEDF (.constDF extEnv_Ext nofun nofun rfl .nil)
              (.sortDF trivial trivial (.refl _))⟩
            canon := ⟨_, .forallEDF (.constDF extEnv_Ext nofun nofun rfl .nil)
              (.sortDF trivial trivial (.refl _))⟩ }
  ctors := by
    intro env₁ he j T hT C hC
    match j, hT with
    | 0, hT =>
      simp only [boxDecl, List.getElem?_cons_zero, Option.some.injEq] at hT
      subst hT
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
      subst hC
      have hext : env₁.IsDefEq 0 [] (.const `Ext []) (.const `Ext []) (.sort .zero) :=
        .constDF (boxDecl_Ext_staged he) nofun nofun rfl .nil
      have hbox : env₁.HasType 0 [VExpr.const `Ext []] (.const `Box [])
          (.forallE (.const `Ext []) (.sort .zero)) :=
        .constDF (boxDecl_Box_staged he) nofun nofun rfl .nil
      exact { params_len := rfl
              params_eq := .succ .zero hext
              fields := nofun
              args_len := rfl
              args_fresh := nofun
              args_ty := .nil
              result := .appDF hbox (.bvar .zero) }
  isLE := by simp [boxDecl]

/-- **A two-declaration history ending in the block.**  So `boxDecl` is not a hypothetical:
`VEnv.WF'` reaches it, and `∀ d ∈ ds, d.noUnsafe` holds of the list. -/
theorem boxDecl_history : ∃ env₁, VEnv.WF' [.induct boxDecl, .axiom extAx] env₁ :=
  let ⟨env₁, he⟩ := boxDecl_add
  ⟨env₁, .decl (.induct boxDecl_WF he) (.decl extAx_decl_WF .empty)⟩

end SetModelAudit

/-! ## 4. The repair: properly stated, `staged` is a **theorem**, not an obligation

`coherentOn_cnstOf` uses the field exactly once, as `hok.staged hadd` at the block's *own*
environment — and at that point the recursion already has `henv₀ : env₀.Ordered` and
`hd : D.WF env₀`.  Those two suffice: the three `addConstList` stages of `addInduct'` line up
with `VInductDecl'.WF`'s own staging, and the recursor stage is `recType_isType`, which
`addInduct'_ordered_final` already discharges unconditionally.

So the residual has **two** fields, not three. -/

section Staged

theorem stagedOcc_typeConsts {env : VEnv} {D : VInductDecl'} (henv : env.Ordered)
    (h : D.WF env) : StagedOcc env D.typeConsts := by
  refine stagedOcc_of_forall fun p hp ↦ ?_
  simp only [VInductDecl'.typeConsts, List.mem_map] at hp
  obtain ⟨T, hT, rfl⟩ := hp
  exact (VEnv.IsDefEq.constsIn henv.constsIn (h.types T hT).isType.choose_spec trivial).1

theorem stagedOcc_ctorConsts {env env₁ : VEnv} {D : VInductDecl'} (henv : env.Ordered)
    (h : D.WF env) (h1 : env.addIndTypes D = some env₁) : StagedOcc env₁ D.ctorConsts := by
  have o1 := VInductDecl'.addIndTypes_ordered henv h h1
  refine stagedOcc_of_forall fun p hp ↦ ?_
  simp only [VInductDecl'.ctorConsts, List.mem_map] at hp
  obtain ⟨⟨j, C⟩, hjC, rfl⟩ := hp
  obtain ⟨T, hT, hC⟩ := VInductDecl'.mem_ctorsAll hjC
  exact (VEnv.IsDefEq.constsIn o1.constsIn
    (((h.ctors env₁ h1 j T hT C hC).constant_wf o1).choose_spec) trivial).1

theorem stagedOcc_recConsts {env env₁ env₂ : VEnv} {D : VInductDecl'} (henv : env.Ordered)
    (h : D.WF env) (h1 : env.addIndTypes D = some env₁) (h2 : env₁.addIndCtors D = some env₂) :
    StagedOcc env₂ D.recConsts := by
  have o1 := VInductDecl'.addIndTypes_ordered henv h h1
  have o2 := VInductDecl'.addIndCtors_ordered o1 h h1 h2
  have hR2 : D.RecCtx env₂ := h.recCtx h1 h2 VEnv.LE.rfl o2
  refine stagedOcc_of_forall fun p hp ↦ ?_
  simp only [VInductDecl'.recConsts, List.mem_map] at hp
  obtain ⟨⟨T, j⟩, hTj, rfl⟩ := hp
  have hT : D.types[j]? = some T := List.mk_mem_zipIdx_iff_getElem?.1 hTj
  have hj : j < D.nm := by
    rcases Nat.lt_or_ge j D.types.length with hlt | hge
    · exact hlt
    · rw [List.getElem?_eq_none hge] at hT; exact absurd hT (by simp)
  have hty := VInductDecl'.recType_isType hR2 hT hj (VInductDecl'.onCtxMinors hR2)
  exact (VEnv.IsDefEq.constsIn o2.constsIn hty.choose_spec trivial).1

/-- **`StagedOcc` at the block's own environment is a theorem.**  This is the whole content
of `InductOracleOK.staged`, and it needs nothing from the oracle, the model, or the split. -/
theorem stagedOcc_allConsts {env env' : VEnv} {D : VInductDecl'} (henv : env.Ordered)
    (h : D.WF env) (he : env.addInduct' D = some env') : StagedOcc env D.allConsts := by
  obtain ⟨env₁, env₂, env₃, h1, h2, h3, rfl⟩ := VEnv.addInduct'_stages he
  rw [VInductDecl'.allConsts, List.append_assoc]
  refine stagedOcc_append (stagedOcc_typeConsts henv h) fun e₁ he₁ ↦ ?_
  have hde : env₁ = e₁ := Option.some_inj.1 (h1.symm.trans he₁)
  subst hde
  refine stagedOcc_append (stagedOcc_ctorConsts henv h h1) fun e₂ he₂ ↦ ?_
  have hde₂ : env₂ = e₂ := Option.some_inj.1 (h2.symm.trans he₂)
  subst hde₂
  exact stagedOcc_recConsts henv h h1 h2

end Staged

/-! ## 5. The refutation at `boxDecl`, and what it costs the recursion -/

section RefuteBox

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ} {κ : ℕ → V} {ls : List ℕ}

open SetModelAudit

/-- **The residual is refuted at an ordinary well-formed block.**  `boxDecl` is
`inductive Box (e : Ext) : Prop | mk : Box e`, declared over the environment holding
`axiom Ext : Prop`; `boxDecl_WF` and `boxDecl_history` certify it. -/
theorem not_inductOracleOK_boxDecl (L : PropSplit envF nv) (o c : Name → List VLevel → V) :
    ¬ InductOracleOK L κ ls o c boxDecl :=
  not_inductOracleOK_of_head_const (Ts := []) rfl boxDecl_add.choose_spec boxDecl_head_const

/-- …hence `OracleFits` is unsatisfiable along the two-declaration history, and
`coherentOn_cnstOf`'s `.induct` case is **vacuous** there.  This is the same failure the
staged occurrence condition was introduced to repair (`docs/vacuity-ledger.md` row 6), one
level up: `StagedOcc` is the right condition, and `staged` asks for it at the wrong
environments — all of them. -/
theorem not_oracleFits_boxDecl (L : PropSplit envF nv) (o : Name → List VLevel → V) :
    ¬ OracleFits L κ ls o [.induct boxDecl, .axiom extAx] :=
  fun h ↦ not_inductOracleOK_boxDecl L o _ h.1

/-- The list is one the recursion is meant to visit: no `unsafe`/`partial` block. -/
theorem boxDecl_noUnsafe :
    ∀ d ∈ [VDecl.induct boxDecl, VDecl.axiom extAx], d.noUnsafe := by
  intro d hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  obtain rfl | rfl := hd <;> trivial

/-- **The vacuity, stated.**  Every other hypothesis of `coherentOn_cnstOf` holds of this
list — it is `VEnv.WF'`, it is `noUnsafe`, and the environment is `Ordered` — and `OracleFits`
is the one that cannot be met. -/
theorem coherentOn_cnstOf_vacuous_boxDecl (L : PropSplit envF nv) (o : Name → List VLevel → V) :
    (∃ env, VEnv.WF' [.induct boxDecl, .axiom extAx] env) ∧
      (∀ d ∈ [VDecl.induct boxDecl, VDecl.axiom extAx], d.noUnsafe) ∧
      ¬ OracleFits L κ ls o [.induct boxDecl, .axiom extAx] :=
  ⟨boxDecl_history, boxDecl_noUnsafe, not_oracleFits_boxDecl L o⟩

/-- And the `staged` field, at the environment the block is actually declared over, holds —
so the refutation is entirely about the field's `∀ env`, not about `StagedOcc`. -/
theorem stagedOcc_boxDecl : StagedOcc extEnv boxDecl.allConsts :=
  stagedOcc_allConsts (.const .empty extAx_WF extEnv_add) boxDecl_WF boxDecl_add.choose_spec

end RefuteBox

/-! ## 6. The repaired residual, and the recursion re-run over it

`InductOracleOK₂` is `InductOracleOK` minus `staged`.  §4 shows nothing is lost;
`coherentOn_cnstOf₂` shows the recursion goes through unchanged, so the *only* edit the
repair needs in `CnstRecursion.lean` is to delete the field and replace `hok.staged hadd`
by `stagedOcc_allConsts henv₀ hD hadd`. -/

section Repaired

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ} {κ : ℕ → V} {ls : List ℕ}

/-- **The residual, restated.**  Two fields: the constants inhabit their declared types, and
the ι-rules hold.  `staged` is gone — it is `stagedOcc_allConsts`. -/
structure InductOracleOK₂ (L : PropSplit envF nv) (κ : ℕ → V) (ls : List ℕ)
    (o c : Name → List VLevel → V) (D : VInductDecl') : Prop where
  consts : ∀ p ∈ D.allConsts, OracleOK L κ ls o c p.1 p.2
  rules : ∀ df ∈ D.iotaRules, DefEqOK L ⟨κ, ls, c⟩ df

/-- Nothing is lost: the refuted field was the only difference. -/
theorem InductOracleOK.to₂ {L : PropSplit envF nv} {o c : Name → List VLevel → V}
    {D : VInductDecl'} (h : InductOracleOK L κ ls o c D) : InductOracleOK₂ L κ ls o c D :=
  ⟨h.consts, h.rules⟩

def OracleStepOK₂ (L : PropSplit envF nv) (κ : ℕ → V) (ls : List ℕ)
    (o : Name → List VLevel → V) : VDecl → List VDecl → Prop
  | .axiom ci, ds =>
    OracleOK L κ ls o (cnstOf L κ ls o (.axiom ci :: ds)) ci.name ci.toVConstant
  | .quot, ds => QuotOracleOK L κ ls o (cnstOf L κ ls o (.quot :: ds))
  | .induct D, ds => InductOracleOK₂ L κ ls o (cnstOf L κ ls o (.induct D :: ds)) D
  | _, _ => True

def OracleFits₂ (L : PropSplit envF nv) (κ : ℕ → V) (ls : List ℕ)
    (o : Name → List VLevel → V) : List VDecl → Prop
  | [] => True
  | d :: ds => OracleStepOK₂ L κ ls o d ds ∧ OracleFits₂ L κ ls o ds

theorem oracleFits₂_of_oracleFits {L : PropSplit envF nv} {o : Name → List VLevel → V} :
    ∀ {ds : List VDecl}, OracleFits L κ ls o ds → OracleFits₂ L κ ls o ds
  | [], _ => trivial
  | .axiom _ :: _, h => ⟨h.1, oracleFits₂_of_oracleFits h.2⟩
  | .def _ :: _, h => ⟨trivial, oracleFits₂_of_oracleFits h.2⟩
  | .opaque _ :: _, h => ⟨trivial, oracleFits₂_of_oracleFits h.2⟩
  | .example _ :: _, h => ⟨trivial, oracleFits₂_of_oracleFits h.2⟩
  | .quot :: _, h => ⟨h.1, oracleFits₂_of_oracleFits h.2⟩
  | .induct _ :: _, h => ⟨InductOracleOK.to₂ h.1, oracleFits₂_of_oracleFits h.2⟩
  | .unsafeDef _ :: _, h => ⟨trivial, oracleFits₂_of_oracleFits h.2⟩

variable (L : PropSplit envF nv) (o : Name → List VLevel → V)
variable {R : List VExpr → List VExpr → Prop}
variable (hS : L.Stable) (hR : CtxInvariant L R)
variable (hRdF : ∀ {Γ : List VExpr} {A A' : VExpr} {u : VLevel},
  envF.IsDefEq nv Γ A A' (.sort u) → R (A' :: Γ) (A :: Γ))

include hS hR hRdF in
/-- **The recursion, over the repaired residual.**  Byte-for-byte `coherentOn_cnstOf` except
in the `.induct` case, where `hok.staged hadd` is replaced by `stagedOcc_allConsts`.  So the
repair costs the reduction nothing and removes the vacuity. -/
theorem coherentOn_cnstOf₂ :
    ∀ (ds : List VDecl) {env : VEnv}, VEnv.WF' ds env → env ≤ envF →
      (∀ d ∈ ds, d.noUnsafe) → OracleFits₂ L κ ls o ds →
      CoherentOn ⟨κ, ls, cnstOf L κ ls o ds⟩ L env
  | [], env, hwf, _, _, _ => by
    cases hwf; exact coherentOn_empty_cnstOf L κ ls o
  | d :: ds, env, hwf, hle, hnu, hfits => by
    obtain ⟨env₀, hd, hds⟩ := wf'_cons_inv hwf
    have hle₀ : env₀ ≤ envF := VEnv.LE.trans (VDecl.WF.le hd) hle
    have henv₀ : env₀.Ordered := VEnv.WF.ordered ⟨ds, hds⟩
    have hC : CoherentOn ⟨κ, ls, cnstOf L κ ls o ds⟩ L env₀ :=
      coherentOn_cnstOf₂ ds hds hle₀ (fun e he ↦ hnu e (.tail _ he)) hfits.2
    have hRd₀ : ∀ {Γ : List VExpr} {A A' : VExpr} {u : VLevel},
        env₀.IsDefEq nv Γ A A' (.sort u) → R (A' :: Γ) (A :: Γ) :=
      fun h ↦ hRdF (VEnv.IsDefEq.mono hle₀ h)
    match d, hd, hfits.1 with
    | .axiom ci, .axiom _ hadd, hok =>
      exact coherentOn_addConst L henv₀.constsClosed hadd hC
        (fun hw hw' hdd ↦ hok.congr hw hw' hdd) (fun hw hlen ↦ hok.type hw hlen)
    | .def ci, .def hci hadd, _ =>
      exact coherentOn_defEq hle₀ henv₀ hS hC hR hRd₀ hci hadd
    | .opaque ci, .opaque hci hadd, _ =>
      exact coherentOn_defConst hle₀ henv₀ hS hC hR hRd₀ hci hadd
    | .example ci, .example _, _ => exact hC
    | .unsafeDef cis, _, _ => exact (hnu _ (.head _)).elim
    | .quot, .quot hqr hadd, hok =>
      rw [addQuot_eq] at hadd
      obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.1 hadd
      have h1 := coherentOn_addConstList' L o quotConsts henv₀.constsClosed hC he
        (stagedOcc_quotConsts hqr) hok.consts
      exact coherentOn_addDefEq h1 (fun {_} hw hl ↦ (hok.rule hw hl).1)
        (fun {_} hw hl ↦ (hok.rule hw hl).2)
    | .induct D, .induct hD hadd, hok =>
      obtain ⟨e, he, rfl⟩ := addInduct'_iff.1 hadd
      have h1 := coherentOn_addConstList' L o D.allConsts henv₀.constsClosed hC he
        (stagedOcc_allConsts henv₀ hD hadd) hok.consts
      exact coherentOn_addDefEqFold D.iotaRules h1 (fun df hdf ↦ hok.rules df hdf)

end Repaired

/-! ## 7. What the refutation costs `upper_bound_of`

`ModelFitsInput` (`CnstRecursion.lean` §7) asks for `ModelFits κ env ds` **uniformly**, at
every well-formed `noUnsafe` pair.  `boxDecl`'s history is such a pair, and `ModelFits`
contains `OracleFits` as a conjunct.  So `ModelFitsInput` is refuted — as soon as there is a
model to instantiate it at, which is exactly what its companion input supplies.

This is `docs/vacuity-ledger.md` row 2's shape at the top of the model route: `upper_bound_of`
is a proved theorem whose second hypothesis cannot be met, so the reduction it states is
vacuous until the residual is repaired.  §6 is the repair; `ModelFits`/`ModelFitsInput` need
the same one-line change (`OracleFits` → `OracleFits₂`). -/

section Cost

/-- **`ModelFitsInput` is unsatisfiable**, given a model to test it at.  The two hypotheses are
`upper_bound_of`'s own first input and its own antecedent, so this says precisely: whenever
`upper_bound_of` has something to say, its second hypothesis is false. -/
theorem not_modelFitsInput (hA : InaccModelInput)
    (hc : Entailment.Consistent 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰) : ¬ ModelFitsInput := by
  refine hA (¬ ModelFitsInput) (fun V _ _ _ _ κ hκ hB ↦ ?_) hc
  obtain ⟨env, hwf⟩ := SetModelAudit.boxDecl_history
  obtain ⟨lvls, L, o, R, hS, hR, hRd, hfits⟩ :=
    hB V κ hκ env [.induct SetModelAudit.boxDecl, .axiom SetModelAudit.extAx] hwf
      boxDecl_noUnsafe
  exact not_oracleFits_boxDecl L o hfits

end Cost

/-! ## 8. The ledger correction, stated exactly

`docs/vacuity-ledger.md` row 11 reads *bounded both ways*, citing `inductOracleOK_empty` as
the positive bound.  That witness is the block with **no type formers**, whose `allConsts` is
`[]` — so its `staged` field is `StagedOcc env []`, i.e. `True`.  The positive bound therefore
says nothing at all about the field that is refuted, which is why the defect survived it. -/

theorem empty_block_allConsts :
    ({ uvars := 0, params := [], lvl := .zero, types := [], isLE := false }
      : VInductDecl').allConsts = [] := rfl

end Lean4Lean.SetModel
