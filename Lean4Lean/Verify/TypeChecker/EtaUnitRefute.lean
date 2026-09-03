import Lean4Lean.Verify.TypeChecker.EtaResidual
import Lean4Lean.Verify.Typing.ConstSpineWF
import Lean4Lean.Verify.Environment.Extension
import Lean4Lean.Verify.Typing.StructureUniq

namespace Lean4Lean
namespace MutField

theorem declEnv_wf : VEnv.WF declEnv :=
  ⟨[.induct decl], .decl (.induct decl_WF declEnv_eq.choose_spec) .empty⟩

/-- The extra inhabitant of the zero-field member `A`, as an **axiom**. -/
def fooC : VConstVal where
  uvars := 0
  type := .const `MutField.A []
  name := `MutField.foo

theorem declEnv_A_isType : declEnv.IsType 0 [] (.const `MutField.A []) :=
  ⟨_, .constDF declEnv_A nofun nofun rfl .nil⟩

theorem unitEnv_eq : ∃ e,
    (VEnv.empty.addInduct' decl).bind
      (fun env => env.addConst fooC.name fooC.toVConstant) = some e := ⟨_, rfl⟩

noncomputable def unitEnv : VEnv := unitEnv_eq.choose

theorem declEnv_addConst :
    declEnv.addConst fooC.name fooC.toVConstant = some unitEnv :=
  (congrArg (fun o : Option VEnv =>
      o.bind fun env => env.addConst fooC.name fooC.toVConstant)
    declEnv_eq.choose_spec.symm).trans unitEnv_eq.choose_spec

theorem unitEnv_wf : VEnv.WF unitEnv :=
  ⟨[.axiom fooC, .induct decl],
    .decl (.axiom declEnv_A_isType declEnv_addConst)
      (.decl (.induct decl_WF declEnv_eq.choose_spec) .empty)⟩

theorem declEnv_le_unitEnv : declEnv ≤ unitEnv := VEnv.addConst_le declEnv_addConst

theorem unitEnv_foo : unitEnv.constants `MutField.foo = some ⟨0, .const `MutField.A []⟩ := by
  rw [VEnv.addConst_constants_eq declEnv_addConst]; simp [fooC]

theorem unitEnv_A : unitEnv.constants `MutField.A = some ⟨0, .sort (.succ .zero)⟩ :=
  declEnv_le_unitEnv.constants declEnv_A

theorem unitEnv_Amk : unitEnv.constants `MutField.A.mk = some ⟨0, .const `MutField.A []⟩ :=
  declEnv_le_unitEnv.constants declEnv_Amk

/-- `addConst` adds no definitional-equality rules, so `unitEnv`'s rules are `declEnv`'s. -/
theorem unitEnv_defeqs {df : VDefEq} (h : unitEnv.defeqs df) : declEnv.defeqs df := by
  rwa [VEnv.addConst_defeqs declEnv_addConst] at h

/-- `declEnv`'s only definitional-equality rules are `decl`'s ι-rules. -/
theorem declEnv_defeqs_mem {df : VDefEq} (h : declEnv.defeqs df) : df ∈ decl.iotaRules := by
  rcases VEnv.addInduct'_defeqs_inv declEnv_eq.choose_spec h with h | h
  · exact h
  · exact h.elim

/-- The two ι-rules of the block are headed by its two recursors, computed. -/
theorem decl_iotaRules_heads :
    decl.iotaRules.map (fun df => VExpr.headConst? df.lhs)
      = [some `MutField.A.rec, some `MutField.B.rec] := rfl

theorem unitEnv_ruleFreeHead {c : Lean.Name}
    (h1 : c ≠ `MutField.A.rec) (h2 : c ≠ `MutField.B.rec) : unitEnv.RuleFreeHead c := by
  intro df hdf
  have hmem := declEnv_defeqs_mem (unitEnv_defeqs hdf)
  have hh : VExpr.headConst? df.lhs
      ∈ decl.iotaRules.map (fun df => VExpr.headConst? df.lhs) := List.mem_map_of_mem hmem
  rw [decl_iotaRules_heads] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with hh | hh <;> rw [hh] <;> intro he
  · exact h1 (Option.some.inj he).symm
  · exact h2 (Option.some.inj he).symm

/-- `foo` is not a proof: its type is `A : Type`, not a proposition. -/
theorem unitEnv_foo_hasType :
    unitEnv.HasType 0 [] ((VExpr.const `MutField.foo []).mkApp [])
      ((VExpr.const `MutField.A []).mkApp []) :=
  .constDF unitEnv_foo nofun nofun rfl .nil

theorem unitEnv_A_hasType :
    unitEnv.HasType 0 [] (VExpr.const `MutField.A []) (.sort (.succ .zero)) :=
  .constDF unitEnv_A nofun nofun rfl .nil

theorem unitEnv_not_isProof_foo :
    ¬ unitEnv.IsProof 0 [] ((VExpr.const `MutField.foo []).mkApp []) := by
  rintro ⟨p, hp, hep⟩
  obtain ⟨w, hw⟩ := VEnv.WF.uniq' unitEnv_wf trivial hep unitEnv_foo_hasType
  have h1 : unitEnv.HasType 0 [] (VExpr.const `MutField.A []) (.sort .zero) :=
    VEnv.HasType.defeqU_l' unitEnv_wf trivial ⟨_, hw⟩ hp
  have h2 : (VLevel.zero : VLevel) ≈ VLevel.succ .zero :=
    VEnv.WF.sortUniq' unitEnv_wf trivial trivial trivial h1 unitEnv_A_hasType
  exact absurd (congrFun h2 []) (by simp [VLevel.eval])

theorem unitEnv_IsStructureG_0 : unitEnv.IsStructureG `MutField.A decl 0 aTy aCtor where
  types := rfl
  name := rfl
  ctors := rfl
  decl := ⟨.empty, declEnv, decl_WF, declEnv_eq.choose_spec, declEnv_le_unitEnv⟩

end MutField

/-- **No-confusion with the `IsType` premise replaced by the `¬ IsProof` premise it is only
ever used to produce.**  `VEnv.constApp_inv_of_patWF` (`Verify/Typing/ConstSpine.lean`) takes
`env.IsType U Γ ((const c ls).mkApp as)` and immediately discards it into
`IsType.not_isProof`; nothing else in the proof reads it.  The weaker premise is what a *term*
(as opposed to a type) can supply, and it is what the eta rule's left-hand side is. -/
theorem VEnv.constNoConf_of_notIsProof {env : VEnv} (henv : env.WF) (U : Nat) (hwf : env.PatWF U)
    {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U)) {c c' : Lean.Name} {ls ls' : List VLevel}
    {as as' : List VExpr}
    (hc : env.RuleFreeHead c) (hc' : env.RuleFreeHead c')
    (hnp : ¬ env.IsProof U Γ ((VExpr.const c ls).mkApp as))
    (H : env.IsDefEqU U Γ ((VExpr.const c ls).mkApp as) ((VExpr.const c' ls').mkApp as')) :
    c = c' :=
  let _inst := VEnv.paramsOfWF henv U hwf
  (@VEnv.IsDefEq.constApp_inv _inst Γ c c' ls ls' as as' H.choose hΓ
    (hc.patFreeHead henv hwf) (hc'.patFreeHead henv hwf) hnp H.choose_spec).1

namespace MutField

/-- **`VEnv.UnitEta` is FALSE at `unitEnv`.** -/
theorem unitEnv_not_unitEta : ¬ unitEnv.UnitEta := by
  intro H
  have h := H (U := 0) (Γ := []) (us := []) (ps := [])
    unitEnv_IsStructureG_0 rfl rfl rfl nofun rfl .nil unitEnv_foo_hasType
  have heq := VEnv.constNoConf_of_notIsProof unitEnv_wf 0 (VEnv.patWF_of_wf unitEnv_wf 0)
    (Γ := []) trivial (c := `MutField.foo) (c' := `MutField.A.mk)
    (ls := []) (ls' := []) (as := []) (as' := [])
    (unitEnv_ruleFreeHead (by decide) (by decide))
    (unitEnv_ruleFreeHead (by decide) (by decide))
    unitEnv_not_isProof_foo ⟨_, h⟩
  exact absurd heq (by decide)

/-- **…and so is `VEnv.StructEtaG`**, the single residual hypothesis of both eta holes. -/
theorem unitEnv_not_structEtaG : ¬ unitEnv.StructEtaG :=
  fun H => unitEnv_not_unitEta H.toUnitEta

end MutField

/-! ## Negative control: the refutation needs `Type`, and at `Prop` it provably cannot be run -/

/-- **The control.**  At a zero-field structure living in `Prop` the very instance refuted above
is a *theorem* — `IsDefEq.proofIrrel`, no new rule.  So the refutation is not an artefact of the
`UnitEta` statement: it is located exactly at the universe, and `unitEnv_not_isProof_foo` is the
step that fails when the structure is a proposition.  (`VEnv.structEta_of_prop`,
`Theory/Inductive/StructureEta.lean`, is the same observation spelled with `etaExpansion`.) -/
theorem VEnv.unitEta_instance_of_prop {env : VEnv} {U : Nat} {Γ : List VExpr}
    {S : Lean.Name} {C : VIndCtor} {us : List VLevel} {ps : List VExpr} {e : VExpr}
    (hprop : env.HasType U Γ ((VExpr.const S us).mkApp ps) (.sort .zero))
    (he : env.HasType U Γ e ((VExpr.const S us).mkApp ps))
    (hmk : env.HasType U Γ ((VExpr.const C.name us).mkApp ps)
      ((VExpr.const S us).mkApp ps)) :
    env.IsDefEq U Γ e ((VExpr.const C.name us).mkApp ps) ((VExpr.const S us).mkApp ps) :=
  .proofIrrel hprop he hmk

/-! ## What this does and does not say about the two holes -/

/-- **The residual of both eta holes is refuted at a well-formed environment.**

`TypeChecker.Inner.etaHoles_of_structEtaG` (`EtaResidual.lean`) reduces both
`tryEtaStructCore.WF` and `isDefEqUnitLike.WF` to the single hypothesis `c.venv.StructEtaG`.
This says that hypothesis is **false** at `MutField.unitEnv`, whose `VEnv.WF` is proved
(`MutField.unitEnv_wf`).  So `StructEtaG` is not a property of the 13-constructor
`VEnv.IsDefEq` that could be derived from `c.Ewf`; structure eta has to change the relation.

It does **not** refute either hole: the holes quantify over `VContext`, and no `VContext` has
`venv = unitEnv` while `AddInduct` has no constructors. -/
theorem MutField.etaResidual_refuted :
    VEnv.WF unitEnv ∧ ¬ unitEnv.StructEtaG ∧ ¬ unitEnv.UnitEta :=
  ⟨unitEnv_wf, unitEnv_not_structEtaG, unitEnv_not_unitEta⟩

/-! ## The refutation's geometry, `sorryAx`-free

`unitEnv_not_unitEta` inherits `sorryAx` from its two inputs and from nowhere else.  The two
are separated out here so that the *shape* of the refutation — which premises of `UnitEta` are
satisfied at `unitEnv`, and what the contradiction is — is a hole-free theorem, and only the
inputs carry taint.  Both hypotheses are inhabited: by `unitEnv_not_isProof_foo` and by
`VEnv.constNoConf_of_notIsProof` respectively, each of which is `sorryAx`-tainted through the
census holes `IsDefEqU.forallE_inv_stratified`, `IsDefEqU.weakN_iff`, `WF.rigidShapeUniqNS` and
`NormalEq.descend` — the same four `isDefEqUnitLike.WF_of_unitEta` already borrows.  So the
statements are two, and the reader can see which is which. -/
theorem MutField.unitEnv_not_unitEta_of
    (hnp : ¬ unitEnv.IsProof 0 [] ((VExpr.const `MutField.foo []).mkApp []))
    (hnc : ∀ {c c' : Lean.Name} {ls ls' : List VLevel} {as as' : List VExpr},
      unitEnv.RuleFreeHead c → unitEnv.RuleFreeHead c' →
      ¬ unitEnv.IsProof 0 [] ((VExpr.const c ls).mkApp as) →
      unitEnv.IsDefEqU 0 [] ((VExpr.const c ls).mkApp as)
        ((VExpr.const c' ls').mkApp as') → c = c') :
    ¬ unitEnv.UnitEta := by
  intro H
  have h := H (U := 0) (Γ := []) (us := []) (ps := [])
    MutField.unitEnv_IsStructureG_0 rfl rfl rfl nofun rfl .nil MutField.unitEnv_foo_hasType
  exact absurd
    (hnc (MutField.unitEnv_ruleFreeHead (by decide) (by decide))
      (MutField.unitEnv_ruleFreeHead (by decide) (by decide)) hnp ⟨_, h⟩) (by decide)

/-! ## Bonus: two hypotheses the same one-liner discharges elsewhere

`Verify/Typing/Rigidity.lean`'s `barEnv_bar_ne_ctorApp` carries `barEnv.WF` and
`barEnv.PatWF U`, with the docstring reason "`barEnv.WF` is unavailable because `VInductDecl'`
is not yet wired into `VDecl.induct`".  **That reason is stale**: `VDecl.WF.induct`
(`Theory/Typing/Env.lean`) takes a `VInductDecl'` and `barDeclEq_WF`
(`Verify/Typing/StructureUniq.lean`) is proved, so `barEnv.WF` is a one-liner and `PatWF`
then comes from `VEnv.patWF_of_wf`.  Both hypotheses fall. -/
namespace EtaUnit

theorem barEnv_wf : VEnv.WF barEnv :=
  ⟨[.induct barDeclEq], .decl (.induct barDeclEq_WF
    (barDeclEq_addInduct.trans barEnv_eq.choose_spec)) .empty⟩

/-- `barEnv_bar_ne_ctorApp` with **both** of its carried hypotheses discharged. -/
theorem barEnv_bar_ne_ctorApp' (U : Nat)
    {Γ : List VExpr} (hΓ : OnCtx Γ (barEnv.IsType U))
    (hBar : barEnv.constants `Bar = some ⟨0, VExpr.sort .zero⟩)
    {us : List VLevel} {as : List VExpr} :
    ¬ barEnv.IsDefEqU U Γ ((VExpr.const `Bar []).mkApp [])
      ((VExpr.const `Bar.mk us).mkApp as) :=
  barEnv_bar_ne_ctorApp barEnv_wf U (VEnv.patWF_of_wf barEnv_wf U) hΓ hBar

end EtaUnit

end Lean4Lean

#print axioms Lean4Lean.MutField.declEnv_wf
#print axioms Lean4Lean.MutField.unitEnv_wf
#print axioms Lean4Lean.MutField.unitEnv_IsStructureG_0
#print axioms Lean4Lean.MutField.unitEnv_foo_hasType
#print axioms Lean4Lean.MutField.unitEnv_ruleFreeHead
#print axioms Lean4Lean.MutField.unitEnv_not_isProof_foo
#print axioms Lean4Lean.VEnv.constNoConf_of_notIsProof
#print axioms Lean4Lean.MutField.unitEnv_not_unitEta
#print axioms Lean4Lean.MutField.unitEnv_not_structEtaG
#print axioms Lean4Lean.VEnv.unitEta_instance_of_prop
#print axioms Lean4Lean.MutField.unitEnv_not_unitEta_of
#print axioms Lean4Lean.EtaUnit.barEnv_wf
#print axioms Lean4Lean.EtaUnit.barEnv_bar_ne_ctorApp'
