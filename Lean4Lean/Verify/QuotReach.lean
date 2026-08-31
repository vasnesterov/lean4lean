import Lean4Lean.Verify.QuotConsts

/-!
# The reachability boundary of the quotient step

`Verify/QuotConsts.lean` closed `docs/handoff-addinduct.md` §7.1: `addQuot.WF`
(`Verify/Environment.lean`) is `addQuot.WF' wf`, which builds the four `AddQuot1` steps from
`TrExprS` derivations for the four stored quotient types, with no `False.elim` anywhere.  That
half is a **closure**, not a reduction, and this file adds nothing to it.

What this file measures is the *other* half, which §7 of that file states in prose and does not
prove: with `ves.WF env` in hand the non-initialized branch of `addQuot.WF` is **still
unreachable**, so the theorem's content today is only its trivial branch.  Prose is the wrong
place for that, because a vacuous theorem and a true one look identical from the statement.
Here it is machine-checked, and localized:

* §1–§2 — the **converses** of `checkEqType.WF_type` and `checkName.WF`: sufficient conditions
  under which those two checks *succeed*.  `checkEqType.WF_type` says what a success implies;
  `checkEqType_ok` says what makes one happen.  Only the second can witness reachability.
* §3 — a concrete `envEqInd` in which `Eq` is a genuine safe **inductive** of exactly the
  stored type `checkEqType` demands, with `Eq.refl` present.  `checkEqType envEqInd = .ok ()`
  and `Environment.addQuot envEqInd = .ok (markQuotInit …)`: the executable non-initialized
  branch — the one whose postcondition needs all four `AddQuot1` steps — is **live**.
* §4 — and `∀ ves, ¬ ves.WF envEqInd`.  So the obstruction is not in `checkEqType`, not in
  `checkName`, not in the `mkForall` computations and not in the four `AddQuot1` steps: every
  one of those is now discharged at a witness.  It is exactly that `envEqInd` has no `VEnvs`
  model, i.e. `AddInduct`'s emptiness (`VEnvs.WF.no_inductInfo`).  `addQuot_trivial_of_wf`
  states the consequence without hedging: under `ves.WF env`, `Environment.addQuot` either
  fails or returns `env` unchanged.

**These are boundary controls in the sense of `sortConv_encoding_vacuous`
(`Theory/Typing/NormalEqStrengthen.lean`): they say what the present tree *cannot* reach.**
`no_wf_envEqInd` and `addQuot_trivial_of_wf` become **false** when the `AddInduct` flip
(`docs/handoff-addinduct.md` §6) lands, and must be deleted then; §1–§3 survive verbatim and
are what makes `addQuot.WF` bite the moment it does.  Nothing here presupposes the flip or
argues for it.

Corrections to standing claims, from reading the tree at commit `b58b248`:

| where | claim | correction |
|---|---|---|
| `docs/handoff-addinduct.md` §7.1 | the `AddQuot` construction "is now the only thing between the checker and a non-vacuous `addQuot.WF`", to be picked up first | Done, in `Verify/QuotConsts.lean` (`addQuot.WF'`, and `addQuot.WF` already delegates to it). The remaining obstruction is `AddInduct`'s emptiness alone, and §4 below pins it. |
| `docs/handoff-addinduct.md` §6(3) | the `checkEqType.WF` swap and `addQuot.WF`'s `TrEnv'.quot` branch are "not yet in hand" | Both landed; `Verify/Environment.lean` carries them. |
| `docs/critical-path.md` addendum | §7.1 "can proceed now" | Already complete; only the §7.2 flip decision and §7.3 remain of §7's list. |
-/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

/-! ## 1. `Eq.refl`'s stored type

`checkEqType`'s second half compares `Eq.refl`'s stored type against a two-binder `mkForall`.
The general computation is `mkForall_ofDecls` (`Verify/QuotConsts.lean` §3), which already
does the `mkBindingList_cons` iteration the handoff asked for, at any number of binders; this
is its two-binder instance. -/

def eqReflStoredType (u : Name) : Expr :=
  .forallE `α (.sort (.param u))
    (.forallE `a (.bvar 0)
      (mkApp3 (.const ``Eq [.param u]) (.bvar 1) (.bvar 0) (.bvar 0)) .default) .implicit

set_option linter.unusedSimpArgs false in
theorem mkForall_eqReflStoredType {α a : FVarId} {u : Name} (h : ¬ (a = α)) :
    ((({} : LocalContext).mkLocalDecl α `α (.sort (.param u)) .implicit).mkLocalDecl
        a `a (.fvar α)).mkForall #[.fvar α, .fvar a]
      (mkApp3 (.const ``Eq [.param u]) (.fvar α) (.fvar a) (.fvar a))
      = eqReflStoredType u := by
  rw [show ((({} : LocalContext).mkLocalDecl α `α (.sort (.param u)) .implicit).mkLocalDecl
        a `a (.fvar α)) =
      ofDecls [(a, `a, Expr.fvar α, .default),
               (α, `α, .sort (.param u), .implicit)] from rfl,
    show (#[.fvar α, .fvar a] : Array Expr) =
      ⟨([(α, `α, Expr.sort (.param u), BinderInfo.implicit),
         (a, `a, Expr.fvar α, BinderInfo.default)] : List BinderData).map
        (fun d => .fvar d.1)⟩ from rfl,
    mkForall_ofDecls (by simp [h]) (by simp [Ne.symm h]) (by simp)
      (by simp [mkApp3, Expr.looseBVarRange'])
      (by simp [Expr.looseBVarRange'])]
  simp [eqReflStoredType, Expr.abstract1, mkApp3, mkApp2, mkAppB, h, Ne.symm h, beq_iff_eq]

/-! ## 2. The converses of the two checks

`checkEqType.WF_type` and `checkName.WF` are *soundness* statements: they say what a success
implies.  Reachability needs the other direction. -/

-- The two `simp only` sets are deliberately over-complete: the monad unfoldings must all be
-- available in one pass, because the `match` on `Environment.get` only fires after `pure_bind`
-- and a split across two calls leaves `if info.isUnsafe = true` unreduced.  Which members end
-- up used is therefore an artefact of the reduction order, not a choice.
set_option linter.unusedSimpArgs false in
theorem checkEqType_ok {env : Environment} {info : InductiveVal} {u ctor : Name}
    {cinfo : ConstantInfo}
    (h1 : env.find? ``Eq = some (.inductInfo info))
    (h2 : info.isUnsafe = false) (h3 : info.levelParams = [u]) (h4 : info.ctors = [ctor])
    (h5 : info.type = eqStoredType u)
    (h6 : env.find? ctor = some cinfo) (h7 : cinfo.levelParams = [u])
    (h8 : cinfo.type = eqReflStoredType u) :
    checkEqType env = .ok () := by
  unfold checkEqType
  simp only [Environment.get, h1, h2, h3, h4, h5, h6, h7, h8,
    ExprBuildT.run, ReaderT.bind, ReaderT.pure, withLocalDecl, withFreshId,
    MonadLocalNameGenerator.withFreshId, withReader, MonadWithReaderOf.withReader,
    ReaderT.read, read, MonadReaderOf.read, liftM, monadLift,
    MonadLift.monadLift, withTheReader, readThe, pure_bind, bind_pure,
    mkForall_eqStoredType, Bool.false_eq_true, if_false, reduceIte, bne_self_eq_false]
  simp only [(· >>= ·), ReaderT.bind, ReaderT.pure, pure, Pure.pure, Except.pure, Except.bind,
    mkForall_eqStoredType, bne_self_eq_false, Bool.false_eq_true, if_false, reduceIte, h7, h8]
  rw [mkForall_eqReflStoredType (by simp [Lean.NameGenerator.curr, Lean.NameGenerator.next, Lean.FVarId.mk.injEq, Lean.Name.num.injEq])]
  simp only [bne, Lean.Expr.eqv_refl, Bool.not_true, Bool.false_eq_true, if_false,
    ReaderT.pure, pure, Pure.pure, Except.pure]

theorem checkName_ok {env : Environment} (mapWF : env.constants.WF) {n : Name}
    (h : env.find? n = none) (hp : Environment.primitives.contains n = false) :
    Environment.checkName env n = .ok () := by
  have hc : env.contains n = false := by
    change env.constants.contains n = false
    rw [mapWF.find?_isSome]
    rw [Kernel.Environment.find?, mapWF.find?'_eq_find?] at h
    simp [h]
  simp [Environment.checkName, hc, hp, pure, Except.pure]

/-! ## 3. A concrete environment on which the check succeeds

Everything in this section is about the executable checker only; no `VEnvs` appears.  `Eq` is
a safe inductive of exactly the type `checkEqType` demands and `Eq.refl` is present with
exactly the constructor type it demands -- taken as an axiom, since `checkEqType` reads only
the constructor's `levelParams` and `type`.  (An `Eq.refl` `ctorInfo` would do as well and
would change nothing below; the axiom keeps the witness small.) -/

namespace QuotReach

def eqIndVal : InductiveVal where
  name := ``Eq
  levelParams := [`u]
  type := eqStoredType `u
  numParams := 2
  numIndices := 0
  all := [``Eq]
  ctors := [``Eq.refl]
  numNested := 0
  isRec := false
  isUnsafe := false
  isReflexive := false

def eqReflAx : AxiomVal where
  name := ``Eq.refl
  levelParams := [`u]
  type := eqReflStoredType `u
  isUnsafe := false

open private Lean.Kernel.Environment.add markQuotInit from Lean.Environment

def envEqInd : Environment :=
  (QuotWit.env0.add (.inductInfo eqIndVal)).add (.axiomInfo eqReflAx)

def cm1 : ConstMap := SMap.insert QuotWit.env0.constants ``Eq (.inductInfo eqIndVal)
def cm2 : ConstMap := SMap.insert cm1 ``Eq.refl (.axiomInfo eqReflAx)

theorem constants_envEqInd : envEqInd.constants = cm2 := rfl

theorem wf1 : cm1.WF :=
  QuotWit.constants_env0_wf.insert _ _ (QuotWit.constants_env0_find? _)

theorem find?_cm1_EqRefl : cm1.find? ``Eq.refl = none := by
  show SMap.find? (SMap.insert QuotWit.env0.constants ``Eq (.inductInfo eqIndVal)) _ = _
  rw [QuotWit.constants_env0_wf.find?_insert, if_neg (by simp)]
  exact QuotWit.constants_env0_find? _

theorem wf2 : cm2.WF := wf1.insert _ _ find?_cm1_EqRefl

theorem find?_envEqInd_Eq : envEqInd.find? ``Eq = some (.inductInfo eqIndVal) := by
  show SMap.find?' cm2 _ = _
  rw [wf2.find?'_eq_find?]
  show SMap.find? (SMap.insert cm1 ``Eq.refl (.axiomInfo eqReflAx)) _ = _
  rw [wf1.find?_insert, if_neg (by simp)]
  show SMap.find? (SMap.insert QuotWit.env0.constants ``Eq (.inductInfo eqIndVal)) _ = _
  rw [QuotWit.constants_env0_wf.find?_insert, if_pos (by simp)]

theorem find?_envEqInd_EqRefl : envEqInd.find? ``Eq.refl = some (.axiomInfo eqReflAx) := by
  show SMap.find?' cm2 _ = _
  rw [wf2.find?'_eq_find?]
  show SMap.find? (SMap.insert cm1 ``Eq.refl (.axiomInfo eqReflAx)) _ = _
  rw [wf1.find?_insert, if_pos (by simp)]

/-- **`checkEqType`'s success branch is reachable.** -/
theorem checkEqType_envEqInd : checkEqType envEqInd = .ok () :=
  checkEqType_ok find?_envEqInd_Eq rfl rfl rfl rfl find?_envEqInd_EqRefl rfl rfl

theorem find?_cm2_Eq : cm2.find? ``Eq = some (.inductInfo eqIndVal) := by
  show SMap.find? (SMap.insert cm1 ``Eq.refl (.axiomInfo eqReflAx)) _ = _
  rw [wf1.find?_insert, if_neg (by simp)]
  show SMap.find? (SMap.insert QuotWit.env0.constants ``Eq (.inductInfo eqIndVal)) _ = _
  rw [QuotWit.constants_env0_wf.find?_insert, if_pos (by simp)]

theorem find?_envEqInd_none {n : Name} (h1 : ¬ ``Eq.refl = n) (h2 : ¬ ``Eq = n) :
    envEqInd.find? n = none := by
  show SMap.find?' cm2 _ = _
  rw [wf2.find?'_eq_find?]
  show SMap.find? (SMap.insert cm1 ``Eq.refl (.axiomInfo eqReflAx)) _ = _
  rw [wf1.find?_insert, if_neg (by simpa using h1)]
  show SMap.find? (SMap.insert QuotWit.env0.constants ``Eq (.inductInfo eqIndVal)) _ = _
  rw [QuotWit.constants_env0_wf.find?_insert, if_neg (by simpa using h2)]
  exact QuotWit.constants_env0_find? _

theorem wf2' : envEqInd.constants.WF := wf2

theorem prim_Quot : Environment.primitives.contains ``Quot = false := by
  simp [Environment.primitives, NameSet.contains, NameSet.ofList]
theorem prim_QuotMk : Environment.primitives.contains ``Quot.mk = false := by
  simp [Environment.primitives, NameSet.contains, NameSet.ofList]
theorem prim_QuotLift : Environment.primitives.contains ``Quot.lift = false := by
  simp [Environment.primitives, NameSet.contains, NameSet.ofList]
theorem prim_QuotInd : Environment.primitives.contains ``Quot.ind = false := by
  simp [Environment.primitives, NameSet.contains, NameSet.ofList]

theorem addQuot_envEqInd :
    Environment.addQuot envEqInd = .ok (markQuotInit
      ((((envEqInd.add quotCI).add quotMkCI).add quotLiftCI).add quotIndCI)) := by
  rw [addQuot_eq]
  rw [if_neg (show ¬ envEqInd.quotInit = true by simp [show envEqInd.quotInit = false from rfl])]
  rw [checkEqType_envEqInd,
    checkName_ok wf2' (find?_envEqInd_none (by decide) (by decide)) prim_Quot,
    checkName_ok wf2' (find?_envEqInd_none (by decide) (by decide)) prim_QuotMk,
    checkName_ok wf2' (find?_envEqInd_none (by decide) (by decide)) prim_QuotLift,
    checkName_ok wf2' (find?_envEqInd_none (by decide) (by decide)) prim_QuotInd]
  rfl

/-! ## 4. Where the vacuity sits

Three statements, each one an upper bound on what the present tree can reach.  `AddQuot`,
`AddQuot1`, `trEnv_addQuot` and `addQuot.WF'` are *not* among the things bounded: those fire
at `Verify/QuotConsts.lean` §7's witness, where `Eq` is an axiom.  The two witnesses cannot be
made to coincide today, and that gap is precisely `AddInduct`'s emptiness -- nothing
quotient-specific survives in it. -/

/-- **The environment of §3 has no model.**  One line from `VEnvs.WF.no_inductInfo`; stated
here because it is the exact reason §3's reachability does not transfer to `addQuot.WF`.

False after the `AddInduct` flip. -/
theorem no_wf_envEqInd (ves : VEnvs) : ¬ ves.WF envEqInd := fun wf =>
  wf.no_inductInfo find?_cm2_Eq

/-- **`checkEqType` never succeeds on a modelled environment.**  Its success forces `Eq` to be
an `.inductInfo`, and no environment carrying a `VEnvs` model has one.

False after the `AddInduct` flip. -/
theorem checkEqType_ne_ok_of_wf {env : Environment} {ves : VEnvs} (wf : ves.WF env) :
    checkEqType env ≠ .ok () := fun h => by
  obtain ⟨info, u, hfind, -, -, -⟩ := checkEqType.WF_type (env := env) () h
  rw [Kernel.Environment.find?, (wf.tr (safety := .safe)).map_wf.find?'_eq_find?] at hfind
  exact wf.no_inductInfo hfind

/-- **The sharp statement of what `addQuot.WF` proves today.**  Under `ves.WF env` the
quotient step either fails or is the identity: the branch that installs `Quot`, `Quot.mk`,
`Quot.lift` and `Quot.ind` is unreachable, so `addQuot.WF`'s content is its `quotInit = true`
branch and nothing else.  `addQuot.WF'`'s proof is nonetheless complete and unconditional --
what is missing is an environment to run it at, not a step of the argument.

False after the `AddInduct` flip, which is what makes it worth stating now. -/
theorem addQuot_trivial_of_wf {env env' : Environment} {ves : VEnvs} (wf : ves.WF env)
    (h : Environment.addQuot env = .ok env') : env' = env ∧ env.quotInit = true := by
  rw [addQuot_eq] at h
  split at h
  · exact ⟨(Except.ok.inj h).symm, by assumption⟩
  · exfalso
    cases hc : checkEqType env with
    | error e => rw [hc] at h; simp [( · >>= ·), Except.bind] at h
    | ok a => exact checkEqType_ne_ok_of_wf wf (by rw [hc])

end QuotReach

end Lean4Lean
