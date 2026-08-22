import Lean4Lean.Verify.Environment
import Lean4Lean.Theory.Consistency

/-!
# Bridge: from the refinement layer to the abstract type theory

This module connects `Lean4Lean/Verify/` (the refinement of the executable
checker against `VEnv`) to `Lean4Lean/Theory/Consistency.lean` (the statement
of consistency of the abstract type theory), producing the shape of statement
that `Lean4Lean.kernel_sound` in the frozen `Verify/Soundness.lean` consumes:

  the checker accepted `stdPrelude ++ ds` and the result proves `False`
  ⟹ `¬ leanTTConsistent`.

`Verify/Soundness.lean` is frozen and will eventually `import` this file, so
nothing here may import it. The definitions it needs (`foldAddDecl`,
`falseExpr`, `ContainsSafeProofOfFalse`, `Declaration.IsAxiomFree`) are
therefore *mirrored* here, in the `Lean4Lean.Bridge` namespace, with bodies
identical to the frozen ones; the two are definitionally equal, so the frozen
statement can be discharged by `exact`.

## What is proved, and what is still hypothetical

Proved outright:

* `VEnvs.trivial_WF` — the base case of the fold, for any kernel environment
  whose constant map is literally `{}` and which is not quot-initialized.
* `foldlM_addDecl_WF` / `foldAddDecl_WF` / `foldAddDecl_tr` — iteration of
  `addDecl.WF` along `List.foldlM`.
* `hasType_falseProp` — a safe, universe-monomorphic constant of type
  `∀ p : Prop, p` in the kernel environment yields an inhabitant of
  `falseProp` in the abstract environment.

Left as explicit hypotheses (see the individual doc comments):

* `HasEmptyModel` — the base case *for `Kernel.Environment.empty`*, which is
  **not** an instance of `VEnvs.trivial_WF`: see `constants_empty_ne`.
* `AddDeclWF fuel` — `addDecl.WF` at an arbitrary fuel setting; the version in
  `Verify/Environment.lean` is stated only for `fuel := {}`
  (`addDeclWF_default` discharges that instance).
* `PreludeBridge pre` — the prelude/axiom-free bookkeeping: that the abstract
  environment obtained from `pre ++ ds` is `VEnv.LeanWF`. This is the step that
  needs the inductive-declaration work (`AddInduct` is currently an inductive
  with no constructors, so `TrEnv` provably contains no inductive at all, while
  `stdPrelude` is mostly `.inductDecl`s).
-/

namespace Lean4Lean.Bridge

open Lean hiding Environment Exception
open Kernel
open Lean4Lean

/-! ## Mirrors of the definitions used by the frozen statement

Each of these has the same body as the corresponding definition in
`Lean4Lean/Verify/Soundness.lean`, hence is definitionally equal to it. -/

/-- Mirror of `Lean4Lean.foldAddDecl`. -/
def foldAddDecl (fuel : FuelConfig) (ds : List Declaration) :
    Except Kernel.Exception Kernel.Environment :=
  ds.foldlM (fun env d => addDecl env d (check := true) (fuel := fuel))
    (Kernel.Environment.empty `main)

/-- Mirror of `Lean4Lean.Declaration.IsAxiomFree`. -/
def Declaration.IsAxiomFree : Declaration → Prop
  | .axiomDecl _ => False
  | _ => True

/-- Mirror of `Lean4Lean.falseExpr`: `∀ p : Prop, p` as a kernel expression. -/
def falseExpr : Expr := .forallE `p (.sort .zero) (.bvar 0) .default

/-- Mirror of `Lean4Lean.ContainsSafeProofOfFalse`. -/
def ContainsSafeProofOfFalse (env : Kernel.Environment) : Prop :=
  ∃ (n : Name) (ci : ConstantInfo), env.find? n = some ci ∧
    ci.isUnsafe = false ∧ ci.isPartial = false ∧
    ci.levelParams = [] ∧ ci.type = falseExpr

/-! ## 1. The base of the fold -/

/-- The everywhere-empty family of abstract environments. -/
def VEnvs.trivial : VEnvs := ⟨fun _ => .empty⟩

theorem hasPrimitives_empty : VEnv.HasPrimitives .empty := by
  constructor <;>
    simp +decide [VEnv.contains, VEnv.empty, VEnv.ReflectsNatNatNat, VEnv.ReflectsNatNatBool]

/-- **Item 1.** Any kernel environment whose constant map is literally empty and which has not
run `init_quot` is modelled by the everywhere-empty `VEnvs`. -/
theorem VEnvs.trivial_WF {env : Kernel.Environment}
    (hc : env.constants = ({} : ConstMap)) (hq : env.quotInit = false) :
    VEnvs.trivial.WF env where
  tr := by unfold TrEnv; rw [hc, hq]; exact .empty
  hasPrimitives := hasPrimitives_empty
  safePrimitives {n ci} h := by
    rw [Kernel.Environment.find?, hc] at h
    simp [SMap.find?'] at h
  mono _ := VEnv.LE.rfl

/-- **A gap in item 1.** `Kernel.Environment.empty` is *not* covered by `VEnvs.trivial_WF`:
its constant map is created at SMap stage 2 (`stage₁ := false`), whereas `TrEnv'.empty` — and
`Aligned.empty` — pin the constant map to `({} : ConstMap)`, whose `stage₁` is `true`.
`TrEnv'` has no other rule producing `VEnv.empty`, so `TrEnv safety (.empty `main) .empty` is
underivable as the inductive family currently stands.

The fix is a one-line change in `Verify/Environment/Basic.lean` (and the matching `Aligned.empty`
in `Verify/Environment/Lemmas.lean`): let the `empty` constructor take an arbitrary constant map
with empty `map₁`/`map₂` rather than the literal `{}`. That file is outside this module's remit,
so the base case is threaded through as the hypothesis `HasEmptyModel` below. -/
theorem constants_empty_ne : (Kernel.Environment.empty `main).constants ≠ ({} : ConstMap) :=
  fun h => absurd (congrArg SMap.stage₁ h) (by decide)

/-- The base case of the fold, as a hypothesis: the empty kernel environment has an abstract
model. Blocked only by the SMap-stage mismatch documented at `constants_empty_ne`. -/
def HasEmptyModel : Prop := ∃ ves : VEnvs, ves.WF (Kernel.Environment.empty `main)

/-! ## 2. Iterating `addDecl.WF` along the fold -/

/-- `addDecl.WF`, generalized over the fuel configuration.

`Verify/Environment.lean` proves this only at `fuel := {}` (`addDeclWF_default`), because the
statements of `checkConstantValCore.WF`, `checkConstantVal.WF`, `checkBodyCore.WF`,
`checkBody.WF`, `checkTheorem.WF`, `checkDefinition.WF`, `checkOpaque.WF` (in
`Verify/Environment/Checker.lean`) and `checkPrimitiveDef.WF` (in
`Verify/Environment/Boundaries.lean`) instantiate `TypeChecker.VContext.mk'`/`.mk1` at their
default `fuel := {}`. Every lemma those proofs consume (`TypeChecker.checkType.WF`,
`isDefEq.WF`, `M.WF.run`, `M.WF.run1`, `VState.WF.empty1`, …) is already stated for an
arbitrary `VContext`/`fuel`, so generalizing is purely a matter of threading one extra
argument through those eight statements. -/
def AddDeclWF (fuel : FuelConfig) : Prop :=
  ∀ {env : Kernel.Environment} {ves : VEnvs}, ves.WF env → ∀ decl : Declaration,
    (addDecl env decl (check := true) (fuel := fuel)).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧ ∀ safety, ves.venv safety ≤ ves'.venv safety

theorem addDeclWF_default : AddDeclWF {} := fun wf decl => addDecl.WF wf decl

/-- **Item 2.** `addDecl.WF` iterated along `List.foldlM`. -/
theorem foldlM_addDecl_WF {fuel : FuelConfig} (H : AddDeclWF fuel) :
    ∀ (ds : List Declaration) {env : Kernel.Environment} {ves : VEnvs}, ves.WF env →
      (ds.foldlM (fun env d => addDecl env d (check := true) (fuel := fuel)) env).WF
        fun env' => ∃ ves' : VEnvs, ves'.WF env' ∧ ∀ safety, ves.venv safety ≤ ves'.venv safety
  | [], _, _, wf => Except.WF.pure ⟨_, wf, fun _ => VEnv.LE.rfl⟩
  | d :: ds, _, _, wf => by
    refine Except.WF.bind (H wf d) fun env₁ ⟨ves₁, wf₁, le₁⟩ => ?_
    exact (foldlM_addDecl_WF H ds wf₁).mono fun _ ⟨ves₂, wf₂, le₂⟩ =>
      ⟨ves₂, wf₂, fun safety => (le₁ safety).trans (le₂ safety)⟩

/-- **Item 2.** A successful run of the checker over a whole declaration list yields an abstract
model of the resulting environment, extending the model of the empty environment it started
from. -/
theorem foldAddDecl_WF' {fuel : FuelConfig} (H : AddDeclWF fuel) {ves₀ : VEnvs}
    (wf₀ : ves₀.WF (Kernel.Environment.empty `main))
    {ds : List Declaration} {env : Kernel.Environment} (hok : foldAddDecl fuel ds = .ok env) :
    ∃ ves : VEnvs, ves.WF env ∧ ∀ safety, ves₀.venv safety ≤ ves.venv safety :=
  foldlM_addDecl_WF H ds wf₀ _ hok

/-- **Item 2.** The same, with the base case supplied by `HasEmptyModel`. -/
theorem foldAddDecl_WF {fuel : FuelConfig} (H : AddDeclWF fuel) (hbase : HasEmptyModel)
    {ds : List Declaration} {env : Kernel.Environment} (hok : foldAddDecl fuel ds = .ok env) :
    ∃ ves : VEnvs, ves.WF env := by
  obtain ⟨_, wf₀⟩ := hbase
  obtain ⟨ves, wf, -⟩ := foldAddDecl_WF' H wf₀ hok
  exact ⟨ves, wf⟩

/-! ## 3. From the fold to a well-formed abstract environment -/

/-- **Item 3.** The `safe`-level model of the accepted environment, together with its
well-formedness. -/
theorem foldAddDecl_tr {fuel : FuelConfig} (H : AddDeclWF fuel) (hbase : HasEmptyModel)
    {ds : List Declaration} {env : Kernel.Environment} (hok : foldAddDecl fuel ds = .ok env) :
    ∃ venv : VEnv, TrEnv .safe env venv ∧ venv.WF := by
  obtain ⟨ves, wf⟩ := foldAddDecl_WF H hbase hok
  exact ⟨ves.venv .safe, wf.tr, wf.tr.wf⟩

/-! ## 4. The `False` witness, transported to the abstract environment -/

theorem trExprS_falseExpr_inv {venv : VEnv} {A : VExpr}
    (H : TrExprS venv [] [] falseExpr A) : A = falseProp := by
  cases H with
  | forallE _ _ hty hbody =>
    cases hty with
    | sort hu =>
      cases hu
      cases hbody with
      | bvar hfind =>
        cases hfind
        rfl

/-- **Item 4.** A safe, universe-monomorphic kernel constant whose type is literally
`∀ p : Prop, p` gives a closed inhabitant of `falseProp` in the abstract environment. -/
theorem hasType_falseProp {env : Kernel.Environment} {venv : VEnv}
    (htr : TrEnv .safe env venv) (hwf : venv.WF) (h : ContainsSafeProofOfFalse env) :
    ∃ e, venv.HasType 0 [] e falseProp := by
  obtain ⟨n, ci, hfind, hunsafe, hpartial, hlp, htype⟩ := h
  have hsafety : ci.safety = .safe := by
    simp [ConstantInfo.safety, hunsafe, hpartial]
  obtain ⟨ci', hconst, -, huvars, htr'⟩ :=
    htr.find? hfind (by rw [hsafety]; exact DefinitionSafety.le_rfl)
  rw [hlp] at huvars htr'
  rw [htype] at htr'
  have htype' : ci'.type = falseProp := trExprS_falseExpr_inv htr'
  refine ⟨.const n (VLevel.params ci'.uvars), ?_⟩
  have := VEnv.HasType.const0 hconst (hwf.ordered.constWF hconst)
  rw [htype'] at this
  rwa [← huvars] at this ⊢

/-! ## 5–6. The prelude bookkeeping and the final export -/

/-- The prelude/axiom-free bookkeeping, as a hypothesis: if the checker accepts `pre` followed by
axiom-free declarations, then the resulting `safe`-level abstract environment is a *standard*
Lean environment in the sense of `VEnv.LeanWF` — built from `leanPrelude` by axiom-free
`VDecl` steps.

This is the one link of the chain that the refinement layer cannot supply today: `TrEnv'.wf`
only exposes `∃ ds, VEnv.WF' ds venv`, with no control over the tail of `ds`, and `AddInduct`
(`Verify/Environment/Basic.lean`) has no constructors, so `TrEnv` provably contains no inductive
declaration at all — while `stdPrelude` is mostly `.inductDecl`s. Discharging it needs the
inductive-declaration workstream (`VInductDecl.WF`/`VEnv.addInduct`/`AddInduct`) plus a
`foldAddDecl`-level invariant recording that the first `pre.length` steps were exactly the
prelude. -/
def PreludeBridge (pre : List Declaration) : Prop :=
  ∀ (ds : List Declaration) (fuel : FuelConfig) (env : Kernel.Environment) (venv : VEnv),
    foldAddDecl fuel (pre ++ ds) = .ok env →
    (∀ d ∈ ds, Declaration.IsAxiomFree d) →
    TrEnv .safe env venv → venv.LeanWF

/-- **Item 6, the final export.** If the checker, from the empty environment, accepts the
standard prelude `pre` followed by axiom-free declarations and the result contains a safe proof
of `∀ p : Prop, p`, then the abstract type theory is inconsistent.

Composed with a proof of `leanTTConsistent` (link 2 of `PLAN.md`) and the three hypotheses
below, this discharges `Lean4Lean.kernel_sound`; the mirrored definitions above are
definitionally equal to the frozen ones, so no restatement is needed there. -/
theorem not_leanTTConsistent_of_kernel_proves_false
    {pre : List Declaration} (hbase : HasEmptyModel) (hpre : PreludeBridge pre)
    (ds : List Declaration) (fuel : FuelConfig) (hfuel : AddDeclWF fuel)
    (env : Kernel.Environment)
    (hok : foldAddDecl fuel (pre ++ ds) = .ok env)
    (hax : ∀ d ∈ ds, Declaration.IsAxiomFree d)
    (hfalse : ContainsSafeProofOfFalse env) : ¬ leanTTConsistent := by
  obtain ⟨venv, htr, hwf⟩ := foldAddDecl_tr hfuel hbase hok
  exact fun hcon => hcon venv (hpre ds fuel env venv hok hax htr) (hasType_falseProp htr hwf hfalse)

/-- The same, specialized to the fuel setting at which `addDecl.WF` is currently available. -/
theorem not_leanTTConsistent_of_kernel_proves_false_default
    {pre : List Declaration} (hbase : HasEmptyModel) (hpre : PreludeBridge pre)
    (ds : List Declaration) (env : Kernel.Environment)
    (hok : foldAddDecl {} (pre ++ ds) = .ok env)
    (hax : ∀ d ∈ ds, Declaration.IsAxiomFree d)
    (hfalse : ContainsSafeProofOfFalse env) : ¬ leanTTConsistent :=
  not_leanTTConsistent_of_kernel_proves_false hbase hpre ds {} addDeclWF_default env hok hax hfalse

end Lean4Lean.Bridge
