import Lean4Lean.Verify.Inductive.AddInductiveStep
import Lean4Lean.Verify.Inductive.FlipConstruct
import Lean4Lean.Verify.Soundness

/-!
# `addDecl.WF`: the claim, the per-kind checklist, and the route that keeps the statement

`Lean4Lean.addDecl.WF` (`Verify/Environment.lean`) is one of the thirteen holes and the direct
parent of `Lean4Lean.kernel_sound`.  This file is its **map**: what it claims, which of its seven
declaration kinds are already discharged, what the remaining kind needs, and which parts of it are
vacuous today.  Everything asserted here is a theorem in this file unless it is explicitly
labelled `[source]`.
-/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

/-! ## 1. The claim, unfolded

`addDecl.WF`'s conclusion is one postcondition applied at every constructor of `Declaration`.
`AddDeclClaimAt decl` is that statement at a *fixed* declaration, so the seven kinds can be
scored separately; `AddDeclClaim` is the conjunction over all of them, i.e. `addDecl.WF` itself.

Read `Except.WF x Q` as "if `x` succeeds, its value satisfies `Q`" (`Except.WF x Q := ∀ a,
x = .ok a → Q a`), and `ves.WF env` as "the four-field bundle `VEnvs.WF`: a `TrEnv` model at
every `DefinitionSafety`, `VEnv.HasPrimitives` at each, the kernel-side `safePrimitives`
side-condition, and `mono` between levels".  Spelled out, the claim is:

> for every kernel environment `env` carrying a `VEnvs` model `ves`, and every `decl` and
> `fuel`, if `addDecl env decl` succeeds with `env'` then some `VEnvs` `ves'` models `env'`,
> and `ves'` extends `ves` at every safety level. -/
def AddDeclClaimAt (decl : Declaration) : Prop :=
  ∀ ⦃env : Environment⦄ ⦃ves : VEnvs⦄, ves.WF env → ∀ fuel : FuelConfig,
    (addDecl env decl (check := true) (fuel := fuel)).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧ ∀ safety, ves.venv safety ≤ ves'.venv safety

/-- The claim at every declaration kind: **this is `addDecl.WF`'s statement**, and
`addDeclClaim_iff_bridge` below checks that against the one consumer that repeats it. -/
def AddDeclClaim : Prop := ∀ decl : Declaration, AddDeclClaimAt decl

/-- **The restatement is the consumer's statement, verbatim.**  `Verify/Bridge.lean`'s
`Bridge.AddDeclWF` is the def that `Bridge.addDeclWF` discharges from `addDecl.WF`, and it is the
only direct user of the hole.  Proved by `Iff.intro` of two reorderings, so nothing is lost. -/
theorem addDeclClaim_iff_bridge : AddDeclClaim ↔ ∀ fuel : FuelConfig, Bridge.AddDeclWF fuel := by
  constructor
  · intro H fuel _ _ wf decl; exact H decl wf fuel
  · intro H decl _ _ wf fuel; exact H fuel wf decl

/-! ## 2. The per-kind checklist, machine-checked

Six of the seven kinds are **discharged**: each is one `mono` from a branch lemma that
`Verify/Environment.lean` already proves.  The proofs below are the branch-by-branch content of
`addDecl.WF`'s own body, restated so that each kind is a named theorem and can be cited alone.

These six inherit the type-checker stream's `sorryAx` taint through their branch lemmas
(`addAxiom.WF`, …, `addMutual.WF`); none of them contains a `sorry`, and none is refuted. -/

theorem addDeclClaimAt_axiomDecl (v : AxiomVal) : AddDeclClaimAt (.axiomDecl v) := by
  intro _ _ wf fuel
  exact (addAxiom.WF wf v fuel).mono fun _ ⟨ves', hwf, _, h⟩ => ⟨ves', hwf, (h · |>.le)⟩

theorem addDeclClaimAt_thmDecl (v : TheoremVal) : AddDeclClaimAt (.thmDecl v) := by
  intro _ _ wf fuel
  exact (addTheorem.WF wf v fuel).mono fun _ ⟨ves', hwf, _, h⟩ => ⟨ves', hwf, (h · |>.le)⟩

theorem addDeclClaimAt_defnDecl (v : DefinitionVal) : AddDeclClaimAt (.defnDecl v) := by
  intro _ _ wf fuel
  exact (addDefinition.WF wf v fuel).mono fun _ ⟨ves', hwf, h, _⟩ => ⟨ves', hwf, h⟩

theorem addDeclClaimAt_opaqueDecl (v : OpaqueVal) : AddDeclClaimAt (.opaqueDecl v) := by
  intro _ _ wf fuel
  exact (addOpaque.WF wf v fuel).mono fun _ ⟨ves', hwf, _, h⟩ => ⟨ves', hwf, (h · |>.le)⟩

theorem addDeclClaimAt_quotDecl : AddDeclClaimAt .quotDecl := by
  intro _ _ wf _; exact addQuot.WF wf

theorem addDeclClaimAt_mutualDefnDecl (vs : List DefinitionVal) :
    AddDeclClaimAt (.mutualDefnDecl vs) := by
  intro _ _ wf fuel; exact addMutual.WF wf vs fuel

/-- **The whole hole is the inductive kind.**  `addDecl.WF` is equivalent to its `inductDecl`
branch alone: the other six are discharged above, so nothing else is open and nothing else can
be false.  This is the checklist as one `↔`. -/
theorem addDeclClaim_iff_inductDecl :
    AddDeclClaim ↔ ∀ (lp : List Name) (np : Nat) (types : List InductiveType) (iu : Bool),
      AddDeclClaimAt (.inductDecl lp np types iu) := by
  constructor
  · intro H lp np types iu; exact H _
  · intro H decl
    match decl with
    | .axiomDecl v => exact addDeclClaimAt_axiomDecl v
    | .thmDecl v => exact addDeclClaimAt_thmDecl v
    | .defnDecl v => exact addDeclClaimAt_defnDecl v
    | .opaqueDecl v => exact addDeclClaimAt_opaqueDecl v
    | .quotDecl => exact addDeclClaimAt_quotDecl
    | .mutualDefnDecl vs => exact addDeclClaimAt_mutualDefnDecl vs
    | .inductDecl lp np types iu => exact H lp np types iu

/-! ## 3. The inductive kind is FALSE, and it is false at the *prelude's own first declaration*

`Verify/Inductive/AddDeclWF.lean` §4 already refutes the branch at a synthetic block
(`R10.Wit.uIndType`).  What is added here is that the refutation reaches `stdPrelude`: the first
declaration `Lean4Lean.kernel_sound` feeds to the checker is `eqDecl`, an `.inductDecl`, so the
falsity is on the goal theorem's own path and not only at a witness chosen to break it.

As in §4 there, the executable half is a build-time `#eval` **test**, not a proof: `addDecl` does
not reduce in the kernel, and `Verify/Guard.lean` forbids `native_decide`. -/

/-- The premise is unsatisfiable at any environment holding an `.inductInfo`: one line from
`VEnvs.WF.no_inductInfo`, and the reason every statement below about vacuity is not a hedge. -/
theorem no_model_of_inductInfo {env : Environment} {n v}
    (h : env.constants.find? n = some (.inductInfo v)) (ves : VEnvs) : ¬ ves.WF env :=
  fun wf => wf.no_inductInfo h

/-- **The inductive kind of the claim is false**, conditionally on the checker accepting one
inductive declaration from one modelled environment and inserting an `.inductInfo`. -/
theorem not_addDeclClaimAt_inductDecl {lp : List Name} {np : Nat} {types : List InductiveType}
    {iu : Bool}
    (hex : ∃ (env env' : Environment) (ves : VEnvs) (n : Name) (v : InductiveVal)
        (fuel : FuelConfig), ves.WF env ∧
      addDecl env (.inductDecl lp np types iu) (check := true) (fuel := fuel) = .ok env' ∧
      env'.constants.find? n = some (.inductInfo v)) :
    ¬ AddDeclClaimAt (.inductDecl lp np types iu) := by
  rintro H
  obtain ⟨env, env', ves, n, v, fuel, wf, hok, hfind⟩ := hex
  obtain ⟨ves', hwf', -⟩ := H wf fuel _ hok
  exact no_model_of_inductInfo hfind ves' hwf'

/-- **`addDecl.WF` is false at `stdPrelude`'s first declaration.**  `eqDecl` is
`Verify/Soundness.lean`'s own literal for `Eq`, and the empty environment is modelled
(`Bridge.hasEmptyModel`), so the only executable input is that the checker accepts it and stores
an `.inductInfo` — check E below. -/
theorem not_addDeclClaim_of_eqDecl
    (hex : ∃ (env' : Environment) (n : Name) (v : InductiveVal),
      addDecl (Kernel.Environment.empty `main) eqDecl (check := true) = .ok env' ∧
      env'.constants.find? n = some (.inductInfo v)) :
    ¬ AddDeclClaim := by
  rintro H
  obtain ⟨env', n, v, hok, hfind⟩ := hex
  obtain ⟨ves₀, wf₀⟩ := Bridge.hasEmptyModel
  obtain ⟨ves', hwf', -⟩ := H eqDecl wf₀ {} _ hok
  exact no_model_of_inductInfo hfind ves' hwf'

/- **Check E** (test, not a proof).  The checker accepts `eqDecl` from the empty environment and
stores a safe `.inductInfo` at `Eq`, which is `not_addDeclClaim_of_eqDecl`'s missing premise. -/
#eval show Lean.CoreM Unit from do
  match Lean4Lean.addDecl (Kernel.Environment.empty `main) eqDecl (check := true) with
  | .error _ => throwError "check E: the checker rejected eqDecl"
  | .ok env' =>
    let some (.inductInfo v) := env'.constants.find? ``Eq
      | throwError "check E: Eq is not an inductInfo in the output map"
    unless v.isUnsafe = false do throwError "check E: Eq came out unsafe"
    IO.println "check E: addDecl accepts eqDecl and stores a safe .inductInfo at Eq ✓"

/-! ## 4. Vacuity, loudly

Two different vacuities, and they are the same fact twice. -/

/-- **(V1) The claim says NOTHING at an environment that already holds an `.inductInfo`** — not
merely "is hard to use there": with an arbitrary postcondition `P`, the statement still holds,
because its premise has no model.  Since every successful `.inductDecl` step produces such an
environment (§3), `addDecl.WF` has content only *before the first inductive declaration*, and
`stdPrelude` begins with one. -/
theorem addDeclClaim_vacuous_at {env : Environment} {n v}
    (h : env.constants.find? n = some (.inductInfo v)) (decl : Declaration)
    (P : Environment → Prop) :
    ∀ ⦃ves : VEnvs⦄, ves.WF env → ∀ fuel : FuelConfig,
      (addDecl env decl (check := true) (fuel := fuel)).WF P :=
  fun _ wf _ => absurd wf (no_model_of_inductInfo h _)

/-- **(V2) The premise kills the nested apparatus.**  `ves.WF env` forbids every `.inductInfo`,
which is what `Verify/Inductive/AddInductiveStep.lean` §3–§5 turns into `numNested = 0` and the
collapse of `Environment.addInductive` onto `AddInductive.run`.  So the *nested* half of the
inductive kind — the half `kernel_sound` may not do without — is unreachable from this premise,
and any proof of the inductive kind that uses this consequence is proving the non-nested case
only. -/
theorem premise_forbids_inductInfo {env : Environment} {ves : VEnvs} (wf : ves.WF env) :
    ∀ n v, env.find? n ≠ some (.inductInfo v) :=
  fun _ _ => wf.find?_ne_inductInfo

/-! ## 5. The flip destroys the refutation — and the route that lives off it

`AddInductFlip` (`Verify/Inductive/AddDeclWF.lean`) is `AddInductStagesR … → AddInduct …`, i.e.
`AddInduct` acquiring the constructor `Verify/Inductive/FlipConstruct.lean` builds.  Under it,
`TrEnv'` admits a constant map holding an `.inductInfo`, so **`TrEnv'.no_inductInfo` is false** —
and that lemma is the sole content of `VEnvs.WF.no_inductInfo` (`(wf.tr (safety := .unsafe)).no_inductInfo`)
and of `VEnvs.WF.find?_ne_inductInfo`.

Both directions of this matter:

* §3's refutation of the inductive kind dies with the flip, so `addDecl.WF` **need not be
  weakened**: the statement is false only relative to a placeholder definition;
* §4's (V1) and (V2) die with it too.  In particular `addInductiveStepWF_of_run` — the reduction
  of `AddInductiveStepWF` to the nesting-free `AddInductiveRunRealises` — is proved *from*
  `VEnvs.WF.find?_ne_inductInfo`, so it is a route that the flip removes. -/

/-- **Under the flip, `TrEnv'` reaches a map holding an `.inductInfo`, at every safety level.**
Built from `R10.Wit.inductStepSafe_wit_inductInfo` (a safe one-constructor block at the empty
environment), `AddInductStages.toR`, and `TrEnv'.induct`. -/
theorem trEnv'_inductInfo_of_flip (hflip : AddInductFlip) {m : ConstMap}
    (hwf : m.WF) (hfr : ∀ n, m.find? n = none) (safety : DefinitionSafety) :
    ∃ (m' : ConstMap) (venv' : VEnv) (v : InductiveVal),
      TrEnv' safety m' false venv' ∧ m'.find? `R10.Wit.U = some (.inductInfo v) := by
  obtain ⟨m', venv', ⟨D, -, hwfD, hadd⟩, v, hv⟩ := R10.Wit.inductStepSafe_wit_inductInfo hwf hfr
  exact ⟨m', venv', v, .induct hwfD (hflip hadd.toR) (.empty hwf hfr), hv⟩

/-- **`TrEnv'.no_inductInfo` is false under the flip.**  Its statement is written out here rather
than referred to, so that the refutation is of the proposition and not of a name. -/
theorem not_trEnv'_no_inductInfo_of_flip (hflip : AddInductFlip) :
    ¬ ∀ ⦃C : ConstMap⦄ ⦃Q : Bool⦄ ⦃venv : VEnv⦄ ⦃name : Name⦄ ⦃info : InductiveVal⦄,
        TrEnv' .unsafe C Q venv → C.find? name ≠ some (.inductInfo info) := by
  intro H
  obtain ⟨m', venv', v, htr, hv⟩ :=
    trEnv'_inductInfo_of_flip hflip (m := {}) Lean.SMap.WF.empty
      (fun _ => by simp [Lean.SMap.find?]) .unsafe
  exact H htr hv

/-! ## 6. What closes the inductive kind, with the statement kept

This section is the point of the file: the inductive kind of `addDecl.WF` is **not** in need of
weakening, and the route to it is an implication proved here.  Two steps.

**(6a) Glue.**  `AddInductiveStepClaim` is the obligation about the executable — the old
postcondition, at `Environment.addInductive` — and it implies the whole claim.

**(6b) Content.**  `AddInductFlip` plus the honest obligation of
`Verify/Inductive/AddDeclWF.lean` (`InductStepNested`, quantified per safety level) plus three
named side conditions gives the old postcondition.  Nothing else is needed, and each of the
three is measured in §7. -/

/-- The `inductDecl` obligation about the executable, with `addDecl.WF`'s own postcondition. -/
def AddInductiveStepClaim : Prop :=
  ∀ ⦃env : Environment⦄ ⦃ves : VEnvs⦄, ves.WF env →
    ∀ (lp : List Name) (np : Nat) (types : List InductiveType) (iu ap : Bool)
      (fuel : FuelConfig),
      (Environment.addInductive env lp np types iu ap fuel).WF fun env' =>
        ∃ ves' : VEnvs, ves'.WF env' ∧ ∀ safety, ves.venv safety ≤ ves'.venv safety

/-- **(6a)** The checker-side obligation is the whole of `addDecl.WF`. -/
theorem addDeclClaim_of_step (H : AddInductiveStepClaim) : AddDeclClaim := by
  refine addDeclClaim_iff_inductDecl.2 fun lp np types iu _ _ wf fuel => ?_
  refine Except.WF.bind (Q := fun _ => True) (fun _ _ => trivial) fun ap _ => ?_
  exact H wf lp np types iu ap fuel

/-- The three `VEnvs.WF` fields that `InductStepNested` does **not** supply, as one bundle so
that the residue is a list rather than a gesture.  `mono` and `hasPrimitives` are about the
abstract side, `safePrimitives` purely about the kernel environment. -/
structure StepSideConditions (env' : Environment) (ves' : VEnvs) : Prop where
  hasPrimitives : ∀ safety, VEnv.HasPrimitives (ves'.venv safety)
  safePrimitives : ∀ {n : Name} {ci : ConstantInfo}, env'.find? n = some ci →
    Environment.primitives.contains n → ci.safety = .safe ∧ ci.levelParams = []
  mono : ∀ {safety safety' : DefinitionSafety}, safety ≤ safety' →
    ves'.venv safety' ≤ ves'.venv safety

/-- **(6b) The core implication.**  Given the flip, the honest nested step at every safety level
carries `addDecl.WF`'s *own* postcondition — `ves'.WF env'` included — as soon as the three side
conditions and the `quotInit` equation hold.  The `TrEnv'` step is `InductStepNested.trEnv'`,
which consumes the flip and nothing else; monotonicity is `AddInductStagesR.le` through
`InductStepNested.le`. -/
theorem venvsWF_of_inductStepNested (hflip : AddInductFlip)
    {env env' : Environment} {ves ves' : VEnvs} {lp : List Name} {np : Nat}
    {types : List InductiveType} {nn : Nat}
    (wf : ves.WF env) (hq : env'.quotInit = env.quotInit)
    (hstep : ∀ safety, InductStepNested env.constants env'.constants
      (ves.venv safety) (ves'.venv safety) lp np types nn)
    (hside : StepSideConditions env' ves') :
    ves'.WF env' ∧ ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  refine ⟨?_, fun safety => (hstep safety).le⟩
  exact
    { tr := by unfold TrEnv; rw [hq]; exact (hstep _).trEnv' hflip wf.tr
      hasPrimitives := hside.hasPrimitives _
      safePrimitives := hside.safePrimitives
      mono := hside.mono }

/-- The `inductDecl` obligation in its *honest* vocabulary, with the side conditions attached:
`InductStepNested` is `Verify/Environment/InductR.lean`'s nested-aware step, the shape
`AddInductPost` already uses, and the extra conjuncts are exactly what §6b consumes. -/
def AddInductiveStepNestedPlus : Prop :=
  ∀ ⦃env : Environment⦄ ⦃ves : VEnvs⦄, ves.WF env →
    ∀ (lp : List Name) (np : Nat) (types : List InductiveType) (ap : Bool) (fuel : FuelConfig),
      (Environment.addInductive env lp np types false ap fuel).WF fun env' =>
        env'.quotInit = env.quotInit ∧
        ∃ (ves' : VEnvs) (nn : Nat),
          (∀ safety, InductStepNested env.constants env'.constants
            (ves.venv safety) (ves'.venv safety) lp np types nn) ∧
          StepSideConditions env' ves'

/-- **The safe inductive kind, closed by the flip plus the honest obligation.**  No weakening of
`addDecl.WF`'s postcondition anywhere in the chain. -/
theorem addDeclClaimAt_safe_inductDecl_of_flip (hflip : AddInductFlip)
    (H : AddInductiveStepNestedPlus) (lp : List Name) (np : Nat) (types : List InductiveType) :
    AddDeclClaimAt (.inductDecl lp np types false) := by
  intro _ _ wf fuel
  refine Except.WF.bind (Q := fun _ => True) (fun _ _ => trivial) fun ap _ => ?_
  refine (H wf lp np types ap fuel).mono fun env' ⟨hq, ves', nn, hstep, hside⟩ => ?_
  exact ⟨ves', venvsWF_of_inductStepNested hflip wf hq hstep hside⟩

/-! ## 7. What §6 leaves, and which of it is *false* rather than open

Three residues, and they are of three different kinds.

**(i) `iu = true` — an unsafe inductive — is FALSE, and the flip does not touch it.**
`unsafe_induct_unreachable` (`Verify/Inductive/AddDeclWF.lean` §1.1) has the two halves for
`AddInductStages`; `AddInductStagesR.inductInfo_not_unsafe` below is the same gate for the
relation the flip actually installs, so the flipped `TrEnv'.induct` cannot take an unsafe block
either, while `TrEnv'.ignore` is unavailable at `safety = .unsafe`.  Closing it is a **new
`TrEnv'` constructor** in `Verify/Environment/Basic.lean` (a design decision), or a `VEnvs.WF`
that does not demand a model at `.unsafe`.  `addDeclClaimAt_safe_inductDecl_of_flip` is therefore
stated at `false` and `AddDeclClaim` is *not* derivable from §6 alone.

**(ii) `StepSideConditions.hasPrimitives` has no lemma.**  `VEnv.HasPrimitives.extend`
(`Verify/Primitive.lean`) transfers `HasPrimitives` across an extension by **one** constant and
additionally demands `n ∉ primInductiveNames = [Bool, Bool.false, Bool.true, Nat, Nat.zero,
Nat.succ]`.  An inductive block declares at least a type and a recursor, and the primitive
inductives are *exactly* the excluded names, so the route named in `AddDeclWF.lean` §5.2 —
"`hasPrimitives` … from `VEnv.HasPrimitives.extend`" — does not compose as written.  A
block-level version does not exist in the tree (measured by conclusion shape over the whole
built population, not by grep). **[analysis: that no such lemma exists is measured; that the
block-level version is provable is not claimed]**

**(iii) `mono` needs the block to be the same at every safety level.**  `AddInductPost`
(`AddDeclWF.lean`) puts `∃ D K R` *inside* the `∀ safety`, so nothing there relates
`ves'.venv .safe` to `ves'.venv .unsafe`; `StepSideConditions.mono` is consequently a hypothesis
here rather than a consequence, and the honest fix is for the obligation to share one `D K R`
across levels (or to supply `mono` directly, as this bundle does). -/

/-- The safety gate for the relation the flip installs: an `.inductInfo` that
`AddInductStagesR` introduces is not unsafe.  The `AddInductStages` analogue is
`AddInductStages.inductInfo_not_unsafe`; the point of the copy is that the flip is over the
`R` form, so the gate must be read there. -/
theorem AddInductStagesR.inductInfo_not_unsafe {m₁ m₂ : ConstMap} {env₁ env₂ : VEnv}
    {D : VInductDecl'} {K : List Name} {R : VIndRestore} {n : Name} {v : InductiveVal}
    (H : AddInductStagesR m₁ env₁ D K R m₂ env₂) (hwf : m₁.WF)
    (hnew : m₁.find? n = none) (h : m₂.find? n = some (.inductInfo v)) : v.isUnsafe = false := by
  rcases H.find?_shape hwf h with h' | ⟨-, -, hsafe⟩
  · rw [hnew] at h'; exact absurd h' nofun
  · rw [ConstantInfo.safety_inductInfo] at hsafe
    cases hu : v.isUnsafe with
    | false => rfl
    | true => rw [hu] at hsafe; simp at hsafe

/-- **`StepSideConditions` is not self-contradictory.**  Inhabited at the empty environment and
the everywhere-empty `VEnvs`, so §6b's bundle is a residue and not a disguised `False`.  (This is
inhabitation of the *bundle*; whether it can be met at the environment an inductive block
produces is (ii) and (iii) above, and is open.) -/
theorem stepSideConditions_nonvacuous :
    StepSideConditions (Kernel.Environment.empty `main) Bridge.VEnvs.trivial where
  hasPrimitives _ := Bridge.hasPrimitives_empty
  safePrimitives {n _} h := by
    rw [Kernel.Environment.find?, Bridge.constants_empty_wf.find?'_eq_find?,
      Bridge.constants_empty_find? n] at h
    exact absurd h nofun
  mono _ := VEnv.LE.rfl

/-! ## 8. The flip's own price, machine-checked: `VDecl.WF` must grow a rule

`TrEnv'.wf` (`Verify/Environment/Basic.lean`) proves `venv.WF` from `TrEnv'` by induction, and its
`induct` arm is `.induct h1 h2.to_addInduct` — i.e. it goes through `AddInduct.to_addInduct`
(`env₁.addInduct' decl = some env₂`) into `VDecl.WF.induct` **[source]**.  Under the flip that
step is not merely unproved but **false**, which is the theorem below: the nested payload
declares the auxiliary members' recursors and *not* the companion member, while `addInduct'`
declares the companion.  So the flip cannot be installed while `VDecl.WF`'s only inductive rule is
`induct`; it needs the `inductNested` rule that `Theory/Typing/Env.lean`'s §"The nested `.induct`
step" writes out and deliberately does not add.

`Lean4Lean.VDecl.WF.inductNested` **does not exist** (checked against the compiled environment,
not by grep), and per that file's own measurement adding it breaks `WF'.defEqHeads`, `WF'.keys`,
`WF'.iotaTypes` (`Theory/Typing/DeltaUnique.lean`) and `WF'.ruleShape`
(`Theory/Typing/PatternRules.lean`), and needs `VEnv.addInductR_ordered` for `VEnv.WF.ordered`'s
new arm **[source]**. -/
theorem not_addInduct_to_addInduct_of_flip (hflip : AddInductFlip) :
    ¬ ∀ ⦃m₁ m₂ : ConstMap⦄ ⦃env₁ env₂ : VEnv⦄ ⦃D : VInductDecl'⦄,
        AddInduct m₁ env₁ D m₂ env₂ → env₁.addInduct' D = some env₂ := by
  intro H
  obtain ⟨env₁, m', env', -, ⟨K, R, hstages, -⟩, -, -, -, hnone⟩ :=
    InductiveDeclExamples.ntreeAux_addInductN_ordered (m := {}) Lean.SMap.WF.empty
      (fun _ _ => by simp [Lean.SMap.find?])
  have hc := H (hflip hstages)
  have hmem : env'.constants `_nested.List_1
      = some ⟨InductiveDeclExamples.ntreeAux.uvars, InductiveDeclExamples.nlistMember.type⟩ :=
    VEnv.addInduct'_types hc InductiveDeclExamples.nlistMember_mem
  rw [hnone] at hmem
  exact absurd hmem nofun

/-- **The consumer's own def is false at the default fuel.**  `Verify/Bridge.lean` is *not* frozen
and `Bridge.addDeclWF` is `fun wf decl => addDecl.WF wf decl fuel`, so this says that theorem's
statement is false, not merely unproved — and hence that `Bridge.foldlM_addDecl_WF`,
`Bridge.foldAddDecl_WF`, `Bridge.foldAddDecl_WF'` and `Bridge.foldAddDecl_tr`, which are proved
from it, all stand on a false statement today.  `stdPrelude` begins with `eqDecl`, so the fold is
false at its **first** step. -/
theorem not_bridge_addDeclWF_of_eqDecl
    (hex : ∃ (env' : Environment) (n : Name) (v : InductiveVal),
      addDecl (Kernel.Environment.empty `main) eqDecl (check := true) = .ok env' ∧
      env'.constants.find? n = some (.inductInfo v)) :
    ¬ Bridge.AddDeclWF {} := by
  rintro H
  obtain ⟨env', n, v, hok, hfind⟩ := hex
  obtain ⟨ves₀, wf₀⟩ := Bridge.hasEmptyModel
  obtain ⟨ves', hwf', -⟩ := H wf₀ eqDecl _ hok
  exact no_model_of_inductInfo hfind ves' hwf'

/-! ## 9. Axiom audit

Every theorem here that does not touch the six discharged kinds is
`[propext, Classical.choice, Quot.sound]`.  Those that do — the six §2 theorems,
`addDeclClaim_iff_inductDecl` and `addDeclClaim_of_step` — additionally report `sorryAx` (plus Guard's
whitelisted frozen `Expr.*`/`Level.*` axioms), **inherited only**, from the branch lemmas of
`Verify/Environment.lean` (which are tainted through
the type-checker stream's holes: `inferProj.WF`, `isDefEqUnitLike.WF`, `tryEtaStructCore.WF`,
`TrProj.weak'_inv`, `weakN_iff`, `forallE_inv_stratified`, `rigidShapeUniqNS`, `NormalEq.descend`).
`addDeclClaimAt_safe_inductDecl_of_flip` — the implication that actually closes the open kind —
is **clean**, because it never touches the six discharged branches.

No declaration in this file contains a `sorry`, and the file adds nothing to the hole census. -/

#print axioms Lean4Lean.addDeclClaim_iff_bridge
#print axioms Lean4Lean.addDeclClaim_iff_inductDecl
#print axioms Lean4Lean.no_model_of_inductInfo
#print axioms Lean4Lean.not_addDeclClaimAt_inductDecl
#print axioms Lean4Lean.not_addDeclClaim_of_eqDecl
#print axioms Lean4Lean.not_bridge_addDeclWF_of_eqDecl
#print axioms Lean4Lean.addDeclClaim_vacuous_at
#print axioms Lean4Lean.premise_forbids_inductInfo
#print axioms Lean4Lean.trEnv'_inductInfo_of_flip
#print axioms Lean4Lean.not_trEnv'_no_inductInfo_of_flip
#print axioms Lean4Lean.venvsWF_of_inductStepNested
#print axioms Lean4Lean.stepSideConditions_nonvacuous
#print axioms Lean4Lean.AddInductStagesR.inductInfo_not_unsafe
#print axioms Lean4Lean.not_addInduct_to_addInduct_of_flip
#print axioms Lean4Lean.addDeclClaim_of_step
#print axioms Lean4Lean.addDeclClaimAt_safe_inductDecl_of_flip

end Lean4Lean
