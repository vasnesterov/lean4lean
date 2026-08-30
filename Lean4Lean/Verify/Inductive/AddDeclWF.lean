import Lean4Lean.Verify.Bridge
import Lean4Lean.Verify.Environment.InductR

/-!
# `addDecl.WF`'s `inductDecl` branch: why it is false, and what the true statement is

`Verify/Environment.lean`'s `addDecl.WF` carries `| inductDecl _ _ _ _ => sorry`.  That
`sorry` is **not** an open goal: its postcondition is refuted by `VEnvs.WF.no_inductInfo`
(`Verify/InductFlip.lean`) for every declaration whose success inserts an `.inductInfo`, and
the checker does accept such declarations.  This file separates the three *independent*
reasons the branch is false, proves what can be proved about each today, and states the
obligation that replaces it.

The three reasons, and their status here:

1. **`AddInduct` is empty** (`Verify/Environment/Basic.lean`), so no inductive block is
   modelled at any safety level.  Repair: the flip, `AddInduct := AddInductStages`.  All the
   content is in hand (`Verify/InductFlip.lean`, `docs/handoff-addinduct.md` §6); §3 below
   states the obligation the flip leaves, and fires it at a witness.
2. **`TrEnv'` has no rule for an *unsafe* inductive at `safety = .unsafe`.**  §1 proves the
   half of this that is about `AddInductStages`: the relation forces `isUnsafe = false` on
   every constant it introduces.  With `ignore_unavailable_at_unsafe`
   (`Verify/TypeChecker/Reduce.lean`) that closes the argument: **the flip does not fix
   this.**
3. **A nested block adds constants no `VInductDecl'` for it declares.**  §2 proves that this
   *refutes* `AddInductStages` for the block — it is not an incompleteness that a better
   `VInductDecl'` (e.g. `Theory/Inductive/NestedBuild.lean`'s) can repair, because the
   obstruction is on the *constant-map* side, not the declaration side.

§4 records the executable facts the argument rests on as build-time checks; they are tests,
not proofs, and are labelled as such.
-/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

/-! ## 1. The safety gate, as a theorem

`AddIndConsts.cons` carries `TrConstant .safe`, i.e. `.safe ≤ ci.safety`; `.safe` is the top
of `DefinitionSafety`, so antisymmetry pins `ci.safety = .safe` (`AddIndConsts.find?`,
`Verify/Environment/Basic.lean`).  `docs/handoff-addinduct.md` §3 calls that "the whole gate,
and it is already written".  It is written, but it was never *read back* into the vocabulary
the checker uses, which is `InductiveVal.isUnsafe` rather than `ConstantInfo.safety`.  That
is what this section does, for all three constant shapes. -/

theorem ConstantInfo.safety_ctorInfo (info : ConstructorVal) :
    (ConstantInfo.ctorInfo info).safety = if info.isUnsafe then .unsafe else .safe := by
  cases h : info.isUnsafe <;>
    simp [ConstantInfo.safety, ConstantInfo.isUnsafe, ConstantInfo.isPartial, h]

theorem ConstantInfo.safety_recInfo (info : RecursorVal) :
    (ConstantInfo.recInfo info).safety = if info.isUnsafe then .unsafe else .safe := by
  cases h : info.isUnsafe <;>
    simp [ConstantInfo.safety, ConstantInfo.isUnsafe, ConstantInfo.isPartial, h]

/-- **The gate, in the checker's vocabulary.**  An `.inductInfo` that `AddInductStages`
introduces — as opposed to one that was already in the map — is not unsafe. -/
theorem AddInductStages.inductInfo_not_unsafe {m₁ m₂ : ConstMap} {env₁ env₂ : VEnv}
    {D : VInductDecl'} {n : Name} {v : InductiveVal}
    (H : AddInductStages m₁ env₁ D m₂ env₂) (hwf : m₁.WF)
    (hnew : m₁.find? n = none) (h : m₂.find? n = some (.inductInfo v)) : v.isUnsafe = false := by
  rcases H.find?_shape hwf h with h' | ⟨-, -, hsafe⟩
  · rw [hnew] at h'; exact absurd h' nofun
  · rw [ConstantInfo.safety_inductInfo] at hsafe
    cases hu : v.isUnsafe with
    | false => rfl
    | true => rw [hu] at hsafe; simp at hsafe

/-- The constructor half of the gate. -/
theorem AddInductStages.ctorInfo_not_unsafe {m₁ m₂ : ConstMap} {env₁ env₂ : VEnv}
    {D : VInductDecl'} {n : Name} {v : ConstructorVal}
    (H : AddInductStages m₁ env₁ D m₂ env₂) (hwf : m₁.WF)
    (hnew : m₁.find? n = none) (h : m₂.find? n = some (.ctorInfo v)) : v.isUnsafe = false := by
  rcases H.find?_shape hwf h with h' | ⟨-, -, hsafe⟩
  · rw [hnew] at h'; exact absurd h' nofun
  · rw [ConstantInfo.safety_ctorInfo] at hsafe
    cases hu : v.isUnsafe with
    | false => rfl
    | true => rw [hu] at hsafe; simp at hsafe

/-- The recursor half of the gate. -/
theorem AddInductStages.recInfo_not_unsafe {m₁ m₂ : ConstMap} {env₁ env₂ : VEnv}
    {D : VInductDecl'} {n : Name} {v : RecursorVal}
    (H : AddInductStages m₁ env₁ D m₂ env₂) (hwf : m₁.WF)
    (hnew : m₁.find? n = none) (h : m₂.find? n = some (.recInfo v)) : v.isUnsafe = false := by
  rcases H.find?_shape hwf h with h' | ⟨-, -, hsafe⟩
  · rw [hnew] at h'; exact absurd h' nofun
  · rw [ConstantInfo.safety_recInfo] at hsafe
    cases hu : v.isUnsafe with
    | false => rfl
    | true => rw [hu] at hsafe; simp at hsafe

/-! ### 1.1 The `.unsafe` hole, which the gate does not close

The gate says an inductive block reaches the *model* only if it is safe.  At
`safety = .safe` and `safety = .partial` that is harmless: an unsafe block's constants are
`.unsafe`-tagged, so `TrEnv'.ignore`'s premise `¬ safety ≤ ci.safety` holds and the block is
taken by `ignore` with no `VEnv` counterpart.  At `safety = .unsafe` it is not harmless:
`.unsafe` is the bottom of `DefinitionSafety`, so `.unsafe ≤ ci.safety` holds for **every**
`ci` and `ignore` is unavailable.

`TrEnv' .unsafe` therefore has no rule at all for an unsafe inductive, before or after the
flip, and `addDecl.WF`'s `inductDecl` branch is false at `isUnsafe = true` for that reason
alone.  Both halves of that are below; the flip changes neither. -/

/-- **The `.unsafe` hole, both halves.**  (1) `AddInductStages` never introduces an unsafe
`.inductInfo`, so the flipped `TrEnv'.induct` cannot take an unsafe block at any safety
level.  (2) `TrEnv'.ignore` cannot take it either at `safety = .unsafe`, because its premise
fails for every constant there.

Closing the hole needs a new `TrEnv'` rule — the inductive analogue of `TrEnv'.unsafeDef`,
adding the block's constants without a positivity witness — or a `VEnvs.WF` that does not
demand a model at `.unsafe`.  It is a design decision, not a proof obligation, and it is
independent of `AddInduct`. -/
theorem unsafe_induct_unreachable (v : InductiveVal) (hu : v.isUnsafe = true) :
    (∀ {m₁ m₂ : ConstMap} {env₁ env₂ : VEnv} {D : VInductDecl'} {n : Name},
      AddInductStages m₁ env₁ D m₂ env₂ → m₁.WF → m₁.find? n = none →
      m₂.find? n ≠ some (.inductInfo v)) ∧
    (∀ ci : ConstantInfo, DefinitionSafety.unsafe ≤ ci.safety) := by
  refine ⟨fun H hwf hnew h => ?_, fun ci => by cases ci.safety <;> decide⟩
  rw [H.inductInfo_not_unsafe hwf hnew h] at hu
  exact absurd hu (by decide)

/-! ## 2. The nested wall

`Verify/Environment/Induct.lean` records that a nested block is outside `TrIndDecl` because
"`addInductive` discards the auxiliary environment and rebuilds".  That is right, but it
understates the obstruction, and locates it in the wrong place.  The rebuild
(`Lean4Lean/Inductive/Add.lean`, the `numNested = 0` guard and the `StateT.run (s := env)`
block after it) adds, besides the block's own types, constructors and recursors, **one extra
recursor per auxiliary nested type** — `mkAuxRecNameMap` renames `_nested.J.rec` to
`I.rec_1`, `I.rec_2`, … and `processRec` adds it.

Those names are not `mkRecName` of any type the block declares, so no `VInductDecl'` that
*translates the declaration* can name them (`TrIndDecl` pins every name to the syntax).  And
`AddInductStages` is exact on the map — `find?_of_not_mem` says the map changes only at
`D.allNames` — so the presence of `I.rec_1` in the output map **refutes**
`AddInductStages m₁ env₁ D m₂ env₂` for every such `D`.

This is a different fact from "the declaration is not recoverable".  `Theory/Inductive/
NestedBuild.lean` supplies the restored `VInductDecl'` as a construction; that closes the
*declaration* side and leaves this one untouched, because the obstruction is on the
constant-map side.  Either `AddInduct` grows a fourth stage for the auxiliary recursors, or
`VInductDecl'` grows them; nothing else will do.

**RESOLVED.**  The repair is `AddInductStagesR` (`Verify/Environment/InductR.lean`): the
first of the two shapes, taken from `Theory/Inductive/NestedHead.lean`'s `recConstsR`
rather than invented here.  §2's refutation is unchanged and still true *of
`AddInductStages`*; what changed is that `AddInductStages` is no longer the intended
definition of `AddInduct`.  See `InductR.lean` for the invariant, the re-run and the witness.

**The four declarations that stood here now live in `Verify/Environment/Induct.lean`**
(`indDeclNames`, `exists_getElem?_of_lt`, `TrIndDecl.mem_indDeclNames`,
`TrIndDecl.not_addInductStages`), unchanged, so that the *nested* repair
(`Verify/Environment/InductR.lean`) can use them without importing the type-checker layer.
This file re-exports them by importing that module. -/

/-! ## 3. The obligation that replaces the `sorry`

There is **no branch-local restatement**.  `addDecl.WF`'s conclusion is uniform across the
constructors of `Declaration`, so one cannot weaken the `inductDecl` arm and leave the others
alone: what has to change is one of the definitions the postcondition quantifies over, and
the minimal change is `AddInduct`'s.  The branch's statement is then *true as written*, for a
safe non-nested block, and the work it needs is the obligation below.

`InductStepSafe` is stated as a **definition of the output map** rather than a check on it:
`AddInductStages` pins `m'` to be `m` with exactly the block's constants inserted
(`AddInductStages.find?_of_not_mem`), so a `VInductDecl'` that under-reports its constructors
cannot be paired with the map the checker produced.  That is the shape
`Theory/Inductive/Companion.lean`'s `fooComp_inconsistent` demands and the shape
`fooComp_WFC` showed a re-staged *check* does not achieve.

**SUPERSEDED for nested blocks.**  `InductStepSafe` is the non-nested obligation and stays
as it is; its nested-aware generalisation is `InductStepNested`
(`Verify/Environment/InductR.lean`), which replaces `AddInductStages` by `AddInductStagesR`,
`TrIndDecl` by `TrIndDeclN`, and adds `∃ et, venv.addIndTypes D = some et` as an explicit
vacuity guard on `VInductDecl'.WF.ctors`.  `TrIndDecl.toN` embeds this obligation's syntactic
half into that one at `numNested = 0`. -/

/-- **The `inductDecl` branch's real obligation, at one safety level, for a safe block.**

Both halves are needed and neither excuses the other: `TrIndDecl` says the abstract
declaration describes the syntax the user wrote, `VInductDecl'.WF` says it is a legitimate
declaration, and `AddInductStages` says the checker's output map and the abstract environment
are the ones that declaration builds. -/
def InductStepSafe (m m' : ConstMap) (venv venv' : VEnv)
    (lp : List Name) (np : Nat) (types : List InductiveType) : Prop :=
  ∃ D : VInductDecl',
    TrIndDecl venv lp np types false D ∧ D.WF venv ∧ AddInductStages m venv D m' venv'

/-- The premises `TrEnv'.induct` consumes, for a non-nested block. -/
theorem InductStepSafe.induct_premises (h : InductStepSafe m m' venv venv' lp np types) :
    ∃ D : VInductDecl', D.WF venv ∧ AddInductStages m venv D m' venv' :=
  let ⟨D, _, hwf, hadd⟩ := h; ⟨D, hwf, hadd⟩

theorem InductStepSafe.le (h : InductStepSafe m m' venv venv' lp np types) : venv ≤ venv' :=
  let ⟨_, _, _, hadd⟩ := h; hadd.le

theorem InductStepSafe.map_wf (h : InductStepSafe m m' venv venv' lp np types)
    (hwf : m.WF) : m'.WF := let ⟨_, _, _, hadd⟩ := h; hadd.map_wf hwf

/-- **The output map is determined outside the block.**  This is the anti-lie property, at
the level the branch consumes it. -/
theorem InductStepSafe.find?_of_not_mem (h : InductStepSafe m m' venv venv' lp np types)
    (hwf : m.WF) {n : Name} (hn : n ∉ indDeclNames types) : m'.find? n = m.find? n := by
  obtain ⟨D, htr, -, hadd⟩ := h
  obtain ⟨et, hst⟩ := hadd.addIndTypes
  exact hadd.find?_of_not_mem hwf fun hm => hn (htr.mem_indDeclNames hst hm)

/-- **The restated obligation, whole.**  Discharging this and flipping `AddInduct` to
`AddInductStages` discharges `addDecl.WF`'s `inductDecl` branch for a safe block whose
elaboration introduces no auxiliary nested type.  Nothing here is proved; the point of
writing it as a `Prop` is that it elaborates, so the shape is checked rather than described.

Not covered, deliberately, and see the module header for why neither is a gap this statement
can close:

* `isUnsafe = true` — `TrEnv'` has no rule at `safety = .unsafe`;
* a block with auxiliary nested types — §2 refutes `AddInductStages` for it. -/
def AddInductiveObligation : Prop :=
  ∀ {env : Environment} {ves : VEnvs}, ves.WF env →
    ∀ (lp : List Name) (np : Nat) (types : List InductiveType) (ap : Bool) (fuel : FuelConfig),
      (Environment.addInductive env lp np types false ap fuel).WF fun env' =>
        env'.quotInit = env.quotInit ∧
        ∃ ves' : VEnvs, ∀ safety,
          InductStepSafe env.constants env'.constants (ves.venv safety) (ves'.venv safety)
            lp np types

/-! ### The obligation fires at a witness

`InductFlip.lean`'s `R10.Wit` supplies `decl.WF VEnv.empty` and `AddInductStages`; what it
did not supply is the *syntactic* half, so the two were never joined.  They are joined here:
`inductStepSafe_wit` is a closed instance of `InductStepSafe`, so the obligation above is not
vacuously satisfiable-looking — it has a model. -/

namespace R10.Wit

/-- `inductive U : Type where | unit : U`, as the kernel declaration. -/
def uIndType : InductiveType :=
  { name := `R10.Wit.U, type := .sort (.succ .zero),
    ctors := [{ name := `R10.Wit.U.unit, type := .const `R10.Wit.U [] }] }

theorem tr_uType : TrExprS VEnv.empty [] [] uIndType.type
    (decl.types.getD 0 default).type := .sort rfl

theorem tr_uUnit {env₁ : VEnv} (h : VEnv.empty.addIndTypes decl = some env₁) :
    TrExprS env₁ [] [] (.const `R10.Wit.U [])
      (((decl.types.getD 0 default).ctors.getD 0 default).type decl 0) :=
  .const (VEnv.addConstList_constants h (`R10.Wit.U, ⟨0, .sort (.succ .zero)⟩)
    (List.Mem.head _)) rfl rfl

/-- **The syntactic half at the `AddInductStages` witness.** -/
theorem trIndDecl_wit : TrIndDecl VEnv.empty [] 0 [uIndType] false decl where
  safe := rfl
  uvars := rfl
  np := rfl
  length := rfl
  trType := by
    intro j t T ht hT
    match j, ht, hT with
    | 0, ht, hT => cases ht; cases hT; exact ⟨rfl, tr_uType⟩
  trCtorsLen := by
    intro j t T ht hT
    match j, ht, hT with
    | 0, ht, hT => cases ht; cases hT; rfl
  trCtors := by
    intro env₁ h j t T ht hT q c C hc hC
    match j, ht, hT with
    | 0, ht, hT =>
      cases ht; cases hT
      match q, hc, hC with
      | 0, hc, hC => cases hc; cases hC; exact ⟨rfl, tr_uUnit h⟩

/-- **`InductStepSafe` has a model.**  All three conjuncts at once, at the empty environment
and any empty well-formed constant map. -/
theorem inductStepSafe_wit {m : ConstMap} (hwf : m.WF) (hfr : ∀ n, m.find? n = none) :
    ∃ m' venv', InductStepSafe m m' VEnv.empty venv' [] 0 [uIndType] := by
  obtain ⟨m', venv', H, -, -, -, -, -⟩ := addInductStages_wit hwf hfr
  exact ⟨m', venv', decl, trIndDecl_wit, decl_WF, H⟩

end R10.Wit

/-! ## 4. The branch is false, and the executable facts that make it so

`VEnvs.WF.no_inductInfo` (`Verify/InductFlip.lean`) is the proved half: the postcondition of
`addDecl.WF` is `False` at any environment whose map holds an `.inductInfo`.  The other half
is that the checker produces such an environment, which is a fact about the *executable* and
is recorded below as a build-time check.

`addDecl` does not reduce in the kernel — `by rfl` on `isOk (addDecl (Environment.empty
`main) uDecl)` fails in two seconds — so short of `native_decide`, which `Verify/Guard.lean`
forbids, there is no way to make that half a proof.  The checks are therefore **tests**; the
theorems do not depend on them. -/

/-- The proved half: no `VEnvs` models an environment holding an `.inductInfo`, so the
`inductDecl` branch's postcondition is `False` at every environment the inductive path of the
checker produces. -/
theorem addDecl_inductDecl_post_false {env' : Environment} {ves : VEnvs} {n v}
    (h : env'.constants.find? n = some (.inductInfo v)) : ¬ ves.WF env' :=
  fun wf => wf.no_inductInfo h

/-- **`addDecl.WF`'s `inductDecl` branch is false, not open** — conditionally on the checker
accepting one inductive declaration from one modelled environment, which check A below
verifies by evaluation. -/
theorem addDecl_inductDecl_WF_false
    (hex : ∃ (env env' : Environment) (ves : VEnvs) (n : Name) (v : InductiveVal)
        (lp : List Name) (np : Nat) (types : List InductiveType) (iu : Bool) (fuel : FuelConfig),
      ves.WF env ∧
      Lean4Lean.addDecl env (.inductDecl lp np types iu) (check := true) (fuel := fuel)
        = .ok env' ∧
      env'.constants.find? n = some (.inductInfo v)) :
    ¬ ∀ {env : Environment} {ves : VEnvs}, ves.WF env →
        ∀ (lp : List Name) (np : Nat) (types : List InductiveType) (iu : Bool)
          (fuel : FuelConfig),
        (Lean4Lean.addDecl env (.inductDecl lp np types iu) (check := true) (fuel := fuel)).WF
          fun env' => ∃ ves' : VEnvs, ves'.WF env' ∧ ∀ safety, ves.venv safety ≤ ves'.venv safety
      := by
  rintro H
  obtain ⟨env, env', ves, n, v, lp, np, types, iu, fuel, wf, hok, hfind⟩ := hex
  obtain ⟨ves', hwf', -⟩ := H wf lp np types iu fuel _ hok
  exact addDecl_inductDecl_post_false hfind hwf'

/-- `inductive U : Type where | unit : U`, as a kernel declaration. -/
def uDecl : Declaration := .inductDecl [] 0 [R10.Wit.uIndType] false

/- **Check A** (test, not a proof).  The checker accepts `uDecl` from the empty environment
and the result holds a safe `.inductInfo` at `R10.Wit.U`.  With `VEnvs.trivial_WF` this is the
missing premise of `addDecl_inductDecl_WF_false`. -/
#eval show Lean.CoreM Unit from do
  match Lean4Lean.addDecl (Kernel.Environment.empty `main) uDecl (check := true) with
  | .error _ => throwError "check A: the checker rejected the U block"
  | .ok env' =>
    let some (.inductInfo v) := env'.constants.find? `R10.Wit.U
      | throwError "check A: R10.Wit.U is not an inductInfo in the output map"
    unless v.isUnsafe = false do throwError "check A: U came out unsafe"

/-! ## 5. The honest restatement

§4 shows `addDecl.WF` is **false**.  This section writes down the statement that replaces it.

The shape is forced by two facts, both established above:

* the old conclusion `∃ ves', ves'.WF env'` is refuted at every environment the inductive
  path produces (`addDecl_inductDecl_post_false`), so the restatement **must not** assert it
  there;
* the conclusion of `addDecl.WF` is one predicate applied at every constructor of
  `Declaration`, so the restatement changes **a definition the statement quantifies over** —
  here `AddDeclPost`, a postcondition that is the old one at the six non-inductive forms and
  the honest obligation at `inductDecl`.

`AddDeclPost` is *weaker* than the old postcondition only at `inductDecl`; §5.4 shows what
recovers the difference, and that the missing ingredient is exactly `AddInduct`'s emptiness
and nothing else.
-/

/-- **The `inductDecl` branch's honest postcondition.**

`InductStepNested` (`Verify/Environment/InductR.lean`) rather than `InductStepSafe`: the
nested path adds one renamed auxiliary recursor per nested type, which refutes
`AddInductStages` (§2), and `InductStepNested` is the repair.  It carries, as separate
conjuncts, the syntactic translation, `∃ et, venv.addIndTypes D = some et` (without which
`VInductDecl'.WF.ctors` goes vacuous — `fooComp_WF`), the declaration's well-formedness
`VInductDecl'.WF` (**not** the re-staged `WFC`: the auxiliary block is checked in a scratch
environment where its `_nested.*` types *are* declared), and the constant-map step.

`numNested` is existential because the checker computes it; `ves'` is existential for the
same reason `addDecl.WF`'s is. -/
def AddInductPost (env env' : Environment) (ves : VEnvs)
    (lp : List Name) (np : Nat) (types : List InductiveType) : Prop :=
  ∃ (ves' : VEnvs) (numNested : Nat), ∀ safety,
    InductStepNested env.constants env'.constants
      (ves.venv safety) (ves'.venv safety) lp np types numNested

/-- The monotonicity half of the old postcondition survives the weakening. -/
theorem AddInductPost.exists_le {env env' ves lp np types}
    (h : AddInductPost env env' ves lp np types) :
    ∃ ves' : VEnvs, ∀ safety, ves.venv safety ≤ ves'.venv safety :=
  let ⟨ves', _, h⟩ := h; ⟨ves', fun safety => (h safety).le⟩

/-- The map is determined outside the block, auxiliary recursors included — the anti-lie
property, at the level `addDecl`'s callers consume it. -/
theorem AddInductPost.find?_of_not_mem {env env' ves lp np types}
    (h : AddInductPost env env' ves lp np types) (hwf : env.constants.WF) :
    ∃ nn : Nat, ∀ n ∉ indDeclNamesN types nn,
      env'.constants.find? n = env.constants.find? n := by
  obtain ⟨_, nn, h⟩ := h
  exact ⟨nn, fun n hn => (h .safe).find?_of_not_mem hwf hn⟩

/-- **The honest postcondition of `addDecl`.**  The old one at the six non-inductive forms;
`AddInductPost` at `inductDecl`.

The `iu = false` guard is not a convenience: an *unsafe* inductive has no `TrEnv'` rule at
`safety = .unsafe` at all (§1.1), before or after the flip, so there is nothing true to
assert there.  That is a missing rule in `Verify/Environment/Basic.lean` — a design decision
about `TrEnv'`, not a proof obligation — and it is recorded here rather than papered over. -/
def AddDeclPost (env : Environment) (decl : Declaration) (ves : VEnvs)
    (env' : Environment) : Prop :=
  match decl with
  | .inductDecl lp np types iu => iu = false → AddInductPost env env' ves lp np types
  | _ => ∃ ves' : VEnvs, ves'.WF env' ∧ ∀ safety, ves.venv safety ≤ ves'.venv safety

/-- Outside `inductDecl` the restatement is the old statement, verbatim. -/
theorem AddDeclPost.eq_old {env env' ves} {decl : Declaration}
    (h : ∀ lp np types iu, decl ≠ .inductDecl lp np types iu) :
    AddDeclPost env decl ves env' =
      ∃ ves' : VEnvs, ves'.WF env' ∧ ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  cases decl with
  | inductDecl lp np types iu => exact absurd rfl (h lp np types iu)
  | _ => rfl

/-! ### 5.1 The one obligation the restatement leaves

Everything else is proved.  This is the checker-side statement — that
`Environment.addInductive` realises the abstract step — and it is the *whole* remaining
content of `addDecl.WF`'s inductive branch under the honest postcondition. -/

/-- **The single open obligation.**  Not refuted by `VEnvs.WF.no_inductInfo`: its conclusion
does not assert `ves'.WF env'`.  Its consequent is satisfiable (§5.3). -/
def AddInductiveStepWF : Prop :=
  ∀ {env : Environment} {ves : VEnvs}, ves.WF env →
    ∀ (lp : List Name) (np : Nat) (types : List InductiveType) (ap : Bool)
      (fuel : FuelConfig),
      (Environment.addInductive env lp np types false ap fuel).WF fun env' =>
        AddInductPost env env' ves lp np types

/-- **The honest restatement, proved.**  No `sorry`: the six non-inductive branches are the
ones `Verify/Environment.lean` already discharges, and the seventh is exactly
`AddInductiveStepWF`.

Contrast `addDecl.WF`, whose `inductDecl` branch cannot be discharged by *any* hypothesis
whose consequent is honest, because the branch's conclusion is refuted outright. -/
theorem addDecl.WF_honest (H : AddInductiveStepWF) {env : Environment} {ves : VEnvs}
    (wf : ves.WF env) (decl : Declaration) (fuel : FuelConfig := {}) :
    (Lean4Lean.addDecl env decl (check := true) (fuel := fuel)).WF
      (AddDeclPost env decl ves) := by
  cases decl with
  | axiomDecl v =>
    exact (addAxiom.WF wf v fuel).mono fun _ ⟨ves', hwf, _, h⟩ => ⟨ves', hwf, (h · |>.le)⟩
  | thmDecl v =>
    exact (addTheorem.WF wf v fuel).mono fun _ ⟨ves', hwf, _, h⟩ => ⟨ves', hwf, (h · |>.le)⟩
  | defnDecl v => exact (addDefinition.WF wf v fuel).mono fun _ ⟨ves', hwf, h, _⟩ => ⟨ves', hwf, h⟩
  | opaqueDecl v =>
    exact (addOpaque.WF wf v fuel).mono fun _ ⟨ves', hwf, _, h⟩ => ⟨ves', hwf, (h · |>.le)⟩
  | quotDecl => exact addQuot.WF wf
  | mutualDefnDecl vs => exact addMutual.WF wf vs fuel
  | inductDecl lp np types iu =>
    cases iu with
    | true => exact fun _ _ => nofun
    | false =>
      refine Except.WF.bind (Q := fun _ => True) (fun _ _ => trivial) fun ap _ => ?_
      exact (H wf lp np types ap fuel).mono fun _ h _ => h

/-! ### 5.2 What the flip buys, exactly

The honest arm is not a permanent weakening.  `AddInductFlip` below is the *only* thing that
stands between `AddInductPost` and the old conclusion's `TrEnv'` step, and it is a change to
`Verify/Environment/Basic.lean`'s `AddInduct` — a file this stream does not own. -/

/-- `AddInduct` accepting the nested constant-map step.  False today, since `AddInduct` has
no constructors and `AddInductStagesR` has witnesses (`inductStepNested_wit_closed`); that is
precisely the emptiness the flip removes. -/
def AddInductFlip : Prop :=
  ∀ {m m' : ConstMap} {env env' : VEnv} {D : VInductDecl'} {K : List Name} {R : VIndRestore},
    AddInductStagesR m env D K R m' env' → AddInduct m env D m' env'

/-- **The honest arm delivers the `TrEnv'` step, given the flip and nothing else.**  Both
premises `TrEnv'.induct` consumes come out of `InductStepNested` directly: no extra
hypothesis, no side condition, no appeal to the syntactic half. -/
theorem InductStepNested.trEnv' {safety : DefinitionSafety} {m m' : ConstMap}
    {venv venv' : VEnv} {Q : Bool} {lp np types nn}
    (hflip : AddInductFlip) (h : InductStepNested m m' venv venv' lp np types nn)
    (H : TrEnv' safety m Q venv) : TrEnv' safety m' Q venv' :=
  let ⟨_, _, _, _, _, hwfD, hadd⟩ := h; .induct hwfD (hflip hadd) H

/-- The three `VEnvs.WF` fields the step above does **not** supply, named so that the
remaining distance to the old conclusion is a list rather than a gesture:
`hasPrimitives`, `safePrimitives` and `mono` at the new environment.  The first two are
`VEnv.HasPrimitives.extend` plus `AddInductStagesR.find?_shape`'s safety gate (§1); the third
is `AddInductStagesR.le` at each pair of safety levels. -/
theorem InductStepNested.mono_of {m m' : ConstMap} {venv venv' : VEnv} {lp np types nn}
    (h : InductStepNested m m' venv venv' lp np types nn) : venv ≤ venv' := h.le

/-! ### 5.3 Non-vacuity, and the separation from the refuted arm

The acceptance criterion is that the honest arm holds somewhere the old arm is refuted.  The
old arm is refuted exactly at a map holding an `.inductInfo`
(`addDecl_inductDecl_post_false`).  So the witness has to be one whose *output map holds an
`.inductInfo`* — not merely one where the three conjuncts happen to meet. -/

/-! The map a stage produces still holds everything the stage started with — each `cons`
demands freshness in the map it inserts into, so no later element of the list can collide
with an earlier one. -/

theorem AddIndConsts.find?_mono {S : ConstantInfo → Prop} {cs m env m₂ env₂}
    (H : AddIndConsts S cs m env m₂ env₂) (hwf : m.WF) {n ci}
    (h : m.find? n = some ci) : m₂.find? n = some ci := by
  induction H generalizing ci with
  | nil => exact h
  | @cons ci₀ n₀ _ _ m _ _ _ _ _ _ _ hfr _ _ ih =>
    refine ih (hwf.insert _ _ hfr) ?_
    rw [hwf.find?_insert]
    split
    · rename_i hb; rw [(by simpa using hb : n₀ = n)] at hfr; rw [hfr] at h; exact absurd h nofun
    · exact h

/-- **The head of a stage's constant list really lands in the output map**, with the stage's
shape.  This is what makes a witness for the honest arm carry the very `.inductInfo` that
refutes the old one. -/
theorem AddIndConsts.find?_head {S : ConstantInfo → Prop} {n ci' cs m env m₂ env₂}
    (H : AddIndConsts S ((n, ci') :: cs) m env m₂ env₂) (hwf : m.WF) :
    ∃ ci, S ci ∧ ci.name = n ∧ m₂.find? n = some ci := by
  cases H with
  | cons hname hS _ hfr _ Hrest =>
    refine ⟨_, hS, hname, Hrest.find?_mono (hwf.insert _ _ hfr) ?_⟩
    rw [hwf.find?_insert]; simp

/-- The first type constant of a block reaches the output map as an `.inductInfo` — and, since
the type stage now carries `IndShapeOf`, with the block bookkeeping that `.inductInfo` must
have.  The extra conjunct is what `StructureBridge` reads. -/
theorem AddInductStages.find?_type_head {m₁ m₂ : ConstMap} {env₁ env₂ : VEnv}
    {D : VInductDecl'} {n ci' cs} (H : AddInductStages m₁ env₁ D m₂ env₂) (hwf : m₁.WF)
    (hts : D.typeConsts = (n, ci') :: cs) :
    ∃ v : InductiveVal, m₂.find? n = some (.inductInfo v) ∧
      IndShapeOf D id (.inductInfo v) := by
  obtain ⟨mt, et, mc, ec, e₃, h1, h2, h3, -⟩ := H
  rw [hts] at h1
  obtain ⟨ci, hS, -, hfind⟩ := h1.find?_head hwf
  obtain ⟨v, rfl⟩ := hS.inductInfo
  exact ⟨v, h3.find?_mono (h2.map_wf (h1.map_wf hwf)) (h2.find?_mono (h1.map_wf hwf) hfind), hS⟩

/-- The nested analogue, over `typeConstsC`. -/
theorem AddInductStagesR.find?_type_head {m₁ m₂ : ConstMap} {env₁ env₂ : VEnv}
    {D : VInductDecl'} {K : List Name} {R : VIndRestore} {n ci' cs}
    (H : AddInductStagesR m₁ env₁ D K R m₂ env₂) (hwf : m₁.WF)
    (hts : D.typeConstsC K = (n, ci') :: cs) :
    ∃ v : InductiveVal, m₂.find? n = some (.inductInfo v) ∧
      IndShapeOf D R.ctorName (.inductInfo v) := by
  obtain ⟨mt, et, mc, ec, e₃, h1, h2, h3, -⟩ := H
  rw [hts] at h1
  obtain ⟨ci, hS, -, hfind⟩ := h1.find?_head hwf
  obtain ⟨v, rfl⟩ := hS.inductInfo
  exact ⟨v, h3.find?_mono (h2.map_wf (h1.map_wf hwf)) (h2.find?_mono (h1.map_wf hwf) hfind), hS⟩

namespace R10.Wit

/-- **`InductStepSafe` holds at a map that carries an `.inductInfo`.**  This is the
separation: the very fact that refutes `∃ ves', ves'.WF env'` is *present* here, and the
honest conjuncts hold anyway. -/
theorem inductStepSafe_wit_inductInfo {m : ConstMap} (hwf : m.WF) (hfr : ∀ n, m.find? n = none) :
    ∃ m' venv', InductStepSafe m m' VEnv.empty venv' [] 0 [uIndType] ∧
      ∃ v : InductiveVal, m'.find? `R10.Wit.U = some (.inductInfo v) := by
  obtain ⟨m', venv', H, -, -, -, -, -⟩ := addInductStages_wit hwf hfr
  obtain ⟨v, hv, -⟩ := H.find?_type_head hwf rfl
  exact ⟨m', venv', ⟨decl, trIndDecl_wit, decl_WF, H⟩, v, hv⟩

end R10.Wit

/-- **The separation, stated once.**  At one and the same constant map: the honest arm's
three conjuncts hold, and the map carries an `.inductInfo` — the hypothesis from which
`addDecl_inductDecl_post_false` derives `¬ ves.WF env'` for every kernel environment built
over that map.

So the restatement is not a relabelling: it moves the branch from *refuted* to *open*. -/
theorem addDeclPost_separation {m : ConstMap} (hwf : m.WF) (hfr : ∀ n, m.find? n = none) :
    (∃ m' venv', InductStepSafe m m' VEnv.empty venv' [] 0 [R10.Wit.uIndType] ∧
        ∃ v : InductiveVal, m'.find? `R10.Wit.U = some (.inductInfo v)) ∧
    (∀ (env' : Environment) (ves : VEnvs) (n : Name) (v : InductiveVal),
      env'.constants.find? n = some (.inductInfo v) → ¬ ves.WF env') := by
  refine ⟨?_, fun _ _ _ _ h => addDecl_inductDecl_post_false h⟩
  exact R10.Wit.inductStepSafe_wit_inductInfo hwf hfr

/-- The nested half of the same fact: `AddInductPost`'s conjunct at a *nested* block, where
`AddInductStages` is refuted and `AddInductStagesR` is not.  Read off
`inductStepNested_wit_closed`, at the environment in which `PFn` has just been declared. -/
theorem addInductPost_nested_nonvacuous {env₂ : VEnv}
    (h : VEnv.empty.addInduct' InductiveDeclExamples.pfnDecl = some env₂)
    {m : ConstMap} (hwf : m.WF) (hfr : ∀ n, m.find? n = none) :
    ∃ m' env', InductStepNested m m' env₂ env' [] 0 [NestedWit.nfnIndType] 1 ∧
      m'.find? ``InductiveDeclExamples.NFn.rec_1 = some (.recInfo NestedWit.nfnRec1CI) :=
  NestedWit.inductStepNested_wit_closed h hwf hfr

/-! ### 5.4 What landing the restatement at `addDecl.WF` itself costs

`addDecl.WF`'s statement is pinned from outside this stream: `Verify/Bridge.lean`'s
`AddDeclWF` repeats it verbatim and `Bridge.addDeclWF` discharges it by
`fun wf decl => addDecl.WF wf decl fuel`.  Replacing `addDecl.WF`'s conclusion by
`AddDeclPost` therefore requires, in that file:

1. `AddDeclWF fuel`'s body to become `… .WF (AddDeclPost env decl ves)`;
2. `foldlM_addDecl_WF` to carry a fold-level invariant instead of `∃ ves', ves'.WF env' ∧ …`,
   since the honest arm does not compose with itself — the *next* step's `wf : ves.WF env`
   is not available after an inductive one;
3. `foldAddDecl_tr` to become a hypothesis alongside `PreludeBridge`, since `TrEnv .safe`
   is exactly what the honest arm stops supplying.

Item 2 is the real content: it is blocked on the same `AddInduct` emptiness, because
`Bridge`'s whole chain is already false past `stdPrelude`'s first declaration (`eqDecl`, an
`.inductDecl`).  Nothing here is edited in `Verify/Bridge.lean`; the restatement is proved
where this stream owns it, and the three-line change above is stated rather than made. -/


end Lean4Lean
