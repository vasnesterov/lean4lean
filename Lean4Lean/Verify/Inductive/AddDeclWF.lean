import Lean4Lean.Verify.Bridge
import Lean4Lean.Verify.Environment.Induct

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
`VInductDecl'` grows them; nothing else will do. -/

/-- Every name a `Lean.Declaration.inductDecl` block can legitimately introduce: the type
names, the constructor names, and `mkRecName` of each type name. -/
def indDeclNames (types : List InductiveType) : List Name :=
  types.map (·.name) ++ types.flatMap (·.ctors.map (·.name)) ++
    types.map fun t => Lean.mkRecName t.name

theorem exists_getElem?_of_lt {α} {l : List α} {j} (h : j < l.length) : ∃ a, l[j]? = some a :=
  ⟨l[j], List.getElem?_eq_getElem h⟩

/-- **`TrIndDecl` pins the block's names.**  Every name the abstract declaration introduces is
one of the declaration's own — a type name, a constructor name, or `mkRecName` of a type
name.  There is no room for an auxiliary constant. -/
theorem TrIndDecl.mem_indDeclNames {env env₁ : VEnv} {Us : List Name} {np : Nat}
    {types : List InductiveType} {iu : Bool} {D : VInductDecl'}
    (h : TrIndDecl env Us np types iu D) (hst : env.addIndTypes D = some env₁)
    {n : Name} (hn : n ∈ D.allNames) : n ∈ indDeclNames types := by
  -- the type-name half, reused for the recursors
  have htypes : ∀ (T : VIndType), T ∈ D.types → ∃ t ∈ types, t.name = T.name := by
    intro T hT
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hT
    have hlt : j < types.length := by
      rw [h.length]; exact List.getElem?_eq_some_iff.1 hj |>.1
    obtain ⟨t, ht⟩ := exists_getElem?_of_lt hlt
    exact ⟨t, List.mem_iff_getElem?.2 ⟨j, ht⟩, (h.trType j t T ht hj).1⟩
  simp only [VInductDecl'.allNames, VInductDecl'.allConsts, List.map_append,
    List.mem_append] at hn
  simp only [indDeclNames, List.mem_append]
  rcases hn with (hn | hn) | hn
  · -- a type name
    simp only [VInductDecl'.typeConsts, List.map_map, List.mem_map, Function.comp] at hn
    obtain ⟨T, hT, rfl⟩ := hn
    obtain ⟨t, ht, hname⟩ := htypes T hT
    exact .inl (.inl (List.mem_map.2 ⟨t, ht, hname⟩))
  · -- a constructor name
    simp only [VInductDecl'.ctorConsts, List.map_map, List.mem_map, Function.comp] at hn
    obtain ⟨⟨j, C⟩, hjC, rfl⟩ := hn
    obtain ⟨T, hT, hC⟩ := VInductDecl'.mem_ctorsAll hjC
    have hlt : j < types.length := by
      rw [h.length]; exact List.getElem?_eq_some_iff.1 hT |>.1
    obtain ⟨t, ht⟩ := exists_getElem?_of_lt hlt
    obtain ⟨q, hq⟩ := List.mem_iff_getElem?.1 hC
    have hqlt : q < t.ctors.length := by
      rw [h.trCtorsLen j t T ht hT]; exact List.getElem?_eq_some_iff.1 hq |>.1
    obtain ⟨c, hc⟩ := exists_getElem?_of_lt hqlt
    have hname : c.name = C.name := (h.trCtors env₁ hst j t T ht hT q c C hc hq).1
    refine .inl (.inr (List.mem_flatMap.2 ⟨t, List.mem_iff_getElem?.2 ⟨j, ht⟩, ?_⟩))
    exact List.mem_map.2 ⟨c, List.mem_iff_getElem?.2 ⟨q, hc⟩, hname⟩
  · -- a recursor name
    simp only [VInductDecl'.recConsts, List.map_map, List.mem_map, Function.comp] at hn
    obtain ⟨⟨T, j⟩, hTj, rfl⟩ := hn
    have hT : T ∈ D.types := by
      have := List.mem_map_of_mem (f := Prod.fst) hTj
      simpa using this
    obtain ⟨t, ht, hname⟩ := htypes T hT
    exact .inr (List.mem_map.2 ⟨t, ht, by rw [hname]⟩)

/-- **The nested wall.**  If the checker's output map holds a name the declaration does not
mention, then *no* `VInductDecl'` translating that declaration stands in `AddInductStages`
between the two maps.

Instantiated at `types := [T]` with `T.ctors = [T.mk]` and `n := `T.rec_1` this refutes the
flipped `AddInduct` for the nested block of §4's second check. -/
theorem TrIndDecl.not_addInductStages {env env₂ : VEnv} {Us : List Name} {np : Nat}
    {types : List InductiveType} {iu : Bool} {D : VInductDecl'} {m₁ m₂ : ConstMap}
    (h : TrIndDecl env Us np types iu D) (hwf : m₁.WF)
    {n : Name} (h₁ : m₁.find? n = none) (h₂ : m₂.find? n ≠ none)
    (hn : n ∉ indDeclNames types) :
    ¬ AddInductStages m₁ env D m₂ env₂ := by
  intro H
  obtain ⟨et, hst⟩ := H.addIndTypes
  exact h₂ <| by
    rw [H.find?_of_not_mem hwf fun hm => hn (h.mem_indDeclNames hst hm), h₁]

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
`fooComp_WFC` showed a re-staged *check* does not achieve. -/

/-- **The `inductDecl` branch's real obligation, at one safety level, for a safe block.**

Both halves are needed and neither excuses the other: `TrIndDecl` says the abstract
declaration describes the syntax the user wrote, `VInductDecl'.WF` says it is a legitimate
declaration, and `AddInductStages` says the checker's output map and the abstract environment
are the ones that declaration builds. -/
def InductStepSafe (m m' : ConstMap) (venv venv' : VEnv)
    (lp : List Name) (np : Nat) (types : List InductiveType) : Prop :=
  ∃ D : VInductDecl',
    TrIndDecl venv lp np types false D ∧ D.WF venv ∧ AddInductStages m venv D m' venv'

/-- The premises `TrEnv'.induct` consumes, once `AddInduct := AddInductStages`. -/
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

/-- `∀ (A : Type), A → Box A` -/
def boxMkTypeE : Expr :=
  .forallE `A (.sort 1) (.forallE `a (.bvar 0) (.app (.const `Box []) (.bvar 1)) .default)
    .default

/-- `inductive Box (A : Type) : Type where | mk : A → Box A` -/
def boxIndType : InductiveType :=
  { name := `Box, type := .forallE `A (.sort 1) (.sort 1) .default,
    ctors := [{ name := `Box.mk, type := boxMkTypeE }] }

/-- `Box T → T` -/
def tMkTypeE : Expr :=
  .forallE `b (.app (.const `Box []) (.const `T [])) (.const `T []) .default

/-- `inductive T : Type where | mk : Box T → T` — a **nested** block: `Box T` is a nested
occurrence, so elaboration introduces an auxiliary type `_nested.Box_1` and, with it, an
auxiliary recursor that the final environment carries under the name `T.rec_1`. -/
def tIndType : InductiveType :=
  { name := `T, type := .sort 1, ctors := [{ name := `T.mk, type := tMkTypeE }] }

def boxDecl : Declaration := .inductDecl [] 1 [boxIndType] false
def tDecl : Declaration := .inductDecl [] 0 [tIndType] false

/-- `T.rec_1` is not a name the `T` block declares. -/
theorem trec1_not_declared : (`T.rec_1 : Name) ∉ indDeclNames [tIndType] := by
  simp [indDeclNames, tIndType, Lean.mkRecName]

/-- **The nested block refutes the flipped `AddInduct`.**  No `VInductDecl'` translating the
`T` block stands in `AddInductStages` between a map without `T.rec_1` and one with it — and
check B below verifies by evaluation that those are exactly the maps the checker produces.

So the flip of `docs/handoff-addinduct.md` §6, even carried out in full, does **not** make
`addDecl.WF`'s `inductDecl` branch true for a nested declaration.  The repair is on the
constant-map side: a fourth `AddIndConsts` stage for the auxiliary recursors, or auxiliary
recursors in `VInductDecl'`. -/
theorem tBlock_not_addInductStages {env env₂ : VEnv} {D : VInductDecl'} {m₁ m₂ : ConstMap}
    (h : TrIndDecl env [] 0 [tIndType] false D) (hwf : m₁.WF)
    (h₁ : m₁.find? `T.rec_1 = none) (h₂ : m₂.find? `T.rec_1 ≠ none) :
    ¬ AddInductStages m₁ env D m₂ env₂ :=
  h.not_addInductStages hwf h₁ h₂ trec1_not_declared

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

/- **Check B** (test, not a proof).  The nested block `T` adds `T.rec_1` — a recursor whose
name is `mkRecName` of no type the block declares — so `tBlock_not_addInductStages`'s premises
are met by the checker's own output. -/
#eval show Lean.CoreM Unit from do
  let e0 := Kernel.Environment.empty `main
  let .ok e1 := Lean4Lean.addDecl e0 boxDecl (check := true)
    | throwError "check B: the checker rejected the Box block"
  let .ok e2 := Lean4Lean.addDecl e1 tDecl (check := true)
    | throwError "check B: the checker rejected the nested T block"
  unless (e1.constants.find? `T.rec_1).isNone do
    throwError "check B: T.rec_1 was already present before the T block"
  unless (e2.constants.find? `T.rec_1).isSome do
    throwError "check B: the nested block did NOT add T.rec_1 -- the finding has regressed"
  let some (.inductInfo v) := e2.constants.find? `T | throwError "check B: T missing"
  unless v.numNested = 1 do throwError "check B: T is not nested"

end Lean4Lean
