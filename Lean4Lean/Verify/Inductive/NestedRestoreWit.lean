import Lean4Lean.Verify.Inductive.NestedRestore

/-!
# `mkRestore` at the checker's own data, and the full nested step it carries

`Verify/Inductive/NestedRestore.lean` §5 builds `ElimNestedInductive.Result.mkRestore` — a
`VIndRestore` computed from the checker's `Result` — and derives all four name-discipline
obligations (`OwnId`, `NestedBarrier`, `SubstFree`, `KeysFree`) from a fourteen-field
`RestoreData` bundle.  **Nothing instantiated that bundle**, so `mkRestore_discipline` had no
witness at all: a fourteen-field hypothesis with no model is exactly the vacuity risk
`docs/vacuity-ledger.md` rows 11/11a are about.  This file supplies the model, at the nested
block `Theory/Inductive/NestedBuild.lean` Part 9 already carries:

```
inductive PFn (α : Type) | mk : α → (Prop → α) → PFn α
inductive NFn            | node : PFn NFn → NFn
```

and then follows the consequences all the way to `VEnv.AddNested`.

## What is established

* §1 `nfnResult`, the checker's data at that block, and a **fidelity check against the
  implementation**: `ElimNestedInductive.run`, actually executed on the block, produces a
  `Result` whose type names, constructor names, `aux2nested` keys, `presentedHead`,
  `ctorRenames` and `recRenames` are the ones `nfnResult` records — up to one measured
  difference, §1.1.
* §2 `nfnResult_restoreData` — **all fourteen fields of `RestoreData`, at once.**  So
  `RestoreData` is satisfiable and `mkRestore_discipline` is not vacuous.  §2.1 is the lower
  bound on the split with §6: a one-`Expr` perturbation at which the whole bundle and all four
  name-discipline obligations still hold and `§6`'s residue is **false**.
* §3 the two-way bound between `mkRestore` and the hand-written `nfnRestore`: four of five
  fields are **equal as functions**, `tyName` agrees at every member of the block, and the two
  restorations are nevertheless **not equal** (they differ off the block).  What the step
  *declares* — `ctorConstsCR`, `recConstsR`, `iotaRulesRS` — is identical.
* §4 the four name-discipline obligations, at this data, by instantiation.
* §5 `trIndDeclN_wit'`: `TrIndDeclN` at `mkRestore` in place of `nfnRestore`.  This is the
  import `Verify/Environment/InductR.lean`'s nested witness made unnecessary.
* §6 the general bridge: `RestoreData` discharges four of `VInductDecl'.Built`'s eight clauses,
  the other four are named `OccResidue`, and with them `Faithful`, `Canonical`, `AddNested` and
  `AddNestedStep` are **theorems** about a `mkRestore`-derived restoration.
* §7 `OccResidue` satisfied, and hence `Built`, `Faithful`, `VEnv.AddNestedB`, `VEnv.AddNested`
  and `VEnv.AddNestedStep`, all at `mkRestore`, at the `NFn` block.
* §8 the constant-map half: `AddInductStagesR` and `InductStepNested` at `mkRestore`.  So
  `Verify/Environment/InductR.lean` §6's nested witness no longer needs the hand-written
  restoration at any of its three conjuncts.

## A correction: `Faithful` and `Canonical` were not open

The handoff this file answers said that `VIndRestore.Faithful` and `VInductDecl'.Canonical`
were the two things "still owed for a full `VEnv.AddNested`", and that `Faithful` would need
"the translation relation itself".  Both already had general routes in `Theory/`, one import
away:

* `VInductDecl'.Built.toFaithful` (`Theory/Inductive/NestedBuild.lean:491`) proves all three
  `Faithful` clauses from `VInductDecl'.Built`, which replaces them by *one*: the companion
  member **is** the value the construction computes.  No `TrExprS` appears.
* `VInductDecl'.Built.canonical` (`:528`) proves `D.Canonical` from `Built` plus
  `CanonicalOwn` — canonicity on the members the *user* wrote.
* `VEnv.AddNestedB.toAddNested` (`:551`) assembles both, and `nfnAux_AddNested` (`:1329`)
  already witnessed the whole step at this very block, with the hand-written `nfnRestore`.

So what was owed is narrower and this file does it: the same conclusions at the restoration the
**checker's own data** determines, plus the general bridge that says which clauses those data
reach (§6) and a measurement showing the rest is not slack (§2.1).  §9 records what is left.
-/

namespace Lean4Lean

open Lean hiding Environment
open Kernel

namespace NestedWit
open InductiveDeclExamples ElimNestedInductive

/-! ## 1. The checker's data at the `NFn` block -/


/-- **The checker's own data at the nested block.**  `ElimNestedInductive.run`, executed on
`inductive NFn | node : PFn NFn → NFn`, produces exactly this — see the fidelity check below.

The one departure is the auxiliary member's *spelling*: `mkUniqueName (`_nested ++ ``PFn)`
returns the fully qualified `` `_nested.Lean4Lean.InductiveDeclExamples.PFn_1 ``, while
`Theory/Inductive/NestedBuild.lean`'s abstract block `nfnAux` abbreviates it to
`` `_nested.PFn_1 ``.  The `D`-side name is what `RestoreData.name` must match, so the
abbreviation is what this `Result` carries; §1.1 checks that every property used of it holds of
the real name too.  Nothing the step *declares* mentions either name (`typeConstsC` and
`ctorConstsCR` filter the companion out), which is why the substitution is harmless.

Only the *names* are read by `mkRestore` and `RestoreData`; the `Expr` payloads are written out
as `run` produces them, and nothing below depends on them. -/
def nfnResult : ElimNestedInductive.Result where
  ngen := { namePrefix := `_nested_fresh }
  nparams := 0
  lctx := {}
  params := #[]
  aux2nested := [(`_nested.PFn_1, .app (.const ``PFn []) (.const ``NFn []))]
  types :=
    [{ name := ``NFn, type := .sort (.succ .zero),
       ctors := [{ name := ``NFn.node,
                   type := .forallE `a (.const `_nested.PFn_1 []) (.const ``NFn []) .default }] },
     { name := `_nested.PFn_1, type := .sort (.succ .zero),
       ctors := [{ name := `_nested.PFn_1.mk,
                   type := .forallE `a (.const ``NFn [])
                     (.forallE `b (.forallE `p (.sort .zero) (.const ``NFn []) .default)
                       (.const `_nested.PFn_1 []) .default) .default }] }]

/-- The presented level list at each member.  `mkRestore` takes `tyLvls`/`tyArgs` as
parameters because there is no `Lean.Expr → VExpr` function (`TrExprS` is a relation); these are
the values `pfnOcc` — the abstract occurrence — records, so §6's `Built.tyLvls`/`tyArgs` clauses
hold by `rfl`. -/
def nfnLs : Nat → List VLevel := fun _ => []

/-- …and the presented parameter spine: `PFn` is instantiated at `NFn`. -/
def nfnAs : Nat → List VExpr := fun j => if j = 1 then [.const ``NFn []] else []

/-! The four name computations `mkRestore` performs, at this data. -/
example : nfnResult.companionNames = nfnK := rfl
example : nfnResult.presentedHead `_nested.PFn_1 = ``PFn := rfl
example : nfnResult.ctorRenames 1 = [(`_nested.PFn_1.mk, ``PFn.mk)] := rfl
example : nfnResult.recRenames [nfnIndType] = [(`_nested.PFn_1.rec, ``NFn.rec_1)] := rfl

/-- **The `auxRec` field of `RestoreData`, for every `k`.**  `auxRecName [nfnIndType] k` is
`appendIndexAfter' (mkRecName ``NFn) (k+1)`, i.e. `NFn.rec_(k+1)`; the `modifyBase` in
`appendIndexAfter'` is transparent because `NFn.rec` carries no macro scopes.  Not `decide`:
the statement quantifies over all `k`. -/
theorem nfn_auxRec (k : Nat) : ¬ IsNestedName (auxRecName [nfnIndType] k) := by
  have he : auxRecName [nfnIndType] k
      = .str `Lean4Lean.InductiveDeclExamples.NFn ("rec" ++ "_" ++ toString (k+1)) := rfl
  rw [he]
  intro h
  rcases IsNestedName.str_iff.1 h with h | h
  · rw [show (`_nested : Name) = .str .anonymous "_nested" from rfl, Name.str.injEq] at h
    exact absurd h.1 (by decide)
  · exact absurd h (by decide)

/-! ### 1.1 Fidelity: the same computations at `run`'s actual output -/

/- **Check (test, not a proof).**  `ElimNestedInductive.run`, executed on the `NFn` block in an
environment holding `PFn`, produces a `Result` on which the four name computations `mkRestore`
performs give the values `nfnResult` records — with `` `_nested.PFn_1 `` replaced throughout by
`mkUniqueName`'s real output `` `_nested.Lean4Lean.InductiveDeclExamples.PFn_1 ``.  The last two
loops check the barrier's own test (`IsNestedName`, i.e. `checkNoNestedAux`'s predicate) at the
real names, in both directions: inside for the three auxiliary names, outside for the six the
restoration produces.  So §2's `auxName`/`auxCtorName`/`ownName`/`ownCtor`/`head`/`auxRec` fields
are not artefacts of the abbreviated spelling. -/
#eval show Lean.CoreM Unit from do
  let kenv := (← getEnv).toKernelEnv
  let .ok r := (ElimNestedInductive.run 1000 0 [nfnIndType] kenv).run'
      { lvls := [], newTypes := #[nfnIndType] }
    | throwError "fidelity: run rejected the nested NFn block"
  let auxN := `_nested ++ (``PFn).appendAfter "_1"
  unless r.types.map (·.name) = [``NFn, auxN] do
    throwError "fidelity: types names = {r.types.map (·.name)}, expected {[``NFn, auxN]}"
  unless r.types.map (·.ctors.map (·.name)) = [[``NFn.node], [auxN ++ `mk]] do
    throwError "fidelity: ctor names = {r.types.map (·.ctors.map (·.name))}"
  unless r.aux2nested.map (·.1) = [auxN] do
    throwError "fidelity: aux2nested keys = {r.aux2nested.map (·.1)}"
  unless r.companionNames = [auxN] do
    throwError "fidelity: companionNames = {r.companionNames}"
  unless r.presentedHead auxN = ``PFn do
    throwError "fidelity: presentedHead = {r.presentedHead auxN}"
  unless r.ctorRenames 1 = [(auxN ++ `mk, ``PFn.mk)] do
    throwError "fidelity: ctorRenames = {r.ctorRenames 1}"
  unless r.recRenames [nfnIndType] = [(mkRecName auxN, ``NFn.rec_1)] do
    throwError "fidelity: recRenames = {r.recRenames [nfnIndType]}"
  for n in [auxN, auxN ++ `mk, mkRecName auxN] do
    unless (`_nested).isPrefixOf n do throwError "fidelity: {n} is outside the barrier"
  for n in [(``NFn : Name), ``NFn.node, ``NFn.rec, ``NFn.rec_1, ``PFn, ``PFn.mk] do
    if (`_nested).isPrefixOf n then throwError "fidelity: {n} is inside the barrier"
  logInfo "fidelity: run's Result matches nfnResult, modulo mkUniqueName's spelling \
    of the auxiliary name \u2713"

/-! ## 2. `RestoreData`, satisfied

**Fourteen fields, one witness.**  `NestedRestore.lean` §8.1 grades each field by how far the
implementation is from establishing it in general; this says nothing about that grading — it
says the conjunction is *satisfiable*, so `mkRestore_discipline` and everything derived from it
below is not vacuous. -/

theorem nfnResult_restoreData :
    nfnResult.RestoreData [nfnIndType] nfnAux nfnK nfnAs where
  len := rfl
  name := by
    rintro (_ | _ | j) T hT t ht <;> simp only [nfnAux, nfnResult] at hT ht ⊢ <;>
      first | (cases hT; cases ht; rfl) | simp at hT
  ctor := by
    rintro (_ | _ | j) T hT t ht C hC <;> simp only [nfnAux, nfnResult] at hT ht ⊢ <;>
      first
        | (cases hT; cases ht; simp only [List.mem_cons, List.not_mem_nil, or_false] at hC;
           subst hC; exact ⟨_, List.mem_cons_self, rfl⟩)
        | simp at hT
  companions := by
    rintro (_ | _ | j) T hT <;> simp only [nfnAux] at hT <;> [skip; skip; simp at hT] <;>
      cases hT <;> simp [nfnK]
  auxName := by
    rintro (_ | _ | j) t ht hle
    · exact absurd hle (by simp)
    · simp only [nfnResult] at ht; cases ht; decide
    · simp [nfnResult] at ht
  auxCtorName := by
    rintro (_ | _ | j) t ht hle c hc
    · exact absurd hle (by simp)
    · simp only [nfnResult] at ht; cases ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc; decide
    · simp [nfnResult] at ht
  auxCtorPrefix := by
    rintro (_ | _ | j) t ht hle c hc
    · exact absurd hle (by simp)
    · simp only [nfnResult] at ht; cases ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc; decide
    · simp [nfnResult] at ht
  auxNodup := by decide
  ownName := by
    rintro (_ | _ | j) t ht hlt
    · simp only [nfnResult] at ht; cases ht; decide
    · exact absurd hlt (by simp)
    · exact absurd hlt (by simp)
  ownCtor := by
    rintro (_ | _ | j) t ht hlt c hc
    · simp only [nfnResult] at ht; cases ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc; decide
    · exact absurd hlt (by simp)
    · exact absurd hlt (by simp)
  head := by
    rintro (_ | _ | j) t ht hle
    · exact absurd hle (by simp)
    · simp only [nfnResult] at ht; cases ht; decide
    · simp [nfnResult] at ht
  headNe := by
    rintro (_ | _ | j) t ht hle
    · exact absurd hle (by simp)
    · simp only [nfnResult] at ht; cases ht; decide
    · simp [nfnResult] at ht
  auxRec := nfn_auxRec
  args := by
    intro j a ha
    simp only [nfnAs] at ha
    split at ha
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha; subst ha; decide
    · simp at ha


/-! ### 2.1 `RestoreData` does not imply §6's residue

The perturbation is one `Expr`: `aux2nested` stores `NFn` where the implementation stores
`PFn NFn`, so `presentedHead` — and therefore `mkRestore`'s `tyName` at the companion — names
the wrong type.  **All fourteen `RestoreData` fields still hold**, because the two that read
`presentedHead` only ask that the presented head avoid the `_nested` prefix and be non-anonymous,
which `` `NFn `` does; so all four name-discipline obligations hold too.  What fails is
`OccResidue.head`, hence `Built.tyName`, hence the step.

This is the field-by-field lower bound (`docs/vacuity-ledger.md` rows 11/11a) on the split
between §2 and §6: the residue is not slack in the bundle, it is content `RestoreData` cannot
see. -/

/-- `nfnResult` with the stored nested application replaced by a bare `NFn`. -/
def nfnResultBadHead : ElimNestedInductive.Result :=
  { nfnResult with aux2nested := [(`_nested.PFn_1, .const ``NFn [])] }

example : nfnResultBadHead.presentedHead `_nested.PFn_1 = ``NFn := rfl
example : nfnResult.presentedHead `_nested.PFn_1 = ``PFn := rfl

theorem nfnResultBadHead_restoreData :
    nfnResultBadHead.RestoreData [nfnIndType] nfnAux nfnK nfnAs where
  len := rfl
  name := by
    rintro (_ | _ | j) T hT t ht <;> simp only [nfnAux, nfnResultBadHead, nfnResult] at hT ht ⊢ <;>
      first | (cases hT; cases ht; rfl) | simp at hT
  ctor := by
    rintro (_ | _ | j) T hT t ht C hC <;> simp only [nfnAux, nfnResultBadHead, nfnResult] at hT ht ⊢ <;>
      first
        | (cases hT; cases ht; simp only [List.mem_cons, List.not_mem_nil, or_false] at hC;
           subst hC; exact ⟨_, List.mem_cons_self, rfl⟩)
        | simp at hT
  companions := by
    rintro (_ | _ | j) T hT <;> simp only [nfnAux] at hT <;> [skip; skip; simp at hT] <;>
      cases hT <;> simp [nfnK]
  auxName := by
    rintro (_ | _ | j) t ht hle
    · exact absurd hle (by simp)
    · simp only [nfnResultBadHead, nfnResult] at ht; cases ht; decide
    · simp [nfnResultBadHead, nfnResult] at ht
  auxCtorName := by
    rintro (_ | _ | j) t ht hle c hc
    · exact absurd hle (by simp)
    · simp only [nfnResultBadHead, nfnResult] at ht; cases ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc; decide
    · simp [nfnResultBadHead, nfnResult] at ht
  auxCtorPrefix := by
    rintro (_ | _ | j) t ht hle c hc
    · exact absurd hle (by simp)
    · simp only [nfnResultBadHead, nfnResult] at ht; cases ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc; decide
    · simp [nfnResultBadHead, nfnResult] at ht
  auxNodup := by decide
  ownName := by
    rintro (_ | _ | j) t ht hlt
    · simp only [nfnResultBadHead, nfnResult] at ht; cases ht; decide
    · exact absurd hlt (by simp)
    · exact absurd hlt (by simp)
  ownCtor := by
    rintro (_ | _ | j) t ht hlt c hc
    · simp only [nfnResultBadHead, nfnResult] at ht; cases ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc; decide
    · exact absurd hlt (by simp)
    · exact absurd hlt (by simp)
  head := by
    rintro (_ | _ | j) t ht hle
    · exact absurd hle (by simp)
    · simp only [nfnResultBadHead, nfnResult] at ht; cases ht; decide
    · simp [nfnResultBadHead, nfnResult] at ht
  headNe := by
    rintro (_ | _ | j) t ht hle
    · exact absurd hle (by simp)
    · simp only [nfnResultBadHead, nfnResult] at ht; cases ht; decide
    · simp [nfnResultBadHead, nfnResult] at ht
  auxRec := nfn_auxRec
  args := by
    intro j a ha
    simp only [nfnAs] at ha
    split at ha
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha; subst ha; decide
    · simp at ha


/-- …and the derived restoration presents the companion as `NFn`. -/
example : (nfnResultBadHead.mkRestore [nfnIndType] nfnAux.uvars nfnAux.np nfnLs nfnAs).tyName 1
    = ``NFn := rfl

/-- **The four name-discipline obligations still hold** at the perturbed data. -/
theorem nfnResultBadHead_discipline :
    (nfnResultBadHead.mkRestore [nfnIndType] nfnAux.uvars nfnAux.np nfnLs nfnAs).OwnId
        nfnAux nfnK ∧
      (nfnResultBadHead.mkRestore [nfnIndType] nfnAux.uvars nfnAux.np nfnLs nfnAs).NestedBarrier
        nfnAux nfnK :=
  ⟨nfnResultBadHead_restoreData.mkRestore_ownId (ls := nfnLs),
    nfnResultBadHead_restoreData.mkRestore_nestedBarrier (ls := nfnLs)⟩

/-! ## 3. `mkRestore` against the hand-written `nfnRestore`, both ways -/

/-- The restoration the checker's data determines, at this block. -/
def nfnRestore' : VIndRestore :=
  nfnResult.mkRestore [nfnIndType] nfnAux.uvars nfnAux.np nfnLs nfnAs

/-! The two agree on the block and disagree off it — the `tyName` field, at three indices. -/
example : nfnRestore'.tyName 0 = ``NFn := rfl
example : nfnRestore'.tyName 1 = ``PFn := rfl
example : nfnRestore'.tyName 2 = .anonymous := rfl
example : nfnRestore.tyName 2 = ``NFn := rfl

theorem nfnRestore'_ctorName : nfnRestore'.ctorName = nfnRestore.ctorName := by
  funext c
  show ((nfnResult.ctorRenames 1).lookup c).getD c = _
  rw [show nfnResult.ctorRenames 1 = [(`_nested.PFn_1.mk, ``PFn.mk)] from rfl]
  rw [List.lookup_cons]
  cases hc : c == `_nested.PFn_1.mk with
  | true => have : c = `_nested.PFn_1.mk := by simpa using hc
            subst this; rfl
  | false => have : ¬ c = `_nested.PFn_1.mk := by simpa using hc
             simp [nfnRestore, this]

theorem nfnRestore'_recName : nfnRestore'.recName = nfnRestore.recName := by
  funext n
  show ((nfnResult.recRenames [nfnIndType]).lookup n).getD n = _
  rw [show nfnResult.recRenames [nfnIndType] = [(`_nested.PFn_1.rec, ``NFn.rec_1)] from rfl]
  rw [List.lookup_cons]
  cases hc : n == `_nested.PFn_1.rec with
  | true => have : n = `_nested.PFn_1.rec := by simpa using hc
            subst this; rfl
  | false => have : ¬ n = `_nested.PFn_1.rec := by simpa using hc
             simp [nfnRestore, this]

theorem nfnRestore'_tyLvls : nfnRestore'.tyLvls = nfnRestore.tyLvls := by
  funext j; show (if j < 1 then VLevel.params 0 else nfnLs j) = _
  split <;> rfl

theorem nfnRestore'_tyArgs : nfnRestore'.tyArgs = nfnRestore.tyArgs := by
  funext j
  show (if j < 1 then VExpr.bvars 0 0 else nfnAs j) = _
  match j with
  | 0 => rfl
  | 1 => rfl
  | (j+2) => simp only [nfnAs, nfnRestore]; rfl

/-- `mkRestore` agrees with the hand-written `nfnRestore` at every member of the block. -/
theorem nfnRestore'_tyName_agree : ∀ j < nfnAux.types.length,
    nfnRestore'.tyName j = nfnRestore.tyName j := by
  rintro (_ | _ | j) h
  · rfl
  · rfl
  · simp only [nfnAux, List.length_cons, List.length_nil] at h; omega

/-- …and is **not** equal to it: outside the block the two disagree. -/
theorem nfnRestore'_ne_nfnRestore : nfnRestore' ≠ nfnRestore := by
  intro h
  have : nfnRestore'.tyName 2 = nfnRestore.tyName 2 := by rw [h]
  exact absurd this (by decide)


/-! ## 4. The four name-discipline obligations, at real data -/

/-- **All four, at the checker's own data**, by instantiating
`RestoreData.mkRestore_discipline`.  `nfnRestore_nestedBarrier`
(`Verify/Inductive/NestedRestore.lean` §7.1) proves the barrier at the *hand-written*
restoration by seven `decide`s; this derives it at the *computed* one from the fourteen-field
bundle, so the two routes cross-check. -/
theorem nfnResult_discipline :
    nfnRestore'.OwnId nfnAux nfnK ∧ nfnRestore'.NestedBarrier nfnAux nfnK ∧
      nfnRestore'.SubstFree nfnAux (nfnRestore'.csubst nfnAux nfnK) ∧
      nfnRestore'.KeysFree nfnAux nfnK :=
  nfnResult_restoreData.mkRestore_discipline (ls := nfnLs)

/-! ### What the step declares is the same at both restorations

`VIndCtor.typeR`, `recTypeR`, and hence all three declared constant lists and the ι-rules, are
**equal** — by `rfl`, at the concrete block.  So §5 and §6 are not weaker statements about a
different block: they are the same declarations, from computed rather than asserted data. -/

theorem nfnNode_typeR_eq :
    nfnNode.typeR nfnAux nfnRestore' 0 = nfnNode.typeR nfnAux nfnRestore 0 := rfl

theorem nfnAux_recTypeR_eq0 :
    nfnAux.recTypeR nfnRestore' 0 = nfnAux.recTypeR nfnRestore 0 := rfl

theorem nfnAux_recTypeR_eq1 :
    nfnAux.recTypeR nfnRestore' 1 = nfnAux.recTypeR nfnRestore 1 := rfl

/-! The three lists `AddInductStagesR` folds over, and the rules `addIndRulesR` emits. -/
example : nfnAux.ctorConstsCR nfnRestore' nfnK = nfnAux.ctorConstsCR nfnRestore nfnK := rfl
example : nfnAux.recConstsR nfnRestore' nfnK = nfnAux.recConstsR nfnRestore nfnK := rfl
example : nfnAux.iotaRulesRS nfnRestore' nfnK = nfnAux.iotaRulesRS nfnRestore nfnK := rfl


/-! ## 5. The nested translation relation, at `mkRestore` -/

section
variable {env : VEnv}
  (hPFn : env.constants ``PFn = some ⟨0, pfnType.type⟩)

include hPFn in
/-- **The nested translation relation holds at the restoration the *checker's data*
determines**, in place of the hand-written `nfnRestore`. -/
theorem trIndDeclN_wit' :
    TrIndDeclN env [] 0 [nfnIndType] false 1 nfnAux nfnK nfnRestore' where
  safe := rfl
  uvars := rfl
  np := rfl
  length := rfl
  companions := by
    rintro (_ | _ | j) T hT <;> simp only [nfnAux] at hT <;> [skip; skip; simp at hT] <;>
      cases hT <;> simp [nfnK]
  trType := by
    rintro (_ | j) t T ht hT
    · cases ht; cases hT; exact ⟨rfl, .sort rfl⟩
    · simp at ht
  trCtorsLen := by
    rintro (_ | j) t T ht hT
    · cases ht; cases hT; rfl
    · simp at ht
  trCtors := by
    rintro env₁ hst (_ | j) t T ht hT (_ | q) c C hc hC
    · cases ht; cases hT; cases hc; cases hC
      have hle : env ≤ env₁ := VEnv.addConstList_le hst
      refine ⟨rfl, ?_⟩
      rw [nfnNode_typeR_eq]
      refine tr_nodeType (hle.constants hPFn) ?_
      exact VEnv.addConstList_constants hst (``NFn, ⟨0, .sort (.succ .zero)⟩)
        (by exact List.Mem.head _)
    · cases ht; cases hT; simp [nfnIndType] at hc
    · simp at ht
    · simp at ht
  recName_own := by
    rintro (_ | j) t T ht hT
    · cases ht; cases hT; rfl
    · simp at ht
  recName_aux := by
    rintro (_ | _ | j) T hT hle
    · simp at hle
    · cases hT; rfl
    · simp [nfnAux] at hT

end


end NestedWit

/-! ## 6. The general bridge: `Built` from `RestoreData` plus a named residue

§6 is concrete.  This is the general form, and it is what makes the shape of the remaining work
visible: of `VInductDecl'.Built`'s eight clauses, **four are discharged by `RestoreData`** — the
three presentation clauses (given the occurrence's own levels and spine as `mkRestore`'s two
semantic parameters, which is a *choice*, not a hypothesis) and `own` — and the other four are
collected as `OccResidue`.

`OccResidue`'s four clauses are where the translation relation genuinely enters: `member` is the
`TrExprS`-level agreement between `restoreNested`'s output and `VIndCtor.typeR`, `occurs` is the
environment's own copy of the nested block, `ctorName_inv` is a `Name.replacePrefix` round trip
whose *lookup* half needs the auxiliary constructor names to be distinct, and `head` says the
head of the `Expr` `aux2nested` stores is the member the occurrence is at.

With that residue, `VIndRestore.Faithful` and `VInductDecl'.Canonical` are **theorems** about a
`mkRestore`-derived restoration, not hypotheses — via `Built.toFaithful` and `Built.canonical`
(`Theory/Inductive/NestedBuild.lean`).  §7's `nfnResult_occResidue` is a model of `OccResidue`,
so none of this is vacuous. -/

namespace ElimNestedInductive.Result

/-- **The residue of `Built` a `Result` does not determine.**  Everything else in `Built` follows
from `RestoreData` (`RestoreData.mkRestore_built`). -/
structure OccResidue (r : Result) (types : List Lean.InductiveType) (D : VInductDecl')
    (K : List Lean.Name) (env : VEnv) (R : VIndRestore) (occ : Nat → VNestedOcc) : Prop where
  /-- The companion member **is** the value the construction computes. -/
  member : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K →
    T = (occ j).member D.header R
  /-- The environment holds the nested block the occurrence is at. -/
  occurs : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K → (occ j).Occurs env
  /-- `restoreCtorName` inverts the auxiliary constructor naming. -/
  ctorName_inv : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K →
    ∀ C ∈ (occ j).src.ctors, R.ctorName ((occ j).ctorName C.name) = C.name
  /-- The head of the `Expr` `aux2nested` stores at this member is the member's presented name.
  This is the one clause that is *about* `r`; the other three are about `occ` and `R`. -/
  head : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K →
    ∀ t, r.types[j]? = some t → r.presentedHead t.name = (occ j).tyName

namespace RestoreData
variable {r : Result} {types : List Lean.InductiveType} {D : VInductDecl'} {K : List Lean.Name}
  {ls : Nat → List VLevel} {as : Nat → List VExpr} {env : VEnv} {occ : Nat → VNestedOcc}
  (h : r.RestoreData types D K as)

include h

/-- **`VInductDecl'.Built` for the construction.**  The two semantic parameters of `mkRestore`
are taken at the occurrence's own values — which is a choice available to any caller, since they
are parameters — and the rest of the presentation is computed. -/
theorem mkRestore_built
    (hl : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K → ls j = (occ j).lvls)
    (ha : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K → as j = (occ j).args)
    (hres : r.OccResidue types D K env (r.mkRestore types D.uvars D.np ls as) occ) :
    D.Built (r.mkRestore types D.uvars D.np ls as) K env occ where
  member := hres.member
  occurs := hres.occurs
  ctorName_inv := hres.ctorName_inv
  own := h.mkRestore_ownId
  tyName := by
    intro j T hT hK
    obtain ⟨t, ht, -, hle⟩ := h.on hT hK
    show (match r.types[j]? with
      | none => Lean.Name.anonymous
      | some T => if j < types.length then T.name else r.presentedHead T.name) = _
    rw [ht]
    show (if j < types.length then t.name else r.presentedHead t.name) = _
    rw [if_neg (by omega)]
    exact hres.head j T hT hK t ht
  tyLvls := by
    intro j T hT hK
    obtain ⟨-, -, -, hle⟩ := h.on hT hK
    show (if j < types.length then _ else ls j) = _
    rw [if_neg (by omega)]
    exact hl j T hT hK
  tyArgs := by
    intro j T hT hK
    obtain ⟨-, -, -, hle⟩ := h.on hT hK
    show (if j < types.length then _ else as j) = _
    rw [if_neg (by omega)]
    exact ha j T hT hK

/-- **`VIndRestore.Faithful` for the construction** — a theorem, not a hypothesis.  Its `npJ` is
the parameter count of the block the *environment* holds, which is what
`Faithful.ctors_complete` pins. -/
theorem mkRestore_faithful
    (hl : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K → ls j = (occ j).lvls)
    (ha : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K → as j = (occ j).args)
    (hres : r.OccResidue types D K env (r.mkRestore types D.uvars D.np ls as) occ) :
    (r.mkRestore types D.uvars D.np ls as).Faithful D env K (fun j => (occ j).decl.np) :=
  (h.mkRestore_built hl ha hres).toFaithful

/-- **`VInductDecl'.Canonical` for the construction**, from canonicity on the members the *user*
wrote: a built companion member is canonical by construction
(`VNestedOcc.member_Canonical`). -/
theorem mkRestore_canonical (hown : D.CanonicalOwn K)
    (hl : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K → ls j = (occ j).lvls)
    (ha : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K → as j = (occ j).args)
    (hres : r.OccResidue types D K env (r.mkRestore types D.uvars D.np ls as) occ) :
    D.Canonical :=
  (h.mkRestore_built hl ha hres).canonical hown

/-- **The whole nested step, from the checker's data plus the residue.** -/
theorem mkRestore_AddNested {env' : VEnv} (hwf : D.WF env) (hown : D.CanonicalOwn K)
    (hl : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K → ls j = (occ j).lvls)
    (ha : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K → as j = (occ j).args)
    (hres : r.OccResidue types D K env (r.mkRestore types D.uvars D.np ls as) occ)
    (hadd : env.addInductR D K (r.mkRestore types D.uvars D.np ls as) = some env') :
    VEnv.AddNested env D K (r.mkRestore types D.uvars D.np ls as)
      (fun j => (occ j).decl.np) env' :=
  VEnv.AddNestedB.toAddNested ⟨hwf, hown, h.mkRestore_built hl ha hres, hadd⟩

/-- …and the packaged premise of `VDecl.WF.inductNested`. -/
theorem mkRestore_AddNestedStep {env' : VEnv} (hwf : D.WF env) (hown : D.CanonicalOwn K)
    (hl : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K → ls j = (occ j).lvls)
    (ha : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K → as j = (occ j).args)
    (hres : r.OccResidue types D K env (r.mkRestore types D.uvars D.np ls as) occ)
    (hadd : env.addInductR D K (r.mkRestore types D.uvars D.np ls as) = some env') :
    VEnv.AddNestedStep env D K (r.mkRestore types D.uvars D.np ls as) env' :=
  ⟨_, h.mkRestore_AddNested hwf hown hl ha hres hadd⟩

end RestoreData
end ElimNestedInductive.Result

namespace NestedWit
open InductiveDeclExamples ElimNestedInductive

/-! ## 7. `Built`, `Faithful`, and the whole nested step, at `mkRestore`

`env₂` is the environment after `PFn`'s own declaration step — the same one
`Theory/Inductive/NestedBuild.lean` Part 9 uses. -/

section
variable {env₂ : VEnv} (h : VEnv.empty.addInduct' pfnDecl = some env₂)

include h in
/-- **`OccResidue` is satisfiable.**  The four clauses `RestoreData` cannot reach, at this
block: `member` and `ctorName_inv` are `rfl`, `occurs` is `pfnOcc_occurs` unchanged, and `head`
reads the stored `PFn NFn` off `aux2nested`. -/
theorem nfnResult_occResidue :
    nfnResult.OccResidue [nfnIndType] nfnAux nfnK env₂ nfnRestore' (fun _ => pfnOcc) where
  member := by
    rintro (_ | _ | j) T hT hK
    · cases hT; exact absurd hK (by decide)
    · cases hT; rfl
    · simp [nfnAux] at hT
  occurs := fun _ _ _ _ => pfnOcc_occurs h
  ctorName_inv := by
    rintro (_ | _ | j) T hT hK C hC
    · cases hT; exact absurd hK (by decide)
    · simp only [show pfnOcc.src.ctors = [pfnMk] from rfl, List.mem_cons,
        List.not_mem_nil, or_false] at hC
      subst hC; rfl
    · simp [nfnAux] at hT
  head := by
    rintro (_ | _ | j) T hT hK t ht
    · cases hT; exact absurd hK (by decide)
    · simp only [nfnResult] at ht; cases ht; rfl
    · simp [nfnAux] at hT

/-- **The other half of §2.1's bound**: at the perturbed `Result`, whose `RestoreData` and whose
four name-discipline obligations hold, `OccResidue.head` is **false** — so the residue is not
derivable from the bundle. -/
theorem nfnResultBadHead_not_occResidue :
    ¬ nfnResultBadHead.OccResidue [nfnIndType] nfnAux nfnK env₂
        (nfnResultBadHead.mkRestore [nfnIndType] nfnAux.uvars nfnAux.np nfnLs nfnAs)
        (fun _ => pfnOcc) := by
  intro hres
  exact absurd (hres.head 1 _ rfl (by decide) _ rfl) (by decide)

/-- …and so is `Built`, at its `tyName` clause: the companion is presented as `NFn`. -/
theorem nfnResultBadHead_not_built :
    ¬ nfnAux.Built (nfnResultBadHead.mkRestore [nfnIndType] nfnAux.uvars nfnAux.np nfnLs nfnAs)
        nfnK env₂ (fun _ => pfnOcc) := by
  intro hb
  exact absurd (hb.tyName 1 _ rfl (by decide)) (by decide)

include h in
/-- **`VInductDecl'.Built` at the computed restoration**, through the general bridge: the three
presentation clauses and `own` come from `RestoreData`, the other four from `OccResidue`. -/
theorem nfnAux_built' : nfnAux.Built nfnRestore' nfnK env₂ (fun _ => pfnOcc) :=
  nfnResult_restoreData.mkRestore_built (ls := nfnLs) (occ := fun _ => pfnOcc)
    (fun _ _ _ _ => rfl)
    (by rintro (_ | _ | j) T hT hK
        · cases hT; exact absurd hK (by decide)
        · rfl
        · simp [nfnAux] at hT)
    (nfnResult_occResidue h)

include h in
theorem nfnAux_admitted' : ∃ env₃, env₂.addInductR nfnAux nfnK nfnRestore' = some env₃ := by
  refine VEnv.addInductR_eq_some_iff.2 ⟨?_, ?_⟩ <;>
    rw [show nfnAux.allNamesCR nfnRestore' nfnK
      = [``NFn, ``NFn.node, ``NFn.rec, ``NFn.rec_1] from rfl]
  · intro n hn; exact nfn_fresh h n hn
  · decide

include h in
/-- **`VEnv.AddNestedB` at the restoration the checker's own data determines.** -/
theorem nfnAux_AddNestedB' :
    ∃ env₃, VEnv.AddNestedB env₂ nfnAux nfnK nfnRestore' (fun _ => pfnOcc) env₃ :=
  ⟨(nfnAux_admitted' h).choose, nfnAux_WF, nfnAux_canonicalOwn, nfnAux_built' h,
    (nfnAux_admitted' h).choose_spec⟩

include h in
/-- **`VIndRestore.Faithful` at `mkRestore`** — derived, not assumed. -/
theorem nfnRestore'_faithful : nfnRestore'.Faithful nfnAux env₂ nfnK (fun _ => 1) :=
  (nfnAux_built' h).toFaithful

include h in
/-- **The full nested step at checker-derived data.** -/
theorem nfnAux_AddNested' :
    ∃ env₃, VEnv.AddNested env₂ nfnAux nfnK nfnRestore' (fun _ => 1) env₃ :=
  let ⟨env₃, hb⟩ := nfnAux_AddNestedB' h
  ⟨env₃, hb.toAddNested⟩

include h in
/-- …and the packaged premise of `VDecl.WF.inductNested` (`Theory/Typing/Env.lean`). -/
theorem nfnAux_AddNestedStep' :
    ∃ env₃, VEnv.AddNestedStep env₂ nfnAux nfnK nfnRestore' env₃ :=
  let ⟨env₃, hb⟩ := nfnAux_AddNestedB' h
  ⟨env₃, hb.toAddNestedStep⟩

end


/-! ## 8. The constant-map step, at `mkRestore`

`Verify/Environment/InductR.lean` §6's `addInductStagesR_wit` / `inductStepNested_wit` with
`nfnRestore` replaced by `nfnRestore'` throughout.  The two shape predicates have to be re-proved
because `CtorShapeOf` takes `R.tyName` as an argument and the two restorations are not equal as
functions (§3); everything else — the three constant lists and the ι-rules — is the *same* data
(§4's `rfl`s), so the proof is the original one. -/

theorem indShapeOf_nfnInd' : IndShapeOf nfnAux nfnRestore'.ctorName (.inductInfo nfnInd) := by
  rw [nfnRestore'_ctorName]; exact indShapeOf_nfnInd

theorem ctorShapeOf_nfnNodeCI' :
    CtorShapeOf nfnAux nfnRestore'.ctorName nfnRestore'.tyName (.ctorInfo nfnNodeCI) := by
  have hcs : nfnAux.ctorsAll = [(0, nfnNode), (1, pfnAuxMk)] := rfl
  refine ⟨nfnNodeCI, rfl, ⟨(0, nfnNode), by rw [hcs]; exact List.mem_cons_self, by decide⟩,
    fun jC hjC hn => ?_⟩
  rw [hcs] at hjC
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hjC
  rcases hjC with rfl | rfl
  · exact ⟨nfnNodeCI, rfl, by decide, by decide, rfl, rfl⟩
  · exact absurd hn (by decide)

section
variable {env : VEnv}
  (hPFn : env.constants ``PFn = some ⟨0, pfnType.type⟩)
  (hPFnMk : env.constants ``PFn.mk = some ⟨0, pfnMk.type pfnDecl 0⟩)
  (hfresh : ∀ n ∈ [``NFn, ``NFn.node, ``NFn.rec, ``NFn.rec_1], env.constants n = none)
  (hfreshAux : env.constants `_nested.PFn_1 = none)

include hPFn hPFnMk hfresh in
/-- **`AddInductStagesR` fires at a nested block, and it declares the renamed auxiliary
recursor.**  Four stages' worth of constants land in the map — `NFn`, `NFn.node`, `NFn.rec`
and `NFn.rec_1` — and the companion member `_nested.PFn_1` and its constructor land nowhere,
which is what `typeConstsC`/`ctorConstsCR` filter out.

`NFn.rec_1` is the constant that refutes `AddInductStages` (`AddDeclWF.lean` §2). -/
theorem addInductStagesR_wit' {m : ConstMap} (hwf : m.WF) (hfr : ∀ n, m.find? n = none) :
    ∃ m' env', AddInductStagesR m env nfnAux nfnK nfnRestore' m' env' ∧
      m'.find? ``NFn.rec_1 = some (.recInfo nfnRec1CI) ∧
      m'.find? ``NFn.rec = some (.recInfo nfnRecCI) ∧
      m'.find? `_nested.PFn_1 = none ∧
      (∃ ci, env'.constants ``NFn.rec_1 = some ci) := by
  have f0 := hfresh ``NFn (by simp)
  obtain ⟨e1, he1⟩ := VEnv.addConst_eq_none (env := env) (name := ``NFn)
    (ci := ⟨0, .sort (.succ .zero)⟩) f0
  have c1 := VEnv.addConst_constants_eq he1
  have hNFn1 : e1.constants ``NFn = some ⟨0, .sort (.succ .zero)⟩ := by rw [c1]; simp
  have hPFn1 : e1.constants ``PFn = some ⟨0, pfnType.type⟩ := by rw [c1]; simp [hPFn]
  have hPFnMk1 : e1.constants ``PFn.mk = some ⟨0, pfnMk.type pfnDecl 0⟩ := by
    rw [c1]; simp [hPFnMk]
  obtain ⟨e2, he2⟩ := VEnv.addConst_eq_none (env := e1) (name := ``NFn.node)
    (ci := ⟨0, nfnNode.typeR nfnAux nfnRestore' 0⟩) (by rw [c1]; simp [hfresh ``NFn.node])
  have c2 := VEnv.addConst_constants_eq he2
  have hNFn2 : e2.constants ``NFn = some ⟨0, .sort (.succ .zero)⟩ := by rw [c2]; simp [hNFn1]
  have hPFn2 : e2.constants ``PFn = some ⟨0, pfnType.type⟩ := by rw [c2]; simp [hPFn1]
  have hPFnMk2 : e2.constants ``PFn.mk = some ⟨0, pfnMk.type pfnDecl 0⟩ := by
    rw [c2]; simp [hPFnMk1]
  have hNode2 : e2.constants ``NFn.node = some ⟨0, nfnNode.typeR nfnAux nfnRestore' 0⟩ := by
    rw [c2]; simp
  obtain ⟨e3, he3⟩ := VEnv.addConst_eq_none (env := e2) (name := ``NFn.rec)
    (ci := ⟨1, nfnAux.recTypeR nfnRestore' 0⟩)
    (by rw [c2, c1]; simp [hfresh ``NFn.rec])
  have c3 := VEnv.addConst_constants_eq he3
  have hNFn3 : e3.constants ``NFn = some ⟨0, .sort (.succ .zero)⟩ := by rw [c3]; simp [hNFn2]
  have hPFn3 : e3.constants ``PFn = some ⟨0, pfnType.type⟩ := by rw [c3]; simp [hPFn2]
  have hPFnMk3 : e3.constants ``PFn.mk = some ⟨0, pfnMk.type pfnDecl 0⟩ := by
    rw [c3]; simp [hPFnMk2]
  have hNode3 : e3.constants ``NFn.node = some ⟨0, nfnNode.typeR nfnAux nfnRestore' 0⟩ := by
    rw [c3]; simp [hNode2]
  obtain ⟨e4, he4⟩ := VEnv.addConst_eq_none (env := e3) (name := ``NFn.rec_1)
    (ci := ⟨1, nfnAux.recTypeR nfnRestore' 1⟩)
    (by rw [c3, c2, c1]; simp [hfresh ``NFn.rec_1])
  -- the map side
  have w1 := hwf.insert ``NFn (.inductInfo nfnInd) (hfr _)
  have f2 : (m.insert ``NFn (.inductInfo nfnInd)).find? ``NFn.node = none := by
    rw [hwf.find?_insert]; simp [hfr]
  have w2 := w1.insert ``NFn.node (.ctorInfo nfnNodeCI) f2
  have f3 : ((m.insert ``NFn (.inductInfo nfnInd)).insert ``NFn.node
      (.ctorInfo nfnNodeCI)).find? ``NFn.rec = none := by
    rw [w1.find?_insert, hwf.find?_insert]; simp [hfr]
  have w3 := w2.insert ``NFn.rec (.recInfo nfnRecCI) f3
  have f4 : (((m.insert ``NFn (.inductInfo nfnInd)).insert ``NFn.node
      (.ctorInfo nfnNodeCI)).insert ``NFn.rec (.recInfo nfnRecCI)).find? ``NFn.rec_1 = none := by
    rw [w2.find?_insert, w1.find?_insert, hwf.find?_insert]; simp [hfr]
  have w4 := w3.insert ``NFn.rec_1 (.recInfo nfnRec1CI) f4
  have s1 : AddIndConsts (IndShapeOf nfnAux nfnRestore'.ctorName) (nfnAux.typeConstsC nfnK)
      m env (m.insert ``NFn (.inductInfo nfnInd)) e1 :=
    .cons (ci := .inductInfo nfnInd) rfl indShapeOf_nfnInd' ⟨by decide, rfl, .sort rfl⟩
      (hfr _) he1 .nil
  have s2 : AddIndConsts (CtorShapeOf nfnAux nfnRestore'.ctorName nfnRestore'.tyName)
      (nfnAux.ctorConstsCR nfnRestore' nfnK)
      (m.insert ``NFn (.inductInfo nfnInd)) e1
      ((m.insert ``NFn (.inductInfo nfnInd)).insert ``NFn.node (.ctorInfo nfnNodeCI)) e2 :=
    .cons (ci := .ctorInfo nfnNodeCI) rfl ctorShapeOf_nfnNodeCI'
      ⟨by decide, rfl, tr_nodeType hPFn1 hNFn1⟩ f2 he2 .nil
  have s3 : AddIndConsts (fun ci => ∃ v, ci = .recInfo v) (nfnAux.recConstsR nfnRestore' nfnK)
      ((m.insert ``NFn (.inductInfo nfnInd)).insert ``NFn.node (.ctorInfo nfnNodeCI)) e2
      ((((m.insert ``NFn (.inductInfo nfnInd)).insert ``NFn.node (.ctorInfo nfnNodeCI)).insert
        ``NFn.rec (.recInfo nfnRecCI)).insert ``NFn.rec_1 (.recInfo nfnRec1CI)) e4 :=
    .cons (ci := .recInfo nfnRecCI) rfl ⟨_, rfl⟩
      ⟨by decide, rfl, tr_recType0 hPFn2 hPFnMk2 hNFn2 hNode2⟩ f3 he3 <|
    .cons (ci := .recInfo nfnRec1CI) rfl ⟨_, rfl⟩
      ⟨by decide, rfl, tr_recType1 hPFn3 hPFnMk3 hNFn3 hNode3⟩ f4 he4 .nil
  refine ⟨_, _, ⟨_, _, _, _, e4, s1, s2, s3, rfl⟩, ?_, ?_, ?_, ?_⟩
  · rw [w3.find?_insert]; simp
  · rw [w3.find?_insert, w2.find?_insert]; simp
  · rw [w3.find?_insert, w2.find?_insert, w1.find?_insert, hwf.find?_insert]; simp [hfr]
  · exact ⟨_, by rw [VEnv.addIndRulesR, VEnv.addDefEqList_constants]
                 exact VEnv.addConst_self he4⟩

include hPFn hPFnMk hfresh hfreshAux in
/-- **`InductStepNested` has a model, at a nested block.**  All three conjuncts at once:
the syntactic translation (`trIndDeclN_wit`), the declaration's well-formedness
(`NestedBuild.lean`'s `nfnAux_WF`, whose `binders_indep` clause is discharged by the
substitution theorem rather than by emptiness), and the constant-map step
(`addInductStagesR_wit'`), which declares `NFn.rec_1`.

This is the joint non-vacuity the companion refutation demands: the two premises of a
flipped `TrEnv'.induct` do not excuse each other here, because `AddInductStagesR` itself
supplies the `addIndTypesC` success that `WF`'s constructor clause is staged over. -/
theorem inductStepNested_wit' {m : ConstMap} (hwf : m.WF) (hfr : ∀ n, m.find? n = none) :
    ∃ m' env', InductStepNested m m' env env' [] 0 [nfnIndType] 1 ∧
      m'.find? ``NFn.rec_1 = some (.recInfo nfnRec1CI) := by
  obtain ⟨m', env', H, hrec1, -, -, -⟩ := addInductStagesR_wit' hPFn hPFnMk hfresh hwf hfr
  refine ⟨m', env', ⟨nfnAux, nfnK, nfnRestore', trIndDeclN_wit' hPFn, ?_, nfnAux_WF, H⟩,
    hrec1⟩
  refine VEnv.addConstList_eq_some_iff.2 ⟨?_, ?_⟩
  · rintro n hn
    simp only [nfnAux, VInductDecl'.typeConsts, List.map_cons, List.map_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hn
    obtain rfl | rfl := hn
    exacts [hfresh _ (by simp), hfreshAux]
  · decide

end
/-! ## 9. What is left

* **`RestoreData` at the *monadic* output of `run`.**  This file instantiates it at a `Result`
  *literal*, and checks that literal against `run` by execution (§1.1) rather than by proof.
  The proof needs a `run`-level invariant calculus; `Verify/Inductive/AddInductiveStep.lean`'s
  `EWF` is the right vehicle, but its postcondition is fixed at `nestedAux = #[]`, which is the
  degenerate branch (`run_EWF` forces `numNested = 0` under `ves.WF env`), so the calculus
  transfers and its theorems do not.
* **`ownName`/`ownCtor` stay hypotheses**, for the reason `NestedRestore.lean` §8.2 measures:
  neither kernel checks that a declaration's own names avoid the `_nested` prefix.  They are
  discharged here by `decide` because `NFn`/`NFn.node` are concrete.
* **`OccResidue`'s four clauses, in general.**  §6 reduces the nested step to them and §7
  discharges them at one block, by `rfl` and by `pfnOcc_occurs`.  In general:
  - `member` is the `TrExprS`-level agreement between `restoreNested`'s output and
    `VIndCtor.typeR`.  This is the clause the handoff described as the content of `Faithful`;
    `Built.toFaithful` shows it is the *only* such clause, and that `ty_agree`, `ctor_agree`
    and `ctors_complete` follow from it plus `occurs`.
  - `occurs` needs `VInductDecl'.Declared env` for the nested block, which a declaration
    history supplies (`VEnv.WF'.declared`) and which `Faithful.ctors_complete` also needs.
  - `ctorName_inv` is a `Name.replacePrefix` round trip; its *lookup* half additionally needs
    the auxiliary constructor names to be pairwise distinct, which `RestoreData.auxNodup` gives
    only for the member *names*.  A `ctorRenames`-level `Nodup` field is the natural
    strengthening, and it is a name fact — reachable from this file's §3 machinery.
  - `head` is `presentedHead` against the environment: `aux2nested`'s stored `Expr` is
    `replaceParams params (mkAppRange (.const J I_lvls) 0 I_nparams args) As`, whose head is
    `J` on the nose, so this is `Expr.getAppFn` of a `mkAppRange` — an `Expr` lemma, not a
    typing one.
* **A conjunct for `InductStepNested`, now satisfiable — and not added here.**
  `InductStepNested` (`Verify/Environment/InductR.lean` §4) existentially quantifies `D`, `K`,
  `R` with `D.WF venv` and **no** `Faithful`/`OwnId`/`Canonical` conjunct, so nothing in it
  excludes a restoration of the shape `pfnJunkRestore` — the one that makes obligation (A) of
  `VEnv.addInductR_ordered'` *false* (`Theory/Inductive/NestedBuild.lean`).  §7 and §8 now meet at one block, so a conjunct
  `VEnv.AddNestedStep venv D K R venv'` — or just `R.OwnId D K` — would have a model rather than
  an unsatisfiable precondition.  Adding it changes a definition the `addDecl.WF` chain consumes,
  so it is reported, not done.
* **`Canonical` was never the hard half.**  `Built.canonical` reduces it to
  `VInductDecl'.CanonicalOwn K`, canonicity on the members the *user* wrote, because a built
  companion member is canonical by construction (`VNestedOcc.member_Canonical`).  What is owed
  for `CanonicalOwn` is that `AddInductive.run`'s recogniser stores a recursive field in its
  canonical form — the same obligation `AddInductiveRunRealises`
  (`Verify/Inductive/AddInductiveStep.lean` §6) already carries as its `D.Canonical` conjunct,
  for the non-nested path.
-/

end NestedWit
end Lean4Lean
