import Lean4Lean.Std.SMap
import Lean4Lean.Verify.LocalContext
import Lean4Lean.Theory.Typing.EnvLemmas

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

theorem ConstantInfo.hasValue_eq (ci : ConstantInfo) : ci.hasValue = ci.value?.isSome := by
  cases ci <;> rfl

theorem ConstantInfo.value!_eq (ci : ConstantInfo) : ci.value! = ci.value?.get! := by
  cases ci <;> simp [ConstantInfo.value?, ConstantInfo.value!]

def _root_.Lean.ConstantInfo.safety (ci : ConstantInfo) : DefinitionSafety :=
  if ci.isUnsafe then .unsafe else if ci.isPartial then .partial else .safe

variable (safety : DefinitionSafety) (env : VEnv) in
def TrConstant (ci : ConstantInfo) (ci' : VConstant) : Prop :=
  safety ≤ ci.safety ∧ ci.levelParams.length = ci'.uvars ∧
  TrExprS env ci.levelParams [] ci.type ci'.type

variable (safety : DefinitionSafety) (env : VEnv) in
def TrConstVal (ci : ConstantInfo) (ci' : VConstVal) : Prop :=
  TrConstant safety env ci ci'.toVConstant ∧ ci.name = ci'.name

variable (safety : DefinitionSafety) (env : VEnv) in
def TrDefVal (ci : ConstantInfo) (ci' : VDefVal) : Prop :=
  TrConstVal safety env ci ci'.toVConstVal ∧
  TrExprS env ci.levelParams [] (ci.value! (allowOpaque := true)) ci'.value

/-- The step an abstract environment takes when `ci`, modelled by `ci'`, is added.

At safety levels where the declaration is visible the constant is added; where it is not, the
environment is unchanged, matching `TrEnv'.ignore`. Stating this rather than just `venv ≤ venv'`
is what lets a caller see *which* constant a step added. -/
def VEnv.AddConst (venv : VEnv) (safety : DefinitionSafety) (ci : ConstantInfo)
    (ci' : VConstant) (venv' : VEnv) : Prop :=
  if safety ≤ ci.safety then
    TrConstant safety venv ci ci' ∧ ci'.WF venv ∧ venv.addConst ci.name ci' = some venv'
  else
    venv' = venv

theorem VEnv.AddConst.le {venv venv' : VEnv} {ci ci'}
    (H : VEnv.AddConst venv safety ci ci' venv') : venv ≤ venv' := by
  unfold VEnv.AddConst at H; split at H
  · exact addConst_le H.2.2
  · exact H ▸ VEnv.LE.rfl

/-- As `VEnv.AddConst`, for a definition: the constant is added and then its defining equation,
matching `TrEnv'.defn`. -/
def VEnv.AddDef (venv : VEnv) (safety : DefinitionSafety) (ci : ConstantInfo)
    (ci' : VDefVal) (venv' : VEnv) : Prop :=
  if safety ≤ ci.safety then
    ∃ base, TrDefVal safety venv ci ci' ∧ ci'.WF venv ∧
      venv.addConst ci.name ci'.toVConstant = some base ∧
      venv' = base.addDefEq ci'.toDefEq
  else
    venv' = venv

theorem VEnv.AddDef.le {venv venv' : VEnv} {ci ci'}
    (H : VEnv.AddDef venv safety ci ci' venv') : venv ≤ venv' := by
  unfold VEnv.AddDef at H; split at H
  · obtain ⟨base, _, _, hadd, rfl⟩ := H
    exact (addConst_le hadd).trans (VEnv.addDefEq_le ..)
  · exact H ▸ VEnv.LE.rfl

def AddQuot1 (name : Name) (kind : QuotKind) (ci' : VConstant) (P : ConstMap → VEnv → Prop)
    (m : ConstMap) (env : VEnv) : Prop :=
  ∃ levelParams type env',
    let ci := .quotInfo { name, kind, levelParams, type }
    TrConstant .safe env ci ci' ∧
    m.find? name = none ∧
    env.addConst name ci' = some env' ∧
    P (m.insert name ci) env'

theorem AddQuot1.to_addQuot
    (H1 : ∀ m env, P m env → f env = some env')
    (m env) (H : AddQuot1 name kind ci' P m env) :
    env.addConst name ci' >>= f = some env' := by
  let ⟨_, _, _, h1, _, h2, h3⟩ := H
  simpa using ⟨_, h2, H1 _ _ h3⟩

theorem AddQuot1.le
    (H1 : ∀ m env, P m env → env ≤ env₀)
    (m env) (H : AddQuot1 name kind ci' P m env) : env ≤ env₀ :=
  let ⟨_, _, _, _, _, h2, h3⟩ := H
  .trans (VEnv.addConst_le h2) (H1 _ _ h3)

def AddQuot (m₁ m₂ : ConstMap) (env₁ env₂ : VEnv) : Prop :=
  AddQuot1 ``Quot .type quotConst (m := m₁) (env := env₁) <|
  AddQuot1 ``Quot.mk .ctor quotMkConst <|
  AddQuot1 ``Quot.lift .lift quotLiftConst <|
  AddQuot1 ``Quot.ind .ind quotIndConst (· = m₂ ∧ ·.addDefEq quotDefEq = env₂)

nonrec theorem AddQuot.to_addQuot (H : AddQuot m₁ m₂ env₁ env₂) : env₁.addQuot = some env₂ :=
  open AddQuot1 in (to_addQuot <| to_addQuot <| to_addQuot <| to_addQuot (by simp)) _ _ H

nonrec theorem AddQuot.le (H : AddQuot m₁ m₂ env₁ env₂) : env₁ ≤ env₂ :=
  open AddQuot1 in (le <| le <| le <| le fun _ _ h => h.2 ▸ VEnv.addDefEq_le) _ _ H

/-- This definition is essentially a `sorry`: it should relate `addInductive`'s
effect on the constant map to `VEnv.addInduct'` (`Lean4Lean.Theory.Inductive.Decl`),
but it currently has no constructors, so the `TrEnv'.induct` case below can never fire
and environments containing inductives are outside the verified `TrEnv` relation.

**CORRECTION.**  This docstring used to say the intended definition is `AddInductStages`
below.  **It is not**, and cannot be: `AddInductStages` is *refuted* for a nested block
(`TrIndDecl.not_addInductStages`, `Verify/Environment/Induct.lean`; `tBlock_not_addInductStages`,
`Verify/Environment/InductR.lean`), because the checker's nested path declares one renamed
auxiliary recursor per nested type — `I.rec_1`, `I.rec_2`, … — and `AddInductStages` is exact
on the map.  The intended definition is now **`AddInductStagesR`**
(`Verify/Environment/InductR.lean`), the same three folds run over
`VInductDecl'.typeConstsC K`, `ctorConstsCR R K` and `recConstsR R`
(`Theory/Inductive/Companion.lean`, `Theory/Inductive/NestedHead.lean`), i.e. over
`VEnv.addInductR`'s constant lists instead of `VEnv.addInduct'`'s.  The flip is

    def AddInduct (m₁ : ConstMap) (env₁ : VEnv) (decl : VInductDecl')
        (m₂ : ConstMap) (env₂ : VEnv) : Prop :=
      ∃ K R, AddInductStagesR m₁ env₁ decl K R m₂ env₂

`AddInductStagesR.of_addInductStages`/`AddInductStages.toR` show this is a *generalisation*:
at `K = []`, `R = decl.idRestore` and `decl.Canonical` the two coincide.

**What the flip additionally needs, and this stream does not own.**
`AddInduct.to_addInduct` then yields `∃ K R, env₁.addInductR decl K R = some env₂`, not
`env₁.addInduct' decl = some env₂`, and `TrEnv'.wf`'s `induct` arm feeds it to
`VDecl.WF.induct` (`Theory/Typing/Env.lean`), whose second hypothesis is the latter.  No
`VInductDecl'` has `addInduct'` equal to a nested `addInductR`, so that rule must be
generalised — to `VEnv.AddNestedB` (`Theory/Inductive/NestedBuild.lean`), which is the sound
form: bare `addInductR` with free `K`/`R` would let a step drop or rename constants at will.
`AddNestedB` needs the declaration history `ds`, which `VDecl.WF` does not currently carry
(`VEnv.WF'` does), so this is a design change in `Theory/Typing/Env.lean` — another stream's
file.  It is the *only* remaining blocker on the abstract side; see
`docs/handoff-inductive-add.md` §5.

Note what the emptiness costs, stated at the top: `VEnvs.WF env` is **unsatisfiable** for any
`env` whose constant map holds an `.inductInfo` (`VEnvs.WF.no_inductInfo`,
`Verify/InductFlip.lean`).  So `addDecl.WF`'s `inductDecl` branch is a *false* statement
today, not merely an open one. -/
inductive AddInduct (m₁ : ConstMap) (env₁ : VEnv) (decl : VInductDecl')
    (m₂ : ConstMap) (env₂ : VEnv) : Prop
  -- TODO

nonrec theorem AddInduct.to_addInduct
    (H : AddInduct m₁ env₁ decl m₂ env₂) : env₁.addInduct' decl = some env₂ :=
  nomatch H

/-! ## R10: the constant-map side of `VEnv.addInduct'`

`AddInductStages` below is what `AddInduct` is meant to be: three folds of a single-constant
step over `D.typeConsts`, `D.ctorConsts` and `D.recConsts`, **with the ι-rules added last**,
in exactly the shape `VEnv.addInduct'_stages` (`Theory/Inductive/Lemmas.lean`) hands back.
That ordering is what makes `to_addInduct` compose the way `AddQuot.to_addQuot` does: each
stage discharges into `VEnv.addConstList`, and `VEnv.addInduct'_eq` glues the three.

**The safety gate.**  Each step asks for `TrConstant .safe`, i.e. `.safe ≤ ci.safety`, and
`.safe` is the top of `DefinitionSafety`, so by antisymmetry `ci.safety = .safe`
(`AddIndConsts.safe` below).  An `unsafe` inductive therefore *cannot* be modelled by this
rule; it is taken by `TrEnv'.ignore`, which gives it no `VEnv` counterpart.  This is the
`TrEnv'.unsafeDef` gate with the polarity flipped, and it is exactly the restriction
`TrIndDecl.safe` (`Verify/Environment/Induct.lean`) records for the same reason: for an
unsafe block `checkConstructors` skips `checkPositivity`, so `VIndField.WF.pos` has no
witness.

Note what the gate does **not** say, and cannot: an unsafe `.inductInfo` may still sit in the
constant map, admitted by `ignore`.  `no_inductInfo_false_at_safe`
(`Verify/TypeChecker/Reduce.lean`) is the standing machine-checked refutation of the stronger
claim, and it is why the shape lemma below is phrased as "either already in `m₁`, or one of
the three inductive shapes" rather than as a statement about the whole map.

**Why this is not (yet) `AddInduct` itself.**  Substituting it for the empty `AddInduct`
above makes `TrEnv'.induct` fire, and the flip is a single coordinated commit across seven
files, four of which this stream does not own.  `docs/handoff-addinduct.md` carries the exact
patch and the measurement below; `Verify/InductFlip.lean` carries everything the flip needs
that was not already in the tree.

**The blast radius, measured** (`scripts/blast-addinduct.lean`, a transitive
`getUsedConstantsAsSet` cone over all 12778 `Lean4Lean` declarations, with the `.thmInfo`
scan trap handled as `scripts/cone-measure.lean` does):

* *Tier 1* — the seven lemmas whose **proofs** case on the empty relation
  (`AddInduct.to_addInduct`, `Aligned.addInduct`, `AddInduct.le`, `TrEnv'.of_value`,
  `TrEnv'.find?_shape`, `TrEnv'.defeqs_shape`, `TrEnv'.no_inductInfo`) have **182**
  transitive users across 18 modules.  All but `no_inductInfo` stay *true*; their induct
  arms are proved (`AddInductStages.le`/`.map_wf`/`.find?_shape`/`.defeqs` here,
  `Aligned.addInductStages` in `Verify/TypeChecker/Reduce.lean`,
  `AddInductStages.of_value_arm` in `Verify/InductFlip.lean`).
* *Tier 2* — the statements that become **false**: 68 transitive users, of which **56 are
  already `sorryAx`-tainted**.  Only **12** are currently sorry-free, and of those, two
  (`checkEqType.WF`, `addQuot.WF`) are repairable and ten are not.

So the earlier note here — "*everything* in `Verify/` goes red" — was too pessimistic: the
irreparable set is **nine declarations**, all in `Verify/TypeChecker/`
(`TrEnv.not_inductInfo`, `.not_ctorInfo`, `.not_recInfo`,
`TypeChecker.VContext.not_inductInfo`, `reduceProjCore_none`, `reduceProjCore.WF`,
`inferProj_always_throws`, `tryEtaStructCore_never_true`, and through the first of those,
`inductiveReduceRec_eq_none`).  They need ι-reduction, projection reduction and structure
eta — real content, not a bigger `rcases`. -/

/-- One stage of an inductive block on the constant-map side: for each `(n, ci')` of the
stage's constant list, some `ConstantInfo` named `n` of the stage's shape `S` is inserted
into the map while `ci'` is added to the abstract environment.

`S` is `.inductInfo` for `D.typeConsts`, `.ctorInfo` for `D.ctorConsts` and `.recInfo` for
`D.recConsts`.  Pinning the shape per stage — rather than asking only for "one of the three"
— is what lets a consumer read off *which* kind of constant a block name carries.

The `ConstantInfo` is existential because `InductiveVal`/`ConstructorVal`/`RecursorVal` carry
elaboration bookkeeping (`numNested`, `isReflexive`, the rule list …) that the abstract
declaration does not model; `TrConstant` pins the two things that matter, the universe count
and the type. -/
inductive AddIndConsts (S : ConstantInfo → Prop) :
    List (Name × VConstant) → ConstMap → VEnv → ConstMap → VEnv → Prop where
  | nil {m env} : AddIndConsts S [] m env m env
  | cons {ci : ConstantInfo} {n ci' cs m env env₁ m₂ env₂} :
    ci.name = n → S ci →
    TrConstant .safe env ci ci' →
    m.find? n = none →
    env.addConst n ci' = some env₁ →
    AddIndConsts S cs (m.insert n ci) env₁ m₂ env₂ →
    AddIndConsts S ((n, ci') :: cs) m env m₂ env₂

theorem AddIndConsts.to_addConstList {S cs m env m₂ env₂}
    (H : AddIndConsts S cs m env m₂ env₂) : env.addConstList cs = some env₂ := by
  induction H with
  | nil => rfl
  | cons _ _ _ _ hadd _ ih => rw [VEnv.addConstList_cons]; simp [hadd, ih]

theorem AddIndConsts.le {S cs m env m₂ env₂}
    (H : AddIndConsts S cs m env m₂ env₂) : env ≤ env₂ :=
  VEnv.addConstList_le H.to_addConstList

theorem AddIndConsts.map_wf {S cs m env m₂ env₂}
    (H : AddIndConsts S cs m env m₂ env₂) (hwf : m.WF) : m₂.WF := by
  induction H with
  | nil => exact hwf
  | cons _ _ _ hfr _ _ ih => exact ih (hwf.insert _ _ hfr)

/-- Anything the stage adds to the map has the stage's shape, is stored under its own name,
and — **the gate** — is `safe`-tagged: `TrConstant .safe` asks for `.safe ≤ ci.safety`, and
`.safe` is the top of `DefinitionSafety`, so antisymmetry pins it. -/
theorem AddIndConsts.find? {S cs m env m₂ env₂} (H : AddIndConsts S cs m env m₂ env₂)
    (hwf : m.WF) (h : m₂.find? name = some ci) :
    m.find? name = some ci ∨ (S ci ∧ ci.name = name ∧ ci.safety = .safe) := by
  induction H with
  | nil => exact .inl h
  | @cons ci₀ n _ _ m _ _ _ _ hname hS htr hfr _ _ ih =>
    rcases ih (hwf.insert _ _ hfr) h with h | h
    · rw [hwf.find?_insert] at h; split at h
      · rename_i hb; cases h
        exact .inr ⟨hS, hname.trans (by simpa using hb),
          DefinitionSafety.le_antisymm DefinitionSafety.le_safe htr.1⟩
      · exact .inl h
    · exact .inr h

/-- The constants a stage adds, on the abstract side, change no definitional equalities. -/
theorem AddIndConsts.defeqs {S cs m env m₂ env₂}
    (H : AddIndConsts S cs m env m₂ env₂) : env₂.defeqs = env.defeqs := by
  induction H with
  | nil => rfl
  | cons _ _ _ _ hadd _ ih =>
    rw [ih]; unfold VEnv.addConst at hadd; split at hadd <;> cases hadd; rfl

/-- **`AddInduct`'s intended definition.**  Three folds — types, constructors, recursors —
and then the ι-rules, mirroring `VEnv.addInduct'_stages`. -/
def AddInductStages (m₁ : ConstMap) (env₁ : VEnv) (D : VInductDecl')
    (m₂ : ConstMap) (env₂ : VEnv) : Prop :=
  ∃ mt et mc ec e₃,
    AddIndConsts (fun ci => ∃ v, ci = .inductInfo v) D.typeConsts m₁ env₁ mt et ∧
    AddIndConsts (fun ci => ∃ v, ci = .ctorInfo v) D.ctorConsts mt et mc ec ∧
    AddIndConsts (fun ci => ∃ v, ci = .recInfo v) D.recConsts mc ec m₂ e₃ ∧
    env₂ = e₃.addIndRules D

theorem AddInductStages.to_addInduct (H : AddInductStages m₁ env₁ D m₂ env₂) :
    env₁.addInduct' D = some env₂ := by
  obtain ⟨mt, et, mc, ec, e₃, h1, h2, h3, rfl⟩ := H
  simp [VEnv.addInduct', VEnv.addIndTypes, VEnv.addIndCtors, VEnv.addIndRecs,
    h1.to_addConstList, h2.to_addConstList, h3.to_addConstList]

theorem AddInductStages.le (H : AddInductStages m₁ env₁ D m₂ env₂) : env₁ ≤ env₂ := by
  obtain ⟨mt, et, mc, ec, e₃, h1, h2, h3, rfl⟩ := H
  exact h1.le.trans <| h2.le.trans <| h3.le.trans VEnv.addIndRules_le

theorem AddInductStages.map_wf (H : AddInductStages m₁ env₁ D m₂ env₂) (hwf : m₁.WF) : m₂.WF := by
  obtain ⟨mt, et, mc, ec, e₃, h1, h2, h3, rfl⟩ := H
  exact h3.map_wf (h2.map_wf (h1.map_wf hwf))

/-- **The new disjunct of `TrEnv'.find?_shape`.**  A name the block introduces carries one of
the three inductive `ConstantInfo` shapes; every other name is unchanged. -/
theorem AddInductStages.find?_shape (H : AddInductStages m₁ env₁ D m₂ env₂) (hwf : m₁.WF)
    (h : m₂.find? name = some ci) :
    m₁.find? name = some ci ∨
    (((∃ v, ci = .inductInfo v) ∨ (∃ v, ci = .ctorInfo v) ∨ (∃ v, ci = .recInfo v)) ∧
      ci.name = name ∧ ci.safety = .safe) := by
  obtain ⟨mt, et, mc, ec, e₃, h1, h2, h3, rfl⟩ := H
  rcases h3.find? (h2.map_wf (h1.map_wf hwf)) h with h | ⟨hS, h⟩
  · rcases h2.find? (h1.map_wf hwf) h with h | ⟨hS, h⟩
    · rcases h1.find? hwf h with h | ⟨hS, h⟩
      exacts [.inl h, .inr ⟨.inl hS, h⟩]
    · exact .inr ⟨.inr (.inl hS), h⟩
  · exact .inr ⟨.inr (.inr hS), h⟩

/-- The converse of `VEnv.addDefEqList_defeqs` (`Theory/Inductive/Lemmas.lean`): a fold of
`addDefEq` adds *only* the rules of its list. -/
theorem VEnv.addDefEqList_defeqs_inv : ∀ (dfs : List VDefEq) (env : VEnv) {df},
    (dfs.foldl VEnv.addDefEq env).defeqs df → env.defeqs df ∨ df ∈ dfs
  | [], _, _, h => .inl h
  | d :: dfs, env, df, h => by
    rcases VEnv.addDefEqList_defeqs_inv dfs (env.addDefEq d) h with h | h
    · rcases h with rfl | h
      · exact .inr (.head _)
      · exact .inl h
    · exact .inr (.tail _ h)

theorem VEnv.addIndRules_defeqs_inv {env : VEnv} {D : VInductDecl'} {df}
    (h : (env.addIndRules D).defeqs df) : env.defeqs df ∨ df ∈ D.iotaRules :=
  VEnv.addDefEqList_defeqs_inv _ _ h

/-- **The new disjunct of `TrEnv'.defeqs_shape`.**  The only rules a block adds are its
ι-rules; the three constant stages add none. -/
theorem AddInductStages.defeqs (H : AddInductStages m₁ env₁ D m₂ env₂) (h : env₂.defeqs df) :
    env₁.defeqs df ∨ df ∈ D.iotaRules := by
  obtain ⟨mt, et, mc, ec, e₃, h1, h2, h3, rfl⟩ := H
  have hstage : e₃.defeqs = env₁.defeqs := by rw [h3.defeqs, h2.defeqs, h1.defeqs]
  refine (VEnv.addIndRules_defeqs_inv h).imp (fun h => ?_) id
  rwa [hstage] at h

/-! ### The anti-lie lemmas

Moved here from `Verify/InductFlip.lean` (unchanged) so that they sit beside the definitions
they are about and are available to `Verify/Environment/Induct.lean` and
`Verify/Environment/InductR.lean`, neither of which may depend on the type-checker layer. -/

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


/-- The stages produce the very `addIndTypes` success `VInductDecl'.WF.ctors` is staged over. -/
theorem AddInductStages.addIndTypes {m₁ m₂ : ConstMap} {env₁ env₂ : VEnv} {D : VInductDecl'}
    (H : AddInductStages m₁ env₁ D m₂ env₂) : ∃ et, env₁.addIndTypes D = some et := by
  obtain ⟨mt, et, mc, ec, e₃, h1, -, -, -⟩ := H
  exact ⟨et, h1.to_addConstList⟩

/-- Insert a whole block of definitions into the constant map. -/
def insertDefs (C : ConstMap) (cis : List DefinitionVal) : ConstMap :=
  cis.foldl (fun C ci => C.insert ci.name (.defnInfo ci)) C

variable (safety : DefinitionSafety) (env env' : VEnv) in
/-- Translation data for a mutual block: the headers are translated against the environment
before the block is added, the values against the environment that already has every constant
of the block, mirroring the kernel adding them all as axioms first. -/
def TrDefBlock (cis : List DefinitionVal) (cis' : List VDefVal) : Prop :=
  List.Forall₂ (fun ci ci' =>
    TrConstVal safety env (.defnInfo ci) ci'.toVConstVal ∧
    TrExprS env' ci.levelParams [] ci.value ci'.value) cis cis'

variable (safety : DefinitionSafety) in
inductive TrEnv' : ConstMap → Bool → VEnv → Prop where
  /-- The base case: any *empty* constant map, at either `SMap` stage, models `VEnv.empty`.

  This is deliberately not pinned to the literal `({} : ConstMap)`: `Kernel.Environment.empty`
  builds its constant map at stage 2 (`stage₁ := false`), while `({} : ConstMap)` has
  `stage₁ = true`, and the two are therefore not equal. Since nothing downstream inspects
  the stage, the constructor asks only for the two facts that are actually used: the map is
  well-formed, and it has no entries. -/
  | empty : C.WF → (∀ n, C.find? n = none) → TrEnv' C false .empty
  | ignore :
    C.find? ci.name = none → ¬safety ≤ ci.safety →
    TrEnv' C Q env →
    TrEnv' (C.insert ci.name ci) Q env
  | axiom :
    TrConstant safety env (.axiomInfo ci) ci' →
    C.find? ci.name = none → ci'.WF env →
    env.addConst ci.name ci' = some env' →
    TrEnv' C Q env →
    TrEnv' (C.insert ci.name (.axiomInfo ci)) Q env'
  | defn {ci' : VDefVal} :
    TrDefVal safety env (.defnInfo ci) ci' →
    C.find? ci.name = none → ci'.WF env →
    env.addConst ci.name ci'.toVConstant = some env' →
    TrEnv' C Q env →
    TrEnv' (C.insert ci.name (.defnInfo ci)) Q (env'.addDefEq ci'.toDefEq)
  /-- A `partial`/`unsafe` mutual block, and an unsafe definition as the one-element case.

  The first hypothesis is the **safety gate**: at least one member must carry a
  `DefinitionSafety` tag other than `.safe`. It is what keeps the rule out of the safe
  fragment: `TrDefBlock .safe` forces `.safe ≤ ci.safety` for *every* member, i.e.
  `ci.safety = .safe`, which contradicts the gate. So `TrEnv' .safe` can never take this
  step (`TrEnv'.wf_pure`), and the model it builds never contains the circular
  `VDecl.WF.unsafeDef`.

  Both kernels reject a *safe* `mutualDefnDecl` outright ("invalid mutual definition,
  declaration is not tagged as unsafe/partial"), so the gate discards nothing real; it is
  discharged from the tag the kernel itself checked, not assumed
  (`addMutualBlock.WF`, `addUnsafeDef.WF`). -/
  | unsafeDef {cis : List DefinitionVal} {cis' : List VDefVal} :
    (∃ ci ∈ cis, (ConstantInfo.defnInfo ci).safety ≠ .safe) →
    TrDefBlock safety env env' cis cis' →
    -- the block's names are distinct; `addMutual` checks this, as does lean4#14632
    (cis.map (·.name)).Nodup →
    (∀ ci ∈ cis, C.find? ci.name = none) →
    (∀ ci' ∈ cis', ci'.toVConstant.WF env) →
    env.addConsts cis' = some env' →
    (∀ ci' ∈ cis', ci'.WF env') →
    TrEnv' C Q env →
    TrEnv' (insertDefs C cis) Q (env'.addDefEqs cis')
  | thm {ci' : VDefVal} :
    TrDefVal safety env (.thmInfo ci) ci' →
    C.find? ci.name = none → ci'.WF env →
    env.HasType ci'.uvars [] ci'.type (.sort .zero) →
    env.addConst ci.name ci'.toVConstant = some env' →
    TrEnv' C Q env →
    TrEnv' (C.insert ci.name (.thmInfo ci)) Q env'
  | opaque {ci' : VDefVal} :
    TrDefVal safety env (.opaqueInfo ci) ci' →
    C.find? ci.name = none → ci'.WF env →
    env.addConst ci.name ci'.toVConstant = some env' →
    TrEnv' C Q env →
    TrEnv' (C.insert ci.name (.opaqueInfo ci)) Q env'
  | quot :
    env.QuotReady →
    AddQuot C C' env env' →
    TrEnv' C false env →
    TrEnv' C' true env'
  | induct :
    decl.WF env →
    AddInduct C env decl C' env' →
    TrEnv' C Q env →
    TrEnv' C' Q env'

def TrEnv (safety : DefinitionSafety) (env : Environment) (venv : VEnv) : Prop :=
  TrEnv' safety env.constants env.quotInit venv

theorem TrEnv'.wf (H : TrEnv' safety C Q venv) : venv.WF := by
  induction H with
  | empty => exact ⟨_, .empty⟩
  | ignore _ _ _ ih => exact ih
  | «axiom» _ _ h1 h2 _ ih =>
    have ⟨_, H⟩ := ih
    exact ⟨_, H.decl <| .axiom (ci := ⟨_, _⟩) h1 h2⟩
  | defn h1 _ h2 h3 _ ih =>
    have ⟨_, H⟩ := ih
    have := h1.1.2; dsimp [ConstantInfo.name, ConstantInfo.toConstantVal] at this
    exact ⟨_, H.decl <| .def h2 (this ▸ h3)⟩
  | unsafeDef _ _ _ _ h2 h3 h4 _ ih =>
    have ⟨_, H⟩ := ih
    exact ⟨_, H.decl <| .unsafeDef h2 h3 h4⟩
  | thm h1 _ h2 h3 h4 _ ih =>
    have ⟨_, H⟩ := ih
    have hn := h1.1.2
    dsimp [ConstantInfo.name, ConstantInfo.toConstantVal] at hn
    exact ⟨_, (H.decl (.example h2)).decl (.axiom ⟨_, h3⟩ (hn ▸ h4))⟩
  | «opaque» h1 _ h2 h3 _ ih =>
    have ⟨_, H⟩ := ih
    have := h1.1.2; dsimp [ConstantInfo.name, ConstantInfo.toConstantVal] at this
    exact ⟨_, H.decl <| .opaque h2 (this ▸ h3)⟩
  | quot h1 h2 _ ih =>
    have ⟨_, H⟩ := ih
    exact ⟨_, H.decl <| .quot h1 h2.to_addQuot⟩
  | induct h1 h2 _ ih =>
    have ⟨_, H⟩ := ih
    exact ⟨_, H.decl <| .induct h1 h2.to_addInduct⟩

/-- A `safe`-visible block is entirely `safe`-tagged, so the `unsafeDef` gate is unsatisfiable
there. This is the whole content of the gate. -/
theorem TrDefBlock.safe_not_unsafeDef {env env' : VEnv} {cis cis'}
    (H : TrDefBlock .safe env env' cis cis') :
    ¬ ∃ ci ∈ cis, (ConstantInfo.defnInfo ci).safety ≠ .safe := by
  rintro ⟨ci, hci, hne⟩
  obtain ⟨ci', -, htr, -⟩ := Lean4Lean.List.Forall₂.forall_exists_l H _ hci
  exact hne (DefinitionSafety.le_antisymm DefinitionSafety.le_safe htr.1.1)

/-- **The safe fragment is closed.** At `safety := .safe` the abstract environment is built
by `VDecl` steps satisfying `VDecl.noUnsafe`: the only circular rule, `TrEnv'.unsafeDef`, is
gated on a member tagged `partial`/`unsafe`, and `TrDefBlock .safe` forces every member to be
tagged `safe`. `partial`/`unsafe` constants reach the safe model only through `TrEnv'.ignore`,
which gives them no `VEnv` counterpart at all.

This is what `VEnv.LeanWF` needs from the refinement layer; the remaining half of
`VDecl.isPure` (no further `.axiom` steps) is bookkeeping about the kernel-level declaration
list, not about `TrEnv'`. -/
theorem TrEnv'.wf_noUnsafe (H : TrEnv' .safe C Q venv) :
    ∃ ds, VEnv.WF' ds venv ∧ ∀ d ∈ ds, d.noUnsafe := by
  have step {d : VDecl} {ds : List VDecl} (hd : d.noUnsafe)
      (h : ∀ d ∈ ds, VDecl.noUnsafe d) : ∀ d' ∈ d :: ds, VDecl.noUnsafe d' := by
    intro d' hd'
    rcases List.mem_cons.1 hd' with rfl | h'
    exacts [hd, h _ h']
  induction H with
  | empty => exact ⟨_, .empty, nofun⟩
  | ignore _ _ _ ih => exact ih
  | «axiom» _ _ h1 h2 _ ih =>
    have ⟨_, H, hp⟩ := ih
    exact ⟨_, H.decl <| .axiom (ci := ⟨_, _⟩) h1 h2, step trivial hp⟩
  | defn h1 _ h2 h3 _ ih =>
    have ⟨_, H, hp⟩ := ih
    have := h1.1.2; dsimp [ConstantInfo.name, ConstantInfo.toConstantVal] at this
    exact ⟨_, H.decl <| .def h2 (this ▸ h3), step trivial hp⟩
  | unsafeDef hns hblk => exact absurd hns hblk.safe_not_unsafeDef
  | thm h1 _ h2 h3 h4 _ ih =>
    have ⟨_, H, hp⟩ := ih
    have hn := h1.1.2
    dsimp [ConstantInfo.name, ConstantInfo.toConstantVal] at hn
    exact ⟨_, (H.decl (.example h2)).decl (.axiom ⟨_, h3⟩ (hn ▸ h4)),
      step trivial (step trivial hp)⟩
  | «opaque» h1 _ h2 h3 _ ih =>
    have ⟨_, H, hp⟩ := ih
    have := h1.1.2; dsimp [ConstantInfo.name, ConstantInfo.toConstantVal] at this
    exact ⟨_, H.decl <| .opaque h2 (this ▸ h3), step trivial hp⟩
  | quot h1 h2 _ ih =>
    have ⟨_, H, hp⟩ := ih
    exact ⟨_, H.decl <| .quot h1 h2.to_addQuot, step trivial hp⟩
  | induct h1 h2 _ ih =>
    have ⟨_, H, hp⟩ := ih
    exact ⟨_, H.decl <| .induct h1 h2.to_addInduct, step trivial hp⟩

nonrec theorem TrEnv.wf_noUnsafe {env : Environment} {venv : VEnv} (H : TrEnv .safe env venv) :
    ∃ ds, VEnv.WF' ds venv ∧ ∀ d ∈ ds, d.noUnsafe := H.wf_noUnsafe

/-! ## A witness: `AddInductStages` is satisfiable

A relation with no instance is the configuration that has produced every unsatisfiable class
found on this project, and the composition lemmas above are only a *proxy*.  This is the
witness, and it is chosen to exercise the one thing three folds can get wrong: **which
environment each stage's obligation is stated at.**

The block is a one-type, one-constructor, parameterless `Unit`.  Its constructor's stored
type is `.const `R10.Wit.U []` — the block's *own* type constant — so the constructor stage's
`TrConstant` is unsatisfiable at `VEnv.empty` and satisfiable only at the environment
`addIndTypes` produced.  That is the same wall `no_trIndCtor_at_base`
(`Verify/Environment/Induct.lean`) records for `TrIndDecl`, met here from the other side; the
fold threads the environment, so it stages by construction.

All three stages are covered, recursor included, and the ι-rules are added last. -/

namespace R10.Wit

/-- `inductive U : Type where | unit : U` -/
def decl : VInductDecl' where
  uvars := 0
  params := []
  lvl := .succ .zero
  isLE := false
  types := [{ name := `R10.Wit.U, type := .sort (.succ .zero), indices := [],
              ctors := [{ name := `R10.Wit.U.unit, params := [], fields := [], args := [] }] }]

example : decl.typeConsts = [(`R10.Wit.U, ⟨0, .sort (.succ .zero)⟩)] := rfl
example : decl.ctorConsts = [(`R10.Wit.U.unit, ⟨0, .const `R10.Wit.U []⟩)] := rfl

/-- `∀ (motive : U → Prop) (h : motive U.unit) (t : U), motive t` -/
def recTypeE : Expr :=
  .forallE `motive (.forallE `t (.const `R10.Wit.U []) (.sort .zero) .default)
    (.forallE `h (.app (.bvar 0) (.const `R10.Wit.U.unit []))
      (.forallE `t (.const `R10.Wit.U []) (.app (.bvar 2) (.bvar 0)) .default) .default) .default

example : decl.recConsts = [(`R10.Wit.U.rec, ⟨0,
    .forallE (.forallE (.const `R10.Wit.U []) (.sort .zero))
      (.forallE (.app (.bvar 0) (.const `R10.Wit.U.unit []))
        (.forallE (.const `R10.Wit.U []) (.app (.bvar 2) (.bvar 0))))⟩)] := rfl

/-- The recursor's motive binder type, `U → Prop`. -/
abbrev motiveV : VExpr := .forallE (.const `R10.Wit.U []) (.sort .zero)

variable {env : VEnv}
  (hU : env.constants `R10.Wit.U = some ⟨0, .sort (.succ .zero)⟩)
  (hu : env.constants `R10.Wit.U.unit = some ⟨0, .const `R10.Wit.U []⟩)

include hU in
theorem hasTy_U (Γ) : env.HasType 0 Γ (.const `R10.Wit.U []) (.sort (.succ .zero)) :=
  VEnv.HasType.const (Γ := Γ) (U := 0) hU nofun rfl

include hu in
theorem hasTy_unit (Γ) : env.HasType 0 Γ (.const `R10.Wit.U.unit []) (.const `R10.Wit.U []) :=
  VEnv.HasType.const (Γ := Γ) (U := 0) hu nofun rfl

include hU hu in
theorem tr_recType : TrExprS env [] [] recTypeE (decl.recType 0) := by
  have hb0 : ∀ Γ, env.HasType 0 (motiveV :: Γ) (.bvar 0) motiveV := fun _ => .bvar .zero
  have hb2 : ∀ A B Γ, env.HasType 0 (A :: B :: motiveV :: Γ) (.bvar 2) motiveV := fun _ _ _ =>
    .bvar (.succ (.succ .zero))
  have hbT : ∀ Γ, env.HasType 0 (VExpr.const `R10.Wit.U [] :: Γ) (.bvar 0)
      (.const `R10.Wit.U []) := fun _ => .bvar .zero
  have hM : env.IsType 0 [] motiveV :=
    ⟨_, .forallEDF (hasTy_U hU _) (.sortDF trivial trivial (.refl _))⟩
  have hH : ∀ Γ, env.HasType 0 (motiveV :: Γ)
      (.app (.bvar 0) (.const `R10.Wit.U.unit [])) (.sort .zero) := fun Γ =>
    .appDF (hb0 Γ) (hasTy_unit hu _)
  have hB : ∀ Γ, env.HasType 0 (VExpr.const `R10.Wit.U [] ::
      (VExpr.app (.bvar 0) (.const `R10.Wit.U.unit [])) :: motiveV :: Γ)
      (.app (.bvar 2) (.bvar 0)) (.sort .zero) := fun Γ =>
    .appDF (hb2 _ _ Γ) (hbT _)
  refine .forallE hM ?_ ?_ ?_
  · exact ⟨_, .forallEDF (hH _) (.forallEDF (hasTy_U hU _) (hB _))⟩
  · exact .forallE ⟨_, hasTy_U hU _⟩ ⟨_, .sortDF trivial trivial (.refl _)⟩
      (.const hU rfl rfl) (.sort rfl)
  · refine .forallE ⟨_, hH _⟩ ?_ ?_ ?_
    · exact ⟨_, .forallEDF (hasTy_U hU _) (hB _)⟩
    · exact .app (hb0 _) (hasTy_unit hu _) (.bvar rfl) (.const hu rfl rfl)
    · refine .forallE ⟨_, hasTy_U hU _⟩ ⟨_, hB _⟩ (.const hU rfl rfl) ?_
      exact .app (hb2 _ _ _) (hbT _) (.bvar rfl) (.bvar rfl)

def uInd : InductiveVal where
  name := `R10.Wit.U; levelParams := []; type := .sort (.succ .zero)
  numParams := 0; numIndices := 0; all := [`R10.Wit.U]; ctors := [`R10.Wit.U.unit]
  numNested := 0; isRec := false; isUnsafe := false; isReflexive := false

def uCtor : ConstructorVal where
  name := `R10.Wit.U.unit; levelParams := []; type := .const `R10.Wit.U []
  induct := `R10.Wit.U; cidx := 0; numParams := 0; numFields := 0; isUnsafe := false

def uRec : RecursorVal where
  name := `R10.Wit.U.rec; levelParams := []; type := recTypeE
  all := [`R10.Wit.U]; numParams := 0; numIndices := 0; numMotives := 1; numMinors := 1
  rules := []; k := false; isUnsafe := false

/-- **`AddInductStages` is satisfiable.**  All three stages fire, and the constructor stage
is the one that could not have fired at `VEnv.empty`: its stored type is the block's own type
constant, so `TrExprS.const` needs `U` declared, which it is only after stage 1. -/
theorem addInductStages_wit {m : ConstMap} (hwf : m.WF) (hfr : ∀ n, m.find? n = none) :
    ∃ m' env', AddInductStages m VEnv.empty decl m' env' ∧
      VEnv.empty.addInduct' decl = some env' ∧
      m'.find? `R10.Wit.U.unit = some (.ctorInfo uCtor) ∧
      m'.find? `R10.Wit.U.rec = some (.recInfo uRec) ∧
      (∃ ci, env'.constants `R10.Wit.U.unit = some ci) ∧
      (∃ ci, env'.constants `R10.Wit.U.rec = some ci) := by
  obtain ⟨e1, he1⟩ := VEnv.addConst_eq_none (env := VEnv.empty) (name := `R10.Wit.U)
    (ci := ⟨0, .sort (.succ .zero)⟩) rfl
  have c1 := VEnv.addConst_constants_eq he1
  have hU1 : e1.constants `R10.Wit.U = some ⟨0, .sort (.succ .zero)⟩ := by rw [c1]; simp
  obtain ⟨e2, he2⟩ := VEnv.addConst_eq_none (env := e1) (name := `R10.Wit.U.unit)
    (ci := ⟨0, .const `R10.Wit.U []⟩) (by rw [c1]; simp [VEnv.empty])
  have c2 := VEnv.addConst_constants_eq he2
  have hU2 : e2.constants `R10.Wit.U = some ⟨0, .sort (.succ .zero)⟩ := by
    rw [c2]; simp [hU1]
  have hu2 : e2.constants `R10.Wit.U.unit = some ⟨0, .const `R10.Wit.U []⟩ := by rw [c2]; simp
  obtain ⟨e3, he3⟩ := VEnv.addConst_eq_none (env := e2) (name := `R10.Wit.U.rec)
    (ci := ⟨0, decl.recType 0⟩) (by rw [c2, c1]; simp [VEnv.empty])
  have w1 := hwf.insert `R10.Wit.U (.inductInfo uInd) (hfr _)
  have f2 : (m.insert `R10.Wit.U (.inductInfo uInd)).find? `R10.Wit.U.unit = none := by
    rw [hwf.find?_insert]; simp [hfr]
  have w2 := w1.insert `R10.Wit.U.unit (.ctorInfo uCtor) f2
  have s1 : AddIndConsts (fun ci => ∃ v, ci = .inductInfo v) decl.typeConsts
      m VEnv.empty (m.insert `R10.Wit.U (.inductInfo uInd)) e1 :=
    .cons (ci := .inductInfo uInd) rfl ⟨_, rfl⟩ ⟨by decide, rfl, .sort rfl⟩ (hfr _) he1 .nil
  have s2 : AddIndConsts (fun ci => ∃ v, ci = .ctorInfo v) decl.ctorConsts
      (m.insert `R10.Wit.U (.inductInfo uInd)) e1
      ((m.insert `R10.Wit.U (.inductInfo uInd)).insert `R10.Wit.U.unit (.ctorInfo uCtor)) e2 :=
    .cons (ci := .ctorInfo uCtor) rfl ⟨_, rfl⟩ ⟨by decide, rfl, .const hU1 rfl rfl⟩ f2 he2 .nil
  have s3 : AddIndConsts (fun ci => ∃ v, ci = .recInfo v) decl.recConsts
      ((m.insert `R10.Wit.U (.inductInfo uInd)).insert `R10.Wit.U.unit (.ctorInfo uCtor)) e2
      (((m.insert `R10.Wit.U (.inductInfo uInd)).insert `R10.Wit.U.unit
        (.ctorInfo uCtor)).insert `R10.Wit.U.rec (.recInfo uRec)) e3 :=
    .cons (ci := .recInfo uRec) rfl ⟨_, rfl⟩ ⟨by decide, rfl, tr_recType hU2 hu2⟩
      (by rw [w1.find?_insert, hwf.find?_insert]; simp [hfr, Lean.mkRecName]) he3 .nil
  have H : AddInductStages m VEnv.empty decl _ (e3.addIndRules decl) :=
    ⟨_, _, _, _, e3, s1, s2, s3, rfl⟩
  have c3 := VEnv.addConst_constants_eq he3
  refine ⟨_, _, H, H.to_addInduct, ?_, ?_, ?_, ?_⟩
  · rw [w2.find?_insert, w1.find?_insert]; simp
  · rw [w2.find?_insert]; simp
  · exact ⟨⟨0, .const `R10.Wit.U []⟩,
      by rw [VEnv.addIndRules_constants, c3]; simp [hu2]⟩
  · exact ⟨_, by rw [VEnv.addIndRules_constants]; exact VEnv.addConst_self he3⟩

end R10.Wit
