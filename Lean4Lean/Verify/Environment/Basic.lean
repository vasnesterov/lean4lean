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
and environments containing inductives are outside the verified `TrEnv` relation. -/
inductive AddInduct (m₁ : ConstMap) (env₁ : VEnv) (decl : VInductDecl')
    (m₂ : ConstMap) (env₂ : VEnv) : Prop
  -- TODO

nonrec theorem AddInduct.to_addInduct
    (H : AddInduct m₁ env₁ decl m₂ env₂) : env₁.addInduct' decl = some env₂ :=
  nomatch H

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
