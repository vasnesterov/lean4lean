import Lean4Lean.Theory.SetModel.InductOracleWitness

/-!
# The `.induct` residual at a block with **no empty domain**

`InductOracleWitness.lean` closes `InductOracleOK` at `boxDecl`
(`inductive Box (e : Ext) : Prop | mk : Box e`) with the oracle `fun _ _ ↦ ∅`.  Every
obligation there holds *because* the parameter `Ext` denotes `∅`, so every declared type is
a `∀` over an empty domain.  Its own §5 says so, and its docstring names the smallest block
that escapes the mechanism: `inductive Unit1 : Prop | mk`.

**This file is that block, and it discharges the residual there.**

## What is proved

* `unitDecl_WF : unitDecl.WF VEnv.empty` — the block is `VInductDecl'.WF` over the **empty**
  environment; unlike `boxDecl` it needs no ambient constant at all.
* `unitDecl_history : VEnv.WF' [.induct unitDecl] unitEnv` — and `unitEnv_add` is `rfl`, so
  every constant lookup below is `rfl` too.
* `inductOracleOK_unit` — **both** fields of `InductOracleOK`, at the oracle
  `unitOracle = (Unit1 ↦ {•}, everything else ↦ •)`.  `oracleFits_unit` extends it to the
  whole list `[.induct unitDecl]`.

## Nothing here is empty, and nothing is vacuous (§7)

* `unitDecl_params_nil`, `unitTy_indices_nil` — there is no parameter or index telescope for
  the empty-domain mechanism to act on.
* `interp_Unit1_ne_empty` — `⟦Unit1⟧ = {•} ≠ ∅`, so `Unit1` is an *inhabited* proposition
  and `Unit1.mk`'s value `•` really is an element of it.
* `exists_true_motive` (hypothesis-free) — there is an `f ∈ ⟦Unit1 → Prop⟧` with
  `f ‘ • = {•}`, and `exists_nonempty_minor_domain` turns that into a nonempty minor-premise
  domain.  So `oracleOK_unit_rec`'s two inner quantifiers are not vacuous.
* `mem_interp_consts_unit`, `defEq_rules_unit` — the obligations with the `Above` wrapper
  **stripped**, at an arbitrary `κ`, no chain hypothesis anywhere.  Every proof here goes
  through `Above.pure`.

## Why it is easier than forecast, and where the real frontier is (§9)

`InductOracleWitness.lean` predicted this case would need "a genuine `mkLam`, i.e.
`SetModel/IndInterp.lean`'s work".  It does not.  `unitDecl.isLE = false`, so the whole of
`recType 0` is a **proposition** (`hasType_recB1`: sort `imax 0 (imax 0 0)`), `interp` takes
the impredicative `mkForallProp` branch at every binder, and the oracle can hand
`Unit1.rec` the value `•`.  The membership is three `mem_interp_forallE_prop_iff` steps
closed by `U₀`-irrelevance; the ι-rule's two sides are both `•` because their bodies are
*proofs* (`isProof_iotaLhsLam`, `isProof_iotaRhsLam`), so `interp_lam_proof` settles the
equation without any β-computation.

The frontier is therefore **large elimination**, not `Prop`.  `VInductDecl'.WF` permits
`isLE := true` for this block (`unitDeclLE_LECond`, vacuous because the constructor has no
fields), and that is what Lean actually declares.  There the innermost binder is no longer
propositional for `u.eval ls ≠ 0`, `interp` takes `mkForallType`, and `•` is not a legal
value (`pt_not_mem_mkForallType_of_nonempty`).  Open.

## The `hle` hypothesis

Every proof-splitting decision is read off a typing derivation in `unitEnv` through
`isProp_iff`/`isProof_iff` (§4), so §5–§6 carry `hle : unitEnv ≤ envF` — the same hypothesis
`QuotInterp.lean` carries for the four quotient constants.  It is not a strengthening of the
residual: `coherentOn_cnstOf` (`CnstRecursion.lean:553`) threads `env ≤ envF` through every
declaration step, and at `[.induct unitDecl]` that `env` **is** `unitEnv`
(`eq_unitEnv_of_wf'`).  `oracleFits_unit_at_consumer` is the statement with no `hle` in it.

## The other direction, field by field

`CnstRecursion.lean` has the `consts` cell's negative bound (`not_oracleOK_falseProp`).
`InductOracleAudit.lean` §5's `rules` cell reads "open — no ι-rule of a `WF` block is known
to be refutable".  `not_defEqOK_falseType` does **not** close that cell as worded: it refutes
`DefEqOK` at a `VDefEq` of one's own choosing, not at an ι-rule of a well-formed block.  It
bounds the cell one notch tighter — the field's *body* is not a tautology — and no more.

Worth saying plainly: the cell as worded is probably asking for something that must not
exist.  A `WF` block's ι-rules are well typed (`addInduct_WF`), so a *correct* model has to
satisfy `DefEqOK` at every one of them; a refutation there would refute the model, not bound
the residual.  So `not_defEqOK_falseType` is likely the strongest honest entry that column can
have, and the cell should be **reworded** rather than closed.  That rewording is a change to
`InductOracleAudit.lean`'s §5 table; it is recorded here and has not been made.
-/

namespace Lean4Lean.SetModel.UnitAudit

open Lean4Lean LO LO.FirstOrder LO.FirstOrder.SetTheory

/-! ## 1. The block -/

/-- `inductive Unit1 : Prop | mk`.  One type former, one constructor, no parameters, no
indices, no fields; small elimination (`isLE := false`). -/
def unitCtor : VIndCtor := { name := `Unit1.mk, params := [], fields := [], args := [] }

def unitTy : VIndType :=
  { name := `Unit1, type := .sort .zero, indices := [], ctors := [unitCtor] }

def unitDecl : VInductDecl' where
  uvars := 0
  params := []
  lvl := .zero
  isLE := false
  types := [unitTy]

/-- `motive : Unit1 → Prop` — the recursor's first binder. -/
abbrev motTy : VExpr := .forallE (.const `Unit1 []) (.sort .zero)
/-- `motive Unit1.mk` — the minor premise, in the context `[motTy]`. -/
abbrev minTy : VExpr := .app (.bvar 0) (.const `Unit1.mk [])
/-- `Unit1.rec`. -/
abbrev recN : Name := Lean.mkRecName `Unit1

/-! ### The derived data, computed

Every equation in this section is `rfl`; they are recorded so that no later proof has to
unfold `recType`/`iotaRule`. -/

theorem unitDecl_motives : unitDecl.motives = [motTy] := rfl
theorem unitDecl_minors : unitDecl.minors = [minTy] := rfl

/-- `Unit1.rec : ∀ (motive : Unit1 → Prop), motive mk → ∀ t : Unit1, motive t`. -/
theorem unitDecl_recType :
    unitDecl.recType 0 =
      .forallE motTy (.forallE minTy
        (.forallE (.const `Unit1 []) (.app (.bvar 2) (.bvar 0)))) := rfl

theorem unitDecl_typeConsts : unitDecl.typeConsts = [(`Unit1, ⟨0, .sort .zero⟩)] := rfl
theorem unitDecl_ctorConsts :
    unitDecl.ctorConsts = [(`Unit1.mk, ⟨0, .const `Unit1 []⟩)] := rfl
theorem unitDecl_recConsts : unitDecl.recConsts = [(recN, ⟨0, unitDecl.recType 0⟩)] := rfl

theorem unitDecl_allConsts :
    unitDecl.allConsts =
      [(`Unit1, ⟨0, .sort .zero⟩), (`Unit1.mk, ⟨0, .const `Unit1 []⟩),
       (recN, ⟨0, unitDecl.recType 0⟩)] := rfl

theorem unitDecl_allNames : unitDecl.allNames = [`Unit1, `Unit1.mk, recN] := rfl

/-- The single ι-rule, `Unit1.rec motive m mk ≡ m`, η-expanded on both sides as
`VInductDecl'.iotaRule` builds it. -/
theorem unitDecl_iotaCtx : unitDecl.iotaCtx unitCtor = [motTy, minTy] := rfl

theorem unitDecl_iotaRules : unitDecl.iotaRules = [unitDecl.iotaRule 0 0 unitCtor] := rfl

theorem unitRule_uvars : (unitDecl.iotaRule 0 0 unitCtor).uvars = 0 := rfl

theorem unitRule_lhs :
    (unitDecl.iotaRule 0 0 unitCtor).lhs =
      .lam motTy (.lam minTy
        (.app (.app (.app (.const recN []) (.bvar 1)) (.bvar 0))
          (.const `Unit1.mk []))) := rfl

theorem unitRule_rhs :
    (unitDecl.iotaRule 0 0 unitCtor).rhs =
      .lam motTy (.lam minTy
        (.app (.app (.lam motTy (.lam minTy (.bvar 0))) (.bvar 1)) (.bvar 0))) := rfl

theorem unitRule_type :
    (unitDecl.iotaRule 0 0 unitCtor).type =
      .forallE motTy (.forallE minTy (.app (.bvar 1) (.const `Unit1.mk []))) := rfl

/-! ## 2. The environment -/

/-- The environment `addInduct' unitDecl` produces over `VEnv.empty`, written in the shape
the definition builds so that `unitEnv_add` is `rfl`. -/
def unitEnv : VEnv where
  constants n :=
    if recN = n then some ⟨0, unitDecl.recType 0⟩ else
    if `Unit1.mk = n then some ⟨0, .const `Unit1 []⟩ else
    if `Unit1 = n then some ⟨0, .sort .zero⟩ else none
  defeqs x := x = unitDecl.iotaRule 0 0 unitCtor ∨ False

theorem unitEnv_add : VEnv.empty.addInduct' unitDecl = some unitEnv := rfl

theorem unitEnv_Unit1 : unitEnv.constants `Unit1 = some ⟨0, .sort .zero⟩ := rfl
theorem unitEnv_mk : unitEnv.constants `Unit1.mk = some ⟨0, .const `Unit1 []⟩ := rfl
theorem unitEnv_rec : unitEnv.constants recN = some ⟨0, unitDecl.recType 0⟩ := rfl

/-! ## 3. `unitDecl` is well formed over `VEnv.empty`, and reachable -/

theorem unitTy_canonType : unitTy.canonType unitDecl = .sort .zero := rfl

theorem unitCtor_canonResult : unitCtor.canonResult unitDecl 0 = .const `Unit1 [] := rfl

theorem unitEnv_addIndTypes :
    ∃ env₁, VEnv.empty.addIndTypes unitDecl = some env₁ ∧
      env₁.constants `Unit1 = some ⟨0, .sort .zero⟩ := ⟨_, rfl, rfl⟩

/-- **`unitDecl` is a well-formed inductive declaration over the empty environment.**
No ambient constant is needed at all: the type former's stored type is `Sort 0` and the
constructor has no parameters and no fields. -/
theorem unitDecl_WF : unitDecl.WF VEnv.empty where
  types_ne := by simp [unitDecl]
  params := trivial
  types := by
    intro T hT
    simp only [unitDecl, List.mem_cons, List.not_mem_nil, or_false] at hT
    subst hT
    exact { indices := trivial
            isType := ⟨_, .sortDF trivial trivial (.refl _)⟩
            canon := ⟨_, .sortDF trivial trivial (.refl _)⟩ }
  ctors := by
    intro env₁ he j T hT C hC
    match j, hT with
    | 0, hT =>
      simp only [unitDecl, List.getElem?_cons_zero, Option.some.injEq] at hT
      subst hT
      simp only [unitTy, List.mem_cons, List.not_mem_nil, or_false] at hC
      subst hC
      have hU : env₁.constants `Unit1 = some ⟨0, .sort .zero⟩ :=
        VEnv.addConstList_constants (cs := unitDecl.typeConsts) he
          (`Unit1, ⟨0, .sort .zero⟩) (by simp [unitDecl, unitTy, VInductDecl'.typeConsts])
      exact { params_len := rfl
              params_eq := .zero
              fields := nofun
              args_len := rfl
              args_fresh := nofun
              args_ty := .nil
              result := .constDF hU nofun nofun rfl .nil }
  isLE := by simp [unitDecl]

theorem unitDecl_add : VEnv.empty.addInduct' unitDecl = some unitEnv := unitEnv_add

/-- **A one-declaration history ending in the block**: `VEnv.WF'` reaches `unitEnv`. -/
theorem unitDecl_history : VEnv.WF' [.induct unitDecl] unitEnv :=
  .decl (.induct unitDecl_WF unitEnv_add) .empty

theorem unitDecl_noUnsafe : ∀ d ∈ [VDecl.induct unitDecl], d.noUnsafe := by
  intro d hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  subst hd; trivial

/-! ## 4. Typing derivations in `unitEnv`

Every proof-splitting decision `interp` makes inside `recType 0` and inside the ι-rule is
read off a typing derivation via `isProp_iff`/`isProof_iff`, exactly as `QuotInterp.lean`
does.  These are those derivations. -/

section Typing

variable {Γ : List VExpr} {nv : ℕ}

theorem hasType_Unit1 : unitEnv.HasType nv Γ (.const `Unit1 []) (.sort .zero) :=
  .constDF unitEnv_Unit1 nofun nofun rfl .nil

theorem hasType_mk : unitEnv.HasType nv Γ (.const `Unit1.mk []) (.const `Unit1 []) :=
  .constDF unitEnv_mk nofun nofun rfl .nil

theorem hasType_rec : unitEnv.HasType nv Γ (.const recN []) (unitDecl.recType 0) :=
  .constDF unitEnv_rec nofun nofun rfl .nil

/-- `motive : Unit1 → Prop` is a type, and **not** a proposition: its sort is
`imax 0 1`, which evaluates to `1`. -/
theorem hasType_motTy :
    unitEnv.HasType nv Γ motTy (.sort (.imax .zero (.succ .zero))) :=
  .forallEDF hasType_Unit1 (.sortDF trivial trivial (.refl _))

/-- `.bvar 0 : motTy` in `motTy :: Γ` — `motTy` is closed, so no lift appears. -/
theorem hasType_bvar0_motTy : unitEnv.HasType nv (motTy :: Γ) (.bvar 0) motTy :=
  .bvar .zero

theorem hasType_bvar1_motTy {A : VExpr} :
    unitEnv.HasType nv (A :: motTy :: Γ) (.bvar 1) motTy :=
  .bvar (.succ .zero)

theorem hasType_bvar2_motTy {A B : VExpr} :
    unitEnv.HasType nv (A :: B :: motTy :: Γ) (.bvar 2) motTy :=
  .bvar (.succ (.succ .zero))

/-- `motive mk : Prop` in `motTy :: Γ`. -/
theorem hasType_minTy : unitEnv.HasType nv (motTy :: Γ) minTy (.sort .zero) :=
  .appDF hasType_bvar0_motTy hasType_mk

/-- The same one binder in: `.app (.bvar 1) mk` is `minTy.lift`. -/
theorem hasType_minTy1 {A : VExpr} :
    unitEnv.HasType nv (A :: motTy :: Γ) (.app (.bvar 1) (.const `Unit1.mk [])) (.sort .zero) :=
  .appDF hasType_bvar1_motTy hasType_mk

theorem hasType_minTy2 {A B : VExpr} :
    unitEnv.HasType nv (A :: B :: motTy :: Γ)
      (.app (.bvar 2) (.const `Unit1.mk [])) (.sort .zero) :=
  .appDF hasType_bvar2_motTy hasType_mk

/-- `motive t : Prop` in `Unit1 :: minTy :: motTy :: Γ` — the recursor's result type. -/
theorem hasType_recBody :
    unitEnv.HasType nv (.const `Unit1 [] :: minTy :: motTy :: Γ)
      (.app (.bvar 2) (.bvar 0)) (.sort .zero) :=
  .appDF hasType_bvar2_motTy (.bvar .zero)

/-- `∀ t : Unit1, motive t : Prop`. -/
theorem hasType_recB2 :
    unitEnv.HasType nv (minTy :: motTy :: Γ)
      (.forallE (.const `Unit1 []) (.app (.bvar 2) (.bvar 0)))
      (.sort (.imax .zero .zero)) :=
  .forallEDF hasType_Unit1 hasType_recBody

/-- `∀ (m : motive mk) (t : Unit1), motive t : Prop` — the recursor type's codomain. -/
theorem hasType_recB1 :
    unitEnv.HasType nv (motTy :: Γ)
      (.forallE minTy (.forallE (.const `Unit1 []) (.app (.bvar 2) (.bvar 0))))
      (.sort (.imax .zero (.imax .zero .zero))) :=
  .forallEDF hasType_minTy hasType_recB2

/-- `∀ (m : motive mk), motive mk : Prop` — the ι-rule's type, one binder in. -/
theorem hasType_ruleB1 :
    unitEnv.HasType nv (motTy :: Γ)
      (.forallE minTy (.app (.bvar 1) (.const `Unit1.mk [])))
      (.sort (.imax .zero .zero)) :=
  .forallEDF hasType_minTy hasType_minTy1

/-- **The ι-rule's left-hand body is a proof**: `Unit1.rec motive m mk : motive mk`. -/
theorem hasType_iotaLhsBody :
    unitEnv.HasType nv (minTy :: motTy :: Γ)
      (.app (.app (.app (.const recN []) (.bvar 1)) (.bvar 0)) (.const `Unit1.mk []))
      (.app (.bvar 1) (.const `Unit1.mk [])) := by
  have h1 : unitEnv.HasType nv (minTy :: motTy :: Γ) (.const recN []) (unitDecl.recType 0) :=
    hasType_rec
  rw [unitDecl_recType] at h1
  have h2 := VEnv.IsDefEq.appDF h1 (hasType_bvar1_motTy (Γ := Γ) (A := minTy))
  have h3 := VEnv.IsDefEq.appDF h2 (VEnv.IsDefEq.bvar (A := minTy.lift) Lookup.zero)
  exact .appDF h3 hasType_mk

theorem hasType_iotaLhsLam :
    unitEnv.HasType nv (motTy :: Γ) (.lam minTy
        (.app (.app (.app (.const recN []) (.bvar 1)) (.bvar 0)) (.const `Unit1.mk [])))
      (.forallE minTy (.app (.bvar 1) (.const `Unit1.mk []))) :=
  .lamDF hasType_minTy hasType_iotaLhsBody

/-- The η-expansion's inner λ-nest, `λ motive m. m`. -/
theorem hasType_iotaLam :
    unitEnv.HasType nv Γ (.lam motTy (.lam minTy (.bvar 0)))
      (.forallE motTy (.forallE minTy (.app (.bvar 1) (.const `Unit1.mk [])))) :=
  .lamDF hasType_motTy (.lamDF hasType_minTy (.bvar .zero))

/-- **And the right-hand body too**, at the same type. -/
theorem hasType_iotaRhsBody :
    unitEnv.HasType nv (minTy :: motTy :: Γ)
      (.app (.app (.lam motTy (.lam minTy (.bvar 0))) (.bvar 1)) (.bvar 0))
      (.app (.bvar 1) (.const `Unit1.mk [])) :=
  .appDF (.appDF hasType_iotaLam hasType_bvar1_motTy) (.bvar .zero)

theorem hasType_iotaRhsLam :
    unitEnv.HasType nv (motTy :: Γ) (.lam minTy
        (.app (.app (.lam motTy (.lam minTy (.bvar 0))) (.bvar 1)) (.bvar 0)))
      (.forallE minTy (.app (.bvar 1) (.const `Unit1.mk []))) :=
  .lamDF hasType_minTy hasType_iotaRhsBody

end Typing

/-! ## 5. The oracle, and every obligation at `unitDecl`

The oracle sends `Unit1` to `{•}` — a **nonempty** set — and everything else to `•`.  So
no domain occurring anywhere below is empty, and `InductOracleWitness.lean`'s three
empty-domain lemmas are unusable here; §6 records that measurement. -/

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- **`Unit1 ↦ {•}`, everything else ↦ `•`.**  `{•}` is the *true* proposition, so `Unit1`
is inhabited in the model and `Unit1.mk`'s value `•` really is an element of it. -/
noncomputable def unitOracle (V : Type*) [SetStructure V] [Nonempty V]
    [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] : Name → List VLevel → V :=
  fun n _ ↦ if n = `Unit1 then ({pt} : V) else pt

@[simp] theorem unitOracle_Unit1 (us : List VLevel) :
    unitOracle V `Unit1 us = ({pt} : V) := by simp [unitOracle]

@[simp] theorem unitOracle_mk (us : List VLevel) : unitOracle V `Unit1.mk us = (pt : V) := by
  simp [unitOracle]

@[simp] theorem unitOracle_rec (us : List VLevel) : unitOracle V recN us = (pt : V) := by
  simp [unitOracle, recN, Lean.mkRecName]

section Obligations

variable {envF : VEnv} {nv : ℕ} (L : PropSplit envF nv) (κ : ℕ → V) (ls : List ℕ)

/-- The model data this file works at. -/
noncomputable def unitM (κ : ℕ → V) (ls : List ℕ) : ModelData V := ⟨κ, ls, unitOracle V⟩

theorem unitM_cnst : (unitM κ ls).cnst = unitOracle V := rfl

/-! ### The proof-splitting decisions

Every one is read off §4's typing derivations through `isProp_iff`/`isProof_iff`, so each
carries `hle : unitEnv ≤ envF`: the ambient environment must contain the block, exactly as
`QuotInterp.lean` requires for the four quotient constants. -/

variable (hle : unitEnv ≤ envF)

include hle in
theorem not_isProof_bvar0 (Γ : List VExpr) :
    ¬ L.IsProof (unitM κ ls) (motTy :: Γ) (.bvar 0) := by
  rw [isProof_iff hle hasType_bvar0_motTy hasType_motTy (u := .imax .zero (.succ .zero))
    ⟨trivial, trivial⟩]
  simp [VLevel.eval, Lean.Nat.imax]

include hle in
theorem not_isProof_bvar1 {A : VExpr} (Γ : List VExpr) :
    ¬ L.IsProof (unitM κ ls) (A :: motTy :: Γ) (.bvar 1) := by
  rw [isProof_iff hle hasType_bvar1_motTy hasType_motTy (u := .imax .zero (.succ .zero))
    ⟨trivial, trivial⟩]
  simp [VLevel.eval, Lean.Nat.imax]

include hle in
theorem not_isProof_bvar2 {A B : VExpr} (Γ : List VExpr) :
    ¬ L.IsProof (unitM κ ls) (A :: B :: motTy :: Γ) (.bvar 2) := by
  rw [isProof_iff hle hasType_bvar2_motTy hasType_motTy (u := .imax .zero (.succ .zero))
    ⟨trivial, trivial⟩]
  simp [VLevel.eval, Lean.Nat.imax]

include hle in
theorem isProp_recB1 (Γ : List VExpr) :
    L.IsProp (unitM κ ls) (motTy :: Γ)
      (.forallE minTy (.forallE (.const `Unit1 []) (.app (.bvar 2) (.bvar 0)))) := by
  rw [isProp_iff hle hasType_recB1 (u := .imax .zero (.imax .zero .zero))
    ⟨trivial, trivial, trivial⟩]
  simp [VLevel.eval, Lean.Nat.imax]

include hle in
theorem isProp_recB2 (Γ : List VExpr) :
    L.IsProp (unitM κ ls) (minTy :: motTy :: Γ)
      (.forallE (.const `Unit1 []) (.app (.bvar 2) (.bvar 0))) := by
  rw [isProp_iff hle hasType_recB2 (u := .imax .zero .zero) ⟨trivial, trivial⟩]
  simp [VLevel.eval, Lean.Nat.imax]

include hle in
theorem isProp_recB3 (Γ : List VExpr) :
    L.IsProp (unitM κ ls) (.const `Unit1 [] :: minTy :: motTy :: Γ)
      (.app (.bvar 2) (.bvar 0)) := by
  rw [isProp_iff hle hasType_recBody (u := .zero) trivial]
  simp [VLevel.eval]

include hle in
theorem isProp_ruleB1 (Γ : List VExpr) :
    L.IsProp (unitM κ ls) (motTy :: Γ)
      (.forallE minTy (.app (.bvar 1) (.const `Unit1.mk []))) := by
  rw [isProp_iff hle hasType_ruleB1 (u := .imax .zero .zero) ⟨trivial, trivial⟩]
  simp [VLevel.eval, Lean.Nat.imax]

include hle in
theorem isProp_ruleB2 (Γ : List VExpr) :
    L.IsProp (unitM κ ls) (minTy :: motTy :: Γ)
      (.app (.bvar 1) (.const `Unit1.mk [])) := by
  rw [isProp_iff hle hasType_minTy1 (u := .zero) trivial]
  simp [VLevel.eval]

include hle in
theorem isProof_iotaLhsLam (Γ : List VExpr) :
    L.IsProof (unitM κ ls) (motTy :: Γ) (.lam minTy
      (.app (.app (.app (.const recN []) (.bvar 1)) (.bvar 0)) (.const `Unit1.mk []))) := by
  rw [isProof_iff hle hasType_iotaLhsLam hasType_ruleB1 (u := .imax .zero .zero)
    ⟨trivial, trivial⟩]
  simp [VLevel.eval, Lean.Nat.imax]

include hle in
theorem isProof_iotaRhsLam (Γ : List VExpr) :
    L.IsProof (unitM κ ls) (motTy :: Γ) (.lam minTy
      (.app (.app (.lam motTy (.lam minTy (.bvar 0))) (.bvar 1)) (.bvar 0))) := by
  rw [isProof_iff hle hasType_iotaRhsLam hasType_ruleB1 (u := .imax .zero .zero)
    ⟨trivial, trivial⟩]
  simp [VLevel.eval, Lean.Nat.imax]

/-! ### The denotations of the two constants -/

section Interp
variable [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]

theorem interp_Unit1_eq (Γ : List VExpr) (ρ : V) :
    (interp (unitM κ ls) L Γ (.const `Unit1 [])).toFun ρ = ({pt} : V) := by
  rw [interp_const, unitM_cnst]; exact unitOracle_Unit1 _

theorem interp_mk_eq (Γ : List VExpr) (ρ : V) :
    (interp (unitM κ ls) L Γ (.const `Unit1.mk [])).toFun ρ = (pt : V) := by
  rw [interp_const, unitM_cnst]; exact unitOracle_mk _

/-! ### The motive binder is a genuine set function into `U₀`

This is the step `boxDecl` never has to take: there, the motive binder's domain is empty,
so `f` is the empty function.  Here the domain is `{•}` and `f` is one of the *two*
functions `{•} → U₀`. -/

theorem motive_app_mem_UProp {Γ : List VExpr} {ρ f : V}
    (hf : f ∈ (interp (unitM κ ls) L Γ motTy).toFun ρ) : f ‘ (pt : V) ∈ (UProp : V) := by
  rw [interp_forallE_type _ L (not_isProp_sort_zero _), mem_mkForallType_iff] at hf
  obtain ⟨hfn, hval⟩ := hf
  rw [interp_Unit1_eq L κ ls] at hfn hval
  have : IsFunction f := IsFunction.of_mem hfn
  have hpt : (pt : V) ∈ ({pt} : V) := by simp
  obtain ⟨y, hy, -⟩ := (mem_function_iff.1 hfn).2 pt hpt
  have hgraph : (⟨pt, f ‘ (pt : V)⟩ₖ : V) ∈ f := by
    rw [value_eq_of_kpair_mem hy]; exact hy
  have h := hval pt hpt (f ‘ (pt : V)) hgraph
  rw [interp_sort] at h
  simpa [VLevel.eval] using h

/-- **A true motive contains `•`**: the two facts above combine to proof irrelevance. -/
theorem pt_mem_of_mem_motive_app {Γ : List VExpr} {ρ f m : V}
    (hf : f ∈ (interp (unitM κ ls) L Γ motTy).toFun ρ) (hm : m ∈ f ‘ (pt : V)) :
    (pt : V) ∈ f ‘ (pt : V) := by
  rcases eq_empty_or_eq_true_of_mem_UProp (motive_app_mem_UProp L κ ls hf) with h | h
  · exact absurd (h ▸ hm) not_mem_empty
  · rw [h]; simp

/-! ### `⟦motive mk⟧` -/

include hle in
/-- `⟦motive mk⟧ρ = f ‘ •` where `f = ρ ‘ 0`, in the context `[motTy]`. -/
theorem interp_minTy_eq {ρ f : V} (hf : ρ ‘ ((0 : ℕ) : V) = f) :
    (interp (unitM κ ls) L [motTy] minTy).toFun ρ = f ‘ (pt : V) := by
  rw [show minTy = VExpr.app (.bvar 0) (.const `Unit1.mk []) from rfl,
    interp_app_type _ L (not_isProof_bvar0 L κ ls hle []), interp_bvar, interp_mk_eq]
  simp only [List.length_cons, List.length_nil]
  rw [hf]

include hle in
/-- The same one binder further in, in the context `[minTy, motTy]`. -/
theorem interp_minTy1_eq {ρ f : V} (hf : ρ ‘ ((0 : ℕ) : V) = f) :
    (interp (unitM κ ls) L [minTy, motTy] (.app (.bvar 1) (.const `Unit1.mk []))).toFun ρ
      = f ‘ (pt : V) := by
  rw [interp_app_type _ L (not_isProof_bvar1 L κ ls hle []), interp_bvar, interp_mk_eq]
  simp only [List.length_cons, List.length_nil]
  rw [hf]

/-! ### The three `OracleOK`s -/

/-- `Unit1 : Prop`.  Its value `{•}` is the **true** proposition, so `Unit1` is inhabited —
the point of the whole file.  Stated `Above`-free. -/
theorem mem_interp_unit_type (us : List VLevel) :
    unitOracle V `Unit1 us ∈
      (interp (unitM κ ls) L [] ((⟨0, .sort .zero⟩ : VConstant).type.instL us)).toFun ∅ := by
  rw [unitOracle_Unit1,
    show ((⟨0, .sort .zero⟩ : VConstant).type.instL us) = VExpr.sort .zero from rfl,
    interp_sort]
  exact true_mem_UProp

theorem oracleOK_unit_type :
    OracleOK L κ ls (unitOracle V) (unitOracle V) `Unit1 ⟨0, .sort .zero⟩ :=
  oracleOK_of (fun _ _ _ ↦ rfl) (fun {us} _ _ ↦ mem_interp_unit_type L κ ls us)

/-- `Unit1.mk : Unit1`.  `• ∈ {•}` — the constructor's value really is an element of the
type former's, which is only possible because the latter is nonempty. -/
theorem mem_interp_unit_mk (us : List VLevel) :
    unitOracle V `Unit1.mk us ∈
      (interp (unitM κ ls) L []
        ((⟨0, .const `Unit1 []⟩ : VConstant).type.instL us)).toFun ∅ := by
  rw [unitOracle_mk,
    show ((⟨0, .const `Unit1 []⟩ : VConstant).type.instL us) = VExpr.const `Unit1 [] from rfl]
  show (pt : V) ∈ (interp (unitM κ ls) L [] (.const `Unit1 [])).toFun ∅
  rw [interp_Unit1_eq L κ ls]
  simp

theorem oracleOK_unit_mk :
    OracleOK L κ ls (unitOracle V) (unitOracle V) `Unit1.mk ⟨0, .const `Unit1 []⟩ :=
  oracleOK_of (fun _ _ _ ↦ rfl) (fun {us} _ _ ↦ mem_interp_unit_mk L κ ls us)

include hle in
/-- **`Unit1.rec`**, the field that `boxDecl` could only get from an empty domain.  Here
all three binder domains — `Unit1 → Prop`, `motive mk` and `Unit1` — are inhabited, and the
membership is the impredicative `∀` three times over, closed by proof irrelevance in `U₀`. -/
theorem pt_mem_interp_unit_recType :
    (pt : V) ∈ (interp (unitM κ ls) L [] ((unitDecl.recType 0).instL [])).toFun ∅ := by
  rw [unitDecl_recType]
  show (pt : V) ∈ (interp (unitM κ ls) L []
    (.forallE motTy (.forallE minTy
      (.forallE (.const `Unit1 []) (.app (.bvar 2) (.bvar 0)))))).toFun ∅
  have h0 : (∅ : V) ∈ interpCtx (unitM κ ls) L [] := by rw [interpCtx_nil]; simp
  refine (mem_interp_forallE_prop_iff (unitM κ ls) L
    (isProp_recB1 L κ ls hle [])).2 ⟨rfl, fun f hf ↦ ?_⟩
  have hf0 : (snoc (∅ : V) f) ‘ ((0 : ℕ) : V) = f :=
    snoc_value_at_len (Γ := []) (unitM κ ls) L h0
  have h1 : snoc (∅ : V) f ∈ interpCtx (unitM κ ls) L [motTy] :=
    (mem_interpCtx_cons (unitM κ ls) L).mpr ⟨∅, h0, f, hf, rfl⟩
  have hmin : (interp (unitM κ ls) L [motTy] minTy).toFun (snoc (∅ : V) f) = f ‘ (pt : V) :=
    interp_minTy_eq L κ ls hle hf0
  refine (mem_interp_forallE_prop_iff (unitM κ ls) L
    (isProp_recB2 L κ ls hle [])).2 ⟨rfl, fun m hm ↦ ?_⟩
  rw [hmin] at hm
  have h2 : snoc (snoc (∅ : V) f) m ∈ interpCtx (unitM κ ls) L [minTy, motTy] :=
    (mem_interpCtx_cons (unitM κ ls) L).mpr ⟨snoc ∅ f, h1, m, by rw [hmin]; exact hm, rfl⟩
  refine (mem_interp_forallE_prop_iff (unitM κ ls) L
    (isProp_recB3 L κ ls hle [])).2 ⟨rfl, fun t ht ↦ ?_⟩
  rw [interp_Unit1_eq L κ ls] at ht
  obtain rfl : t = (pt : V) := mem_singleton_iff.mp ht
  rw [interp_app_type (unitM κ ls) L (not_isProof_bvar2 L κ ls hle []),
    interp_bvar, interp_bvar]
  have e0 : (snoc (snoc (snoc (∅ : V) f) m) pt) ‘ ((0 : ℕ) : V) = f :=
    ((snoc_value_of_lt (Γ := [minTy, motTy]) (unitM κ ls) L h2 (j := 0) (by simp)).trans
      (snoc_value_of_lt (Γ := [motTy]) (unitM κ ls) L h1 (j := 0) (by simp))).trans hf0
  have e2 : (snoc (snoc (snoc (∅ : V) f) m) pt) ‘ ((2 : ℕ) : V) = pt :=
    snoc_value_at_len (Γ := [minTy, motTy]) (unitM κ ls) L h2
  simp only [List.length_cons, List.length_nil]
  rw [show (2 + 1 - 1 - 2 : ℕ) = 0 from rfl, show (2 + 1 - 1 - 0 : ℕ) = 2 from rfl, e0, e2]
  exact pt_mem_of_mem_motive_app L κ ls hf hm

include hle in
theorem oracleOK_unit_rec :
    OracleOK L κ ls (unitOracle V) (unitOracle V) recN ⟨0, unitDecl.recType 0⟩ := by
  refine oracleOK_of (fun _ _ _ ↦ rfl) (fun {us} _ hlen ↦ ?_)
  obtain rfl : us = [] := List.eq_nil_of_length_eq_zero hlen
  rw [unitOracle_rec]
  exact pt_mem_interp_unit_recType L κ ls hle

/-! ### The `rules` field: the ι-rule `Unit1.rec motive m mk ≡ m`

Both sides are λ-nests whose body is a **proof** (its type `motive mk` is a proposition), so
the `lam` clause returns `•` on both, and the equation is `pt = pt`.  That is not the
empty-domain collapse: the domains here are inhabited, and the two sides are equal because
proofs are irrelevant in the model, which is the honest reason. -/

include hle in
theorem interp_unitRule_lhs :
    (interp (unitM κ ls) L [] ((unitDecl.iotaRule 0 0 unitCtor).lhs.instL [])).toFun ∅
      = (pt : V) := by
  rw [unitRule_lhs]
  show (interp (unitM κ ls) L [] (VExpr.lam motTy (.lam minTy
    (.app (.app (.app (.const recN []) (.bvar 1)) (.bvar 0)) (.const `Unit1.mk []))))).toFun ∅
      = pt
  exact interp_lam_proof (unitM κ ls) L (isProof_iotaLhsLam L κ ls hle []) ∅

include hle in
theorem interp_unitRule_rhs :
    (interp (unitM κ ls) L [] ((unitDecl.iotaRule 0 0 unitCtor).rhs.instL [])).toFun ∅
      = (pt : V) := by
  rw [unitRule_rhs]
  show (interp (unitM κ ls) L [] (VExpr.lam motTy (.lam minTy
    (.app (.app (.lam motTy (.lam minTy (.bvar 0))) (.bvar 1)) (.bvar 0))))).toFun ∅ = pt
  exact interp_lam_proof (unitM κ ls) L (isProof_iotaRhsLam L κ ls hle []) ∅

include hle in
/-- `•` inhabits the ι-rule's type `∀ (motive : Unit1 → Prop) (m : motive mk), motive mk`.
Two impredicative `∀`s over **inhabited** domains, closed by `U₀`-irrelevance. -/
theorem pt_mem_interp_unitRule_type :
    (pt : V) ∈
      (interp (unitM κ ls) L [] ((unitDecl.iotaRule 0 0 unitCtor).type.instL [])).toFun ∅ := by
  rw [unitRule_type]
  show (pt : V) ∈ (interp (unitM κ ls) L []
    (.forallE motTy (.forallE minTy (.app (.bvar 1) (.const `Unit1.mk []))))).toFun ∅
  have h0 : (∅ : V) ∈ interpCtx (unitM κ ls) L [] := by rw [interpCtx_nil]; simp
  refine (mem_interp_forallE_prop_iff (unitM κ ls) L
    (isProp_ruleB1 L κ ls hle [])).2 ⟨rfl, fun f hf ↦ ?_⟩
  have hf0 : (snoc (∅ : V) f) ‘ ((0 : ℕ) : V) = f :=
    snoc_value_at_len (Γ := []) (unitM κ ls) L h0
  have h1 : snoc (∅ : V) f ∈ interpCtx (unitM κ ls) L [motTy] :=
    (mem_interpCtx_cons (unitM κ ls) L).mpr ⟨∅, h0, f, hf, rfl⟩
  have hmin : (interp (unitM κ ls) L [motTy] minTy).toFun (snoc (∅ : V) f) = f ‘ (pt : V) :=
    interp_minTy_eq L κ ls hle hf0
  refine (mem_interp_forallE_prop_iff (unitM κ ls) L
    (isProp_ruleB2 L κ ls hle [])).2 ⟨rfl, fun m hm ↦ ?_⟩
  rw [hmin] at hm
  have e0 : (snoc (snoc (∅ : V) f) m) ‘ ((0 : ℕ) : V) = f :=
    (snoc_value_of_lt (Γ := [motTy]) (unitM κ ls) L h1 (j := 0) (by simp)).trans hf0
  rw [interp_minTy1_eq L κ ls hle e0]
  exact pt_mem_of_mem_motive_app L κ ls hf hm

include hle in
/-- **The `rules` field of the residual.** -/
theorem defEqOK_unitRule : DefEqOK L (unitM κ ls) (unitDecl.iotaRule 0 0 unitCtor) := by
  intro us _ hlen
  obtain rfl : us = [] := List.eq_nil_of_length_eq_zero (unitRule_uvars ▸ hlen)
  refine ⟨Above.pure ?_, Above.pure ?_⟩
  · rw [interp_unitRule_lhs L κ ls hle, interp_unitRule_rhs L κ ls hle]
  · rw [interp_unitRule_lhs L κ ls hle]
    exact pt_mem_interp_unitRule_type L κ ls hle

/-! ## 6. The residual, discharged -/

include hle in
/-- **The `consts` field, all three constants.** -/
theorem inductOracleOK_consts_unit :
    ∀ p ∈ unitDecl.allConsts, OracleOK L κ ls (unitOracle V) (unitOracle V) p.1 p.2 := by
  intro p hp
  rw [unitDecl_allConsts] at hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  obtain rfl | rfl | rfl := hp
  · exact oracleOK_unit_type L κ ls
  · exact oracleOK_unit_mk L κ ls
  · exact oracleOK_unit_rec L κ ls hle

include hle in
theorem inductOracleOK_rules_unit :
    ∀ df ∈ unitDecl.iotaRules, DefEqOK L (unitM κ ls) df := by
  intro df hdf
  rw [unitDecl_iotaRules] at hdf
  simp only [List.mem_singleton] at hdf
  subst hdf
  exact defEqOK_unitRule L κ ls hle

include hle in
/-- **`InductOracleOK` at a `VInductDecl'.WF`, `VEnv.WF'`-reachable block whose declared
type formers and constructors have *no* empty domain anywhere.**  This is the cell
`InductOracleWitness.lean`'s docstring left open. -/
theorem inductOracleOK_unit :
    InductOracleOK L κ ls (unitOracle V) (unitOracle V) unitDecl :=
  ⟨inductOracleOK_consts_unit L κ ls hle, inductOracleOK_rules_unit L κ ls hle⟩

/-! ### `OracleFits` for the one-declaration list -/

theorem cnstOf_unit : cnstOf L κ ls (unitOracle V) [.induct unitDecl] = unitOracle V := by
  show oracleExtend (unitOracle V) unitDecl.allNames (cnstOf L κ ls (unitOracle V) []) = _
  rw [show cnstOf L κ ls (unitOracle V) ([] : List VDecl) = fun _ _ ↦ (∅ : V) from rfl,
    unitDecl_allNames]
  funext m us
  show (oracleExtend (unitOracle V) [`Unit1, `Unit1.mk, recN] (fun _ _ ↦ (∅ : V))) m us = _
  simp only [oracleExtend, cnstUpdate]
  by_cases h1 : m = recN
  · subst h1; simp [unitOracle, recN, Lean.mkRecName]
  by_cases h2 : m = `Unit1.mk
  · subst h2; simp [unitOracle, h1]
  by_cases h3 : m = `Unit1
  · subst h3; simp [unitOracle, h1, h2]
  simp only [if_neg h1, if_neg h2, if_neg h3]
  rw [show unitOracle V m us = pt from by simp [unitOracle, h3]]
  rfl

include hle in
/-- **`OracleFits` for `[.induct unitDecl]`.**  The whole list, with the residual's only
step discharged. -/
theorem oracleFits_unit : OracleFits L κ ls (unitOracle V) [.induct unitDecl] := by
  refine ⟨?_, trivial⟩
  show InductOracleOK L κ ls (unitOracle V)
    (cnstOf L κ ls (unitOracle V) [.induct unitDecl]) unitDecl
  rw [cnstOf_unit]
  exact inductOracleOK_unit L κ ls hle

/-! ## 7. The measurement: **nothing here is empty, and nothing here is vacuous**

`InductOracleWitness.lean`'s bound is met *because* `⟦Ext⟧ = ∅`.  This section is the
corresponding audit for `unitDecl`, and it is the reason the file exists. -/

/-- `unitDecl` has **no** parameter and **no** index telescope, so there is no domain for
the empty-domain mechanism to act on.  (Contrast `boxDecl.params = [.const `Ext []]`.) -/
theorem unitDecl_params_nil : unitDecl.params = [] := rfl
theorem unitTy_indices_nil : unitTy.indices = [] := rfl

/-- **The type former's denotation is nonempty**, so `Unit1` is an inhabited proposition and
`interp_lam_of_empty_dom` / `pt_mem_interp_forallE_of_empty_dom` do not apply to any binder
whose domain is `Unit1`. -/
theorem interp_Unit1_ne_empty (Γ : List VExpr) (ρ : V) :
    (interp (unitM κ ls) L Γ (.const `Unit1 [])).toFun ρ ≠ (∅ : V) := by
  rw [interp_Unit1_eq L κ ls]
  intro h
  exact absurd (h ▸ (by simp : (pt : V) ∈ ({pt} : V))) not_mem_empty

/-- **The motive binder's domain is nonempty, and it contains a *true* motive.**  This is
what makes `oracleOK_unit_rec`'s two inner quantifiers non-vacuous: there is an `f` in the
domain for which the minor-premise domain `f ‘ •` is itself nonempty. -/
theorem exists_true_motive :
    ∃ f ∈ (interp (unitM κ ls) L [] motTy).toFun ∅, f ‘ (pt : V) = ({pt} : V) := by
  rw [interp_forallE_type (unitM κ ls) L (not_isProp_sort_zero _)]
  refine ⟨mkLam (interp (unitM κ ls) L [] (.const `Unit1 [])).toFun
      (interp (unitM κ ls) L [] (.const `Unit1 [])).definable
      (fun _ _ ↦ ({pt} : V)) (by definability) ∅, ?_, ?_⟩
  · refine mkLam_mem_mkForallType (fun v hv ↦ ?_)
    rw [interp_sort]
    simp [VLevel.eval]
  · refine mkLam_value ?_
    rw [interp_Unit1_eq L κ ls]; simp

include hle in
/-- …and therefore **the minor-premise binder's domain is nonempty too**, at that `f`.  So
all three of the recursor's binder domains — motive, minor premise, major premise — are
inhabited, which is exactly the property `InductOracleWitness.lean` says its bound lacks. -/
theorem exists_nonempty_minor_domain :
    ∃ f ∈ (interp (unitM κ ls) L [] motTy).toFun ∅,
      (pt : V) ∈ (interp (unitM κ ls) L [motTy] minTy).toFun (snoc ∅ f) := by
  obtain ⟨f, hf, hfv⟩ := exists_true_motive L κ ls
  have h0 : (∅ : V) ∈ interpCtx (unitM κ ls) L [] := by rw [interpCtx_nil]; simp
  refine ⟨f, hf, ?_⟩
  rw [interp_minTy_eq L κ ls hle (snoc_value_at_len (Γ := []) (unitM κ ls) L h0), hfv]
  simp

/-! ### The obligations, `Above`-free

Every field above is proved through `Above.pure`, so each obligation holds at an
**arbitrary** `κ` with no chain-length threshold.  `Above M P` is `∃ m, IsInaccessibleChain
m M.κ → P`, hence trivially true at a `κ` that is not a chain of every finite length; a
bound that went through the wrapper would therefore say nothing.  These four restate the
obligations with the wrapper stripped. -/

include hle in
/-- **The `consts` obligation, `Above`-free**, at an arbitrary `κ` with no chain hypothesis
anywhere.  (The recursor's entry is stated at `us = []`, which is the only length its
`uvars = 0` admits.) -/
theorem mem_interp_consts_unit (us : List VLevel) :
    (∀ vs : List VLevel, unitOracle V `Unit1 vs ∈
        (interp (unitM κ ls) L [] ((VExpr.sort .zero).instL vs)).toFun ∅) ∧
    (∀ vs : List VLevel, unitOracle V `Unit1.mk vs ∈
        (interp (unitM κ ls) L [] ((VExpr.const `Unit1 []).instL vs)).toFun ∅) ∧
    unitOracle V recN us ∈
        (interp (unitM κ ls) L [] ((unitDecl.recType 0).instL [])).toFun ∅ :=
  ⟨fun vs ↦ mem_interp_unit_type L κ ls vs, fun vs ↦ mem_interp_unit_mk L κ ls vs,
   by rw [unitOracle_rec]; exact pt_mem_interp_unit_recType L κ ls hle⟩

include hle in
/-- The `rules` obligation with the wrapper stripped: the two sides are **equal**, and their
common value lies in the equated type. -/
theorem defEq_rules_unit :
    (interp (unitM κ ls) L [] ((unitDecl.iotaRule 0 0 unitCtor).lhs.instL [])).toFun ∅
      = (interp (unitM κ ls) L [] ((unitDecl.iotaRule 0 0 unitCtor).rhs.instL [])).toFun ∅ ∧
    (interp (unitM κ ls) L [] ((unitDecl.iotaRule 0 0 unitCtor).lhs.instL [])).toFun ∅
      ∈ (interp (unitM κ ls) L [] ((unitDecl.iotaRule 0 0 unitCtor).type.instL [])).toFun ∅ :=
  ⟨by rw [interp_unitRule_lhs L κ ls hle, interp_unitRule_rhs L κ ls hle],
   by rw [interp_unitRule_lhs L κ ls hle]; exact pt_mem_interp_unitRule_type L κ ls hle⟩

/-! ### The other direction, field by field

`CnstRecursion.lean` has the `consts` cell's negative bound
(`not_oracleOK_falseProp`, `not_inductOracleOK_falseProp`).  `InductOracleAudit.lean` §5's
`rules` cell reads "open — no ι-rule of a `WF` block is known to be refutable".  The theorem
below does **not** close that cell as worded, and the module docstring says why the wording is
probably unachievable.

Read it precisely.  `not_defEqOK_falseType` refutes `DefEqOK` — the *body* of the `rules`
field — at a `VDefEq` whose equated type is uninhabited, so the field is not a triviality
that any model satisfies for free.  It does **not** exhibit a `VInductDecl'` one of whose
`iotaRules` has that type: `iotaRules` is derived from the block, so such a `D` is not
freely constructible, and no claim about one is made here. -/

theorem not_defEqOK_falseType (hκ : ∀ m : ℕ, IsInaccessibleChain m κ) (e : VExpr) :
    ¬ DefEqOK L (unitM κ ls) ⟨0, e, e, falseProp⟩ := by
  intro h
  obtain ⟨m, hm⟩ := (h (us := []) (by simp) rfl).2
  have hv := hm (hκ m)
  rw [show (VDefEq.mk 0 e e falseProp).type.instL [] = falseProp from rfl,
    interp_falseProp] at hv
  simp at hv

/-- And `unitDecl`'s own `rules` field is not vacuous the other way either: the block has
**one** ι-rule, so `inductOracleOK_rules_unit` is a statement about a nonempty list.
(`inductOracleOK_empty` in `CnstRecursion.lean` is the block with none.) -/
theorem unitDecl_iotaRules_ne_nil : unitDecl.iotaRules ≠ [] := by
  rw [unitDecl_iotaRules]; exact List.cons_ne_nil _ _

/-- …and its `consts` list has all three entries, so `inductOracleOK_consts_unit` is not a
statement about the empty list either. -/
theorem unitDecl_allConsts_length : unitDecl.allConsts.length = 3 := rfl

/-! ### The `hle` hypothesis is exactly what the consumer supplies

Every theorem in §5–§6 that reads a proof-splitting decision carries
`hle : unitEnv ≤ envF`.  That is **not** a strengthening of the residual:
`coherentOn_cnstOf` (`CnstRecursion.lean:553`) threads `env ≤ envF` through every
declaration step, and at `ds = [.induct unitDecl]` that `env` *is* `unitEnv`.  It is the same
hypothesis `QuotInterp.lean` needs for the four quotient constants, and it is discharged the
same way. -/

theorem eq_unitEnv_of_wf' {env : VEnv} (h : VEnv.WF' [.induct unitDecl] env) :
    env = unitEnv := by
  obtain ⟨env₀, hd, hds⟩ := wf'_cons_inv h
  cases hds
  cases hd with
  | induct _ hadd => exact Option.some_injective _ (unitEnv_add.symm.trans hadd).symm

/-- **The residual's `.induct` step, discharged from the recursion's own hypotheses.**  No
`hle` in sight: `VEnv.WF'` and `env ≤ envF` are what `coherentOn_cnstOf` already has at this
step, and they are enough. -/
theorem oracleFits_unit_at_consumer {env : VEnv}
    (hwf : VEnv.WF' [VDecl.induct unitDecl] env) (hle' : env ≤ envF) :
    OracleFits L κ ls (unitOracle V) [.induct unitDecl] :=
  oracleFits_unit L κ ls (eq_unitEnv_of_wf' hwf ▸ hle')

/-! ## 9. What this does **not** show: large elimination

`unitDecl.isLE = false`, so its recursor eliminates only into `Prop`, and *that* is why every
step above is the impredicative `∀` and the oracle can hand `Unit1.rec` the value `•`.  Real
Lean declares the **large** eliminator for `inductive Unit1 : Prop | mk` — it is a
subsingleton — and `VInductDecl'.WF` permits it: `LECond` holds for this block
(`unitDeclLE_LECond`), vacuously, because the constructor has no fields.

At `isLE := true` the recursor gains a universe parameter and its result type becomes
`Sort (param 0)`.  For an instantiation with `u.eval ls ≠ 0` the innermost binder is no longer
propositional, so `interp` takes the `mkForallType` branch — and `•` is then **not** a legal
value (`pt_not_mem_mkForallType_of_nonempty`, since the domain `{•}` is nonempty).  The oracle
must supply a genuine three-layer `mkLam` nest, and the ι-rule must β-compute through it.
*That* is the case `SetModel/IndInterp.lean`'s machinery is for; it is open.

So the frontier this file moves is: from "`consts` at a `WF` block with an inhabited
parameter/index domain" to "`consts` at a `WF` block with a **large** eliminator". -/

/-- `inductive Unit1 : Prop | mk` with the large eliminator — the block Lean really declares. -/
def unitDeclLE : VInductDecl' := { unitDecl with isLE := true }

theorem unitDeclLE_LECond : unitDeclLE.LECond :=
  Or.inr ⟨unitTy, rfl, Or.inr ⟨unitCtor, rfl, nofun⟩⟩

theorem unitDeclLE_recUvars : unitDeclLE.recUvars = 1 := rfl

theorem unitDeclLE_elimLvl : unitDeclLE.elimLvl = .param 0 := rfl

/-- The large recursor's type: the motive now lands in `Sort u` for a *fresh* `u`. -/
theorem unitDeclLE_recType :
    unitDeclLE.recType 0 =
      .forallE (.forallE (.const `Unit1 []) (.sort (.param 0)))
        (.forallE minTy (.forallE (.const `Unit1 []) (.app (.bvar 2) (.bvar 0)))) := rfl

/-- **`•` cannot be the value of a `∀` over a nonempty domain that takes the type branch.**
This is precisely what blocks reusing §5's oracle at `unitDeclLE`: for `u.eval ls ≠ 0` the
recursor's type takes `mkForallType`, and `pt = ∅` is not a function on `{•}`. -/
theorem pt_not_mem_mkForallType_of_nonempty {G : V → V} {hG : ℒₛₑₜ-function₁[V] G}
    {F : V → V → V} {hF : ℒₛₑₜ-function₂[V] F} {ρ x : V} (hx : x ∈ G ρ) :
    (pt : V) ∉ mkForallType G hG F hF ρ := by
  intro h
  obtain ⟨hfn, -⟩ := mem_mkForallType_iff.mp h
  obtain ⟨y, hy, -⟩ := (mem_function_iff.1 hfn).2 x hx
  exact absurd hy not_mem_empty

end Interp

end Obligations

/-! ## 8. Axiom audit -/

#print axioms Lean4Lean.SetModel.UnitAudit.unitEnv_add
#print axioms Lean4Lean.SetModel.UnitAudit.unitDecl_WF
#print axioms Lean4Lean.SetModel.UnitAudit.unitDecl_history
#print axioms Lean4Lean.SetModel.UnitAudit.inductOracleOK_unit
#print axioms Lean4Lean.SetModel.UnitAudit.oracleFits_unit
#print axioms Lean4Lean.SetModel.UnitAudit.mem_interp_consts_unit
#print axioms Lean4Lean.SetModel.UnitAudit.defEq_rules_unit
#print axioms Lean4Lean.SetModel.UnitAudit.exists_true_motive
#print axioms Lean4Lean.SetModel.UnitAudit.exists_nonempty_minor_domain
#print axioms Lean4Lean.SetModel.UnitAudit.interp_Unit1_ne_empty
#print axioms Lean4Lean.SetModel.UnitAudit.not_defEqOK_falseType
#print axioms Lean4Lean.SetModel.UnitAudit.oracleFits_unit_at_consumer
#print axioms Lean4Lean.SetModel.UnitAudit.unitDeclLE_LECond
#print axioms Lean4Lean.SetModel.UnitAudit.pt_not_mem_mkForallType_of_nonempty

end Lean4Lean.SetModel.UnitAudit
