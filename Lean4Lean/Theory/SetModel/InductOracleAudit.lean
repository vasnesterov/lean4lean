import Lean4Lean.Theory.SetModel.CnstRecursion

/-!
# The `.induct` residual's first field was **false**, and the repair has landed

`SetModel/CnstRecursion.lean` reduces the whole declaration-list recursion to one
residual at `.induct` steps.  Until 2026-08-31 that residual carried three fields, the
first of which was

    staged : ∀ {env env' : VEnv}, env.addInduct' D = some env' → StagedOcc env D.allConsts

and **that field is false at ordinary blocks**.  `addInduct'` performs three
`addConstList`s and one `addDefEq` fold and **checks no types at all**, so
`VEnv.empty.addInduct' D` succeeds for every `D` whose names are pairwise distinct
(`VEnv.addInduct'_eq_some_iff`).  Instantiating the `∀ env` at `VEnv.empty` therefore
forces `StagedOcc VEnv.empty D.allConsts`, i.e.

> every type the block declares mentions **no constant outside the block** — and for the
> *first* type former, no constant at all, since no block name is available yet.

`VInductDecl'.WF` demands nothing of the sort: it asks each declared type to be a type
*in the environment the block is declared over*, which is exactly where the block's
external constants live.  So the field was unsatisfiable at every block one of whose
declared types mentions an ambient constant — `inductive Box (e : Ext) : Prop | mk : Box e`
over an environment holding `axiom Ext : Prop` is enough, and `boxDecl` below is that
block, with `VDecl.WF` and a **two-declaration `VEnv.WF'` history** machine-checked.

## What this file now is

The repair is in `CnstRecursion.lean`: `stagedOcc_allConsts` (§4b there) discharges
`StagedOcc env D.allConsts` at the block's own environment from `env.Ordered` and
`D.WF env` alone, so the field is **deleted** and `coherentOn_cnstOf`'s `.induct` case
calls the theorem instead.  There is **one** recursion, not two; the `InductOracleOK₂` /
`OracleFits₂` / `coherentOn_cnstOf₂` duplicates this file used to carry are retired.

What remains here is the *measurement*, which does not go stale:

1. `StagedField` — the deleted field, as a standalone predicate, so the refutation stays
   machine-checked after the field itself is gone.
2. `not_stagedField_of_head_const` — the general refutation; `not_stagedField_boxDecl`
   its instance at a certified block.
3. `stagedOcc_boxDecl` — the *same* condition at the environment the block is actually
   declared over **holds**.  So the defect was entirely the field's `∀ env`, never
   `StagedOcc` itself.
4. `coherentOn_boxDecl_history_of` — the recursion instantiated at `boxDecl`'s history:
   what is left there is exactly two inhabitation obligations, with **no** occurrence
   condition.  This is the sense in which the `.induct` case is no longer vacuous at a
   list the soundness induction actually visits.

`docs/vacuity-ledger.md` rows 11 and 11a record the defect and the fact that row 11's
own "bounded both ways" claim missed it: the positive bound `inductOracleOK_empty` is at
the block with no type formers, whose `allConsts` is `[]` (`empty_block_allConsts`), so
its `staged` field was `True`.  **A two-way bound must be checked field by field.**
-/

namespace Lean4Lean.SetModel

open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-! ## 1. The deleted field, named

Keeping it as a definition rather than as a field of `InductOracleOK` is what lets the
refutation below stay checked after the repair.  Nothing in the main path mentions it. -/

/-- **The field that was deleted from `InductOracleOK`.**  Note the `∀ env`: nothing pins
the environment, which is the whole defect (`Theory/SetModel/CoherentWitness.lean:109`
names the signature). -/
def StagedField (D : VInductDecl') : Prop :=
  ∀ {env env' : VEnv}, env.addInduct' D = some env' → StagedOcc env D.allConsts

namespace SetModelAudit

/-- **`addInduct'` succeeds at the empty environment for any block it succeeds at anywhere.**
The three `addConstList`s check name freshness; nothing checks a type. -/
theorem addInduct'_empty {env env' : VEnv} {D : VInductDecl'}
    (he : env.addInduct' D = some env') : ∃ e, VEnv.empty.addInduct' D = some e :=
  VEnv.addInduct'_eq_some_iff.2 ⟨fun _ _ ↦ rfl, (VEnv.addInduct'_eq_some_iff.1 ⟨_, he⟩).2⟩

@[simp] theorem empty_contains {n : Name} : ¬ VEnv.empty.contains n := nofun

end SetModelAudit

/-! ## 2. The refutation, in general form -/

/-- **The field is a demand at the empty environment.**  It quantifies over *all* `env`,
and `addInduct'` never inspects a type, so it is instantiable at `VEnv.empty` for any
block that is declarable anywhere. -/
theorem StagedField.stagedOcc_empty {D : VInductDecl'} {env env' : VEnv} (h : StagedField D)
    (he : env.addInduct' D = some env') : StagedOcc VEnv.empty D.allConsts :=
  h (SetModelAudit.addInduct'_empty he).choose_spec

/-- Consequently **the block's first type former must mention no constant at all** — not
even one of the ambient environment, which is where a real block's external constants
live.  `VIndType.WF.isType` asks only that `T.type` be a type *over `env`*. -/
theorem stagedOcc_empty_head {D : VInductDecl'} {T : VIndType} {Ts : List VIndType}
    (hT : D.types = T :: Ts) (h : StagedOcc VEnv.empty D.allConsts) :
    T.type.ConstsIn fun _ ↦ False := by
  have : D.allConsts = (T.name, ⟨D.uvars, T.type⟩) ::
      (Ts.map fun T => (T.name, (⟨D.uvars, T.type⟩ : VConstant)) ) ++
        (D.ctorConsts ++ D.recConsts) := by
    simp [VInductDecl'.allConsts, VInductDecl'.typeConsts, hT]
  rw [this] at h
  exact h.1.mono fun _ hn ↦ SetModelAudit.empty_contains hn

/-- **The refutation.**  A block whose first type former's stored type mentions any
constant has no `StagedField` — hence had no `InductOracleOK`, at any oracle, any
assignment, any split, before the field was deleted. -/
theorem not_stagedField_of_head_const {D : VInductDecl'} {T : VIndType} {Ts : List VIndType}
    {env env' : VEnv} (hT : D.types = T :: Ts) (he : env.addInduct' D = some env')
    (hc : ¬ T.type.ConstsIn fun _ ↦ False) : ¬ StagedField D :=
  fun h ↦ hc (stagedOcc_empty_head hT (h.stagedOcc_empty he))

/-! ## 3. The witness: an ordinary block the deleted field rejected

`inductive Box (e : Ext) : Prop | mk : Box e` over an environment holding
`axiom Ext : Prop`.  Nothing exotic: one parameter, one type former, one constructor with
**no fields**.  The only feature that matters is that the parameter's type is a constant
of the ambient environment, which is the normal situation for every inductive that is not
primitive.

`Ext` is a `Prop` rather than a `Type` only to keep the `WF` witness to fifteen lines
(`VIndCtor.WF.result` is then a single `appDF`).  The refutation itself is
`not_stagedField_of_head_const`, which is general: it covers `Fin : Nat → Type`, `Vector`,
and every parameterised inductive whose parameter or index types name an ambient
constant. -/

namespace SetModelAudit

/-- `axiom Ext : Prop`. -/
def extAx : VConstVal := { name := `Ext, uvars := 0, type := .sort .zero }

/-- The environment after that one axiom, written in the shape `addConst` produces. -/
def extEnv : VEnv where
  constants n := if `Ext = n then some ⟨0, .sort .zero⟩ else none
  defeqs _ := False

theorem extEnv_add : VEnv.empty.addConst extAx.name extAx.toVConstant = some extEnv := rfl

theorem extEnv_Ext : extEnv.constants `Ext = some ⟨0, .sort .zero⟩ := rfl

theorem extAx_WF : extAx.toVConstant.WF VEnv.empty :=
  ⟨_, .sortDF trivial trivial (.refl _)⟩

/-- The one axiom is a well-formed declaration step. -/
theorem extAx_decl_WF : VDecl.WF VEnv.empty (.axiom extAx) extEnv :=
  .axiom extAx_WF extEnv_add

theorem extEnv_ordered : extEnv.Ordered := .const .empty extAx_WF extEnv_add

/-- `inductive Box (e : Ext) : Prop | mk : Box e`. -/
def boxDecl : VInductDecl' where
  uvars := 0
  params := [.const `Ext []]
  lvl := .zero
  isLE := false
  types := [{ name := `Box, type := .forallE (.const `Ext []) (.sort .zero), indices := [],
              ctors := [{ name := `Box.mk, params := [.const `Ext []], fields := [],
                          args := [] }] }]

theorem boxDecl_allConsts :
    boxDecl.allConsts =
      [(`Box, ⟨0, .forallE (.const `Ext []) (.sort .zero)⟩),
       (`Box.mk, ⟨0, .forallE (.const `Ext []) (.app (.const `Box []) (.bvar 0))⟩),
       (Lean.mkRecName `Box, ⟨0, boxDecl.recType 0⟩)] := rfl

/-- `Ext` occurs in the type former's stored type — this is the whole of the refutation. -/
theorem boxDecl_head_const :
    ¬ (VExpr.forallE (.const `Ext []) (.sort .zero)).ConstsIn fun _ ↦ False := fun h ↦ h.1

theorem boxDecl_names : boxDecl.allNames = [`Box, `Box.mk, Lean.mkRecName `Box] := rfl

/-- The block is declarable over `extEnv`: its three names are fresh and distinct. -/
theorem boxDecl_add : ∃ env₁, extEnv.addInduct' boxDecl = some env₁ := by
  refine VEnv.addInduct'_eq_some_iff.2 ⟨?_, ?_⟩
  · rw [boxDecl_names]
    intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    obtain rfl | rfl | rfl := hn <;> rfl
  · rw [boxDecl_names]; decide

theorem extEnv_Box_none : extEnv.constants `Box = none := rfl

/-- The type constant, in the staged environment. -/
theorem boxDecl_Box_staged {env₁ : VEnv} (he : extEnv.addIndTypes boxDecl = some env₁) :
    env₁.constants `Box = some ⟨0, .forallE (.const `Ext []) (.sort .zero)⟩ :=
  VEnv.addConstList_constants (cs := boxDecl.typeConsts) he
    (`Box, ⟨0, .forallE (.const `Ext []) (.sort .zero)⟩) (by simp [boxDecl,
      VInductDecl'.typeConsts])

theorem boxDecl_Ext_staged {env₁ : VEnv} (he : extEnv.addIndTypes boxDecl = some env₁) :
    env₁.constants `Ext = some ⟨0, .sort .zero⟩ :=
  (VEnv.addConstList_le (cs := boxDecl.typeConsts) he).constants extEnv_Ext

/-- **`boxDecl` is a well-formed inductive declaration over `extEnv`.** -/
theorem boxDecl_WF : boxDecl.WF extEnv where
  types_ne := by simp [boxDecl]
  params := ⟨trivial, _, .constDF extEnv_Ext nofun nofun rfl .nil⟩
  types := by
    intro T hT
    simp only [boxDecl, List.mem_cons, List.not_mem_nil, or_false] at hT
    subst hT
    exact { indices := ⟨trivial, _, .constDF extEnv_Ext nofun nofun rfl .nil⟩
            isType := ⟨_, .forallEDF (.constDF extEnv_Ext nofun nofun rfl .nil)
              (.sortDF trivial trivial (.refl _))⟩
            canon := ⟨_, .forallEDF (.constDF extEnv_Ext nofun nofun rfl .nil)
              (.sortDF trivial trivial (.refl _))⟩ }
  ctors := by
    intro env₁ he j T hT C hC
    match j, hT with
    | 0, hT =>
      simp only [boxDecl, List.getElem?_cons_zero, Option.some.injEq] at hT
      subst hT
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
      subst hC
      have hext : env₁.IsDefEq 0 [] (.const `Ext []) (.const `Ext []) (.sort .zero) :=
        .constDF (boxDecl_Ext_staged he) nofun nofun rfl .nil
      have hbox : env₁.HasType 0 [VExpr.const `Ext []] (.const `Box [])
          (.forallE (.const `Ext []) (.sort .zero)) :=
        .constDF (boxDecl_Box_staged he) nofun nofun rfl .nil
      exact { params_len := rfl
              params_eq := .succ .zero hext
              fields := nofun
              args_len := rfl
              args_fresh := nofun
              args_ty := .nil
              result := .appDF hbox (.bvar .zero) }
  isLE := by simp [boxDecl]

/-- **A two-declaration history ending in the block.**  So `boxDecl` is not a hypothetical:
`VEnv.WF'` reaches it, and `∀ d ∈ ds, d.noUnsafe` holds of the list. -/
theorem boxDecl_history : ∃ env₁, VEnv.WF' [.induct boxDecl, .axiom extAx] env₁ :=
  let ⟨env₁, he⟩ := boxDecl_add
  ⟨env₁, .decl (.induct boxDecl_WF he) (.decl extAx_decl_WF .empty)⟩

/-- The list is one the recursion is meant to visit: no `unsafe`/`partial` block. -/
theorem boxDecl_noUnsafe :
    ∀ d ∈ [VDecl.induct boxDecl, VDecl.axiom extAx], d.noUnsafe := by
  intro d hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  obtain rfl | rfl := hd <;> trivial

end SetModelAudit

open SetModelAudit in
/-- **The deleted field is refuted at an ordinary well-formed block**, on a declaration
list the soundness induction actually visits (`boxDecl_history`, `boxDecl_noUnsafe`). -/
theorem not_stagedField_boxDecl : ¬ StagedField boxDecl :=
  not_stagedField_of_head_const (Ts := []) rfl boxDecl_add.choose_spec boxDecl_head_const

open SetModelAudit in
/-- …and the **same condition at the environment the block is actually declared over
holds**.  So the defect was entirely the field's `∀ env`, and `StagedOcc` is the right
condition — which is why the repair is a deletion plus a call to a theorem, not a
weakening. -/
theorem stagedOcc_boxDecl : StagedOcc extEnv boxDecl.allConsts :=
  stagedOcc_allConsts extEnv_ordered boxDecl_WF boxDecl_add.choose_spec

/-! ## 4. What the repair bought, at the block the induction visits

Before the repair, `OracleFits L κ ls o [.induct boxDecl, .axiom extAx]` was
**unsatisfiable** (its `.induct` conjunct carried the refuted field), so
`coherentOn_cnstOf` had nothing to say about this list even though every other hypothesis
— `VEnv.WF'`, `noUnsafe`, `Ordered` — holds of it.  That is `docs/vacuity-ledger.md`
row 2's shape.

After the repair the same instantiation goes through from **inhabitation data only**: two
`OracleOK`s for the block's three constants plus one ι-rule, and one `OracleOK` for the
axiom.  Nothing occurrence-shaped is left, and nothing about `env` is quantified where it
cannot be met. -/

section Bought

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ} {κ : ℕ → V} {ls : List ℕ}

open SetModelAudit

/-- `OracleFits` at `boxDecl`'s history is exactly the two inhabitation obligations. -/
theorem oracleFits_boxDecl_iff (L : PropSplit envF nv) (o : Name → List VLevel → V) :
    OracleFits L κ ls o [.induct boxDecl, .axiom extAx] ↔
      (InductOracleOK L κ ls o
          (cnstOf L κ ls o [.induct boxDecl, .axiom extAx]) boxDecl ∧
        OracleOK L κ ls o (cnstOf L κ ls o [.axiom extAx]) extAx.name extAx.toVConstant) := by
  simp only [OracleFits, OracleStepOK, and_true]

/-- **The `.induct` case at a visited list, non-vacuously.**  Given the two inhabitation
obligations, the recursion delivers `CoherentOn` at `boxDecl`'s environment.  Before the
repair this statement was worthless: its `OracleFits` hypothesis was refutable
(`not_stagedField_boxDecl` transported through the deleted field). -/
theorem coherentOn_boxDecl_history_of (L : PropSplit envF nv) (o : Name → List VLevel → V)
    {R : List VExpr → List VExpr → Prop} (hS : L.Stable) (hR : CtxInvariant L R)
    (hRdF : ∀ {Γ : List VExpr} {A A' : VExpr} {u : VLevel},
      envF.IsDefEq nv Γ A A' (.sort u) → R (A' :: Γ) (A :: Γ))
    {env : VEnv} (hwf : VEnv.WF' [.induct boxDecl, .axiom extAx] env) (hle : env ≤ envF)
    (h1 : InductOracleOK L κ ls o (cnstOf L κ ls o [.induct boxDecl, .axiom extAx]) boxDecl)
    (h2 : OracleOK L κ ls o (cnstOf L κ ls o [.axiom extAx]) extAx.name extAx.toVConstant) :
    CoherentOn ⟨κ, ls, cnstOf L κ ls o [.induct boxDecl, .axiom extAx]⟩ L env :=
  coherentOn_cnstOf L o hS hR hRdF _ hwf hle boxDecl_noUnsafe
    ((oracleFits_boxDecl_iff L o).2 ⟨h1, h2⟩)

end Bought

/-! ## 5. Bounds on the repaired residual, field by field

Row 11a's lesson is that a structure-level two-way bound can be vacuous on exactly the
field that is false, so record the two remaining fields separately.

| field | not trivially true | satisfiable |
|---|---|---|
| `consts` | `not_inductOracleOK_falseProp` (`CnstRecursion.lean`) — a block declaring a constant of type `∀ p : Prop, p` | **open at a `WF` block**; free at any block with no type formers (`inductOracleOK_empty`, `empty_block_allConsts`) |
| `rules` | open — no ι-rule of a `WF` block is known to be refutable | free at any block whose types have no constructors (`iotaRules_eq_nil`) |

Both entries in the "not trivially true" column and the `inductOracleOK_empty` entry are
at blocks that are **not `VInductDecl'.WF`**: `types_ne` forbids the type-former-free
block, and no well-formed block declares a constant of type `∀ p : Prop, p` (a type
former's stored type ends in a sort, a constructor's in an application of a type former,
and a recursor's in a motive application; `.bvar 0` is none of those).  So the pair is a
sanity check on the *statement* of the residual, not a measurement at a reachable block —
the same weakness row 11a flagged, now recorded rather than repaired.

`boxDecl` is the natural candidate for a bound at a `WF`, reachable block, and it needs
real model work: `boxDecl.iotaRules` has exactly one rule (one constructor), and `consts`
asks for elements of `⟦∀ e : Ext, Prop⟧`, `⟦∀ e : Ext, Box e⟧` and `⟦Box.rec's type⟧`.
That is `SetModel/IndInterp.lean`'s job, not this file's. -/

/-- Row 11a, machine-checked: the old positive bound's block declares nothing, so its
`staged` field was `StagedOcc env []`, i.e. `True`. -/
theorem empty_block_allConsts :
    ({ uvars := 0, params := [], lvl := .zero, types := [], isLE := false }
      : VInductDecl').allConsts = [] := rfl

/-- The `rules` field is free at a block with no constructors — a genuine class of
`WF` blocks (`inductive Void1 (α : Type) : Type`), unlike the type-former-free block. -/
theorem iotaRules_nil_of_no_ctors {D : VInductDecl'} (h : ∀ T ∈ D.types, T.ctors = []) :
    ∀ df ∈ D.iotaRules, False := by
  intro df hdf; rw [VInductDecl'.iotaRules_eq_nil D h] at hdf; exact absurd hdf nofun

end Lean4Lean.SetModel
