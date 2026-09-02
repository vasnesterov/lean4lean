import Lean4Lean.Theory.SetModel.PreludeWitness
import Lean4Lean.Theory.SetModel.PreludeSpec
import Lean4Lean.Theory.SetModel.UnitOracleLarge
import Lean4Lean.Theory.SetModel.NotProofNoModel

/-!
# The `.induct` residual at a **prelude** block: `Nonempty`

`docs/vacuity-ledger.md` row 83c records the frontier of `InductOracleOK` after
`UnitOracleWitness.lean` and `UnitOracleLarge.lean`: **a block with recursive fields, or with
parameters/indices.**  `boxDecl`, `unitDecl` and `unitDeclLE` have none of those, and
`UpperBound.lean` §5 / `docs/handoff-setmodel.md` §8.4 say the same thing in the form that
matters for H2: `exists_oracleFits_unit` is at `unitEnv`, which is *not* a Lean environment,
and at a **prelude** history the `.induct` steps are `eqIndDecl`, `iffIndDecl` and
`nonemptyIndDecl`, all with parameters.

**This file closes the third of those three**, at the environment `PreludeWitness.lean` names.

## What is proved

| theorem | content |
|---|---|
| `inductOracleOK_NE` | **both** fields of `InductOracleOK` at `nonemptyIndDecl`, for any `L` with `hle : nonemptyEnv ≤ envF` |
| `nonemptyEnv_le_preludeEnv` | `hle` is a **theorem** at the prelude environment (three `VDecl.WF.le` steps) |
| `inductOracleOK_NE_at_preludeEnv` | hence the residual, at `preludeEnv` |
| `cnstOf_preludeTail`, `oracleStepOK_NE` | …and in the exact shape `OracleFits` asks for, at the step's **own position** in `leanPrelude.reverse` |
| `mem_interp_consts_NE`, `defEq_rules_NE` | both obligations with the `Above` wrapper **stripped**, at an arbitrary `κ` |
| `not_mem_interp_zeroOracle_NE_type` | a negative bound: the oracle that carried `boxDecl` **fails** here |
| `nonempty_propSplit_preludeEnv_iff` | the one hypothesis that is *not* discharged, named exactly |
| `propTypeAgree_zero_iff_equivZero` | **a correction**: `NotProofNoModel.lean` §6's "the two shapes do not compose" is a statement about `nv ≥ 2`; at `nv = 0` — the only `nv` this corner uses — the pointwise and `≈ .zero` shapes are *equivalent* |
| `iff_recType`, `eq_recType`, `eq_isLE`, `iff_isLE` | what the other two prelude blocks ask for, **measured** (`rfl`) rather than costed |

## The oracle is not new — it is `PreludeSpec.lean`'s own witness

`neOracle κ ls = (preludeWitness κ ls).cnst`, byte for byte the assignment
`PreludeSpec.preludeSpec_satisfiable` exhibits for `EqSpec`/`IffSpec`/`NonemptySpec`.  Nothing
was tuned for this file: `Nonempty ↦ nonemptyFn κ n` is the intended squash, and
`Nonempty.intro`/`Nonempty.rec` get `∅`, which **is** `•` (`pt_def`).  So the same assignment
that validates the three standard axioms' specifications discharges the `.induct` residual at
the block `Classical.choice`'s type mentions.

## Why this block is not a re-run of the two easy ones

* `boxDecl` met the residual because its parameter denoted `∅`; here the parameter denotes a
  **universe** (`interp_param_ne_empty`), and `not_mem_interp_zeroOracle_NE_type` machine-checks
  that the `∅`-everywhere oracle is *refuted* at the type former.
* `unitDecl` has **no** parameter and **no** constructor field (`unitDecl_params_nil`); this
  block has one of each (`ne_params`, `neCtor_fields`).  The type former's value is therefore a
  genuine internal function rather than a truth value, built with
  `UnitOracleLarge.mkLam_mem_mkForallType_of_dom`.
* The squash must be **faithful**: the constructor's obligation forces `α ≠ ∅ → ⟦Nonempty α⟧`
  true, and the recursor's forces the converse — `nonemptyFn_zero_empty` and
  `nonemptyFn_zero_true` check both branches fire at `U₀`, where they are the only two carriers.

The recursor is where the squash is paid for, and it is cheap for one reason:
`nonemptyIndDecl.isLE = false`, so `elimLvl = .zero` and the **whole** of `recType 0` is a
proposition (`hasType_recB1`: sort `imax 1 0 = 0`).  `interp` therefore takes `mkForallProp`
at every binder and the oracle's value is `•`.  A *large* eliminator over this block would need
a genuine four-layer `mkLam`, which is the `UnitOracleLarge.recFnL` construction one telescope
up — see §13 for what that means for `Eq` and `Iff`.

## What is **not** proved, stated sharply

* `eqIndDecl` and `iffIndDecl` are **open**, and now for a named reason: both have
  `isLE := true`, so their recursors' types are *not* propositions and their oracle values must
  be genuine nested `mkLam`s (six and five layers, against `unitDeclLE`'s three).  §13 records
  the measurement.
* `L : PropSplit envF nv` is quantified over and **nothing in this tree constructs one**, at
  any environment: the only producers are `propSplitOf`, `propSplitUp` (both taking `PropUniq`
  and `PropTypeAgree`) and `LevelAssign.toPropSplit` (taking a structure nothing builds).  §11
  pins that at `preludeEnv`: it is exactly `PropTypeAgree preludeEnv 0`, i.e.
  `UpperBound.PropTypeAgreeInput`'s instance at the witness environment.  **That is a property
  of the whole layer, not of this file** — `coherentOn_cnstOf` quantifies over the same `L` —
  but it is the reason `docs/handoff-setmodel.md` §9.7's items 2 and 3 are one item.
-/

namespace Lean4Lean.SetModel.NEAudit

open Lean4Lean LO LO.FirstOrder LO.FirstOrder.SetTheory

/-! ## 1. The block's shapes, computed -/

/-- `Nonempty.rec`. -/
abbrev recN : Name := Lean.mkRecName ``Nonempty

theorem recN_eq : recN = ``Nonempty.rec := rfl

/-- `motive : Nonempty α → Prop`, in the context `[.sort u]`. -/
abbrev motTy (u : VLevel) : VExpr :=
  .forallE (.app (.const ``Nonempty [u]) (.bvar 0)) (.sort .zero)

/-- `minor : ∀ val : α, motive (Nonempty.intro α val)`, in `[motTy u, .sort u]`. -/
abbrev minTy (u : VLevel) : VExpr :=
  .forallE (.bvar 1)
    (.app (.bvar 1) (.app (.app (.const ``Nonempty.intro [u]) (.bvar 2)) (.bvar 0)))

/-- `t : Nonempty α`, in `[minTy u, motTy u, .sort u]`. -/
abbrev majTy (u : VLevel) : VExpr := .app (.const ``Nonempty [u]) (.bvar 2)

/-- `motive t`, in `[majTy u, minTy u, motTy u, .sort u]`. -/
abbrev resTy : VExpr := .app (.bvar 2) (.bvar 0)

theorem ne_typeConsts :
    nonemptyIndDecl.typeConsts =
      [(``Nonempty, ⟨1, .forallE (.sort (.param 0)) (.sort .zero)⟩)] := rfl

theorem ne_ctorConsts :
    nonemptyIndDecl.ctorConsts =
      [(``Nonempty.intro, ⟨1, .forallE (.sort (.param 0))
        (.forallE (.bvar 0) (.app (.const ``Nonempty [.param 0]) (.bvar 1)))⟩)] := rfl

theorem ne_recConsts :
    nonemptyIndDecl.recConsts = [(recN, ⟨1, nonemptyIndDecl.recType 0⟩)] := rfl

theorem ne_allConsts :
    nonemptyIndDecl.allConsts =
      [(``Nonempty, ⟨1, .forallE (.sort (.param 0)) (.sort .zero)⟩),
       (``Nonempty.intro, ⟨1, .forallE (.sort (.param 0))
         (.forallE (.bvar 0) (.app (.const ``Nonempty [.param 0]) (.bvar 1)))⟩),
       (recN, ⟨1, nonemptyIndDecl.recType 0⟩)] := rfl

theorem ne_allNames :
    nonemptyIndDecl.allNames = [``Nonempty, ``Nonempty.intro, recN] := rfl

theorem ne_recUvars : nonemptyIndDecl.recUvars = 1 := rfl

/-- The recursor type with its one level parameter substituted. -/
theorem ne_recType_instL (u : VLevel) :
    (nonemptyIndDecl.recType 0).instL [u] =
      .forallE (.sort u) (.forallE (motTy u) (.forallE (minTy u)
        (.forallE (majTy u) resTy))) := rfl

/-- The constructor, `[Nonempty.intro]`. -/
def neCtor : VIndCtor :=
  { name := ``Nonempty.intro, params := [.sort (.param 0)],
    fields := [{ type := .bvar 0, lvl := .param 0, recArg := none }], args := [] }

theorem ne_ctorsAll : nonemptyIndDecl.ctorsAll = [(0, neCtor)] := rfl

theorem ne_iotaRules : nonemptyIndDecl.iotaRules = [nonemptyIndDecl.iotaRule 0 0 neCtor] := rfl

theorem ne_iotaCtx :
    nonemptyIndDecl.iotaCtx neCtor = [.sort (.param 0), motTy (.param 0),
      minTy (.param 0), .bvar 2] := by
  show _ = _
  rfl

theorem neRule_uvars : (nonemptyIndDecl.iotaRule 0 0 neCtor).uvars = 1 := rfl

theorem neRule_lhs_instL (u : VLevel) :
    (nonemptyIndDecl.iotaRule 0 0 neCtor).lhs.instL [u] =
      .lam (.sort u) (.lam (motTy u) (.lam (minTy u) (.lam (.bvar 2)
        (.app (.app (.app (.app (.const recN [u]) (.bvar 3)) (.bvar 2)) (.bvar 1))
          (.app (.app (.const ``Nonempty.intro [u]) (.bvar 3)) (.bvar 0)))))) := rfl

theorem neRule_rhs_instL (u : VLevel) :
    (nonemptyIndDecl.iotaRule 0 0 neCtor).rhs.instL [u] =
      .lam (.sort u) (.lam (motTy u) (.lam (minTy u) (.lam (.bvar 2)
        (.app (.app (.app (.app
          (.lam (.sort u) (.lam (motTy u) (.lam (minTy u) (.lam (.bvar 2)
            (.app (.bvar 1) (.bvar 0))))))
          (.bvar 3)) (.bvar 2)) (.bvar 1)) (.bvar 0))))) := rfl

theorem neRule_type_instL (u : VLevel) :
    (nonemptyIndDecl.iotaRule 0 0 neCtor).type.instL [u] =
      .forallE (.sort u) (.forallE (motTy u) (.forallE (minTy u) (.forallE (.bvar 2)
        (.app (.bvar 2) (.app (.app (.const ``Nonempty.intro [u]) (.bvar 3)) (.bvar 0)))))) :=
  rfl


/-! ## 2. The environment `nonemptyEnv`, and the three constants it stores -/

theorem nonemptyEnv_intro : nonemptyEnv.constants ``Nonempty.intro =
    some ⟨1, .forallE (.sort (.param 0))
      (.forallE (.bvar 0) (.app (.const ``Nonempty [.param 0]) (.bvar 1)))⟩ := rfl

theorem nonemptyEnv_rec :
    nonemptyEnv.constants recN = some ⟨1, nonemptyIndDecl.recType 0⟩ := rfl

/-! ## 3. Typing derivations in `nonemptyEnv`

Every proof-splitting decision below is read off one of these through
`isProp_iff`/`isProof_iff`, exactly as `UnitOracleWitness.lean` does. -/

section Typing

variable {nv : ℕ} {u : VLevel} (hu : u.WF nv)

theorem levels_wf {nv : ℕ} {u : VLevel} (hu : u.WF nv) : ∀ l ∈ [u], l.WF nv := by
  intro l hl; rw [List.mem_singleton] at hl; subst hl; exact hu

include hu in
/-- `Nonempty.{u} : ∀ α : Sort u, Prop`. -/
theorem hasType_NE {Γ : List VExpr} :
    nonemptyEnv.HasType nv Γ (.const ``Nonempty [u])
      (.forallE (.sort u) (.sort .zero)) :=
  .constDF nonemptyEnv_Nonempty (levels_wf hu) (levels_wf hu) rfl (.cons (by rfl) .nil)

include hu in
/-- `Nonempty.intro.{u} : ∀ (α : Sort u) (val : α), Nonempty α`. -/
theorem hasType_IN {Γ : List VExpr} :
    nonemptyEnv.HasType nv Γ (.const ``Nonempty.intro [u])
      (.forallE (.sort u) (.forallE (.bvar 0) (.app (.const ``Nonempty [u]) (.bvar 1)))) :=
  .constDF nonemptyEnv_intro (levels_wf hu) (levels_wf hu) rfl (.cons (by rfl) .nil)

include hu in
/-- `Nonempty.rec.{u}` at its stored type. -/
theorem hasType_RC {Γ : List VExpr} :
    nonemptyEnv.HasType nv Γ (.const recN [u])
      (.forallE (.sort u) (.forallE (motTy u) (.forallE (minTy u)
        (.forallE (majTy u) resTy)))) := by
  have h := VEnv.IsDefEq.constDF (env := nonemptyEnv) (Γ := Γ) (uvars := nv)
    nonemptyEnv_rec (levels_wf hu) (levels_wf hu) rfl (.cons (by rfl) .nil)
  rwa [show (⟨1, nonemptyIndDecl.recType 0⟩ : VConstant).type.instL [u] =
    VExpr.forallE (.sort u) (.forallE (motTy u) (.forallE (minTy u)
      (.forallE (majTy u) resTy))) from rfl] at h

end Typing



/-! ## 4. The binder contexts, with an arbitrary tail

`Lookup` depends only on the prefix, so every typing lemma below holds over an arbitrary
tail `Γ`; the interpretation is then read at `Γ = []`, where `interp`'s `bvar` clause turns
de Bruijn indices into positions. -/

section Ctxs
variable (u : VLevel) (Γ : List VExpr)
/-- `α : Sort u`. -/
abbrev ctx1 : List VExpr := .sort u :: Γ
/-- `motive, α`. -/
abbrev ctx2 : List VExpr := motTy u :: ctx1 u Γ
/-- `minor, motive, α`. -/
abbrev ctx3 : List VExpr := minTy u :: ctx2 u Γ
/-- `t, minor, motive, α` — the recursor's major premise. -/
abbrev ctx4 : List VExpr := majTy u :: ctx3 u Γ
/-- `val, minor, motive, α` — the ι-rule's context. -/
abbrev ctxF : List VExpr := .bvar 2 :: ctx3 u Γ
/-- `val, α` — inside `Nonempty.intro`'s type. -/
abbrev ctxI : List VExpr := .bvar 0 :: ctx1 u Γ
/-- `val, motive, α` — inside the minor premise's type. -/
abbrev ctxM : List VExpr := .bvar 1 :: ctx2 u Γ
end Ctxs

/-! ## 5. Typing derivations in `nonemptyEnv`

Every proof-splitting decision the interpretation makes inside the three declared types and
inside the ι-rule is read off one of these, through `isProp_iff`/`isProof_iff` — exactly the
arrangement of `UnitOracleWitness.lean` §4, and of `QuotInterp.lean` before it. -/

section Derived

variable {nv : ℕ} {u : VLevel} (hu : u.WF nv) (Γ : List VExpr)

include hu in
theorem hasType_NEapp0 :
    nonemptyEnv.HasType nv (ctx1 u Γ) (.app (.const ``Nonempty [u]) (.bvar 0))
      (.sort .zero) :=
  .appDF (hasType_NE hu) (.bvar .zero)

include hu in
/-- `motive : Nonempty α → Prop` is a **type**, of sort `imax 0 1 = 1`. -/
theorem hasType_motTy :
    nonemptyEnv.HasType nv (ctx1 u Γ) (motTy u) (.sort (.imax .zero (.succ .zero))) :=
  .forallEDF (hasType_NEapp0 hu Γ) (.sortDF trivial trivial (.refl _))

theorem hasType_bvar1_ctx2 :
    nonemptyEnv.HasType nv (ctx2 u Γ) (.bvar 1) (.sort u) := .bvar (.succ .zero)

theorem hasType_bvar2_ctx3 :
    nonemptyEnv.HasType nv (ctx3 u Γ) (.bvar 2) (.sort u) := .bvar (.succ (.succ .zero))

theorem hasType_bvar3_ctxF :
    nonemptyEnv.HasType nv (ctxF u Γ) (.bvar 3) (.sort u) :=
  .bvar (.succ (.succ (.succ .zero)))

theorem hasType_bvar1_ctxI :
    nonemptyEnv.HasType nv (ctxI u Γ) (.bvar 1) (.sort u) := .bvar (.succ .zero)

theorem hasType_bvar2_ctxM :
    nonemptyEnv.HasType nv (ctxM u Γ) (.bvar 2) (.sort u) := .bvar (.succ (.succ .zero))

include hu in
theorem hasType_NEapp1_ctxI :
    nonemptyEnv.HasType nv (ctxI u Γ) (.app (.const ``Nonempty [u]) (.bvar 1))
      (.sort .zero) :=
  .appDF (hasType_NE hu) (hasType_bvar1_ctxI Γ)

include hu in
/-- `∀ val : α, Nonempty α : Prop` — the codomain of `Nonempty.intro`'s type, sort
`imax u 0 = 0`. -/
theorem hasType_introB1 :
    nonemptyEnv.HasType nv (ctx1 u Γ)
      (.forallE (.bvar 0) (.app (.const ``Nonempty [u]) (.bvar 1)))
      (.sort (.imax u .zero)) :=
  .forallEDF (.bvar .zero) (hasType_NEapp1_ctxI hu Γ)

/-! ### Inside the minor premise's type -/

theorem hasType_bvar1_ctxM :
    nonemptyEnv.HasType nv (ctxM u Γ) (.bvar 1)
      (.forallE (.app (.const ``Nonempty [u]) (.bvar 2)) (.sort .zero)) :=
  .bvar (.succ .zero)

theorem hasType_bvar0_ctxM :
    nonemptyEnv.HasType nv (ctxM u Γ) (.bvar 0) (.bvar 2) := .bvar .zero

include hu in
theorem hasType_introApp_ctxM :
    nonemptyEnv.HasType nv (ctxM u Γ)
      (.app (.app (.const ``Nonempty.intro [u]) (.bvar 2)) (.bvar 0))
      (.app (.const ``Nonempty [u]) (.bvar 2)) :=
  ((hasType_IN hu).appDF (hasType_bvar2_ctxM Γ)).appDF (hasType_bvar0_ctxM Γ)

include hu in
theorem hasType_minBody :
    nonemptyEnv.HasType nv (ctxM u Γ)
      (.app (.bvar 1) (.app (.app (.const ``Nonempty.intro [u]) (.bvar 2)) (.bvar 0)))
      (.sort .zero) :=
  (hasType_bvar1_ctxM Γ).appDF (hasType_introApp_ctxM hu Γ)

include hu in
/-- `minor : ∀ val : α, motive (Nonempty.intro α val)` is a **proposition**. -/
theorem hasType_minTy :
    nonemptyEnv.HasType nv (ctx2 u Γ) (minTy u) (.sort (.imax u .zero)) :=
  .forallEDF (hasType_bvar1_ctx2 Γ) (hasType_minBody hu Γ)

/-! ### The recursor's remaining binders -/

include hu in
theorem hasType_majTy :
    nonemptyEnv.HasType nv (ctx3 u Γ) (majTy u) (.sort .zero) :=
  (hasType_NE hu).appDF (hasType_bvar2_ctx3 Γ)

theorem hasType_bvar2_ctx4 :
    nonemptyEnv.HasType nv (ctx4 u Γ) (.bvar 2)
      (.forallE (.app (.const ``Nonempty [u]) (.bvar 3)) (.sort .zero)) :=
  .bvar (.succ (.succ .zero))

theorem hasType_bvar0_ctx4 :
    nonemptyEnv.HasType nv (ctx4 u Γ) (.bvar 0)
      (.app (.const ``Nonempty [u]) (.bvar 3)) := .bvar .zero

theorem hasType_resTy :
    nonemptyEnv.HasType nv (ctx4 u Γ) resTy (.sort .zero) :=
  (hasType_bvar2_ctx4 Γ).appDF (hasType_bvar0_ctx4 Γ)

include hu in
theorem hasType_recB3 :
    nonemptyEnv.HasType nv (ctx3 u Γ) (.forallE (majTy u) resTy)
      (.sort (.imax .zero .zero)) :=
  .forallEDF (hasType_majTy hu Γ) (hasType_resTy Γ)

include hu in
theorem hasType_recB2 :
    nonemptyEnv.HasType nv (ctx2 u Γ) (.forallE (minTy u) (.forallE (majTy u) resTy))
      (.sort (.imax (.imax u .zero) (.imax .zero .zero))) :=
  .forallEDF (hasType_minTy hu Γ) (hasType_recB3 hu Γ)

include hu in
/-- **The recursor type's codomain is a proposition**: `imax 1 0 = 0`.  This is what makes
`nonemptyIndDecl`'s recursor value `•` rather than a function — the block is a *small*
eliminator (`isLE := false`). -/
theorem hasType_recB1 :
    nonemptyEnv.HasType nv (ctx1 u Γ)
      (.forallE (motTy u) (.forallE (minTy u) (.forallE (majTy u) resTy)))
      (.sort (.imax (.imax .zero (.succ .zero))
        (.imax (.imax u .zero) (.imax .zero .zero)))) :=
  .forallEDF (hasType_motTy hu Γ) (hasType_recB2 hu Γ)

/-! ### The ι-rule's context -/

theorem hasType_bvar2_ctxF :
    nonemptyEnv.HasType nv (ctxF u Γ) (.bvar 2)
      (.forallE (.app (.const ``Nonempty [u]) (.bvar 3)) (.sort .zero)) :=
  .bvar (.succ (.succ .zero))

theorem hasType_bvar1_ctxF :
    nonemptyEnv.HasType nv (ctxF u Γ) (.bvar 1)
      (.forallE (.bvar 3)
        (.app (.bvar 3) (.app (.app (.const ``Nonempty.intro [u]) (.bvar 4)) (.bvar 0)))) :=
  .bvar (.succ .zero)

theorem hasType_bvar0_ctxF :
    nonemptyEnv.HasType nv (ctxF u Γ) (.bvar 0) (.bvar 3) := .bvar .zero

include hu in
theorem hasType_introApp_ctxF :
    nonemptyEnv.HasType nv (ctxF u Γ)
      (.app (.app (.const ``Nonempty.intro [u]) (.bvar 3)) (.bvar 0))
      (.app (.const ``Nonempty [u]) (.bvar 3)) :=
  ((hasType_IN hu).appDF (hasType_bvar3_ctxF Γ)).appDF (hasType_bvar0_ctxF Γ)

include hu in
theorem hasType_ruleBody :
    nonemptyEnv.HasType nv (ctxF u Γ)
      (.app (.bvar 2) (.app (.app (.const ``Nonempty.intro [u]) (.bvar 3)) (.bvar 0)))
      (.sort .zero) :=
  (hasType_bvar2_ctxF Γ).appDF (hasType_introApp_ctxF hu Γ)

include hu in
theorem hasType_ruleB3 :
    nonemptyEnv.HasType nv (ctx3 u Γ)
      (.forallE (.bvar 2)
        (.app (.bvar 2) (.app (.app (.const ``Nonempty.intro [u]) (.bvar 3)) (.bvar 0))))
      (.sort (.imax u .zero)) :=
  .forallEDF (hasType_bvar2_ctx3 Γ) (hasType_ruleBody hu Γ)

include hu in
theorem hasType_ruleB2 :
    nonemptyEnv.HasType nv (ctx2 u Γ)
      (.forallE (minTy u) (.forallE (.bvar 2)
        (.app (.bvar 2) (.app (.app (.const ``Nonempty.intro [u]) (.bvar 3)) (.bvar 0)))))
      (.sort (.imax (.imax u .zero) (.imax u .zero))) :=
  .forallEDF (hasType_minTy hu Γ) (hasType_ruleB3 hu Γ)

include hu in
/-- **The ι-rule's type minus its outer binder is a proposition** (`imax 1 0 = 0`) — which
is why both sides of the rule are proofs and the equation is `• = •`. -/
theorem hasType_ruleB1 :
    nonemptyEnv.HasType nv (ctx1 u Γ)
      (.forallE (motTy u) (.forallE (minTy u) (.forallE (.bvar 2)
        (.app (.bvar 2) (.app (.app (.const ``Nonempty.intro [u]) (.bvar 3)) (.bvar 0))))))
      (.sort (.imax (.imax .zero (.succ .zero)) (.imax (.imax u .zero) (.imax u .zero)))) :=
  .forallEDF (hasType_motTy hu Γ) (hasType_ruleB2 hu Γ)

/-! ### The two sides of the ι-rule -/

include hu in
/-- `Nonempty.rec α motive minor (Nonempty.intro α val) : motive (Nonempty.intro α val)`. -/
theorem hasType_lhsBody :
    nonemptyEnv.HasType nv (ctxF u Γ)
      (.app (.app (.app (.app (.const recN [u]) (.bvar 3)) (.bvar 2)) (.bvar 1))
        (.app (.app (.const ``Nonempty.intro [u]) (.bvar 3)) (.bvar 0)))
      (.app (.bvar 2) (.app (.app (.const ``Nonempty.intro [u]) (.bvar 3)) (.bvar 0))) :=
  ((((hasType_RC hu).appDF (hasType_bvar3_ctxF Γ)).appDF (hasType_bvar2_ctxF Γ)).appDF
    (hasType_bvar1_ctxF Γ)).appDF (hasType_introApp_ctxF hu Γ)

include hu in
theorem hasType_lhsLam :
    nonemptyEnv.HasType nv (ctx1 u Γ)
      (.lam (motTy u) (.lam (minTy u) (.lam (.bvar 2)
        (.app (.app (.app (.app (.const recN [u]) (.bvar 3)) (.bvar 2)) (.bvar 1))
          (.app (.app (.const ``Nonempty.intro [u]) (.bvar 3)) (.bvar 0))))))
      (.forallE (motTy u) (.forallE (minTy u) (.forallE (.bvar 2)
        (.app (.bvar 2) (.app (.app (.const ``Nonempty.intro [u]) (.bvar 3)) (.bvar 0)))))) :=
  .lamDF (hasType_motTy hu Γ) (.lamDF (hasType_minTy hu Γ)
    (.lamDF (hasType_bvar2_ctx3 Γ) (hasType_lhsBody hu Γ)))

/-- The ι-rule's inner λ-nest, `λ α motive minor val. minor val`. -/
abbrev iotaLamE (u : VLevel) : VExpr :=
  .lam (.sort u) (.lam (motTy u) (.lam (minTy u) (.lam (.bvar 2)
    (.app (.bvar 1) (.bvar 0)))))

theorem hasType_iotaLamBody :
    nonemptyEnv.HasType nv (ctxF u Γ) (.app (.bvar 1) (.bvar 0))
      (.app (.bvar 2) (.app (.app (.const ``Nonempty.intro [u]) (.bvar 3)) (.bvar 0))) :=
  (hasType_bvar1_ctxF Γ).appDF (hasType_bvar0_ctxF Γ)

include hu in
theorem hasType_iotaLamE :
    nonemptyEnv.HasType nv Γ (iotaLamE u)
      (.forallE (.sort u) (.forallE (motTy u) (.forallE (minTy u) (.forallE (.bvar 2)
        (.app (.bvar 2)
          (.app (.app (.const ``Nonempty.intro [u]) (.bvar 3)) (.bvar 0))))))) :=
  .lamDF (.sortDF hu hu (.refl _)) (.lamDF (hasType_motTy hu Γ)
    (.lamDF (hasType_minTy hu Γ) (.lamDF (hasType_bvar2_ctx3 Γ)
      (hasType_iotaLamBody Γ))))

include hu in
/-- The η-expanded right-hand side's body, at the same type as the left. -/
theorem hasType_rhsBody :
    nonemptyEnv.HasType nv (ctxF u Γ)
      (.app (.app (.app (.app (iotaLamE u) (.bvar 3)) (.bvar 2)) (.bvar 1)) (.bvar 0))
      (.app (.bvar 2) (.app (.app (.const ``Nonempty.intro [u]) (.bvar 3)) (.bvar 0))) :=
  ((((hasType_iotaLamE hu _).appDF (hasType_bvar3_ctxF Γ)).appDF
    (hasType_bvar2_ctxF Γ)).appDF (hasType_bvar1_ctxF Γ)).appDF (hasType_bvar0_ctxF Γ)

include hu in
theorem hasType_rhsLam :
    nonemptyEnv.HasType nv (ctx1 u Γ)
      (.lam (motTy u) (.lam (minTy u) (.lam (.bvar 2)
        (.app (.app (.app (.app (iotaLamE u) (.bvar 3)) (.bvar 2)) (.bvar 1)) (.bvar 0)))))
      (.forallE (motTy u) (.forallE (minTy u) (.forallE (.bvar 2)
        (.app (.bvar 2) (.app (.app (.const ``Nonempty.intro [u]) (.bvar 3)) (.bvar 0)))))) :=
  .lamDF (hasType_motTy hu Γ) (.lamDF (hasType_minTy hu Γ)
    (.lamDF (hasType_bvar2_ctx3 Γ) (hasType_rhsBody hu Γ)))

end Derived


/-! ## 6. The oracle: **`PreludeSpec.lean`'s own witness, unchanged** -/

section Model

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]

/-- **The oracle is `preludeWitness`' constant assignment**, the joint witness
`PreludeSpec.lean` built for `EqSpec`/`IffSpec`/`NonemptySpec`.  Nothing is added and
nothing is changed: `Nonempty ↦ nonemptyFn κ n` is the intended squash, and the two
`Prop`-valued names get `∅`, which *is* `•` (`pt_def`). -/
noncomputable def neOracle (κ : ℕ → V) (ls : List ℕ) : Name → List VLevel → V :=
  (preludeWitness κ ls).cnst

/-- The model data, which is `preludeWitness κ ls` on the nose. -/
noncomputable def neM (κ : ℕ → V) (ls : List ℕ) : ModelData V := ⟨κ, ls, neOracle κ ls⟩

theorem neM_eq (κ : ℕ → V) (ls : List ℕ) : neM κ ls = preludeWitness κ ls := rfl

section OracleValues
variable {κ : ℕ → V} {ls : List ℕ}

theorem neOracle_NE (u : VLevel) :
    neOracle κ ls ``Nonempty [u] = nonemptyFn κ (u.eval ls) := by
  simp [neOracle, preludeWitness]

theorem neOracle_intro (us : List VLevel) : neOracle κ ls ``Nonempty.intro us = (pt : V) := by
  simp [neOracle, preludeWitness, pt]

theorem neOracle_rec (us : List VLevel) : neOracle κ ls recN us = (pt : V) := by
  simp [neOracle, preludeWitness, recN, Lean.mkRecName, pt]

/-! The same three, phrased at `(neM κ ls).cnst` so that `interp_const`'s output rewrites. -/

theorem neM_cnst_NE (u : VLevel) :
    (neM κ ls).cnst ``Nonempty [u] = nonemptyFn κ (u.eval ls) := neOracle_NE u

theorem neM_cnst_intro (us : List VLevel) :
    (neM κ ls).cnst ``Nonempty.intro us = (pt : V) := neOracle_intro us

theorem neM_cnst_rec (us : List VLevel) :
    (neM κ ls).cnst recN us = (pt : V) := neOracle_rec us

end OracleValues

/-! ### The proof-splitting decisions

Each is `isProp_iff`/`isProof_iff` at one of §5's derivations, so each carries
`hle : nonemptyEnv ≤ envF` — the same hypothesis `UnitOracleWitness.lean` and
`QuotInterp.lean` carry, and the one `coherentOn_cnstOf` already has in scope at the step. -/

section Split

variable {envF : VEnv} {nv : ℕ} (L : PropSplit envF nv) (κ : ℕ → V) (ls : List ℕ)
variable {u : VLevel} (hu : u.WF nv) (hle : nonemptyEnv ≤ envF)

include hu in
/-- `Nonempty.{u} : ∀ α : Sort u, Prop` is a **type**, not a proposition: its sort is
`imax (u+1) 1 = u+1`. -/
theorem hasType_tyNE {Γ : List VExpr} :
    nonemptyEnv.HasType nv Γ (.forallE (.sort u) (.sort .zero))
      (.sort (.imax (.succ u) (.succ .zero))) :=
  .forallEDF (.sortDF hu hu (.refl _)) (.sortDF trivial trivial (.refl _))

include hu hle in
theorem not_isProof_NE (Γ : List VExpr) :
    ¬ L.IsProof (neM κ ls) Γ (.const ``Nonempty [u]) := by
  rw [isProof_iff hle (hasType_NE hu) (hasType_tyNE hu)
    (u := .imax (.succ u) (.succ .zero)) ⟨hu, trivial⟩]
  simp [VLevel.eval, Lean.Nat.imax]

include hu hle in
/-- `motive : Nonempty α → Prop`, one binder in: **not** a proof, sort `imax 0 1 = 1`. -/
theorem not_isProof_bvar1_ctxM (Γ : List VExpr) :
    ¬ L.IsProof (neM κ ls) (ctxM u Γ) (.bvar 1) := by
  rw [isProof_iff hle (hasType_bvar1_ctxM Γ)
    (.forallEDF ((hasType_NE hu).appDF (hasType_bvar2_ctxM Γ))
      (.sortDF trivial trivial (.refl _)))
    (u := .imax .zero (.succ .zero)) ⟨trivial, trivial⟩]
  simp [VLevel.eval, Lean.Nat.imax]

include hu hle in
theorem not_isProof_bvar2_ctx4 (Γ : List VExpr) :
    ¬ L.IsProof (neM κ ls) (ctx4 u Γ) (.bvar 2) := by
  rw [isProof_iff hle (hasType_bvar2_ctx4 Γ)
    (.forallEDF ((hasType_NE hu).appDF (.bvar (.succ (.succ (.succ .zero)))))
      (.sortDF trivial trivial (.refl _)))
    (u := .imax .zero (.succ .zero)) ⟨trivial, trivial⟩]
  simp [VLevel.eval, Lean.Nat.imax]

include hu hle in
theorem not_isProof_bvar2_ctxF (Γ : List VExpr) :
    ¬ L.IsProof (neM κ ls) (ctxF u Γ) (.bvar 2) := by
  rw [isProof_iff hle (hasType_bvar2_ctxF Γ)
    (.forallEDF ((hasType_NE hu).appDF (.bvar (.succ (.succ (.succ .zero)))))
      (.sortDF trivial trivial (.refl _)))
    (u := .imax .zero (.succ .zero)) ⟨trivial, trivial⟩]
  simp [VLevel.eval, Lean.Nat.imax]

include hu hle in
/-- **`Nonempty.intro α val` is a proof**: its type `Nonempty α` is a proposition, so the
partial application `Nonempty.intro α` is a proof and `interp` discards the argument. -/
theorem isProof_introApp_ctxM (Γ : List VExpr) :
    L.IsProof (neM κ ls) (ctxM u Γ) (.app (.const ``Nonempty.intro [u]) (.bvar 2)) := by
  rw [isProof_iff hle ((hasType_IN hu).appDF (hasType_bvar2_ctxM Γ))
    (.forallEDF (hasType_bvar2_ctxM Γ) ((hasType_NE hu).appDF (.bvar (.succ (.succ (.succ .zero))))))
    (u := .imax u .zero) ⟨hu, trivial⟩]
  simp [VLevel.eval, Lean.Nat.imax]

include hu hle in
theorem isProof_introApp_ctxF (Γ : List VExpr) :
    L.IsProof (neM κ ls) (ctxF u Γ) (.app (.const ``Nonempty.intro [u]) (.bvar 3)) := by
  rw [isProof_iff hle ((hasType_IN hu).appDF (hasType_bvar3_ctxF Γ))
    (.forallEDF (hasType_bvar3_ctxF Γ)
      ((hasType_NE hu).appDF (.bvar (.succ (.succ (.succ (.succ .zero)))))))
    (u := .imax u .zero) ⟨hu, trivial⟩]
  simp [VLevel.eval, Lean.Nat.imax]

/-! #### The four `IsProp`s of the recursor type, and the four of the ι-rule's type -/

include hu hle in
theorem isProp_recB1 (Γ : List VExpr) :
    L.IsProp (neM κ ls) (ctx1 u Γ)
      (.forallE (motTy u) (.forallE (minTy u) (.forallE (majTy u) resTy))) := by
  rw [isProp_iff hle (hasType_recB1 hu Γ)
    (u := .imax (.imax .zero (.succ .zero)) (.imax (.imax u .zero) (.imax .zero .zero)))
    ⟨⟨trivial, trivial⟩, ⟨hu, trivial⟩, trivial, trivial⟩]
  simp [VLevel.eval, Lean.Nat.imax]

include hu hle in
theorem isProp_recB2 (Γ : List VExpr) :
    L.IsProp (neM κ ls) (ctx2 u Γ) (.forallE (minTy u) (.forallE (majTy u) resTy)) := by
  rw [isProp_iff hle (hasType_recB2 hu Γ)
    (u := .imax (.imax u .zero) (.imax .zero .zero)) ⟨⟨hu, trivial⟩, trivial, trivial⟩]
  simp [VLevel.eval, Lean.Nat.imax]

include hu hle in
theorem isProp_recB3 (Γ : List VExpr) :
    L.IsProp (neM κ ls) (ctx3 u Γ) (.forallE (majTy u) resTy) := by
  rw [isProp_iff hle (hasType_recB3 hu Γ) (u := .imax .zero .zero) ⟨trivial, trivial⟩]
  simp [VLevel.eval, Lean.Nat.imax]

include hle in
theorem isProp_resTy (Γ : List VExpr) :
    L.IsProp (neM κ ls) (ctx4 u Γ) resTy := by
  rw [isProp_iff hle (hasType_resTy Γ) (u := .zero) trivial]
  simp [VLevel.eval]

include hu hle in
theorem isProp_minBody (Γ : List VExpr) :
    L.IsProp (neM κ ls) (ctxM u Γ)
      (.app (.bvar 1) (.app (.app (.const ``Nonempty.intro [u]) (.bvar 2)) (.bvar 0))) := by
  rw [isProp_iff hle (hasType_minBody hu Γ) (u := .zero) trivial]
  simp [VLevel.eval]

include hu hle in
theorem isProp_introB1 (Γ : List VExpr) :
    L.IsProp (neM κ ls) (ctx1 u Γ)
      (.forallE (.bvar 0) (.app (.const ``Nonempty [u]) (.bvar 1))) := by
  rw [isProp_iff hle (hasType_introB1 hu Γ) (u := .imax u .zero) ⟨hu, trivial⟩]
  simp [VLevel.eval, Lean.Nat.imax]

include hu hle in
theorem isProp_NEapp1_ctxI (Γ : List VExpr) :
    L.IsProp (neM κ ls) (ctxI u Γ) (.app (.const ``Nonempty [u]) (.bvar 1)) := by
  rw [isProp_iff hle (hasType_NEapp1_ctxI hu Γ) (u := .zero) trivial]
  simp [VLevel.eval]

include hu hle in
theorem isProp_ruleB1 (Γ : List VExpr) :
    L.IsProp (neM κ ls) (ctx1 u Γ)
      (.forallE (motTy u) (.forallE (minTy u) (.forallE (.bvar 2)
        (.app (.bvar 2) (.app (.app (.const ``Nonempty.intro [u]) (.bvar 3)) (.bvar 0)))))) := by
  rw [isProp_iff hle (hasType_ruleB1 hu Γ)
    (u := .imax (.imax .zero (.succ .zero)) (.imax (.imax u .zero) (.imax u .zero)))
    ⟨⟨trivial, trivial⟩, ⟨hu, trivial⟩, hu, trivial⟩]
  simp [VLevel.eval, Lean.Nat.imax]

include hu hle in
theorem isProp_ruleB2 (Γ : List VExpr) :
    L.IsProp (neM κ ls) (ctx2 u Γ)
      (.forallE (minTy u) (.forallE (.bvar 2)
        (.app (.bvar 2) (.app (.app (.const ``Nonempty.intro [u]) (.bvar 3)) (.bvar 0))))) := by
  rw [isProp_iff hle (hasType_ruleB2 hu Γ)
    (u := .imax (.imax u .zero) (.imax u .zero)) ⟨⟨hu, trivial⟩, hu, trivial⟩]
  simp [VLevel.eval, Lean.Nat.imax]

include hu hle in
theorem isProp_ruleB3 (Γ : List VExpr) :
    L.IsProp (neM κ ls) (ctx3 u Γ)
      (.forallE (.bvar 2)
        (.app (.bvar 2) (.app (.app (.const ``Nonempty.intro [u]) (.bvar 3)) (.bvar 0)))) := by
  rw [isProp_iff hle (hasType_ruleB3 hu Γ) (u := .imax u .zero) ⟨hu, trivial⟩]
  simp [VLevel.eval, Lean.Nat.imax]

include hu hle in
theorem isProp_ruleBody (Γ : List VExpr) :
    L.IsProp (neM κ ls) (ctxF u Γ)
      (.app (.bvar 2) (.app (.app (.const ``Nonempty.intro [u]) (.bvar 3)) (.bvar 0))) := by
  rw [isProp_iff hle (hasType_ruleBody hu Γ) (u := .zero) trivial]
  simp [VLevel.eval]

include hu hle in
/-- **The left-hand side of the ι-rule is a proof.** -/
theorem isProof_lhsLam (Γ : List VExpr) :
    L.IsProof (neM κ ls) (ctx1 u Γ)
      (.lam (motTy u) (.lam (minTy u) (.lam (.bvar 2)
        (.app (.app (.app (.app (.const recN [u]) (.bvar 3)) (.bvar 2)) (.bvar 1))
          (.app (.app (.const ``Nonempty.intro [u]) (.bvar 3)) (.bvar 0)))))) := by
  rw [isProof_iff hle (hasType_lhsLam hu Γ) (hasType_ruleB1 hu Γ)
    (u := .imax (.imax .zero (.succ .zero)) (.imax (.imax u .zero) (.imax u .zero)))
    ⟨⟨trivial, trivial⟩, ⟨hu, trivial⟩, hu, trivial⟩]
  simp [VLevel.eval, Lean.Nat.imax]

include hu hle in
/-- **…and so is the right-hand side**, the η-expanded β-redex `iotaRule` builds. -/
theorem isProof_rhsLam (Γ : List VExpr) :
    L.IsProof (neM κ ls) (ctx1 u Γ)
      (.lam (motTy u) (.lam (minTy u) (.lam (.bvar 2)
        (.app (.app (.app (.app (iotaLamE u) (.bvar 3)) (.bvar 2)) (.bvar 1)) (.bvar 0))))) := by
  rw [isProof_iff hle (hasType_rhsLam hu Γ) (hasType_ruleB1 hu Γ)
    (u := .imax (.imax .zero (.succ .zero)) (.imax (.imax u .zero) (.imax u .zero)))
    ⟨⟨trivial, trivial⟩, ⟨hu, trivial⟩, hu, trivial⟩]
  simp [VLevel.eval, Lean.Nat.imax]

end Split

/-! ## 7. The denotations, and the three `OracleOK`s -/

section Interp

variable {envF : VEnv} {nv : ℕ} (L : PropSplit envF nv) (κ : ℕ → V) (ls : List ℕ)
variable {u : VLevel} (hu : u.WF nv) (hle : nonemptyEnv ≤ envF)

theorem interp_sortu (Γ : List VExpr) (ρ : V) :
    (interp (neM κ ls) L Γ (.sort u)).toFun ρ = U κ (u.eval ls) := interp_sort ..

theorem interp_sort_zero' (Γ : List VExpr) (ρ : V) :
    (interp (neM κ ls) L Γ (.sort .zero)).toFun ρ = (UProp : V) := by
  rw [interp_sort]; exact U_zero ..

include hu hle in
/-- `⟦Nonempty (bvar i)⟧ρ = nonemptyFn κ n ‘ (ρ ‘ …)`. -/
theorem interp_NEapp (Γ : List VExpr) (i : ℕ) (ρ : V) :
    (interp (neM κ ls) L Γ (.app (.const ``Nonempty [u]) (.bvar i))).toFun ρ
      = (nonemptyFn κ (u.eval ls)) ‘ (ρ ‘ ((Γ.length - 1 - i : ℕ) : V)) := by
  rw [interp_app_type _ L (not_isProof_NE L κ ls hu hle Γ), interp_const, interp_bvar,
    neM_cnst_NE]

/-! ### The type former -/

omit hu hle in
/-- **`Nonempty.{u} : ∀ α : Sort u, Prop`.**  Its value is a genuine internal *function* —
the type former's type is not a proposition, so `•` is not a legal value here (contrast
`boxDecl`, where the domain was empty, and `Unit1`, which has no parameter at all). -/
theorem mem_interp_NE_type :
    neOracle κ ls ``Nonempty [u] ∈
      (interp (neM κ ls) L []
        ((⟨1, .forallE (.sort (.param 0)) (.sort .zero)⟩ : VConstant).type.instL [u])).toFun ∅ := by
  rw [show ((⟨1, .forallE (.sort (.param 0)) (.sort .zero)⟩ : VConstant).type.instL [u])
      = VExpr.forallE (.sort u) (.sort .zero) from rfl,
    interp_forallE_type _ L (not_isProp_sort_zero _), neOracle_NE]
  unfold nonemptyFn
  refine UnitAudit.mkLam_mem_mkForallType_of_dom (by rw [interp_sortu L κ ls]) (fun v _ ↦ ?_)
  rw [interp_sort_zero' L κ ls]
  split
  · exact empty_mem_UProp
  · exact true_mem_UProp

/-! ### The constructor -/

include hu hle in
/-- **`Nonempty.intro.{u} : ∀ (α : Sort u) (val : α), Nonempty α`.**  Its value is `•`,
and the membership is where the squash's *positive* direction is spent: a `val` in `α`
witnesses `α ≠ ∅`, hence `nonemptyFn κ n ‘ α = {•}`. -/
theorem mem_interp_NE_intro :
    neOracle κ ls ``Nonempty.intro [u] ∈
      (interp (neM κ ls) L []
        ((⟨1, .forallE (.sort (.param 0))
            (.forallE (.bvar 0) (.app (.const ``Nonempty [.param 0]) (.bvar 1)))⟩
          : VConstant).type.instL [u])).toFun ∅ := by
  rw [show ((⟨1, .forallE (.sort (.param 0))
        (.forallE (.bvar 0) (.app (.const ``Nonempty [.param 0]) (.bvar 1)))⟩
      : VConstant).type.instL [u])
      = VExpr.forallE (.sort u)
        (.forallE (.bvar 0) (.app (.const ``Nonempty [u]) (.bvar 1))) from rfl,
    neOracle_intro]
  refine (mem_interp_forallE_prop_iff _ L
    (isProp_introB1 L κ ls hu hle [])).2 ⟨rfl, fun α hα ↦ ?_⟩
  rw [interp_sortu L κ ls] at hα
  refine (mem_interp_forallE_prop_iff _ L
    (isProp_NEapp1_ctxI L κ ls hu hle [])).2 ⟨rfl, fun v hv ↦ ?_⟩
  rw [interp_bvar] at hv
  have h0 : (snoc (∅ : V) α) ‘ ((0 : ℕ) : V) = α := isSeq_empty.read_top
  simp only [List.length_cons, List.length_nil] at hv
  rw [show (0 + 1 - 1 - 0 : ℕ) = 0 from rfl, h0] at hv
  rw [interp_NEapp L κ ls hu hle]
  simp only [List.length_cons, List.length_nil]
  rw [show (1 + 1 - 1 - 1 : ℕ) = 0 from rfl,
    (isSeq_empty.snoc' (v := α)).read_lt (n := 1) (j := 0) (by omega), h0,
    nonemptyFn_value hα, if_neg (fun h : α = ∅ ↦ absurd (h ▸ hv) not_mem_empty)]
  exact mem_singleton_iff.2 rfl


/-! ### Reading the environment: the four snoc chains -/

theorem read1 {α : V} : (snoc (∅ : V) α) ‘ ((0 : ℕ) : V) = α := isSeq_empty.read_top

theorem read2_0 {α f : V} : (snoc (snoc (∅ : V) α) f) ‘ ((0 : ℕ) : V) = α :=
  (isSeq_empty.snoc'.read_lt (by omega)).trans read1

theorem read2_1 {α f : V} : (snoc (snoc (∅ : V) α) f) ‘ ((1 : ℕ) : V) = f :=
  isSeq_empty.snoc'.read_top

theorem read3_0 {α f m : V} : (snoc (snoc (snoc (∅ : V) α) f) m) ‘ ((0 : ℕ) : V) = α :=
  (isSeq_empty.snoc'.snoc'.read_lt (by omega)).trans read2_0

theorem read3_1 {α f m : V} : (snoc (snoc (snoc (∅ : V) α) f) m) ‘ ((1 : ℕ) : V) = f :=
  (isSeq_empty.snoc'.snoc'.read_lt (by omega)).trans read2_1

theorem read4_1 {α f m t : V} :
    (snoc (snoc (snoc (snoc (∅ : V) α) f) m) t) ‘ ((1 : ℕ) : V) = f :=
  (isSeq_empty.snoc'.snoc'.snoc'.read_lt (by omega)).trans read3_1

theorem read4_3 {α f m t : V} :
    (snoc (snoc (snoc (snoc (∅ : V) α) f) m) t) ‘ ((3 : ℕ) : V) = t :=
  isSeq_empty.snoc'.snoc'.snoc'.read_top

/-! ### The minor premise's denotation -/

include hu hle in
/-- `⟦motive (Nonempty.intro α val)⟧ = f ‘ •`: the constructor application is a *proof*, so
`interp` discards `val` and the motive is read at `•`. -/
theorem interp_minBody_val (α f v : V) :
    (interp (neM κ ls) L (ctxM u [])
        (.app (.bvar 1)
          (.app (.app (.const ``Nonempty.intro [u]) (.bvar 2)) (.bvar 0)))).toFun
      (snoc (snoc (snoc (∅ : V) α) f) v) = f ‘ (pt : V) := by
  rw [interp_app_type _ L (not_isProof_bvar1_ctxM L κ ls hu hle []),
    interp_app_proof _ L (isProof_introApp_ctxM L κ ls hu hle []), interp_bvar]
  simp only [List.length_cons, List.length_nil]
  rw [show (2 + 1 - 1 - 1 : ℕ) = 1 from rfl, read3_1]

omit hu hle in
theorem interp_minTy_dom (α f : V) :
    (interp (neM κ ls) L (ctx2 u []) (.bvar 1)).toFun (snoc (snoc (∅ : V) α) f) = α := by
  rw [interp_bvar]
  simp only [List.length_cons, List.length_nil]
  rw [show (1 + 1 - 1 - 1 : ℕ) = 0 from rfl, read2_0]

include hu hle in
/-- **What the minor premise gives**: at any `val ∈ α`, the motive holds at `•`. -/
theorem pt_mem_f_pt_of_mem_interp_minTy {α f m : V}
    (hm : m ∈ (interp (neM κ ls) L (ctx2 u []) (minTy u)).toFun (snoc (snoc (∅ : V) α) f))
    {v : V} (hv : v ∈ α) : (pt : V) ∈ f ‘ (pt : V) := by
  obtain ⟨rfl, h⟩ :=
    (mem_interp_forallE_prop_iff _ L (isProp_minBody L κ ls hu hle [])).1 hm
  have h2 := h v (by rw [interp_minTy_dom L κ ls]; exact hv)
  rwa [interp_minBody_val L κ ls hu hle] at h2

/-! ### The recursor -/

include hu hle in
/-- **`Nonempty.rec.{u}`**, the field the squash's *negative* direction pays for.  The
recursor type is a proposition (`isLE := false`), so its value is `•`; the membership needs
`⟦Nonempty α⟧ = {•} → α ≠ ∅`, i.e. exactly that `nonemptyFn` is a *faithful* squash.  A
constant-true `Nonempty` satisfies the constructor and **fails here** (§9). -/
theorem pt_mem_interp_NE_recType :
    (pt : V) ∈
      (interp (neM κ ls) L [] ((nonemptyIndDecl.recType 0).instL [u])).toFun ∅ := by
  rw [ne_recType_instL]
  refine (mem_interp_forallE_prop_iff _ L
    (isProp_recB1 L κ ls hu hle [])).2 ⟨rfl, fun α hα ↦ ?_⟩
  rw [interp_sortu L κ ls] at hα
  refine (mem_interp_forallE_prop_iff _ L
    (isProp_recB2 L κ ls hu hle [])).2 ⟨rfl, fun f _ ↦ ?_⟩
  refine (mem_interp_forallE_prop_iff _ L
    (isProp_recB3 L κ ls hu hle [])).2 ⟨rfl, fun m hm ↦ ?_⟩
  refine (mem_interp_forallE_prop_iff _ L
    (isProp_resTy L κ ls hle [])).2 ⟨rfl, fun t ht ↦ ?_⟩
  -- the major premise's domain is `nonemptyFn κ n ‘ α`
  rw [show (majTy u) = VExpr.app (.const ``Nonempty [u]) (.bvar 2) from rfl,
    interp_NEapp L κ ls hu hle] at ht
  simp only [List.length_cons, List.length_nil] at ht
  rw [show (2 + 1 - 1 - 2 : ℕ) = 0 from rfl, read3_0, nonemptyFn_value hα] at ht
  by_cases hα0 : α = ∅
  · rw [if_pos hα0] at ht; exact absurd ht not_mem_empty
  rw [if_neg hα0] at ht
  obtain rfl : t = (pt : V) := mem_singleton_iff.mp ht
  obtain ⟨v, hv⟩ := ne_empty_iff_isNonempty.mp hα0
  -- the goal is `• ∈ f ‘ t`
  rw [show resTy = VExpr.app (.bvar 2) (.bvar 0) from rfl,
    interp_app_type _ L (not_isProof_bvar2_ctx4 L κ ls hu hle []), interp_bvar, interp_bvar]
  simp only [List.length_cons, List.length_nil]
  rw [show (3 + 1 - 1 - 2 : ℕ) = 1 from rfl, show (3 + 1 - 1 - 0 : ℕ) = 3 from rfl,
    read4_1, read4_3]
  exact pt_mem_f_pt_of_mem_interp_minTy L κ ls hu hle hm hv


/-! ### The ι-rule `Nonempty.rec α motive minor (Nonempty.intro α val) ≡ minor val`

Both sides are λ-nests whose body is a **proof** — its type `motive (Nonempty.intro α val)`
is a proposition — so `interp`'s `lam` clause returns `•` on both and the equation needs no
β-computation.  That is *not* the empty-domain collapse of `boxDecl`: every domain here is
inhabited whenever `α` is, and the reason the two sides agree is proof irrelevance. -/

include hu hle in
theorem interp_neRule_lhs :
    (interp (neM κ ls) L [] ((nonemptyIndDecl.iotaRule 0 0 neCtor).lhs.instL [u])).toFun ∅
      = (pt : V) := by
  rw [neRule_lhs_instL]
  exact interp_lam_proof _ L (isProof_lhsLam L κ ls hu hle []) ∅

include hu hle in
theorem interp_neRule_rhs :
    (interp (neM κ ls) L [] ((nonemptyIndDecl.iotaRule 0 0 neCtor).rhs.instL [u])).toFun ∅
      = (pt : V) := by
  rw [neRule_rhs_instL]
  exact interp_lam_proof _ L (isProof_rhsLam L κ ls hu hle []) ∅

include hu hle in
/-- `•` inhabits the ι-rule's type — four impredicative `∀`s, and the last step is the minor
premise applied at the `val` the last binder supplies. -/
theorem pt_mem_interp_neRule_type :
    (pt : V) ∈
      (interp (neM κ ls) L []
        ((nonemptyIndDecl.iotaRule 0 0 neCtor).type.instL [u])).toFun ∅ := by
  rw [neRule_type_instL]
  refine (mem_interp_forallE_prop_iff _ L
    (isProp_ruleB1 L κ ls hu hle [])).2 ⟨rfl, fun α hα ↦ ?_⟩
  rw [interp_sortu L κ ls] at hα
  refine (mem_interp_forallE_prop_iff _ L
    (isProp_ruleB2 L κ ls hu hle [])).2 ⟨rfl, fun f _ ↦ ?_⟩
  refine (mem_interp_forallE_prop_iff _ L
    (isProp_ruleB3 L κ ls hu hle [])).2 ⟨rfl, fun m hm ↦ ?_⟩
  refine (mem_interp_forallE_prop_iff _ L
    (isProp_ruleBody L κ ls hu hle [])).2 ⟨rfl, fun v hv ↦ ?_⟩
  rw [interp_bvar] at hv
  simp only [List.length_cons, List.length_nil] at hv
  rw [show (2 + 1 - 1 - 2 : ℕ) = 0 from rfl, read3_0] at hv
  rw [interp_app_type _ L (not_isProof_bvar2_ctxF L κ ls hu hle []),
    interp_app_proof _ L (isProof_introApp_ctxF L κ ls hu hle []), interp_bvar]
  simp only [List.length_cons, List.length_nil]
  rw [show (3 + 1 - 1 - 2 : ℕ) = 1 from rfl, read4_1]
  exact pt_mem_f_pt_of_mem_interp_minTy L κ ls hu hle hm hv

/-! ## 8. `InductOracleOK` at `nonemptyIndDecl` -/

theorem eq_singleton_of_length_one {us : List VLevel} (h : us.length = 1) : ∃ w, us = [w] := by
  match us, h with
  | [w], _ => exact ⟨w, rfl⟩

omit hu hle in
/-- The oracle is level-congruent at `Nonempty`: its value depends on `us` only through
`(us.head).eval ls`, which `≈` preserves. -/
theorem neOracle_congr_NE {us us' : List VLevel} (hd : List.Forall₂ (· ≈ ·) us us') :
    neOracle κ ls ``Nonempty us = neOracle κ ls ``Nonempty us' := by
  rcases hd with _ | ⟨h, ht⟩
  · rfl
  rcases ht with _ | ⟨h2, ht2⟩
  · rw [neOracle_NE, neOracle_NE, VLevel.equiv_def.mp h ls]
  · rfl

omit hu hle in
/-- The type former's obligation needs **neither** `hle` nor the level's well-formedness:
`Prop` is not a proposition in any `PropSplit` (`not_isProp_sort_zero`), so the branch is
fixed without consulting the environment. -/
theorem oracleOK_NE_type :
    OracleOK L κ ls (neOracle κ ls) (neOracle κ ls) ``Nonempty
      ⟨1, .forallE (.sort (.param 0)) (.sort .zero)⟩ := by
  refine oracleOK_of (fun _ _ hd ↦ neOracle_congr_NE κ ls hd) (fun {us} hw hlen ↦ ?_)
  obtain ⟨w, rfl⟩ := eq_singleton_of_length_one hlen
  exact mem_interp_NE_type L κ ls

include hle in
theorem oracleOK_NE_intro :
    OracleOK L κ ls (neOracle κ ls) (neOracle κ ls) ``Nonempty.intro
      ⟨1, .forallE (.sort (.param 0))
        (.forallE (.bvar 0) (.app (.const ``Nonempty [.param 0]) (.bvar 1)))⟩ := by
  refine oracleOK_of (fun _ _ _ ↦ by rw [neOracle_intro, neOracle_intro])
    (fun {us} hw hlen ↦ ?_)
  obtain ⟨w, rfl⟩ := eq_singleton_of_length_one hlen
  rw [neOracle_intro]
  exact mem_interp_NE_intro L κ ls (hw w (by simp)) hle

include hle in
theorem oracleOK_NE_rec :
    OracleOK L κ ls (neOracle κ ls) (neOracle κ ls) recN ⟨1, nonemptyIndDecl.recType 0⟩ := by
  refine oracleOK_of (fun _ _ _ ↦ by rw [neOracle_rec, neOracle_rec]) (fun {us} hw hlen ↦ ?_)
  obtain ⟨w, rfl⟩ := eq_singleton_of_length_one hlen
  rw [neOracle_rec]
  exact pt_mem_interp_NE_recType L κ ls (hw w (by simp)) hle

include hle in
/-- **The `consts` field, all three constants.**  `Above`-free: every proof goes through
`Above.pure`, at an arbitrary `κ`, so no chain condition is used anywhere. -/
theorem inductOracleOK_consts_NE :
    ∀ p ∈ nonemptyIndDecl.allConsts,
      OracleOK L κ ls (neOracle κ ls) (neOracle κ ls) p.1 p.2 := by
  intro p hp
  rw [ne_allConsts] at hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  obtain rfl | rfl | rfl := hp
  · exact oracleOK_NE_type L κ ls
  · exact oracleOK_NE_intro L κ ls hle
  · exact oracleOK_NE_rec L κ ls hle

include hle in
/-- **The `rules` field.**  One ι-rule; both sides are `•`, and `•` lies in its type. -/
theorem inductOracleOK_rules_NE :
    ∀ df ∈ nonemptyIndDecl.iotaRules, DefEqOK L (neM κ ls) df := by
  intro df hdf
  rw [ne_iotaRules] at hdf
  simp only [List.mem_singleton] at hdf
  subst hdf
  intro us hw hlen
  obtain ⟨w, rfl⟩ := eq_singleton_of_length_one hlen
  have hw' : w.WF nv := hw w (by simp)
  refine ⟨Above.pure ?_, Above.pure ?_⟩
  · rw [interp_neRule_lhs L κ ls hw' hle, interp_neRule_rhs L κ ls hw' hle]
  · rw [interp_neRule_lhs L κ ls hw' hle]
    exact pt_mem_interp_neRule_type L κ ls hw' hle

include hle in
/-- **`InductOracleOK` at a prelude block.**  `nonemptyIndDecl` is `VInductDecl'.WF`
(`nonemptyIndDecl_WF`), sits on the certified prelude history (`preludeEnv_history`), has a
**nonempty parameter telescope** and a constructor with a **field**, and the oracle is
`PreludeSpec.lean`'s own joint witness, unchanged. -/
theorem inductOracleOK_NE :
    InductOracleOK L κ ls (neOracle κ ls) (neOracle κ ls) nonemptyIndDecl :=
  ⟨inductOracleOK_consts_NE L κ ls hle, inductOracleOK_rules_NE L κ ls hle⟩

end Interp

end Model



/-! ## 9. The measurements

Three separate things have to be checked, and this directory's own trap list
(`docs/handoff-setmodel.md` §7.8) names all three.  `Above` must not be doing the work; the
block must not be degenerate; and the hypotheses must be satisfiable at an environment the
recursion actually visits. -/

section Measure

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ} (L : PropSplit envF nv) (κ : ℕ → V) (ls : List ℕ)

/-! ### `Above` is not doing the work

`Above M P := ∃ m, IsInaccessibleChain m M.κ → P`, so it is trivially true at a `κ` that is
not a chain of every finite length (`not_isInaccessibleChain_const`).  Every field of
`OracleOK` and `DefEqOK` is an `Above`, so a positive bound stated only through them would
say nothing.  These are §7–§8's obligations with the wrapper **removed**, at an arbitrary
`κ`, with no chain hypothesis anywhere. -/

/-- **The `consts` obligation, `Above`-free.** -/
theorem mem_interp_consts_NE (hle : nonemptyEnv ≤ envF) :
    ∀ p ∈ nonemptyIndDecl.allConsts, ∀ w : VLevel, w.WF nv →
      neOracle κ ls p.1 [w] ∈
        (interp (neM κ ls) L [] (p.2.type.instL [w])).toFun ∅ := by
  intro p hp w hw
  rw [ne_allConsts] at hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  obtain rfl | rfl | rfl := hp
  · exact mem_interp_NE_type L κ ls
  · exact mem_interp_NE_intro L κ ls hw hle
  · rw [show neOracle κ ls recN [w] = (pt : V) from neOracle_rec _]
    exact pt_mem_interp_NE_recType L κ ls hw hle

/-- **The `rules` obligation, `Above`-free**: the two sides are *equal*, and the common
value lies in the equated type, with no threshold. -/
theorem defEq_rules_NE (hle : nonemptyEnv ≤ envF) :
    ∀ df ∈ nonemptyIndDecl.iotaRules, ∀ w : VLevel, w.WF nv →
      (interp (neM κ ls) L [] (df.lhs.instL [w])).toFun ∅
          = (interp (neM κ ls) L [] (df.rhs.instL [w])).toFun ∅ ∧
        (interp (neM κ ls) L [] (df.lhs.instL [w])).toFun ∅
          ∈ (interp (neM κ ls) L [] (df.type.instL [w])).toFun ∅ := by
  intro df hdf w hw
  rw [ne_iotaRules] at hdf
  simp only [List.mem_singleton] at hdf
  subst hdf
  refine ⟨?_, ?_⟩
  · rw [interp_neRule_lhs L κ ls hw hle, interp_neRule_rhs L κ ls hw hle]
  · rw [interp_neRule_lhs L κ ls hw hle]
    exact pt_mem_interp_neRule_type L κ ls hw hle

/-! ### The block is not degenerate

`boxDecl` met the residual because its parameter denoted `∅`; `unitDecl` has no parameter and
no field at all.  `nonemptyIndDecl` has both, and its parameter's denotation is a *universe*. -/

/-- A **nonempty parameter telescope** — contrast `UnitOracleWitness.unitDecl_params_nil`. -/
theorem ne_params : nonemptyIndDecl.params = [.sort (.param 0)] := rfl

/-- …and a constructor with a **field**, which is what makes the block a genuine squash —
contrast `unitCtor.fields = []` and `boxDecl`'s constructor. -/
theorem neCtor_fields : neCtor.fields = [{ type := .bvar 0, lvl := .param 0, recArg := none }] :=
  rfl

/-- The parameter's denotation is a **universe**, not `∅`: at `u := .zero` it is `U₀ = ℘{•}`,
which has two elements.  So none of `InductOracleWitness.lean`'s three empty-domain lemmas
applies to any binder here. -/
theorem interp_param_ne_empty :
    (interp (neM κ ls) L [] (.sort (.zero : VLevel))).toFun ∅ ≠ (∅ : V) := by
  rw [interp_sort_zero' L κ ls]
  intro h
  exact absurd (h ▸ (empty_mem_UProp : (∅ : V) ∈ (UProp : V))) not_mem_empty

/-- **Both branches of the squash fire.**  `nonemptyFn` is not constantly true nor constantly
false: at `U₀`, where every carrier is `∅` or `{•}`, it separates them.  This is the property
the recursor's obligation consumes (§7), and the reason a level-uniform constant value is not
available. -/
theorem nonemptyFn_zero_empty : (nonemptyFn κ 0) ‘ (∅ : V) = (∅ : V) := by
  rw [nonemptyFn_value (by rw [U_zero]; exact empty_mem_UProp), if_pos rfl]

theorem nonemptyFn_zero_true : (nonemptyFn κ 0) ‘ ({pt} : V) = ({pt} : V) := by
  rw [nonemptyFn_value (by rw [U_zero]; exact true_mem_UProp),
    if_neg (fun h : ({pt} : V) = ∅ ↦ empty_ne_singleton_pt h.symm)]

/-- **A negative bound, `Above`-free: the oracle that carried `boxDecl` fails here.**
`InductOracleWitness.lean` met the whole residual with `zeroOracle = fun _ _ ↦ ∅`; at
`Nonempty.{0} : Prop → Prop` that value is not even in the type former's denotation, because
`∀ α : Prop, Prop` is a *function space* over the nonempty domain `U₀` and `∅ = •` is not a
function on a nonempty domain.  So this file's oracle is not a re-run of that trick.

Stated on the field's **body** rather than on `OracleOK` itself: `OracleOK.type` is an
`Above`, and refuting an `Above` would need a chain hypothesis on `κ` — the same asymmetry
`InductOracleAudit.lean` §5 records for the `rules` cell. -/
theorem not_mem_interp_zeroOracle_NE_type :
    zeroOracle V ``Nonempty [(.zero : VLevel)] ∉
      (interp (⟨κ, ls, zeroOracle V⟩ : ModelData V) L []
        (VExpr.forallE (.sort .zero) (.sort .zero))).toFun ∅ := by
  rw [interp_forallE_type _ L (not_isProp_sort_zero _)]
  show (pt : V) ∉ _
  refine UnitAudit.pt_not_mem_mkForallType_of_nonempty (x := ∅) ?_
  show (∅ : V) ∈ (interp (⟨κ, ls, zeroOracle V⟩ : ModelData V) L [] (.sort (.zero : VLevel))).toFun ∅
  rw [interp_sort]
  show (∅ : V) ∈ (U κ 0 : V)
  rw [U_zero]
  exact empty_mem_UProp

end Measure

/-! ## 10. At the named environment `preludeEnv`

The hypothesis `hle : nonemptyEnv ≤ envF` is satisfiable at the environment the prelude
recursion actually reaches, and `PreludeWitness.lean` names it. -/

section AtPrelude

/-- `nonemptyEnv ≤ preludeEnv`, by the three `VDecl.WF` steps that separate them
(`.axiom Classical.choice`, `.quot`, `.axiom Quot.sound`).  Every one of the three is a
theorem of `PreludeWitness.lean`. -/
theorem nonemptyEnv_le_choiceEnv : nonemptyEnv ≤ choiceEnv :=
  VDecl.WF.le (d := .axiom choiceConst) (.axiom choiceConst_WF choiceEnv_add)

theorem choiceEnv_le_quotEnv : choiceEnv ≤ quotEnv :=
  VDecl.WF.le (d := .quot) (.quot choiceEnv_quotReady quotEnv_add)

theorem quotEnv_le_preludeEnv : quotEnv ≤ preludeEnv :=
  VDecl.WF.le (d := .axiom quotSoundConst) (.axiom quotSoundConst_WF preludeEnv_add)

theorem nonemptyEnv_le_preludeEnv : nonemptyEnv ≤ preludeEnv :=
  VEnv.LE.trans nonemptyEnv_le_choiceEnv
    (VEnv.LE.trans choiceEnv_le_quotEnv quotEnv_le_preludeEnv)

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]

/-- **`InductOracleOK` at `preludeEnv`.**  The `.induct nonemptyIndDecl` step of the *actual*
prelude — the block Lean declares, on the history `preludeEnv_history` certifies — with the
oracle `PreludeSpec.lean` built for the standard axioms.

What is still quantified is `L : PropSplit preludeEnv nv`, and §11 measures exactly what that
costs. -/
theorem inductOracleOK_NE_at_preludeEnv {nv : ℕ} (L : PropSplit preludeEnv nv)
    (κ : ℕ → V) (ls : List ℕ) :
    InductOracleOK L κ ls (neOracle κ ls) (neOracle κ ls) nonemptyIndDecl :=
  inductOracleOK_NE L κ ls nonemptyEnv_le_preludeEnv

end AtPrelude

/-! ## 11. The parameter that is **not** known inhabited, and what it is

Every `.induct` witness in this directory — `inductOracleOK_zero`, `inductOracleOK_unit`,
`inductOracleOKL`, and §8 above — is stated for an arbitrary `L : PropSplit envF nv`, and
`docs/vacuity-ledger.md` §0's eighth blindness applies verbatim: **no declaration in this
tree constructs a `PropSplit` at any environment.**  The only three producers are
`PropSplitAudit.propSplitOf`, `PropSplitUp.propSplitUp` and `Interp.LevelAssign.toPropSplit`,
and the first two take `PropUniq` and `PropTypeAgree` as hypotheses while the third takes a
`LevelAssign`, which nothing constructs either.

That is not a defect of the witness — `coherentOn_cnstOf` quantifies over the same `L` — but
it *is* the reason the two open items of `docs/handoff-setmodel.md` §9.7 are one item.  The
statement below is `NotProofNoModel.nonempty_propSplit_iff_agree` at the named environment,
and it says: `PropTypeAgree preludeEnv 0` is precisely the missing half of the inhabitation
of the parameter that every `.induct` oracle result at the prelude is quantified over. -/

section Vacuity

/-- **The parameter of §10, pinned at `preludeEnv`.** -/
theorem nonempty_propSplit_preludeEnv_iff :
    Nonempty (PropSplit preludeEnv 0) ↔
      preludeEnv.PropUniq 0 ∧ preludeEnv.PropTypeAgree 0 :=
  nonempty_propSplit_iff_agree

/-- …and its `PropUniq` half is free wherever the reduction is consumed: `env.Consistent` is
a negation, so the goal's own inhabitant of `∀ p : Prop, p` feeds
`PropUniq.of_propTypeAgree`.  So at the point of use the *whole* content of "§10 is not
vacuous" is `PropTypeAgree preludeEnv 0` — `UpperBound.PropTypeAgreeInput`'s instance at the
witness environment, and nothing else. -/
theorem nonempty_propSplit_preludeEnv_of_propTypeAgree
    (hT : preludeEnv.PropTypeAgree 0) (hf : ∃ e, preludeEnv.HasType 0 [] e falseProp) :
    Nonempty (PropSplit preludeEnv 0) :=
  nonempty_propSplit_preludeEnv_iff.2
    ⟨VEnv.PropUniq.of_propTypeAgree preludeEnv_ordered hf hT, hT⟩

/-- The same statement one level up: the input of `UpperBound.lean` delivers it. -/
theorem propTypeAgree_preludeEnv_of_input (h : PropTypeAgreeInput) :
    preludeEnv.PropTypeAgree 0 := propTypeAgree_of_input h

end Vacuity


/-! ## 12. The step, at its position in the prelude

§10 discharges `InductOracleOK` at the oracle `neOracle` itself.  `OracleFits` states the
obligation at `cnstOf` applied to the *tail* of the declaration list, so the two are the same
statement only once `cnstOf` is computed.  It is: the prelude's first four steps assign
exactly `Eq`, `Eq.refl`, `Eq.rec`, `Iff`, `Iff.intro`, `Iff.rec`, `propext`, `Nonempty`,
`Nonempty.intro` and `Nonempty.rec`, and `neOracle` is `∅` at every other name, so the fold
reproduces it. -/

section Step

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ} (L : PropSplit envF nv) (κ : ℕ → V) (ls : List ℕ)

omit [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
theorem cnstUpdate_apply (c : Name → List VLevel → V) (n : Name) (v : List VLevel → V)
    (m : Name) (us : List VLevel) :
    cnstUpdate c n v m us = if m = n then v us else c m us := by
  by_cases h : m = n <;> simp [cnstUpdate, h]

omit [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
/-- `oracleExtend` is a lookup in the name list. -/
theorem oracleExtend_apply (o : Name → List VLevel → V) :
    ∀ (ns : List Name) (c : Name → List VLevel → V) (m : Name) (us : List VLevel),
      oracleExtend o ns c m us = if m ∈ ns then o m us else c m us
  | [], _, _, _ => by simp [oracleExtend]
  | n :: ns, c, m, us => by
    rw [show oracleExtend o (n :: ns) c = oracleExtend o ns (cnstUpdate c n (o n)) from rfl,
      oracleExtend_apply o ns]
    by_cases h1 : m ∈ ns
    · simp [h1]
    by_cases h2 : m = n
    · subst h2; simp [h1, cnstUpdate]
    · simp [h1, h2, cnstUpdate]

/-- The prelude's declaration list, reversed, from the `.induct nonemptyIndDecl` step down. -/
abbrev preludeTail : List VDecl :=
  [.induct nonemptyIndDecl, .axiom propextConst, .induct iffIndDecl, .induct eqIndDecl]

theorem preludeTail_eq : (preludeTail : List VDecl) = leanPrelude.reverse.drop 3 := rfl

/-- `neOracle` is `∅` off the ten names the prelude's first four steps declare. -/
theorem neOracle_eq_empty_of_not_mem {m : Name} (h1 : m ≠ ``Eq) (h2 : m ≠ ``Iff)
    (h3 : m ≠ ``Nonempty) (us : List VLevel) : neOracle κ ls m us = (∅ : V) := by
  simp [neOracle, preludeWitness, h1, h2, h3]

/-- **`cnstOf` at the prelude tail *is* the oracle.**  Every name the four steps declare is
set to `neOracle`'s value, and `neOracle` is `∅` — which is `cnstOf …  []` — everywhere
else. -/
theorem cnstOf_preludeTail :
    cnstOf L κ ls (neOracle κ ls) preludeTail = neOracle κ ls := by
  funext m us
  show oracleExtend (neOracle κ ls) nonemptyIndDecl.allNames
      (cnstUpdate (cnstOf L κ ls (neOracle κ ls) [.induct iffIndDecl, .induct eqIndDecl])
        propextConst.name (neOracle κ ls propextConst.name)) m us = _
  rw [oracleExtend_apply]
  by_cases hn : m ∈ nonemptyIndDecl.allNames
  · rw [if_pos hn]
  rw [if_neg hn]
  rw [cnstUpdate_apply]
  by_cases hp : m = propextConst.name
  · rw [if_pos hp, hp]
  rw [if_neg hp]
  show oracleExtend (neOracle κ ls) iffIndDecl.allNames
      (cnstOf L κ ls (neOracle κ ls) [.induct eqIndDecl]) m us = _
  rw [oracleExtend_apply]
  by_cases hi : m ∈ iffIndDecl.allNames
  · rw [if_pos hi]
  rw [if_neg hi]
  show oracleExtend (neOracle κ ls) eqIndDecl.allNames
      (cnstOf L κ ls (neOracle κ ls) ([] : List VDecl)) m us = _
  rw [oracleExtend_apply]
  by_cases he : m ∈ eqIndDecl.allNames
  · rw [if_pos he]
  rw [if_neg he]
  show (∅ : V) = _
  refine (neOracle_eq_empty_of_not_mem κ ls ?_ ?_ ?_ us).symm
  · exact fun h ↦ he (by rw [h]; simp [eqIndDecl, VInductDecl'.allNames,
      VInductDecl'.allConsts, VInductDecl'.typeConsts])
  · exact fun h ↦ hi (by rw [h]; simp [iffIndDecl, VInductDecl'.allNames,
      VInductDecl'.allConsts, VInductDecl'.typeConsts])
  · exact fun h ↦ hn (by rw [h]; simp [nonemptyIndDecl, VInductDecl'.allNames,
      VInductDecl'.allConsts, VInductDecl'.typeConsts])

/-- **The oracle's obligation at the prelude's `.induct nonemptyIndDecl` step**, in the exact
form `OracleFits` asks for. -/
theorem oracleStepOK_NE (hle : nonemptyEnv ≤ envF) :
    OracleStepOK L κ ls (neOracle κ ls) (.induct nonemptyIndDecl)
      [.axiom propextConst, .induct iffIndDecl, .induct eqIndDecl] := by
  show InductOracleOK L κ ls (neOracle κ ls)
    (cnstOf L κ ls (neOracle κ ls) preludeTail) nonemptyIndDecl
  rw [cnstOf_preludeTail]
  exact inductOracleOK_NE L κ ls hle

/-- …and at `preludeEnv`, where `hle` is a theorem. -/
theorem oracleStepOK_NE_at_preludeEnv {nv : ℕ} (L : PropSplit preludeEnv nv)
    (κ : ℕ → V) (ls : List ℕ) :
    OracleStepOK L κ ls (neOracle κ ls) (.induct nonemptyIndDecl)
      [.axiom propextConst, .induct iffIndDecl, .induct eqIndDecl] :=
  oracleStepOK_NE L κ ls nonemptyEnv_le_preludeEnv

end Step


/-! ## 13. The two blocks that remain, measured rather than costed

`eqIndDecl` and `iffIndDecl` are the other two `.induct` steps of `leanPrelude`.  Everything
in this section is `rfl`, so it is a **measurement** of what they ask for, not an estimate.
The single structural fact that separates them from `nonemptyIndDecl` is `isLE`. -/

section Remaining

/-- `Nonempty` is a **small** eliminator, so its recursor's elimination universe is `.zero`
and its whole type is a proposition — which is why §7's oracle value is `•`. -/
theorem ne_isLE : nonemptyIndDecl.isLE = false := rfl
theorem ne_elimLvl : nonemptyIndDecl.elimLvl = .zero := rfl
theorem ne_recUvars' : nonemptyIndDecl.recUvars = 1 := rfl

/-- `Eq` and `Iff` are **large** eliminators: a fresh elimination universe is prepended, so
`recType 0`'s result is `Sort (param 0)`-valued and is *not* a proposition at an
instantiation with `u.eval ls ≠ 0`.  That is the whole difference, and it is the same
difference `UnitOracleLarge.lean` had to pay for `unitDeclLE`. -/
theorem eq_isLE : eqIndDecl.isLE = true := rfl
theorem iff_isLE : iffIndDecl.isLE = true := rfl
theorem eq_elimLvl : eqIndDecl.elimLvl = .param 0 := rfl
theorem iff_elimLvl : iffIndDecl.elimLvl = .param 0 := rfl
theorem eq_recUvars : eqIndDecl.recUvars = 2 := rfl
theorem iff_recUvars : iffIndDecl.recUvars = 1 := rfl

/-- **`Iff.rec`'s type, measured.**  Five binders before the result: two parameters, the
motive, one minor premise, the major premise. -/
theorem iff_recType :
    iffIndDecl.recType 0 =
      .forallE (.sort .zero) (.forallE (.sort .zero)
        (.forallE (.forallE (.app (.app (.const ``Iff []) (.bvar 1)) (.bvar 0))
            (.sort (.param 0)))
          (.forallE
            (.forallE (.forallE (.bvar 2) (.bvar 2)) (.forallE (.forallE (.bvar 2) (.bvar 4))
              (.app (.bvar 2)
                (.app (.app (.app (.app (.const ``Iff.intro []) (.bvar 4)) (.bvar 3))
                  (.bvar 1)) (.bvar 0)))))
            (.forallE (.app (.app (.const ``Iff []) (.bvar 3)) (.bvar 2))
              (.app (.bvar 2) (.bvar 0)))))) := rfl

/-- **`Eq.rec`'s type, measured.**  Six binders: two parameters, the motive (which is itself a
two-binder pi, over the index and the major premise), one minor premise, the index, the major
premise. -/
theorem eq_recType :
    eqIndDecl.recType 0 =
      .forallE (.sort (.param 1)) (.forallE (.bvar 0)
        (.forallE
          (.forallE (.bvar 1)
            (.forallE (.app (.app (.app (.const ``Eq [.param 1]) (.bvar 2)) (.bvar 1))
              (.bvar 0)) (.sort (.param 0))))
          (.forallE
            (.app (.app (.bvar 0) (.bvar 1))
              (.app (.app (.const ``Eq.refl [.param 1]) (.bvar 2)) (.bvar 1)))
            (.forallE (.bvar 3)
              (.forallE (.app (.app (.app (.const ``Eq [.param 1]) (.bvar 4)) (.bvar 3))
                (.bvar 0))
                (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0))))))) := rfl

/-- `Eq`'s block also carries an **index** (`Iff`'s and `Nonempty`'s do not), which is what
puts a second binder inside the motive. -/
theorem eq_indices : (eqIndDecl.types.getD 0 default).indices = [.bvar 1] := rfl
theorem iff_indices : (iffIndDecl.types.getD 0 default).indices = [] := rfl
theorem ne_indices : (nonemptyIndDecl.types.getD 0 default).indices = [] := rfl

/-- And `PreludeSpec.lean`'s witness assigns `∅` to both recursors, so it is **not** a
candidate oracle at either block: `preludeWitness` was written to satisfy `EqSpec`/`IffSpec`,
which constrain only the type formers.

*This is a fact about the assignment, not yet a refutation of `InductOracleOK` at those
blocks* — flagged as such, because an unproved negative is worse than an unproved positive
(`docs/vacuity-ledger.md` §0, kind 4).  What would refute it is the `mkForallType` argument of
`UnitOracleLarge.pt_not_mem_interpL_recType_of_ne` transported to a five- or six-binder
telescope, and that has **not** been done. -/
theorem preludeWitness_eqRec_empty {V : Type*} [SetStructure V] [Nonempty V]
    [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] (κ : ℕ → V) (ls : List ℕ) (us : List VLevel) :
    (preludeWitness κ ls).cnst ``Eq.rec us = (∅ : V) := by
  simp [preludeWitness]

theorem preludeWitness_iffRec_empty {V : Type*} [SetStructure V] [Nonempty V]
    [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] (κ : ℕ → V) (ls : List ℕ) (us : List VLevel) :
    (preludeWitness κ ls).cnst ``Iff.rec us = (∅ : V) := by
  simp [preludeWitness]

end Remaining


/-! ## 14. The level-layer gap in §11's missing hypothesis **closes at `nv = 0`**

`NotProofNoModel.lean` §6 records that the model's `PropTypeAgree` (pointwise in `ls`) and the
syntactic development's `IsPropN`-shaped statement (`u ≈ .zero`) *do not compose*: one
direction is `propTypeAgree_equivZero`, and the other is refuted by
`propAgree_pointwise_not_from_equivZero`, whose witness is `.param 0` / `.param 1` at
`WF 2`.

**That witness needs `nv ≥ 2`, and the only `nv` this corner uses is `0`.**
`UpperBound.PropTypeAgreeInput` is `PropTypeAgree env 0`, and `PropReduce.PropTypeAgree.of_zero`
lifts `0` to every `nv` with no hypothesis.  At `nv = 0` a `WF` level contains no `.param` at
all, so its evaluation is constant in `ls` and the two shapes are **equivalent**.

So the recorded non-composition is a statement about `nv ≥ 2` and does *not* apply to the
instance the reduction consumes.  What still separates the two streams is the
`HasTypeN U n` / `HasType nv` bridge and the fact that `PropTypeAgreeN` is itself open — not
the level layer. -/

section LevelLayer

/-- A `WF 0` level mentions no parameter, so its evaluation does not depend on the
valuation. -/
theorem eval_const_of_wf_zero : ∀ {u : VLevel}, u.WF 0 → ∀ ls ls' : List ℕ,
    u.eval ls = u.eval ls'
  | .zero, _, _, _ => rfl
  | .succ l, h, ls, ls' => by
    simp only [VLevel.eval]; rw [eval_const_of_wf_zero (u := l) h ls ls']
  | .max l₁ l₂, h, ls, ls' => by
    simp only [VLevel.eval]
    rw [eval_const_of_wf_zero (u := l₁) h.1 ls ls',
      eval_const_of_wf_zero (u := l₂) h.2 ls ls']
  | .imax l₁ l₂, h, ls, ls' => by
    simp only [VLevel.eval]
    rw [eval_const_of_wf_zero (u := l₁) h.1 ls ls',
      eval_const_of_wf_zero (u := l₂) h.2 ls ls']
  | .param i, h, _, _ => absurd h (by simp [VLevel.WF])

/-- Hence at `nv = 0` the `≈ .zero` shape and the pointwise shape agree. -/
theorem equivZero_iff_eval_zero {u : VLevel} (hu : u.WF 0) (ls : List ℕ) :
    u ≈ (.zero : VLevel) ↔ u.eval ls = 0 := by
  rw [VLevel.equiv_def]
  refine ⟨fun h ↦ by simpa [VLevel.eval] using h ls, fun h ls' ↦ ?_⟩
  simp only [VLevel.eval]
  rw [eval_const_of_wf_zero hu ls' ls]; exact h

/-- **`PropTypeAgree env 0` *is* the `≈ .zero`-shaped statement.**  The `→` is
`NotProofNoModel.propTypeAgree_equivZero`; the `←` is what §6 of that file records as refuted,
and it holds here because the refutation's witness lives at `WF 2`. -/
theorem propTypeAgree_zero_iff_equivZero (env : VEnv) :
    env.PropTypeAgree 0 ↔
      ∀ {Γ : List VExpr} {e A A' : VExpr} {u u' : VLevel}, u.WF 0 → u'.WF 0 →
        env.HasType 0 Γ e A → env.HasType 0 Γ e A' →
        env.HasType 0 Γ A (.sort u) → env.HasType 0 Γ A' (.sort u') →
        (u ≈ (.zero : VLevel) ↔ u' ≈ (.zero : VLevel)) := by
  refine ⟨fun hT _ _ _ _ _ _ hu hu' he he' hA hA' ↦
    VEnv.propTypeAgree_equivZero hT hu hu' he he' hA hA', fun h ↦ ?_⟩
  intro Γ e A A' u u' ls hu hu' he he' hA hA'
  rw [← equivZero_iff_eval_zero hu ls, ← equivZero_iff_eval_zero hu' ls]
  exact h hu hu' he he' hA hA'

/-- The instance at the witness environment, which is what §11 needs. -/
theorem propTypeAgree_preludeEnv_iff_equivZero :
    preludeEnv.PropTypeAgree 0 ↔
      ∀ {Γ : List VExpr} {e A A' : VExpr} {u u' : VLevel}, u.WF 0 → u'.WF 0 →
        preludeEnv.HasType 0 Γ e A → preludeEnv.HasType 0 Γ e A' →
        preludeEnv.HasType 0 Γ A (.sort u) → preludeEnv.HasType 0 Γ A' (.sort u') →
        (u ≈ (.zero : VLevel) ↔ u' ≈ (.zero : VLevel)) :=
  propTypeAgree_zero_iff_equivZero preludeEnv

end LevelLayer

end Lean4Lean.SetModel.NEAudit

/-! ## Axiom census -/

#print axioms Lean4Lean.SetModel.NEAudit.ne_allConsts
#print axioms Lean4Lean.SetModel.NEAudit.ne_recType_instL
#print axioms Lean4Lean.SetModel.NEAudit.ne_iotaRules
#print axioms Lean4Lean.SetModel.NEAudit.hasType_NE
#print axioms Lean4Lean.SetModel.NEAudit.hasType_RC
#print axioms Lean4Lean.SetModel.NEAudit.hasType_recB1
#print axioms Lean4Lean.SetModel.NEAudit.hasType_ruleB1
#print axioms Lean4Lean.SetModel.NEAudit.hasType_lhsBody
#print axioms Lean4Lean.SetModel.NEAudit.hasType_rhsLam
#print axioms Lean4Lean.SetModel.NEAudit.neOracle_NE
#print axioms Lean4Lean.SetModel.NEAudit.mem_interp_NE_type
#print axioms Lean4Lean.SetModel.NEAudit.mem_interp_NE_intro
#print axioms Lean4Lean.SetModel.NEAudit.pt_mem_interp_NE_recType
#print axioms Lean4Lean.SetModel.NEAudit.pt_mem_interp_neRule_type
#print axioms Lean4Lean.SetModel.NEAudit.inductOracleOK_consts_NE
#print axioms Lean4Lean.SetModel.NEAudit.inductOracleOK_rules_NE
#print axioms Lean4Lean.SetModel.NEAudit.inductOracleOK_NE
#print axioms Lean4Lean.SetModel.NEAudit.mem_interp_consts_NE
#print axioms Lean4Lean.SetModel.NEAudit.defEq_rules_NE
#print axioms Lean4Lean.SetModel.NEAudit.not_mem_interp_zeroOracle_NE_type
#print axioms Lean4Lean.SetModel.NEAudit.nonemptyFn_zero_empty
#print axioms Lean4Lean.SetModel.NEAudit.nonemptyFn_zero_true
#print axioms Lean4Lean.SetModel.NEAudit.nonemptyEnv_le_preludeEnv
#print axioms Lean4Lean.SetModel.NEAudit.inductOracleOK_NE_at_preludeEnv
#print axioms Lean4Lean.SetModel.NEAudit.cnstOf_preludeTail
#print axioms Lean4Lean.SetModel.NEAudit.oracleStepOK_NE
#print axioms Lean4Lean.SetModel.NEAudit.oracleStepOK_NE_at_preludeEnv
#print axioms Lean4Lean.SetModel.NEAudit.nonempty_propSplit_preludeEnv_iff
#print axioms Lean4Lean.SetModel.NEAudit.nonempty_propSplit_preludeEnv_of_propTypeAgree

#print axioms Lean4Lean.SetModel.NEAudit.eval_const_of_wf_zero
#print axioms Lean4Lean.SetModel.NEAudit.propTypeAgree_zero_iff_equivZero
#print axioms Lean4Lean.SetModel.NEAudit.propTypeAgree_preludeEnv_iff_equivZero
#print axioms Lean4Lean.SetModel.NEAudit.iff_recType
#print axioms Lean4Lean.SetModel.NEAudit.eq_recType
