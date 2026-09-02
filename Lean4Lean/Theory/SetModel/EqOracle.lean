import Lean4Lean.Theory.SetModel.IffOracle

/-!
# `eqIndDecl`: the level branch at the **last** of the three prelude blocks

`docs/handoff-setmodel.md` §15.6 item 6 says to take `eqIndDecl` after `iffIndDecl`, and offers a
prediction, labelled as one:

> the same branch, for `imax`'s reason rather than `Prop`'s; six binders, one index, a two-binder
> motive, and a **`Type`-valued** first parameter, so the `≠ 0` exclusion will need the
> nonemptiness of `U κ (v.eval ls)` rather than of `U κ 0`.

**Both halves are now measured, and both are right** — the second one is right in a way that
*costs* something, and §5.3 says exactly what.  This file does not close `InductOracleOK` at
`eqIndDecl`; §7 says what is left.

## What is proved

`Eq.rec`'s type over `eqEnv`, at an arbitrary instantiation `[u, v]` of its **two** recursor
universes (`eqIndDecl.recUvars = 2` — `iffIndDecl`'s is 1), with an **explicit** sort, which is
again the datum `VInductDecl'.recType_isType` withholds (it returns `IsType`, the sort under an
`∃`):

```lean
theorem hasType_eqRecType : eqEnv.HasType nv Γ ((eqIndDecl.recType 0).instL [u, v])
                                               (.sort (eqRecSort u v))
theorem eqRecSort_eval_eq_zero_iff : (eqRecSort u v).eval ls = 0 ↔ u.eval ls = 0
theorem isProp_eqRecType_iff : L.IsProp M Γ ((eqIndDecl.recType 0).instL [u, v]) ↔ u.eval ls = 0
```

## The transfer signal, tested rather than trusted

§15.3's positive signal was that the collapse at `iffIndDecl` is **`imax`'s** (`imax _ 0 = 0`)
and not `Prop`'s, so a `Type`-valued parameter should behave identically.  That is now a theorem:
`eqRecSort_eval_eq_zero_iff`'s statement **does not mention `v` on the right-hand side at all**,
and its proof is six `imax_eq_zero_iff` steps in which `v` only ever appears as a *domain*.
Concretely, `eqRecSort_eval_eq_zero_iff_of_ne_zero` instantiates it at a `v` with
`v.eval ls ≠ 0` — a genuinely `Type`-valued parameter — and the branch is unchanged.  So the
first positive transfer signal this corner produced for `eqIndDecl` **holds**.

The six sorts, writing `p := u.eval ls` and `q := v.eval ls`:

| binder | domain sort | `∀`-sort |
|---|---|---|
| `h : Eq α a b` | `0` | `imax 0 p = p` |
| `b : α` | `q` | `imax q p = p` (`p = 0 ⇒ 0`) |
| `minor : motive a (Eq.refl α a)` | `p` | `imax p p = p` |
| `motive : ∀ x : α, Eq α a x → Sort u` | `imax q (imax 0 (p+1))` | `imax … p` |
| `a : α` | `q` | `imax q …` |
| `α : Sort v` | `q+1` | `imax (q+1) …` |

Every step is `imax`, and an `imax` is `0` exactly when its **codomain** is; `q` never occupies a
codomain position.  That is the whole reason the `Type`-valued parameter costs nothing *here* —
and §5.3 is where it does cost something.

## Bounds

`Above` occurs in **no statement** in this file (three mentions, all prose).  Two `κ`s are
chosen, both deliberately and both in *control* lemmas, never in a positive bound:
`omegaChain V` in §6.4 (to show the parameter-space hypothesis is satisfiable — a good `κ`,
`IsInaccessibleChain` at every length) and `zeroChain` in §6.5b (to show it is necessary — a bad
`κ`, the same one `AboveAudit.above_false_zeroChain` uses).  **Every statement in §§3, 4, 6.1,
6.2, 6.3 and 6.6 is at an arbitrary `κ : ℕ → V`.**  `hle : eqEnv ≤ envF` is discharged at
`preludeEnv` by `eqEnv_le_preludeEnv`, which
is one new `VDecl.WF.le` step on top of `IffAudit.iffEnv_le_preludeEnv`, so nothing here is a
statement about an unreachable environment; `preludeEnv` is `VEnv.WF` (`preludeEnv_WF`) and its
history contains no `VDecl.unsafeDef`.  Axioms: `propext`, `Quot.sound`, `Classical.choice`.
-/

namespace Lean4Lean.SetModel.EqAudit

open Lean4Lean LO LO.FirstOrder LO.FirstOrder.SetTheory

/-! ## 1. The block, measured

Everything in this section is `rfl`, so it is a measurement of `eqIndDecl` and not a
transcription of it. -/

section Shapes

/-- `Eq`'s type former, as it sits in `eqEnv`: `∀ (α : Sort u) (a : α), α → Prop`. -/
theorem eqEnv_EqC : eqEnv.constants ``Eq =
    some ⟨1, .forallE (.sort (.param 0))
      (.forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)))⟩ := rfl

/-- `Eq.refl : ∀ (α : Sort u) (a : α), Eq α a a`. -/
theorem eqEnv_EqReflC : eqEnv.constants ``Eq.refl =
    some ⟨1, .forallE (.sort (.param 0))
      (.forallE (.bvar 0)
        (.app (.app (.app (.const ``Eq [.param 0]) (.bvar 1)) (.bvar 0)) (.bvar 0)))⟩ := rfl

/-- `Eq.rec`'s type is the block's `recType 0`, and its `uvars` is `recUvars = 2`. -/
theorem eqEnv_EqRecC :
    eqEnv.constants ``Eq.rec = some ⟨eqIndDecl.recUvars, eqIndDecl.recType 0⟩ := rfl

theorem eq_recUvars' : eqIndDecl.recUvars = 2 := rfl

/-- `Eq.{v} α a b`, for arbitrary `α a b`. -/
abbrev eqAp (v : VLevel) (α a b : VExpr) : VExpr :=
  .app (.app (.app (.const ``Eq [v]) α) a) b

/-- `Eq.refl.{v} α a`. -/
abbrev reflAp (v : VLevel) (α a : VExpr) : VExpr :=
  .app (.app (.const ``Eq.refl [v]) α) a

/-- The motive binder's type over `[a, α]`: `∀ (x : α), Eq α a x → Sort u`.  **Two** binders,
because `eqIndDecl` has an index and `iffIndDecl` does not. -/
abbrev motTyE (u v : VLevel) : VExpr :=
  .forallE (.bvar 1) (.forallE (eqAp v (.bvar 2) (.bvar 1) (.bvar 0)) (.sort u))

/-- The minor premise's type over `[motive, a, α]`: `motive a (Eq.refl α a)`. -/
abbrev minTyE (v : VLevel) : VExpr :=
  .app (.app (.bvar 0) (.bvar 1)) (reflAp v (.bvar 2) (.bvar 1))

/-- The major premise's type over `[b, minor, motive, a, α]`: `Eq α a b`. -/
abbrev majTyE (v : VLevel) : VExpr := eqAp v (.bvar 4) (.bvar 3) (.bvar 0)

/-- The innermost binder, over `[b, minor, motive, a, α]`. -/
abbrev recBH (v : VLevel) : VExpr :=
  .forallE (majTyE v) (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0))
/-- …the index binder `b : α`, over `[minor, motive, a, α]`. -/
abbrev recBB (v : VLevel) : VExpr := .forallE (.bvar 3) (recBH v)
/-- …over `[motive, a, α]`. -/
abbrev recBN (v : VLevel) : VExpr := .forallE (minTyE v) (recBB v)
/-- …over `[a, α]`. -/
abbrev recBM (u v : VLevel) : VExpr := .forallE (motTyE u v) (recBN v)
/-- …over `[α]`. -/
abbrev recBA (u v : VLevel) : VExpr := .forallE (.bvar 0) (recBM u v)

/-- **`Eq.rec`'s type at the instantiation `[u, v]`, written out.**  `rfl`, so this is a
measurement of the block.  Note that `instL` sends `.param 0 ↦ u` (the *elimination* universe,
prepended because `eqIndDecl.isLE = true`) and `.param 1 ↦ v` (the block's own universe). -/
theorem eqRecType_instL (u v : VLevel) :
    (eqIndDecl.recType 0).instL [u, v] = .forallE (.sort v) (recBA u v) := rfl

end Shapes

/-! ## 2. Contexts

Every context abbrev carries a **tail** `Γ`, per §10.6 item 3 of the handoff: the minor
premise's and motive's own sub-bodies live in longer contexts, and pinning the tail to `[]`
makes `Lookup` unusable there. -/

section Ctxs
variable (Γ : List VExpr)

/-- `α : Sort v`. -/
abbrev ectxA (v : VLevel) : List VExpr := .sort v :: Γ
/-- `a, α` — both parameters bound. -/
abbrev ectxP (v : VLevel) : List VExpr := (.bvar 0 : VExpr) :: ectxA Γ v
/-- `x, a, α` — inside the motive's first binder. -/
abbrev ectxX (v : VLevel) : List VExpr := (.bvar 1 : VExpr) :: ectxP Γ v
/-- `h, x, a, α` — inside the motive's second binder. -/
abbrev ectxXH (v : VLevel) : List VExpr :=
  eqAp v (.bvar 2) (.bvar 1) (.bvar 0) :: ectxX Γ v
/-- `motive, a, α`. -/
abbrev ectxM (u v : VLevel) : List VExpr := motTyE u v :: ectxP Γ v
/-- `minor, motive, a, α`. -/
abbrev ectxN (u v : VLevel) : List VExpr := minTyE v :: ectxM Γ u v
/-- `b, minor, motive, a, α` — the index. -/
abbrev ectxB (u v : VLevel) : List VExpr := (.bvar 3 : VExpr) :: ectxN Γ u v
/-- `h, b, minor, motive, a, α` — the major premise. -/
abbrev ectxH (u v : VLevel) : List VExpr := majTyE v :: ectxB Γ u v

end Ctxs

/-! ### The sorts

Named so that `eqRecSort_eval` is a computation on `Lean.Nat.imax` rather than on a term. -/

/-- The motive binder's own sort: `imax v (imax 0 (u+1))`.  Two `imax`es, because of the
index. -/
abbrev motSortE (u v : VLevel) : VLevel := .imax v (.imax .zero (.succ u))
/-- `recBH`'s sort. -/
abbrev sortHE (u : VLevel) : VLevel := .imax .zero u
/-- `recBB`'s sort — the index binder, whose domain is the **`Type`-valued** `α`. -/
abbrev sortBE (u v : VLevel) : VLevel := .imax v (sortHE u)
/-- `recBN`'s sort. -/
abbrev sortNE (u v : VLevel) : VLevel := .imax u (sortBE u v)
/-- `recBM`'s sort. -/
abbrev sortME (u v : VLevel) : VLevel := .imax (motSortE u v) (sortNE u v)
/-- `recBA`'s sort. -/
abbrev sortAE (u v : VLevel) : VLevel := .imax v (sortME u v)
/-- **`Eq.rec`'s sort at the instantiation `[u, v]`.**  Six `imax`es, **three** of them with a
possibly-`Type`-valued domain (`v`, twice, and `.succ v` once). -/
abbrev eqRecSort (u v : VLevel) : VLevel := .imax (.succ v) (sortAE u v)

/-! ## 3. Typing derivations in `eqEnv` -/

section Typing

variable {nv : ℕ} {u v : VLevel} (hu : u.WF nv) (hv : v.WF nv)
variable (Γ : List VExpr)

/-- **`appDF` with the substituted codomain given explicitly.**  Every application step below
needs this, and the reason is the one thing about `eqIndDecl` that `iffIndDecl` did not have:
here the applied arguments *are* the bound variables, so `B.inst a` reduces through
`VExpr.instVar 0 a 0 = VExpr.liftN 0 a`, and `liftN_zero` is a **theorem** (proved by induction on
the expression), not a definitional unfolding.  So `.appDF` cannot unify the domain, and each
step has to carry its equation.  At `iffIndDecl` the two parameters were `.sort .zero`, i.e.
closed, and this never arose — see §7.4 item 1. -/
theorem hasType_app' {env : VEnv} {Γ : List VExpr} {f a A B C : VExpr}
    (hf : env.HasType nv Γ f (.forallE A B)) (ha : env.HasType nv Γ a A)
    (hC : B.inst a = C) : env.HasType nv Γ (.app f a) C := hC ▸ hf.appDF ha

include hv in
/-- The type former, at any context. -/
theorem hasType_Eq :
    eqEnv.HasType nv Γ (.const ``Eq [v])
      (.forallE (.sort v) (.forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)))) :=
  .constDF eqEnv_EqC (by simpa using hv) (by simpa using hv) rfl (.cons (by rfl) .nil)

include hv in
/-- The constructor, at any context. -/
theorem hasType_EqRefl :
    eqEnv.HasType nv Γ (.const ``Eq.refl [v])
      (.forallE (.sort v)
        (.forallE (.bvar 0) (eqAp v (.bvar 1) (.bvar 0) (.bvar 0)))) :=
  .constDF eqEnv_EqReflC (by simpa using hv) (by simpa using hv) rfl (.cons (by rfl) .nil)

include hv in
/-- `Eq α a b : Prop` whenever `α : Sort v` and `a b : α`. -/
theorem hasType_eqAp {Γ : List VExpr} {α a b : VExpr}
    (hα : eqEnv.HasType nv Γ α (.sort v))
    (ha : eqEnv.HasType nv Γ a α) (hb : eqEnv.HasType nv Γ b α) :
    eqEnv.HasType nv Γ (eqAp v α a b) (.sort .zero) := by
  have h1 : eqEnv.HasType nv Γ (.app (.const ``Eq [v]) α)
      (.forallE α (.forallE (VExpr.liftN 1 α) (.sort .zero))) :=
    hasType_app' (hasType_Eq hv Γ) hα (by simp [VExpr.inst, VExpr.instVar])
  have h2 : eqEnv.HasType nv Γ (.app (.app (.const ``Eq [v]) α) a)
      (.forallE α (.sort .zero)) :=
    hasType_app' h1 ha (by simp [VExpr.inst, VExpr.inst_lift])
  exact hasType_app' h2 hb rfl

include hv in
/-- `Eq.refl α a : Eq α a a`. -/
theorem hasType_reflAp {Γ : List VExpr} {α a : VExpr}
    (hα : eqEnv.HasType nv Γ α (.sort v)) (ha : eqEnv.HasType nv Γ a α) :
    eqEnv.HasType nv Γ (reflAp v α a) (eqAp v α a a) := by
  have h1 : eqEnv.HasType nv Γ (.app (.const ``Eq.refl [v]) α)
      (.forallE α (eqAp v (VExpr.liftN 1 α) (.bvar 0) (.bvar 0))) :=
    hasType_app' (hasType_EqRefl hv Γ) hα (by simp [VExpr.inst, VExpr.instVar])
  exact hasType_app' h1 ha (by simp [VExpr.inst, VExpr.inst_lift])

/-! ### The two parameters, at every context they are read in -/

theorem hasType_al_ctxP : eqEnv.HasType nv (ectxP Γ v) (.bvar 1) (.sort v) :=
  .bvar (.succ .zero)

theorem hasType_a_ctxP : eqEnv.HasType nv (ectxP Γ v) (.bvar 0) (.bvar 1) := .bvar .zero

theorem hasType_al_ctxX : eqEnv.HasType nv (ectxX Γ v) (.bvar 2) (.sort v) :=
  .bvar (.succ (.succ .zero))

theorem hasType_a_ctxX : eqEnv.HasType nv (ectxX Γ v) (.bvar 1) (.bvar 2) :=
  .bvar (.succ .zero)

theorem hasType_x_ctxX : eqEnv.HasType nv (ectxX Γ v) (.bvar 0) (.bvar 2) := .bvar .zero

theorem hasType_al_ctxM : eqEnv.HasType nv (ectxM Γ u v) (.bvar 2) (.sort v) :=
  .bvar (.succ (.succ .zero))

theorem hasType_a_ctxM : eqEnv.HasType nv (ectxM Γ u v) (.bvar 1) (.bvar 2) :=
  .bvar (.succ .zero)

theorem hasType_al_ctxN : eqEnv.HasType nv (ectxN Γ u v) (.bvar 3) (.sort v) :=
  .bvar (.succ (.succ (.succ .zero)))

theorem hasType_al_ctxB : eqEnv.HasType nv (ectxB Γ u v) (.bvar 4) (.sort v) :=
  .bvar (.succ (.succ (.succ (.succ .zero))))

theorem hasType_a_ctxB : eqEnv.HasType nv (ectxB Γ u v) (.bvar 3) (.bvar 4) :=
  .bvar (.succ (.succ (.succ .zero)))

theorem hasType_b_ctxB : eqEnv.HasType nv (ectxB Γ u v) (.bvar 0) (.bvar 4) := .bvar .zero

/-! ### The motive's own two binders -/

include hv in
/-- `Eq α a x : Prop`, inside the motive's first binder. -/
theorem hasType_eqAp_ctxX :
    eqEnv.HasType nv (ectxX Γ v) (eqAp v (.bvar 2) (.bvar 1) (.bvar 0)) (.sort .zero) :=
  hasType_eqAp hv (hasType_al_ctxX Γ) (hasType_a_ctxX Γ) (hasType_x_ctxX Γ)

include hu hv in
/-- The motive binder's type, with its sort: `imax v (imax 0 (u+1))`.  **Two** `imax`es, because
`eqIndDecl` has an index and `iffIndDecl` does not. -/
theorem hasType_motTyE :
    eqEnv.HasType nv (ectxP Γ v) (motTyE u v) (.sort (motSortE u v)) :=
  .forallEDF (hasType_al_ctxP Γ)
    (.forallEDF (hasType_eqAp_ctxX hv Γ) (.sortDF hu hu rfl))

/-! ### The minor premise -/

include hv in
/-- `Eq.refl α a : Eq α a a`, over `[motive, a, α]`. -/
theorem hasType_reflAp_ctxM :
    eqEnv.HasType nv (ectxM Γ u v) (reflAp v (.bvar 2) (.bvar 1))
      (eqAp v (.bvar 2) (.bvar 1) (.bvar 1)) :=
  hasType_reflAp hv (hasType_al_ctxM Γ) (hasType_a_ctxM Γ)

/-- The motive variable over `[motive, a, α]`, **with its type pinned** — per §15.4 item 3,
`appDF` against an expected `.sort u` leaves a metavariable in the function's type unless the
variable's type is stated first. -/
theorem hasType_mot_ctxM :
    eqEnv.HasType nv (ectxM Γ u v) (.bvar 0)
      (.forallE (.bvar 2) (.forallE (eqAp v (.bvar 3) (.bvar 2) (.bvar 0)) (.sort u))) :=
  .bvar .zero

/-- `motive a : Eq α a a → Sort u`. -/
theorem hasType_motA_ctxM :
    eqEnv.HasType nv (ectxM Γ u v) (.app (.bvar 0) (.bvar 1))
      (.forallE (eqAp v (.bvar 2) (.bvar 1) (.bvar 1)) (.sort u)) :=
  hasType_app' (hasType_mot_ctxM Γ) (hasType_a_ctxM Γ)
    (by simp [VExpr.inst, VExpr.instVar])

include hv in
/-- **The minor premise, of sort `u`.**  This is where the block's two slices diverge: the minor
premise's own type is `Sort u`, not `Prop`. -/
theorem hasType_minTyE :
    eqEnv.HasType nv (ectxM Γ u v) (minTyE v) (.sort u) :=
  hasType_app' (hasType_motA_ctxM Γ) (hasType_reflAp_ctxM hv Γ) rfl

/-! ### The major premise and the result -/

include hv in
theorem hasType_majTyE :
    eqEnv.HasType nv (ectxB Γ u v) (majTyE v) (.sort .zero) :=
  hasType_eqAp hv (hasType_al_ctxB Γ) (hasType_a_ctxB Γ) (hasType_b_ctxB Γ)

/-- The motive variable at the recursor's innermost context. -/
theorem hasType_mot_ctxH :
    eqEnv.HasType nv (ectxH Γ u v) (.bvar 3)
      (.forallE (.bvar 5) (.forallE (eqAp v (.bvar 6) (.bvar 5) (.bvar 0)) (.sort u))) :=
  .bvar (.succ (.succ (.succ .zero)))

theorem hasType_b_ctxH : eqEnv.HasType nv (ectxH Γ u v) (.bvar 1) (.bvar 5) :=
  .bvar (.succ .zero)

theorem hasType_h_ctxH :
    eqEnv.HasType nv (ectxH Γ u v) (.bvar 0) (eqAp v (.bvar 5) (.bvar 4) (.bvar 1)) :=
  .bvar .zero

/-- `motive b : Eq α a b → Sort u`. -/
theorem hasType_motB_ctxH :
    eqEnv.HasType nv (ectxH Γ u v) (.app (.bvar 3) (.bvar 1))
      (.forallE (eqAp v (.bvar 5) (.bvar 4) (.bvar 1)) (.sort u)) :=
  hasType_app' (hasType_mot_ctxH Γ) (hasType_b_ctxH Γ)
    (by simp [VExpr.inst, VExpr.instVar])

/-- **The result `motive b h : Sort u`.** -/
theorem hasType_resE :
    eqEnv.HasType nv (ectxH Γ u v) (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0)) (.sort u) :=
  hasType_app' (hasType_motB_ctxH Γ) (hasType_h_ctxH Γ) rfl

/-! ### The whole type, one binder at a time -/

include hv in
theorem hasType_recBH : eqEnv.HasType nv (ectxB Γ u v) (recBH v) (.sort (sortHE u)) :=
  .forallEDF (hasType_majTyE hv Γ) (hasType_resE Γ)

include hv in
theorem hasType_recBB : eqEnv.HasType nv (ectxN Γ u v) (recBB v) (.sort (sortBE u v)) :=
  .forallEDF (hasType_al_ctxN Γ) (hasType_recBH hv Γ)

include hv in
theorem hasType_recBN : eqEnv.HasType nv (ectxM Γ u v) (recBN v) (.sort (sortNE u v)) :=
  .forallEDF (hasType_minTyE hv Γ) (hasType_recBB hv Γ)

include hu hv in
theorem hasType_recBM : eqEnv.HasType nv (ectxP Γ v) (recBM u v) (.sort (sortME u v)) :=
  .forallEDF (hasType_motTyE hu hv Γ) (hasType_recBN hv Γ)

include hu hv in
theorem hasType_recBA : eqEnv.HasType nv (ectxA Γ v) (recBA u v) (.sort (sortAE u v)) :=
  .forallEDF (.bvar .zero) (hasType_recBM hu hv Γ)

include hu hv in
/-- **`Eq.rec`'s type at the instantiation `[u, v]`, with its sort exhibited.**  This is the
datum `VInductDecl'.recType_isType` withholds — it returns `IsType`, i.e. the sort under an `∃`,
and the level branch is a statement about *which* sort (§15.4 item 1). -/
theorem hasType_eqRecType :
    eqEnv.HasType nv Γ ((eqIndDecl.recType 0).instL [u, v]) (.sort (eqRecSort u v)) := by
  rw [eqRecType_instL]
  exact .forallEDF (.sortDF hv hv rfl) (hasType_recBA hu hv Γ)

/-! ### The sorts are well formed -/

include hu in
theorem sortHE_wf : (sortHE u).WF nv := ⟨trivial, hu⟩
include hu hv in
theorem sortBE_wf : (sortBE u v).WF nv := ⟨hv, sortHE_wf hu⟩
include hu hv in
theorem sortNE_wf : (sortNE u v).WF nv := ⟨hu, sortBE_wf hu hv⟩
include hu hv in
theorem motSortE_wf : (motSortE u v).WF nv := ⟨hv, trivial, hu⟩
include hu hv in
theorem sortME_wf : (sortME u v).WF nv := ⟨motSortE_wf hu hv, sortNE_wf hu hv⟩
include hu hv in
theorem sortAE_wf : (sortAE u v).WF nv := ⟨hv, sortME_wf hu hv⟩
include hu hv in
theorem eqRecSort_wf : (eqRecSort u v).WF nv := ⟨hv, sortAE_wf hu hv⟩

end Typing

/-! ## 4. The level branch, computed — **and the transfer signal confirmed**

Six `imax`es, each of which is `0` exactly when its **codomain** is (`imax_eq_zero_iff`).  The
block's own universe `v` occupies a codomain position **nowhere**, so it does not enter the
branch: `eqRecSort_eval_eq_zero_iff`'s right-hand side does not mention it.  That is the test of
§15.3's prediction, and it passes. -/

section Levels

variable {u v : VLevel} {ls : List ℕ}

theorem sortHE_eval_eq_zero_iff : (sortHE u).eval ls = 0 ↔ u.eval ls = 0 := imax_eq_zero_iff

theorem sortBE_eval_eq_zero_iff : (sortBE u v).eval ls = 0 ↔ u.eval ls = 0 :=
  imax_eq_zero_iff.trans sortHE_eval_eq_zero_iff

theorem sortNE_eval_eq_zero_iff : (sortNE u v).eval ls = 0 ↔ u.eval ls = 0 :=
  imax_eq_zero_iff.trans sortBE_eval_eq_zero_iff

theorem sortME_eval_eq_zero_iff : (sortME u v).eval ls = 0 ↔ u.eval ls = 0 :=
  imax_eq_zero_iff.trans sortNE_eval_eq_zero_iff

theorem sortAE_eval_eq_zero_iff : (sortAE u v).eval ls = 0 ↔ u.eval ls = 0 :=
  imax_eq_zero_iff.trans sortME_eval_eq_zero_iff

/-- **The level branch at `eqIndDecl`.**  `Eq.rec`'s type is a proposition exactly at a `Prop`
instantiation of the *elimination* universe — independently of the block's own universe `v`. -/
theorem eqRecSort_eval_eq_zero_iff : (eqRecSort u v).eval ls = 0 ↔ u.eval ls = 0 :=
  imax_eq_zero_iff.trans sortAE_eval_eq_zero_iff

/-- **The transfer signal, instantiated where it could have failed.**  §15.3 predicted that
`eqIndDecl`'s `Type`-valued first parameter would not disturb the branch, because the collapse is
`imax`'s and not `Prop`'s.  Here is the branch at a `v` that is provably **not** `Prop`. -/
theorem eqRecSort_eval_eq_zero_iff_of_ne_zero {v : VLevel} (_hv : v.eval ls ≠ 0) :
    (eqRecSort u v).eval ls = 0 ↔ u.eval ls = 0 := eqRecSort_eval_eq_zero_iff

/-- …and the `v` in question exists, so the previous lemma is not a vacuous implication. -/
theorem exists_ne_zero_blockLevel {nv : ℕ} : ∃ v : VLevel, v.WF nv ∧ v.eval ls ≠ 0 :=
  ⟨.succ .zero, trivial, by simp [VLevel.eval]⟩

/-- **Both slices of the elimination universe are non-empty**, so the branch is a real split. -/
theorem exists_ne_zero_level {nv : ℕ} : ∃ u : VLevel, u.WF nv ∧ u.eval ls ≠ 0 :=
  ⟨.succ .zero, trivial, by simp [VLevel.eval]⟩

theorem exists_eq_zero_level {nv : ℕ} : ∃ u : VLevel, u.WF nv ∧ u.eval ls = 0 :=
  ⟨.zero, trivial, rfl⟩

/-- **Non-degeneracy of the branch, in the shape the ledger asks for**: the two universes are
*independent*, i.e. there is an instantiation in each of the four corners.  Without this the
`eqRecSort_eval_eq_zero_iff_of_ne_zero` control could be read as covering a corner that does not
exist. -/
theorem exists_four_corners {nv : ℕ} :
    ∀ bu bv : Bool, ∃ u v : VLevel, u.WF nv ∧ v.WF nv ∧
      (u.eval ls = 0 ↔ bu = true) ∧ (v.eval ls = 0 ↔ bv = true) := by
  intro bu bv
  refine ⟨if bu then .zero else .succ .zero, if bv then .zero else .succ .zero,
    ?_, ?_, ?_, ?_⟩ <;> cases bu <;> cases bv <;> simp [VLevel.eval, VLevel.WF]

end Levels

/-! ## 5. `eqEnv` is reachable

`eqEnv` is the **first** environment of `leanPrelude.reverse`, so `hle : eqEnv ≤ envF` is the
weakest of the three prelude blocks' reachability conditions.  One new `VDecl.WF.le` step on top
of `IffAudit.iffEnv_le_preludeEnv`. -/

section Reachable

theorem eqEnv_le_iffEnv : eqEnv ≤ iffEnv :=
  VDecl.WF.le (d := .induct iffIndDecl) (.induct (iffIndDecl_WF _) iffEnv_add)

/-- **`eqEnv ≤ preludeEnv`** — and `preludeEnv` is `VEnv.WF` (`preludeEnv_WF`), built by
`preludeEnv_history` with no `VDecl.unsafeDef`. -/
theorem eqEnv_le_preludeEnv : eqEnv ≤ preludeEnv :=
  VEnv.LE.trans eqEnv_le_iffEnv IffAudit.iffEnv_le_preludeEnv

end Reachable

/-! ## 6. The model consequence: `•` is legal at `= 0`, and **excluded at `≠ 0` — but only over
a nonempty domain**

This is where `eqIndDecl`'s `Type`-valued parameter finally costs something, and §15.6 item 6
predicted it exactly.  At `iffIndDecl` the outermost binder is a parameter over `Prop`, so its
denotation is `U κ 0 = UProp`, which contains `∅` at **every** `κ`
(`pt_not_mem_interp_iffRecType_of_ne` is therefore unconditional).  Here the outermost binder is
`α : Sort v`, whose denotation is `U κ (v.eval ls)`, and at `v.eval ls = i+1` that is
`vsetV (κ i)` — **empty at a junk `κ`**.  So the exclusion carries a hypothesis, §6.4 shows the
hypothesis is *satisfiable*, and §6.5 shows it is *necessary*. -/

section Model

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ} (L : PropSplit envF nv) (M : ModelData V)
variable {u v : VLevel} (hu : u.WF nv) (hv : v.WF nv) (hle : eqEnv ≤ envF)
variable {Γ : List VExpr} (hΓ : OnCtx Γ (eqEnv.IsType nv))

include hv in
/-- `Sort v` is a type at every context over `eqEnv`. -/
theorem isType_sortv : eqEnv.IsType nv Γ (.sort v) := ⟨_, .sortDF hv hv rfl⟩

include hv hΓ in
theorem onCtxE_A : OnCtx (ectxA Γ v) (eqEnv.IsType nv) := ⟨hΓ, isType_sortv hv⟩

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hu hv hle hΓ in
/-- **The propositionhood of `Eq.rec`'s type is exactly the level branch** — and, as §4 shows,
it does not depend on the block's own universe `v`. -/
theorem isProp_eqRecType_iff :
    L.IsProp M Γ ((eqIndDecl.recType 0).instL [u, v]) ↔ u.eval M.ls = 0 :=
  (isProp_iff hle hΓ (hasType_eqRecType hu hv Γ) (eqRecSort_wf hu hv)).trans
    eqRecSort_eval_eq_zero_iff

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hu hv hle hΓ in
/-- The same for the five-binder body, which is what `interp_forallE_type` reads (it wants the
*body's* propositionhood one binder in — §15.4 item 6). -/
theorem isProp_recBA_iff :
    L.IsProp M (ectxA Γ v) (recBA u v) ↔ u.eval M.ls = 0 :=
  (isProp_iff hle (onCtxE_A hv hΓ) (hasType_recBA hu hv Γ) (sortAE_wf hu hv)).trans
    sortAE_eval_eq_zero_iff

/-! ### 6.1 The `≠ 0` slice: `•` is excluded, over a nonempty domain -/

include hu hv hle in
/-- **`•` is excluded from `Eq.rec`'s type at every non-`Prop` instantiation of the elimination
universe, provided the block's own universe is nonempty in the model.**

Contrast `IffAudit.pt_not_mem_interp_iffRecType_of_ne`, which needs **no** hypothesis at all, and
`UnitOracleLarge.pt_not_mem_interpL_recType_of_ne`, which needs an inhabitant of the *motive*
space.  This one needs an inhabitant of the **parameter** space, which is a third thing: weaker
than `UnitOracleLarge`'s (the motive space is a function space over the parameter space) and
strictly stronger than `IffAudit`'s (which is free).  §6.4 discharges it, §6.5 shows it cannot be
dropped. -/
theorem pt_not_mem_interp_eqRecType_of_ne (hn : u.eval M.ls ≠ 0)
    {x : V} (hx : x ∈ U M.κ (v.eval M.ls)) :
    (pt : V) ∉ (interp M L [] ((eqIndDecl.recType 0).instL [u, v])).toFun ∅ := by
  rw [eqRecType_instL, interp_forallE_type M L
    (fun h ↦ hn ((isProp_recBA_iff L M hu hv hle (Γ := []) trivial).mp h))]
  refine UnitAudit.pt_not_mem_mkForallType_of_nonempty (x := x) ?_
  rw [interp_sort]
  exact hx

/-! ### 6.2 The `= 0` slice: `•` is the only candidate -/

include hu hv hle in
/-- **At a `Prop` instantiation the only candidate value is `•`.**  The type is a proposition, so
its interpretation is a `mkForallProp`, all of whose members are `pt`. -/
theorem eq_pt_of_mem_interp_eqRecType_of_zero (h0 : u.eval M.ls = 0) {w : V}
    (hw : w ∈ (interp M L [] ((eqIndDecl.recType 0).instL [u, v])).toFun ∅) : w = pt := by
  rw [eqRecType_instL] at hw
  exact ((mem_interp_forallE_prop_iff M L
    ((isProp_recBA_iff L M hu hv hle (Γ := []) trivial).mpr h0)).mp hw).1

/-! ### 6.3 The branch is forced -/

variable {u₀ u₁ : VLevel}

include hv hle in
/-- **The oracle's level branch is FORCED at `eqIndDecl`**, the last of the three prelude blocks.
No value can serve both slices: at a `Prop` instantiation of the elimination universe the only
candidate is `•` (§6.2), and `•` is excluded at every non-`Prop` one (§6.1).

**Read the hypotheses.**  `hx` is discharged in §6.4 and is *necessary* by §6.5.  `hw₀` is
`w ∈ ⟦recType [u₀, v]⟧`, and **its satisfiability is exactly the `= 0` slice's truth, which is
OPEN at this block for the same reason it is open at `iffIndDecl`** (row 146b) — see §7.2.  That
makes the *implication* form of this statement conditional on an unmeasured hypothesis, which is
why §6.6 restates the same content as two unconditional facts instead. -/
theorem level_branch_forced (hu₀ : u₀.WF nv) (hu₁ : u₁.WF nv)
    (h0 : u₀.eval M.ls = 0) (hn : u₁.eval M.ls ≠ 0)
    {x : V} (hx : x ∈ U M.κ (v.eval M.ls)) {w : V}
    (hw₀ : w ∈ (interp M L [] ((eqIndDecl.recType 0).instL [u₀, v])).toFun ∅) :
    w ∉ (interp M L [] ((eqIndDecl.recType 0).instL [u₁, v])).toFun ∅ := by
  rw [eq_pt_of_mem_interp_eqRecType_of_zero L M hu₀ hv hle h0 hw₀]
  exact pt_not_mem_interp_eqRecType_of_ne L M hu₁ hv hle hn hx

end Model

/-! ## 6.4 The parameter-space hypothesis is **satisfiable** — two routes, both machine-checked -/

section Satisfiable

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- **Route 1 — free at a `Prop`-valued block universe.**  `U κ 0 = UProp` and `∅ ∈ UProp` at
every `κ`, so at `v.eval ls = 0` the hypothesis costs nothing.  This is exactly
`IffAudit`'s situation, recovered as the `v.eval ls = 0` special case. -/
theorem exists_mem_U_of_eq_zero (κ : ℕ → V) {j : ℕ} (hj : j = 0) : ∃ x : V, x ∈ U κ j := by
  subst hj; exact ⟨∅, by rw [U_zero]; simp⟩

/-- **Route 2 — free under the chain condition the reduction already carries.**
`CnstRecursion.leanTTConsistent_of` and `AxiomsValidatedAudit.axiomsValidated_of_coherentOn` take
`IsInaccessibleChain m κ` as a hypothesis, so this is not a new assumption: it is the one the
consumer supplies. -/
theorem exists_mem_U_of_chain {n : ℕ} {κ : ℕ → V} (hκ : IsInaccessibleChain n κ)
    {j : ℕ} (hj : j ≤ n) : ∃ x : V, x ∈ U κ j := by
  cases j with
  | zero => exact ⟨∅, by rw [U_zero]; simp⟩
  | succ i => exact ⟨U κ i, U_mem_succ hκ (by omega)⟩

end Satisfiable

section SatisfiableOmega

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰]

/-- **The positive control, at the one `κ` the reduction actually uses.**  `omegaChain V` is an
inaccessible chain of *every* finite length (`omegaChain_isInaccessibleChain`), so the hypothesis
of §6.1 is satisfiable at **every** value of `v.eval ls` — no bound, no side condition.

This is a real control and not a degenerate one: the conclusion is `∃ x, x ∈ U κ j`, which is
**false** for some `κ` and some `j` (§6.5's `U_eq_empty_of_...` shows the shape is refutable), so
it is not free the way `RegPiSat.lean`'s `PropTypeAgreeOnN … 0` was (row 146c). -/
theorem exists_mem_U_omegaChain (j : ℕ) : ∃ x : V, x ∈ U (omegaChain V) j :=
  exists_mem_U_of_chain (omegaChain_isInaccessibleChain j) (le_refl j)

/-- …and the same at an arbitrary `ModelData` built over that chain, which is the form §6.1
consumes. -/
theorem exists_mem_U_omegaChain_model (ls : List ℕ) (c : Name → List VLevel → V) (v : VLevel) :
    ∃ x : V, x ∈ U (⟨omegaChain V, ls, c⟩ : ModelData V).κ
      (v.eval (⟨omegaChain V, ls, c⟩ : ModelData V).ls) :=
  exists_mem_U_omegaChain _

end SatisfiableOmega

/-! ## 6.5 …and it is **necessary**: at an empty parameter space the exclusion is FALSE

This is the guard the ledger's newest blindness asks for (row 146c: *check the conclusion is not
free, as well as the hypotheses not empty*).  Here the check runs the other way — the worry is
not that `hx` is unsatisfiable but that it is **decorative**, i.e. that the conclusion holds
without it.  It does not: with an empty parameter space, `mkForallType` over `∅` is `{∅}` (the
empty function is the unique function out of `∅`), so `•` **is** a member and §6.1's conclusion is
refuted.  The proof is `FalseProp.interp_forallE_falseProp_sort_nonempty`'s, at this telescope. -/

section Necessary

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ} (L : PropSplit envF nv) (M : ModelData V)
variable {u v : VLevel} (hu : u.WF nv) (hv : v.WF nv) (hle : eqEnv ≤ envF)

include hu hv hle in
/-- **§6.1's hypothesis cannot be dropped.**  At `U M.κ (v.eval M.ls) = ∅` the conclusion of
`pt_not_mem_interp_eqRecType_of_ne` is false, so the hypothesis is load-bearing rather than
bookkeeping.  Together with §6.4 this brackets it: satisfiable, and necessary. -/
theorem pt_mem_interp_eqRecType_of_empty_dom (hn : u.eval M.ls ≠ 0)
    (hemp : U M.κ (v.eval M.ls) = (∅ : V)) :
    (pt : V) ∈ (interp M L [] ((eqIndDecl.recType 0).instL [u, v])).toFun ∅ := by
  rw [eqRecType_instL, interp_forallE_type M L
    (fun h ↦ hn ((isProp_recBA_iff L M hu hv hle (Γ := []) trivial).mp h)),
    mem_mkForallType_iff]
  refine ⟨mem_function_iff.mpr ⟨?_, ?_⟩, ?_⟩
  · rw [interp_sort, hemp]; simp [pt_def]
  · rw [interp_sort, hemp]; simp [pt_def]
  · intro x hx; rw [interp_sort, hemp] at hx; simp at hx

end Necessary

/-! ### 6.5b …and the empty parameter space is **reached**, at a named `κ`

`U κ 0 = UProp` is never empty, so the least index at which this can happen is `1`, and there it
does: `U κ (i+1) = vsetV (κ i)`, and `vsetV ∅ = ∅`.  The `κ` is `fun _ ↦ ∅`, the same junk chain
`AboveAudit.above_false_zeroChain` uses — ledger §0's sixth blindness.  So §6.5 is a statement
about a configuration that **exists**, which is what makes it a refutation of the unconditional
form rather than a remark. -/

section ZeroChain

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- **The junk stage is empty.** -/
theorem vsetV_empty : vsetV (∅ : V) = (∅ : V) := by
  rw [mem_ext_iff]
  intro z
  simp only [not_mem_empty, iff_false]
  intro hz
  rw [mem_vsetV_iff_mem_Vset, mem_Vset_iff] at hz
  obtain ⟨β, hβ, -⟩ := hz
  exact absurd (Ordinal.lt_def.1 hβ) not_mem_empty

/-- The chain that is `∅` everywhere — `AboveAudit.above_false_zeroChain`'s. -/
noncomputable def zeroChain : ℕ → V := fun _ ↦ ∅

theorem U_zeroChain_succ (i : ℕ) : U (zeroChain (V := V)) (i + 1) = (∅ : V) := by
  rw [U_succ]; exact vsetV_empty

/-- …and `U κ 0` is never empty, so `1` really is the least index. -/
theorem U_zero_nonempty (κ : ℕ → V) : ∃ x : V, x ∈ U κ 0 := ⟨∅, by rw [U_zero]; simp⟩

end ZeroChain

section NecessaryWitness

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ} (L : PropSplit envF nv)
variable {u : VLevel} (hu : u.WF nv) (hle : eqEnv ≤ envF)

include hu hle in
/-- **The refutation of the unconditional form, at an exhibited `κ`.**  With `v := .succ .zero`
(so `v.eval ls = 1`, a genuinely `Type`-valued parameter) and `κ := zeroChain V`, `•` **is** a
member of `⟦Eq.rec's type⟧` even though the elimination universe is not `Prop`.  So §6.1 without
its hypothesis is **false**, not merely unproved. -/
theorem pt_mem_interp_eqRecType_at_zeroChain (ls : List ℕ) (c : Name → List VLevel → V)
    (hn : u.eval ls ≠ 0) :
    (pt : V) ∈ (interp (⟨zeroChain, ls, c⟩ : ModelData V) L []
      ((eqIndDecl.recType 0).instL [u, .succ .zero])).toFun ∅ := by
  have he : U (⟨zeroChain, ls, c⟩ : ModelData V).κ
      ((VLevel.succ .zero).eval (⟨zeroChain, ls, c⟩ : ModelData V).ls) = (∅ : V) :=
    U_zeroChain_succ 0
  exact pt_mem_interp_eqRecType_of_empty_dom (v := .succ .zero) L
    (⟨zeroChain, ls, c⟩ : ModelData V) hu trivial hle hn he

end NecessaryWitness

/-! ## 6.6 The branch, restated so **no hypothesis about a member is needed**

`level_branch_forced` (§6.3) is an implication whose antecedent `hw₀` is satisfiable exactly when
the `= 0` slice is *true* in the model — which is OPEN (§7.2).  So the implication form is, by
this project's own standard, an **unmeasured** statement.  The content that survives without it is
a negation, and negations do not evaporate at an empty slice:

`no_level_uniform_value` says *no set at all* lies in both slices.  That is what
`InductOracleOK` would have to violate, and it is unconditional in `w`. -/

section Forced

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ} (L : PropSplit envF nv) (M : ModelData V)
variable {v : VLevel} (hv : v.WF nv) (hle : eqEnv ≤ envF) {u₀ u₁ : VLevel}

include hv hle in
/-- **No value serves both slices at `eqIndDecl`.**  Unconditional in the candidate value. -/
theorem no_level_uniform_value (hu₀ : u₀.WF nv) (hu₁ : u₁.WF nv)
    (h0 : u₀.eval M.ls = 0) (hn : u₁.eval M.ls ≠ 0)
    {x : V} (hx : x ∈ U M.κ (v.eval M.ls)) :
    ¬ ∃ w : V, w ∈ (interp M L [] ((eqIndDecl.recType 0).instL [u₀, v])).toFun ∅ ∧
        w ∈ (interp M L [] ((eqIndDecl.recType 0).instL [u₁, v])).toFun ∅ := by
  rintro ⟨w, hw₀, hw₁⟩
  rw [eq_pt_of_mem_interp_eqRecType_of_zero L M hu₀ hv hle h0 hw₀] at hw₁
  exact pt_not_mem_interp_eqRecType_of_ne L M hu₁ hv hle hn hx hw₁

include hv hle in
/-- **The exact statement of why `level_branch_forced`'s member hypothesis is unmeasured.**
`hw₀ : w ∈ ⟦Eq.rec's type at [u₀, v]⟧` is satisfiable **iff `•` is in that interpretation** — and
"`•` is in that interpretation" is verbatim the `= 0` slice, the obligation §7.2 records as OPEN.
So the implication form of §6.3 is conditional on an obligation nobody has discharged, and
`no_level_uniform_value` is the form to quote.

**This applies verbatim to `IffAudit.level_branch_forced` too**, whose `hv₀` has the same shape;
handoff §15.5's anti-vacuity table lists that theorem's open hypotheses as "the same [as
`isProp_iffRecType_iff`'s], and nothing else", which **omits `hv₀`**.  The "both slices
non-empty" control there (`exists_eq_zero_level` / `exists_ne_zero_level`) is about the two
*level* slices; it says nothing about whether either interpretation has a member. -/
theorem exists_mem_interp_eqRecType_zero_iff (hu₀ : u₀.WF nv) (h0 : u₀.eval M.ls = 0) :
    (∃ w : V, w ∈ (interp M L [] ((eqIndDecl.recType 0).instL [u₀, v])).toFun ∅) ↔
      (pt : V) ∈ (interp M L [] ((eqIndDecl.recType 0).instL [u₀, v])).toFun ∅ := by
  refine ⟨fun ⟨w, hw⟩ ↦ ?_, fun h ↦ ⟨pt, h⟩⟩
  rwa [eq_pt_of_mem_interp_eqRecType_of_zero L M hu₀ hv hle h0 hw] at hw

end Forced

/-! ## 7. The rest of the block, measured — and what is left

`InductOracleOK L κ ls o c eqIndDecl` has two fields over three constants and one ι-rule.
Everything in §7.1 is `rfl` or a level computation, so it is a measurement. -/

section Remaining

/-- The three constants the block declares. -/
theorem eq_allConsts : eqIndDecl.allConsts.map Prod.fst = [``Eq, ``Eq.refl, ``Eq.rec] := rfl

/-- One ι-rule, as at `iffIndDecl`. -/
theorem eq_iotaRules_length : eqIndDecl.iotaRules.length = 1 := rfl

/-- **`Eq.refl` has no constructor fields** — two parameters and one result index, and nothing
else.  `Iff.intro` has two fields.  This is the measurement §7.2's costing rests on. -/
theorem eqRefl_fields : ((eqIndDecl.types.getD 0 default).ctors.getD 0 default).fields = [] := rfl

theorem iffIntro_fields_length :
    ((iffIndDecl.types.getD 0 default).ctors.getD 0 default).fields.length = 2 := rfl

theorem eq_params_length : eqIndDecl.params.length = 2 := rfl

theorem eq_indices' : (eqIndDecl.types.getD 0 default).indices = [.bvar 1] := rfl

/-- **`Eq.refl`'s type IS a proposition, at every `v`.**  `imax v 0 = 0` and
`imax (v+1) 0 = 0`, so the small-eliminator argument applies to `Eq.refl ↦ •` — this is the
cheapest remaining piece of the `consts` field, exactly as `Iff.intro ↦ •` is at `iffIndDecl`
(§15.6 item 2). -/
abbrev reflSort (v : VLevel) : VLevel := .imax (.succ v) (.imax v .zero)

theorem reflSort_eval_eq_zero (v : VLevel) (ls : List ℕ) : (reflSort v).eval ls = 0 := by
  simp [VLevel.eval, Lean.Nat.imax]

/-- …and the sort is the right one: `Eq.refl : ∀ (α : Sort v) (a : α), Eq α a a` has sort
`imax (v+1) (imax v 0)`. -/
theorem hasType_EqReflType {nv : ℕ} {v : VLevel} (hv : v.WF nv) (Γ : List VExpr) :
    eqEnv.HasType nv Γ
      (.forallE (.sort v) (.forallE (.bvar 0) (eqAp v (.bvar 1) (.bvar 0) (.bvar 0))))
      (.sort (reflSort v)) :=
  .forallEDF (.sortDF hv hv rfl)
    (.forallEDF (.bvar .zero)
      (hasType_eqAp hv (.bvar (.succ .zero)) (.bvar .zero) (.bvar .zero)))

/-- **`Eq`'s type former is NOT a proposition**, so — unlike `Eq.refl` — its oracle value has to
be a genuine internal function, as `Nonempty`'s was (`NEAudit`, handoff §10.1).  Measured at
`v.eval ls = 0`, the cheapest instantiation: the sort evaluates to `1`. -/
abbrev eqTyFormerSort (v : VLevel) : VLevel :=
  .imax (.succ v) (.imax v (.imax v (.succ .zero)))

theorem eqTyFormerSort_eval_zero (ls : List ℕ) :
    (eqTyFormerSort .zero).eval ls = 1 := by simp [VLevel.eval, Lean.Nat.imax]

theorem hasType_EqType {nv : ℕ} {v : VLevel} (hv : v.WF nv) (Γ : List VExpr) :
    eqEnv.HasType nv Γ
      (.forallE (.sort v) (.forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero))))
      (.sort (eqTyFormerSort v)) :=
  .forallEDF (.sortDF hv hv rfl)
    (.forallEDF (.bvar .zero)
      (.forallEDF (.bvar (.succ .zero)) (.sortDF trivial trivial rfl)))

end Remaining

/-! ### 7.2 The status table, stated so it is not mistaken for done

| obligation | status |
|---|---|
| the level branch is forced, and which way | **proved** (§6.3, §6.6) |
| the branch does not depend on the block's `Type`-valued universe | **proved** (§4) — §15.3's transfer signal, tested |
| `Eq.rec`'s type typed with an explicit sort, at every context, at both universes | **proved** (§3) |
| `•` excluded at `≠ 0` | **proved (§6.1) with one hypothesis**, which is satisfiable (§6.4) and necessary (§6.5) |
| `Eq.refl`'s type is a proposition, so `Eq.refl ↦ •` is the small-eliminator argument | **proved** (§7.1) |
| `Eq`'s type former is not a proposition, so it needs a real function value | **proved** (§7.1) |
| `• ∈ ⟦Eq.rec's type⟧` at `= 0` | **OPEN** — and *not* free, see below |
| `Eq ↦ ⟦Sort v → α → α → Prop⟧`, a genuine internal function | open |
| the `≠ 0` slice's value (a **six**-layer `mkLam` nest, one layer over `U κ (v.eval ls)`) | open |
| the ι-rule | open |

**The `= 0` slice is not free here either, and the reason is `iffIndDecl`'s (row 146b).**  At
`= 0` the proposition to be verified is

> for all `α ∈ U κ (v.eval ls)`, all `a ∈ α`, every motive `f`, every minor premise and every
> `b ∈ α` and `h ∈ ⟦Eq α a b⟧`, `• ∈ f ‘ b ‘ h`

and closing it needs the *constructor's* content — so row 146b's warning transfers: the branch
machinery carries over, the slice does not come for free.

**But the content it needs is already in the tree, and `iffIndDecl`'s was not.**  The datum is
`SetModel.eqFn_value` — note the **namespace**: `PreludeSpec.lean` declares into
`Lean4Lean.SetModel`, so handoff §15.3's spellings `PreludeSpec.iffFn_value` and
`PreludeSpec.propext_of_mem_UProp` both fail with *unknown constant* (row 146e's trap, committed
in the handoff that records it).  Verified present by `#check`, and it is an *equation*, i.e.
faithfulness in both directions at once:

```lean
theorem eqFn_value (hα : α ∈ U κ i) (ha : a ∈ α) (hb : b ∈ α) :
    (((eqFn κ i) ‘ α) ‘ a) ‘ b = (if a = b then ({pt} : V) else ∅)
```

From it, `h ∈ ⟦Eq α a b⟧` forces both `a = b` and `h = •`, and the minor premise then supplies the
value directly.  There is **no `propext` analogue here**, and the reason is measured:
`iffIndDecl`'s hard half is not the recursor's at all — it is `Iff.intro`'s, whose **two fields**
(`iffIntro_fields_length = 2`) are implications, so accepting the constructor forces
"`p → q` and `q → p` both inhabited ⇒ `p = q`".  `Eq.refl` has **no fields**
(`eqRefl_fields = []`).

So `eqIndDecl`'s `= 0` slice should be *strictly cheaper* than `iffIndDecl`'s — the reverse of
how §10.4 priced the two blocks ("`Iff` wants five layers and `Eq` six"), which counted binders
and not constructor fields.  Labelled as a **costing**, not attempted in Lean.
-/

end Lean4Lean.SetModel.EqAudit
