import Lean4Lean.Theory.SetModel.PreludeOracle

/-!
# `iffIndDecl`: the level branch, **measured** rather than predicted

`docs/handoff-setmodel.md` §10.9 item 2, repeated verbatim in §11.7, §12.7, §13.7 and §14.7,
says to take `iffIndDecl` before `eqIndDecl` and predicts that

> the oracle's value branches on `u.eval ls = 0` exactly as `unitOracleL`'s does; §7.4's "the
> level branch is FORCED" should reappear, and the `= 0` slice should be free by §10.1's
> argument.

This file **verifies the first half as a theorem** and reports honestly on the second.  It does
not close `InductOracleOK` at `iffIndDecl`; see §5 for exactly what is left and why.

## What is proved

The typing of `Iff.rec`'s type over `iffEnv`, at an arbitrary instantiation `[u]` of the single
elimination universe, with an **explicit** sort — that is the datum `VInductDecl'.recType_isType`
does not give (it returns `IsType`, i.e. the sort existentially), and it is the datum the level
branch is a statement about:

```lean
theorem hasType_iffRecType : iffEnv.HasType nv Γ ((iffIndDecl.recType 0).instL [u])
                                              (.sort (iffRecSort u))
theorem iffRecSort_eval_eq_zero_iff : (iffRecSort u).eval ls = 0 ↔ u.eval ls = 0
theorem isProp_iffRecType_iff : L.IsProp M Γ ((iffIndDecl.recType 0).instL [u]) ↔ u.eval ls = 0
```

So the branch is **forced, and forced by the level layer alone**: at `u.eval ls = 0` the whole
five-binder telescope is a proposition, so its interpretation is a subset of `{•}` and `•` is
the only value available; at `u.eval ls ≠ 0` it is not a proposition, so `•` is excluded exactly
as `UnitOracleLarge.pt_not_mem_interpL_recType_of_ne` excludes it at `unitDeclLE`.  §10.9's
prediction is **confirmed**, at a block with two parameters and two constructor fields rather
than none of either.

## Why the level computation is not a formality

`Iff` is the first prelude block where the answer could have come out differently, and the
reason is `imax`.  Write `p := u.eval ls`.  The five binders' sorts are

| binder | domain sort | `∀`-sort |
|---|---|---|
| `h : Iff a b` | `0` | `imax 0 p = p` |
| `minor` | `imax (imax 0 0) (imax (imax 0 0) p) = p` | `imax p p = p` |
| `motive : Iff a b → Sort u` | `imax 0 (p+1) = p+1` | `imax (p+1) p` = `0` if `p = 0` else `p+1` |
| `b : Prop` | `1` | `imax 1 (…)` — same |
| `a : Prop` | `1` | `imax 1 (…)` — same |

Two of the five steps have a **`Prop` domain and a non-`Prop` codomain** (`a` and `b` range over
`Prop : Type 0`), so the outer sort is `imax 1 X` and it is only `imax`'s "if the codomain is
`0`, so is the whole thing" clause that keeps the telescope propositional at `p = 0`.  Had the
parameters been `Type`-valued the branch would still exist, but the `= 0` slice would **not** be
`•`-valued: `imax 2 0 = 0` too, so in fact the collapse is `imax`'s and not `Prop`'s.  The
computation is `iffRecSort_eval`, and it is a `rfl`-plus-`omega` fact rather than an argument.

Note where the prediction is *not* confirmed: §10.4's table says the difference from
`nonemptyIndDecl` "is `isLE`", and that is true of *why* there is a branch.  It is not true that
the block behaves like `unitDeclLE` at the `≠ 0` slice — see §5.2.

## Bounds

`Above` does not occur in this file; no `κ` is chosen; `hle : iffEnv ≤ envF` is discharged at
`preludeEnv` by `iffEnv_le_preludeEnv`, five `VDecl.WF.le` steps out of `PreludeWitness.lean`,
so nothing here is a statement about an unreachable environment.  Axioms: `propext`,
`Quot.sound`, `Classical.choice`.
-/

namespace Lean4Lean.SetModel.IffAudit

open Lean4Lean LO LO.FirstOrder LO.FirstOrder.SetTheory

/-! ## 1. The block, measured -/

section Shapes

/-- `Iff`'s type former, as it sits in `iffEnv`. -/
theorem iffEnv_IffC : iffEnv.constants ``Iff =
    some ⟨0, .forallE (.sort .zero) (.forallE (.sort .zero) (.sort .zero))⟩ := rfl

/-- `Iff.intro : ∀ (a b : Prop), (a → b) → (b → a) → Iff a b`. -/
theorem iffEnv_IffIntroC : iffEnv.constants ``Iff.intro =
    some ⟨0, .forallE (.sort .zero) (.forallE (.sort .zero)
      (.forallE (.forallE (.bvar 1) (.bvar 1))
        (.forallE (.forallE (.bvar 1) (.bvar 3))
          (.app (.app (.const ``Iff []) (.bvar 3)) (.bvar 2)))))⟩ := rfl

/-- `Iff.rec`'s type is the block's `recType 0`, and its `uvars` is the block's `recUvars`. -/
theorem iffEnv_IffRecC :
    iffEnv.constants ``Iff.rec = some ⟨iffIndDecl.recUvars, iffIndDecl.recType 0⟩ := rfl

/-- `Iff p q`, for arbitrary `p q`. -/
abbrev iffAp (p q : VExpr) : VExpr := .app (.app (.const ``Iff []) p) q

/-- `Iff.intro p q x y`. -/
abbrev introAp (p q x y : VExpr) : VExpr :=
  .app (.app (.app (.app (.const ``Iff.intro []) p) q) x) y

/-- The motive binder's type over `[b, a]`: `Iff a b → Sort u`. -/
abbrev motTyI (u : VLevel) : VExpr := .forallE (iffAp (.bvar 1) (.bvar 0)) (.sort u)

/-- The minor premise's type over `[motive, b, a]`. -/
abbrev minTyI : VExpr :=
  .forallE (.forallE (.bvar 2) (.bvar 2))
    (.forallE (.forallE (.bvar 2) (.bvar 4))
      (.app (.bvar 2) (introAp (.bvar 4) (.bvar 3) (.bvar 1) (.bvar 0))))

/-- The major premise's type over `[minor, motive, b, a]`: `Iff a b`. -/
abbrev majTyI : VExpr := iffAp (.bvar 3) (.bvar 2)

/-- The innermost two binders, over `[minor, motive, b, a]`. -/
abbrev recBH : VExpr := .forallE majTyI (.app (.bvar 2) (.bvar 0))
/-- …one binder out, over `[motive, b, a]`. -/
abbrev recBN : VExpr := .forallE minTyI recBH
/-- …over `[b, a]`. -/
abbrev recBM (u : VLevel) : VExpr := .forallE (motTyI u) recBN
/-- …over `[a]`. -/
abbrev recBB (u : VLevel) : VExpr := .forallE (.sort .zero) (recBM u)

/-- **`Iff.rec`'s type at the instantiation `[u]`, written out.**  `rfl`, so this is a
measurement of the block and not a transcription. -/
theorem iffRecType_instL (u : VLevel) :
    (iffIndDecl.recType 0).instL [u] = .forallE (.sort .zero) (recBB u) := rfl

end Shapes

/-! ## 2. Contexts

Every context abbrev carries a **tail** `Γ`, per §10.6 item 3: the minor premise's own λ-bodies
live in a longer context, and pinning the tail to `[]` makes `Lookup` unusable there. -/

section Ctxs
variable (Γ : List VExpr)

/-- `a : Prop`. -/
abbrev ictxA : List VExpr := .sort .zero :: Γ
/-- `b, a`. -/
abbrev ictxB : List VExpr := .sort .zero :: ictxA Γ
/-- `motive, b, a`. -/
abbrev ictxM (u : VLevel) : List VExpr := motTyI u :: ictxB Γ
/-- `minor, motive, b, a`. -/
abbrev ictxN (u : VLevel) : List VExpr := minTyI :: ictxM Γ u
/-- `h, minor, motive, b, a` — the recursor's major premise. -/
abbrev ictxH (u : VLevel) : List VExpr := majTyI :: ictxN Γ u
/-- `mp, motive, b, a` — inside the minor premise. -/
abbrev ictxP (u : VLevel) : List VExpr := .forallE (.bvar 2) (.bvar 2) :: ictxM Γ u
/-- `mpr, mp, motive, b, a` — one binder further in. -/
abbrev ictxQ (u : VLevel) : List VExpr := .forallE (.bvar 2) (.bvar 4) :: ictxP Γ u
/-- `x, b, a` — inside the motive's own domain. -/
abbrev ictxI : List VExpr := iffAp (.bvar 1) (.bvar 0) :: ictxB Γ
/-- `x : a`, `motive, b, a` — **inside** `mp`'s own arrow, not after binding `mp`. -/
abbrev ictxPa (u : VLevel) : List VExpr := (.bvar 2 : VExpr) :: ictxM Γ u
/-- `y : b`, `mp, motive, b, a` — inside `mpr`'s own arrow. -/
abbrev ictxQb (u : VLevel) : List VExpr := (.bvar 2 : VExpr) :: ictxP Γ u

end Ctxs

/-! ### The sorts

Named so that `iffRecSort_eval` is a computation on `Lean.Nat.imax` rather than on a term. -/

/-- `a → b`'s sort, `a b : Prop`. -/
abbrev mpSortI : VLevel := .imax .zero .zero
/-- The motive binder's sort. -/
abbrev motSortI (u : VLevel) : VLevel := .imax .zero (.succ u)
/-- The minor premise's sort. -/
abbrev minSortI (u : VLevel) : VLevel := .imax mpSortI (.imax mpSortI u)
/-- `recBH`'s sort. -/
abbrev sortH (u : VLevel) : VLevel := .imax .zero u
/-- `recBN`'s sort. -/
abbrev sortN (u : VLevel) : VLevel := .imax (minSortI u) (sortH u)
/-- `recBM`'s sort. -/
abbrev sortM (u : VLevel) : VLevel := .imax (motSortI u) (sortN u)
/-- `recBB`'s sort. -/
abbrev sortB (u : VLevel) : VLevel := .imax (.succ .zero) (sortM u)
/-- **`Iff.rec`'s sort at the instantiation `[u]`.**  Five `imax`es, two of them with a
`Prop`-typed domain (`.succ .zero`) and a possibly-non-`Prop` codomain. -/
abbrev iffRecSort (u : VLevel) : VLevel := .imax (.succ .zero) (sortB u)

/-! ## 3. Typing derivations in `iffEnv` -/

section Typing

variable {nv : ℕ} {u : VLevel} (hu : u.WF nv)
variable (Γ : List VExpr)

/-- The type former, at any context. -/
theorem hasType_Iff :
    iffEnv.HasType nv Γ (.const ``Iff [])
      (.forallE (.sort .zero) (.forallE (.sort .zero) (.sort .zero))) :=
  .constDF iffEnv_IffC nofun nofun rfl .nil

/-- The constructor, at any context. -/
theorem hasType_IffIntro :
    iffEnv.HasType nv Γ (.const ``Iff.intro [])
      (.forallE (.sort .zero) (.forallE (.sort .zero)
        (.forallE (.forallE (.bvar 1) (.bvar 1))
          (.forallE (.forallE (.bvar 1) (.bvar 3))
            (iffAp (.bvar 3) (.bvar 2)))))) :=
  .constDF iffEnv_IffIntroC nofun nofun rfl .nil

/-- `Iff p q : Prop` whenever `p` and `q` are propositions. -/
theorem hasType_iffAp {Γ : List VExpr} {p q : VExpr}
    (hp : iffEnv.HasType nv Γ p (.sort .zero))
    (hq : iffEnv.HasType nv Γ q (.sort .zero)) :
    iffEnv.HasType nv Γ (iffAp p q) (.sort .zero) :=
  .appDF (.appDF (hasType_Iff Γ) hp) hq

/-! ### The two parameters, at every context they are read in -/

theorem hasType_b_ctxB : iffEnv.HasType nv (ictxB Γ) (.bvar 0) (.sort .zero) :=
  .bvar .zero

theorem hasType_a_ctxB : iffEnv.HasType nv (ictxB Γ) (.bvar 1) (.sort .zero) :=
  .bvar (.succ .zero)

theorem hasType_iffAp_ctxB :
    iffEnv.HasType nv (ictxB Γ) (iffAp (.bvar 1) (.bvar 0)) (.sort .zero) :=
  hasType_iffAp (hasType_a_ctxB Γ) (hasType_b_ctxB Γ)

theorem hasType_b_ctxM : iffEnv.HasType nv (ictxM Γ u) (.bvar 1) (.sort .zero) :=
  .bvar (.succ .zero)

theorem hasType_a_ctxM : iffEnv.HasType nv (ictxM Γ u) (.bvar 2) (.sort .zero) :=
  .bvar (.succ (.succ .zero))

theorem hasType_b_ctxPa : iffEnv.HasType nv (ictxPa Γ u) (.bvar 2) (.sort .zero) :=
  .bvar (.succ (.succ .zero))

theorem hasType_b_ctxP : iffEnv.HasType nv (ictxP Γ u) (.bvar 2) (.sort .zero) :=
  .bvar (.succ (.succ .zero))

theorem hasType_a_ctxQb : iffEnv.HasType nv (ictxQb Γ u) (.bvar 4) (.sort .zero) :=
  .bvar (.succ (.succ (.succ (.succ .zero))))

theorem hasType_a_ctxQ : iffEnv.HasType nv (ictxQ Γ u) (.bvar 4) (.sort .zero) :=
  .bvar (.succ (.succ (.succ (.succ .zero))))

theorem hasType_b_ctxQ : iffEnv.HasType nv (ictxQ Γ u) (.bvar 3) (.sort .zero) :=
  .bvar (.succ (.succ (.succ .zero)))

/-! ### The five binders' types, each with its sort written out -/

include hu in
/-- The motive binder: `Iff a b → Sort u`, of sort `imax 0 (u+1)`. -/
theorem hasType_motTyI :
    iffEnv.HasType nv (ictxB Γ) (motTyI u) (.sort (motSortI u)) :=
  .forallEDF (hasType_iffAp_ctxB Γ) (.sortDF hu hu rfl)

/-- `mp : a → b`, of sort `imax 0 0`. -/
theorem hasType_mpTyI :
    iffEnv.HasType nv (ictxM Γ u) (.forallE (.bvar 2) (.bvar 2)) (.sort mpSortI) :=
  .forallEDF (hasType_a_ctxM Γ) (hasType_b_ctxPa Γ)

/-- `mpr : b → a`, of sort `imax 0 0`. -/
theorem hasType_mprTyI :
    iffEnv.HasType nv (ictxP Γ u) (.forallE (.bvar 2) (.bvar 4)) (.sort mpSortI) :=
  .forallEDF (hasType_b_ctxP Γ) (hasType_a_ctxQb Γ)

/-- `Iff.intro a b mp mpr : Iff a b`, inside the minor premise. -/
theorem hasType_introAp_ctxQ :
    iffEnv.HasType nv (ictxQ Γ u)
      (introAp (.bvar 4) (.bvar 3) (.bvar 1) (.bvar 0)) (iffAp (.bvar 4) (.bvar 3)) :=
  .appDF (.appDF (.appDF (.appDF (hasType_IffIntro (ictxQ Γ u))
    (hasType_a_ctxQ Γ)) (hasType_b_ctxQ Γ)) (.bvar (.succ .zero))) (.bvar .zero)

/-- The motive variable, at the minor premise's innermost context. -/
theorem hasType_mot_ctxQ :
    iffEnv.HasType nv (ictxQ Γ u) (.bvar 2)
      (.forallE (iffAp (.bvar 4) (.bvar 3)) (.sort u)) :=
  .bvar (.succ (.succ .zero))

/-- `motive (Iff.intro a b mp mpr) : Sort u` — the minor premise's body. -/
theorem hasType_minBodyI :
    iffEnv.HasType nv (ictxQ Γ u)
      (.app (.bvar 2) (introAp (.bvar 4) (.bvar 3) (.bvar 1) (.bvar 0))) (.sort u) :=
  .appDF (hasType_mot_ctxQ Γ) (hasType_introAp_ctxQ Γ)

/-- The minor premise, of sort `imax (imax 0 0) (imax (imax 0 0) u)`. -/
theorem hasType_minTyI :
    iffEnv.HasType nv (ictxM Γ u) minTyI (.sort (minSortI u)) :=
  .forallEDF (hasType_mpTyI Γ) (.forallEDF (hasType_mprTyI Γ) (hasType_minBodyI Γ))

/-- The major premise `Iff a b : Prop`. -/
theorem hasType_majTyI :
    iffEnv.HasType nv (ictxN Γ u) majTyI (.sort .zero) :=
  hasType_iffAp (.bvar (.succ (.succ (.succ .zero)))) (.bvar (.succ (.succ .zero)))

/-- The motive variable, at the recursor's innermost context. -/
theorem hasType_mot_ctxH :
    iffEnv.HasType nv (ictxH Γ u) (.bvar 2)
      (.forallE (iffAp (.bvar 4) (.bvar 3)) (.sort u)) :=
  .bvar (.succ (.succ .zero))

/-- The major premise variable `h : Iff a b`. -/
theorem hasType_maj_ctxH :
    iffEnv.HasType nv (ictxH Γ u) (.bvar 0) (iffAp (.bvar 4) (.bvar 3)) := .bvar .zero

/-- The result `motive h : Sort u`. -/
theorem hasType_resI :
    iffEnv.HasType nv (ictxH Γ u) (.app (.bvar 2) (.bvar 0)) (.sort u) :=
  .appDF (hasType_mot_ctxH Γ) (hasType_maj_ctxH Γ)

/-! ### The whole type -/

theorem hasType_recBH : iffEnv.HasType nv (ictxN Γ u) recBH (.sort (sortH u)) :=
  .forallEDF (hasType_majTyI Γ) (hasType_resI Γ)

theorem hasType_recBN : iffEnv.HasType nv (ictxM Γ u) recBN (.sort (sortN u)) :=
  .forallEDF (hasType_minTyI Γ) (hasType_recBH Γ)

include hu in
theorem hasType_recBM : iffEnv.HasType nv (ictxB Γ) (recBM u) (.sort (sortM u)) :=
  .forallEDF (hasType_motTyI hu Γ) (hasType_recBN Γ)

include hu in
theorem hasType_recBB : iffEnv.HasType nv (ictxA Γ) (recBB u) (.sort (sortB u)) :=
  .forallEDF (.sortDF trivial trivial rfl) (hasType_recBM hu Γ)

include hu in
/-- **`Iff.rec`'s type at the instantiation `[u]`, with its sort exhibited.**  This is the datum
`VInductDecl'.recType_isType` withholds: it returns `IsType`, i.e. the sort under an `∃`, and
the level branch is a statement about *which* sort. -/
theorem hasType_iffRecType :
    iffEnv.HasType nv Γ ((iffIndDecl.recType 0).instL [u]) (.sort (iffRecSort u)) := by
  rw [iffRecType_instL]
  exact .forallEDF (.sortDF trivial trivial rfl) (hasType_recBB hu Γ)

/-! ### The sorts are well formed -/

include hu in
theorem sortH_wf : (sortH u).WF nv := ⟨trivial, hu⟩
include hu in
theorem sortN_wf : (sortN u).WF nv := ⟨⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩, hu⟩, sortH_wf hu⟩
include hu in
theorem sortM_wf : (sortM u).WF nv := ⟨⟨trivial, hu⟩, sortN_wf hu⟩
include hu in
theorem sortB_wf : (sortB u).WF nv := ⟨trivial, sortM_wf hu⟩
include hu in
theorem iffRecSort_wf : (iffRecSort u).WF nv := ⟨trivial, sortB_wf hu⟩

end Typing

/-! ## 4. The level branch, computed

Four `imax`es, each of which is `0` exactly when its codomain is (`imax_eq_zero_iff`).  So the
whole five-binder telescope is propositional exactly when the elimination universe evaluates to
`0` — **the branch is forced by the level layer alone**, with no reference to `interp`. -/

section Levels

variable {u : VLevel} {ls : List ℕ}

theorem sortH_eval_eq_zero_iff : (sortH u).eval ls = 0 ↔ u.eval ls = 0 := imax_eq_zero_iff

theorem sortN_eval_eq_zero_iff : (sortN u).eval ls = 0 ↔ u.eval ls = 0 :=
  imax_eq_zero_iff.trans sortH_eval_eq_zero_iff

theorem sortM_eval_eq_zero_iff : (sortM u).eval ls = 0 ↔ u.eval ls = 0 :=
  imax_eq_zero_iff.trans sortN_eval_eq_zero_iff

theorem sortB_eval_eq_zero_iff : (sortB u).eval ls = 0 ↔ u.eval ls = 0 :=
  imax_eq_zero_iff.trans sortM_eval_eq_zero_iff

/-- **The level branch.**  `Iff.rec`'s type is a proposition exactly at a `Prop`
instantiation. -/
theorem iffRecSort_eval_eq_zero_iff : (iffRecSort u).eval ls = 0 ↔ u.eval ls = 0 :=
  imax_eq_zero_iff.trans sortB_eval_eq_zero_iff

/-- **Both slices are non-empty**, so the split is real rather than a formality — the same
control `UnitOracleLarge.exists_ne_zero_level` / `exists_eq_zero_level` provides there. -/
theorem exists_ne_zero_level {nv : ℕ} : ∃ u : VLevel, u.WF nv ∧ u.eval ls ≠ 0 :=
  ⟨.succ .zero, trivial, by simp [VLevel.eval]⟩

theorem exists_eq_zero_level {nv : ℕ} : ∃ u : VLevel, u.WF nv ∧ u.eval ls = 0 :=
  ⟨.zero, trivial, rfl⟩

end Levels

/-! ## 5. `iffEnv` is reachable

`hle : iffEnv ≤ envF` is discharged at `preludeEnv` — five `VDecl.WF.le` steps, each a theorem
of `PreludeWitness.lean`, no `VDecl.unsafeDef` anywhere.  So nothing in §6 is a statement about
an unreachable environment. -/

section Reachable

theorem iffEnv_le_propextEnv : iffEnv ≤ propextEnv :=
  VDecl.WF.le (d := .axiom propextConst) (.axiom propextConst_WF propextEnv_add)

theorem propextEnv_le_nonemptyEnv : propextEnv ≤ nonemptyEnv :=
  VDecl.WF.le (d := .induct nonemptyIndDecl) (.induct (nonemptyIndDecl_WF _) nonemptyEnv_add)

theorem iffEnv_le_nonemptyEnv : iffEnv ≤ nonemptyEnv :=
  VEnv.LE.trans iffEnv_le_propextEnv propextEnv_le_nonemptyEnv

/-- **`iffEnv ≤ preludeEnv`.** -/
theorem iffEnv_le_preludeEnv : iffEnv ≤ preludeEnv :=
  VEnv.LE.trans iffEnv_le_nonemptyEnv NEAudit.nonemptyEnv_le_preludeEnv

end Reachable

/-! ## 6. The model consequence: `•` is legal at `= 0` and **excluded** at `≠ 0` -/

section Model

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ} (L : PropSplit envF nv) (M : ModelData V)
variable {u : VLevel} (hu : u.WF nv) (hle : iffEnv ≤ envF)
variable {Γ : List VExpr} (hΓ : OnCtx Γ (iffEnv.IsType nv))

/-- `Prop` is a type at every context over `iffEnv`. -/
theorem isType_prop : iffEnv.IsType nv Γ (.sort .zero) :=
  ⟨_, .sortDF trivial trivial rfl⟩

include hΓ in
theorem onCtxI_A : OnCtx (ictxA Γ) (iffEnv.IsType nv) := ⟨hΓ, isType_prop⟩

include hΓ in
theorem onCtxI_B : OnCtx (ictxB Γ) (iffEnv.IsType nv) := ⟨onCtxI_A hΓ, isType_prop⟩

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hu hle hΓ in
/-- **The propositionhood of `Iff.rec`'s type is exactly the level branch.** -/
theorem isProp_iffRecType_iff :
    L.IsProp M Γ ((iffIndDecl.recType 0).instL [u]) ↔ u.eval M.ls = 0 :=
  (isProp_iff hle hΓ (hasType_iffRecType hu Γ) (iffRecSort_wf hu)).trans
    iffRecSort_eval_eq_zero_iff

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hu hle hΓ in
/-- The same for the four-binder body, which is what `interp_forallE_type` reads. -/
theorem isProp_recBB_iff :
    L.IsProp M (ictxA Γ) (recBB u) ↔ u.eval M.ls = 0 :=
  (isProp_iff hle (onCtxI_A hΓ) (hasType_recBB hu Γ) (sortB_wf hu)).trans
    sortB_eval_eq_zero_iff

include hu hle in
/-- **`•` is excluded from `Iff.rec`'s type at every non-`Prop` instantiation** — and,
unlike `UnitOracleLarge.pt_not_mem_interpL_recType_of_ne`, with **no hypothesis about an
inhabitant of the motive space.**  The outermost binder here is a *parameter over `Prop`*, and
`∅ ∈ U κ 0` holds at every `κ`, so the domain is unconditionally nonempty.  That is a genuine
simplification the parameterised block buys, not a cost. -/
theorem pt_not_mem_interp_iffRecType_of_ne (hn : u.eval M.ls ≠ 0) :
    (pt : V) ∉ (interp M L [] ((iffIndDecl.recType 0).instL [u])).toFun ∅ := by
  rw [iffRecType_instL, interp_forallE_type M L
    (fun h ↦ hn ((isProp_recBB_iff L M hu hle (Γ := []) trivial).mp h))]
  refine UnitAudit.pt_not_mem_mkForallType_of_nonempty (x := (∅ : V)) ?_
  rw [interp_sort]
  show (∅ : V) ∈ U M.κ 0
  rw [U_zero]
  exact mem_UProp_iff.mpr (by simp)

include hu hle in
/-- **At a `Prop` instantiation the only candidate value is `•`.**  The type is a proposition, so
its interpretation is `mkForallProp`, whose members are all `pt`. -/
theorem eq_pt_of_mem_interp_iffRecType_of_zero (h0 : u.eval M.ls = 0) {v : V}
    (hv : v ∈ (interp M L [] ((iffIndDecl.recType 0).instL [u])).toFun ∅) : v = pt := by
  rw [iffRecType_instL] at hv
  exact ((mem_interp_forallE_prop_iff M L
    ((isProp_recBB_iff L M hu hle (Γ := []) trivial).mpr h0)).mp hv).1

variable {u₀ u₁ : VLevel}

include hle in
/-- **The oracle's level branch is FORCED at `iffIndDecl`.**  No value can serve both slices: at
a `Prop` instantiation the only candidate is `•` (`eq_pt_of_mem_interp_iffRecType_of_zero`), and
`•` is excluded at every non-`Prop` one (`pt_not_mem_interp_iffRecType_of_ne`).  Both slices are
non-empty (`exists_eq_zero_level`, `exists_ne_zero_level`), so this is a real obstruction and not
a vacuous implication.

This is the analogue of `UnitOracleLarge`'s §7.4 verdict at a block with **two parameters and
two constructor fields**, and it comes out the same way — §10.9's prediction, confirmed. -/
theorem level_branch_forced (hu₀ : u₀.WF nv) (hu₁ : u₁.WF nv)
    (h0 : u₀.eval M.ls = 0) (hn : u₁.eval M.ls ≠ 0) {v : V}
    (hv₀ : v ∈ (interp M L [] ((iffIndDecl.recType 0).instL [u₀])).toFun ∅) :
    v ∉ (interp M L [] ((iffIndDecl.recType 0).instL [u₁])).toFun ∅ := by
  rw [eq_pt_of_mem_interp_iffRecType_of_zero L M hu₀ hle h0 hv₀]
  exact pt_not_mem_interp_iffRecType_of_ne L M hu₁ hle hn

end Model

/-! ## 6.6 The branch, restated so **no hypothesis about a member is needed**

*Added 2026-09-02 (tenth session), executing handoff §16.4 / ledger row 149b.*

`level_branch_forced` (§6) is an implication whose antecedent `hv₀ : v ∈ ⟦Iff.rec's type at u₀⟧`
is satisfiable **exactly when the `= 0` slice is true in the model** — the obligation §7 records
as OPEN.  Handoff §15.5's anti-vacuity table listed that theorem's open hypotheses as "the same
[as `isProp_iffRecType_iff`'s], and nothing else", which **omitted `hv₀`**; the "both slices
non-empty" control quoted alongside (`exists_eq_zero_level` / `exists_ne_zero_level`) is about the
two *level* slices, a different object.

The content that survives without the member hypothesis is a **negation**, and a negation does not
evaporate at an empty slice.  `no_level_uniform_value` is the form to quote; it is exactly what
`InductOracleOK` at this block would have to violate, and it is unconditional in the candidate
value.  This is `EqAudit.no_level_uniform_value`'s twin, with **no** parameter-space hypothesis
(§6's exclusion is free here, see `pt_not_mem_interp_iffRecType_of_ne`). -/

section Forced

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ} (L : PropSplit envF nv) (M : ModelData V)
variable (hle : iffEnv ≤ envF) {u₀ u₁ : VLevel}

include hle in
/-- **No value serves both slices at `iffIndDecl`.**  Unconditional in the candidate value, and —
unlike `EqAudit.no_level_uniform_value` — with no parameter-space hypothesis either, so this
statement's *only* open hypotheses are `hle` (a theorem at `preludeEnv`) and the `PropSplit`
parameter. -/
theorem no_level_uniform_value (hu₀ : u₀.WF nv) (hu₁ : u₁.WF nv)
    (h0 : u₀.eval M.ls = 0) (hn : u₁.eval M.ls ≠ 0) :
    ¬ ∃ w : V, w ∈ (interp M L [] ((iffIndDecl.recType 0).instL [u₀])).toFun ∅ ∧
        w ∈ (interp M L [] ((iffIndDecl.recType 0).instL [u₁])).toFun ∅ := by
  rintro ⟨w, hw₀, hw₁⟩
  rw [eq_pt_of_mem_interp_iffRecType_of_zero L M hu₀ hle h0 hw₀] at hw₁
  exact pt_not_mem_interp_iffRecType_of_ne L M hu₁ hle hn hw₁

include hle in
/-- **The exact statement of why `level_branch_forced`'s `hv₀` is unmeasured**, at `iffIndDecl`.
`hv₀ : v ∈ ⟦Iff.rec's type at u₀⟧` is satisfiable **iff `•` is in that interpretation** — and
"`•` is in that interpretation" is verbatim the `= 0` slice, which §7 records as OPEN.  So the
implication form of `level_branch_forced` is conditional on an undischarged obligation, and the
negation above is the form to quote.  `EqAudit.exists_mem_interp_eqRecType_zero_iff` is the same
statement at `eqIndDecl`. -/
theorem exists_mem_interp_iffRecType_zero_iff (hu₀ : u₀.WF nv) (h0 : u₀.eval M.ls = 0) :
    (∃ w : V, w ∈ (interp M L [] ((iffIndDecl.recType 0).instL [u₀])).toFun ∅) ↔
      (pt : V) ∈ (interp M L [] ((iffIndDecl.recType 0).instL [u₀])).toFun ∅ := by
  refine ⟨fun ⟨w, hw⟩ ↦ ?_, fun h ↦ ⟨pt, h⟩⟩
  rwa [eq_pt_of_mem_interp_iffRecType_of_zero L M hu₀ hle h0 hw] at hw

end Forced

/-! ## 7. What is left at this block, stated so it is not mistaken for done

`InductOracleOK L κ ls o c iffIndDecl` has two fields over three constants (`Iff`, `Iff.intro`,
`Iff.rec`) and **one** ι-rule (`iffIndDecl.iotaRules.length = 1`, measured).  After this file:

| obligation | status |
|---|---|
| the level branch is forced, and which way | **proved** (§6, `level_branch_forced`) |
| `Iff.rec`'s type typed with an explicit sort, at every context | **proved** (§3) |
| `•` excluded at `≠ 0`, with **no** motive-space hypothesis | **proved** (§6) |
| `• ∈ ⟦Iff.rec's type⟧` at `= 0` — the slice §10.9 calls "free" | **OPEN**, see below |
| `Iff ↦ iffFn ∈ ⟦Prop → Prop → Prop⟧` | open; `PreludeSpec.iffFn` and `iffFn_value` exist |
| `Iff.intro ↦ •` | open; its type **is** a proposition (`imax _ (imax _ (imax 0 (imax 0 0))) = 0`) |
| the `≠ 0` slice's value (a **five**-layer `mkLam` nest, two layers over `U κ 0`) | open |
| the ι-rule | open |

**§10.9's "the `= 0` slice should be free by §10.1's argument" is the one prediction this round
could not confirm, and the reason is not budget.**  At `nonemptyIndDecl` the `= 0` slice was free
because the block's recursor type is a proposition *whose truth in the model is immediate*: the
minor premise's own value forces it.  Here the proposition to be verified is

> for all `p q ∈ U κ 0`, every motive `f`, every minor premise and every `h ∈ ⟦Iff p q⟧`,
> `• ∈ f ‘ h`

and discharging it needs **`iffFn`'s faithfulness in both directions** — `⟦Iff p q⟧ ≠ ∅ → p = q`
(the easy half, `PreludeSpec.iffFn_value`) *and* `⟦p → q⟧ and ⟦q → p⟧ both nonempty → p = q`, which is
the model-side shadow of `propext` and is exactly what `PreludeSpec.propext_of_mem_UProp` is
for.  So the `= 0` slice is **not** free at this block; it is the first place in this corner where
the *constructor's* content is needed to close the *recursor's* obligation.  That is a
correction to §10.9 item 2, and it is the thing to fund next.
-/

end Lean4Lean.SetModel.IffAudit
