import Lean4Lean.Theory.SetModel.RecTypePeel

/-!
# `interp (mkPi …)` as an **equation**, and the four `interp` hypotheses of
`eq_singleton_of_mem_interp_mkPi3`

`SetModel.eq_singleton_of_mem_interp_mkPi3` (`Theory/SetModel/RecTypePeel.lean` §8) has nine
hypotheses.  `Theory/SetModel/TeleWFBridge.lean` discharges the three `IsProp` ones
(`hpm`, `hpp`, `hpx`).  This file discharges the four `interp` equations — `hmot`, `hmin`,
`hmaj`, `hbody` — and reports precisely what is left.

## The absence this file fills, measured

`shape.lean` against the compiled environment, five queries (population 450 modules each):

| heads | hits | what they are |
|---|---|---|
| `SetModel.interp`, `VExpr.mkPi` | 17 | two `∈`-implications, 12 auto-generated `PeelArgs*`, `eq_singleton_of_mem_interp_mkPi3`, and `PeelArgs*.below.*` — **no equation** |
| `SetModel.interp`, `SetModel.mkForallType` | 3 | `interp.eq_def`, `interp.eq_6`, `interp_forallE_type` |
| `SetModel.interp`, `SetModel.mkForallProp` | 3 | `interp.eq_def`, `interp.eq_6`, `interp_forallE_prop` |
| `SetModel.interp`, `HPow.hPow` | 4 | `fldDom.eq_1`, `UnitAudit.interpL_motTyU`, `UnitAudit.interpL_lhsBody`, `eq_singleton_of_mem_interp_mkPi3` |
| `SetModel.interp`, `SetModel.piProp` | 0 | — |

So the absence is real and stronger than "no general equation": before this file the tree had
**no iterated `interp` equation over a telescope in either branch**, only the two single-binder
defining lemmas `interp_forallE_type` and `interp_forallE_prop`.

(Recorded so the next reader does not mis-read a zero: `HEADS="… LO.FirstOrder.SetTheory.function"`
returns 0 *not* because nothing mentions the function space, but because `^` is the `Pow V V`
instance and the instance, not `function`, is what appears in types.  Route that query through
`HPow.hPow`.)

## Two corrections to the framing this file was written against

**1.  The branch trap does not bite here.**  `interp`'s `forallE` clause branches on the
codomain, and `RecTypePeel.lean`'s status note is right that at a propositional elimination level
every binder of `recType` takes the *propositional* branch.  But the four `interp` equations are
not about `recType`'s binders.  Three of them (`hmin`, `hmaj`, `hbody`) are about expressions
that are not `∀`s at all — an application, a constant, an application — and the fourth, `hmot`,
is about the **motive's own type**, which ends in `.sort elimLvl`.  The level of `.sort v` is
`.succ v`, and `(.succ v).eval ls = v.eval ls + 1` is never `0`, so `not_isProp_sort` below rules
out the propositional branch for **every** `v`, `elimLvl = .zero` included.  There is no branch
hypothesis to carry and no second branch to state: §3's equation is total.

**2.  The layer counts 6/6/5 belong to different theorems.**  `RecTypePeel.lean`'s table
attributes "6 hardcoded layers" to `UnitOracleLarge.interpL_motTyU`, "6" to
`EqRecLarge.motSet_eq_interp_motTyE` and "5" to `IffRecLarge.motSetI_eq_interp_motTyI`.  The
6/6/5 are the binder counts of the *big slice theorems* in those files (the
`mkLam_mem_mkForallType_of_dom` towers, commented `-- layer 3 … layer 6`).  The three named
`interp (mkPi …) = _` equations have **1, 2 and 1** binder respectively.  The general equation
was therefore never fighting a six-deep hardcode; it was fighting that each instance is written
against a *literal* `.forallE` nest with a per-block right-hand side.

Block-specific in the three, itemised: (i) the RHS spelling (`U _ ^ {•}` / `motSet` / `motSetI`);
(ii) the per-binder `¬IsProp` side condition, supplied by `not_isPropL_sortU` /
`not_isProp_motInner`+`not_isProp_sortu` / `not_isProp_sortuI` — **all three are now the single
`not_isProp_sort`**; (iii) the domain-identification step (`interpL_Unit1` / `hspec`+`eqFn_value`
/ `hspec`+`iffFn_value`).  Only (iii) is irreducibly per-block, and only for `Eq`/`Iff` is it
oracle data.

## Why there is no closed form for a general telescope

A closed-form `interp M L Γ (mkPi Δ B) = ⟨something simpler⟩` cannot exist for arbitrary `Δ`:
the fibre of each `mkForallType` layer *is* `interp` at the extended context, so any putative
right-hand side has to re-implement `interp`.  What is general is the pair in §3 — the one-binder
unfolding with its branch **discharged from typing rather than hypothesised**
(`interp_mkPi_sort_cons`, general in `Δ`), plus the genuine closed form at the arity the consumer
needs (`interp_forallE_sort`).  That arity is not a restriction: `eq_singleton_of_mem_interp_mkPi3`
is about index-free blocks, and `VInductDecl'.motiveType_eq_mkPi_sort` says an index-free
motive type is a **one**-element `mkPi`.

## Does `hmin` need the oracle?  No — but `hmk` does

The question this file was asked to settle.  `hmin` says
`⟦motive mk⟧(ρ, m) = m ‘ mkv`, which does tie a value to the constructor's denotation.  But the
tie is an **identity**, not a fact about the oracle's choice: with `mkv` *defined* to be
`M.cnst cc cus`, `hmin` is `interp_app_type` + `interp_bvar` + `snoc_value_at_len` +
`interp_const`, and no field of the oracle is consulted.  §5 proves it that way.

The oracle is needed in two places, and neither is one of the four:

* `hmk : mkv ∈ Sv`, i.e. `M.cnst cc cus ∈ M.cnst tc tus` — the constructor inhabits the type.
  That is `InductOracleOK`'s constructor obligation and there is no route to it from typing.
* Naming `M.cnst cc cus` concretely.  §5's conclusion is
  `M.cnst tc tus = {M.cnst cc cus}`, which is the useful statement as it stands; a consumer who
  wants `{•}` on the right (as `UnitAudit.unitL_denot_eq_singleton_of_zero` does) needs the
  oracle's value, e.g. `unitOracleL_mk`.

So the model side's remaining work after this file is **not** a second `interp`-equation item.
It is `hmk` plus `hf` — the oracle's two `InductOracleOK` obligations — and both were already
oracle obligations before.

## One premise that was not among the nine

§5 needs `hρ : ρ ∈ interpCtx M L Γ`, which `eq_singleton_of_mem_interp_mkPi3` does not have.  It
is unavoidable and not a defect: `hmin` and `hbody` read variables out of the valuation
(`interp_bvar` gives `ρ ‘ (|Γ| - 1 - i)`), and `snoc_value_at_len` / `snoc_value_of_lt` are false
for a `ρ` that is not a valuation of `Γ`.  `UnitAudit.unitL_denot_eq_singleton_of_zero` supplies
it as `interpCtxL_nil`; a general consumer has it from `InductOracleOK`'s own quantifier.
-/

namespace Lean4Lean.SetModel

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V]

section
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-! ## 1. The combinator step, general in the domain -/

/-- **A `∀` whose fibre is constant on the domain is the function space** — with *no* condition
on the domain at all.  This is `UnitAudit.mkForallType_singleton_const` with its
`G ρ = {a}` hypothesis deleted; that hypothesis was doing nothing.

The empty-domain case is not a case: `mkFamUnion G hG F hF ρ = ∅ ≠ Y` there, yet both sides
are `{∅}`, and the proof below never names `mkFamUnion`'s value, so it does not have to split. -/
theorem mkForallType_const_cod {G : V → V} {hG : ℒₛₑₜ-function₁[V] G}
    {F : V → V → V} {hF : ℒₛₑₜ-function₂[V] F} {ρ Y : V}
    (hF0 : ∀ v ∈ G ρ, F ρ v = Y) :
    mkForallType G hG F hF ρ = (Y ^ G ρ : V) := by
  rw [mem_ext_iff]
  intro f
  rw [mem_mkForallType_iff, mem_function_iff, mem_function_iff]
  constructor
  · rintro ⟨⟨hsub, huniq⟩, hsep⟩
    refine ⟨fun p hp ↦ ?_, huniq⟩
    obtain ⟨v, hv, y, -, rfl⟩ := mem_prod_iff.1 (hsub p hp)
    exact mem_prod_iff.2 ⟨v, hv, _, (hF0 v hv) ▸ hsep v hv _ hp, rfl⟩
  · rintro ⟨hsub, huniq⟩
    refine ⟨⟨fun p hp ↦ ?_, huniq⟩, fun v hv y hy ↦ ?_⟩
    · obtain ⟨v, hv, y, hy, rfl⟩ := mem_prod_iff.1 (hsub p hp)
      exact mem_prod_iff.2 ⟨v, hv, y, mem_mkFamUnion_iff.2 ⟨v, hv, (hF0 v hv) ▸ hy⟩, rfl⟩
    · obtain ⟨v', hv', y', hy', he⟩ := mem_prod_iff.1 (hsub _ hy)
      obtain ⟨rfl, rfl⟩ := kpair_iff.1 he.symm
      rw [hF0 _ hv']; exact hy'

/-- `UnitAudit.mkForallType_singleton_const` is the `G ρ = {a}` case of
`mkForallType_const_cod` — the reproduction that shows §1 generalises rather than parallels. -/
theorem mkForallType_singleton_const' {G : V → V} {hG : ℒₛₑₜ-function₁[V] G}
    {F : V → V → V} {hF : ℒₛₑₜ-function₂[V] F} {ρ a Y : V}
    (hG0 : G ρ = ({a} : V)) (hF0 : ∀ v ∈ ({a} : V), F ρ v = Y) :
    mkForallType G hG F hF ρ = (Y ^ ({a} : V) : V) := by
  rw [mkForallType_const_cod (hG := hG) (hF := hF) (Y := Y) (by rw [hG0]; exact hF0), hG0]

/-! ## 2. The branch is not a choice: a sort codomain forces `mkForallType` -/

section
variable [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF env₀ : VEnv} {nv : ℕ} {M : ModelData V} {L : PropSplit envF nv}

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
/-- **A universe is never a proposition, at any level and in any context.**  The general form of
`not_isProp_sort_zero` (`Theory/SetModel/FalseProp.lean`), which is the `v = .zero` case.

This is what settles the trap `RecTypePeel.lean`'s status note records.  `interp`'s `forallE`
clause branches on the *codomain*, and at a propositional elimination level every binder of
`recType` takes the propositional branch — but the **motive's own** type ends in `.sort elimLvl`,
and the level of `.sort v` is `.succ v`, whose evaluation is never `0`.  So the motive binder
takes the `mkForallType` branch **unconditionally**, for every `v`, `elimLvl = .zero`
included.  There is no branch hypothesis to carry and no second branch to state: §2's equation
is total. -/
theorem not_isProp_sort {Γ : List VExpr} {v : VLevel}
    (hΓ : OnCtx Γ (envF.IsType nv)) (hv : v.WF nv) : ¬ L.IsProp M Γ (.sort v) := by
  have h : envF.HasType nv Γ (.sort v) (.sort (.succ v)) := VEnv.IsDefEq.sortDF hv hv rfl
  rw [show L.IsProp M Γ (.sort v) = L.IsPropAt M.ls Γ (.sort v) from rfl,
    L.prop_sound (u := .succ v) hΓ (by exact hv) h]
  simp [VLevel.eval]

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
/-- **…hence a sort-ended telescope takes the `mkForallType` branch at every layer**, for a
telescope of any length.  `isProp_mkPi_iff` says all the layers make the *same* decision;
`not_isProp_sort` says which one. -/
theorem not_isProp_mkPi_sort (hle : env₀ ≤ envF) {Γ Δ : List VExpr} {v : VLevel}
    (hΓ : OnCtx Γ (env₀.IsType nv)) (ht : TeleWF env₀ nv Γ Δ) (hv : v.WF nv) :
    ¬ L.IsProp M Γ (VExpr.mkPi Δ (.sort v)) := by
  rw [isProp_mkPi_iff (M := M) (L := L) (v := .succ v) hle hΓ ht (by exact hv)
    (VEnv.IsDefEq.sortDF hv hv rfl)]
  exact not_isProp_sort (onCtxF hle (ht.onCtx hΓ)) hv

/-! ## 3. The equation

Two statements, and between them they are the general form of all three per-declaration
instances.

**Why there is no closed form for a general telescope, and what replaces it.**  A closed-form
`interp M L Γ (mkPi Δ B) = <something simpler>` cannot exist for arbitrary `Δ`: the fibre of
each `mkForallType` layer *is* `interp` at the extended context, so any putative right-hand side
has to re-implement `interp`.  What is general is the pair below — the one-binder unfolding with
its branch **discharged from typing rather than hypothesised** (`interp_mkPi_sort_cons`, general
in `Δ`), and the genuine closed form at the arity the target needs
(`interp_forallE_sort`). -/

/-- **The general equation, one binder, closed form.**  `⟦A → Sort v⟧ = U_{⟦v⟧} ^ ⟦A⟧`, general
in `A`, `Γ`, `ρ`, `v`, `envF`, `M` and `L`, with **no** hypothesis about the branch and none
about the domain — §1 deleted the domain condition and §2 deleted the branch condition. -/
theorem interp_forallE_sort {Γ : List VExpr} {A : VExpr} {v : VLevel}
    (hΓ : OnCtx (A :: Γ) (envF.IsType nv)) (hv : v.WF nv) (ρ : V) :
    (interp M L Γ (.forallE A (.sort v))).toFun ρ
      = ((U M.κ (v.eval M.ls)) ^ (interp M L Γ A).toFun ρ : V) := by
  rw [interp_forallE_type M L (not_isProp_sort hΓ hv)]
  exact mkForallType_const_cod (fun x _ ↦ interp_sort M L _ v _)

/-- The same, spelled with `mkPi` — the form `motiveType_eq_mkPi_sort` hands you. -/
theorem interp_mkPi_sort_one {Γ : List VExpr} {A : VExpr} {v : VLevel}
    (hΓ : OnCtx (A :: Γ) (envF.IsType nv)) (hv : v.WF nv) (ρ : V) :
    (interp M L Γ (VExpr.mkPi [A] (.sort v))).toFun ρ
      = ((U M.κ (v.eval M.ls)) ^ (interp M L Γ A).toFun ρ : V) :=
  interp_forallE_sort hΓ hv ρ

/-- **The general equation, arbitrary telescope, one layer at a time.**  General in `Δ`; the
`¬IsProp` side condition `interp_forallE_type` demands is discharged by §2 from `TeleWF` plus
`OnCtx`, so this is an unconditional rewrite for any sort-ended telescope. -/
theorem interp_mkPi_sort_cons (hle : env₀ ≤ envF) {Γ Δ : List VExpr} {A : VExpr} {v : VLevel}
    (hΓ : OnCtx (A :: Γ) (env₀.IsType nv)) (ht : TeleWF env₀ nv (A :: Γ) Δ) (hv : v.WF nv)
    (ρ : V) :
    (interp M L Γ (VExpr.mkPi (A :: Δ) (.sort v))).toFun ρ
      = mkForallType (interp M L Γ A).toFun (interp M L Γ A).definable
          (fun ρ x ↦ (interp M L (A :: Γ) (VExpr.mkPi Δ (.sort v))).toFun (snoc ρ x))
          (by have := (interp M L (A :: Γ) (VExpr.mkPi Δ (.sort v))).definable; definability)
          ρ := by
  rw [VExpr.mkPi_cons, interp_forallE_type M L (not_isProp_mkPi_sort hle hΓ ht hv)]

end

end

/-! ## 4. Reproduction: `UnitAudit.interpL_motTyU` from §3

Test (d).  The hand-written instance is re-derived from the general equation, with the
per-block content reduced to the two things that are genuinely per-block: `interpL_Unit1`
(the oracle's value at the type constant) and `unitML_kappa`/`unitML_ls` (the model data's
projections).  No `interp_forallE_type`, no `mkForallType_*`, no branch reasoning. -/

namespace UnitAudit

open Lean4Lean.SetModel.UnitAudit

section
variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ} (L : PropSplit envF nv) (κ : ℕ → V) (ls : List ℕ)
variable {u : VLevel} (hu : u.WF nv) (hle : unitEnvLE ≤ envF)

include hu hle in
/-- **`UnitOracleLarge.interpL_motTyU`, re-derived from `interp_forallE_sort`.**  Statement
identical to the original (`Theory/SetModel/UnitOracleLarge.lean:633`), proof three rewrites
none of which mentions the `forallE` branch. -/
theorem interpL_motTyU' (Γ : List VExpr) (hΓ : OnCtx Γ (unitEnvLE.IsType nv)) (ρ : V) :
    (interp (unitML κ ls) L Γ (motTyU u)).toFun ρ
      = ((U κ (u.eval ls)) ^ ({pt} : V) : V) := by
  rw [show motTyU u = VExpr.forallE (.const `Unit1 []) (.sort u) from rfl,
    interp_forallE_sort (onCtxF hle (onCtxL_unitTy hΓ)) hu,
    interpL_Unit1 L κ ls Γ ρ, unitML_kappa, unitML_ls]

include hu hle in
/-- **…and it is the SAME statement, not a parallel one.**  `rfl` here is only typeable if the
two theorems have literally the same type, so this is the reproduction check rather than a
restatement: `interpL_motTyU'` (proved from the general equation) and `interpL_motTyU` (proved
by hand at `unitDeclLE`) are interchangeable terms. -/
theorem interpL_motTyU_reproduced (Γ : List VExpr) (hΓ : OnCtx Γ (unitEnvLE.IsType nv)) (ρ : V) :
    interpL_motTyU' L κ ls hu hle Γ hΓ ρ = interpL_motTyU L κ ls hu hle Γ hΓ ρ := rfl

end

end UnitAudit

/-! ## 5. The four `interp` equations, discharged -/

section
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF env₀ : VEnv} {nv : ℕ} {M : ModelData V} {L : PropSplit envF nv}

/-- `motive : T → Sort w`, the motive's type at a zero-field, index-free, parameter-free
block. -/
abbrev motTyG (tc : Name) (tus : List VLevel) (w : VLevel) : VExpr :=
  .forallE (.const tc tus) (.sort w)

/-- `motive mk`, the minor premise's type. -/
abbrev minTyG (cc : Name) (cus : List VLevel) : VExpr := .app (.bvar 0) (.const cc cus)

/-- `motive x`, the recursor type's body. -/
abbrev recBodyG : VExpr := .app (.bvar 2) (.bvar 0)

/-- The three-binder recursor type of the shape `eq_singleton_of_mem_interp_mkPi3` is about. -/
abbrev recTyG (tc cc : Name) (tus cus : List VLevel) (w : VLevel) : VExpr :=
  VExpr.mkPi [motTyG tc tus w, minTyG cc cus, .const tc tus] recBodyG

/-- **Structure eta in the set model, with the four `interp` equations gone.**

`eq_singleton_of_mem_interp_mkPi3` has nine hypotheses.  The `TeleWF` bridge discharges the
three `IsProp` ones; this discharges the four `interp` equations `hmot`/`hmin`/`hmaj`/`hbody`.
What is left is `hmk` — `⟦mk⟧ ∈ ⟦T⟧`, the oracle's constructor obligation — and `hf`, which is
`InductOracleOK.type` at the recursor.

The two unknowns of the original statement are **defined, not hypothesised**: `Sv := M.cnst tc
tus` (the type constant's denotation) and `mkv := M.cnst cc cus` (the constructor's).  That is
what makes `hmin` a typing fact rather than an oracle one — see the module docstring. -/
theorem cnst_eq_singleton_of_mem_interp_recTyG (hle : env₀ ≤ envF)
    {Γ : List VExpr} {tc cc : Name} {tus cus : List VLevel} {w v0 : VLevel} {ρ f : V}
    (hΓ : OnCtx Γ (env₀.IsType nv)) (hρ : ρ ∈ interpCtx M L Γ)
    (hw : w.WF nv) (hv0 : v0.WF nv) (h0 : w.eval M.ls = 0)
    (hT : ∀ Δ : List VExpr, env₀.HasType nv Δ (.const tc tus) (.sort v0))
    (hC : ∀ Δ : List VExpr, env₀.HasType nv Δ (.const cc cus) (.const tc tus))
    (hpm : L.IsProp M (motTyG tc tus w :: Γ)
      (VExpr.mkPi [minTyG cc cus, .const tc tus] recBodyG))
    (hpp : L.IsProp M (minTyG cc cus :: motTyG tc tus w :: Γ)
      (VExpr.mkPi [.const tc tus] recBodyG))
    (hpx : L.IsProp M (.const tc tus :: minTyG cc cus :: motTyG tc tus w :: Γ) recBodyG)
    (hmk : M.cnst cc cus ∈ M.cnst tc tus)
    (hf : f ∈ (interp M L Γ (recTyG tc cc tus cus w)).toFun ρ) :
    M.cnst tc tus = ({M.cnst cc cus} : V) := by
  -- the motive's type is a type former, in every context: `OnCtx` and `TeleWF` for free
  have hty : ∀ Δ : List VExpr, env₀.IsType nv Δ (motTyG tc tus w) :=
    fun Δ => ⟨.imax v0 (.succ w), .forallEDF (hT Δ) (.sortDF hw hw rfl)⟩
  have hteleT : ∀ Δ : List VExpr, TeleWF env₀ nv Δ [VExpr.const tc tus] :=
    fun Δ => .cons hv0 (hT Δ) .nil
  -- the minor premise's type is `Sort w`: the motive variable applied to the constructor
  have hminT : env₀.HasType nv (motTyG tc tus w :: Γ) (minTyG cc cus) (.sort w) := by
    have hlk : Lookup (motTyG tc tus w :: Γ) 0 (.forallE (.const tc tus) (.sort w)) := .zero
    exact VEnv.IsDefEq.appDF (B := .sort w) (VEnv.IsDefEq.bvar hlk) (hC _)
  -- the two `¬IsProof` facts, both instances of `not_isProof_bvar_of_typeFormer`
  have hnp0 : ¬ L.IsProof M (motTyG tc tus w :: Γ) (.bvar 0) :=
    not_isProof_bvar_of_typeFormer hle ⟨hΓ, hty Γ⟩ (hteleT _) hw Lookup.zero
  have hnp2 : ¬ L.IsProof M
      (.const tc tus :: minTyG cc cus :: motTyG tc tus w :: Γ) (.bvar 2) :=
    not_isProof_bvar_of_typeFormer hle ⟨⟨⟨hΓ, hty Γ⟩, _, hminT⟩, _, hT _⟩
      (hteleT _) hw (.succ (.succ Lookup.zero))
  -- `hmot`
  have hmot : (interp M L Γ (motTyG tc tus w)).toFun ρ
      = ((UProp : V) ^ M.cnst tc tus : V) := by
    rw [interp_forallE_sort (onCtxF hle ⟨hΓ, _, hT Γ⟩) hw, h0, U_zero, interp_const]
  -- `hmin`
  have hmin : ∀ m : V, (interp M L (motTyG tc tus w :: Γ) (minTyG cc cus)).toFun (snoc ρ m)
      = m ‘ (M.cnst cc cus) := by
    intro m
    rw [show minTyG cc cus = VExpr.app (.bvar 0) (.const cc cus) from rfl,
      interp_app_type M L hnp0, interp_bvar, interp_const]
    simp only [List.length_cons, Nat.add_sub_cancel, Nat.sub_zero]
    rw [snoc_value_at_len M L hρ]
  -- `hbody`, which needs the two extended valuations
  have hbody : ∀ m ∈ ((UProp : V) ^ M.cnst tc tus : V), ∀ p ∈ m ‘ (M.cnst cc cus),
      ∀ x ∈ M.cnst tc tus,
      (interp M L (.const tc tus :: minTyG cc cus :: motTyG tc tus w :: Γ) recBodyG).toFun
        (snoc (snoc (snoc ρ m) p) x) = m ‘ x := by
    intro m hm p hp x _
    have h1 : snoc ρ m ∈ interpCtx M L (motTyG tc tus w :: Γ) :=
      (mem_interpCtx_cons M L).mpr ⟨ρ, hρ, m, by rw [hmot]; exact hm, rfl⟩
    have h2 : snoc (snoc ρ m) p
        ∈ interpCtx M L (minTyG cc cus :: motTyG tc tus w :: Γ) :=
      (mem_interpCtx_cons M L).mpr ⟨_, h1, p, by rw [hmin m]; exact hp, rfl⟩
    have e0 : (snoc (snoc (snoc ρ m) p) x) ‘ ((Γ.length : ℕ) : V) = m := by
      rw [snoc_value_of_lt M L h2 (j := Γ.length) (by simp only [List.length_cons]; omega),
        snoc_value_of_lt M L h1 (j := Γ.length) (by simp only [List.length_cons]; omega),
        snoc_value_at_len M L hρ]
    have e2 : (snoc (snoc (snoc ρ m) p) x) ‘ (((Γ.length + 2 : ℕ)) : V) = x := by
      have := snoc_value_at_len M L h2 (v := x)
      simpa only [List.length_cons, show Γ.length + 1 + 1 = Γ.length + 2 from rfl] using this
    rw [show recBodyG = VExpr.app (.bvar 2) (.bvar 0) from rfl,
      interp_app_type M L hnp2, interp_bvar, interp_bvar]
    simp only [List.length_cons]
    rw [show (Γ.length + 1 + 1 + 1 - 1 - 2) = Γ.length by omega,
      show (Γ.length + 1 + 1 + 1 - 1 - 0) = Γ.length + 2 by omega, e0, e2]
  -- and the assembly
  exact eq_singleton_of_mem_interp_mkPi3 (M := M) (L := L) (Γ := Γ)
    (Am := motTyG tc tus w) (Ap := minTyG cc cus) (Ax := .const tc tus) (B := recBodyG)
    (ρ := ρ) (f := f) (Sv := M.cnst tc tus) (mkv := M.cnst cc cus)
    hpm hpp hpx hmot (fun m _ => hmin m) (fun m _ p _ => interp_const ..) hbody hmk hf

end

/-! ### §5's shape is not vacuous -/

namespace UnitAudit

open Lean4Lean.SetModel.UnitAudit

/-- **§5's shape is `unitDeclLE`'s recursor type on the nose.**
`recTyG `Unit1 `Unit1.mk [] [] u` is *syntactically* `(unitDeclLE.recType 0).instL [u]` —
`motTyG `Unit1 [] u = motTyU u`, `minTyG `Unit1.mk [] = minTy` and
`recBodyG = .app (.bvar 2) (.bvar 0)` — so the hypotheses of
`cnst_eq_singleton_of_mem_interp_recTyG` are instantiable at a real declaration, one whose
`InductOracleOK` witness the tree already has (`UnitAudit.inductOracleOKL`).  Without this the
theorem could be vacuous. -/
theorem recTyG_eq_unitDeclLE_recType (u : VLevel) :
    recTyG `Unit1 `Unit1.mk [] [] u = (unitDeclLE.recType 0).instL [u] :=
  (unitDeclLE_recType_instL_mkPi u).symm

end UnitAudit

/-! ## 6. Firing at `ntreeAux`, the parameterised nested block -/

namespace InductiveDeclExamples

open Lean4Lean.InductiveDeclExamples

section
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ} {M : ModelData V} {L : PropSplit envF nv}

/-- `ntreeAux.elimLvl` is well formed as soon as there is one universe parameter — the block
`isLE`s, so `elimLvl = .param 0`, and the recursor's numbering has `recUvars = 2`. -/
theorem ntreeAux_elimLvl_wf (hnv : 0 < nv) : ntreeAux.elimLvl.WF nv := hnv

/-- **§3's equation at `ntreeAux`'s motive type, both members.**  Test (d), second target: the
general equation *does* reach the parameterised nested block at the motive binder, with the
per-block content reduced to one hypothesis — that the saturated type former is a type in the
ambient context, which is `VInductDecl'.RecCtx.onCtxMotives`-layer data and not something an
`interp` lemma can supply.

What does **not** reach is §5: `eq_singleton_of_mem_interp_mkPi3` has exactly three binders
(motive, minor, major) and `ntreeAux.recPiTele j` has **seven** — one parameter, two motives,
three minors, one major premise (`ntreeAux_recPiTele_length`, `RecTypePeel.lean` §11).  The block
is parameterised, has two mutually nested members and three constructors with fields, so it is
outside the zero-field/one-constructor/index-free/parameter-free shape §5 and §8 of
`RecTypePeel.lean` are about.  That is a limit of the *three-binder* consumer, not of the
equation. -/
theorem interp_ntreeAux_motiveType (t : Nat) {Γ : List VExpr} (ρ : V) (hnv : 0 < nv)
    (hΓ : OnCtx (ntreeAux.tyApp' t t [] :: Γ) (envF.IsType nv)) :
    (interp M L Γ (ntreeAux.motiveType t)).toFun ρ
      = ((U M.κ (ntreeAux.elimLvl.eval M.ls))
          ^ (interp M L Γ (ntreeAux.tyApp' t t [])).toFun ρ : V) := by
  rw [ntreeAux_motiveType_mkPi t]
  exact interp_mkPi_sort_one hΓ (ntreeAux_elimLvl_wf hnv) ρ

/-- The same at the block's own member, spelled out: `elimLvl = .param 0`, so the universe is
the one the recursor's first level parameter names. -/
theorem interp_ntreeAux_motiveType_zero {Γ : List VExpr} (ρ : V) (hnv : 0 < nv)
    (hΓ : OnCtx (ntreeAux.tyApp' 0 0 [] :: Γ) (envF.IsType nv)) :
    (interp M L Γ (ntreeAux.motiveType 0)).toFun ρ
      = ((U M.κ (M.ls.getD 0 0))
          ^ (interp M L Γ (ntreeAux.tyApp' 0 0 [])).toFun ρ : V) := by
  rw [interp_ntreeAux_motiveType 0 ρ hnv hΓ]
  rfl

end

end InductiveDeclExamples

end Lean4Lean.SetModel

/-! ## Status -/

#print axioms Lean4Lean.SetModel.mkForallType_const_cod
#print axioms Lean4Lean.SetModel.mkForallType_singleton_const'
#print axioms Lean4Lean.SetModel.not_isProp_sort
#print axioms Lean4Lean.SetModel.not_isProp_mkPi_sort
#print axioms Lean4Lean.SetModel.interp_forallE_sort
#print axioms Lean4Lean.SetModel.interp_mkPi_sort_one
#print axioms Lean4Lean.SetModel.interp_mkPi_sort_cons
#print axioms Lean4Lean.SetModel.UnitAudit.interpL_motTyU'
#print axioms Lean4Lean.SetModel.UnitAudit.recTyG_eq_unitDeclLE_recType
#print axioms Lean4Lean.SetModel.UnitAudit.interpL_motTyU_reproduced
#print axioms Lean4Lean.SetModel.cnst_eq_singleton_of_mem_interp_recTyG
#print axioms Lean4Lean.SetModel.InductiveDeclExamples.interp_ntreeAux_motiveType
#print axioms Lean4Lean.SetModel.InductiveDeclExamples.interp_ntreeAux_motiveType_zero
