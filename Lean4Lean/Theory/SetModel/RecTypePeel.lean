import Lean4Lean.Theory.SetModel.SoundInduction
import Lean4Lean.Theory.Inductive.Decl
import Lean4Lean.Theory.SetModel.RecPropSingleton
import Lean4Lean.Theory.SetModel.UnitOracleLarge
import Lean4Lean.Theory.Inductive.NestedHead

/-!
# The general `interp (D.recType j)` peel, and the model's `sort_not_proof`

**Layering note, 2026-09-04.**  This file used to `import Lean4Lean.Theory.Typing.StructEtaPrice`
for one theorem, `SetModel.eq_singleton_of_recProp`.  That file imports
`Lean4Lean.Verify.TypeChecker.EtaUnitRefute`, so the import inverted the refinement chain
(`Verify/` → `Theory/` → `Theory/SetModel/` → Foundation) at its deepest layer: it put **46**
`Verify.*` modules into this file's import closure (154 `Lean4Lean` modules in total), and a
measured constant walk over all 91 declarations here found that **not one** of them uses a single
`Verify.*` constant.  The theorem and its six helpers were moved verbatim to
`Theory/SetModel/RecPropSingleton.lean` (see `docs/handoff-layering.md`); `UnitOracleLarge`, the
other thing `StructEtaPrice.lean` was transitively supplying here (`UnitAudit.*`), is now imported
directly.  The closure is **59** `Lean4Lean` modules with **zero** `Verify.*` entries.  Nothing in
this file's mathematics changed.

`Theory/Typing/StructEtaPrice.lean` §8 records the set model's verdict on structure eta —
it validates it, and *forcedly* — and then names, precisely, the two steps still owed:

> 1. *The unfolding.*  `interp (D.recType j)` must be peeled to the shape
>    `eq_singleton_of_recProp` consumes.  `SetModel/UnitOracleLarge.lean` performs exactly this
>    peel at `unitDeclLE` …; at a general block it is `recType`'s telescope instead of two
>    binders.
> 2. *The `PropSplit` side condition.*  `interp (.app f a)` collapses to `pt` when
>    `L.IsProof M Γ f`.  The argument needs the motive not to be classified as a proof, which
>    `PropSplit`'s agreement with typing gives (a motive has type `S ps → Sort u`, not a
>    proposition) but which no lemma in the tree states in that form.

This file discharges both, and they are not independent: (2) is a *prerequisite* of (1),
because the recursor type's body is `motive_j indices major` — an application whose head is the
motive variable, so `interp`'s `app` clause has to be told the head is not a proof before the
peel can name the body's value.

## What was per-declaration, and what is general now

The three peels in `Theory/SetModel/` are all per-declaration, verified:

| peel | declaration | shape |
|---|---|---|
| `UnitOracleLarge.interpL_motTyU` | `unitDeclLE` | 6 hardcoded `mkLam_mem_mkForallType_of_dom` layers |
| `EqRecLarge.motSet_eq_interp_motTyE` | `eqIndDecl`, under `EqSpec M v` | 6 layers |
| `IffRecLarge.motSetI_eq_interp_motTyI` | `iffIndDecl`, under `IffSpec M` | 5 layers |

Nothing in the tree quantified over `D : VInductDecl'`.  §4 does: `PeelArgs` is the telescope's
argument list together with the two side conditions the `interp` clauses need, and
`appAll_mem_interp_of_peel` peels *any* `mkPi`.  §5 fires it at `D.recType j` for an arbitrary
`D` and `j`, which is step 1; §6 fires that at `unitDeclLE` and at the parameterised nested
block `ntreeAux`.

## `sort_not_proof`: what the statement is

The cited name `Lean4Lean.SetModel.sort_not_proof` is genuinely absent, but the *reading* the
citation suggests — "the interpretations of a sort and of a proof are distinct" — is **not**
what the peel needs, and that reading is in the tree twice already
(`SetModel.sortDenot_not_mem_propDenot`, `SetModel.sortNotProof_of_propSplit`, and syntactically
`VEnv.sort_not_proof`).  What the peel needs is §1's `not_isProof_of_isType`:

> a term whose type is a **sort** is never classified as a proof.

It is unconditional in the level — `A : Sort u` makes `A`'s own type `Sort u`, whose sort is
`succ u`, and `(succ u).eval ls = u.eval ls + 1 ≠ 0` for every valuation, so no `u.eval ≠ 0`
side condition is needed.  Every `¬IsProof` in the three per-declaration peels
(`UnitOracleLarge.not_isProofL_bvar0/1/2`, `IffRecLarge.not_isProof_mot_gen`/`not_isProof_iffC0`,
`EqIotaRule.not_isProof_mot_ctxN`) is an instance, and §1's `sort_not_proof` is the special case
`A = .sort u` that the cited name literally asks for.
-/

namespace Lean4Lean.SetModel

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V]

section
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF env₀ : VEnv} {nv : ℕ} {M : ModelData V} {L : PropSplit envF nv}

/-! ## 1. `sort_not_proof`, in the form the peel consumes -/

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
/-- **A type is not a proof.**  `StructEtaPrice.lean` §8's owed step 2, general: the model's
`app` clause may not collapse an application whose head is a type former.

Unconditional in `u`: `A`'s type is `.sort u`, whose own sort is `.succ u`, and
`(.succ u).eval ls = u.eval ls + 1` is never `0`.  In particular a *motive* — whose type is
`S ps → Sort u`, so a type in its own right — is never a proof, which is the sentence
`StructEtaPrice.lean` says no lemma in the tree states. -/
theorem not_isProof_of_isType (hle : env₀ ≤ envF) {Γ : List VExpr} {A : VExpr} {u : VLevel}
    (hΓ : OnCtx Γ (env₀.IsType nv)) (hA : env₀.HasType nv Γ A (.sort u)) (hw : u.WF nv) :
    ¬ L.IsProof M Γ A := by
  intro hp
  have hsu : env₀.HasType nv Γ (.sort u) (.sort (.succ u)) := .sortDF hw hw (.refl _)
  have := (isProof_iff (M := M) (L := L) hle hΓ hA hsu (u := .succ u) hw).mp hp
  simp [VLevel.eval] at this

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
/-- **`sort_not_proof` at the name the citation used**: a universe is not a proof.  The
`A = .sort u` case of `not_isProof_of_isType`. -/
theorem sort_not_proof (hle : env₀ ≤ envF) {Γ : List VExpr} {u : VLevel}
    (hΓ : OnCtx Γ (env₀.IsType nv)) (hw : u.WF nv) :
    ¬ L.IsProof M Γ (.sort u) :=
  not_isProof_of_isType hle hΓ (.sortDF hw hw (.refl _)) (u := .succ u) hw

/-! ## 2. Telescopes: the sort of a `mkPi`, and its `IsProp` split

`interp`'s `forallE` clause branches on `L.IsProp M (A :: Γ) B`, so peeling an `n`-binder
telescope needs `n` such decisions.  They all reduce to **one**: a `∀` lands in `Prop` exactly
when its codomain does (`SoundInduction.imax_eq_zero_iff`), so the whole telescope is a `Prop`
exactly when the innermost body is. -/

/-- A telescope in **declaration order** whose entries are types, each with a well-formed
level.  This is `OnCtx (As.reverse ++ Γ)` read outermost-first, plus the level well-formedness
that `PropSplit`'s fields need and `OnCtx` does not carry. -/
inductive TeleWF (env : VEnv) (nv : ℕ) : List VExpr → List VExpr → Prop
  | nil {Γ : List VExpr} : TeleWF env nv Γ []
  | cons {Γ : List VExpr} {A : VExpr} {As : List VExpr} {u : VLevel} :
      u.WF nv → env.HasType nv Γ A (.sort u) → TeleWF env nv (A :: Γ) As →
      TeleWF env nv Γ (A :: As)

theorem TeleWF.onCtx : ∀ {Γ As : List VExpr}, TeleWF env₀ nv Γ As →
    OnCtx Γ (env₀.IsType nv) → OnCtx (As.reverse ++ Γ) (env₀.IsType nv)
  | _, _, .nil, hΓ => hΓ
  | _, _, .cons _ hA ht, hΓ => by
    simpa using ht.onCtx (Γ := _ :: _) ⟨hΓ, _, hA⟩

/-- **The sort of `mkPi As B`, and the only thing about it that matters.**  The level is
produced by the induction (a right fold of `imax` over the telescope's levels); the third
conjunct is the whole content: it is `0` exactly when `B`'s level is, at *every* valuation. -/
theorem exists_sort_mkPi : ∀ {Γ As : List VExpr} {B : VExpr} {v : VLevel},
    TeleWF env₀ nv Γ As → v.WF nv → env₀.HasType nv (As.reverse ++ Γ) B (.sort v) →
    ∃ w : VLevel, w.WF nv ∧ env₀.HasType nv Γ (VExpr.mkPi As B) (.sort w) ∧
      ∀ ls : List ℕ, (w.eval ls = 0 ↔ v.eval ls = 0)
  | _, _, _, v, .nil, hv, hB => ⟨v, hv, by simpa using hB, fun _ => Iff.rfl⟩
  | _, _, _, _, .cons (u := u) hu hA ht, hv, hB => by
    obtain ⟨w, hw, hP, he⟩ := exists_sort_mkPi ht hv (by simpa using hB)
    exact ⟨.imax u w, ⟨hu, hw⟩, .forallEDF hA hP, fun ls =>
      imax_eq_zero_iff.trans (he ls)⟩

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
/-- **The `IsProp` decision for a whole telescope is the body's.**  `interp`'s `forallE` clause
needs one decision per binder; this says all `n` of them are the same decision, so a peel needs
exactly one hypothesis about the body and nothing per binder. -/
theorem isProp_mkPi_iff (hle : env₀ ≤ envF) {Γ As : List VExpr} {B : VExpr} {v : VLevel}
    (hΓ : OnCtx Γ (env₀.IsType nv)) (ht : TeleWF env₀ nv Γ As) (hv : v.WF nv)
    (hB : env₀.HasType nv (As.reverse ++ Γ) B (.sort v)) :
    L.IsProp M Γ (VExpr.mkPi As B) ↔ L.IsProp M (As.reverse ++ Γ) B := by
  obtain ⟨w, hw, hP, he⟩ := exists_sort_mkPi ht hv hB
  rw [isProp_iff hle hΓ hP hw, isProp_iff hle (ht.onCtx hΓ) hB hv]
  exact he M.ls

/-! ## 3. One binder off a `mkForallType`

The three per-declaration peels all go the *introduction* way — build a `mkLam` and show it
lands in `interp`'s `mkForallType` (`UnitOracleLarge.mkLam_mem_mkForallType_of_dom`).  The peel
`eq_singleton_of_recProp` consumes goes the other way: given an inhabitant of the recursor type,
*apply* it.  That elimination step is this. -/

/-- **Applying an element of a `mkForallType`.**  The dual of
`UnitOracleLarge.mkLam_mem_mkForallType_of_dom`, and the atomic step of the peel. -/
theorem apply_mem_of_mem_mkForallType {G : V → V} {hG : ℒₛₑₜ-function₁[V] G}
    {F : V → V → V} {hF : ℒₛₑₜ-function₂[V] F} {ρ f v : V}
    (hf : f ∈ mkForallType G hG F hF ρ) (hv : v ∈ G ρ) : f ‘ v ∈ F ρ v := by
  obtain ⟨hfun, hcod⟩ := mem_mkForallType_iff.1 hf
  obtain ⟨y, hy, -⟩ := (mem_function_iff.1 hfun).2 v hv
  have : IsFunction f := IsFunction.of_mem hfun
  have hg : (⟨v, f ‘ v⟩ₖ : V) ∈ f := by rw [value_eq_of_kpair_mem hy]; exact hy
  exact hcod v hv _ hg

/-! ## 4. The general peel

`PeelArgs M L B Γ As ρ vs` records an argument list `vs` for the telescope `As` over `Γ`
together with the two side conditions `interp` needs at each binder: the codomain is not a
proposition (so the `forallE` clause is `mkForallType`, not `mkForallProp`), and the argument
lies in the binder's denotation.  `isProp_mkPi_iff` reduces the first family to one decision
about `B`; §5 supplies the second at a recursor type. -/

/-- The peel's data: an argument for each binder, in its denotation, with the codomain not a
proposition. -/
inductive PeelArgs (M : ModelData V) (L : PropSplit envF nv) (B : VExpr) :
    List VExpr → List VExpr → V → List V → Prop
  | nil {Γ : List VExpr} {ρ : V} : PeelArgs M L B Γ [] ρ []
  | cons {Γ : List VExpr} {A : VExpr} {As : List VExpr} {ρ v : V} {vs : List V} :
      ¬ L.IsProp M (A :: Γ) (VExpr.mkPi As B) →
      v ∈ (interp M L Γ A).toFun ρ →
      PeelArgs M L B (A :: Γ) As (snoc ρ v) vs →
      PeelArgs M L B Γ (A :: As) ρ (v :: vs)

/-- `appAll f [v₁,…,vₙ] = f ‘ v₁ ‘ ⋯ ‘ vₙ`, the set-theoretic saturated application. -/
noncomputable def appAll (f : V) : List V → V
  | [] => f
  | v :: vs => appAll (f ‘ v) vs

/-- `snocs ρ [v₁,…,vₙ]` extends the valuation by the whole argument list. -/
noncomputable def snocs (ρ : V) : List V → V
  | [] => ρ
  | v :: vs => snocs (snoc ρ v) vs

set_option linter.unusedSectionVars false in
@[simp] theorem appAll_nil (f : V) : appAll f [] = f := rfl

set_option linter.unusedSectionVars false in
@[simp] theorem appAll_cons (f v : V) (vs : List V) : appAll f (v :: vs) = appAll (f ‘ v) vs := rfl

set_option linter.unusedSectionVars false in
@[simp] theorem snocs_nil (ρ : V) : snocs ρ [] = ρ := rfl

set_option linter.unusedSectionVars false in
@[simp] theorem snocs_cons (ρ v : V) (vs : List V) :
    snocs ρ (v :: vs) = snocs (snoc ρ v) vs := rfl

/-- **THE GENERAL PEEL.**  An inhabitant of `⟦mkPi As B⟧`, applied to a legal argument list for
`As`, lands in `⟦B⟧` at the extended valuation — for an arbitrary telescope, an arbitrary body,
an arbitrary environment and an arbitrary `PropSplit`.

This is what `SetModel/UnitOracleLarge.lean`, `EqRecLarge.lean` and `IffRecLarge.lean` each do
by hand at one declaration with a fixed number of binders. -/
theorem appAll_mem_interp_of_peel {B : VExpr} {Γ As : List VExpr} {ρ : V} {vs : List V}
    (h : PeelArgs M L B Γ As ρ vs) : ∀ f : V,
      f ∈ (interp M L Γ (VExpr.mkPi As B)).toFun ρ →
      appAll f vs ∈ (interp M L (As.reverse ++ Γ) B).toFun (snocs ρ vs) := by
  induction h with
  | nil => intro f hf; simpa using hf
  | cons hnp hv _ ih =>
    intro f hf
    rw [VExpr.mkPi_cons, interp_forallE_type M L hnp] at hf
    simpa using ih _ (apply_mem_of_mem_mkForallType hf hv)

/-! ## 5. `not_isProof` for a *term of a type-former type* — the motive case

§1's `not_isProof_of_isType` is the `As = []` case of the following, and the motive needs the
general one: a motive's type is `S ps → Sort u`, a Π *ending* in a sort rather than a sort. -/

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
/-- **A term whose type is a type former is not a proof.**  `StructEtaPrice.lean` §8's owed step
2 in the generality the peel needs: `e : ∀ As, Sort u` is never a proof, at every valuation and
with no condition on `u`, because `∀ As, Sort u` has sort `w` with
`w.eval ls = 0 ↔ (u+1).eval ls = 0` (`exists_sort_mkPi`), and the right-hand side is false. -/
theorem not_isProof_of_typeFormer (hle : env₀ ≤ envF) {Γ As : List VExpr} {e : VExpr}
    {u : VLevel} (hΓ : OnCtx Γ (env₀.IsType nv)) (ht : TeleWF env₀ nv Γ As) (hw : u.WF nv)
    (he : env₀.HasType nv Γ e (VExpr.mkPi As (.sort u))) : ¬ L.IsProof M Γ e := by
  obtain ⟨w, hww, hP, hev⟩ :=
    exists_sort_mkPi (B := .sort u) (v := .succ u) ht hw (.sortDF hw hw (.refl _))
  intro hp
  have h0 := (isProof_iff (M := M) (L := L) hle hΓ he hP hww).mp hp
  have := (hev M.ls).1 h0
  simp [VLevel.eval] at this

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
/-- **The motive variable is not a proof**, from its context entry alone.  This is the form the
recursor-type peel calls: the head of `recType`'s body is a `.bvar` whose context entry is
`D.motiveType t`, which is a `mkPi` ending in `.sort D.elimLvl`. -/
theorem not_isProof_bvar_of_typeFormer (hle : env₀ ≤ envF) {Γ As : List VExpr} {i : ℕ}
    {u : VLevel} (hΓ : OnCtx Γ (env₀.IsType nv)) (ht : TeleWF env₀ nv Γ As) (hw : u.WF nv)
    (hL : Lookup Γ i (VExpr.mkPi As (.sort u))) : ¬ L.IsProof M Γ (.bvar i) :=
  not_isProof_of_typeFormer hle hΓ ht hw (.bvar hL)

end

/-! ## 6. `recType` as a `mkPi`, for an arbitrary block

`VInductDecl'.recType` is *already* an `mkPi` — of the parameter, motive, minor and index
blocks — followed by one more `forallE` for the major premise.  `recPiTele` folds the major
premise into the telescope so that the whole type is a single `mkPi`, which is what §4's peel
consumes. -/

end Lean4Lean.SetModel

namespace Lean4Lean.VInductDecl'

open Lean4Lean.VExpr (mkPi bvars liftTele)

variable (D : VInductDecl')

/-- **`recType`'s complete binder telescope**: parameters, motives, minors, indices, and the
major premise, in declaration order. -/
def recPiTele (j : Nat) : List VExpr :=
  let T := D.types.getD j default
  let ni := T.indices.length
  D.atRecTele D.params ++ D.motives ++ D.minors ++
    VExpr.liftTele (D.nm + D.nmin) (D.atRecTele T.indices) ++
    [D.tyApp' j (ni + D.nmin + D.nm) (VExpr.bvars 0 ni)]

/-- **`recType`'s body under `recPiTele`**: `motive_j indices major`. -/
def recPiBody (j : Nat) : VExpr :=
  let T := D.types.getD j default
  let ni := T.indices.length
  (VExpr.bvar (1 + ni + D.nmin + (D.nm - 1 - j))).mkApp (VExpr.bvars 1 ni ++ [.bvar 0])

/-- **The decomposition.**  Pure `mkPi` bookkeeping — no typing, no environment. -/
theorem recType_eq_mkPi (j : Nat) : D.recType j = VExpr.mkPi (D.recPiTele j) (D.recPiBody j) := by
  simp [VInductDecl'.recType, recPiTele, recPiBody, VExpr.mkPi_append]

/-- The same after `instL`, which is the form an oracle obligation
(`InductOracleOK.type`: `o (S.rec) us ∈ interp (D.recType j).instL us`) presents. -/
theorem recType_instL_eq_mkPi (j : Nat) (us : List VLevel) :
    (D.recType j).instL us =
      VExpr.mkPi ((D.recPiTele j).map (VExpr.instL us)) ((D.recPiBody j).instL us) := by
  rw [D.recType_eq_mkPi j, VExpr.instL_mkPi]

/-- **A non-indexed member's motive type is a one-binder `mkPi` ending in a sort.**  This is what
makes owed step 2 apply at a motive variable: it is a *type former*, not a sort. -/
theorem motiveType_eq_mkPi_sort {t : Nat} (hi : (D.types.getD t default).indices = []) :
    D.motiveType t = VExpr.mkPi [D.tyApp' t t []] (.sort D.elimLvl) := by
  rw [List.getD_eq_getElem?_getD] at hi
  simp [motiveType, hi]

theorem recPiTele_length (j : Nat) :
    (D.recPiTele j).length = D.np + D.nm + D.nmin + (D.types.getD j default).indices.length + 1 := by
  simp [recPiTele, VInductDecl'.atRecTele, VInductDecl'.np, VInductDecl'.motives,
    VInductDecl'.minors, VInductDecl'.nm, VInductDecl'.nmin]
  omega

end Lean4Lean.VInductDecl'

namespace Lean4Lean.SetModel

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V]

section
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF env₀ : VEnv} {nv : ℕ} {M : ModelData V} {L : PropSplit envF nv}

/-- **THE GENERAL `interp (D.recType j)` PEEL** — `StructEtaPrice.lean` §8's owed step 1.

For an arbitrary block `D`, an arbitrary member `j`, an arbitrary environment and an arbitrary
`PropSplit`: an inhabitant of the recursor type's denotation, applied to a legal argument list
for its complete telescope (parameters, motives, minors, indices, major premise), lands in the
denotation of `motive_j indices major`.

The three peels in `Theory/SetModel/` do this at `unitDeclLE`, `eqIndDecl` and `iffIndDecl` with
the binder count hardcoded; this quantifies over `D`. -/
theorem appAll_mem_interp_recPiBody {D : VInductDecl'} {j : Nat} {Γ : List VExpr} {ρ : V}
    {vs : List V} (h : PeelArgs M L (D.recPiBody j) Γ (D.recPiTele j) ρ vs) (f : V)
    (hf : f ∈ (interp M L Γ (D.recType j)).toFun ρ) :
    appAll f vs ∈
      (interp M L ((D.recPiTele j).reverse ++ Γ) (D.recPiBody j)).toFun (snocs ρ vs) :=
  appAll_mem_interp_of_peel h f (D.recType_eq_mkPi j ▸ hf)

/-- The `instL` form, which is what an `InductOracleOK.type` obligation hands you. -/
theorem appAll_mem_interp_recPiBody_instL {D : VInductDecl'} {j : Nat} {us : List VLevel}
    {Γ : List VExpr} {ρ : V} {vs : List V}
    (h : PeelArgs M L ((D.recPiBody j).instL us) Γ ((D.recPiTele j).map (VExpr.instL us)) ρ vs)
    (f : V) (hf : f ∈ (interp M L Γ ((D.recType j).instL us)).toFun ρ) :
    appAll f vs ∈ (interp M L (((D.recPiTele j).map (VExpr.instL us)).reverse ++ Γ)
      ((D.recPiBody j).instL us)).toFun (snocs ρ vs) :=
  appAll_mem_interp_of_peel h f (D.recType_instL_eq_mkPi j us ▸ hf)

/-! ## 7. The **propositional** peel — the one `eq_singleton_of_recProp` consumes

A trap, and it is worth recording because it invalidated the first version of this section.
`interp`'s `forallE` clause branches on whether the **codomain** is a proposition, not the
domain.  At `elimLvl = .zero` the *whole* recursor type is propositional, so **every** binder of
`recType` — the motive binder included, whose domain is a type — takes the `mkForallProp` branch.
`eq_singleton_of_recProp`'s hypothesis is stated at `UProp ^ Sv`, i.e. at the small eliminator, so
the peel it consumes is this one and not §4's.

§4 is not thereby idle: it is the *large*-eliminator route, and it is what
`UnitOracleLarge.lean`, `EqRecLarge.lean` and `IffRecLarge.lean` each perform by hand at their
large slices.  The two peels are the two branches of one `interp` clause, and
`isProp_mkPi_iff` is what decides which of them applies — from a single fact about the body. -/

/-- The propositional peel's data.  Same as `PeelArgs` with the sign of the `IsProp` condition
flipped; `isProp_mkPi_iff` supplies the whole family from one decision about `B`. -/
inductive PeelArgsP (M : ModelData V) (L : PropSplit envF nv) (B : VExpr) :
    List VExpr → List VExpr → V → List V → Prop
  | nil {Γ : List VExpr} {ρ : V} : PeelArgsP M L B Γ [] ρ []
  | cons {Γ : List VExpr} {A : VExpr} {As : List VExpr} {ρ v : V} {vs : List V} :
      L.IsProp M (A :: Γ) (VExpr.mkPi As B) →
      v ∈ (interp M L Γ A).toFun ρ →
      PeelArgsP M L B (A :: Γ) As (snoc ρ v) vs →
      PeelArgsP M L B Γ (A :: As) ρ (v :: vs)

/-- **THE GENERAL PROPOSITIONAL PEEL.**  An inhabitant of `⟦mkPi As B⟧` where the telescope is
propositional throughout lands, *unchanged*, in `⟦B⟧` at the extended valuation — for every legal
argument list.  (Unchanged because `mkForallProp` collapses the function to `pt`: this is proof
irrelevance in the model, and it is why the recursor's *value* never appears in
`eq_singleton_of_recProp`'s hypothesis.) -/
theorem mem_interp_of_peelP {B : VExpr} {Γ As : List VExpr} {ρ : V} {vs : List V}
    (h : PeelArgsP M L B Γ As ρ vs) : ∀ f : V,
      f ∈ (interp M L Γ (VExpr.mkPi As B)).toFun ρ →
      f ∈ (interp M L (As.reverse ++ Γ) B).toFun (snocs ρ vs) := by
  induction h with
  | nil => intro f hf; simpa using hf
  | cons hp hv _ ih =>
    intro f hf
    rw [VExpr.mkPi_cons, interp_forallE_prop M L hp] at hf
    simpa using ih f ((mem_mkForallProp_iff.1 hf).2 _ hv)

/-- The propositional peel at `D.recType j`, for an arbitrary block: **owed step 1, small
eliminator.** -/
theorem mem_interp_recPiBody_of_peelP {D : VInductDecl'} {j : Nat} {Γ : List VExpr} {ρ : V}
    {vs : List V} (h : PeelArgsP M L (D.recPiBody j) Γ (D.recPiTele j) ρ vs) (f : V)
    (hf : f ∈ (interp M L Γ (D.recType j)).toFun ρ) :
    f ∈ (interp M L ((D.recPiTele j).reverse ++ Γ) (D.recPiBody j)).toFun (snocs ρ vs) :=
  mem_interp_of_peelP h f (D.recType_eq_mkPi j ▸ hf)

/-- The `instL` form, which is what an `InductOracleOK.type` obligation hands you. -/
theorem mem_interp_recPiBody_of_peelP_instL {D : VInductDecl'} {j : Nat} {us : List VLevel}
    {Γ : List VExpr} {ρ : V} {vs : List V}
    (h : PeelArgsP M L ((D.recPiBody j).instL us) Γ ((D.recPiTele j).map (VExpr.instL us)) ρ vs)
    (f : V) (hf : f ∈ (interp M L Γ ((D.recType j).instL us)).toFun ρ) :
    f ∈ (interp M L (((D.recPiTele j).map (VExpr.instL us)).reverse ++ Γ)
      ((D.recPiBody j).instL us)).toFun (snocs ρ vs) :=
  mem_interp_of_peelP h f (D.recType_instL_eq_mkPi j us ▸ hf)

/-! ## 8. Surjective pairing, forced — the peel composed with `eq_singleton_of_recProp`

Three binders (motive, minor, major): the zero-field, one-constructor, index-free,
parameter-free shape `eq_singleton_of_recProp` is about.  Everything per-declaration is isolated
into the four `interp` equations `hmot`/`hmin`/`hmaj`/`hbody`; the three `IsProp` facts come from
`isProp_mkPi_iff` and one decision about the body. -/

/-- **Structure eta is forced in the set model, from the recursor's type obligation alone.**

`hf` is `OracleOK.type` at the recursor, `hpt` is the model's proof object being the unique
inhabitant of a propositional denotation.  The conclusion is that the type former's denotation
is the singleton `{mkv}` — surjective pairing, i.e. `VEnv.UnitEta.unitLike`.

This is `Theory/Typing/StructEtaPrice.lean` §8's "what is still owed", discharged: the peel
(§7) supplies exactly `eq_singleton_of_recProp`'s hypothesis. -/
theorem eq_singleton_of_mem_interp_mkPi3 {Γ : List VExpr} {Am Ap Ax B : VExpr}
    {ρ f Sv mkv : V}
    (hpm : L.IsProp M (Am :: Γ) (VExpr.mkPi [Ap, Ax] B))
    (hpp : L.IsProp M (Ap :: Am :: Γ) (VExpr.mkPi [Ax] B))
    (hpx : L.IsProp M (Ax :: Ap :: Am :: Γ) B)
    (hmot : (interp M L Γ Am).toFun ρ = ((UProp : V) ^ Sv : V))
    (hmin : ∀ m ∈ ((UProp : V) ^ Sv : V),
      (interp M L (Am :: Γ) Ap).toFun (snoc ρ m) = m ‘ mkv)
    (hmaj : ∀ m ∈ ((UProp : V) ^ Sv : V), ∀ p ∈ m ‘ mkv,
      (interp M L (Ap :: Am :: Γ) Ax).toFun (snoc (snoc ρ m) p) = Sv)
    (hbody : ∀ m ∈ ((UProp : V) ^ Sv : V), ∀ p ∈ m ‘ mkv, ∀ x ∈ Sv,
      (interp M L (Ax :: Ap :: Am :: Γ) B).toFun (snoc (snoc (snoc ρ m) p) x) = m ‘ x)
    (hmk : mkv ∈ Sv) (hf : f ∈ (interp M L Γ (VExpr.mkPi [Am, Ap, Ax] B)).toFun ρ) :
    Sv = ({mkv} : V) := by
  refine eq_singleton_of_recProp hmk (fun m hm hpt x hx ↦ ?_)
  have hpeel : PeelArgsP M L B Γ [Am, Ap, Ax] ρ [m, pt, x] :=
    .cons hpm (by rw [hmot]; exact hm)
      (.cons hpp (by rw [hmin m hm]; exact hpt)
        (.cons hpx (by rw [hmaj m hm pt hpt]; exact hx) .nil))
  have hgoal := mem_interp_of_peelP hpeel f hf
  simp only [snocs_cons, snocs_nil] at hgoal
  rw [show ([Am, Ap, Ax] : List VExpr).reverse ++ Γ = Ax :: Ap :: Am :: Γ from rfl,
    hbody m hm pt hpt x hx] at hgoal
  -- `m ‘ x` is a proposition and it has an element, so that element is `pt`
  have hmx : m ‘ x ∈ (UProp : V) := by
    have hfun : IsFunction m := IsFunction.of_mem hm
    obtain ⟨y, hy, -⟩ := (mem_function_iff.1 hm).2 x hx
    have hg : (⟨x, m ‘ x⟩ₖ : V) ∈ m := by rw [value_eq_of_kpair_mem hy]; exact hy
    exact (mem_of_mem_functions hm hg).2
  exact (mem_singleton_iff.mp (mem_UProp_iff.mp hmx _ hgoal)) ▸ hgoal

/-! ## 9. `motiveType` is a type former, for every non-indexed block

Owed step 2 at the site that actually needs it: the head of `recPiBody` is a `.bvar` whose
context entry is `D.motiveType t`.  For a non-indexed member that entry is literally a one-binder
`mkPi` ending in `.sort D.elimLvl`, so §5 applies. -/

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
/-- **A motive variable of a non-indexed block is not a proof.**  General in `D`, `t` and the
context; the only inputs are that the block member has no indices and that its saturated type
former is a type. -/
theorem not_isProof_motive_bvar (hle : env₀ ≤ envF) {D : VInductDecl'} {t i : Nat}
    {Γ : List VExpr} {w : VLevel}
    (hi : (D.types.getD t default).indices = [])
    (hΓ : OnCtx Γ (env₀.IsType nv)) (hwe : D.elimLvl.WF nv) (hww : w.WF nv)
    (hty : env₀.HasType nv Γ (D.tyApp' t t []) (.sort w))
    (hL : Lookup Γ i (D.motiveType t)) : ¬ L.IsProof M Γ (.bvar i) := by
  rw [D.motiveType_eq_mkPi_sort hi] at hL
  exact not_isProof_bvar_of_typeFormer hle hΓ (.cons hww hty .nil) hwe hL

end

/-! ## 10. Firing: `unitDeclLE`

The general definitions of §6 are checked against `UnitOracleLarge.lean`'s hand-written
decomposition, `isProp_mkPi_iff` re-derives one of its three hand-computed level facts, and §8's
hypothesis bundle is shown satisfiable at a real declaration. -/

namespace UnitAudit

open Lean4Lean.SetModel.UnitAudit

/-- §6's general telescope, at `unitDeclLE`: the motive, the minor, the major premise. -/
theorem unitDeclLE_recPiTele : unitDeclLE.recPiTele 0 = [motTyL, minTy, .const `Unit1 []] := rfl

/-- §6's general body, at `unitDeclLE`. -/
theorem unitDeclLE_recPiBody : unitDeclLE.recPiBody 0 = .app (.bvar 2) (.bvar 0) := rfl

/-- **§6's general decomposition agrees with `unitDeclLE_recType_instL`**, which was written by
hand.  This is the check that `recPiTele`/`recPiBody` are the right general definitions. -/
theorem unitDeclLE_recType_instL_mkPi (u : VLevel) :
    (unitDeclLE.recType 0).instL [u] =
      VExpr.mkPi [motTyU u, minTy, .const `Unit1 []] (.app (.bvar 2) (.bvar 0)) := by
  rw [unitDeclLE.recType_instL_eq_mkPi 0 [u], unitDeclLE_recPiTele, unitDeclLE_recPiBody]; rfl

theorem unitDeclLE_recPiTele_length : (unitDeclLE.recPiTele 0).length = 3 := by
  rw [unitDeclLE.recPiTele_length 0]; rfl

section
variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ} (L : PropSplit envF nv) (κ : ℕ → V) (ls : List ℕ)
variable {u : VLevel} (hu : u.WF nv) (hle : unitEnvLE ≤ envF)

omit [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
include hu hle in
/-- **`isPropL_recB1_iff` re-derived from `isProp_mkPi_iff`.**  `UnitOracleLarge.lean` computes
the level of each of the three nested `forallE`s by hand (`isPropL_recB1_iff`,
`isPropL_recB2_iff`, `isPropL_recB3_iff`, three separate `imax` computations); the general lemma
does all three from the innermost one. -/
theorem isPropL_recB1_iff' (Γ : List VExpr) (hΓ : OnCtx Γ (unitEnvLE.IsType nv)) :
    L.IsProp (unitML κ ls) (motTyU u :: Γ)
      (VExpr.mkPi [minTy, .const `Unit1 []] (.app (.bvar 2) (.bvar 0)))
    ↔ u.eval ls = 0 := by
  rw [isProp_mkPi_iff (M := unitML κ ls) hle (onCtxL_mot hu hΓ)
      (.cons (u := u) hu (hasTypeL_minTy) (.cons (u := .zero) trivial hasTypeL_Unit1 .nil))
      hu hasTypeL_recBody]
  rw [show ([minTy, .const `Unit1 []] : List VExpr).reverse ++ motTyU u :: Γ
      = .const `Unit1 [] :: minTy :: motTyU u :: Γ from rfl]
  rw [isProp_iff hle (onCtxL_unit hu hΓ) hasTypeL_recBody (u := u) hu, unitML_ls]

include hu hle in
/-- **The type former's denotation at `unitDeclLE` is a singleton — derived from the recursor's
type obligation through §8, not from the oracle's definition.**

Every input of `eq_singleton_of_mem_interp_mkPi3` is discharged here: the three `IsProp` facts
(`isPropL_recB{1,2,3}_iff` at the `Prop` slice), the four `interp` equations, and `hf`, which is
`pt_mem_interpL_recType_of_zero` — i.e. `OracleOK.type` at the recursor.

At `unitDeclLE` the conclusion is *also* available directly (the oracle sends `Unit1 ↦ {•}`
by definition, `interpL_Unit1`), so this firing is a consistency check rather than news.  Its
purpose is that §8's hypothesis bundle is **satisfiable at a real declaration**: the general
lemma is not vacuous.  §8 is news exactly where the type former's denotation is not a priori a
singleton, which is the general zero-field structure `StructEtaPrice.lean` §8 is about. -/
theorem unitL_denot_eq_singleton_of_zero (h0 : u.eval ls = 0) :
    (interp (unitML κ ls) L [] (.const `Unit1 [])).toFun ∅ = ({pt} : V) := by
  have hU : ∀ (Δ : List VExpr) (r : V),
      (interp (unitML κ ls) L Δ (.const `Unit1 [])).toFun r = ({pt} : V) :=
    fun Δ r => interpL_Unit1 L κ ls Δ r
  have hρ0 := interpCtxL_nil L κ ls
  have hmot : (interp (unitML κ ls) L [] (motTyU u)).toFun ∅
      = ((UProp : V) ^ (interp (unitML κ ls) L [] (.const `Unit1 [])).toFun ∅ : V) := by
    rw [interpL_motTyU L κ ls hu hle [] trivial, h0, U_zero, hU]
  have hf0 : ∀ m : V, (snoc (∅ : V) m) ‘ ((0 : ℕ) : V) = m :=
    fun m => snoc_value_at_len (Γ := []) (unitML κ ls) L hρ0
  have hmin : ∀ m : V, (interp (unitML κ ls) L [motTyU u] minTy).toFun (snoc ∅ m) = m ‘ (pt : V) :=
    fun m => interpL_minTy L κ ls hu hle (hf0 m)
  refine eq_singleton_of_mem_interp_mkPi3 (M := unitML κ ls) (L := L)
    (Γ := []) (Am := motTyU u) (Ap := minTy) (Ax := .const `Unit1 [])
    (B := .app (.bvar 2) (.bvar 0)) (ρ := ∅) (f := pt)
    (Sv := (interp (unitML κ ls) L [] (.const `Unit1 [])).toFun ∅) (mkv := pt)
    ((isPropL_recB1_iff L κ ls hu hle [] trivial).mpr h0)
    ((isPropL_recB2_iff L κ ls hu hle [] trivial).mpr h0)
    ((isPropL_recB3_iff L κ ls hu hle [] trivial).mpr h0)
    hmot (fun m _ => hmin m) (fun m _ p _ => (hU _ _).trans (hU _ _).symm) ?hbody
    (by rw [hU]; simp) ?hf
  case hbody =>
    intro m hm p hp x hx
    have h1 : snoc (∅ : V) m ∈ interpCtx (unitML κ ls) L [motTyU u] :=
      (mem_interpCtx_cons (unitML κ ls) L).mpr
        ⟨∅, hρ0, m, by rw [hmot]; exact hm, rfl⟩
    have h2 : snoc (snoc (∅ : V) m) p ∈ interpCtx (unitML κ ls) L [minTy, motTyU u] :=
      (mem_interpCtx_cons (unitML κ ls) L).mpr ⟨_, h1, p, by rw [hmin m]; exact hp, rfl⟩
    have e0 : (snoc (snoc (snoc (∅ : V) m) p) x) ‘ ((0 : ℕ) : V) = m :=
      ((snoc_value_of_lt (Γ := [minTy, motTyU u]) (unitML κ ls) L h2 (j := 0) (by simp)).trans
        (snoc_value_of_lt (Γ := [motTyU u]) (unitML κ ls) L h1 (j := 0) (by simp))).trans (hf0 m)
    have e2 : (snoc (snoc (snoc (∅ : V) m) p) x) ‘ ((2 : ℕ) : V) = x :=
      snoc_value_at_len (Γ := [minTy, motTyU u]) (unitML κ ls) L h2
    exact interpL_recBody L κ ls hu hle e0 e2
  case hf =>
    have h := pt_mem_interpL_recType_of_zero L κ ls hu hle h0
    rwa [unitDeclLE_recType_instL_mkPi] at h

end

end UnitAudit

/-! ## 11. Firing: `ntreeAux`, the parameterised nested block -/

namespace InductiveDeclExamples

open Lean4Lean.InductiveDeclExamples

/-- §6's general telescope at the nested block's **own** member: parameter, two motives, three
minors, no indices, major premise. -/
theorem ntreeAux_recPiTele_length : (ntreeAux.recPiTele 0).length = 7 := by
  rw [ntreeAux.recPiTele_length 0]; rfl

theorem ntreeAux_recPiTele_length_1 : (ntreeAux.recPiTele 1).length = 7 := by
  rw [ntreeAux.recPiTele_length 1]; rfl

/-- Both members of the nested block are index-free, so §9 applies to both motives. -/
theorem ntreeAux_indices_nil : ∀ j, (ntreeAux.types.getD j default).indices = []
  | 0 => rfl
  | 1 => rfl
  | _ + 2 => rfl

/-- §9's shape at the nested block's own motive. -/
theorem ntreeAux_motiveType_mkPi (t : Nat) :
    ntreeAux.motiveType t = VExpr.mkPi [ntreeAux.tyApp' t t []] (.sort ntreeAux.elimLvl) :=
  ntreeAux.motiveType_eq_mkPi_sort (ntreeAux_indices_nil t)

/-- §6's decomposition at the nested block, both members. -/
theorem ntreeAux_recType_mkPi (j : Nat) :
    ntreeAux.recType j = VExpr.mkPi (ntreeAux.recPiTele j) (ntreeAux.recPiBody j) :=
  ntreeAux.recType_eq_mkPi j

end InductiveDeclExamples

end Lean4Lean.SetModel

/-! ## Status

Every declaration below is `sorryAx`-free; the `#print axioms` block is the check.

**What this file settles.**  Both steps `Theory/Typing/StructEtaPrice.lean` §8 records as owed
by the set model:

* Step 1, the peel, in **both** branches of `interp`'s `forallE` clause —
  `appAll_mem_interp_of_peel` (`mkForallType`, the large eliminator) and
  `mem_interp_of_peelP` (`mkForallProp`, the small eliminator), each general in the telescope,
  the body, the environment and the `PropSplit`; fired at `D.recType j` for an arbitrary block
  by `appAll_mem_interp_recPiBody` / `mem_interp_recPiBody_of_peelP` (and their `instL` forms,
  which are the shape an `InductOracleOK.type` obligation presents).
* Step 2, `sort_not_proof`, in the form the peel consumes — `not_isProof_of_typeFormer`, with
  `not_isProof_of_isType` and `sort_not_proof` as its `As = []` case and
  `not_isProof_motive_bvar` as its application at a motive variable.

**And it records one trap.**  `interp`'s `forallE` clause branches on the **codomain**, so at
`elimLvl = .zero` every binder of `recType` — the motive binder included — is `mkForallProp`.
`eq_singleton_of_recProp`'s hypothesis lives at `UProp`, hence at that slice, hence needs §7 and
not §4.  A composition built on §4 with a `UProp ^ Sv` motive space (the first version of §8 in
this file) has hypotheses that the intended instance does not satisfy.

**What is *not* here.**  A general `TeleWF env (D.recPiTele j)` from `D.RecCtx env`: the
telescope typings exist (`VInductDecl'.RecCtx.onCtxParams`, `onCtxMotives`, `onCtxMinors`,
`recType_isType` in `Theory/Inductive/Lemmas.lean`) but they carry `OnCtx`, which does not record
level well-formedness, and `PropSplit`'s two fields do need it.  Bridging that is level
bookkeeping over `IsDefEq.levelWF`/`CtxStrong.levelWF`, not new mathematics, and it is the one
thing between §7 and a `D`-quantified surjective-pairing theorem with no `interp` equations left
as hypotheses.  Neither this nor anything else here touches `Theory/Equiconsistency.lean`'s hole
or asks Foundation for anything it does not already provide (Power, Replacement, `℘{•}`, internal
function spaces — all used by `eq_singleton_of_recProp` already). -/

#print axioms Lean4Lean.SetModel.not_isProof_of_isType
#print axioms Lean4Lean.SetModel.sort_not_proof
#print axioms Lean4Lean.SetModel.exists_sort_mkPi
#print axioms Lean4Lean.SetModel.isProp_mkPi_iff
#print axioms Lean4Lean.SetModel.apply_mem_of_mem_mkForallType
#print axioms Lean4Lean.SetModel.appAll_mem_interp_of_peel
#print axioms Lean4Lean.SetModel.not_isProof_of_typeFormer
#print axioms Lean4Lean.SetModel.not_isProof_bvar_of_typeFormer
#print axioms Lean4Lean.VInductDecl'.recType_eq_mkPi
#print axioms Lean4Lean.VInductDecl'.recType_instL_eq_mkPi
#print axioms Lean4Lean.VInductDecl'.motiveType_eq_mkPi_sort
#print axioms Lean4Lean.VInductDecl'.recPiTele_length
#print axioms Lean4Lean.SetModel.appAll_mem_interp_recPiBody
#print axioms Lean4Lean.SetModel.appAll_mem_interp_recPiBody_instL
#print axioms Lean4Lean.SetModel.mem_interp_of_peelP
#print axioms Lean4Lean.SetModel.mem_interp_recPiBody_of_peelP
#print axioms Lean4Lean.SetModel.mem_interp_recPiBody_of_peelP_instL
#print axioms Lean4Lean.SetModel.eq_singleton_of_mem_interp_mkPi3
#print axioms Lean4Lean.SetModel.not_isProof_motive_bvar
#print axioms Lean4Lean.SetModel.UnitAudit.unitDeclLE_recType_instL_mkPi
#print axioms Lean4Lean.SetModel.UnitAudit.unitDeclLE_recPiTele
#print axioms Lean4Lean.SetModel.UnitAudit.isPropL_recB1_iff'
#print axioms Lean4Lean.SetModel.UnitAudit.unitL_denot_eq_singleton_of_zero
#print axioms Lean4Lean.SetModel.InductiveDeclExamples.ntreeAux_recPiTele_length
#print axioms Lean4Lean.SetModel.InductiveDeclExamples.ntreeAux_motiveType_mkPi
#print axioms Lean4Lean.SetModel.InductiveDeclExamples.ntreeAux_recType_mkPi
