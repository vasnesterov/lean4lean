import Lean4Lean.Verify.Environment.InductR
import Lean4Lean.Verify.Inductive.ValAtParam

/-!
# `TrIndDeclN.trType`, in general

`TrIndDeclN` (`Verify/Environment/InductR.lean:276`) has twelve fields; `trIndDeclN_of_ownId`
(`TrIndDeclNProducer.lean`) discharges nine and carries three as named hypotheses.  This file is
about the first of the three.

## What the field requires, unfolded

`TrIndType` (`Verify/Environment/Induct.lean:86`) is a `def`, not a structure -- it has no
projections -- and it unfolds to a conjunction, so the field is, with nothing hidden:

```
trType : ∀ (j : Nat) (t : Lean.InductiveType) (T : VIndType),
  types[j]? = some t → D.types[j]? = some T →
    t.name = T.name ∧ TrExprS env Us [] t.type T.type
```

Three things about that statement are easy to get wrong and all three matter here.

* **`env` is the pre-block environment** and the local context is **empty**.  Unlike `trCtors`,
  this field is *not* staged over `env.addIndTypesC D K`, and it must not be: the members'
  arities are type-checked before any of the block's constants exist
  (`Inductive/Add.lean:210`'s `_ ← checkType type` inside `checkInductiveTypes`, which runs
  before `declareInductiveTypes`), and a `TrExprS.const` on a block member would be
  unsatisfiable at `env` anyway.  So the "`TrExprS` at the staged environment" the field might
  be expected to want is the wrong object for it.
* **Only the user's members are constrained.**  `types[j]? = some t` fails for every `j ≥
  types.length`, so the `numNested` auxiliary members say nothing here.  §4's
  `trType_congr_prefix` states that as an `↔`: the clause depends only on `D.types`' first
  `types.length` entries.  The nested tail makes this field no harder than `TrIndDecl.trType`.
* **`T.type` is not a free choice.**  `TrExprS` is functional wherever the surface term has no
  `.proj` (`TrExprS.unique`, `Verify/Typing/Lemmas.lean:2648`), so `TrIndType.rigid` (§2) says
  any two `T`s satisfying the field agree on both `name` and `type`.  `D` *is* existentially
  quantified at the assembly point (`AddInductiveRunRealises`,
  `Verify/Inductive/AddInductiveStep.lean:405`), but rigidity means no choice of `D` makes the
  field cheaper: the stored type is forced to be the translation.

## Why the block case is free, and what that does not give

`InductiveDeclExamples.tr_ntreeType` (`FlipConstruct.lean:121`) has **arity 1** -- one implicit
`{env : VEnv}` and no hypotheses -- and its section's five `env.constants … = some …`
variables are deliberately not `include`d.  The reason is syntactic, not special to the block:
`NTree`'s arity is `Type u → Type u`, whose translation is built from `TrExprS.forallE` and
`TrExprS.sort` alone, and `TrExprS.const` is the only constructor that reads `env.constants`
(`bvar`/`fvar` the only ones that read the context).  A sort-and-pi arity therefore translates
**at every `VEnv` whatsoever**.

§1 is exactly that observation made general, with `.mdata` allowed as well: `sortPiTr?` computes
the translation of the fragment, and `trExprS_of_sortPiTr` holds at every `env` and every
`VLCtx`.  §3's `trType_of_sortPiTr` discharges the whole field, with no environment hypothesis,
for every block all of whose members' arities are in the fragment -- every parameterised
non-indexed inductive, `NTree` and `List` included -- and `trType_iff_of_sortPiTr` makes it an
`↔` against a *decidable* equation, so on this class the field is settled in both directions and
there is nothing left for a successor to re-attack.

§6 is the boundary, machine-checked rather than asserted: an arity mentioning one constant is
outside the fragment (`sortPiTr?_none_of_const`), and at such a member no `T` satisfies the
field when that constant is undeclared (`no_trIndType_of_undeclared`).  So env-uniformity cannot
be pushed past the fragment; indexed families genuinely need the pre-block environment.

## The general case: derivable, and what it costs

For arbitrary arities the field reduces (§4, `trType_iff_exists_trans`, an `↔` with no
hypotheses) to: the arity translates at the pre-block environment, and `D` stores that
translation.  The first half is **available, not a new obligation** --
`TypeChecker.checkType.WF` (`Verify/TypeChecker.lean:197`) yields
`∃ e' ty', c.TrTyping e ty e' ty'` at the very check `checkInductiveTypes` performs, with
`TrExprS.weakFV_inv` needed only for members after the first (the check for `j ≥ 1` happens
inside the earlier members' `withLocalDecl` scopes, and `checkNoMVarNoFVar` has already
established the arity is fvar-free).  The second half is then free by rigidity.

The measured price, recorded in `docs/handoff-trtype.md` M6: that route's cone is contaminated.
`checkType.WF` has cone 18795 with eight holes and both watched `VEnv.IsDefEq.uniq` /
`IsDefEq.uniqU`; `weakFV_inv` has cone 8653 with five holes and the same two.  §4's
`exists_indTypes_of_trExprS` / `exists_indTypes_append` therefore take the translation
existential as a hypothesis and are choice-free and clean, so the contamination is confined to
whoever eventually supplies it -- while the fragment route of §1--§3 never touches the checker
and stays clean.

## §5, the vacuity guard

`ntreeAux_trType_witness` is arity 0 and existentially closed at the real staged environment,
at the **parameterised** nested block (`uvars = 1`, `params = [.sort (.succ (.param 0))]`,
`types.length = 2`), and it is reached through §3's general route: this file does not import
`FlipConstruct`, so `tr_ntreeType` is not even in scope.  Its last conjunct is the `↔` at that
block, so the witness is evidence about the route and not about the block.
-/

namespace Lean4Lean
open Lean hiding Environment Exception

/-! ## §1 The environment-uniform fragment -/

/-- The translation of an arity built from `.sort`, `.forallE` and `.mdata` alone. -/
def sortPiTr? (Us : List Name) : Expr → Option VExpr
  | .sort u => (VLevel.ofLevel Us u).map .sort
  | .forallE _ d b _ => (sortPiTr? Us d).bind fun d' => (sortPiTr? Us b).map (.forallE d' ·)
  | .mdata _ e => sortPiTr? Us e
  | _ => none

theorem sortPiTr?_isType {Us : List Name} {e : Expr} {e' : VExpr}
    (h : sortPiTr? Us e = some e') (env : VEnv) (Γ : List VExpr) :
    env.IsType Us.length Γ e' := by
  induction e generalizing e' Γ with
  | sort u =>
    simp [sortPiTr?, Option.map_eq_some_iff] at h
    obtain ⟨u', hu, rfl⟩ := h
    exact ⟨_, .sortDF (VLevel.WF.of_ofLevel hu) (VLevel.WF.of_ofLevel hu) (.refl _)⟩
  | forallE _ d b _ ihd ihb =>
    simp [sortPiTr?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨d', hd, b', hb, rfl⟩ := h
    exact (ihd hd Γ).forallE (ihb hb _)
  | mdata _ _ ih => exact ih (by simpa [sortPiTr?] using h) Γ
  | _ => simp [sortPiTr?] at h

theorem trExprS_of_sortPiTr {env : VEnv} {Us : List Name} {e : Expr} {e' : VExpr}
    (h : sortPiTr? Us e = some e') (Δ : VLCtx) : TrExprS env Us Δ e e' := by
  induction e generalizing e' Δ with
  | sort u =>
    simp [sortPiTr?, Option.map_eq_some_iff] at h
    obtain ⟨u', hu, rfl⟩ := h
    exact .sort hu
  | forallE _ d b _ ihd ihb =>
    simp [sortPiTr?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨d', hd, b', hb, rfl⟩ := h
    exact .forallE (sortPiTr?_isType hd env Δ.toCtx)
      (sortPiTr?_isType hb env (d' :: Δ.toCtx)) (ihd hd Δ) (ihb hb _)
  | mdata _ _ ih => exact .mdata (ih (by simpa [sortPiTr?] using h) Δ)
  | _ => simp [sortPiTr?] at h

theorem isUnique_of_sortPiTr {Us : List Name} {e : Expr} {e' : VExpr}
    (h : sortPiTr? Us e = some e') : TrExprS.IsUnique e := by
  induction e generalizing e' with
  | sort => trivial
  | forallE _ d b _ ihd ihb =>
    simp [sortPiTr?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨d', hd, b', hb, rfl⟩ := h
    exact ⟨ihd hd, ihb hb⟩
  | mdata _ _ ih => exact ih (by simpa [sortPiTr?] using h)
  | _ => simp [sortPiTr?] at h

/-! ## §2 The member-level obligation: rigid, and an `↔` on the fragment -/

theorem TrIndType.rigid {env : VEnv} {Us : List Name} {t : InductiveType} {T₁ T₂ : VIndType}
    (hu : TrExprS.IsUnique t.type)
    (h₁ : TrIndType env Us t T₁) (h₂ : TrIndType env Us t T₂) :
    T₁.name = T₂.name ∧ T₁.type = T₂.type :=
  ⟨h₁.1.symm.trans h₂.1, TrExprS.unique hu h₁.2 h₂.2⟩

theorem trIndType_iff_of_sortPiTr {env : VEnv} {Us : List Name} {t : InductiveType}
    {T : VIndType} {Tt : VExpr} (h : sortPiTr? Us t.type = some Tt) :
    TrIndType env Us t T ↔ (t.name = T.name ∧ T.type = Tt) := by
  refine ⟨fun ⟨hn, htr⟩ => ⟨hn, TrExprS.unique (isUnique_of_sortPiTr h) htr
    (trExprS_of_sortPiTr h _)⟩, fun ⟨hn, ht⟩ => ⟨hn, ?_⟩⟩
  exact ht ▸ trExprS_of_sortPiTr h _

/-! ## §3 The field: a producer and an `↔`, both uniform in `env` -/

theorem trType_of_sortPiTr {env : VEnv} {Us : List Name} {types : List InductiveType}
    {D : VInductDecl'}
    (h : ∀ (j : Nat) t T, types[j]? = some t → D.types[j]? = some T →
      t.name = T.name ∧ sortPiTr? Us t.type = some T.type) :
    ∀ (j : Nat) t T, types[j]? = some t → D.types[j]? = some T → TrIndType env Us t T := by
  intro j t T ht hT
  obtain ⟨hn, hfr⟩ := h j t T ht hT
  exact (trIndType_iff_of_sortPiTr hfr).2 ⟨hn, rfl⟩

theorem trType_iff_of_sortPiTr {env : VEnv} {Us : List Name} {types : List InductiveType}
    {D : VInductDecl'}
    (hfrag : ∀ (j : Nat) t, types[j]? = some t → ∃ Tt, sortPiTr? Us t.type = some Tt) :
    (∀ (j : Nat) t T, types[j]? = some t → D.types[j]? = some T → TrIndType env Us t T) ↔
    (∀ (j : Nat) t T, types[j]? = some t → D.types[j]? = some T →
      t.name = T.name ∧ sortPiTr? Us t.type = some T.type) := by
  refine ⟨fun h j t T ht hT => ?_, trType_of_sortPiTr⟩
  obtain ⟨Tt, hTt⟩ := hfrag j t ht
  obtain ⟨hn, he⟩ := (trIndType_iff_of_sortPiTr hTt).1 (h j t T ht hT)
  exact ⟨hn, he ▸ hTt⟩

/-! ## §4 The general case: what the field is, and that it is satisfiable -/

theorem trType_congr_prefix {env : VEnv} {Us : List Name} {types : List InductiveType}
    {D₁ D₂ : VInductDecl'}
    (h : ∀ j, j < types.length → D₁.types[j]? = D₂.types[j]?) :
    (∀ (j : Nat) t T, types[j]? = some t → D₁.types[j]? = some T → TrIndType env Us t T) ↔
    (∀ (j : Nat) t T, types[j]? = some t → D₂.types[j]? = some T → TrIndType env Us t T) := by
  constructor <;> intro H j t T ht hT <;>
    exact H j t T ht (by
      first
        | rw [h j (List.getElem?_eq_some_iff.1 ht).1]; exact hT
        | rw [← h j (List.getElem?_eq_some_iff.1 ht).1]; exact hT)

theorem trType_iff_exists_trans {env : VEnv} {Us : List Name} {types : List InductiveType}
    {D : VInductDecl'} :
    (∀ (j : Nat) t T, types[j]? = some t → D.types[j]? = some T → TrIndType env Us t T) ↔
    (∀ (j : Nat) t T, types[j]? = some t → D.types[j]? = some T →
      t.name = T.name ∧ ∃ Tt, TrExprS env Us [] t.type Tt ∧ T.type = Tt) := by
  refine ⟨fun H j t T ht hT => ?_, fun H j t T ht hT => ?_⟩
  · exact ⟨(H j t T ht hT).1, _, (H j t T ht hT).2, rfl⟩
  · obtain ⟨hn, Tt, htr, rfl⟩ := H j t T ht hT
    exact ⟨hn, htr⟩

theorem exists_indTypes_of_trExprS {env : VEnv} {Us : List Name} :
    ∀ {types : List InductiveType},
    (∀ (j : Nat) t, types[j]? = some t → ∃ Tt, TrExprS env Us [] t.type Tt) →
    ∃ Ts : List VIndType, Ts.length = types.length ∧
      ∀ (j : Nat) t T, types[j]? = some t → Ts[j]? = some T → TrIndType env Us t T
  | [], _ => ⟨[], rfl, by simp⟩
  | t :: rest, h => by
    obtain ⟨Tt, hTt⟩ := h 0 t rfl
    obtain ⟨Ts, hlen, hp⟩ := exists_indTypes_of_trExprS (types := rest)
      fun j t' ht' => h (j + 1) t' (by simpa using ht')
    refine ⟨⟨t.name, Tt, [], []⟩ :: Ts, by simp [hlen], ?_⟩
    rintro (_ | j) t' T ht' hT
    · cases ht'; cases hT; exact ⟨rfl, hTt⟩
    · exact hp j t' T (by simpa using ht') (by simpa using hT)

theorem exists_indTypes_append {env : VEnv} {Us : List Name} {types : List InductiveType}
    (h : ∀ (j : Nat) t, types[j]? = some t → ∃ Tt, TrExprS env Us [] t.type Tt)
    (aux : List VIndType) :
    ∃ Ts : List VIndType, Ts.length = types.length ∧
      ∀ (j : Nat) t T, types[j]? = some t → (Ts ++ aux)[j]? = some T → TrIndType env Us t T := by
  obtain ⟨Ts, hlen, hp⟩ := exists_indTypes_of_trExprS h
  refine ⟨Ts, hlen, fun j t T ht hT => hp j t T ht ?_⟩
  rwa [List.getElem?_append_left (by rw [hlen]; exact (List.getElem?_eq_some_iff.1 ht).1)] at hT

/-! ## §5 Vacuity: the arity-0 witness at the parameterised nested block -/

namespace InductiveDeclExamples

theorem ntreeIndType_sortPi :
    sortPiTr? [`u] ntreeIndType.type
      = some (.forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))) := by
  rfl

theorem ntreeAux_trType_uniform {env : VEnv} :
    ∀ (j : Nat) t T, [ntreeIndType][j]? = some t → ntreeAux.types[j]? = some T →
      TrIndType env [`u] t T := by
  refine trType_of_sortPiTr ?_
  rintro (_ | j) t T ht hT
  · cases ht; cases hT; exact ⟨rfl, ntreeIndType_sortPi⟩
  · simp at ht

theorem ntreeAux_trType_witness :
    ∃ env₁ : VEnv, VEnv.empty.addInduct' listDecl = some env₁ ∧
      ntreeAux.uvars = 1 ∧ ntreeAux.params = [.sort (.succ (.param 0))] ∧
      ntreeAux.types.length = 2 ∧
      (∀ (j : Nat) t T, [ntreeIndType][j]? = some t → ntreeAux.types[j]? = some T →
        TrIndType env₁ [`u] t T) ∧
      ((∀ (j : Nat) t T, [ntreeIndType][j]? = some t → ntreeAux.types[j]? = some T →
          TrIndType env₁ [`u] t T) ↔
        (∀ (j : Nat) t T, [ntreeIndType][j]? = some t → ntreeAux.types[j]? = some T →
          t.name = T.name ∧ sortPiTr? [`u] t.type = some T.type)) ∧
      -- the anti-vacuity conjunct: member `0` really is a matching pair, and the clause really
      -- does say something about it
      (∃ T, ntreeAux.types[0]? = some T ∧ T.name = ``NTree ∧
        TrIndType env₁ [`u] ntreeIndType T) := by
  obtain ⟨env₁, -, -, -, -, h, -⟩ := ntree_stage₂_exists
  refine ⟨env₁, h, rfl, rfl, rfl, ntreeAux_trType_uniform, trType_iff_of_sortPiTr ?_,
    _, rfl, rfl, ntreeAux_trType_uniform 0 _ _ rfl rfl⟩
  rintro (_ | j) t ht
  · cases ht; exact ⟨_, ntreeIndType_sortPi⟩
  · simp at ht

end InductiveDeclExamples

/-! ## §6 The boundary of §1–§3, machine-checked -/

/-- An arity mentioning a constant is outside the fragment: `sortPiTr?` returns `none`. -/
theorem sortPiTr?_none_of_const {Us : List Name} :
    sortPiTr? Us (.forallE `n (.const ``Nat []) (.sort (.succ .zero)) .default) = none := rfl

/-- …and at such a member the field is genuinely environment-dependent: with `Nat` undeclared,
**no** `T` satisfies `TrIndType`.  So §1's uniformity in `env` cannot be extended past the
fragment, and the general case really does need facts about the pre-block environment. -/
theorem no_trExprS_of_undeclared {env : VEnv} {Us : List Name} {Tt : VExpr}
    (hNat : env.constants ``Nat = none) :
    ¬ TrExprS env Us [] (.forallE `n (.const ``Nat []) (.sort (.succ .zero)) .default) Tt := by
  intro htr
  cases htr with
  | forallE _ _ hd _ =>
    cases hd with
    | const hc _ _ => rw [hNat] at hc; exact absurd hc nofun

theorem no_trIndType_of_undeclared {env : VEnv} {Us : List Name} {t : InductiveType}
    {T : VIndType} (hNat : env.constants ``Nat = none)
    (ht : t.type = .forallE `n (.const ``Nat []) (.sort (.succ .zero)) .default) :
    ¬ TrIndType env Us t T := fun ⟨_, htr⟩ => no_trExprS_of_undeclared hNat (ht ▸ htr)

/-! ## §7 The shapes coincide with the field, checked by elaboration

`TrIndDeclN.trType`'s type and the conclusion of §3's producer are the same statement.  This file
does not import `TrIndDeclNProducer` (see §5's rationale), so instead of applying its `hty`
binder these two `example`s check the fit against the structure field itself. -/

example {env : VEnv} {Us : List Name} {np nn : Nat} {types : List InductiveType} {iu : Bool}
    {D : VInductDecl'} {K : List Name} {R : VIndRestore}
    (h : TrIndDeclN env Us np types iu nn D K R) :
    ∀ (j : Nat) t T, types[j]? = some t → D.types[j]? = some T → TrIndType env Us t T := h.trType

example {env : VEnv} {Us : List Name} {np nn : Nat} {types : List InductiveType} {iu : Bool}
    {D : VInductDecl'} {K : List Name} {R : VIndRestore}
    (h : ∀ (j : Nat) t T, types[j]? = some t → D.types[j]? = some T →
      t.name = T.name ∧ sortPiTr? Us t.type = some T.type)
    (mk : (∀ (j : Nat) t T, types[j]? = some t → D.types[j]? = some T → TrIndType env Us t T) →
      TrIndDeclN env Us np types iu nn D K R) :
    TrIndDeclN env Us np types iu nn D K R := mk (trType_of_sortPiTr h)

end Lean4Lean
