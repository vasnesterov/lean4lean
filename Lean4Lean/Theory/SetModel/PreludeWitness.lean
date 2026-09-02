import Lean4Lean.Theory.SetModel.UpperBound

/-!
# `PreludeWF`: the missing witness, built

`SetModel/UpperBound.lean` §3 proves that the whole `←` half of the equiconsistency —
its three inputs **and** its conclusion `leanTTConsistent` — collapses to `True` if
`VEnv.LeanWF` is empty (`upper_bound_vacuous_of_no_leanWF`), and §4 pins the missing object
*exactly*: `exists_leanWF_iff : (∃ env, env.LeanWF) ↔ PreludeWF`, where

    PreludeWF : Prop := ∃ env : VEnv, VEnv.WF' leanPrelude.reverse env

is abstract well-formedness of the seven prelude steps and nothing more (the `ds` of `LeanWF`
cannot help: `exists_wf'_of_append`).  §6 discharged the first step, `eqIndDecl_WF`.

**This file discharges the other six and closes `PreludeWF`.**  Consequences, all proved
below and all `[propext, Quot.sound]`:

| theorem | content |
|---|---|
| `iffIndDecl_WF`, `nonemptyIndDecl_WF` | the two remaining `.induct` blocks, over an **arbitrary** environment, exactly as `eqIndDecl_WF` |
| `propextConst_WF`, `choiceConst_WF`, `quotSoundConst_WF` | the three standard axioms' types are types, over the *staged* environments |
| `preludeEnv_history` | `VEnv.WF' leanPrelude.reverse preludeEnv` |
| `preludeWF` | `PreludeWF` |
| `exists_leanWF`, `preludeEnv_leanWF` | `∃ env, env.LeanWF`, through `exists_leanWF_iff`, and the named witness |
| `not_forall_not_leanWF` | the hypothesis of `upper_bound_vacuous_of_no_leanWF` is **refuted** |

So `leanTTConsistent` and the three inputs `PropTypeAgreeInput` / `InstDescendInput` /
`OracleInput` are statements about a class with a member.  §5 exhibits that as
`propTypeAgree_of_input`, `instDescend_of_input` and `consistent_of_leanTTConsistent`:
each input, and the conclusion, now says something at the *named* environment `preludeEnv`.

## How the environments are handled

The seven environments are **computed**, not axiomatised: each is
`(previous.addX …).getD .empty` and each `…_add` lemma is `rfl`.  That is not a
tautology — had an `addConst`/`addInduct'` failed, `getD .empty` would have returned
`VEnv.empty` and the lemma would read `none = some VEnv.empty`, which `rfl` refuses.  So the
`rfl`s certify freshness of all sixteen declared names as a side effect, and every constant
lookup the axiom spines need (`iffEnv_Eq`, `quotEnv_Quot`, …) is likewise `rfl`.
§5 adds positive and negative controls on the final environment.

## Two corrections to what this step was costed at

* **The `.quot` step does not need the four quotient constants' types to be types.**
  `VDecl.WF.quot` asks for exactly `env.QuotReady` — i.e. `constants ``Eq = some eqConst`,
  one `rfl` — plus `addQuot = some env'`.  Well-formedness of `Quot`, `Quot.mk`,
  `Quot.lift`, `Quot.ind` is a **theorem** (`Typing/QuotLemmas.lean`'s `addQuot_WF`, which
  delivers `Ordered env'`), not an obligation of the step.  So this was the *cheapest* of the
  six, not a middle-cost one.
* **The three axiom types are not `Quot.lift`-sized.**  Each is one `constDF` plus at most
  three `appDF`s per constant head, with no rewriting, no transport and no `instL` bookkeeping
  beyond what `exact` computes: `quotSoundConst_WF`, the largest, is about 40 lines and
  mentions `Eq`, `Quot` and `Quot.mk`.  The `QuotInterp.lean` comparison was about the *model*
  interpretation of `Quot.lift`, which is a different obligation.

## What the three `.induct` blocks needed that `Eq` did not

`Eq.refl` has no constructor fields, so `eqIndDecl_WF` never met `VIndField.WF`.  `Iff.intro`
has two fields and `Nonempty.intro` one, and all four of its fields are one-liners once named:

* `hasType` — `forallEDF` types a pi at `.sort (.imax u v)`, and the recorded `F.lvl` is
  `.zero`, so a `defeqDF` through `sortDF … VLevel.imax_zero` is needed; `by decide` cannot
  see it because `VLevel.Equiv` is an equality of `eval` functions.
* `level` — `VLevel.imax F.lvl D.lvl ≤ D.lvl` at `D.lvl = .zero` is
  `(VLevel.le_antisymm_iff.1 VLevel.imax_zero).1`.  Not `decide`-able: `VLevel.LE` is a `∀ ls`.
* `pos` — the `none` branch is `∃ A, D.NoBlock A ∧ IsDefEqType Γ F.type A`; take `A := F.type`
  **explicitly** (a metavariable there blocks `NoConsts`' anonymous constructor, since
  `NoConsts` is a `def` by pattern match, not a structure) and supply `u := .zero` explicitly
  for the same reason.
* `binders_indep` — `nofun`; both blocks' fields are non-recursive, so
  `VIndRecArg.exists_indep` (which carries a `sorry`) is **not** on this file's cone.
-/

namespace Lean4Lean.SetModel

/-! ## 1. The two remaining `.induct` steps, over an arbitrary environment -/

set_option maxHeartbeats 1000000 in
/-- **`Iff` is a well-formed inductive block**, over an arbitrary environment: nothing in the
block's data mentions a constant other than its own type former, which `ctors` reads out of
the staged environment `env₁`.  Same generality as `eqIndDecl_WF`, and the same proof shape
apart from `VIndField.WF`, which `Eq.refl`'s empty field list let `eqIndDecl_WF` skip. -/
theorem iffIndDecl_WF (env : VEnv) : VInductDecl'.WF env iffIndDecl := by
  constructor
  case types_ne => nofun
  case params =>
    show OnCtx [VExpr.sort .zero, VExpr.sort .zero] _
    exact ⟨⟨trivial, ⟨_, .sortDF trivial trivial (.refl _)⟩⟩,
      ⟨_, .sortDF trivial trivial (.refl _)⟩⟩
  case isLE =>
    intro _
    refine Or.inr ⟨_, rfl, Or.inr ⟨_, rfl, ?_⟩⟩
    intro i F hF
    exact Or.inl (by
      match i, hF with
      | 0, hF => simp only [List.getElem?_cons_zero, Option.some.injEq] at hF
                 subst hF; exact .refl _
      | 1, hF => simp only [List.getElem?_cons_succ, List.getElem?_cons_zero,
            Option.some.injEq] at hF; subst hF; exact .refl _
      | (n+2), hF => nomatch hF)
  case types =>
    intro T hT
    simp only [iffIndDecl, List.mem_cons, List.not_mem_nil, or_false] at hT
    subst hT
    have hty : VEnv.IsType env 0 [] (VExpr.forallE (.sort .zero)
        (.forallE (.sort .zero) (.sort .zero))) := by
      refine .forallE ⟨_, .sortDF trivial trivial (.refl _)⟩ ?_
      refine .forallE ⟨_, .sortDF trivial trivial (.refl _)⟩ ?_
      exact ⟨_, .sortDF trivial trivial (.refl _)⟩
    refine { indices := ?_, isType := hty, canon := hty }
    show OnCtx [VExpr.sort .zero, VExpr.sort .zero] _
    exact ⟨⟨trivial, ⟨_, .sortDF trivial trivial (.refl _)⟩⟩,
      ⟨_, .sortDF trivial trivial (.refl _)⟩⟩
  case ctors =>
    intro env₁ he j T hT C hC
    match j, hT with
    | 0, hT =>
      simp only [iffIndDecl, List.getElem?_cons_zero, Option.some.injEq] at hT
      subst hT
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
      subst hC
      have hIff : env₁.constants ``Iff = some ⟨0, VExpr.forallE (.sort .zero)
          (.forallE (.sort .zero) (.sort .zero))⟩ :=
        VEnv.addConstList_constants (cs := iffIndDecl.typeConsts) he
          (``Iff, ⟨0, _⟩) (by simp [iffIndDecl, VInductDecl'.typeConsts])
      refine { params_len := rfl, params_eq := ?_, fields := ?_, args_len := rfl,
               args_fresh := nofun, args_ty := .nil, result := ?_ }
      · exact .succ (.succ .zero (.sortDF trivial trivial (.refl _)))
          (.sortDF trivial trivial (.refl _))
      · intro i F hF
        match i, hF with
        | 0, hF =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hF; subst hF
          refine { hasType := ?_, level := ?_,
                   pos := ⟨VExpr.forallE (.bvar 1) (.bvar 1), ⟨trivial, trivial⟩, ⟨VLevel.zero, ?_⟩⟩,
                   binders_indep := nofun }
          · exact .defeqDF (.sortDF (by decide) trivial VLevel.imax_zero)
              (.forallEDF (.bvar (.succ .zero)) (.bvar (.succ .zero)))
          · exact (VLevel.le_antisymm_iff.1 VLevel.imax_zero).1
          · exact .defeqDF (.sortDF (by decide) trivial VLevel.imax_zero)
              (.forallEDF (.bvar (.succ .zero)) (.bvar (.succ .zero)))
        | 1, hF =>
          simp only [List.getElem?_cons_succ, List.getElem?_cons_zero,
            Option.some.injEq] at hF; subst hF
          refine { hasType := ?_, level := ?_,
                   pos := ⟨VExpr.forallE (.bvar 1) (.bvar 3), ⟨trivial, trivial⟩, ⟨VLevel.zero, ?_⟩⟩,
                   binders_indep := nofun }
          · exact .defeqDF (.sortDF (by decide) trivial VLevel.imax_zero)
              (.forallEDF (.bvar (.succ .zero)) (.bvar (.succ (.succ (.succ .zero)))))
          · exact (VLevel.le_antisymm_iff.1 VLevel.imax_zero).1
          · exact .defeqDF (.sortDF (by decide) trivial VLevel.imax_zero)
              (.forallEDF (.bvar (.succ .zero)) (.bvar (.succ (.succ (.succ .zero)))))
        | (n+2), hF => nomatch hF
      · have hE : VEnv.HasType env₁ 0
            [VExpr.forallE (.bvar 1) (.bvar 3), VExpr.forallE (.bvar 1) (.bvar 1),
             VExpr.sort .zero, VExpr.sort .zero]
            (.const ``Iff []) (VExpr.forallE (.sort .zero)
              (.forallE (.sort .zero) (.sort .zero))) :=
          .constDF hIff nofun nofun rfl .nil
        exact (hE.appDF (.bvar (.succ (.succ (.succ .zero))))).appDF
          (.bvar (.succ (.succ .zero)))

set_option maxHeartbeats 1000000 in
/-- **`Nonempty` is a well-formed inductive block**, over an arbitrary environment.  Unlike
`Eq` and `Iff` this is a small eliminator (`isLE := false`), so `LECond` is not even asked
for; its one field has `lvl := .param 0`, which is where `level`'s `VLevel.imax_zero` earns
its keep — `imax (param 0) zero ≤ zero` is true but not decidable as stated. -/
theorem nonemptyIndDecl_WF (env : VEnv) : VInductDecl'.WF env nonemptyIndDecl := by
  constructor
  case types_ne => nofun
  case params =>
    show OnCtx [VExpr.sort (.param 0)] _
    exact ⟨trivial, ⟨_, .sortDF (by decide) (by decide) (.refl _)⟩⟩
  case isLE => nofun
  case types =>
    intro T hT
    simp only [nonemptyIndDecl, List.mem_cons, List.not_mem_nil, or_false] at hT
    subst hT
    have hty : VEnv.IsType env 1 [] (VExpr.forallE (.sort (.param 0)) (.sort .zero)) := by
      refine .forallE ⟨_, .sortDF (by decide) (by decide) (.refl _)⟩ ?_
      exact ⟨_, .sortDF trivial trivial (.refl _)⟩
    refine { indices := ?_, isType := hty, canon := hty }
    show OnCtx [VExpr.sort (.param 0)] _
    exact ⟨trivial, ⟨_, .sortDF (by decide) (by decide) (.refl _)⟩⟩
  case ctors =>
    intro env₁ he j T hT C hC
    match j, hT with
    | 0, hT =>
      simp only [nonemptyIndDecl, List.getElem?_cons_zero, Option.some.injEq] at hT
      subst hT
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
      subst hC
      have hN : env₁.constants ``Nonempty = some ⟨1,
          VExpr.forallE (.sort (.param 0)) (.sort .zero)⟩ :=
        VEnv.addConstList_constants (cs := nonemptyIndDecl.typeConsts) he
          (``Nonempty, ⟨1, _⟩) (by simp [nonemptyIndDecl, VInductDecl'.typeConsts])
      refine { params_len := rfl, params_eq := ?_, fields := ?_, args_len := rfl,
               args_fresh := nofun, args_ty := .nil, result := ?_ }
      · exact .succ .zero (.sortDF (by decide) (by decide) (.refl _))
      · intro i F hF
        match i, hF with
        | 0, hF =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hF
          subst hF
          exact { hasType := .bvar .zero,
                  level := (VLevel.le_antisymm_iff.1 VLevel.imax_zero).1,
                  pos := ⟨VExpr.bvar 0, trivial, ⟨VLevel.param 0, .bvar .zero⟩⟩,
                  binders_indep := nofun }
        | (n+1), hF => nomatch hF
      · have hE : VEnv.HasType env₁ 1 [VExpr.bvar 0, VExpr.sort (.param 0)]
            (.const ``Nonempty [.param 0])
            (VExpr.forallE (.sort (.param 0)) (.sort .zero)) :=
          .constDF hN (by decide) (by decide) rfl (.cons (by rfl) .nil)
        exact hE.appDF (.bvar (.succ .zero))

/-! ## 2. The seven environments, computed -/

section Envs

/-- After `.induct eqIndDecl` over `VEnv.empty`. -/
def eqEnv : VEnv := (VEnv.empty.addInduct' eqIndDecl).getD .empty
theorem eqEnv_add : VEnv.empty.addInduct' eqIndDecl = some eqEnv := rfl

/-- After `.induct iffIndDecl`. -/
def iffEnv : VEnv := (eqEnv.addInduct' iffIndDecl).getD .empty
theorem iffEnv_add : eqEnv.addInduct' iffIndDecl = some iffEnv := rfl

/-- After `.axiom propextConst`. -/
def propextEnv : VEnv := (iffEnv.addConst ``propext propextConst.toVConstant).getD .empty
theorem propextEnv_add :
    iffEnv.addConst propextConst.name propextConst.toVConstant = some propextEnv := rfl

/-- After `.induct nonemptyIndDecl`. -/
def nonemptyEnv : VEnv := (propextEnv.addInduct' nonemptyIndDecl).getD .empty
theorem nonemptyEnv_add : propextEnv.addInduct' nonemptyIndDecl = some nonemptyEnv := rfl

/-- After `.axiom choiceConst`. -/
def choiceEnv : VEnv :=
  (nonemptyEnv.addConst ``Classical.choice choiceConst.toVConstant).getD .empty
theorem choiceEnv_add :
    nonemptyEnv.addConst choiceConst.name choiceConst.toVConstant = some choiceEnv := rfl

/-- After `.quot`. -/
def quotEnv : VEnv := choiceEnv.addQuot.getD .empty
theorem quotEnv_add : choiceEnv.addQuot = some quotEnv := rfl

/-- After `.axiom quotSoundConst` — the full prelude. -/
def preludeEnv : VEnv := (quotEnv.addConst ``Quot.sound quotSoundConst.toVConstant).getD .empty
theorem preludeEnv_add :
    quotEnv.addConst quotSoundConst.name quotSoundConst.toVConstant = some preludeEnv := rfl

/-! ### The lookups the three axiom types need -/

theorem iffEnv_Iff : iffEnv.constants ``Iff =
    some ⟨0, .forallE (.sort .zero) (.forallE (.sort .zero) (.sort .zero))⟩ := rfl

theorem iffEnv_Eq : iffEnv.constants ``Eq =
    some ⟨1, .forallE (.sort (.param 0)) (.forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)))⟩ :=
  rfl

theorem nonemptyEnv_Nonempty : nonemptyEnv.constants ``Nonempty =
    some ⟨1, .forallE (.sort (.param 0)) (.sort .zero)⟩ := rfl

theorem choiceEnv_quotReady : choiceEnv.QuotReady := rfl

theorem quotEnv_Eq : quotEnv.constants ``Eq =
    some ⟨1, .forallE (.sort (.param 0)) (.forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)))⟩ :=
  rfl

theorem quotEnv_Quot : quotEnv.constants ``Quot = some quotConst := rfl
theorem quotEnv_QuotMk : quotEnv.constants ``Quot.mk = some quotMkConst := rfl

end Envs

/-! ## 3. The three axiom types are types -/

section AxiomTypes

/-- `propext : ∀ (a b : Prop), (a ↔ b) → @Eq.{1} Prop a b` is a type over the environment
that has just declared `Iff`. -/
theorem propextConst_WF : propextConst.toVConstant.WF iffEnv := by
  show VEnv.IsType iffEnv 0 [] _
  refine .forallE ⟨_, .sortDF trivial trivial (.refl _)⟩ ?_
  refine .forallE ⟨_, .sortDF trivial trivial (.refl _)⟩ ?_
  refine .forallE ?_ ?_
  · have hI : VEnv.HasType iffEnv 0 [VExpr.sort .zero, VExpr.sort .zero] (.const ``Iff [])
        (.forallE (.sort .zero) (.forallE (.sort .zero) (.sort .zero))) :=
      .constDF iffEnv_Iff nofun nofun rfl .nil
    exact ⟨_, (hI.appDF (.bvar (.succ .zero))).appDF (.bvar .zero)⟩
  · have hE : VEnv.HasType iffEnv 0
        [VExpr.app (.app (.const ``Iff []) (.bvar 1)) (.bvar 0),
         VExpr.sort .zero, VExpr.sort .zero] (.const ``Eq [.succ .zero])
        (.forallE (.sort (.succ .zero))
          (.forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)))) :=
      .constDF iffEnv_Eq (by decide) (by decide) rfl (.cons (by rfl) .nil)
    exact ⟨_, ((hE.appDF (.sortDF (l := .zero) (l' := .zero) trivial trivial (.refl _))).appDF
      (.bvar (.succ (.succ .zero)))).appDF (.bvar (.succ .zero))⟩

/-- `Classical.choice : ∀ {α : Sort u}, Nonempty α → α`. -/
theorem choiceConst_WF : choiceConst.toVConstant.WF nonemptyEnv := by
  show VEnv.IsType nonemptyEnv 1 [] _
  refine .forallE ⟨_, .sortDF (by decide) (by decide) (.refl _)⟩ ?_
  refine .forallE ?_ ⟨_, .bvar (.succ .zero)⟩
  have hN : VEnv.HasType nonemptyEnv 1 [VExpr.sort (.param 0)]
      (.const ``Nonempty [.param 0]) (.forallE (.sort (.param 0)) (.sort .zero)) :=
    .constDF nonemptyEnv_Nonempty (by decide) (by decide) rfl (.cons (by rfl) .nil)
  exact ⟨_, hN.appDF (.bvar .zero)⟩

/-- `Quot.sound : ∀ {α : Sort u} {r : α → α → Prop} {a b : α},
r a b → @Eq.{u} (Quot α r) (Quot.mk r a) (Quot.mk r b)`. -/
theorem quotSoundConst_WF : quotSoundConst.toVConstant.WF quotEnv := by
  show VEnv.IsType quotEnv 1 [] _
  refine .forallE ⟨_, .sortDF (by decide) (by decide) (.refl _)⟩ ?_
  refine .forallE ?_ ?_
  · refine .forallE ⟨.param 0, .bvar .zero⟩ ?_
    refine .forallE ⟨.param 0, .bvar (.succ .zero)⟩ ?_
    exact ⟨_, .sortDF (l := .zero) (l' := .zero) trivial trivial (.refl _)⟩
  refine .forallE ⟨.param 0, .bvar (.succ .zero)⟩ ?_
  refine .forallE ⟨.param 0, .bvar (.succ (.succ .zero))⟩ ?_
  refine .forallE ?_ ?_
  · have hr : VEnv.HasType quotEnv 1
        [VExpr.bvar 2, VExpr.bvar 1,
         VExpr.forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)), VExpr.sort (.param 0)]
        (.bvar 2) (.forallE (.bvar 3) (.forallE (.bvar 4) (.sort .zero))) :=
      .bvar (.succ (.succ .zero))
    exact ⟨_, (hr.appDF (.bvar (.succ .zero))).appDF (.bvar .zero)⟩
  · have hQ : VEnv.HasType quotEnv 1
        [VExpr.app (.app (.bvar 2) (.bvar 1)) (.bvar 0), VExpr.bvar 2, VExpr.bvar 1,
         VExpr.forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)), VExpr.sort (.param 0)]
        (.const ``Quot [.param 0])
        (.forallE (.sort (.param 0))
          (.forallE (.forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)))
            (.sort (.param 0)))) :=
      .constDF quotEnv_Quot (by decide) (by decide) rfl (.cons (by rfl) .nil)
    have hM : VEnv.HasType quotEnv 1
        [VExpr.app (.app (.bvar 2) (.bvar 1)) (.bvar 0), VExpr.bvar 2, VExpr.bvar 1,
         VExpr.forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)), VExpr.sort (.param 0)]
        (.const ``Quot.mk [.param 0])
        (.forallE (.sort (.param 0))
          (.forallE (.forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)))
            (.forallE (.bvar 1)
              (.app (.app (.const ``Quot [.param 0]) (.bvar 2)) (.bvar 1))))) :=
      .constDF quotEnv_QuotMk (by decide) (by decide) rfl (.cons (by rfl) .nil)
    have hE : VEnv.HasType quotEnv 1
        [VExpr.app (.app (.bvar 2) (.bvar 1)) (.bvar 0), VExpr.bvar 2, VExpr.bvar 1,
         VExpr.forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)), VExpr.sort (.param 0)]
        (.const ``Eq [.param 0])
        (.forallE (.sort (.param 0))
          (.forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)))) :=
      .constDF quotEnv_Eq (by decide) (by decide) rfl (.cons (by rfl) .nil)
    have hQAR := (hQ.appDF (.bvar (.succ (.succ (.succ (.succ .zero)))))).appDF
      (.bvar (.succ (.succ (.succ .zero))))
    have hMA := ((hM.appDF (.bvar (.succ (.succ (.succ (.succ .zero)))))).appDF
      (.bvar (.succ (.succ (.succ .zero))))).appDF (.bvar (.succ (.succ .zero)))
    have hMB := ((hM.appDF (.bvar (.succ (.succ (.succ (.succ .zero)))))).appDF
      (.bvar (.succ (.succ (.succ .zero))))).appDF (.bvar (.succ .zero))
    exact ⟨_, ((hE.appDF hQAR).appDF hMA).appDF hMB⟩

end AxiomTypes

/-! ## 4. `PreludeWF`, and the `LeanWF` witness it delivers -/

/-- **The seven-step prelude history.** -/
theorem preludeEnv_history : VEnv.WF' leanPrelude.reverse preludeEnv :=
  .decl (.axiom quotSoundConst_WF preludeEnv_add)
    (.decl (.quot choiceEnv_quotReady quotEnv_add)
      (.decl (.axiom choiceConst_WF choiceEnv_add)
        (.decl (.induct (nonemptyIndDecl_WF _) nonemptyEnv_add)
          (.decl (.axiom propextConst_WF propextEnv_add)
            (.decl (.induct (iffIndDecl_WF _) iffEnv_add)
              (.decl (.induct (eqIndDecl_WF _) eqEnv_add) .empty))))))

/-- **`PreludeWF`.** -/
theorem preludeWF : PreludeWF := ⟨preludeEnv, preludeEnv_history⟩

/-- **The witness `exists_leanWF_iff` consumes.** -/
theorem exists_leanWF : ∃ env : VEnv, env.LeanWF := exists_leanWF_iff.2 preludeWF

/-- **…and it is `preludeEnv` itself.** -/
theorem preludeEnv_leanWF : preludeEnv.LeanWF := ⟨[], by simpa using preludeEnv_history, nofun⟩

/-! ## 5. Controls: the witness is a real environment, and the corner is no longer vacuous -/

section Controls

/-- The prelude environment really carries the three axioms and the four quotient
primitives — a positive control against the `getD .empty` fallback having fired (it cannot
have: `eqEnv_add`'s `rfl` would then have been `none = some .empty`). -/
theorem preludeEnv_propext :
    preludeEnv.constants ``propext = some propextConst.toVConstant := rfl
theorem preludeEnv_choice :
    preludeEnv.constants ``Classical.choice = some choiceConst.toVConstant := rfl
theorem preludeEnv_quotSound :
    preludeEnv.constants ``Quot.sound = some quotSoundConst.toVConstant := rfl
theorem preludeEnv_quotLift : preludeEnv.constants ``Quot.lift = some quotLiftConst := rfl
theorem preludeEnv_eqRec :
    preludeEnv.constants ``Eq.rec = some ⟨eqIndDecl.recUvars, eqIndDecl.recType 0⟩ := rfl

/-- …and nothing else: a negative control. -/
theorem preludeEnv_no_Nat : preludeEnv.constants ``Nat = none := rfl

theorem preludeEnv_WF : preludeEnv.WF := ⟨_, preludeEnv_history⟩

theorem preludeEnv_ordered : preludeEnv.Ordered := VEnv.WF.ordered preludeEnv_WF

/-- **The hypothesis of `upper_bound_vacuous_of_no_leanWF` is refuted.**  So the collapse
recorded in `UpperBound.lean` §3 cannot be used to discharge the three inputs, and every
statement quantified over `VEnv.LeanWF` — `leanTTConsistent` included — is now about a
class with a member. -/
theorem not_forall_not_leanWF : ¬ ∀ env : VEnv, ¬ env.LeanWF :=
  fun h ↦ h preludeEnv preludeEnv_leanWF

/-- Each of the three inputs now has content at a named environment. -/
theorem propTypeAgree_of_input (h : PropTypeAgreeInput) : preludeEnv.PropTypeAgree 0 :=
  h _ preludeEnv_leanWF

theorem instDescend_of_input (h : InstDescendInput) : preludeEnv.InstDescendUp 0 :=
  h _ preludeEnv_leanWF

/-- …and so does the conclusion. -/
theorem consistent_of_leanTTConsistent (h : leanTTConsistent) : preludeEnv.Consistent :=
  h _ preludeEnv_leanWF

open LO LO.FirstOrder LO.FirstOrder.SetTheory in
/-- **The `←` half, now delivering something.**  `upper_bound_of_inputs` composed with the
witness: from the three inputs and consistency of `ZFC + n inaccessibles`, the *named*
environment `preludeEnv` — the one carrying `Eq`, `Iff`, `Nonempty`, the quotient primitives
and the three standard axioms — proves no inhabitant of `∀ p : Prop, p`.  Before
`preludeWF` this composition had no instance to point at. -/
theorem preludeEnv_consistent_of_inputs (hTI : PropTypeAgreeInput) (hII : InstDescendInput)
    (hO : OracleInput) (hc : Entailment.Consistent (𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰 : SetTheory)) :
    preludeEnv.Consistent :=
  consistent_of_leanTTConsistent (upper_bound_of_inputs hTI hII hO hc)

end Controls

end Lean4Lean.SetModel

/-! ## Axiom census -/

#print axioms Lean4Lean.SetModel.iffIndDecl_WF
#print axioms Lean4Lean.SetModel.nonemptyIndDecl_WF
#print axioms Lean4Lean.SetModel.eqEnv_add
#print axioms Lean4Lean.SetModel.iffEnv_add
#print axioms Lean4Lean.SetModel.propextEnv_add
#print axioms Lean4Lean.SetModel.nonemptyEnv_add
#print axioms Lean4Lean.SetModel.choiceEnv_add
#print axioms Lean4Lean.SetModel.quotEnv_add
#print axioms Lean4Lean.SetModel.preludeEnv_add
#print axioms Lean4Lean.SetModel.choiceEnv_quotReady
#print axioms Lean4Lean.SetModel.propextConst_WF
#print axioms Lean4Lean.SetModel.choiceConst_WF
#print axioms Lean4Lean.SetModel.quotSoundConst_WF
#print axioms Lean4Lean.SetModel.preludeEnv_history
#print axioms Lean4Lean.SetModel.preludeWF
#print axioms Lean4Lean.SetModel.exists_leanWF
#print axioms Lean4Lean.SetModel.preludeEnv_leanWF
#print axioms Lean4Lean.SetModel.not_forall_not_leanWF
#print axioms Lean4Lean.SetModel.preludeEnv_ordered
#print axioms Lean4Lean.SetModel.consistent_of_leanTTConsistent
#print axioms Lean4Lean.SetModel.preludeEnv_consistent_of_inputs
