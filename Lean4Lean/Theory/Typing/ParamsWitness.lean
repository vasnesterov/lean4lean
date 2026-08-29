import Lean4Lean.Theory.Typing.ChurchRosser
import Lean4Lean.Theory.Typing.CycleConv
import Lean4Lean.Theory.Typing.ParamsBuild

/-!
# `VEnv.Params` is inhabited -- a concrete witness

`Theory/Typing/ChurchRosser.lean` and `Theory/Typing/HeadReduction.lean` develop parallel
reduction, `NormalEq` and Church--Rosser entirely under `variable [Params]`, and `Params`
carries `env`/`henv` as *fields*.  Until this file nothing in the package produced a term of
that type -- 545 declarations were statements about a structure with no exhibited inhabitant.

This file builds one **by hand**, over `CycleConv.propLoopEnv`: a `VEnv.WF` environment
(`propLoopEnv_wf`) with two constants `A B : Prop` and two δ-rules `A ⟶ B`, `B ⟶ A`.  The
witness is deliberately *not* `VEnv.empty`: it has constants, it has defeq rules, and its
rules are not well-founded as a *head*-reduction (`propLoop_headStep_not_wf`), so `extra_pat`
is discharged at a rule that really fires rather than vacuously.

The hand-built instance imports nothing but `ChurchRosser.lean` and `CycleConv.lean`, so it
is an independent check on `Theory/Typing/ParamsBuild.lean`, which builds `Params` from
`VEnv.WF` generically (modulo `PatWF`) via the 2100-line `Theory/Typing/PatternRules.lean`.
The last section derives the same environment's instance that way instead, so the two routes
are exercised side by side.

**Correction to an earlier reading.**  `extra_pat` was singled out as "the field `VEnv.WF`
does not supply".  It is not: `PatternRules.lean`'s `Pat.extra` proves it for an arbitrary
`VEnv.WF` environment, and `VInductDecl'.iotaRule`'s η-expanded right-hand side was chosen
precisely so that it holds on the nose.  The one field that is genuinely open is `pat_wf`.
See `docs/handoff-params.md`.
-/
namespace Lean4Lean
namespace VEnv

open VExpr

namespace PropLoopParams

/-- The pattern table for `propLoopEnv`: exactly its two δ-rules, each registered as the
`SimplePattern.defn` of its head constant, with a closed `fixed` right-hand side and no
side conditions. -/
def Pat : (p : Pattern) → p.RHS × p.Check → Prop
  | .const c, r =>
    (c = `A ∧ r = (⟨.fixed (.const `B []) () trivial, .true⟩ :
      (Pattern.const c).RHS × (Pattern.const c).Check)) ∨
    (c = `B ∧ r = (⟨.fixed (.const `A []) () trivial, .true⟩ :
      (Pattern.const c).RHS × (Pattern.const c).Check))
  | .app .., _ => False
  | .var .., _ => False

theorem Pat.const {p r} (h : Pat p r) : ∃ c, p = .const c := by
  cases p with
  | const c => exact ⟨c, rfl⟩
  | app => exact h.elim
  | var => exact h.elim

/-- A constant pattern has no proper subpatterns. -/
theorem sub_const {q c} (h : Subpattern q (.const c)) : q = .const c := by cases h; rfl

theorem pat_simple {p r} (h : Pat p r) : ∃ sp : SimplePattern, p = sp.toPattern := by
  obtain ⟨c, rfl⟩ := Pat.const h; exact ⟨.defn c, rfl⟩

theorem pat_uniq {p₁ p₂ p₃ p₄ r r'} (h1 : Pat p₁ r) (h2 : Pat p₂ r')
    (h3 : Subpattern p₃ p₁) (h4 : p₂.inter p₃ = some p₄) :
    p₁ = p₂ ∧ p₂ = p₃ ∧ r ≍ r' := by
  obtain ⟨c₁, rfl⟩ := Pat.const h1
  obtain ⟨c₂, rfl⟩ := Pat.const h2
  cases sub_const h3
  rw [Pattern.inter] at h4
  split at h4
  · next hc =>
    cases hc
    refine ⟨rfl, rfl, heq_of_eq ?_⟩
    rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases h2 with ⟨hc, rfl⟩ | ⟨hc, rfl⟩ <;>
      first
        | rfl
        | exact absurd hc (by decide)
  · simp at h4

/-- Vacuous: `Pat` only ever registers `.const` patterns, which have no `.app` subpattern. -/
theorem pat_app_l_uniq {p p' p₁ p₂ p₁' p₂' p₃ r r'} (h1 : Pat p r) (_h2 : Pat p' r')
    (h3 : Subpattern (.app p₁ p₂) p) (_h4 : Subpattern (.app p₁' p₂') p')
    (_h5 : Subpattern (.var p₃) p₁) : p₁'.inter p₃ = none := by
  obtain ⟨c, rfl⟩ := Pat.const h1
  exact Pattern.noConfusion (sub_const h3)

/-- Vacuous, for the same reason as `pat_app_l_uniq`. -/
theorem pat_app_uniq {p p' p₁ p₂ p₁' p₂' p₃ p₃' r r'} (h1 : Pat p r) (_h2 : Pat p' r')
    (h3 : Subpattern (.app p₁ p₂) p) (_h4 : Subpattern (.app p₁' p₂') p')
    (_h5 : Subpattern p₃ p₁) (_h6 : Subpattern p₃' p₂') : p₃.inter p₃' = none := by
  obtain ⟨c, rfl⟩ := Pat.const h1
  exact Pattern.noConfusion (sub_const h3)

theorem pat_wf {p r e m1 m2 Γ A} (h1 : Pat p r) (h2 : p.Matches e m1 m2)
    (hΓ : OnCtx Γ (propLoopEnv.IsType 0))
    (hT : propLoopEnv.HasType 0 Γ e A)
    (_hck : r.2.OK (propLoopEnv.IsDefEqU 0 Γ) m1 m2) :
    propLoopEnv.IsDefEqU 0 Γ e (r.1.apply m1 m2) := by

  obtain ⟨c, rfl⟩ := Pat.const h1
  cases h2
  rename_i ls
  obtain ⟨ci, hci, -, hlen⟩ := HasType.const_inv propLoopEnv_wf.ordered hΓ hT
  rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [propLoopEnv_A] at hci
    cases hci
    obtain rfl : ls = [] := by simpa [VDefVal.toDefEq, propLoopA, propLoopB] using hlen
    exact ⟨_, .extra propLoopEnv_defeqs_A nofun rfl⟩
  · rw [propLoopEnv_B] at hci
    cases hci
    obtain rfl : ls = [] := by simpa [VDefVal.toDefEq, propLoopA, propLoopB] using hlen
    exact ⟨_, .extra propLoopEnv_defeqs_B nofun rfl⟩

theorem extra_pat {Γ df ls uvars} (_hΓ : OnCtx Γ (propLoopEnv.IsType 0))
    (hdf : propLoopEnv.defeqs df) (_hls : ∀ l ∈ ls, l.WF uvars) (hlen : ls.length = df.uvars) :
    ∃ Δ L R p r m1 m2,
      df.lhs.instL ls = VExpr.mkLams Δ L ∧ df.rhs.instL ls = VExpr.mkLams Δ R ∧
      Pat p r ∧ p.Matches L m1 m2 ∧
      r.2.OK (propLoopEnv.IsDefEqU 0 (Δ.reverse ++ Γ)) m1 m2 ∧ R = r.1.apply m1 m2 := by
  rcases hdf with rfl | rfl | hdf
  · obtain rfl : ls = [] := by simpa [VDefVal.toDefEq, propLoopA, propLoopB] using hlen
    exact ⟨[], _, _, .const `B, _, _, _, rfl, rfl, .inr ⟨rfl, rfl⟩, .const, trivial, rfl⟩
  · obtain rfl : ls = [] := by simpa [VDefVal.toDefEq, propLoopA, propLoopB] using hlen
    exact ⟨[], _, _, .const `A, _, _, _, rfl, rfl, .inl ⟨rfl, rfl⟩, .const, trivial, rfl⟩
  · exact hdf.elim

end PropLoopParams

/-- **`Params` is inhabited.**  Not registered as an `instance`: the consumers in
`ChurchRosser.lean` are stated for an arbitrary `[Params]`, and a global instance would let
them be silently specialised to this witness.  Use `letI := propLoopParams`. -/
@[instance_reducible] def propLoopParams : Params where
  env := propLoopEnv
  henv := propLoopEnv_wf
  univs := 0
  Pat := PropLoopParams.Pat
  pat_simple := PropLoopParams.pat_simple
  pat_uniq := PropLoopParams.pat_uniq
  pat_wf := PropLoopParams.pat_wf
  pat_app_l_uniq := PropLoopParams.pat_app_l_uniq
  pat_app_uniq := PropLoopParams.pat_app_uniq
  extra_pat := PropLoopParams.extra_pat


section Fires

attribute [local instance] propLoopParams

/-! ## Firing the development at the witness -/

/-- Sanity: the instance's environment and universe count are the intended ones. -/
theorem propLoopParams_env : @Params.env propLoopParams = propLoopEnv := rfl
theorem propLoopParams_univs : @Params.univs propLoopParams = 0 := rfl

/-- The δ-rule `A ⟶ B` is a **`ParRed.extra` step** at the witness: the `Pat` table is not
decorative, the reduction relation of `ChurchRosser.lean` really moves at this environment. -/
theorem propLoopEnv_parRed_fires :
    ParRed [] (.const `A []) (.const `B []) :=
  .extra (p := .const `A) (r := ⟨.fixed (.const `B []) () trivial, .true⟩) (m2' := nofun)
    (.inl ⟨rfl, rfl⟩) .const trivial nofun

theorem propLoopEnv_parRed_fires' :
    ParRed [] (.const `B []) (.const `A []) :=
  .extra (p := .const `B) (r := ⟨.fixed (.const `A []) () trivial, .true⟩) (m2' := nofun)
    (.inr ⟨rfl, rfl⟩) .const trivial nofun

/-- `CRDefEq` holds at the δ-loop, and its left leg is a **real reduction step**, not
reflexivity: `A` and `B` are joined at `B`, reached from `A` by `propLoopEnv_parRed_fires`.
Proved by hand, so this statement is `sorry`-free -- unlike `IsDefEq.church_rosser`, which
would also produce it (see `propLoopEnv_church_rosser_fires`). -/
theorem propLoopEnv_crDefEq_fires :
    CRDefEq [] (.const `A []) (.const `B []) :=
  ⟨⟨_, hasType_constProp propLoopEnv_A⟩, ⟨_, hasType_constProp propLoopEnv_B⟩,
    _, _, .tail .rfl propLoopEnv_parRed_fires, .rfl,
    .refl (hasType_constProp propLoopEnv_B)⟩

/-- The `Params`-gated Church--Rosser theorem itself, applied at the witness.

**This one is not `sorry`-free**: `IsDefEq.church_rosser` carries `sorryAx` from
`NormalEq.descend` (`ChurchRosser.lean:1696`) and `IsDefEqU.forallE_inv_stratified`. It is
recorded to show that the *application* goes through -- the instance discharges every
`Params` obligation the theorem asks for -- not as a proved result. -/
theorem propLoopEnv_church_rosser_fires :
    CRDefEq [] (.const `A []) (.const `B []) :=
  IsDefEq.church_rosser (Γ := []) trivial (.extra (ls := []) propLoopEnv_defeqs_A nofun rfl)

/-! ## The same instance, from the general construction

`Theory/Typing/ParamsBuild.lean` builds `Params` from `VEnv.WF` plus `PatWF`, and proves
`PatWF` outright on the δ fragment.  `propLoopEnv` is in that fragment, so it also gets an
instance *without* the bespoke `Pat` table above.  Two independently built instances over the
same environment; the hand-built one above depends on nothing but `ChurchRosser.lean`, this
one exercises all 2100 lines of `Theory/Typing/PatternRules.lean`. -/

/-- Every rule of `propLoopEnv` is a δ-rule, so its `VDefEq.key` is a singleton -- while the
quotient rule's and every ι-rule's key has two entries. -/
theorem propLoopEnv_key_length {df : VDefEq} (h : propLoopEnv.defeqs df) : df.key.length = 1 := by
  have key1 : ∀ v : VDefVal, v.toDefEq.key = [v.name] := fun _ =>
    key_of_isDeltaRule IsDeltaRule.const
  rcases h with rfl | rfl | h
  · rw [key1]; rfl
  · rw [key1]; rfl
  · exact h.elim

theorem propLoopEnv_deltaFragment : DeltaFragment propLoopEnv := by
  intro p r h
  cases h with
  | delta => exact ⟨_, rfl⟩
  | quot hdf _ _ =>
    have h1 := propLoopEnv_key_length hdf
    rw [key_quotDefEq] at h1; simp at h1
  | iota _ _ _ _ hdf _ _ _ =>
    have h1 := propLoopEnv_key_length hdf
    rw [VInductDecl'.key_iotaRule] at h1; simp at h1

/-- `Params` over `propLoopEnv`, obtained from `paramsOfDelta` rather than by hand. -/
@[instance_reducible] def propLoopParamsOfWF : Params :=
  paramsOfDelta propLoopEnv_wf 0 propLoopEnv_deltaFragment

theorem propLoopParamsOfWF_env : @Params.env propLoopParamsOfWF = propLoopEnv := rfl

end Fires

end VEnv
end Lean4Lean
