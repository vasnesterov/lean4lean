import Lean4Lean.Verify.Typing.ConstSpine
import Lean4Lean.Theory.Typing.ParamsWitness

/-!
# `VEnv.WeakNorm` is **false**

`Verify/Typing/ConstSpine.lean` ends at one residual.  Facts (A), (B) and (D) of
`Theory/Typing/Injectivity.lean` are proved there from Church--Rosser; fact (C) --
*rigidity*: a term definitionally equal to a rule-free constant application weak-head reduces
to one with the same head -- is proved from **one** extra hypothesis and nothing else,

    VEnv.WeakNorm : ∀ Γ e A, OnCtx Γ (IsType env univs) → HasType env univs Γ e A →
      ∃ e', WHRedS Γ e e' ∧ WHNF Γ e'

("every well-typed term has a weak-head normal form"), by `constRigid_of_weakNorm` and, at
the canonical pattern table, `Rigidity.lean`'s `constRigidPat_of_weakNorm`.

**That hypothesis is not open, it is refuted.**  `not_weakNorm` / `not_weakNorm'` below
exhibit a `VEnv.Params` instance -- i.e. a well-formed environment together with a pattern
table satisfying every side condition `Theory/Typing/ChurchRosser.lean` asks for -- at which
`WeakNorm` fails.  The witness is `CycleConv.propLoopEnv`, one `.unsafeDef` step from
`VEnv.empty`:

    A : Prop := B        B : Prop := A

Both `A` and `B` are well typed (`hasType_constProp`, at `.sort .zero`), each δ-reduces to
the other (`whRed_AB`, `whRed_BA`), and `WHRed` is **deterministic** (`WHRed.determ`), so
every `WHRedS`-reduct of `A` is `A` or `B` (`whRedS_mem`) and neither is a `WHNF`.  `A` is
therefore a well-typed term with no weak-head normal form.

Two independent instances are used, because the refutation must not be an artefact of a
bespoke pattern table:

* `not_weakNorm` uses `ParamsWitness.propLoopParams`, the hand-built instance;
* `not_weakNorm'` uses `propLoopParamsOfWF = paramsOfDelta propLoopEnv_wf 0 …`, which
  `Theory/Typing/ParamsBuild.lean` derives from `VEnv.WF` **alone** on the δ fragment, with
  the canonical `Lean4Lean.Pat` table.

`not_forall_weakNorm_of_wf` states the consequence in the form the consumers need: there is
no proof of `WeakNorm` from `env.WF` -- not even for environments whose every rule is a
δ-rule, where `Params` needs no open hypothesis at all.

## What this does and does not settle

It settles that **the route to (C) through `WeakNorm` is dead** at the generality (C) is
wanted at, namely `∀ env, env.WF → …` (`Verify/Typing/Lemmas.lean`'s `TrProj.weak'_inv`,
whose only non-shared residual is (C) in its `constRigidPat_of_weakNorm` form).  Any repair
must either prove (C) directly -- it is strictly weaker than `WeakNorm`, since it only asks
for a reduct with a *given rule-free head*, and asks it only of subjects convertible with
such a spine -- or add an environment hypothesis excluding cyclic δ-rules (`.unsafeDef`
blocks are what `VEnv.WF` permits here; see `Theory/Typing/CycleConv.lean` for what such a
block does and does not do to conversion).

It does **not** refute (C).  At this very witness (C) is vacuous: `PatFreeHead c` forces
`c ∉ {A, B}` (`patFreeHead_ne`) while the only constants the environment declares are `A` and
`B` (`propLoopEnv_constants_eq`), so no rule-free constant spine is even well typed here.
The witness kills the *lemma* `constRigid_of_weakNorm` as a usable route, by killing its
hypothesis; it says nothing about (C)'s truth.

Pattern: `Theory/Typing/DescendRefute.lean`, `Theory/Typing/ParRedPropRefute.lean`.

*Confidence: machine-checked and `sorry`-free -- `#print axioms
Lean4Lean.VEnv.PropLoopWeakNorm.not_weakNorm` is `[propext, Classical.choice, Quot.sound]`.
`propLoopEnv_wf`, `propLoopParams` and `propLoopParamsOfWF` are all `sorry`-free upstream.*
-/

namespace Lean4Lean
namespace VEnv

open VExpr

namespace PropLoopWeakNorm

section Hand

attribute [local instance] propLoopParams

theorem whRed_AB : WHRed [] (.const `A []) (.const `B []) :=
  .extra (p := .const `A) (r := ⟨.fixed (.const `B []) () trivial, .true⟩)
    (.inl ⟨rfl, rfl⟩) .const trivial

theorem whRed_BA : WHRed [] (.const `B []) (.const `A []) :=
  .extra (p := .const `B) (r := ⟨.fixed (.const `A []) () trivial, .true⟩)
    (.inr ⟨rfl, rfl⟩) .const trivial

theorem whRedS_mem {e : VExpr} (H : WHRedS [] (.const `A []) e) :
    e = .const `A [] ∨ e = .const `B [] := by
  induction H with
  | rfl => exact .inl rfl
  | tail h1 h2 ih =>
    rcases ih with rfl | rfl
    · exact .inr (h2.determ whRed_AB ▸ rfl)
    · exact .inl (h2.determ whRed_BA ▸ rfl)

/-- At the witness, `PatFreeHead` -- (C)'s side condition -- excludes both constants the
environment declares.  Half of the reason (C) itself is vacuous here. -/
theorem patFreeHead_ne {c : Lean.Name} (h : PatFreeHead c) : c ≠ `A ∧ c ≠ `B := by
  refine ⟨?_, ?_⟩ <;> rintro rfl
  · exact h (.const `A) ⟨.fixed (.const `B []) () trivial, .true⟩ (Or.inl ⟨rfl, rfl⟩) rfl
  · exact h (.const `B) ⟨.fixed (.const `A []) () trivial, .true⟩ (Or.inr ⟨rfl, rfl⟩) rfl

theorem not_weakNorm : ¬ WeakNorm := by
  intro hwn
  obtain ⟨e', hred, hw⟩ :=
    hwn [] (.const `A []) (.sort .zero) trivial (hasType_constProp propLoopEnv_A)
  rcases whRedS_mem hred with rfl | rfl
  · exact hw _ whRed_AB
  · exact hw _ whRed_BA

end Hand

section General

attribute [local instance] propLoopParamsOfWF

theorem pat_A : Pat propLoopEnv (.const `A) (deltaRHS `A (.const `B []) trivial, .true) :=
  .delta _ propLoopEnv_defeqs_A

theorem pat_B : Pat propLoopEnv (.const `B) (deltaRHS `B (.const `A []) trivial, .true) :=
  .delta _ propLoopEnv_defeqs_B

theorem whRed_AB' : WHRed [] (.const `A []) (.const `B []) :=
  .extra pat_A .const trivial

theorem whRed_BA' : WHRed [] (.const `B []) (.const `A []) :=
  .extra pat_B .const trivial

theorem whRedS_mem' {e : VExpr} (H : WHRedS [] (.const `A []) e) :
    e = .const `A [] ∨ e = .const `B [] := by
  induction H with
  | rfl => exact .inl rfl
  | tail h1 h2 ih =>
    rcases ih with rfl | rfl
    · exact .inr (h2.determ whRed_AB' ▸ rfl)
    · exact .inl (h2.determ whRed_BA' ▸ rfl)

theorem not_weakNorm' : ¬ WeakNorm := by
  intro hwn
  obtain ⟨e', hred, hw⟩ :=
    hwn [] (.const `A []) (.sort .zero) trivial (hasType_constProp propLoopEnv_A)
  rcases whRedS_mem' hred with rfl | rfl
  · exact hw _ whRed_AB'
  · exact hw _ whRed_BA'

/-- No proof of `WeakNorm` from `VEnv.WF`: it fails even on the δ fragment, where
`VEnv.Params` is available with no open hypothesis. -/
theorem not_forall_weakNorm_of_wf :
    ¬ ∀ (env : VEnv) (U : Nat) (henv : env.WF) (hd : DeltaFragment env),
        @WeakNorm (paramsOfDelta henv U hd) :=
  fun h => not_weakNorm' (h propLoopEnv 0 propLoopEnv_wf propLoopEnv_deltaFragment)

/-- The same, quantified over `Params` instances rather than over environments. -/
theorem not_forall_weakNorm : ¬ ∀ P : Params, @WeakNorm P :=
  fun h => not_weakNorm' (h _)

end General

/-- The other half of (C)'s vacuity at the witness: `propLoopEnv` declares no constant
besides `A` and `B`. -/
theorem propLoopEnv_constants_eq {c : Lean.Name} {ci : VConstant}
    (h : propLoopEnv.constants c = some ci) : c = `A ∨ c = `B := by
  by_cases hB : `B = c
  · exact .inr hB.symm
  by_cases hA : `A = c
  · exact .inl hA.symm
  · rw [show propLoopEnv.constants c = none from by
      simp [propLoopEnv, propLoopEnv2, propLoopEnv1, VEnv.addDefEqs, VEnv.empty, hA, hB]] at h
    exact absurd h nofun

end PropLoopWeakNorm

end VEnv
end Lean4Lean
