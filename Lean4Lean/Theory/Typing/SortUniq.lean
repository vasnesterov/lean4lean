import Lean4Lean.Theory.Typing.Strong

/-!
# Universe uniqueness, and what it buys

`Theory/Typing/Injectivity.lean`'s open statements are usually described as needing "the
Church–Rosser theorem".  Writing the inductions out shows they need **two** separate things,
and only one of them is about reduction:

1. **Normalisation** — for `IsDefEqStrong.trans`: a term convertible with a sort reduces to
   a sort.  There is no way around this one.
2. **Universe uniqueness** — `VEnv.SortUniq` below: `Γ ⊢ e : .sort u` and `Γ ⊢ e : .sort v`
   force `u ≈ v`.

This file isolates (2) and shows what it alone is worth.  The one theorem here,
`VEnv.sort_not_proof`, closes the `proofIrrel` case of `IsDefEqU.sort_inv` outright — the
case whose refutation was previously described as needing `sort_inv` itself.  It also
supplies exactly the level-alignment step that `IsDefEqU.forallE_inv_stratified`'s
`forallEDF` and `symm` cases stall on (see that lemma's docstring).  So, granted (2), the
whole Π/sort inversion family reduces to the single `trans` case.

**`SortUniq` is a hypothesis, not a theorem.**  Nothing in this repository exhibits one, for
any environment.  It is the `VExpr`-side statement of
`Experimental/Reflect/Capstone.lean`'s `sort_uniq_of_hasType` — which is not available, its
`Params`-style side condition being unsatisfiable — and it is what
`SetModel/Interp.lean`'s `LevelAssign.srt_sound` field demands (that field asks a *single*
chosen level to agree with *every* type of a term, which is (2) restated).  So read every
result below as a reduction between open statements, not as progress on either.

`SortUniq` is stated for types only (`e` at a sort), which is all the consumers need; the
`srt`-flavoured version for arbitrary terms is strictly stronger and is not used here.

## Two guards, and why they are there

`SortUniq` carries `OnCtx Γ (env.IsType U)` and `WF U` on both levels.  Neither is
decoration.  `SetModel/LevelAssignUnsat.lean` machine-checks that the *unguarded* analogue
of this condition — `LevelAssign`'s original `lvl_sound` — is not merely unproved but
**unsatisfiable for every environment**: `IsDefEq.bvar` has no side condition, so a context
may hold `.sort (.param U)` and derive `Γ ⊢ .bvar 0 : .sort (.param U)`, a level no `WF U`
level is equivalent to.  Guarding is what keeps this hypothesis from being empty for a
reason that has nothing to do with the mathematics.  Both consumers below have the guards
available for free.

`Theory/Typing/SortUniqFacts.lean` machine-checks the other direction: `SortUniq` follows
from `IsDefEq.uniq` and `IsDefEqU.sort_inv`.  So assuming it is not assuming anything beyond
the family it is used to attack — it is an *upper* bound on the hypothesis's strength, and
the reason to believe it is satisfiable at all.
-/

namespace Lean4Lean
namespace VEnv

/-- **Universe uniqueness.**  Two sorts inhabited by the same type agree.

Equivalently `IsDefEq.uniq` composed with `IsDefEqU.sort_inv`, restricted to sorts — but
stated separately because both of those are downstream of, or equal to, the statements this
is used to attack. -/
def SortUniq (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {e : VExpr} {u v : VLevel},
    OnCtx Γ (env.IsType U) → u.WF U → v.WF U →
    env.HasType U Γ e (.sort u) → env.HasType U Γ e (.sort v) → u ≈ v

variable {env : VEnv} {U : Nat} {Γ : List VExpr} {u : VLevel} {p : VExpr} {b : Bool}

/-- **The type of a sort is a sort, one level up** — granted universe uniqueness.

Without `huniq` this is *not* routine, contrary to how it reads.  The induction's `defeq`
case has the equation `A ≡ B` at the level the derivation chose and the inductive hypothesis
at the level `A` was found to inhabit, and retyping either to the other is exactly
`huniq`. -/
theorem HasTypeStrong.sort_type (huniq : env.SortUniq U) (hΓ : OnCtx Γ (env.IsType U))
    (H : env.HasTypeStrong U Γ (.sort u) p b) :
    ∃ u' w, u ≈ u' ∧ w.WF U ∧ env.IsDefEq U Γ (.sort (.succ u')) p (.sort w) := by
  generalize eq : VExpr.sort u = e at H
  induction H with cases eq
  | sort' _ h2 h3 =>
    -- `w` must be pinned by the equation, not by the `WF` slot: `(w.succ.succ).WF` and
    -- `w.WF` are definitionally equal, so unifying on the `WF` slot first picks the wrong `w`.
    refine ⟨_, _, h3, ?_, IsDefEq.sortDF h2 h2 rfl⟩
    exact h2
  | base _ ih => exact ih hΓ rfl
  | defeq hu hAB hA _ _ _ _ ih3 =>
    obtain ⟨u', w, h1, hw, h2⟩ := ih3 hΓ rfl
    exact ⟨u', w, h1, hw,
      h2.trans (.defeqDF (.sortDF hu hw (huniq hΓ hu hw hA.hasType h2.hasType.2)) hAB.defeq)⟩

/-- **A sort is not a proof** — granted universe uniqueness.

This is the `proofIrrel` case of `IsDefEqU.sort_inv`.  The argument is Carneiro's
(`~/lean-type-theory/unique.tex:266`): `p` would have to be both `.sort .zero` and
`.sort (u+2)`, and `0 ≈ u+2` is false at any valuation. -/
theorem sort_not_proof (huniq : env.SortUniq U) (henv : Ordered env)
    (hΓ : OnCtx Γ (env.IsType U))
    (hp : env.HasType U Γ p (.sort .zero)) (hu : env.HasType U Γ (.sort u) p) : False := by
  obtain ⟨u', w, _, hw, h2⟩ := ((hu.strong henv hΓ).hasType'.1).sort_type huniq hΓ
  have hw0 : w ≈ VLevel.zero := huniq hΓ hw trivial h2.hasType.2 hp
  have hu' : (VLevel.succ u').WF U := h2.sort_inv_l henv
  have hw2 : w ≈ (VLevel.succ (VLevel.succ u')) :=
    huniq hΓ hw (by exact hu') h2.hasType.1 (HasType.sort (by exact hu'))
  have := hw0.symm.trans hw2
  exact absurd (congrFun this []) (by simp [VLevel.eval])

end VEnv
end Lean4Lean
