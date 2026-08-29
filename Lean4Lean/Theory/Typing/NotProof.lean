import Lean4Lean.Theory.Typing.SortUniq

/-!
# "A Π is not a proof" — the Π half of the `proofIrrel` residual

`Theory/Typing/SortUniq.lean` proves `VEnv.sort_not_proof`: granted `VEnv.SortUniq`, a sort
is not a proof, which is the `proofIrrel` case of `IsDefEqU.sort_inv`.

Three more statements in `Theory/Typing/Injectivity.lean` have a `proofIrrel` residual, and
after that file's inductions were written out it became visible that **all three want the Π
half of the same fact** rather than the sort half:

| statement | its `proofIrrel` case asks |
|---|---|
| `IsDefEqU.sort_inv` | a **sort** is not a proof — `VEnv.sort_not_proof` |
| `IsDefEqU.forallE_inv` | a **Π** is not a proof — `VEnv.forallE_not_proof`, below |
| `IsDefEqU.sort_forallE_inv` | *either* one; both endpoints are available |
| `IsDefEqU.const_forallE_inv` | a **Π** is not a proof — below |

This file supplies the missing half, from the *same* hypothesis and by the *same* argument,
so that the accounting is machine-checked rather than prose: **the Π/sort inversion family's
`proofIrrel` residual is one obligation, `VEnv.SortUniq`, not two.**

`SortUniq` remains a hypothesis with no instance anywhere in the tree — see
`Theory/Typing/SortUniq.lean`'s docstring, including its argument that no *model* route to
`SortUniq` can exist.  Read everything here as a reduction between open statements.

The same hypothesis is what `ChurchRosser.lean`'s `NormalEq.appDF_proofIrrel` takes as its
`hsu` argument, and what the two "function is a proof" `sorry`s in `NormalEq.descend` are
waiting for.  So this is not a fourth consumer: it is the third sighting of one.
-/

namespace Lean4Lean
namespace VEnv

variable {env : VEnv} {U : Nat} {Γ : List VExpr} {A B p : VExpr} {b : Bool}

/-- **The type of a Π is a sort** — granted universe uniqueness.

The mirror of `HasTypeStrong.sort_type`, and it needs `huniq` in exactly the same place and
for exactly the same reason: the induction's `defeq` case holds the equation `A ≡ B` at the
level the derivation chose and the inductive hypothesis at the level `A` was separately
found to inhabit. -/
theorem HasTypeStrong.forallE_type (huniq : env.SortUniq U) (hΓ : OnCtx Γ (env.IsType U))
    (H : env.HasTypeStrong U Γ (.forallE A B) p b) :
    ∃ l w, w.WF U ∧ env.IsDefEq U Γ (.sort l) p (.sort w) := by
  generalize eq : VExpr.forallE A B = e at H
  induction H with cases eq
  | forallE h1 h2 _ _ =>
    -- `w` must be pinned by the equation, not by the `WF` slot, exactly as in `sort_type`.
    refine ⟨_, _, ?_, IsDefEq.sortDF (l := VLevel.imax _ _) ⟨h1, h2⟩ ⟨h1, h2⟩ rfl⟩
    exact ⟨h1, h2⟩
  | base _ ih => exact ih hΓ rfl
  | defeq hu hAB hA _ _ _ _ ih3 =>
    obtain ⟨l, w, hw, h2⟩ := ih3 hΓ rfl
    exact ⟨l, w, hw,
      h2.trans (.defeqDF (.sortDF hu hw (huniq hΓ hu hw hA.hasType h2.hasType.2)) hAB.defeq)⟩

/-- **A Π is not a proof** — granted universe uniqueness.

Carneiro's argument for `sort_not_proof` (`~/lean-type-theory/unique.tex:266`), transposed:
`p` would have to be both `.sort .zero` and `.sort (l+1)`, and `0 ≈ l+1` at no valuation. -/
theorem forallE_not_proof (huniq : env.SortUniq U) (henv : Ordered env)
    (hΓ : OnCtx Γ (env.IsType U))
    (hp : env.HasType U Γ p (.sort .zero)) (hf : env.HasType U Γ (.forallE A B) p) : False := by
  obtain ⟨l, w, hw, h2⟩ := ((hf.strong henv hΓ).hasType'.1).forallE_type huniq hΓ
  have hw0 : w ≈ VLevel.zero := huniq hΓ hw trivial h2.hasType.2 hp
  have hl : l.WF U := h2.sort_inv_l henv
  have hw2 : w ≈ VLevel.succ l :=
    huniq hΓ hw (by exact hl) h2.hasType.1 (HasType.sort (by exact hl))
  have := hw0.symm.trans hw2
  exact absurd (congrFun this []) (by simp [VLevel.eval])

end VEnv
end Lean4Lean
