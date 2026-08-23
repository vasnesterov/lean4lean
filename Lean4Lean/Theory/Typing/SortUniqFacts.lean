import Lean4Lean.Theory.Typing.SortUniq
import Lean4Lean.Theory.Typing.UniqueTyping

/-!
# `SortUniq` is no stronger than the family it is used to attack

`Theory/Typing/SortUniq.lean` states universe uniqueness as a hypothesis and derives
`sort_not_proof` from it.  A hypothesis is only worth stating if it is satisfiable, and the
one check available here is an upper bound: `SortUniq` *follows* from `IsDefEq.uniq` and
`IsDefEqU.sort_inv`, which is what the whole Π/sort inversion cone is for.

So the reduction in `SortUniq.lean` does not smuggle in extra strength — and, conversely,
this file is **not** evidence that `SortUniq` holds: it depends on `sorryAx` through
`sort_inv`.  `#print axioms Lean4Lean.VEnv.WF.sortUniq` says so.
-/

namespace Lean4Lean
namespace VEnv

theorem WF.sortUniq {env : VEnv} {U : Nat} (henv : env.WF) : env.SortUniq U :=
  fun hΓ _ _ h1 h2 => IsDefEqU.sort_inv henv hΓ (h1.uniqU henv hΓ h2)

end VEnv
end Lean4Lean
