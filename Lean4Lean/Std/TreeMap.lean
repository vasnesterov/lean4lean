import Std.Data.DTreeMap.Internal.WF.Lemmas
import Std.Data.TreeMap.Basic

/-!
# Missing `Std.TreeMap` lemma

Upstream (`Std/Data/DTreeMap/Internal/WF/Lemmas.lean`) proves
`Std.DTreeMap.Internal.Impl.all_eq_all_toListModel` but not its `any` counterpart.
This file supplies the mirror image, which is what `Std.TreeMap.any_eq_any_toList`
in `Lean4Lean/Verify/Axioms.lean` needs; see `docs/axiom-audit.md` §8.

Deliberately stated without an `Ord α` instance, matching upstream's `all` lemma:
adding one stops `simp` from matching the goal.
-/

namespace Std.DTreeMap.Internal.Impl

theorem any_eq_any_toListModel {α : Type u} {β : α → Type v} {p : (a : α) → β a → Bool}
    {m : Impl α β} : m.any p = m.toListModel.any fun x => p x.1 x.2 := by
  simp [any, ForIn.forIn, Id.run_bind]
  rw [forIn_eq_forIn_toListModel, ← toList_eq_toListModel, forIn_eq_forIn']
  induction m.toList with
  | nil => simp
  | cons hd tl ih =>
    simp only [forIn'_eq_forIn, List.any_cons]
    by_cases h : p hd.fst hd.snd = true
    · simp [h]
    · simp only [forIn'_eq_forIn] at ih
      simp [h, ih]

end Std.DTreeMap.Internal.Impl
