import Lean.Data.SMap
import Std.Data.HashMap.Lemmas
import Lean4Lean.Std.HashMap
import Lean4Lean.Std.PersistentHashMap

namespace Lean.SMap

variable [BEq α] [Hashable α]

/--
Well-formedness of a staged map as this kernel builds it: **stage 1**, with an empty
`PersistentHashMap` half.

`SMap` is the type of `Lean.Kernel.Environment.constants`, and its `map₂` half is a
`PersistentHashMap`, whose `insertAux`/`findAux`/`containsAux` are `partial` upstream and
therefore `opaque`: *nothing* can be proved about them, which is why this repo used to assume
`PersistentHashMap.WF.{toList'_insert, find?_eq}` and `findAux_isSome`.

At stage 1 every operation this kernel uses — `insert`, `find?`, `find?'`, `contains` —
dispatches to the `Std.HashMap` half, which has a complete verified API upstream, and `map₂`
is neither read nor written.  `WF` records exactly that, and it is preserved by `insert`,
which is the only operation that writes.

The cost is that inserts now go into a `Std.HashMap`; see `divergences.md`.
-/
structure WF (s : SMap α β) : Prop where
  /-- The map is at stage 1, so no operation consults `map₂`. -/
  stage : s.stage₁ = true
  /-- The `PersistentHashMap` half is empty. -/
  map₂ : s.map₂ = .empty

theorem WF.empty : WF ({} : SMap α β) := ⟨rfl, rfl⟩

protected theorem WF.insert {s : SMap α β} (h : s.WF) (k : α) (v : β)
    (_hn : s.find? k = none) : (s.insert k v).WF := by
  obtain ⟨st, m₁, m₂⟩ := s
  cases h.stage
  exact ⟨rfl, h.map₂⟩

variable [LawfulBEq α] [LawfulHashable α] in
theorem WF.find?_insert {s : SMap α β} (h : s.WF) :
    (s.insert k v).find? x = if k == x then some v else s.find? x := by
  obtain ⟨st, m₁, m₂⟩ := s
  cases h.stage
  simp [insert, find?, Std.HashMap.getElem?_insert]

noncomputable def toList' [BEq α] [Hashable α] (m : SMap α β) :
    List (α × β) := m.map₂.toList' ++ m.map₁.toList

theorem WF.toList'_eq {m : SMap α β} (h : m.WF) : m.toList' = m.map₁.toList := by
  simp [toList', h.map₂]

open scoped _root_.List in
theorem WF.toList'_insert {α β} [BEq α] [LawfulBEq α] [Hashable α] [LawfulHashable α]
    {m : SMap α β} (wf : WF m) (a : α) (b : β)
    (h : m.find? a = none) :
    (m.insert a b).toList' ~ (a, b) :: m.toList' := by
  obtain ⟨st, m₁, m₂⟩ := m
  obtain rfl : st = true := wf.stage
  obtain rfl : m₂ = .empty := wf.map₂
  show SMap.toList' ⟨true, m₁.insert a b, .empty⟩ ~ (a, b) :: SMap.toList' ⟨true, m₁, .empty⟩
  simp only [toList', PersistentHashMap.toList'_empty, List.nil_append]
  simp only [find?] at h
  have : EquivBEq α := inferInstance
  refine (List.filter_eq_self.2 ?_ ▸ Std.HashMap.insert_toList (a := a) (b := b) m₁ :)
  rintro ⟨a', b'⟩ hm
  refine Decidable.by_contra fun h2 => ?_
  simp at h2
  subst h2
  have : m₁[a]? = some b' :=
    Std.HashMap.getElem?_eq_some_iff_exists_beq_and_mem_toList.2 ⟨a, by simp, hm⟩
  rw [h] at this
  exact absurd this nofun

theorem WF.find?_eq {α β} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]
    {m : SMap α β} (wf : WF m) (a : α) : m.find? a = m.toList'.lookup a := by
  obtain ⟨st, m₁, m₂⟩ := m
  obtain rfl : st = true := wf.stage
  obtain rfl : m₂ = .empty := wf.map₂
  show m₁[a]? = List.lookup a (SMap.toList' ⟨true, m₁, .empty⟩)
  simp only [toList', PersistentHashMap.toList'_empty, List.nil_append]
  exact Std.HashMap.getElem?_eq_lookup_toList m₁ a

theorem WF.find?'_eq_find? {α β} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {m : SMap α β} (wf : WF m) (a : α) : m.find?' a = m.find? a := by
  obtain ⟨st, m₁, m₂⟩ := m
  obtain rfl : st = true := wf.stage
  rfl

theorem WF.find?_isSome {α β} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {m : SMap α β} (wf : WF m) (a : α) : m.contains a = (m.find? a).isSome := by
  obtain ⟨st, m₁, m₂⟩ := m
  obtain rfl : st = true := wf.stage
  exact Std.HashMap.contains_eq_isSome_getElem?
