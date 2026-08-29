import Lean.Data.SMap
import Std.Data.HashMap.Lemmas
import Lean4Lean.Verify.Axioms

namespace Lean.PersistentHashMap

/-- The empty `PersistentHashMap` really is empty.  This is provable — `Node.toList'` is
structural recursion over the `Node` inductive — unlike anything about `insert`/`find?`, whose
`insertAux`/`findAux` are `partial` upstream and therefore `opaque`. -/
@[simp] theorem toList'_empty [BEq α] [Hashable α] :
    (.empty : PersistentHashMap α β).toList' = [] := by
  have this n : @Node.toList' α β (.entries ⟨.replicate n .null⟩) = [] := by
    simp [Node.toList']
    induction n <;> simp [*, List.replicate_succ]
  apply this

@[simp] theorem toList'_empty' [BEq α] [Hashable α] :
    ({} : PersistentHashMap α β).toList' = [] := toList'_empty
