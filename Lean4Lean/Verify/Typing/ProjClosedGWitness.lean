import Lean4Lean.Theory.Inductive.ProjClosedG
import Lean4Lean.Verify.Typing.ProjGenWitness

/-!
# Witnesses for `ProjClosedG`

Three things are checked here, and they are different claims:

1. **The refutation is re-run against the fix.**  `ProjClosedGap.projClosedG_needs_recArgs`
   (`ProjGenWitness.lean`) exhibits a block satisfying all three `ProjClosed` fields whose
   `minorBinders` is not `ClosedTele` at the spine arity.  `badCtor_not_projClosedG` below
   shows that same block **fails `ProjClosedG`** — so the repair visibly kills its own
   witness rather than merely coexisting with it.
2. **Both conjuncts of the fourth field are load-bearing.**  The old witness moves only the
   stored `ξ` (`VIndRecArg.binders`).  `argsCtor` moves only the stored `π` (`.args`), with
   `ξ` empty, and the conclusion still fails — so the second conjunct is not a passenger.
3. **The consumer fires at a block where the fourth field carries real data.**
   `Rich.minorBinders_closed` runs `closedTele_minorBinders` end to end at a block with a
   parameter, an index, two fields, and a recursive field whose `ξ` and `π` are both
   non-empty.  The bound is **exactly saturated** — `Rich.minorBinders_not_closed_at_1` is
   the negative control showing the same telescope is *not* closed one below.
-/

namespace Lean4Lean

open VExpr VEnv

namespace ProjClosedGap

/-! ## 1. The refutation, re-run against the fix -/

/-- **The repair kills the witness.**  `blockOf badCtor` satisfies `ProjClosedG`'s first
three fields — they are `ProjClosed`'s, and `projClosedG_needs_recArgs` already checked
them — and **fails the fourth**, at the very recursive field that made its `minorBinders`
open.  So the four-field predicate is not merely *sufficient* for the consumer
(`closedTele_minorBinders`); it is *false* exactly where the three-field one was too weak. -/
theorem badCtor_not_projClosedG : ¬ (blockOf badCtor).ProjClosedG := by
  intro H
  have hmem : ((0 : Nat), ({ binders := [.bvar 0], idx := 0, args := [] } : VIndRecArg))
      ∈ badCtor.recFields := List.mem_singleton_self _
  have h := (H.recArgs 0 _ rfl badCtor (List.mem_singleton_self _) 0 _ hmem).1
  exact Nat.not_lt_zero 0 h.1

/-! ## 2. The `args` conjunct is load-bearing too -/

/-- A recursive field with **closed `ξ`** (it is empty) but a stored `π` that is not closed
at `np + i + |ξ| = 0`. -/
def argsCtor : VIndCtor where
  name := `ProjClosedGap.Q.mk
  params := []
  fields := [{ type := qty, lvl := .succ .zero,
               recArg := some { binders := [], idx := 0, args := [.bvar 0] } }]
  args := []

/-- The minor's telescope at `argsCtor`: the induction hypothesis reads `.bvar 2`, one past
the `k = 2` its entry allows.  The offending variable comes from `π`, not from `ξ`. -/
theorem minorBinders_args :
    ((blockOf argsCtor).minorBinders 0 argsCtor).map (VExpr.instL [])
      = [qty, ((VExpr.bvar 1).app (.bvar 2)).app (.bvar 0)] := rfl

/-- **The second conjunct of `recArgs` is not a passenger.**  `ξ` is closed here (it is
empty), all three `ProjClosed` fields hold, and the conclusion block A needs still fails —
because the stored `π` is open. -/
theorem projClosedG_needs_recArgs_args :
    VExpr.ClosedTele (blockOf argsCtor).params 0 ∧
    VExpr.ClosedTele ((blockOf argsCtor).types.getD 0 default).indices (blockOf argsCtor).np ∧
    VExpr.ClosedTele (argsCtor.fields.map (·.type)) (blockOf argsCtor).np ∧
    VExpr.ClosedTele ({ binders := [], idx := 0, args := [.bvar 0] } : VIndRecArg).binders
      ((blockOf argsCtor).np + 0) ∧
    ¬ VExpr.ClosedTele (((blockOf argsCtor).minorBinders 0 argsCtor).map (VExpr.instL []))
        ((blockOf argsCtor).np + (blockOf argsCtor).nm + 0) := by
  refine ⟨trivial, trivial, ⟨trivial, trivial⟩, trivial, ?_⟩
  rw [minorBinders_args]
  show ¬ VExpr.ClosedTele [qty, _] 1
  simp [VExpr.ClosedTele, VExpr.ClosedN, qty]

/-- …and `argsCtor`'s block fails `ProjClosedG` too, at the `args` conjunct. -/
theorem argsCtor_not_projClosedG : ¬ (blockOf argsCtor).ProjClosedG := by
  intro H
  have hmem : ((0 : Nat), ({ binders := [], idx := 0, args := [.bvar 0] } : VIndRecArg))
      ∈ argsCtor.recFields := List.mem_singleton_self _
  have h := (H.recArgs 0 _ rfl argsCtor (List.mem_singleton_self _) 0 _ hmem).2
  exact Nat.not_lt_zero 0 (h (.bvar 0) (List.mem_singleton_self _))

end ProjClosedGap

/-! ## 3. The consumer, fired where the fourth field carries data -/

namespace Rich

open VExpr

/-- One parameter, one index, two fields — the second recursive with a **non-empty** `ξ`
that mentions the parameter and a **non-empty** `π` that mentions the `ξ` binder.  As with
every witness in this cluster, only the shape data matters and no `WF` claim is made. -/
def richCtor : VIndCtor where
  name := `Rich.Q.mk
  params := [.const `Rich.P []]
  fields :=
    [ { type := .bvar 0, lvl := .succ .zero, recArg := none },
      { type := .const `Rich.Dummy [], lvl := .succ .zero,
        recArg := some { binders := [.bvar 1], idx := 0, args := [.bvar 0] } } ]
  args := [.const `Rich.Ix0 []]

def richTy : VIndType where
  name := `Rich.Q
  type := .sort (.succ .zero)
  indices := [.const `Rich.Ix []]
  ctors := [richCtor]

def richBlock : VInductDecl' where
  uvars := 0
  params := [.const `Rich.P []]
  lvl := .succ .zero
  isLE := false
  types := [richTy]

/-- The fourth field really has something to say here: `ξ = [.bvar 1]` points at the
parameter, `π = [.bvar 0]` points at the `ξ` binder. -/
theorem recFields_rich :
    richCtor.recFields = [(1, { binders := [.bvar 1], idx := 0, args := [.bvar 0] })] := rfl

/-- `ProjClosedG` at this block, built by hand (no `WF` claim is made, so it cannot come
from `projClosedG_of_wf`). -/
theorem richBlock_projClosedG : richBlock.ProjClosedG where
  params := ⟨trivial, trivial⟩
  indices := by
    rintro (_ | t) T' hT
    · obtain rfl : richTy = T' := Option.some.inj hT
      exact ⟨trivial, trivial⟩
    · exact absurd hT (by simp [richBlock])
  fields := by
    rintro (_ | t) T' hT C' hC
    · obtain rfl : richTy = T' := Option.some.inj hT
      obtain rfl : C' = richCtor := List.mem_singleton.1 hC
      exact ⟨Nat.zero_lt_one, trivial, trivial⟩
    · exact absurd hT (by simp [richBlock])
  recArgs := by
    rintro (_ | t) T' hT C' hC i r hr
    · obtain rfl : richTy = T' := Option.some.inj hT
      obtain rfl : C' = richCtor := List.mem_singleton.1 hC
      obtain ⟨rfl, rfl⟩ : i = 1 ∧ r = { binders := [.bvar 1], idx := 0, args := [.bvar 0] } :=
        Prod.mk.injEq .. ▸ List.mem_singleton.1 hr
      refine ⟨⟨Nat.one_lt_two, trivial⟩, fun a ha => ?_⟩
      obtain rfl : a = .bvar 0 := List.mem_singleton.1 ha
      exact show (0:Nat) < 3 from by omega
    · exact absurd hT (by simp [richBlock])

/-- The minor's binder telescope at this block, computed.  The third entry is the induction
hypothesis: its own binder is the stored `ξ` shifted to `.bvar 3`, and its body applies the
motive `.bvar 3` to the stored `π` (shifted to `.bvar 0`) and to the recursive field applied
to that binder.  Both halves of `recArgs` are visible in it. -/
theorem minorBinders_rich :
    (richBlock.minorBinders 0 richCtor).map (VExpr.instL [])
      = [.bvar 1, .const `Rich.Dummy [],
         .forallE (.bvar 3)
           (((VExpr.bvar 3).app (.bvar 0)).app ((VExpr.bvar 1).app (.bvar 0)))] := rfl

/-- **`closedN_ihType` fired**, at a recursive field with non-empty `ξ` and non-empty `π`.
The bound `D.np + D.nm + q + nf + s` is `1 + 1 + 0 + 2 + 0 = 4`, and the entry's largest
variable is `.bvar 3`: **exactly saturated**. -/
theorem ihType_closed :
    (richBlock.ihType 0 richCtor 1
        { binders := [.bvar 1], idx := 0, args := [.bvar 0] } 0).ClosedN 4 :=
  VInductDecl'.closedN_ihType (D := richBlock) (C' := richCtor) (q := 0) (s := 0) (i := 1)
    (r := { binders := [.bvar 1], idx := 0, args := [.bvar 0] })
    Nat.one_pos (show 1 < richCtor.fields.length from Nat.one_lt_two)
    ⟨Nat.one_lt_two, trivial⟩
    (fun a ha => by
      obtain rfl : a = .bvar 0 := List.mem_singleton.1 ha
      exact show (0:Nat) < 3 from by omega)

/-- **The consumer, fired end to end.**  `closedTele_minorBinders` at `richBlock`, from the
hand-built `ProjClosedG`.  This is the audit `docs/handoff-projections.md` §0.9 asked for:
the four-field predicate *does* discharge `VExpr.lift'_instAllTele`'s hypothesis, at a block
where the fourth field carries data no `ProjClosed` field mentions. -/
theorem minorBinders_closed :
    VExpr.ClosedTele ((richBlock.minorBinders 0 richCtor).map (VExpr.instL []))
      (richBlock.np + richBlock.nm + 0) :=
  VInductDecl'.closedTele_minorBinders richBlock_projClosedG (t := 0) rfl
    (List.mem_singleton_self _) 0 []

/-! ### Negative controls

`minorBinders_closed`'s bound is `D.np + D.nm + q = 1 + 1 + 0 = 2`.  Both of the following
are rejected, and neither is a length error — the telescope has three entries either way. -/

/-- One below the spine arity the lemma proves, the telescope is **not** closed: the field
entry `.bvar 1` (the parameter, weakened past the motive block) already escapes.  So the
`D.np + D.nm + q` in the statement is not slack. -/
theorem minorBinders_not_closed_at_1 :
    ¬ VExpr.ClosedTele ((richBlock.minorBinders 0 richCtor).map (VExpr.instL [])) 1 := by
  rw [minorBinders_rich]
  simp [VExpr.ClosedTele, VExpr.ClosedN]

/-- …and the induction-hypothesis entry is tight at its own bound too: at `3` — which is
what `D.np + D.nm + q + nf` would be with the motive block forgotten — the `ξ`-shifted
`.bvar 3` escapes.  This is the entry `ProjClosed`'s three fields say nothing about. -/
theorem ihEntry_not_closed_at_3 :
    ¬ (VExpr.forallE (.bvar 3)
        (((VExpr.bvar 3).app (.bvar 0)).app ((VExpr.bvar 1).app (.bvar 0)))).ClosedN 3 := by
  simp [VExpr.ClosedN]


end Rich

end Lean4Lean
