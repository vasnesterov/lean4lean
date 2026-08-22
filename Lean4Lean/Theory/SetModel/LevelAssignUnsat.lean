import Lean4Lean.Theory.SetModel.Interp

/-!
# `LevelAssign` is unsatisfiable as stated

A tree-wide audit observed that `SetModel.LevelAssign` has never been
constructed for any environment, and that every other model structure is
downstream of it. The narrow question was whether one could be built for a
small concrete environment — `VEnv.empty`, say — without `IsDefEqU.sort_inv`.

**The answer is no, and for a stronger reason than `sort_inv`: no `LevelAssign`
exists for *any* environment, at *any* parameter count.** Two of its fields
contradict each other.

## The contradiction

`lvl_wf` demands `(lvl Γ A).WF nv` — for every `Γ`, with no hypothesis that `Γ`
is well-formed. `lvl_sound` demands `lvl Γ A ≈ u` whenever
`env.HasType nv Γ A (.sort u)` — again with no hypothesis on `Γ`, and none on
`u`.

But `IsDefEq.bvar` has no side condition at all:

```
| bvar : Lookup Γ i A → Γ ⊢ .bvar i : A
```

so a context may contain `.sort (.param nv)` — a level that is *not* `WF nv` —
and then `Γ ⊢ .bvar 0 : .sort (.param nv)` is derivable. `lvl_sound` forces
`lvl Γ (.bvar 0) ≈ .param nv` while `lvl_wf` forces that same level to be
`WF nv`; and a `WF nv` level cannot be equivalent to `.param nv`, because its
evaluation depends only on the first `nv` entries of the valuation while
`.param nv` reads the `nv`-th.

Note this is *not* about `env`: the derivation uses no constant and no defeq, so
it goes through at `VEnv.empty` exactly as anywhere else. It is also not about
`nv = 0`; `no_levelAssign` below is stated for all `nv`.

## Status

**The repair below has been applied** (`SetModel/Interp.lean`).  So the
counterexample no longer applies to `LevelAssign` itself; to keep it checkable,
it is stated here against `LevelAssignUnguarded`, a local copy of the structure
with the *old* `lvl_sound`.  The two differ in exactly one hypothesis.

## The repair

Add the missing well-formedness hypothesis to `lvl_sound`:

```
lvl_sound : ∀ {Γ A u}, u.WF nv → env.HasType nv Γ A (.sort u) → lvl Γ A ≈ u
```

That blocks the counterexample and costs the consumers nothing, because the
soundness induction runs on `IsDefEqStrong`, whose every rule carries the
`u.WF uvars` side conditions explicitly (`appDF`, `lamDF`, `forallEDF`, … all
take `u.WF uvars → v.WF uvars → …`). The information is already threaded; the
structure simply failed to ask for it.

`srt_sound` needs no repair: it relates `srt Γ e` to `lvl Γ A`, both of which
`srt_wf`/`lvl_wf` already constrain to be `WF nv`, so there is no conflict.

**After the repair, satisfiability is exactly `sort_inv` for the environment** —
two well-formed sort-typings of the same term must have equivalent levels. That
is the honest answer to the audit's narrow question: even at `VEnv.empty` the
obligations are not vacuous, because `sortDF`, `bvar`, `forallEDF`, `lamDF`,
`appDF`, `beta`, `eta` and `defeqDF` all fire without any constants. The
existing `LevelAssign.lvl_uniq` proves the converse implication in one line, so
the two are equivalent rather than merely related.
-/

namespace Lean4Lean.SetModel

/-- `LevelAssign` as it was stated before the repair: `lvl_sound` with no
well-formedness hypothesis on `u`.  Kept so the counterexample stays
machine-checked. -/
structure LevelAssignUnguarded (env : VEnv) (nv : ℕ) where
  lvl : List VExpr → VExpr → VLevel
  lvl_wf : ∀ Γ A, (lvl Γ A).WF nv
  lvl_sound : ∀ {Γ : List VExpr} {A : VExpr} {u : VLevel},
    env.HasType nv Γ A (.sort u) → lvl Γ A ≈ u

/-- A level well-formed at `n` parameters only reads the first `n` entries of a
valuation. -/
theorem eval_eq_of_wf : ∀ {l : VLevel} {n : ℕ}, l.WF n → ∀ ls ls' : List ℕ,
    (∀ i, i < n → ls.getD i 0 = ls'.getD i 0) → l.eval ls = l.eval ls'
  | .zero, _, _, _, _, _ => rfl
  | .succ l, _, h, ls, ls', hag => congrArg (· + 1) (eval_eq_of_wf (l := l) h ls ls' hag)
  | .max a b, _, ⟨h1, h2⟩, ls, ls', hag => by
      simp only [VLevel.eval, eval_eq_of_wf (l := a) h1 ls ls' hag,
        eval_eq_of_wf (l := b) h2 ls ls' hag]
  | .imax a b, _, ⟨h1, h2⟩, ls, ls', hag => by
      simp only [VLevel.eval, eval_eq_of_wf (l := a) h1 ls ls' hag,
        eval_eq_of_wf (l := b) h2 ls ls' hag]
  | .param i, _, h, _, _, hag => hag i h

/-- **No `LevelAssign` exists**, for any environment and any parameter count.
`lvl_wf` and `lvl_sound` contradict each other at a context holding an
out-of-range universe parameter. -/
theorem no_levelAssign (env : VEnv) (nv : ℕ) : IsEmpty (LevelAssignUnguarded env nv) := by
  constructor
  intro L
  -- a context whose single entry is `Sort (param nv)` — not `WF nv`
  have h : env.HasType nv [VExpr.sort (.param nv)] (.bvar 0) (.sort (.param nv)) :=
    VEnv.IsDefEq.bvar .zero
  have hs := VLevel.equiv_def.1 (L.lvl_sound h)
  have hw := L.lvl_wf [VExpr.sort (.param nv)] (.bvar 0)
  -- two valuations agreeing below `nv` but differing at `nv`
  have hag : ∀ i, i < nv → (List.replicate nv 0).getD i 0
      = (List.replicate nv 0 ++ [1]).getD i 0 := by
    intro i hi
    have hlen : i < (List.replicate nv (0 : ℕ)).length := by simpa using hi
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hlen]
  have key := eval_eq_of_wf hw _ _ hag
  have e0 := hs (List.replicate nv 0)
  have e1 := hs (List.replicate nv 0 ++ [1])
  rw [key] at e0
  rw [e1] at e0
  simp [VLevel.eval, List.getD_eq_getElem?_getD] at e0

end Lean4Lean.SetModel
