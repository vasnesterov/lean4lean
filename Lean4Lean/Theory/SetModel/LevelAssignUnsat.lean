import Lean4Lean.Theory.SetModel.InterpSubst

/-!
# Two unsatisfiable structures in the model tower

Both were found by the same test: **a structure whose producers all consume the
same structure has never had its fields tested.**  The first was found by a
tree-wide audit, the second by applying that criterion to its neighbours.

## 1. `LevelAssign` was unsatisfiable as stated

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

/-! ## 2. `LevelAssign.Stable` is unsatisfiable — and this one is *not* repaired

Same family, same cause: a relation that fails to constrain something its
consumers assume is constrained.

`Ctx.InstN` is declared with `Γ₀ e₀ A₀` as **parameters**, and its `zero`
constructor is `Ctx.InstN 0 (A₀ :: Γ₀) Γ₀` — `e₀` does not appear. So
`Ctx.InstN Γ₀ e₀ A₀ 0 (A₀ :: Γ₀) Γ₀` holds for *every* `e₀`, with no requirement
that `e₀` have type `A₀`, or any type at all.

`Stable.lvl_instN` then demands, for every `e₀` and every `A₀`,

```
L.lvl Γ₀ ((VExpr.bvar 0).inst e₀ 0) ≈ L.lvl (A₀ :: Γ₀) (.bvar 0)
```

whose left side does not mention `A₀` while the right side is pinned by
`lvl_sound` to `A₀`'s own level.  Taking `A₀ := .sort .zero` and
`A₀ := .sort (.succ .zero)` with the same `e₀` forces `.zero ≈ .succ .zero`.

**Consequence: every theorem taking `L.Stable` as a hypothesis is currently
vacuous**, including `soundAbove` and everything downstream of it.

**The repair** is the same shape as the first: add the hypothesis the consumers
already have, namely that the substituted term is well-typed at the type it
replaces —

```
lvl_instN : … → env.HasType nv Γ₀ e₀ A₀ → ∀ B, L.lvl Γ (B.inst e₀ k) ≈ L.lvl Γ₁ B
```

and likewise for `srt_instN`.  With it the counterexample dies, because a single
`e₀` cannot have both `.sort .zero` and `.sort (.succ .zero)` as its type.  The
`liftN` fields need no repair: `Ctx.LiftN` constrains everything it mentions, and
weakening-invariance of the assignment is not in tension with `lvl_sound`. -/

theorem no_stable {env : VEnv} {nv : ℕ} (L : LevelAssign env nv) : ¬ L.Stable := by
  intro hS
  have h0 := hS.lvl_instN (Γ₀ := []) (e₀ := .sort .zero) (A₀ := .sort .zero)
    (k := 0) (Γ₁ := [VExpr.sort .zero]) (Γ := []) .zero (.bvar 0)
  have h1 := hS.lvl_instN (Γ₀ := []) (e₀ := .sort .zero) (A₀ := .sort (.succ .zero))
    (k := 0) (Γ₁ := [VExpr.sort (.succ .zero)]) (Γ := []) .zero (.bvar 0)
  have k0 : L.lvl [VExpr.sort .zero] (.bvar 0) ≈ VLevel.zero :=
    L.lvl_sound trivial (VEnv.IsDefEq.bvar .zero)
  have k1 : L.lvl [VExpr.sort (.succ .zero)] (.bvar 0) ≈ VLevel.succ .zero :=
    L.lvl_sound trivial (VEnv.IsDefEq.bvar .zero)
  have e0 := VLevel.equiv_def.1 h0 []
  have e1 := VLevel.equiv_def.1 h1 []
  have f0 := VLevel.equiv_def.1 k0 []
  have f1 := VLevel.equiv_def.1 k1 []
  simp [VLevel.eval] at f0 f1
  omega

end Lean4Lean.SetModel
