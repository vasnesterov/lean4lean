import Lean4Lean.Theory.Typing.Env

/-!
# Each constant name carries at most one δ-rule

`VEnv.Params.pat_uniq` concludes `r ≍ r'` whenever two registered patterns intersect.  For a
δ-rule that forces the rule's *value* to be determined by its head constant — and
`env.defeqs` alone does not give that, because it is a bare predicate with no memory of which
declaration produced a rule.  What does give it is `VEnv.WF`'s declaration history: `addConst`
rejects duplicates, so a second δ-rule for a name already carrying one is impossible.

This is a deliberately *minimal* slice of what a `VEnv.Sig` (design §7.7, ledger I1) would
provide.  It says nothing about inductive blocks and nothing about which declaration a rule
came from; only that a bare-`const`-headed rule is unique to its head.

## Why the invariant is a conjunction

The induction does not go through on uniqueness alone.  In the `.def` step the new rule's
head is `ci.name` and `env.addConst ci.name … = some env'` gives `env.constants ci.name =
none`; to contradict an *existing* rule with that head one needs to know that every rule's
head is already declared.  So the induction runs on

* `DefEqHeadsDeclared` — every bare-`const`-headed rule's head is a declared constant, and
* `DefEqHeadsUnique` — at most one such rule per head,

together.  Neither is provable without the other.

## Why "bare `const`" rather than "all rules"

Only `.def` and `.unsafeDef` contribute rules whose left-hand side is a bare constant.  A
`quot` rule is `fun α r β f c a => …`, a **lam**; an ι-rule is `mkLams Γ' (iotaLhs …)`, a lam
when `Γ'` is non-empty and otherwise an application, since `iotaLhs` always carries at least
the major premise.  Restricting the statement to bare-`const` heads is what keeps those two
cases to a shape computation instead of an argument about their contents.
-/

namespace Lean4Lean
namespace VEnv

/-- `df` is a δ-rule with head `c`: its left-hand side is a bare constant. -/
def IsDeltaRule (df : VDefEq) (c : Lean.Name) : Prop := ∃ ls, df.lhs = .const c ls

theorem IsDeltaRule.const {c ls} : IsDeltaRule ⟨u, .const c ls, v, t⟩ c := ⟨ls, rfl⟩

/-- Every δ-rule's head is a declared constant. -/
def DefEqHeadsDeclared (env : VEnv) : Prop :=
  ∀ df c, env.defeqs df → IsDeltaRule df c → env.contains c

/-- At most one δ-rule per head. -/
def DefEqHeadsUnique (env : VEnv) : Prop :=
  ∀ df df' c, env.defeqs df → env.defeqs df' → IsDeltaRule df c → IsDeltaRule df' c → df = df'

/-! ## How the two primitive operations move the invariants -/

theorem addConst_defeqs {env env' : VEnv} {n ci} (h : env.addConst n ci = some env') :
    env'.defeqs = env.defeqs := by
  unfold VEnv.addConst at h; split at h <;> cases h; rfl

theorem addConst_contains {env env' : VEnv} {n ci} (h : env.addConst n ci = some env')
    {c} (hc : env.contains c) : env'.contains c := by
  obtain ⟨ci', hci'⟩ := hc
  exact ⟨_, (addConst_le h).constants hci'⟩

@[simp] theorem addDefEq_constants (env : VEnv) (df : VDefEq) :
    (env.addDefEq df).constants = env.constants := rfl

theorem addDefEq_defeqs (env : VEnv) (df x : VDefEq) :
    (env.addDefEq df).defeqs x ↔ x = df ∨ env.defeqs x := Iff.rfl

/-- Adding a constant preserves both invariants: the rules are untouched and the constants
only grow. -/
theorem DefEqHeadsDeclared.addConst {env env' : VEnv} {n ci}
    (h : env.addConst n ci = some env') (H : env.DefEqHeadsDeclared) :
    env'.DefEqHeadsDeclared := by
  intro df c hdf hd
  rw [addConst_defeqs h] at hdf
  exact addConst_contains h (H df c hdf hd)

theorem DefEqHeadsUnique.addConst {env env' : VEnv} {n ci}
    (h : env.addConst n ci = some env') (H : env.DefEqHeadsUnique) :
    env'.DefEqHeadsUnique := by
  intro df df' c hdf hdf' hd hd'
  rw [addConst_defeqs h] at hdf hdf'
  exact H df df' c hdf hdf' hd hd'

/-- Adding a rule whose head is *not* a bare constant leaves both invariants alone.  This is
the `quot` and `induct` case. -/
theorem DefEqHeadsDeclared.addDefEq_notDelta {env : VEnv} {df : VDefEq}
    (H : env.DefEqHeadsDeclared) (hnd : ∀ c, ¬ IsDeltaRule df c) :
    (env.addDefEq df).DefEqHeadsDeclared := by
  rintro x c (rfl | hx) hd
  · exact absurd hd (hnd c)
  · exact H x c hx hd

theorem DefEqHeadsUnique.addDefEq_notDelta {env : VEnv} {df : VDefEq}
    (H : env.DefEqHeadsUnique) (hnd : ∀ c, ¬ IsDeltaRule df c) :
    (env.addDefEq df).DefEqHeadsUnique := by
  rintro x y c (rfl | hx) (rfl | hy) hd hd'
  · rfl
  · exact absurd hd (hnd c)
  · exact absurd hd' (hnd c)
  · exact H x y c hx hy hd hd'

/-- **The load-bearing step.**  Adding a δ-rule whose head is *fresh* — not yet a declared
constant — preserves uniqueness, precisely because `DefEqHeadsDeclared` rules out an existing
rule with that head.  This is where the two invariants need each other. -/
theorem DefEqHeadsUnique.addDefEq_fresh {env : VEnv} {df : VDefEq}
    (Hd : env.DefEqHeadsDeclared) (Hu : env.DefEqHeadsUnique)
    (hfresh : ∀ c, IsDeltaRule df c → ¬ env.contains c) :
    (env.addDefEq df).DefEqHeadsUnique := by
  rintro x y c (rfl | hx) (rfl | hy) hd hd'
  · rfl
  · exact absurd (Hd y c hy hd') (hfresh c hd)
  · exact absurd (Hd x c hx hd) (hfresh c hd')
  · exact Hu x y c hx hy hd hd'

/-- …and preserves declaredness, provided the head has just been declared. -/
theorem DefEqHeadsDeclared.addDefEq_declared {env : VEnv} {df : VDefEq}
    (H : env.DefEqHeadsDeclared) (hnew : ∀ c, IsDeltaRule df c → env.contains c) :
    (env.addDefEq df).DefEqHeadsDeclared := by
  rintro x c (rfl | hx) hd
  · exact hnew c hd
  · exact H x c hx hd

end VEnv
end Lean4Lean
