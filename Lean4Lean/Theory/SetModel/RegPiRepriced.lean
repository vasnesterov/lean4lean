import Lean4Lean.Theory.Typing.AppUniqRefute
import Lean4Lean.Theory.Typing.RegPiSat
import Lean4Lean.Theory.SetModel.PreludeWitness

/-!
# The `RegPiOn` re-pricing, graded

`docs/vacuity-ledger.md` row 144b records that `RegPi` is **false at every environment**
(`VEnv.regPi_false`), that `Theory/Typing/RegPiSat.lean` "already holds the repair
(`RegPiOn`/`Regular`)", and names `propTypeAgree_appCase_on_of` as the re-pricing target.

**The re-pricing is already done in HEAD**, sorry-free: `propTypeAgree_appCase_on_of`,
`propTypeAgree_on_of`, `propTypeAgreeOn_of_residuals`.  So nothing was owed there.  What was
never established is the *grading* — what the guarded form buys — and that is this file.

## The verdict, in one line

**Merely differently conditional.**  The repair removes an *unconditional* falsity and puts in
its place a bundle that (a) is refuted at an `Ordered` environment at the smallest index where
its consumer is even stated, and (b) has **no non-degenerate positive instance anywhere in the
tree** — the one positive control that exists lands at an index where the conclusion is a
hypothesis-free theorem.

Three graded statements, each machine-checked below.

### 1. What the repair genuinely removes

`RegPi` is false at *every* environment, so it is false at the environments the constant
recursion actually visits.  `regPi_false_at_preludeEnv` says so at `preludeEnv` — a `VEnv.WF`
environment built by `PreludeWitness.lean` from `leanPrelude.reverse` with no
`VDecl.unsafeDef` — which is the form the vacuity claim has to take to be worth anything: "at
every environment" is only interesting once one of those environments is named and known
reachable.  So the pre-repair assembly was vacuous **on the path**, not merely in principle.

That is a real gain and it is unambiguous: after the repair no hypothesis of
`propTypeAgreeOn_of_residuals` is refuted at every environment.

### 2. What it does *not* remove: the bundle is still refuted at `Ordered`

`propTypeAgreeOn_of_residuals` takes five hypotheses at index `k+1`, and one of them —
`PropUniqN` — is refuted at `piLvlEnv`, `Theory/Typing/AppUniqRefute.lean`'s `Ordered`
environment, at `n = 1`, i.e. at the **smallest index the theorem is stated at**.
`RepricedInput` bundles the five and `not_repricedInput_piLvlEnv` refutes the bundle.

So the shape of the vacuity changed rather than disappeared: from "vacuous at every
environment, for a reason internal to one hypothesis" to "vacuous at an exhibited `Ordered`
environment, for a reason `IsDeclRule.lhs_ne_forallE` excludes at `VEnv.WF`".  The second is
strictly better — `piLvlEnv` is provably not `WF` (`piLvlEnv_not_wf`) — but it is not the same
as non-vacuous, and the distinction is exactly the one row 144b's "hole-free ≠ discharged"
column is for.

### 3. The one positive control is degenerate — and this is the finding

`RegPiSat.lean` §4 offers `propTypeAgreeOn_zero_from_residuals : propLoopEnv.PropTypeAgreeOnN U 0`
as the non-vacuity replay of the repaired chain.  **Its conclusion is free**:
`PropTypeAgreeOnN.zero` proves `env.PropTypeAgreeOnN U 0` for *every* environment with no
hypotheses at all (`HasTypeN.uniq_zero`), and `regPiOn_zero_needs_no_conversion` shows the same
of the `RegConvE` input, whose index-0 instance holds only because `IsDefEqN U 0` **is**
syntactic equality.  So the replay demonstrates that the hypotheses are satisfiable at an index
where the conclusion needs none of them, which is no evidence about the indices where the
theorem is stated.  `zero_replay_is_free` records this as a theorem rather than as prose.

`RegPiSat.lean` says as much about its consumers — "the three that cannot be fired at index
`0`" — and is right that `SortInvN env U 1` is what blocks the replay.  What it does not say is
that the *positive* control it does offer proves nothing, and that is the half a reader takes
away as reassurance.

### 4. Net

| | before the repair | after |
|---|---|---|
| a hypothesis false at **every** environment | `RegPi` (`regPi_false`) | none |
| the bundle refuted at some `Ordered` env, at the least stated index | yes (a fortiori) | **yes**, `not_repricedInput_piLvlEnv` |
| the bundle refuted at some `VEnv.WF` env | yes (a fortiori) | **not known** |
| a non-degenerate positive instance | none | **none** |

Rows 2 and 4 are the ones that decide whether an assembly is worth funding, and the repair
moves neither.  It moves row 1, which is what makes it worth having, and row 3, which is what
makes it worth *continuing*.

`Above` does not occur in this file and no `κ` is chosen; nothing here is a model-side
statement.  Axioms: `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace Lean4Lean
namespace SetModel
namespace RegPiAudit

open Lean4Lean.VEnv

/-! ## 1. The pre-repair falsity, at an environment the recursion visits -/

/-- `RegPi` is false at `preludeEnv` — a `VEnv.WF` environment reached by
`PreludeWitness.preludeEnv_history` with no `VDecl.unsafeDef` step.  This is `regPi_false`
instantiated; the point is that the environment is named and reachable, so the pre-repair
assembly was vacuous *on the path* rather than at a hypothetical environment. -/
theorem regPi_false_at_preludeEnv {U n : Nat} : ¬ preludeEnv.RegPi U n := regPi_false

/-- …and `preludeEnv` really is well formed, so the previous statement is not about a junk
environment. -/
theorem preludeEnv_is_wf : preludeEnv.WF := preludeEnv_WF

/-! ## 2. The repaired bundle, and its refutation at an `Ordered` environment -/

/-- The five hypotheses of `propTypeAgreeOn_of_residuals`, bundled.  Stated at `k+1` because
that is the only shape the theorem has. -/
def RepricedInput (env : VEnv) (U k : Nat) : Prop :=
  env.SortInvN U (k+1) ∧ env.Regular U (k+1) ∧ env.InstLvl U (k+1) ∧
    env.PropUniqN U (k+1) ∧ env.PropConvInv U (k+1)

/-- The bundle is what the re-priced assembly consumes: nothing is dropped or added. -/
theorem propTypeAgreeOnN_of_repricedInput {env : VEnv} {U k : Nat}
    (h : RepricedInput env U k) : env.PropTypeAgreeOnN U (k+1) :=
  propTypeAgreeOn_of_residuals h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

/-- **The repaired bundle is refuted at an `Ordered` environment, at the smallest index its
consumer is stated at.**  The offending member is `PropUniqN`, by
`AppUniqRefute.piLvlEnv_propUniqN_false`; the other four are not examined, so this is a
refutation of the bundle and not a claim about any individual member. -/
theorem not_repricedInput_piLvlEnv : ¬ RepricedInput piLvlEnv 0 0 :=
  fun h => piLvlEnv_propUniqN_false h.2.2.2.1

/-- The witness environment is `Ordered`… -/
theorem piLvlEnv_is_ordered : Ordered piLvlEnv := piLvlEnv_ordered

/-- …and provably **not** `VEnv.WF`, which is exactly why the refutation does not settle the
real target.  `IsDeclRule.lhs_ne_forallE` excludes the rogue rule at `VEnv.WF`. -/
theorem piLvlEnv_is_not_wf : ¬ piLvlEnv.WF := piLvlEnv_not_wf

/-- So `Ordered` is not enough for the repaired bundle either — the same verdict
`AppUniqRefute` reaches for route B's inputs, transported to this bundle. -/
theorem ordered_not_enough_for_repricedInput :
    ¬ ∀ (env : VEnv), Ordered env → ∀ k, RepricedInput env 0 k :=
  fun h => not_repricedInput_piLvlEnv (h _ piLvlEnv_ordered 0)

/-! ## 3. The positive control is degenerate

`propTypeAgreeOn_zero_from_residuals` is the only replay of the repaired chain in the tree.
It is at index `0`, and at index `0` the conclusion holds with no hypotheses. -/

/-- The conclusion of the index-`0` replay, with **no** hypotheses and at **every**
environment.  This is `PropTypeAgreeOnN.zero`; naming it here is the point. -/
theorem propTypeAgreeOnN_zero_free (env : VEnv) (U : Nat) : env.PropTypeAgreeOnN U 0 :=
  PropTypeAgreeOnN.zero

/-- **The index-`0` replay proves nothing.**  Its conclusion is implied by the trivial theorem
above, so the fact that its five hypotheses are satisfiable at index `0` is not evidence that
the bundle is satisfiable anywhere the consumer is stated. -/
theorem zero_replay_is_free :
    (∀ (U : Nat), propLoopEnv.PropTypeAgreeOnN U 0) ∧
      (∀ (env : VEnv) (U : Nat), env.PropTypeAgreeOnN U 0) :=
  ⟨fun _ => propTypeAgreeOn_zero_from_residuals, fun env U => propTypeAgreeOnN_zero_free env U⟩

/-- And the reason the `Regular` input is available at index `0` is that `IsDefEqN U 0` is
syntactic equality, so `RegConvE` has no content there: `RegConvE.zero`'s whole proof is a
rewrite along `IsDefEqN.zero_iff`.  Stated as the equivalence, so the collapse is visible. -/
theorem regConvE_zero_is_syntactic {env : VEnv} {U : Nat} {Γ : List VExpr} {A A' : VExpr} :
    env.IsDefEqN U 0 Γ A A' ↔ A = A' := IsDefEqN.zero_iff

/-- The `RegConvE` input at index `0`, exhibited as free at every environment — the companion
of `propTypeAgreeOnN_zero_free` on the hypothesis side. -/
theorem regConvE_zero_free (env : VEnv) (U : Nat) : env.RegConvE U 0 := RegConvE.zero

/-! ## 4. What is left, stated so it is not mistaken for discharged

The bundle's own residuals at `k+1`, in the order they block a replay:

* `SortInvN env U 1` — `RegPiSat.lean` §4 names this as the blocker and reduces it, over `∅`,
  to `SortRedAppDF ∅ 1 0` (`SortClauses.empty_sortInvN_one_of_appDF`).  Open.
* `RegConvE env U (k+1)` — the input `Regular` needs beyond `EnvReg` and `InstLvl`.  Free at
  index `0` for the degenerate reason above; **no instance at any `k+1` exists in the tree.**
  This is the member the re-pricing newly depends on, and it has never been graded.
* `PropUniqN env U (k+1)` — refuted at `Ordered` (§2), open at `VEnv.WF`.
* `PropConvInv env U (k+1)` — open; its `extra` case is `RegPiSat.lean` §4's residual.

None of these is proved here and none is claimed.  In particular
**`regularAtSucc_open` is a statement, not a theorem**: it says what would have to be produced,
and it is `def`-shaped so that no reader can mistake an axiom print for a discharge. -/

/-- The missing datum, written as a statement so it can be quoted rather than described:
`Regular` at a *stated* index, at any environment at all.  Nothing in the tree inhabits this. -/
def RegularAtSucc : Prop :=
  ∃ (env : VEnv) (U k : Nat), env.Regular U (k+1)

/-- What would suffice for it, by `regular_of`: the two index-`(k+1)` inputs, since `EnvReg`
is free for a `ConstPropType` environment at every index (`EnvReg.of_constPropType`). -/
theorem regularAtSucc_of {env : VEnv} {U k : Nat} (henv : Ordered env)
    (hcp : ConstPropType env) (hinst : env.InstLvl U (k+1)) (hrc : env.RegConvE U (k+1)) :
    env.Regular U (k+1) :=
  regular_of henv (EnvReg.of_constPropType hcp) hinst hrc

end RegPiAudit
end SetModel
end Lean4Lean
