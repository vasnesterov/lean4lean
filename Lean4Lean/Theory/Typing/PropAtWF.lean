import Lean4Lean.Theory.Typing.PropAgreeGuarded
import Lean4Lean.Theory.Typing.AppUniqWF
import Lean4Lean.Theory.Typing.PiInvVac

/-!
# `PropAgreeOn` at `VEnv.WF`: the `VEnv.WF` hypothesis contributes nothing

**The question this file answers.**  `Theory/Typing/PiInvWF.lean` leaves `proofIrrel` as the only
open refutation *route* into `VEnv.PiInv` at `VEnv.WF` (its author's word, and it is analysis, not
a theorem), and `Theory/Typing/PiInvVac.lean` kills that route's **entry** at every
`Ordered ∧ PropAgreeOn` environment, hole-free and with no `SortUniq`
(`not_forallEProofPair_of_propAgreeOn`).  That is a reduction, not a closure, because
`Ordered ∧ PropAgreeOn` has no hole-free inhabitant.  So: **is `env.PropAgreeOn U` derivable from
`VEnv.WF env` alone, hole-free?**

**Answer: no, and the obstruction is not where the corner has been looking.**  Two measurements,
both machine-checked below, and one search result that belongs with them.

## 1. A `VEnv.WF`-only derivation exists and is circular

Searching by *conclusion shape* rather than by name — `docs/handoff-propat-wf.md` §1 Q1 — turns up
`SetModel/NotProofNoModel.WF.propTypeAgreeOn`:

    theorem WF.propTypeAgreeOn (henv : env.WF) : env.PropTypeAgreeOnCtx nv

whose conclusion is `PropAgreeOn` under a third name (the three names `SortInvIndep.PropAgreeOn`,
`PropAgreeLift.PropAgreeUp` and `SetModel/PropSplitAudit.PropTypeAgreeOnCtx` are the same
statement; a source-level scan for every `Prop`-valued definition in the tree mentioning `OnCtx`,
`HasType` and `VLevel.eval` finds exactly those three, and no fourth).  It is a derivation from
`VEnv.WF` and nothing else, and its cone reaches `IsDefEqU.forallE_inv_stratified` — the hole the
whole corner exists to discharge — through `IsDefEq.uniqU` and `IsDefEqU.sort_inv`.  Its own
docstring says so.  So the `VEnv.WF`-only derivation is a **hole** derivation: it cannot close the
`proofIrrel` route without assuming what the route is being cleared for.

Nothing here imports that file (it would drag the model layer and the hole's cone into a
`Theory/Typing` leaf for no proof-theoretic gain); §1 of `docs/handoff-propat-wf.md` records the
measurement instead.

## 2. …and no hole-free `VEnv.WF`-only derivation can do better than the **empty** environment

This is the part that is proved here, and it is the transport of `Theory/Typing/AppUniqWF.lean`'s
instrument from the `app`-case family to `PropAgreeOn` itself, where nobody had run it:

* `PropAgreeOn.mono_env` — `PropAgreeOn` is **antitone** in the environment.  Its environment
  occurs only in its premises (the guard `OnCtx Γ (env.IsType U)` included, which is *monotone*
  by `IsType.mono` and so travels the same way), and its conclusion is a statement about two
  levels.  Hence the *larger* environment's statement is the *stronger* one.
* `PropAgreeOn.mono_univs` — antitone in the universe count too, by `IsDefEq.mono_uvars` and
  `VLevel.WF.mono`.  So `U = 0` is the **weakest** member of that chain, which is exactly what the
  hole-free producer `PropAgreeGuarded.propAgreeOn_of_stratifiedNOn` delivers (`PropAgreeOn env 0`,
  `U` fixed at `0` — a limit the reduction chain's relay does not carry).
* `propAgreeOn_wf_lower` and `no_wf_hypothesis_avoids_empty_propAgreeOn` — since `∅` is `VEnv.WF`
  (`AppUniqWF.wf_emptyEnv`), **every** consequence of `VEnv.WF` holds at `∅`, so any proof schema
  `H env → PropAgreeOn env U` with `H` implied by `VEnv.WF` proves `PropAgreeOn (∅ : VEnv) U` as a
  special case.  `VEnv.WF`'s δ-rule structure — one rule per constant, `IsDeclRule.lhs_shape`, the
  large-elimination guard, even total rule-freeness — is therefore unable to lift this goal above
  the empty-environment clause.  It is the same obstruction `AppUniqWF.no_wf_hypothesis_avoids_empty`
  records one level down, and it applies here for the same reason.

**Grading, up front, as this corner requires: the bound is one-way.**  `PropAgreeOn (∅ : VEnv) U`
is a *necessary* condition for the `VEnv.WF`-quantified target and possibly strictly weaker.
Refuting it refutes the target everywhere (`propAgreeOn_empty_false_imp`); *proving* it proves
nothing about any larger environment.  Nothing here discharges anything.

## 3. What that leaves, and it is the sharpest form of the entry-kill available

At `∅` the `Ordered` half of `PiInvVac`'s hypothesis is **free** (`PiInvVac.empty_ordered`), so the
`proofIrrel` entry-kill at the bottom of both chains needs exactly one open statement, the weakest
member of the `PropAgreeOn` family in both coordinates: `PropAgreeOn (∅ : VEnv) 0`
(`forallEProofPair_empty_dies_of_weakest`).  That is the hypothesis a future round should attack,
and naming it is this round's contribution to method rule 3.

**And the limit of even a full success, which must be said rather than implied**: closing the entry
is not closing the route.  `PiInvVac.propAgreeOn_trivial_at_sort_types` shows `PropAgreeOn`'s
conclusion is *trivially true* whenever both types compared are sorts — both propositionhood bits
are `false` — which is precisely the exit residual `SortZeroOneConv`'s configuration.  So
`PropAgreeOn`, at any environment and any `U`, cannot kill the exit residual, and `PiInv` at
`VEnv.WF` would remain un-refuted rather than proved.
-/

namespace Lean4Lean
namespace VEnv

variable {env : VEnv} {U : Nat}

/-! ## §1 `PropAgreeOn` is antitone in the environment -/

/-- **`PropAgreeOn` is antitone in the environment.**  Every occurrence of `env` is in a premise:
the guard `OnCtx Γ (env.IsType U)` is monotone (`IsType.mono`), and the four typing premises climb
by `HasType.mono`; the conclusion mentions no environment at all.  So a larger environment states a
*stronger* fact, and the statement descends along `env ≤ env'`.

The analogue of `AppUniqWF.PropUniqNOn.mono_env` for the unstratified, guarded statement — the one
member of this family for which it had not been recorded. -/
theorem PropAgreeOn.mono_env {env env' : VEnv} (le : env ≤ env') (h : PropAgreeOn env' U) :
    PropAgreeOn env U := by
  intro Γ e A A' u u' ls hΓ hu hu' he he' hA hA'
  exact h (hΓ.mono fun ht => ht.mono le) hu hu'
    (he.mono le) (he'.mono le) (hA.mono le) (hA'.mono le)

/-- **The bound.**  `∅ ≤ env` always (`AppUniqWF.emptyEnv_le`), so the empty environment's clause
is implied by every other one. -/
theorem propAgreeOn_le (h : PropAgreeOn env U) : PropAgreeOn (∅ : VEnv) U :=
  PropAgreeOn.mono_env emptyEnv_le h

/-- **Antitone in the universe count as well**, by `IsDefEq.mono_uvars` and `VLevel.WF.mono`.  So
`PropAgreeOn env 0` is the weakest member of the `U`-chain, and the hole-free producer
`propAgreeOn_of_stratifiedNOn` — whose conclusion is fixed at `U = 0` — produces exactly that
weakest member.  Stated so that the `U = 0` restriction is a theorem about position in a chain
rather than a remark. -/
theorem PropAgreeOn.mono_univs {U U' : Nat} (le : U ≤ U') (h : PropAgreeOn env U') :
    PropAgreeOn env U := by
  intro Γ e A A' u u' ls hΓ hu hu' he he' hA hA'
  exact h (hΓ.mono fun ⟨w, hw⟩ => ⟨w, hw.mono_uvars le⟩) (hu.mono le) (hu'.mono le)
    (he.mono_uvars le) (he'.mono_uvars le) (hA.mono_uvars le) (hA'.mono_uvars le)

/-- Both coordinates at once: the bottom of the whole family is `PropAgreeOn ∅ 0`. -/
theorem propAgreeOn_bottom (h : PropAgreeOn env U) : PropAgreeOn (∅ : VEnv) 0 :=
  PropAgreeOn.mono_univs (Nat.zero_le U) (propAgreeOn_le h)

/-! ## §2 `∅` is `VEnv.WF`, so `VEnv.WF` cannot lift the goal -/

/-- **The `VEnv.WF`-quantified target implies the empty-environment clause.**  `∅` is `WF`
(`AppUniqWF.wf_emptyEnv`), so this needs no bound at all. -/
theorem propAgreeOn_wf_lower (h : ∀ env : VEnv, env.WF → PropAgreeOn env U) :
    PropAgreeOn (∅ : VEnv) U := h _ wf_emptyEnv

/-- **The general obstruction.**  Any proof schema `H env → PropAgreeOn env U` whose hypothesis `H`
is implied by `VEnv.WF` proves `PropAgreeOn (∅ : VEnv) U` as a special case — because `∅` is `WF`
and therefore satisfies every consequence of `WF`, in the strongest available form (it has no
constants and no δ-rules at all).

This is `AppUniqWF.no_wf_hypothesis_avoids_empty` for `PropAgreeOn`, and it is the answer to the
question this file is named for: **the `VEnv.WF` hypothesis contributes nothing to this target.** -/
theorem no_wf_hypothesis_avoids_empty_propAgreeOn {H : VEnv → Prop}
    (hH : ∀ env : VEnv, env.WF → H env) (h : ∀ env : VEnv, H env → PropAgreeOn env U) :
    PropAgreeOn (∅ : VEnv) U := h _ (hH _ wf_emptyEnv)

/-- Spelled out for the two constraints on `env.defeqs` that `VEnv.WF` actually supplies and that
`PiInvWF` §2 turns on — `IsDeclRule.lhs_shape`, and the strictly stronger total rule-freeness.
Neither can lift the goal, for the same reason: `∅` satisfies both. -/
theorem lhs_shape_not_enough_propAgreeOn
    (h : ∀ env : VEnv, (∀ df : VDefEq, env.defeqs df →
        (∃ c ls, df.lhs = .const c ls) ∨ (∃ f a, df.lhs = .app f a) ∨
          ∃ A b, df.lhs = .lam A b) →
      PropAgreeOn env U) : PropAgreeOn (∅ : VEnv) U :=
  h _ fun _ hdf => (emptyEnv_no_defeqs hdf).elim

theorem rule_freeness_not_enough_propAgreeOn
    (h : ∀ env : VEnv, (∀ df : VDefEq, ¬ env.defeqs df) → PropAgreeOn env U) :
    PropAgreeOn (∅ : VEnv) U := h _ fun _ => emptyEnv_no_defeqs

/-- **The negative transfers the other way, and that is the strong half.**  A refutation of
`PropAgreeOn` at `∅` refutes it at **every** environment, `VEnv.WF` ones included.  No such
refutation exists in the tree; this records where one would have to be aimed. -/
theorem propAgreeOn_empty_false_imp (h : ¬ PropAgreeOn (∅ : VEnv) U) :
    ∀ env : VEnv, ¬ PropAgreeOn env U := fun _ h' => h (propAgreeOn_le h')

/-! ## §3 The chain, at the bottom, with the `Ordered` half free -/

/-- The hole-free producer at `∅`: `Ordered` costs nothing there (`PiInvVac.empty_ordered`), so the
chain's whole price at the bottom is its two `∀ n` stratified hypotheses. -/
theorem propAgreeOn_empty_of_stratifiedNOn
    (pta : ∀ n, PropTypeAgreeNOn (∅ : VEnv) 0 n) (pun : ∀ n, PropUniqNOn (∅ : VEnv) 0 n) :
    PropAgreeOn (∅ : VEnv) 0 :=
  propAgreeOn_of_stratifiedNOn empty_ordered pta pun

/-- …and the second of those two hypotheses is itself antitone
(`AppUniqWF.propUniqNOn_le`), so a `VEnv.WF`-quantified supply of it also collapses onto `∅`.
The *first* one does **not** descend by the same argument: `PropTypeAgreeNOn`'s conclusion is
`IsPropN env U n Γ A'`, which mentions `env` in a *conclusion*, so the antitone argument does not
apply to it and its direction is unmeasured here. -/
theorem propUniqNOn_all_wf_lower (h : ∀ env : VEnv, env.WF → ∀ n, PropUniqNOn env 0 n) :
    ∀ n, PropUniqNOn (∅ : VEnv) 0 n := fun n => propUniqNOn_le (h _ wf_emptyEnv n)

/-- **The sharpest form of `PiInvVac`'s entry-kill: one open hypothesis, the weakest in the whole
family.**  `PiInvVac.proofIrrel_route_entry_closed_of_propAgreeOn` needs `Ordered env` and
`PropAgreeOn env U`; at `∅` the first is free and, by §1, the second is at the bottom of both
chains.  So the `proofIrrel` route's entry at `∅` dies from `PropAgreeOn ∅ 0` alone.

This is the hypothesis the next round should attack, and by `propAgreeOn_bottom` **any**
`PropAgreeOn` instance anywhere in the class supplies it. -/
theorem forallEProofPair_empty_dies_of_weakest (hT : PropAgreeOn (∅ : VEnv) 0) :
    (¬ ForallEProofPair (∅ : VEnv) 0) ∧ (¬ SortZeroConvProp (∅ : VEnv) 0) :=
  proofIrrel_route_entry_closed_of_propAgreeOn empty_ordered hT

/-- The same kill, driven by a `VEnv.WF`-quantified derivation should one ever be found hole-free:
it factors through the empty-environment clause, i.e. through §2's bound. -/
theorem forallEProofPair_empty_dies_of_wf_route
    (h : ∀ env : VEnv, env.WF → PropAgreeOn env 0) :
    (¬ ForallEProofPair (∅ : VEnv) 0) ∧ (¬ SortZeroConvProp (∅ : VEnv) 0) :=
  forallEProofPair_empty_dies_of_weakest (propAgreeOn_wf_lower h)

section Audit
#print axioms Lean4Lean.VEnv.PropAgreeOn.mono_env
#print axioms Lean4Lean.VEnv.propAgreeOn_le
#print axioms Lean4Lean.VEnv.PropAgreeOn.mono_univs
#print axioms Lean4Lean.VEnv.propAgreeOn_bottom
#print axioms Lean4Lean.VEnv.propAgreeOn_wf_lower
#print axioms Lean4Lean.VEnv.no_wf_hypothesis_avoids_empty_propAgreeOn
#print axioms Lean4Lean.VEnv.lhs_shape_not_enough_propAgreeOn
#print axioms Lean4Lean.VEnv.rule_freeness_not_enough_propAgreeOn
#print axioms Lean4Lean.VEnv.propAgreeOn_empty_false_imp
#print axioms Lean4Lean.VEnv.propAgreeOn_empty_of_stratifiedNOn
#print axioms Lean4Lean.VEnv.propUniqNOn_all_wf_lower
#print axioms Lean4Lean.VEnv.forallEProofPair_empty_dies_of_weakest
#print axioms Lean4Lean.VEnv.forallEProofPair_empty_dies_of_wf_route
end Audit

end VEnv
end Lean4Lean
