import Lean4Lean.Theory.Typing.AppCase
import Lean4Lean.Theory.Typing.SortClauses
import Lean4Lean.Theory.Typing.SortInvIndep

/-!
# `∀ n, PropTypeAgreeN env 0 n` and `∀ n, PropUniqN env 0 n`: what they actually cost

These two are `SetModel/PropAgreeWall.propTypeAgreeOnCtx_of_stratifiedN`'s hypotheses, and
`docs/vacuity-ledger.md` row 136d makes them "the model corner's entire remaining syntactic
import".  This file measures what discharging them needs.  Four results, and one of them
corrects a claim that has been driving the funding of this corner.

## 1. `SortForallEDisjoint` is NOT the missing primitive on the live route

`Theory/Typing/UniqueTypingN.lean`'s audit of `PropTypeAgreeN` names its `eta` case's residual
as `SortForallEDisjoint` and concludes "the primitive to route or fund is
`SortForallEDisjoint`".  **That audit is about a route that has since been replaced.**  It
inducts on the *conversion* judgment, where `eta` is a case.  `Theory/Typing/PropConv.lean`'s
`propTypeAgree_of` inducts on the **typing** judgment, where `eta` — like `trans`, `beta`,
`proofIrrel` and `extra` — is `nomatch hb`: there is no `eta` case at all.  Its residuals are
`SortInvN`, `PropConvInv` and `PropTypeAgreeN.AppCase`, and `SortForallEDisjoint` occurs in
none of them.  `propTypeAgree_appCase_of` then prices the `AppCase` at
`SortInvN ∧ RegPi ∧ InstLvl ∧ PropUniqN ∧ PropConvInv`, all at the *same* index — again no
`SortForallEDisjoint`.

§2 below assembles those two into the target and the assembly is `SortForallEDisjoint`-free.
So funding `SortForallEDisjoint` would be work on a route the tree has already routed around.

## 2. What the target does reduce to, machine-checked

`propTypeAgreeN_and_propUniqN_of` (§2): for **every** environment and every `U`,

    (∀ n, SortDisjInvN) ∧ (∀ n, PropConvInv) ∧ (∀ n, RegPi) ∧ (∀ n, InstLvl)
      ∧ (∀ n, PropUniqN.AppCase)
    →  (∀ n, PropTypeAgreeN) ∧ (∀ n, PropUniqN)

with the base index discharged internally (`PropUniqN.zero`, `PropTypeAgreeN.zero`).

**And it is a collapse, stated as one.**  `PropConv.PropUniqN.appCase_iff` proves
`PropUniqN.AppCase ↔ PropUniqN` over `SortDisjInvN`, so the fifth hypothesis *is* the second
conclusion.  `propUniqN_iff_appCase_all` below states that as an `↔` at the `∀ n` level, which
is the honest form: the reduction moves no content, it **isolates** it — the content of both
`∀ n` targets is the single statement `∀ n, PropUniqN.AppCase env U n`
(= `AppCase.AppUniqLvl`), modulo four side conditions.

That is still worth having, because it says the two `∀ n` statements are **one** obligation and
not two, and because `AppCase.lean` has already priced and refuted every named route to it.

**The caveat, and it is a real one.**  `PropConv.RegPi`'s own docstring says it is **not shown
satisfiable** — not even at the base index — because `Stratified.lam` does not ship
`A::Γ ⊢ B : .sort v` and `Lookup` can hand back a Π-type whose components were never typed.  So
`propTypeAgreeN_and_propUniqN_iff` is **conditional on `RegPi` being satisfiable**, and if it is
not, that `↔` is vacuous (`docs/vacuity-ledger.md` §0, seventh blindness).  The half that carries
no such caveat is `propUniqN_iff_appCase_all`: it needs only `SortDisjInvN`, whose base index is
`PropConv.SortDisjInvN.zero`.  Read the two accordingly — one is clean, one is conditional, and
they are stated separately for that reason.

## 3. Route B's hypotheses can carry the `OnCtx` guard — a genuine weakening

`propTypeAgreeOnCtx_of_stratifiedN`'s conclusion is `OnCtx`-guarded and its proof has the guard
in hand at the point where it applies `pta` and `pun`; it just does not use it.  §3 restates
route B with the guard pushed onto its two hypotheses (`PropTypeAgreeNOn`, `PropUniqNOn`), which
is strictly less to prove — `PropTypeAgreeN.propTypeAgreeNOn` is the one-line comparison.  The
conclusion is `SortInvIndep.PropAgreeOn`, which is `NotProofNoModel.PropTypeAgreeOnCtx` restated
(see that file).

**The exact edit this suggests in a file I do not own**: `SetModel/PropAgreeWall.lean`'s
`propTypeAgreeOnCtx_of_stratifiedN` and `propUniqOnCtx_of_stratifiedN` should take
`PropTypeAgreeNOn` / `PropUniqNOn`, and `nonempty_propSplit_of_stratifiedN` with them.  Nothing
here edits it; §3 proves the `Theory/Typing`-side statement so that the edit is a rename.

Why it matters beyond tidiness: `PropConv.RegPi`'s own docstring records that it is **not known
satisfiable unguarded** — "`Lookup` can hand back a Π-type whose components were never typed, so
it needs a well-formed-context hypothesis (`OnCtx`)".  With the guard on the target, that
hypothesis is available to whoever proves `RegPi`.

## 4. `SortForallEDisjoint` cannot be proved from `Ordered env`

§4 refutes it at `SortClauses.sortPiEnv`, an `Ordered` environment that is not `VEnv.WF`.  This
is the typing-level statement, not `SortClauses.sortPiEnv_sortForallEDisjN_false`'s
conversion-level clause (3); the two are different predicates with confusingly similar names.
So *if* anyone does return to the `SortForallEDisjoint` route, the premise must be `VEnv.WF`,
and `Ordered env` — which is all `propTypeAgreeOnCtx_of_stratifiedN` asks for — is not enough.
-/

namespace Lean4Lean

namespace VLevel

/-- At `nv = 0` a well-formed level has no parameters, so its value does not depend on the
assignment.  A local copy of `SetModel/PreludeOracle.eval_const_of_wf_zero`; that file is in the
model cone, which `Theory/Typing` must not import. -/
theorem eval_indep_of_wf_zero : ∀ {u : VLevel}, u.WF 0 → ∀ ls ls', u.eval ls = u.eval ls'
  | .zero, _, _, _ => rfl
  | .succ l, h, ls, ls' => by simp only [VLevel.eval, eval_indep_of_wf_zero (u := l) h ls ls']
  | .max l₁ l₂, h, ls, ls' => by
    simp only [VLevel.eval, eval_indep_of_wf_zero (u := l₁) h.1 ls ls',
      eval_indep_of_wf_zero (u := l₂) h.2 ls ls']
  | .imax l₁ l₂, h, ls, ls' => by
    simp only [VLevel.eval, eval_indep_of_wf_zero (u := l₁) h.1 ls ls',
      eval_indep_of_wf_zero (u := l₂) h.2 ls ls']
  | .param i, h, _, _ => absurd h (by simp [VLevel.WF])

/-- Hence at `nv = 0` the `≈ .zero` shape and the pointwise shape agree.  Local copy of
`SetModel/PreludeOracle.equivZero_iff_eval_zero`, same reason. -/
theorem equivZero_iff_eval_zero' {u : VLevel} (hu : u.WF 0) (ls : List Nat) :
    u ≈ (.zero : VLevel) ↔ u.eval ls = 0 := by
  rw [VLevel.equiv_def]
  refine ⟨fun h => by simpa [VLevel.eval] using h ls, fun h ls' => ?_⟩
  simp only [VLevel.eval]
  rw [eval_indep_of_wf_zero hu ls' ls]; exact h

end VLevel

namespace VEnv

variable {env : VEnv} {U n : Nat}

/-! ## §1 The assembly, and the collapse it isolates -/

/-- **Both `∀ n` targets from four side conditions and one fixpoint.**

`PropConv.propUniq_of'` gives `PropUniqN` at each index from `SortDisjInvN` and the `app` case;
`PropConv.propTypeAgree_appCase_of` gives `PropTypeAgreeN`'s `app` case at `k+1` from
`PropUniqN` at the *same* index plus `RegPi`, `InstLvl`, `SortInvN`, `PropConvInv`; and
`PropConv.propTypeAgree_of'` closes `PropTypeAgreeN`.  The base index is
`PropUniqN.zero` / `PropTypeAgreeN.zero`, unconditional at every environment.

`SortForallEDisjoint` does not occur, which is §1 of the module docstring. -/
theorem propTypeAgreeN_and_propUniqN_of
    (dinv : ∀ n, env.SortDisjInvN U n) (pci : ∀ n, env.PropConvInv U n)
    (hreg : ∀ n, env.RegPi U n) (hinst : ∀ n, env.InstLvl U n)
    (happ : ∀ n, PropUniqN.AppCase env U n) :
    (∀ n, env.PropTypeAgreeN U n) ∧ (∀ n, env.PropUniqN U n) := by
  have hpu : ∀ n, env.PropUniqN U n := fun n => propUniq_of' (dinv n) (happ n)
  refine ⟨fun n => ?_, hpu⟩
  cases n with
  | zero => exact PropTypeAgreeN.zero
  | succ k =>
    exact propTypeAgree_of' (dinv (k+1)).1 (pci (k+1))
      (propTypeAgree_appCase_of (dinv (k+1)).1 (hreg (k+1)) (hinst (k+1)) (hpu (k+1))
        (pci (k+1)))

/-- **The collapse in §1, stated as the `↔` it is.**  The fifth hypothesis of §1 is the second
conclusion — `PropConv.PropUniqN.appCase_iff` both ways — so §1 does not move content across a
boundary; it shows the two `∀ n` targets are **one** obligation, `∀ n, PropUniqN.AppCase`, plus
four side conditions.  `AppCase.AppUniqLvl.iff` identifies that obligation with
`env.AppUniqLvl U n`. -/
theorem propUniqN_iff_appCase_all (dinv : ∀ n, env.SortDisjInvN U n) :
    (∀ n, PropUniqN.AppCase env U n) ↔ (∀ n, env.PropUniqN U n) :=
  ⟨fun h n => (PropUniqN.appCase_iff (dinv n)).1 (h n),
   fun h n => (PropUniqN.appCase_iff (dinv n)).2 (h n)⟩

/-- **…and so the whole of §1 is an `↔` in that coordinate.**  The four side conditions plus
`∀ n, AppUniqLvl` are *equivalent* to the two `∀ n` targets — not merely sufficient for them.
This is the anti-vacuity check `docs/vacuity-ledger.md` §0 asks for, run before the reduction is
reported rather than after. -/
theorem propTypeAgreeN_and_propUniqN_iff
    (dinv : ∀ n, env.SortDisjInvN U n) (pci : ∀ n, env.PropConvInv U n)
    (hreg : ∀ n, env.RegPi U n) (hinst : ∀ n, env.InstLvl U n) :
    (∀ n, PropUniqN.AppCase env U n) ↔
      ((∀ n, env.PropTypeAgreeN U n) ∧ (∀ n, env.PropUniqN U n)) :=
  ⟨fun h => propTypeAgreeN_and_propUniqN_of dinv pci hreg hinst h,
   fun h => (propUniqN_iff_appCase_all dinv).2 h.2⟩

/-! ## §2 Route B with the `OnCtx` guard on its hypotheses -/

/-- `PropTypeAgreeN` with the context guard the *conclusion* of route B already carries. -/
def PropTypeAgreeNOn (env : VEnv) (U n : Nat) : Prop :=
  ∀ {Γ : List VExpr} {e A A' : VExpr}, OnCtx Γ (env.IsType U) →
    env.HasTypeN U n Γ e A → env.HasTypeN U n Γ e A' →
    IsPropN env U n Γ A → IsPropN env U n Γ A'

/-- `PropUniqN`, likewise. -/
def PropUniqNOn (env : VEnv) (U n : Nat) : Prop :=
  ∀ {Γ : List VExpr} {A : VExpr} {u v : VLevel}, OnCtx Γ (env.IsType U) →
    env.HasTypeN U n Γ A (.sort u) → env.HasTypeN U n Γ A (.sort v) →
    (u ≈ (.zero : VLevel) ↔ v ≈ (.zero : VLevel))

theorem PropTypeAgreeN.propTypeAgreeNOn (h : env.PropTypeAgreeN U n) :
    PropTypeAgreeNOn env U n := fun _ => h

theorem PropUniqN.propUniqNOn (h : env.PropUniqN U n) : PropUniqNOn env U n := fun _ => h

/-- **Route B, with strictly weaker hypotheses.**

`SetModel/PropAgreeWall.propTypeAgreeOnCtx_of_stratifiedN`'s proof, with the guard it already
has in hand passed on to `pta` and `pun`.  The conclusion is `SortInvIndep.PropAgreeOn`, which
is `SetModel/NotProofNoModel.PropTypeAgreeOnCtx` restated in `Theory/Typing`.

`nv = 0` is load-bearing exactly as it is there: `equivZero_iff_eval_zero'` needs `u.WF 0`, and
the step is refuted at `nv ≥ 2`. -/
theorem propAgreeOn_of_stratifiedNOn (henv : Ordered env)
    (pta : ∀ n, PropTypeAgreeNOn env 0 n) (pun : ∀ n, PropUniqNOn env 0 n) :
    PropAgreeOn env 0 := by
  intro Γ e A A' u u' ls hΓ hu hu' he he' hA hA'
  rw [← VLevel.equivZero_iff_eval_zero' hu ls, ← VLevel.equivZero_iff_eval_zero' hu' ls]
  obtain ⟨n₁, sHe⟩ := he.stratifyN henv hΓ
  obtain ⟨n₂, sHe'⟩ := he'.stratifyN henv hΓ
  obtain ⟨n₃, sHA⟩ := hA.stratifyN henv hΓ
  obtain ⟨n₄, sHA'⟩ := hA'.stratifyN henv hΓ
  have hrefl : (VLevel.zero : VLevel) ≈ (VLevel.zero : VLevel) := VLevel.equiv_def.2 fun _ => rfl
  have He : env.HasTypeN 0 (max (max n₁ n₂) (max n₃ n₄) + 1) Γ e A :=
    sHe.mono (Nat.le_succ_of_le (Nat.le_trans (Nat.le_max_left n₁ n₂) (Nat.le_max_left _ _)))
  have He' : env.HasTypeN 0 (max (max n₁ n₂) (max n₃ n₄) + 1) Γ e A' :=
    sHe'.mono (Nat.le_succ_of_le (Nat.le_trans (Nat.le_max_right n₁ n₂) (Nat.le_max_left _ _)))
  have HA : env.HasTypeN 0 (max (max n₁ n₂) (max n₃ n₄) + 1) Γ A (.sort u) :=
    sHA.mono (Nat.le_succ_of_le (Nat.le_trans (Nat.le_max_left n₃ n₄) (Nat.le_max_right _ _)))
  have HA' : env.HasTypeN 0 (max (max n₁ n₂) (max n₃ n₄) + 1) Γ A' (.sort u') :=
    sHA'.mono (Nat.le_succ_of_le (Nat.le_trans (Nat.le_max_right n₃ n₄) (Nat.le_max_right _ _)))
  constructor
  · intro hz
    have hpA : env.HasTypeN 0 (max (max n₁ n₂) (max n₃ n₄) + 1) Γ A (.sort .zero) :=
      .conv (.sortDF hu trivial hz) HA
    exact (pun _ hΓ (pta _ hΓ He He' hpA) HA').1 hrefl
  · intro hz
    have hpA' : env.HasTypeN 0 (max (max n₁ n₂) (max n₃ n₄) + 1) Γ A' (.sort .zero) :=
      .conv (.sortDF hu' trivial hz) HA'
    exact (pun _ hΓ (pta _ hΓ He' He hpA') HA).1 hrefl

/-- The unguarded hypotheses still work, so §2 subsumes route B rather than replacing it. -/
theorem propAgreeOn_of_stratifiedN (henv : Ordered env)
    (pta : ∀ n, env.PropTypeAgreeN 0 n) (pun : ∀ n, env.PropUniqN 0 n) :
    PropAgreeOn env 0 :=
  propAgreeOn_of_stratifiedNOn henv (fun n => PropTypeAgreeN.propTypeAgreeNOn (pta n))
    (fun n => PropUniqN.propUniqNOn (pun n))

/-- The guarded statements hold at the base index, unconditionally at every environment — the
anti-vacuity check route B's own section runs, replayed for the guarded forms. -/
theorem PropTypeAgreeNOn.zero : PropTypeAgreeNOn env U 0 :=
  fun _ => PropTypeAgreeN.zero

theorem PropUniqNOn.zero : PropUniqNOn env U 0 := fun _ => PropUniqN.zero

/-! ## §3 `SortForallEDisjoint` is false at an `Ordered` environment

`SortClauses.sortPiEnv` carries the rule `Prop ≡ ∀ (_ : Prop), Prop`.  In the one-entry context
`[Prop]` the variable `.bvar 0` is typed at `.sort .zero` — a *sort* type — and `conv` along the
rule retypes it at a *Π*.  So a single term has both, which is exactly what
`SortForallEDisjoint` forbids.

This is the typing-level primitive (`UniqueTypingN.SortForallEDisjoint`), **not**
`SortClauses.sortPiEnv_sortForallEDisjN_false`'s conversion-level clause (3)
(`DefInvRefute.SortForallEDisjN`).  The names are close and the statements are different. -/

/-- `.bvar 0` is typed at the *sort* `Prop` in the context `[Prop]`, at any index. -/
theorem sortPiEnv_bvar_sort :
    sortPiEnv.HasTypeN 0 1 [.sort .zero] (.bvar 0) (.sort .zero) :=
  .bvar (Lookup.zero' rfl)

/-- The rule, in the one-entry context: `extra`'s conclusion is context-independent. -/
theorem sortPiEnv_conv_cons : sortPiEnv.IsDefEqN 0 1 [.sort .zero] (.sort .zero)
    (.forallE (.sort .zero) (.sort .zero)) :=
  Stratified.extra (ls := []) sortPiEnv_defeqs nofun rfl

/-- …and hence the same `.bvar 0` is also typed at a **Π**. -/
theorem sortPiEnv_bvar_pi :
    sortPiEnv.HasTypeN 0 1 [.sort .zero] (.bvar 0)
      (.forallE (.sort .zero) (.sort .zero)) :=
  .conv sortPiEnv_conv_cons sortPiEnv_bvar_sort

/-- **`SortForallEDisjoint` is false at an `Ordered`, non-`WF` environment.**  So the route
through it cannot be run at the generality
`SetModel/PropAgreeWall.propTypeAgreeOnCtx_of_stratifiedN` is stated in (`Ordered env`); the
right premise is `VEnv.WF`, as `SortClauses` §3 concludes for clause (3). -/
theorem sortPiEnv_sortForallEDisjoint_false : ¬ sortPiEnv.SortForallEDisjoint 0 1 :=
  fun h => h sortPiEnv_bvar_sort sortPiEnv_bvar_pi

/-- …and hence the `∀ n` form is false there too. -/
theorem sortPiEnv_sortForallEDisjoint_all_false :
    ¬ ∀ n, sortPiEnv.SortForallEDisjoint 0 n :=
  fun h => sortPiEnv_sortForallEDisjoint_false (h 1)

/-- **The witness does NOT refute the two `∀ n` targets**, and that has to be said, because a
refutation of `SortForallEDisjoint` at an environment would be worthless if it came from a
counterexample to the targets themselves.  It does not: the witness's two types are
`.sort .zero` and `.forallE (.sort .zero) (.sort .zero)`, and **neither is a proposition** —
`IsPropN` at `.sort .zero` would need `.sort .zero : .sort .zero`.  The one-liner below is the
`sort` half; `PropTypeAgreeN`'s hypothesis `IsPropN Γ A` is therefore never met at this witness,
so it is silent here. -/
theorem sortPiEnv_witness_type_not_prop (dinv : sortPiEnv.SortInvN 0 1) :
    ¬ IsPropN sortPiEnv 0 1 [.sort .zero] (.sort .zero) :=
  not_isPropN_sort dinv

section Audit
#print axioms Lean4Lean.VLevel.eval_indep_of_wf_zero
#print axioms Lean4Lean.VLevel.equivZero_iff_eval_zero'
#print axioms Lean4Lean.VEnv.propTypeAgreeN_and_propUniqN_of
#print axioms Lean4Lean.VEnv.propUniqN_iff_appCase_all
#print axioms Lean4Lean.VEnv.propTypeAgreeN_and_propUniqN_iff
#print axioms Lean4Lean.VEnv.PropTypeAgreeNOn
#print axioms Lean4Lean.VEnv.PropUniqNOn
#print axioms Lean4Lean.VEnv.PropTypeAgreeN.propTypeAgreeNOn
#print axioms Lean4Lean.VEnv.PropUniqN.propUniqNOn
#print axioms Lean4Lean.VEnv.propAgreeOn_of_stratifiedNOn
#print axioms Lean4Lean.VEnv.propAgreeOn_of_stratifiedN
#print axioms Lean4Lean.VEnv.PropTypeAgreeNOn.zero
#print axioms Lean4Lean.VEnv.PropUniqNOn.zero
#print axioms Lean4Lean.VEnv.sortPiEnv_bvar_sort
#print axioms Lean4Lean.VEnv.sortPiEnv_conv_cons
#print axioms Lean4Lean.VEnv.sortPiEnv_bvar_pi
#print axioms Lean4Lean.VEnv.sortPiEnv_sortForallEDisjoint_false
#print axioms Lean4Lean.VEnv.sortPiEnv_sortForallEDisjoint_all_false
#print axioms Lean4Lean.VEnv.sortPiEnv_witness_type_not_prop
end Audit

end VEnv
end Lean4Lean
