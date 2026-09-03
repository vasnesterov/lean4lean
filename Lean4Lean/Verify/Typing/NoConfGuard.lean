import Lean4Lean.Verify.Typing.ConstSpineWF
import Lean4Lean.Theory.Typing.ConstInvWitness
import Lean4Lean.Theory.Typing.ShapeIndep
import Lean4Lean.Theory.Typing.SortInvIndep
import Lean4Lean.Theory.Typing.RigidConstPrice

/-!
# Is the `¬ IsProof`-guarded constant no-confusion row true?

`docs/handoff-shapeindep.md` §7 item 1 asks exactly that, and says of it

> nothing in the tree has the `¬ IsProof` form of constant no-confusion

**That sentence is false**, and the answer to the question is *yes*.  See §2: the
`Params`-level statement `VEnv.IsDefEq.constApp_inv` (`Verify/Typing/ConstSpine.lean:248`) is
guarded by `¬ IsProof`, not by `IsType`, and its own docstring says why —

> The `¬IsProof` side condition is exactly `const_app_inv`'s, for the same reason: it is what
> blocks the `proofIrrel` constructor, and it propagates down the spine by `IsProof.app'`
> where `IsType` would not.

`VEnv.ConstNoConf`'s `IsType` guard is introduced one level *above* that, in the `VEnv`-facing
wrapper `VEnv.constApp_inv_of_patWF` (`ConstSpine.lean:579`), which applies
`IsType.not_isProof` to it on the spot.  So the "guard gap" is a **wrapper**, not a gap: going
under the wrapper gives the `¬ IsProof` form directly, and `patWF_of_wf` discharges `PatWF`.

This file does that (§2), after trying to refute the row first (§1), and then measures what is
and is not thereby settled (§3, §4).

## The file in one table

| statement | what it is |
| --- | --- |
| `not_constNoConfUG_ncPropEnv` | no-confusion with **both** guards dropped is false at a `VEnv.WF` environment |
| `isProof_ncPropEnv_lhs` | …and the `¬ IsProof` guard excludes that witness — so the refutation does **not** extend to the row |
| `not_isType_ncPropEnv_lhs` | …and so does the `IsType` guard; at this witness the two guards fail *together* |
| `constNoConfNP_of_patWF` / `_of_wf` | **the row is a theorem**, modulo `PatWF`, and unconditionally at `VEnv.WF` |
| `ConstNoConfNP.constNoConf` | the `¬ IsProof` form implies the `IsType` form (through `IsType.not_isProof`, tainted) |
| `constNoConf_iff_constNoConfNP_over_wf` | over `VEnv.WF` the two are the **same predicate** — an inert equivalence, stated to be dismissed |
| `rigidConstNoConf_of_wf`, `spineVarAppDisjT_wf` | `ShapeIndep.lean`'s row 3, discharged in the tree instead of in a `/tmp` probe |

Layer note: this file is under `Verify/` because it needs `Verify/Typing/ConstSpine.lean` and
`Theory/Typing/ShapeIndep.lean` at once, which no `Theory/` file may (`Theory` must not import
`Verify`).  The previous round did the same cross-layer step in `/tmp` and said so.
-/

namespace Lean4Lean

open VExpr

namespace VEnv

/-! ## §1 The refutation attempt: two heads on one proposition

Tried first, per the brief.  `Theory/Typing/ConstInvWitness.lean`'s **W2** is the place where
dropping a guard proves `False`, and it is *one head applied to two arguments*
(`mkP A ≡ mkP B`).  No-confusion needs *two heads*, so W2's environment gets a second axiom of
`mkP`'s own type, and the same `proofIrrel` step then relates two **distinct** rule-free
constant spines.

Three things make this a sharper witness than W2:

* the environment is built from `VEnv.empty` by three `.axiom` steps and is **`VEnv.WF`**
  (`wf_ncPropEnv`) — so this is a hard constraint, not a control.  Nothing here needs a δ-rule,
  and `ncPropEnv.defeqs` is literally `False`, so *every* head is rule-free;
* the two spines are **non-empty** and their arguments are not definitionally equal (they are
  `Prop` and `Prop → Prop`, W2's own pair);
* it therefore refutes no-confusion with **both** guards deleted, at a well-formed environment.

And then it stops: §1.3 proves the left spine *is* a proof, so the `¬ IsProof` guard excludes
it.  The refutation attempt fails, and fails for the reason the guard exists. -/

/-! ### §1.1 The environment: W2's two axioms plus one more -/

/-- `P : Prop` alone. -/
def ncPropEnv1 : VEnv where
  constants n := if `P = n then some propAx else none
  defeqs _ := False

/-- `P : Prop`, `mkP : Type 0 → P`. -/
def ncPropEnv2 : VEnv where
  constants n := if `mkP = n then some mkPAx else if `P = n then some propAx else none
  defeqs _ := False

/-- `P : Prop`, `mkP : Type 0 → P`, `mkQ : Type 0 → P`.  Three axioms, no rules. -/
def ncPropEnv : VEnv where
  constants n :=
    if `mkQ = n then some mkPAx else
    if `mkP = n then some mkPAx else
    if `P = n then some propAx else none
  defeqs _ := False

theorem ncPropEnv1_P : ncPropEnv1.constants `P = some propAx := by simp [ncPropEnv1]
theorem ncPropEnv2_P : ncPropEnv2.constants `P = some propAx := by simp [ncPropEnv2]
theorem ncPropEnv_P : ncPropEnv.constants `P = some propAx := by simp [ncPropEnv]
theorem ncPropEnv_mkP : ncPropEnv.constants `mkP = some mkPAx := by simp [ncPropEnv]
theorem ncPropEnv_mkQ : ncPropEnv.constants `mkQ = some mkPAx := by simp [ncPropEnv]

theorem addConst_ncPropEnv1 : VEnv.empty.addConst `P propAx = some ncPropEnv1 := by
  simp [VEnv.addConst, VEnv.empty, ncPropEnv1]

theorem addConst_ncPropEnv2 : ncPropEnv1.addConst `mkP mkPAx = some ncPropEnv2 := by
  simp [VEnv.addConst, ncPropEnv1, ncPropEnv2]

theorem addConst_ncPropEnv : ncPropEnv2.addConst `mkQ mkPAx = some ncPropEnv := by
  simp [VEnv.addConst, ncPropEnv2, ncPropEnv]

/-! ### §1.2 Typing, generic in the head name

`ncMkApp` is stated for an arbitrary `c` whose recorded type is `mkPAx`'s, which is what lets
one lemma serve both `mkP` and `mkQ`. -/

/-- `P : Prop`, at any context. -/
theorem ncPty {env : VEnv} {Γ : List VExpr} (hP : env.constants `P = some propAx) :
    env.HasType 0 Γ (.const `P []) vprop :=
  .constDF (ls := []) (ls' := []) hP nofun nofun rfl .nil

/-- `Type 0 : Type 1`. -/
theorem ncType0 {env : VEnv} {Γ : List VExpr} :
    env.HasType 0 Γ vtype0 (.sort (.succ (.succ .zero))) := .sortDF trivial trivial rfl

/-- `c C : P`, for either of the two constructors and any `C : Type 0`. -/
theorem ncMkApp {env : VEnv} {Γ : List VExpr} {c : Lean.Name}
    (hmk : env.constants c = some mkPAx) {C : VExpr} (hC : env.HasType 0 Γ C vtype0) :
    env.HasType 0 Γ (.app (.const c []) C) (.const `P []) :=
  .appDF (.constDF (ls := []) (ls' := []) hmk nofun nofun rfl .nil) hC

/-- `mkP`'s (and `mkQ`'s) type is a legal axiom type: `Type 0 → P` is a `Prop`. -/
theorem mkPAx_wf {env : VEnv} (hP : env.constants `P = some propAx) :
    VConstant.WF env mkPAx := ⟨_, .forallEDF ncType0 (ncPty (Γ := [vtype0]) hP)⟩

/-- **The witness environment is well formed.** -/
theorem wf_ncPropEnv : VEnv.WF ncPropEnv :=
  ⟨[.axiom ⟨mkPAx, `mkQ⟩, .axiom ⟨mkPAx, `mkP⟩, .axiom ⟨propAx, `P⟩],
    .decl (.axiom (mkPAx_wf ncPropEnv2_P) addConst_ncPropEnv)
      (.decl (.axiom (mkPAx_wf ncPropEnv1_P) addConst_ncPropEnv2)
        (.decl (.axiom ⟨_, hasType_vprop⟩ addConst_ncPropEnv1) .empty))⟩

/-- No rules at all, so every head is rule-free. -/
theorem ruleFreeHead_ncPropEnv (c : Lean.Name) : ncPropEnv.RuleFreeHead c :=
  fun _ h => absurd h not_false

/-- **W2 with two heads**: `mkP Prop ≡ mkQ (Prop → Prop)`, by `proofIrrel` alone, with no
rule in the environment and no reduction. -/
theorem ncPropEnv_link :
    ncPropEnv.IsDefEqU 0 [] ((VExpr.const `mkP []).mkApp [vprop])
      ((VExpr.const `mkQ []).mkApp [vpropArrow]) :=
  ⟨_, .proofIrrel (ncPty ncPropEnv_P) (ncMkApp ncPropEnv_mkP hasType_vprop)
      (ncMkApp ncPropEnv_mkQ hasType_vpropArrow)⟩

/-- `VEnv.ConstNoConf` with **both** guards deleted — nothing else changed. -/
def ConstNoConfUG (env : VEnv) (U : Nat) : Prop :=
  ∀ (Γ : List VExpr) (c c' : Lean.Name) (us us' : List VLevel) (as as' : List VExpr),
    OnCtx Γ (env.IsType U) →
    env.RuleFreeHead c → env.RuleFreeHead c' →
    env.IsDefEqU U Γ ((VExpr.const c us).mkApp as) ((VExpr.const c' us').mkApp as') →
    c = c'

/-- **Unguarded constant no-confusion is false at a `VEnv.WF` environment.**  Not a control:
`wf_ncPropEnv` is the well-formedness proof, and the mechanism is `proofIrrel`, which no
condition on `env.defeqs` can touch. -/
theorem not_constNoConfUG_ncPropEnv : ¬ ConstNoConfUG ncPropEnv 0 := fun H =>
  absurd (H [] `mkP `mkQ [] [] [vprop] [vpropArrow] trivial
    (ruleFreeHead_ncPropEnv _) (ruleFreeHead_ncPropEnv _) ncPropEnv_link) (by decide)

/-! ### §1.3 Why the attempt stops here -/

/-- **The left spine is a proof**, so `ConstNoConfNP`'s guard excludes the witness of §1.2 and
the refutation does not reach the row.  `sorryAx`-free. -/
theorem isProof_ncPropEnv_lhs :
    ncPropEnv.IsProof 0 [] ((VExpr.const `mkP []).mkApp [vprop]) :=
  ⟨_, ncPty ncPropEnv_P, ncMkApp ncPropEnv_mkP hasType_vprop⟩

/-- **…and it is not a type either**, so `ConstNoConf`'s guard excludes it too.  The two guards
fail *together* at this witness, which is why it separates neither.  Tainted: the only route
from "is a proof" to "is not a type" is `IsType.not_isProof`, i.e. universe uniqueness. -/
theorem not_isType_ncPropEnv_lhs :
    ¬ ncPropEnv.IsType 0 [] ((VExpr.const `mkP []).mkApp [vprop]) := fun h =>
  IsType.not_isProof (Γ := []) wf_ncPropEnv trivial h isProof_ncPropEnv_lhs

section Audit
#print axioms Lean4Lean.VEnv.wf_ncPropEnv
#print axioms Lean4Lean.VEnv.ncPropEnv_link
#print axioms Lean4Lean.VEnv.not_constNoConfUG_ncPropEnv
#print axioms Lean4Lean.VEnv.isProof_ncPropEnv_lhs
#print axioms Lean4Lean.VEnv.not_isType_ncPropEnv_lhs
end Audit

/-! ## §2 The verdict: the row is a theorem, and the `¬ IsProof` form was already there

`VEnv.ConstNoConf` (`Verify/Typing/Rigidity.lean:151`) is *not* where the `IsType` guard comes
from.  Its supply is

    constNoConf_of_wf  ←  constNoConf_of_patWF  ←  constApp_inv_of_patWF
                                                   ←  IsDefEq.constApp_inv   (¬ IsProof)

and the `IsType` appears for the first time in `constApp_inv_of_patWF`, whose *last argument* is
literally `IsType.not_isProof henv hΓ hty` (`ConstSpine.lean:579`).  Everything below the
wrapper is `¬ IsProof`-guarded already.  So the row asked about is obtained by re-doing that one
wrapper without the conversion. -/

/-- **`VEnv.ConstNoConf` with the `IsType` guard replaced by `¬ IsProof`** — the row
`docs/handoff-shapeindep.md` §7 item 1 asks about, character for character otherwise.  The
guard is on the left spine, as in `RigidConstAppInv` and `IsDefEq.constApp_inv`. -/
def ConstNoConfNP (env : VEnv) (U : Nat) : Prop :=
  ∀ (Γ : List VExpr) (c c' : Lean.Name) (us us' : List VLevel) (as as' : List VExpr),
    OnCtx Γ (env.IsType U) →
    env.RuleFreeHead c → env.RuleFreeHead c' →
    ¬ env.IsProof U Γ ((VExpr.const c us).mkApp as) →
    env.IsDefEqU U Γ ((VExpr.const c us).mkApp as) ((VExpr.const c' us').mkApp as') →
    c = c'

/-- **The `¬ IsProof` row is TRUE, modulo `PatWF`.**  Same proof as
`VEnv.constApp_inv_of_patWF` with `IsType.not_isProof hty` replaced by the hypothesis. -/
theorem constNoConfNP_of_patWF {env : VEnv} (henv : env.WF) (U : Nat) (hwf : env.PatWF U) :
    env.ConstNoConfNP U := by
  intro Γ c c' us us' as as' hΓ hc hc' hnp h
  let _inst := VEnv.paramsOfWF henv U hwf
  exact (@VEnv.IsDefEq.constApp_inv _inst Γ c c' us us' as as' h.choose hΓ
    (hc.patFreeHead henv hwf) (hc'.patFreeHead henv hwf) hnp h.choose_spec).1

/-- **…and unconditionally at every well-formed environment**, `PatWF` discharged by
`patWF_of_wf` exactly as for the `IsType` form. -/
theorem constNoConfNP_of_wf {env : VEnv} (henv : env.WF) (U : Nat) : env.ConstNoConfNP U :=
  constNoConfNP_of_patWF henv U (patWF_of_wf henv U)

/-! ### §2.1 The two guards, in both directions

One direction is a one-liner; the other does not exist, and the reason is not difficulty. -/

/-- **`¬ IsProof` ⟹ `IsType` form.**  Tainted, and unavoidably: `IsType.not_isProof` is
universe uniqueness. -/
theorem ConstNoConfNP.constNoConf {env : VEnv} {U : Nat} (henv : env.WF)
    (H : env.ConstNoConfNP U) : env.ConstNoConf U :=
  fun Γ c c' us us' as as' hΓ hc hc' hty h =>
    H Γ c c' us us' as as' hΓ hc hc' (IsType.not_isProof henv hΓ hty) h

/-- **The converse implication is not available at a fixed environment**, and no amount of work
on no-confusion will make it so: it would need `¬ IsProof e → IsType e`, and a term of a
non-`Prop`, non-sort type satisfies the first and not the second.  What *is* provable is the
implication between the two *quantified over all well-formed environments*, in both directions —
because over `VEnv.WF` both sides are theorems (§2).

This is stated to be **dismissed**, in the shape `ShapeIndep.rowsFromBridge_iff_rows` gave the
same trap: it is an equivalence between two things that are separately true, so it measures
nothing.  Anyone tempted to read it as "the guards are interchangeable" should read §3. -/
theorem constNoConf_iff_constNoConfNP_over_wf (U : Nat) :
    (∀ env : VEnv, env.WF → env.ConstNoConf U) ↔ (∀ env : VEnv, env.WF → env.ConstNoConfNP U) :=
  ⟨fun _ _ he => constNoConfNP_of_wf he U, fun _ _ he => constNoConf_of_wf he U⟩

/-! ### §2.2 The consumer side: `ShapeIndep.lean`'s row 3, in the tree

`docs/handoff-shapeindep.md` §3 checked `rigidConstNoConf_iff_constNoConf` and
`spineVarAppDisjT_via_constNoConf` in a `/tmp` probe, because a `Theory/` file cannot import
`Verify/`.  This file can, so the two are recorded here rather than in a scratch directory. -/

/-- `ShapeIndep.RigidConstNoConf` **is** `VEnv.ConstNoConf`, contrapositive for contrapositive. -/
theorem rigidConstNoConf_iff_constNoConf {env : VEnv} {U : Nat} :
    env.RigidConstNoConf U ↔ env.ConstNoConf U := by
  constructor
  · intro H Γ c c' us us' as as' hΓ hc hc' hty h
    exact Classical.byContradiction fun hne => H hΓ hc hc' hne hty h
  · intro H Γ c c' us us' as as' hΓ hc hc' hne hty h
    exact hne (H Γ c c' us us' as as' hΓ hc hc' hty h)

/-- `ShapeIndep.lean`'s row-3 hypothesis, discharged at every well-formed environment. -/
theorem rigidConstNoConf_of_wf {env : VEnv} (henv : env.WF) (U : Nat) :
    env.RigidConstNoConf U := rigidConstNoConf_iff_constNoConf.2 (constNoConf_of_wf henv U)

/-- **`ShapeIndep.spineVarAppDisjT_theorem` with its hypothesis gone.**  Row 3 in its
`IsType`-guarded form is a theorem of the tree. -/
theorem spineVarAppDisjT_wf (U : Nat) : ∀ env : VEnv, env.WF → SpineVarAppDisjT env U :=
  spineVarAppDisjT_theorem (fun _ henv => rigidConstNoConf_of_wf henv U)

/-- The `¬ IsProof`-guarded companion of `RigidConstNoConf`, for the same reason its
`IsType`-guarded original exists: so the row and the fact are the same statement. -/
def RigidConstNoConfNP (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {c c' : Lean.Name} {ls ls' : List VLevel} {as as' : List VExpr},
    OnCtx Γ (env.IsType U) → env.RuleFreeHead c → env.RuleFreeHead c' → c ≠ c' →
    ¬ env.IsProof U Γ ((VExpr.const c ls).mkApp as) →
    ¬ env.IsDefEqU U Γ ((VExpr.const c ls).mkApp as) ((VExpr.const c' ls').mkApp as')

theorem rigidConstNoConfNP_of_wf {env : VEnv} (henv : env.WF) (U : Nat) :
    env.RigidConstNoConfNP U := fun hΓ hc hc' hne hnp h =>
  hne (constNoConfNP_of_wf henv U _ _ _ _ _ _ _ hΓ hc hc' hnp h)

section Audit
#print axioms Lean4Lean.VEnv.constNoConfNP_of_patWF
#print axioms Lean4Lean.VEnv.constNoConfNP_of_wf
#print axioms Lean4Lean.VEnv.ConstNoConfNP.constNoConf
#print axioms Lean4Lean.VEnv.constNoConf_iff_constNoConfNP_over_wf
#print axioms Lean4Lean.VEnv.rigidConstNoConf_iff_constNoConf
#print axioms Lean4Lean.VEnv.rigidConstNoConf_of_wf
#print axioms Lean4Lean.VEnv.spineVarAppDisjT_wf
#print axioms Lean4Lean.VEnv.rigidConstNoConfNP_of_wf
end Audit

/-! ## §3 The guard bridge does **not** need hole A

`ConstNoConfNP.constNoConf` above pays `IsType.not_isProof`, whose cone is
`IsDefEqU.forallE_inv_stratified` — hole A.  It need not.  `SortInvIndep.PropAgreeOn`
("propositionhood of a term's type is invariant") is the *other* axis's node, and the general
"a type is not a proof" follows from it in four lines with no `sorryAx`.

The tree had this argument twice, both times at less generality:
`SortInvIndep.sortNotProof_of_propAgreeOn` (the term must be a **sort**) and
`SpineVarVacuity.spineVar_not_isProof_of_propAgreeOn` (one fixed witness).  The general form is
`IsType.not_isProof`'s statement with `PropAgreeOn` in place of `WF.sortUniq'`. -/

/-- **A type is not a proof, hole-free** — from `PropAgreeOn` rather than from universe
uniqueness.  Compare `IsType.not_isProof`, whose cone is hole A. -/
theorem not_isProof_of_hasType_sort {env : VEnv} {U : Nat} (hT : PropAgreeOn env U)
    {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U)) {e : VExpr} {u : VLevel} (hu : u.WF U)
    (h : env.HasType U Γ e (.sort u)) : ¬ env.IsProof U Γ e := by
  rintro ⟨p, hp0, hep⟩
  have h2 := hT (u := .succ u) (u' := .zero) (ls := []) hΓ hu trivial h hep
    (HasType.sort hu) hp0
  simp [VLevel.eval] at h2

/-- **The `¬ IsProof` form implies the `IsType` form with no hole**, `PropAgreeOn` carried.
So the guard bridge at this row is *not* the `ConstVar` strengthening target and not hole A;
it is the independent node of the corner's other axis.  Levels: `IsType` gives the sort but not
its well-formedness, so `HasType.sort_inv` supplies that from `Ordered`. -/
theorem ConstNoConfNP.constNoConf_of_propAgreeOn {env : VEnv} {U : Nat} (hord : Ordered env)
    (hT : PropAgreeOn env U) (H : env.ConstNoConfNP U) : env.ConstNoConf U :=
  fun Γ c c' us us' as as' hΓ hc hc' hty h =>
    H Γ c c' us us' as as' hΓ hc hc'
      (not_isProof_of_hasType_sort hT hΓ
        ((hty.choose_spec.isType hord hΓ).sort_inv hord) hty.choose_spec) h

/-! ## §4 Anti-vacuity: the guarded row fires at §1's own environment

The strongest form of "the guard is not eating the statement" available here: the environment
that **refutes** the unguarded row also **satisfies** the guarded one at a non-trivial instance.
`P` is a type there, so the guard is discharged, and the conclusion is a genuine negative fact —
`P` is not definitionally equal to any `mkP`-headed spine — at the very environment where `mkP`
and `mkQ` *are* confused. -/

theorem ncPropEnv_P_isType : ncPropEnv.IsType 0 [] (.const `P []) := ⟨_, ncPty ncPropEnv_P⟩

/-- The guard, discharged **hole-free** modulo `PropAgreeOn` at `ncPropEnv` (§3's route), and
unconditionally-but-tainted by `IsType.not_isProof`.  Both are recorded; neither is assumed. -/
theorem ncPropEnv_P_not_isProof_of_propAgreeOn (hT : PropAgreeOn ncPropEnv 0) :
    ¬ ncPropEnv.IsProof 0 [] ((VExpr.const `P []).mkApp []) :=
  not_isProof_of_hasType_sort hT (Γ := []) trivial (u := .zero) trivial (ncPty ncPropEnv_P)

theorem ncPropEnv_P_not_isProof : ¬ ncPropEnv.IsProof 0 [] ((VExpr.const `P []).mkApp []) :=
  IsType.not_isProof (Γ := []) wf_ncPropEnv trivial ncPropEnv_P_isType

/-- **The guarded row fires, non-vacuously, at the refuting environment.**  Every premise of
`ConstNoConfNP` discharged at a concrete `VEnv.WF` environment, for every level list and every
argument list, with a conclusion that is not `True`. -/
theorem ncPropEnv_P_ne_mkP_spine (us : List VLevel) (as : List VExpr) :
    ¬ ncPropEnv.IsDefEqU 0 [] ((VExpr.const `P []).mkApp []) ((VExpr.const `mkP us).mkApp as) :=
  fun h => absurd (constNoConfNP_of_wf wf_ncPropEnv 0 [] `P `mkP [] us [] as trivial
    (ruleFreeHead_ncPropEnv _) (ruleFreeHead_ncPropEnv _) ncPropEnv_P_not_isProof h) (by decide)

/-! ## §5 What a *separating* witness would have to be, and why it cannot be a refutation

The one thing this round did not get is a witness where the `IsType` form holds and the
`¬ IsProof` form fails.  §5.1 is the reason it can only ever be a **control**. -/

/-- The separation, named so it can be graded. -/
def GuardSeparated (env : VEnv) (U : Nat) : Prop := env.ConstNoConf U ∧ ¬ env.ConstNoConfNP U

/-- **Any separating witness is not well formed** — so brief-outcome 1 ("a witness where the
`¬ IsProof` form fails while the `IsType` form holds") is *unreachable at `VEnv.WF`*, and a
non-`VEnv.WF` one is a control in the sense of `RigidConstPrice.lean` §5, not a refutation of
anything the corner needs.  This is the precise sense in which the row is settled. -/
theorem not_wf_of_guardSeparated {env : VEnv} {U : Nat} (h : GuardSeparated env U) : ¬ env.WF :=
  fun henv => h.2 (constNoConfNP_of_wf henv U)

/-- **…and the two guards fail together at every witness of §1's shape.**  A separating instance
needs a spine that is not a proof *and* not a type; §1's is neither-nor in the other direction
(it is a proof, hence — at a well-formed environment — not a type).  So the separation cannot be
built from `proofIrrel`, which is the only mechanism that identifies distinct rule-free heads
without a δ-rule. -/
theorem ncPropEnv_guards_fail_together :
    ncPropEnv.IsProof 0 [] ((VExpr.const `mkP []).mkApp [vprop]) ∧
      ¬ ncPropEnv.IsType 0 [] ((VExpr.const `mkP []).mkApp [vprop]) :=
  ⟨isProof_ncPropEnv_lhs, not_isType_ncPropEnv_lhs⟩

section Audit
#print axioms Lean4Lean.VEnv.not_isProof_of_hasType_sort
#print axioms Lean4Lean.VEnv.ConstNoConfNP.constNoConf_of_propAgreeOn
#print axioms Lean4Lean.VEnv.ncPropEnv_P_not_isProof_of_propAgreeOn
#print axioms Lean4Lean.VEnv.ncPropEnv_P_ne_mkP_spine
#print axioms Lean4Lean.VEnv.not_wf_of_guardSeparated
end Audit

/-! ## §6 A side effect worth flagging: the corner's three constant conjuncts, and a measured circle

`RigidConstPrice.lean` §6.1 names one open instance:

> at `rcEnv0` … all three conjuncts are **non-vacuous at a well-formed environment**.  Nothing
> here proves them there; that is the smallest open instance in this corner and it is named as
> such.

**They are provable there** — all three, at every `VEnv.WF` environment, by the same
Church–Rosser route as §2, since `RigidConstAppInv` is the `¬ IsProof`-guarded (B) and the other
two are (A)'s two halves.  §6.2 instantiates at `rcEnv0` itself.

**This is not progress, and the reason is measured, not argued.**  The hole cone of every
statement in §6 contains `VEnv.WF.rigidShapeUniqNS` — hole B — which is the node the three
conjuncts were being priced *for* (`constFamily_iff_rigidShapeUniqNS` proves them jointly
equivalent to it over hole A's base).  So this closes the instance through its own target.  It is
recorded here so that nobody reads `RigidConstPrice.lean` §6.1 as an *open* item and spends a
round on it; the open item is a route to the three whose cone does **not** contain hole B, which
is `RigidNodeCircle.lean` §5's untouched `PatWF` re-derivation. -/

/-- **(B) + (D) at the `VEnv` level with the `¬ IsProof` guard** — `constApp_inv_of_patWF` with
`IsType.not_isProof` *deleted* rather than applied.  §2 and §6.1 are its two projections. -/
theorem constApp_inv_np_of_patWF {env : VEnv} (henv : env.WF) (U : Nat) (hwf : env.PatWF U)
    {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U)) {c c' : Lean.Name} {ls ls' : List VLevel}
    {as as' : List VExpr}
    (hc : env.RuleFreeHead c) (hc' : env.RuleFreeHead c')
    (hnp : ¬ env.IsProof U Γ ((VExpr.const c ls).mkApp as))
    (h : env.IsDefEqU U Γ ((VExpr.const c ls).mkApp as) ((VExpr.const c' ls').mkApp as')) :
    c = c' ∧ List.Forall₂ (· ≈ ·) ls ls' ∧ List.Forall₂ (env.IsDefEqU U Γ) as as' :=
  let _inst := VEnv.paramsOfWF henv U hwf
  @VEnv.IsDefEq.constApp_inv _inst Γ c c' ls ls' as as' h.choose hΓ
    (hc.patFreeHead henv hwf) (hc'.patFreeHead henv hwf) hnp h.choose_spec

/-! ### §6.1 The three conjuncts -/

theorem rigidConstAppInv_of_wf {env : VEnv} (henv : env.WF) (U : Nat) :
    env.RigidConstAppInv U := fun hΓ hc hnp h =>
  (constApp_inv_np_of_patWF henv U (patWF_of_wf henv U) hΓ hc hc hnp h).2

theorem rigidConstPiDisj_of_wf {env : VEnv} (henv : env.WF) (U : Nat) :
    env.RigidConstPiDisj U := fun hΓ hc =>
  const_forallE_inv_of_patWF henv U (patWF_of_wf henv U) hΓ hc

theorem rigidConstSortDisj_of_wf {env : VEnv} (henv : env.WF) (U : Nat) :
    env.RigidConstSortDisj U := fun hΓ hc =>
  const_sort_inv_of_patWF henv U (patWF_of_wf henv U) hΓ hc

/-- `RigidConstPrice.lean`'s three conjuncts, together, at every well-formed environment. -/
theorem constFamily_of_wf {env : VEnv} (henv : env.WF) (U : Nat) :
    env.RigidConstAppInv U ∧ env.RigidConstPiDisj U ∧ env.RigidConstSortDisj U :=
  ⟨rigidConstAppInv_of_wf henv U, rigidConstPiDisj_of_wf henv U, rigidConstSortDisj_of_wf henv U⟩

/-! ### §6.2 …instantiated at the named open instance

`rcEnv0` is `RigidConstPrice.lean`'s own non-degenerate witness: one axiom `rcRF : Sort 1`, no
δ-rules, `VEnv.WF` by `wf_rcEnv0`, every head rule-free, the spine typeable.  Instantiating
rather than admiring, per `docs/vacuity-ledger.md` §0. -/
theorem constFamily_at_rcEnv0 (U : Nat) :
    rcEnv0.RigidConstAppInv U ∧ rcEnv0.RigidConstPiDisj U ∧ rcEnv0.RigidConstSortDisj U :=
  constFamily_of_wf wf_rcEnv0 U

/-- …and it *says* something there: `rcRF.{0}` is not definitionally equal to `Prop`, at the
environment `RigidConstPrice.lean` §6.1 names.  Compare `not_rigidConstSortDisj_rcSortEnv`,
which refutes the same conjunct once two δ-rules are hung on a hub. -/
theorem rcEnv0_spine_ne_prop :
    ¬ rcEnv0.IsDefEqU 0 [] (rcSpine .zero) (.sort .zero) := by
  have H : rcEnv0.RigidConstSortDisj 0 := rigidConstSortDisj_of_wf wf_rcEnv0 0
  exact H (Γ := []) (c := rcRF) (ls := [.zero]) (as := []) trivial (ruleFreeHead_rcEnv0 _)

section Audit
#print axioms Lean4Lean.VEnv.constApp_inv_np_of_patWF
#print axioms Lean4Lean.VEnv.constFamily_of_wf
#print axioms Lean4Lean.VEnv.constFamily_at_rcEnv0
#print axioms Lean4Lean.VEnv.rcEnv0_spine_ne_prop
end Audit

/-! ## §7 Measurements

Hole cones, transitive over type **and** value, `allowOpaque := true`, seeded in a `/tmp` probe
(`/tmp/noconf-cone.lean`, the body of `scripts/hole-cone.lean` with these seeds — `scripts/` is
not this stream's to edit).  Population: the import closure of this module, 7 500-odd constants.

| seed | cone | holes in cone |
| --- | --- | --- |
| `not_isProof_of_hasType_sort` | 600 | none |
| `ConstNoConfNP.constNoConf_of_propAgreeOn` | 2138 | none |
| `isProof_ncPropEnv_lhs` | 3575 | none |
| `ncPropEnv_link` | 3585 | none |
| `wf_ncPropEnv` | 3586 | none |
| `not_constNoConfUG_ncPropEnv` | 3600 | none |
| `ncPropEnv_P_not_isProof_of_propAgreeOn` | 3569 | none |
| `IsType.not_isProof` | 3456 | `forallE_inv_stratified` |
| `ConstNoConfNP.constNoConf` | 3464 | `forallE_inv_stratified` |
| `not_isType_ncPropEnv_lhs` | 5180 | `forallE_inv_stratified` |
| `IsDefEq.constApp_inv` (the tree's) | 4446 | `weakN_iff`, `forallE_inv_stratified`, `WF.rigidShapeUniqNS`, `NormalEq.descend` |
| `constApp_inv_np_of_patWF` | 7328 | the same four |
| `constApp_inv_of_patWF` (the tree's) | 7329 | the same four |
| `constNoConfNP_of_patWF` | 7329 | the same four |
| `constNoConf_of_patWF` (the tree's) | 7331 | the same four |
| `constNoConfNP_of_wf` | 7491 | the same four |
| `constNoConf_of_wf` (the tree's) | 7493 | the same four |
| `rigidConstNoConfNP_of_wf` | 7493 | the same four |
| `rigidConstNoConf_of_wf` | 7496 | the same four |
| `spineVarAppDisjT_wf` | 7634 | the same four |
| `constFamily_of_wf`, `constFamily_at_rcEnv0` | 7517, 7526 | the same four |

Three things to read off, in order of how much they change:

1. **The `¬ IsProof` form is not more expensive than the `IsType` form — it is two constants
   *cheaper*, with an identical hole set** (7491 vs 7493, 7329 vs 7331).  The difference is
   exactly the `IsType.not_isProof` application the wrapper makes.  So the guard was never a
   strength question at all; the `IsType` form is the `¬ IsProof` form plus a paid conversion.
2. **`WF.rigidShapeUniqNS` — hole B — is in the cone of everything routed through
   `church_rosser`.**  That is the machine-checked form of `RigidNodeCircle.lean`'s "circular"
   annotation, and it is why §6 is not progress and why `rigidConstNoConf_of_wf` must not be fed
   back into the bridge.
3. **The guard *bridge* is hole-free** (`ConstNoConfNP.constNoConf_of_propAgreeOn`, 2138, no
   holes) while the *row* is not.  Those are separate facts and were run together in
   `docs/handoff-shapeindep.md` §3.
-/

end VEnv
end Lean4Lean
