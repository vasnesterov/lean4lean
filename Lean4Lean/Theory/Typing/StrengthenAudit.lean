import Lean4Lean.Theory.Typing.StrengthenPiProp
import Lean4Lean.Theory.Typing.StrengthenVerdict

/-!
# Round 8: the neutral `trans` residual, **bounded both ways**, and two routes closed

Target: the forward direction of `VEnv.IsDefEqU.weakN_iff` (`Theory/Typing/UniqueTyping.lean:187`,
the `sorry` at `:189`; **198 transitive users**, measured by `scripts/sorry-census.lean`).
Round 5 (`StrengthenNarrow.lean`) reduced it to `PiDescend` plus the `trans` residual with a
non-lift middle term; rounds 6 and 7 (`NormalEqStrengthen.lean` §1c, `StrengthenPiProp.lean`)
sliced that residual by the *type* of its endpoints, leaving
`TransStrengtheningNarrowNeutral` — the residual at a `T` that is neither a sort nor a Π and
is not a Prop.  **Nothing here closes the hole either.**  What this file does is

* remove `.lam` from the surviving type shapes, at **no hole cost** (§1–§2) — round 7 believed
  this cost a new hole, and that was wrong (see "Corrections" below);
* decide round 7's Prop side condition *exactly*, as a condition on the type's universe (§3);
* **bound the residual both ways** in the sense of `docs/vacuity-ledger.md` §5, check 2: its
  hypothesis set is jointly satisfiable (§5, bound 1) and it holds at a well-formed environment
  (§5, bound 3) — and, in between, its *conclusion* is not free (§5, bound 2);
* run the collapse test on its own witness (§6);
* close two routes: the premise-free `proofIrrel` collapse of round 7 §1 has **no** analogue at
  a neutral type (§5 bound 2), and **no further restriction on the middle term** can sharpen
  the residual, because the middle term is always convertible to a lift and "it may be taken
  to be a lift" is a triviality (§8).

## Corrections to the round-7/round-8 briefs

1. **`IsDefEqU.sort_forallE_inv` is not open.**  The brief said excluding `.lam` from
   `VExpr.NeutralTy` "needs `IsDefEqU.sort_forallE_inv`, itself open — so excluding it would
   *add* a hole".  `Theory/Typing/Injectivity.lean:1252` proves it; that file's only two holes
   are `WF.rigidShapeUniqNS` (`:1046`) and `IsDefEqU.forallE_inv_stratified` (`:261`), which are
   already in the cone of every round-6/7 result.  Measured: `IsType.not_lam` has cone **3594**
   with exactly those two — the *same pair and the same size* as
   `TypingStrengthening.hasType_inv`, round 5's baseline.  So `.lam` comes off for free.
2. **`VEnv.SortUniq` is not open either.**  `WF.sortUniq'` (`Injectivity.lean:556`) proves it
   from `forallE_inv_stratified` alone — cone 3404, **one** hole, not two.  That is what makes
   §3 possible, and §3 is what makes the Prop side condition checkable rather than merely
   assumed.
3. Census: 13 declarations directly contain `sorryAx` (not 18/19); `IsDefEqU.weakN_iff` has 198
   transitive users, which the brief has right.  `NormalEqStrengthen.lean`'s docstring still says
   131 and `StrengthenNarrow.lean`'s still says `UniqueTyping.lean:172`/`:174`; both are stale.
4. The round-6 `ChurchRosser.lean` edit is **still unapplied** and is not needed by anything
   here.

## What is claimed, and what is not

**§2 is a tidy-up, not a narrowing of content.**  `IsType.not_lam` says the `.lam` entry of
`VExpr.NeutralTy` was *vacuous*: there is no `Γ ⊢ e : .lam A c` at all, so removing `.lam`
deletes no instance a prover would ever face.  It is worth doing because the brief was carrying
the opposite belief — that the removal cost a hole — but it buys no content.  The content of
this round is §3, §5, §6, §7 and §8.

`TransStrengtheningNarrowSpine` (§2) is **narrower in scope** than round 7's residual and
*equivalent to it* given the typing half (§2's two directions), exactly as round 7's was
equivalent to round 5's.  **No strictness is claimed**, and §8 explains why none should be
expected from this direction: by `mid_defeq_lift` the residual's middle term is always
convertible to a lifted term, so every restriction rounds 5–8 have imposed on `b` is a
restriction on *representatives*, not on conversion classes.  The one thing that would restrict
the class is a normalisation result, i.e. confluence — which is entry (1) of the cycle
`ParRedKWeakN.lean` measures.

## Measured cones (`scripts/hole-cone.lean`'s walker: `deps` over type AND value with
`allowOpaque := true`)

| declaration | cone | reaches `weakN_iff` | other holes |
| --- | --- | --- | --- |
| `VExpr.NeutralTyNL.neutralTy` | 381 | no | **none** |
| `TransStrengtheningNarrowNeutral.spine` (§2, trivial direction) | 420 | no | **none** |
| `IsType.not_lam` (§1) | 3594 | no | `forallE_inv_stratified`, `rigidShapeUniqNS` |
| `TransStrengtheningNarrowSpine.neutral` (§2) | 3607 | no | same two |
| `strengtheningTarget_iff_piDescend_spine` (§2, capstone) | 3770 | no | same two |
| `hasType_sort_zero_iff_of_sortUniq` (§3, `SortUniq` hypothesised) | 2113 | no | **none** |
| `hasType_sort_zero_iff` (§3, discharged) | 3406 | no | `forallE_inv_stratified` only |
| `auditT_beta`, `auditE2_beta`, `auditB_beta` (§4) | 603/611/608 | no | **none** |
| `auditPi_hasType` (§4) | 1483 | no | **none** |
| `auditB_not_skips`, `audit_premise₁`, `audit_premise₂` (§4–§5) | 412/618/623 | no | **none** |
| `transStrengtheningNarrowSpine_hyps_satisfiable` (bound 1) | 3456 | no | `forallE_inv_stratified` only |
| `no_neutral_proofIrrel` (bound 2) | 3576 | no | `forallE_inv_stratified`, `rigidShapeUniqNS` |
| `StrengtheningTarget.narrowSpine`, `exists_wf_narrowSpine` (bound 3) | 3445/3483 | no | `forallE_inv_stratified` only |
| `audit_stripped_entry_inhabited`, `audit_witness_is_substitution_case` (§6) | 609/3198 | no | **none** |
| `hasType_constSpine_shape` (§7) | 3617 | no | `forallE_inv_stratified`, `rigidShapeUniqNS` |
| `mid_defeq_lift`, `midNormalise_trivial` (§8) | 144/150 | no | **none** |

Baselines measured in the same run: `TypingStrengthening.hasType_inv` 3594 (two holes),
`TransStrengtheningNarrowNeutral.transNarrowT` 3655 (two), round 7's capstone
`strengtheningTarget_iff_piDescend_neutral` 3725 (two), `TransStrengtheningNarrowAt.at_pi` 3228
(hole-free), `IsDefEqU.sort_forallE_inv` 3558 (two), `WF.sortUniq'` 3404 (one),
`exists_univInhabEnv` 3228 (**hole-free**).

**Nothing in this file reaches `IsDefEqU.weakN_iff`**, so none of it is circular with the
statement it is about.  §4, §6 and §8 are fully `sorryAx`-free (`#print axioms` gives
`[propext]`, `[propext, Quot.sound]` or `[propext, Classical.choice, Quot.sound]`), as is §3's
`SortUniq`-hypothesised core.

`#print axioms`, verbatim:

    IsType.not_lam                                 [propext, sorryAx, Classical.choice, Quot.sound]
    TransStrengtheningNarrowSpine.neutral          [propext, sorryAx, Classical.choice, Quot.sound]
    strengtheningTarget_iff_piDescend_spine        [propext, sorryAx, Classical.choice, Quot.sound]
    hasType_sort_zero_iff_of_sortUniq              [propext, Quot.sound]
    hasType_sort_zero_iff                          [propext, sorryAx, Classical.choice, Quot.sound]
    transStrengtheningNarrowSpine_hyps_satisfiable [propext, sorryAx, Classical.choice, Quot.sound]
    no_neutral_proofIrrel                          [propext, sorryAx, Classical.choice, Quot.sound]
    exists_wf_narrowSpine                          [propext, sorryAx, Classical.choice, Quot.sound]
    audit_witness_is_substitution_case              [propext, Classical.choice, Quot.sound]
    hasType_constSpine_shape                       [propext, sorryAx, Classical.choice, Quot.sound]
    auditPi_hasType, auditB_not_skips              [propext, Quot.sound]
    audit_premise₁, audit_premise₂                 [propext]
    mid_defeq_lift, midNormalise_trivial           [propext]

Every `sorryAx` above is inherited from `forallE_inv_stratified` / `rigidShapeUniqNS`; none is
introduced here.

Census: 13 before, 13 after.  No `sorry`, no `axiom`, no `native_decide`, no
`@[implemented_by]` is added here.

This module is a leaf that nothing imports, so it is invisible to
`scripts/sorry-census.lean` and `scripts/dup-names.lean` until
`Lean4Lean/Experimental/ConeJoin.lean` gains

    import Lean4Lean.Theory.Typing.StrengthenAudit

which this module does not add, because that file is owned elsewhere.  It contains no `sorry`,
so the census is not being under-reported; the duplicate-name check was run separately over the
`Verify.Guard` cone plus this module (clean) and by a name scan over all of `Lean4Lean/`.
-/
namespace Lean4Lean

namespace VExpr

/-- Neutral **and** not a `lam`. -/
def NeutralTyNL : VExpr → Prop
  | .bvar _ => True
  | .const _ _ => True
  | .app _ _ => True
  | _ => False

theorem NeutralTyNL.bvar {i : Nat} : (VExpr.bvar i).NeutralTyNL := trivial
theorem NeutralTyNL.const {c ls} : (VExpr.const c ls).NeutralTyNL := trivial
theorem NeutralTyNL.app {f a} : (VExpr.app f a).NeutralTyNL := trivial

theorem NeutralTyNL.neutralTy : ∀ {T : VExpr}, T.NeutralTyNL → T.NeutralTy
  | .bvar _, _ => trivial
  | .const .., _ => trivial
  | .app .., _ => trivial

end VExpr

namespace VEnv

variable {env : VEnv} {U : Nat} {Γ Γ' : List VExpr}

/-! ## 1. `.lam` is not a type -/

/-- **A `lam` is never a type.** -/
theorem IsType.not_lam (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U)) {A c : VExpr} :
    ¬ env.IsType U Γ (.lam A c) := by
  rintro ⟨u, hu⟩
  have ⟨⟨_, hA⟩, _, hc⟩ := HasType.lam_inv henv.ordered hΓ hu
  exact IsDefEqU.sort_forallE_inv henv hΓ
    ((IsDefEq.lamDF hA hc).uniqU henv hΓ hu).symm

/-! ## 2. The residual, narrowed to a spine-headed type -/

/-- **The residual of round 7, with `.lam` removed from the admissible type shapes.** -/
def TransStrengtheningNarrowSpine (env : VEnv) (U : Nat) : Prop :=
  ∀ {n k : Nat} {Γ Γ' : List VExpr} {e1 e2 b T : VExpr}, Ctx.LiftN n k Γ Γ' →
    OnCtx Γ (env.IsType U) → OnCtx Γ' (env.IsType U) →
    ¬ b.Skips n k → T.NeutralTyNL → ¬ env.HasType U Γ T (.sort .zero) →
    env.HasType U Γ e1 T → env.HasType U Γ e2 T →
    env.IsDefEq U Γ' (e1.liftN n k) b (T.liftN n k) →
    env.IsDefEq U Γ' b (e2.liftN n k) (T.liftN n k) →
    env.IsDefEq U Γ e1 e2 T

/-- Dropping a hypothesis: the spine residual is a consequence of round 7's neutral one. -/
theorem TransStrengtheningNarrowNeutral.spine (H : TransStrengtheningNarrowNeutral env U) :
    TransStrengtheningNarrowSpine env U :=
  fun W hΓ hΓ' hb hT hp h1 h2 h3 h4 => H W hΓ hΓ' hb hT.neutralTy hp h1 h2 h3 h4

/-- **The `.lam` case of round 7's residual is vacuous.** -/
theorem TransStrengtheningNarrowSpine.neutral (henv : VEnv.WF env)
    (H : TransStrengtheningNarrowSpine env U) : TransStrengtheningNarrowNeutral env U := by
  intro n k Γ Γ' e1 e2 b T W hΓ hΓ' hb hTn hp hT hT2 h1 h2
  match T, hTn with
  | .bvar _, _ => exact H W hΓ hΓ' hb .bvar hp hT hT2 h1 h2
  | .const .., _ => exact H W hΓ hΓ' hb .const hp hT hT2 h1 h2
  | .app .., _ => exact H W hΓ hΓ' hb .app hp hT hT2 h1 h2
  | .lam .., _ => exact absurd (hT.isType henv.ordered hΓ) (IsType.not_lam henv hΓ)

/-- **Capstone.** -/
theorem strengtheningTarget_iff_piDescend_spine (henv : VEnv.WF env) :
    StrengtheningTarget env U ↔
      PiDescend env U ∧ TransStrengtheningNarrowSpine env U := by
  refine ⟨fun H => ?_, fun ⟨HP, HN⟩ => ?_⟩
  · have ⟨h1, h2⟩ := (strengtheningTarget_iff_piDescend_neutral henv).1 H
    exact ⟨h1, h2.spine⟩
  · exact (strengtheningTarget_iff_piDescend_neutral henv).2 ⟨HP, HN.neutral henv⟩

/-! ## 3. The Prop side condition is exactly a level condition -/

/-- **Round 7's Prop side condition, decided by the type's level.** -/
theorem hasType_sort_zero_iff_of_sortUniq (hord : Ordered env) (hsu : env.SortUniq U)
    (hΓ : OnCtx Γ (env.IsType U)) {T : VExpr} {u : VLevel}
    (h : env.HasType U Γ T (.sort u)) :
    env.HasType U Γ T (.sort .zero) ↔ u ≈ .zero := by
  have hu : u.WF U := IsType.sort_inv hord (h.isType hord hΓ)
  refine ⟨fun hp => hsu hΓ hu trivial h hp, fun hz => ?_⟩
  exact IsDefEq.defeqDF (IsDefEq.sortDF hu trivial hz) h

/-- The same with `SortUniq` discharged by `WF.sortUniq'`. -/
theorem hasType_sort_zero_iff (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    {T : VExpr} {u : VLevel} (h : env.HasType U Γ T (.sort u)) :
    env.HasType U Γ T (.sort .zero) ↔ u ≈ .zero :=
  hasType_sort_zero_iff_of_sortUniq henv.ordered (WF.sortUniq' henv) hΓ h

/-! ## 4. The witness data -/

/-- A neutral (`.app`-headed) type convertible with `Sort 1`. -/
def auditT : VExpr := .app (.lam (.sort (.succ .zero)) (.sort (.succ .zero))) (.sort .zero)
/-- `Prop`, the first inhabitant of `auditT`. -/
def auditE1 : VExpr := .sort .zero
/-- A `.app`-headed term convertible with `Prop`. -/
def auditE2 : VExpr := .app (.lam (.sort (.succ .zero)) (.bvar 0)) (.sort .zero)
/-- The middle term: a redex whose argument is the stripped variable. -/
def auditB : VExpr := .app (.lam (.sort .zero) (.sort .zero)) (.bvar 0)
/-- `Prop -> Prop`, the second inhabitant of `auditT`. -/
def auditPi : VExpr := .forallE (.sort .zero) (.sort .zero)

theorem auditT_beta :
    env.IsDefEq U Γ auditT (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) := by
  have hb : env.HasType U (VExpr.sort (.succ .zero) :: Γ) (.sort (.succ .zero))
      (.sort (.succ (.succ .zero))) := HasType.sort trivial
  have ha : env.HasType U Γ (.sort .zero) (.sort (.succ .zero)) := HasType.sort trivial
  simpa [auditT, VExpr.inst] using IsDefEq.beta hb ha

theorem auditE2_beta : env.IsDefEq U Γ auditE2 (.sort .zero) (.sort (.succ .zero)) := by
  have hb : env.HasType U (VExpr.sort (.succ .zero) :: Γ) (.bvar 0) (.sort (.succ .zero)) := by
    have h : env.HasType U (VExpr.sort (.succ .zero) :: Γ) (.bvar 0)
        ((VExpr.sort (.succ .zero)).lift) := .bvar .zero
    simpa [VExpr.lift, VExpr.liftN] using h
  have ha : env.HasType U Γ (.sort .zero) (.sort (.succ .zero)) := HasType.sort trivial
  simpa [auditE2, VExpr.inst, VExpr.instVar] using IsDefEq.beta hb ha

theorem auditB_beta :
    env.IsDefEq U (VExpr.sort .zero :: Γ) auditB (.sort .zero) (.sort (.succ .zero)) := by
  have hb : env.HasType U (VExpr.sort .zero :: VExpr.sort .zero :: Γ) (.sort .zero)
      (.sort (.succ .zero)) := HasType.sort trivial
  have ha : env.HasType U (VExpr.sort .zero :: Γ) (.bvar 0) (.sort .zero) := by
    have h : env.HasType U (VExpr.sort .zero :: Γ) (.bvar 0) ((VExpr.sort .zero).lift) :=
      .bvar .zero
    simpa [VExpr.lift, VExpr.liftN] using h
  simpa [auditB, VExpr.inst] using IsDefEq.beta hb ha

theorem auditPi_hasType : env.HasType U Γ auditPi (.sort (.succ .zero)) := by
  have h1 : env.IsDefEq U Γ (.sort .zero) (.sort .zero) (.sort (.succ .zero)) :=
    .sortDF trivial trivial rfl
  have h2 : env.IsDefEq U (VExpr.sort .zero :: Γ) (.sort .zero) (.sort .zero)
      (.sort (.succ .zero)) := .sortDF trivial trivial rfl
  have hc : env.IsDefEq U Γ (.sort (.imax (.succ .zero) (.succ .zero)))
      (.sort (.succ .zero)) (.sort (.succ (.imax (.succ .zero) (.succ .zero)))) :=
    .sortDF ⟨trivial, trivial⟩ trivial
      (by simp [VLevel.equiv_def, VLevel.eval, Lean.Nat.imax])
  exact IsDefEq.defeqDF hc (IsDefEq.forallEDF h1 h2)

/-! ## 5. The witness context, and the two bounds -/

/-- The witness lifting: strip one entry, `Prop`, off the front of the empty context. -/
theorem audit_onCtx : OnCtx [VExpr.sort .zero] (env.IsType U) :=
  ⟨trivial, .succ .zero, HasType.sort trivial⟩

theorem auditT_liftN : auditT.liftN 1 0 = auditT := by simp [auditT, VExpr.liftN]
theorem auditE1_liftN : auditE1.liftN 1 0 = auditE1 := by simp [auditE1, VExpr.liftN]
theorem auditE2_liftN : auditE2.liftN 1 0 = auditE2 := by
  simp [auditE2, VExpr.liftN, liftVar]

theorem auditB_not_skips : ¬ auditB.Skips 1 0 := by
  simp [VExpr.skips_iff, VExpr.Skips', auditB]

theorem auditE1_hasType : env.HasType U Γ auditE1 auditT :=
  IsDefEq.defeqDF auditT_beta.symm (HasType.sort trivial)

theorem auditE2_hasType : env.HasType U Γ auditE2 auditT :=
  IsDefEq.defeqDF auditT_beta.symm auditE2_beta.hasType.1

theorem auditPi_hasType_auditT : env.HasType U Γ auditPi auditT :=
  IsDefEq.defeqDF auditT_beta.symm auditPi_hasType

theorem auditT_not_prop (henv : VEnv.WF env) : ¬ env.HasType U [] auditT (.sort .zero) := by
  rw [hasType_sort_zero_iff henv (Γ := []) trivial (auditT_beta (Γ := [])).hasType.1]
  simp [VLevel.equiv_def, VLevel.eval]

theorem audit_premise₁ :
    env.IsDefEq U [VExpr.sort .zero] (auditE1.liftN 1 0) auditB (auditT.liftN 1 0) := by
  rw [auditE1_liftN, auditT_liftN]
  exact (IsDefEq.defeqDF auditT_beta.symm auditB_beta).symm

theorem audit_premise₂ :
    env.IsDefEq U [VExpr.sort .zero] auditB (auditE2.liftN 1 0) (auditT.liftN 1 0) := by
  rw [auditE2_liftN, auditT_liftN]
  exact IsDefEq.defeqDF auditT_beta.symm (auditB_beta.trans auditE2_beta.symm)

/-- **Bound 1: the hypothesis set of the spine residual is jointly satisfiable.** -/
theorem transStrengtheningNarrowSpine_hyps_satisfiable :
    ∃ (env : VEnv) (U n k : Nat) (Γ Γ' : List VExpr) (e1 e2 b T : VExpr),
      VEnv.WF env ∧ Ctx.LiftN n k Γ Γ' ∧ OnCtx Γ (env.IsType U) ∧
      OnCtx Γ' (env.IsType U) ∧ ¬ b.Skips n k ∧ T.NeutralTyNL ∧
      ¬ env.HasType U Γ T (.sort .zero) ∧
      env.HasType U Γ e1 T ∧ env.HasType U Γ e2 T ∧
      env.IsDefEq U Γ' (e1.liftN n k) b (T.liftN n k) ∧
      env.IsDefEq U Γ' b (e2.liftN n k) (T.liftN n k) ∧ e1 ≠ e2 :=
  ⟨VEnv.empty, 0, 1, 0, [], [VExpr.sort .zero], auditE1, auditE2, auditB, auditT,
   ⟨[], .empty⟩, .one, trivial, audit_onCtx, auditB_not_skips, .app,
   auditT_not_prop ⟨[], .empty⟩, auditE1_hasType, auditE2_hasType,
   audit_premise₁, audit_premise₂, by simp [auditE1, auditE2]⟩

/-- **Bound 2: the conclusion is not free.** -/
theorem no_neutral_proofIrrel :
    ∃ (env : VEnv) (U : Nat) (Γ : List VExpr) (e1 e2 T : VExpr),
      VEnv.WF env ∧ OnCtx Γ (env.IsType U) ∧ T.NeutralTyNL ∧
      ¬ env.HasType U Γ T (.sort .zero) ∧
      env.HasType U Γ e1 T ∧ env.HasType U Γ e2 T ∧ ¬ env.IsDefEqU U Γ e1 e2 :=
  ⟨VEnv.empty, 0, [], auditE1, auditPi, auditT, ⟨[], .empty⟩, trivial, .app,
   auditT_not_prop ⟨[], .empty⟩, auditE1_hasType, auditPi_hasType_auditT,
   IsDefEqU.sort_forallE_inv ⟨[], .empty⟩ trivial⟩

/-- **Bound 3: the residual holds at a well-formed environment.** -/
theorem StrengtheningTarget.narrowSpine (henv : VEnv.WF env) (H : StrengtheningTarget env U) :
    TransStrengtheningNarrowSpine env U :=
  fun W hΓ hΓ' _ _ _ hT _ h1 h2 => (H W hΓ' ⟨_, h1.trans h2⟩).of_l henv hΓ hT

theorem exists_wf_narrowSpine :
    ∃ env : VEnv, VEnv.WF env ∧ ∀ U, TransStrengtheningNarrowSpine env U :=
  have ⟨env, henv, H⟩ := Lean4Lean.exists_univInhabEnv
  ⟨env, henv, fun U => StrengtheningTarget.narrowSpine henv (H U)⟩

/-! ## 6. Collapse test on the bound-1 witness -/

theorem audit_stripped_entry_inhabited :
    env.HasType U [] (.forallE (.sort .zero) (.bvar 0)) (.sort .zero) :=
  Lean4Lean.allProp_isProp

theorem audit_witness_is_substitution_case (henv : VEnv.WF env)
    (h : env.IsDefEqU U [VExpr.sort .zero] (auditE1.liftN 1 0) (auditE2.liftN 1 0)) :
    env.IsDefEqU U [] auditE1 auditE2 :=
  IsDefEqU.strengthen_of_instN henv.ordered (Γ₀ := []) (A₀ := .sort .zero)
    (e₀ := .forallE (.sort .zero) (.bvar 0)) .zero audit_stripped_entry_inhabited h

/-! ## 7. The endpoints at the case where the real instances live -/

/-- **At a rule-free `const`-headed type nothing is a sort, a Π or a `lam`.** -/
theorem hasType_constSpine_shape (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    {c : Lean.Name} {ls : List VLevel} {as : List VExpr} (hrigid : RuleFreeHead env c)
    {e : VExpr} (he : env.HasType U Γ e ((VExpr.const c ls).mkApp as)) :
    (∀ v, e ≠ .sort v) ∧ (∀ A B, e ≠ .forallE A B) ∧ (∀ A d, e ≠ .lam A d) := by
  refine ⟨fun v h => ?_, fun A B h => ?_, fun A d h => ?_⟩
  · subst h
    exact IsDefEqU.const_sort_inv henv hΓ hrigid
      ((HasType.sort (IsDefEq.sort_inv_l henv.ordered he)).uniqU henv hΓ he).symm
  · subst h
    have ⟨⟨_, hA⟩, _, hB⟩ := HasType.forallE_inv henv.ordered he
    exact IsDefEqU.const_sort_inv henv hΓ hrigid
      ((IsDefEq.forallEDF hA hB).uniqU henv hΓ he).symm
  · subst h
    have ⟨⟨_, hA⟩, _, hd⟩ := HasType.lam_inv henv.ordered hΓ he
    exact IsDefEqU.const_forallE_inv henv hΓ hrigid
      ((IsDefEq.lamDF hA hd).uniqU henv hΓ he).symm

/-! ## 8. Why no further restriction on the middle term can help -/

/-- **The middle term is always convertible to a lift.** -/
theorem mid_defeq_lift {n k : Nat} {e1 b T : VExpr}
    (h1 : env.IsDefEq U Γ' (e1.liftN n k) b (T.liftN n k)) :
    ∃ c : VExpr, env.IsDefEqU U Γ' b (c.liftN n k) := ⟨e1, _, h1.symm⟩

/-- **"The middle term may be taken to be a lift" is a triviality.** -/
def MidNormalise (env : VEnv) (U : Nat) : Prop :=
  ∀ {n k : Nat} {Γ' : List VExpr} {e1 e2 b T : VExpr},
    env.IsDefEq U Γ' (e1.liftN n k) b (T.liftN n k) →
    env.IsDefEq U Γ' b (e2.liftN n k) (T.liftN n k) →
    ∃ b₀ : VExpr, env.IsDefEq U Γ' (e1.liftN n k) (b₀.liftN n k) (T.liftN n k) ∧
      env.IsDefEq U Γ' (b₀.liftN n k) (e2.liftN n k) (T.liftN n k)

theorem midNormalise_trivial : MidNormalise env U :=
  fun h1 h2 => ⟨_, h1.trans h2, h2.hasType.2⟩

end VEnv
end Lean4Lean
