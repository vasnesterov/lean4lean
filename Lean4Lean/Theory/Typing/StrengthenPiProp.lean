import Lean4Lean.Theory.Typing.NormalEqStrengthen

/-!
# Round 7: the `trans` residual, narrowed by the *type* of its endpoints

Target: the forward direction of `VEnv.IsDefEqU.weakN_iff`
(`Theory/Typing/UniqueTyping.lean:187`, 136 transitive users).  **Nothing here closes it.**
What this file does is shrink the one obligation round 5 left
(`StrengthenNarrow.lean`'s `TransStrengtheningNarrow`) by **three type-shape slices**, two of
them new:

| shared type `T` of the residual's endpoints | disposed of by | status |
| --- | --- | --- |
| `T = .sort u` (the endpoints are *types*) | `NormalEqStrengthen.lean` §1c `at_sort` | round 6 |
| `Γ ⊢ T : .sort .zero` (the endpoints are *proofs*) | §1 here, `at_prop` | **new** |
| `T = .forallE A B` (the endpoints are *functions*) | §2 here, `at_pi`, by η | **new** |

§3 then runs those three as a **structural induction on `T`**, leaving
`TransStrengtheningNarrowNeutral`: the residual restricted to a `T` that is neither a sort nor
a Π *and* is not a Prop — i.e. to endpoints that are data at a `bvar`/`const`/`app`/`lam`-headed
type.  Capstone: `StrengtheningTarget ↔ PiDescend ∧ TransStrengtheningNarrowNeutral`
(`strengtheningTarget_iff_piDescend_neutral`), which replaces round 5's
`StrengtheningTarget.iff_piDescend_narrow` by an equivalence whose second conjunct is
**narrower in scope**: three families of instances are excluded from it.

*Not* claimed: that `TransStrengtheningNarrowNeutral` is strictly weaker than
`TransStrengtheningNarrow` as a `Prop`.  It is weaker *given* `TypingStrengthening` (that is
`transNarrowT` plus `TransStrengtheningNarrowT.neutral`, both here); whether the implication is
strict is not proved, and given `PiDescend` sits next to it in the capstone the two conjunctions
are equivalent.  What is proved is that the *obligation* excludes the sort, Π and Prop
instances, which is a narrowing of what a prover has to handle, not a logical weakening of the
conjunction.

## Honest accounting

* **This narrows scope, it does not weaken content.**  The remaining case is where all the
  real instances live: a conversion between two terms of an inductive type such as `Nat` has a
  `const`-headed, non-Prop, non-Π, non-sort type.  §2's η step is a genuine reduction (it
  reduces the residual at `Π A B` to the residual at `B`, structurally smaller), and §1 is a
  genuine *collapse* (proof-typed instances need no upstairs hypothesis at all), but neither
  touches the neutral case.  Anyone reading this as "the hole is nearly closed" is reading it
  wrong.
* §1's collapse is stronger than a slice: `IsDefEqU.strengthen_at_prop` needs **no conversion
  upstairs**, only that both endpoints are lifted terms of a common Prop type.  So
  strengthening is not merely provable on proofs, it is *vacuous* on them.
* §2 consumes *nothing*: measured hole-free (see the table below), so it does not even need
  the typing half.  `hT : Γ ⊢ e1 : Π A B` is a *hypothesis* of the residual, so the η step never
  has to invert a Π type upstairs.  That is what distinguishes it from `ChurchRosser.lean:1184`'s
  `hasType_app_bvar0`, which is η-shaped too but must *discover* the Π type and therefore does
  appeal to the hole.
* The `NeutralTy` predicate keeps `.lam` for honesty: a `lam`-typed term is presumably
  impossible, but ruling it out needs Π/sort no-confusion, which is not available here.

## Measured cones (the `scripts/hole-cone.lean` walker: `deps` over type AND value with
`allowOpaque := true`, so `.thmInfo` values are not silently empty)

| declaration | cone | reaches `IsDefEqU.weakN_iff` | other holes reached |
| --- | --- | --- | --- |
| `VExpr.Skips.of_lift_succ` | 405 | no | **none** |
| `VExpr.not_skips_eta` | 436 | no | **none** |
| `TransStrengtheningNarrowAt.at_pi` (§2, the Π slice) | 3228 | no | **none** |
| `TransStrengtheningNarrowT.neutral` | 415 | no | **none** |
| `hasType_bvar0_prop` (§4) | 148 | no | **none** |
| `hasType_app_bvar0_of_hasType` (§4) | 3190 | no | **none** |
| `IsDefEqU.strengthen_at_prop` (§1) | 3595 | no | `forallE_inv_stratified`, `WF.rigidShapeUniqNS` |
| `TransStrengtheningNarrow.at_prop` (§1) | 3596 | no | same two |
| `transNarrowT_of_transNarrow` | 3444 | no | `forallE_inv_stratified` |
| `TransStrengtheningNarrowNeutral.transNarrowT` (§3) | 3655 | no | same two |
| `TransStrengtheningNarrowNeutral.transNarrow` (§3) | 3658 | no | same two |
| `strengtheningTarget_iff_piDescend_neutral` (§3, capstone) | 3725 | no | same two |

Reference points, measured in the same run: `TypingStrengthening.hasType_inv` has cone 3594
with the same two holes, `TransStrengtheningNarrow.at_sort` 3604 with the same two, and round
5's `StrengtheningTarget.iff_piDescend_narrow` 3662 with the same two.  So:

* **Nothing here reaches the hole** — the narrowing is not circular with the statement it is
  about.
* §1's Prop slice and §3's induction add *no* holes beyond what `TypingStrengthening.hasType_inv`
  already carries, and the capstone carries exactly round 5's two.  No regression.
* **§2's Π slice is completely hole-free**, `#print axioms` giving only
  `propext, Classical.choice, Quot.sound`.  The η reduction of the residual at `Π A B` to the
  residual at `B` is therefore unconditional: it does not even need the typing half.

`forallE_inv_stratified` and `WF.rigidShapeUniqNS` are the tree's two pervasive non-circular
holes; `NormalEqStrengthen.lean`'s results carry them too.  So nothing here is conditional on the
statement it is about, and nothing here is unconditional either.

This file adds no `sorry`, no `axiom`, no `native_decide` and no `@[implemented_by]`.
-/

namespace Lean4Lean

namespace VExpr

/-! ## 0. Lift facts the slices need -/

/-- `bvar 0` is fixed by a lift strictly above it. -/
theorem liftN_bvar0 {n k : Nat} : (VExpr.bvar 0).liftN n (k+1) = .bvar 0 := by
  simp [VExpr.liftN, liftVar]

/-- The η-expansion of a lift is the lift of the η-expansion, one binder further in. -/
theorem liftN_app_lift_bvar0 {n k : Nat} (e : VExpr) :
    (VExpr.app e.lift (.bvar 0)).liftN n (k+1) = .app (e.liftN n k).lift (.bvar 0) := by
  simp [VExpr.liftN, liftVar, ← VExpr.lift_liftN']

/-- **The non-lift hypothesis survives going under a binder.**  If `b.lift` is in the image of
the lift of `n` variables at `k+1`, then `b` is in the image of the lift of `n` variables at
`k`.  Contrapositively: `¬ b.Skips n k` is preserved by η-expansion, which is what lets §2's η
step hand the *same* middle term to its induction hypothesis. -/
theorem Skips.of_lift_succ {b : VExpr} {n k : Nat}
    (h : (b.lift).Skips n (k+1)) : b.Skips n k := by
  obtain ⟨c, hc⟩ := skips_iff_exists.1 h
  obtain ⟨e', -, rfl⟩ :=
    VExpr.of_liftN_eq_liftN (n1 := n) (e1 := c) (k1 := k) (n2 := 1) (e2 := b) (k2 := 0) hc.symm
  exact .liftN

/-- The η-expanded middle term is not a lift either. -/
theorem not_skips_eta {b : VExpr} {n k : Nat} (h : ¬ b.Skips n k) :
    ¬ (VExpr.app b.lift (.bvar 0)).Skips n (k+1) := by
  intro hs
  rw [skips_iff] at hs
  exact h (Skips.of_lift_succ (skips_iff.2 hs.1))

/-! ## 0b. The type shapes the slices do *not* dispose of -/

/-- Neither a sort nor a Π.  `.lam` is included: a `lam`-typed term is presumably impossible,
but ruling it out needs Π/sort no-confusion, which is out of scope here. -/
def NeutralTy : VExpr → Prop
  | .sort _ => False
  | .forallE _ _ => False
  | _ => True

theorem NeutralTy.bvar {i : Nat} : (VExpr.bvar i).NeutralTy := trivial
theorem NeutralTy.const {c ls} : (VExpr.const c ls).NeutralTy := trivial
theorem NeutralTy.app {f a} : (VExpr.app f a).NeutralTy := trivial
theorem NeutralTy.lam {A b} : (VExpr.lam A b).NeutralTy := trivial

theorem not_neutralTy_sort {u : VLevel} : ¬ (VExpr.sort u).NeutralTy := id
theorem not_neutralTy_forallE {A B : VExpr} : ¬ (VExpr.forallE A B).NeutralTy := id

end VExpr

namespace VEnv

variable {env : VEnv} {U : Nat}

/-! ## 1. The proof slice: strengthening is *vacuous* on proofs

`IsDefEq.proofIrrel` (`Basic.lean:52`) needs nothing but a Prop and two of its inhabitants, all
three **downstairs**.  So for endpoints at a Prop type the residual's two premises are not used
at all: the only work is descending the *typing* of the endpoints, which is the typing half.

This is not just "`proofIrrel` exists": the hypotheses below are about the *lifted* terms
upstairs, and it is `TypingStrengthening` that turns them into typings downstairs. -/

/-- **Strengthening at a Prop type, with no conversion hypothesis.**  If `T` is a Prop
downstairs and both lifted endpoints are typed at `T.liftN n k` upstairs, then the endpoints are
already convertible downstairs — whether or not they are convertible upstairs. -/
theorem IsDefEqU.strengthen_at_prop (henv : VEnv.WF env) (HT : TypingStrengthening env U)
    {n k : Nat} {Γ Γ' : List VExpr} {e1 e2 T : VExpr}
    (W : Ctx.LiftN n k Γ Γ') (hΓ' : OnCtx Γ' (env.IsType U))
    (hp : env.HasType U Γ T (.sort .zero))
    (h1 : env.HasType U Γ' (e1.liftN n k) (T.liftN n k))
    (h2 : env.HasType U Γ' (e2.liftN n k) (T.liftN n k)) :
    env.IsDefEq U Γ e1 e2 T :=
  .proofIrrel hp (HT.hasType_inv henv W hΓ' h1) (HT.hasType_inv henv W hΓ' h2)

/-- **The narrow `trans` residual at a Prop type, from the typing half alone.**  Compare
`TransStrengtheningNarrow.at_sort`, where the two premises are composed by `trans` and fed to
the sort collapse; here they are *discarded*. -/
theorem TransStrengtheningNarrow.at_prop (henv : VEnv.WF env) (HT : TypingStrengthening env U)
    {n k : Nat} {Γ Γ' : List VExpr} {e1 e2 b T : VExpr}
    (W : Ctx.LiftN n k Γ Γ') (hΓ' : OnCtx Γ' (env.IsType U))
    (hp : env.HasType U Γ T (.sort .zero))
    (h1 : env.IsDefEq U Γ' (e1.liftN n k) b (T.liftN n k))
    (h2 : env.IsDefEq U Γ' b (e2.liftN n k) (T.liftN n k)) :
    env.IsDefEqU U Γ e1 e2 :=
  ⟨_, IsDefEqU.strengthen_at_prop henv HT W hΓ' hp h1.hasType.1 h2.hasType.2⟩

/-! ## 2. The typed residual, indexed by the shared type, and the Π slice

To run an induction on the shared type, the conclusion has to *carry* that type and the
statement has to be indexed by it. -/

/-- **The narrow `trans` residual at a fixed type `T`.**  `TransStrengtheningNarrow` with the
endpoints' common type recorded on both sides: `Γ ⊢ e2 : T` in place of `VExpr.WF env U Γ e2`,
and the conclusion at `T` rather than existential.  Both changes are free given the typing half
(`TransStrengtheningNarrowT.transNarrow`, `transNarrowT_of_transNarrow`). -/
def TransStrengtheningNarrowAt (env : VEnv) (U : Nat) (T : VExpr) : Prop :=
  ∀ {n k : Nat} {Γ Γ' : List VExpr} {e1 e2 b : VExpr}, Ctx.LiftN n k Γ Γ' →
    OnCtx Γ (env.IsType U) → OnCtx Γ' (env.IsType U) →
    ¬ b.Skips n k → env.HasType U Γ e1 T → env.HasType U Γ e2 T →
    env.IsDefEq U Γ' (e1.liftN n k) b (T.liftN n k) →
    env.IsDefEq U Γ' b (e2.liftN n k) (T.liftN n k) →
    env.IsDefEq U Γ e1 e2 T

/-- The typed residual: `TransStrengtheningNarrowAt` at every type. -/
def TransStrengtheningNarrowT (env : VEnv) (U : Nat) : Prop :=
  ∀ T : VExpr, TransStrengtheningNarrowAt env U T

/-- The typed form implies `StrengthenNarrow.lean` §1's untyped one, using the typing half to
type the right endpoint.  (The `VExpr.WF env U Γ e2` hypothesis of `TransStrengtheningNarrow`
is not even needed: the type comes from the second premise.) -/
theorem TransStrengtheningNarrowT.transNarrow (henv : VEnv.WF env) (HT : TypingStrengthening env U)
    (H : TransStrengtheningNarrowT env U) : TransStrengtheningNarrow env U := by
  intro n k Γ Γ' e1 e2 b T W hΓ hΓ' hb hT _ h1 h2
  exact ⟨_, H T W hΓ hΓ' hb hT (HT.hasType_inv henv W hΓ' h2.hasType.2) h1 h2⟩

/-- The converse, so that §3's capstone is an equivalence rather than a strengthening of the
obligation.  This is the only place the untyped-to-typed upgrade `IsDefEqU.of_l` is used. -/
theorem transNarrowT_of_transNarrow (henv : VEnv.WF env)
    (H : TransStrengtheningNarrow env U) : TransStrengtheningNarrowT env U := by
  intro T n k Γ Γ' e1 e2 b W hΓ hΓ' hb hT hT2 h1 h2
  exact (H W hΓ hΓ' hb hT ⟨_, hT2⟩ h1 h2).of_l henv hΓ hT

/-- **The Π slice.**  The residual at a function type follows from the residual at the
*codomain*, one binder further in.

η-expand both endpoints and the middle term: each premise weakens into `A.liftN n k :: Γ'` and
applies to `bvar 0`, giving a conversion at the codomain — and `bvar 0` is fixed by the lift
while `e.lift.liftN n (k+1) = (e.liftN n k).lift` (`VExpr.liftN_app_lift_bvar0`), so this is an
instance of the residual at `B` over the extended contexts `A :: Γ` and `A.liftN n k :: Γ'`.
The middle term `b.lift ⬝ 0` still mentions a stripped variable
(`VExpr.not_skips_eta`).  Feeding the result through `lamDF` and the `eta` rule on both sides
recovers `e1 ≡ e2`.

Nothing here appeals to conversion strengthening, nor to the typing half, nor to any hole in
the tree (measured: cone 3228, no holes): the domain `A` and codomain `B` come from the
residual's own hypothesis `Γ ⊢ e1 : Π A B`, so no Π type has to be discovered upstairs. -/
theorem TransStrengtheningNarrowAt.at_pi (henv : VEnv.WF env) {A B : VExpr}
    (H : TransStrengtheningNarrowAt env U B) :
    TransStrengtheningNarrowAt env U (.forallE A B) := by
  intro n k Γ Γ' e1 e2 b W hΓ hΓ' hb hT hT2 h1 h2
  -- the domain is a type, downstairs and upstairs
  have ⟨u, hA⟩ := (IsType.forallE_inv henv.ordered (hT.isType henv.ordered hΓ)).1
  have hA' : env.HasType U Γ' (A.liftN n k) (.sort u) := hA.weakN henv W
  have hΓA : OnCtx (A :: Γ) (env.IsType U) := ⟨hΓ, u, hA⟩
  have hΓA' : OnCtx (A.liftN n k :: Γ') (env.IsType U) := ⟨hΓ', u, hA'⟩
  -- η-expand a conversion at `(forallE A B).liftN n k`, upstairs
  have key : ∀ {x y : VExpr}, env.IsDefEq U Γ' x y ((VExpr.forallE A B).liftN n k) →
      env.IsDefEq U (A.liftN n k :: Γ') (.app x.lift (.bvar 0)) (.app y.lift (.bvar 0))
        (B.liftN n (k+1)) := by
    intro x y h
    have := (h.weakN henv Ctx.LiftN.one).appDF (.bvar .zero)
    rwa [VExpr.instN_bvar0] at this
  -- η-expand a typing, downstairs
  have eta : ∀ {x : VExpr}, env.HasType U Γ x (.forallE A B) →
      env.HasType U (A :: Γ) (.app x.lift (.bvar 0)) B := by
    intro x h
    have := (h.weakN henv Ctx.LiftN.one).appDF (.bvar .zero)
    rwa [VExpr.instN_bvar0] at this
  -- the residual at the codomain
  have q := H (e1 := .app e1.lift (.bvar 0)) (e2 := .app e2.lift (.bvar 0))
    (b := .app b.lift (.bvar 0)) W.succ hΓA hΓA' (VExpr.not_skips_eta hb) (eta hT) (eta hT2)
    (by rw [VExpr.liftN_app_lift_bvar0]; exact key h1)
    (by rw [VExpr.liftN_app_lift_bvar0]; exact key h2)
  -- and back out through `lamDF` and `eta`
  exact hT.eta.symm.trans ((hA.lamDF q).trans hT2.eta)

/-! ## 3. The neutral residual, and the capstone -/

/-- **The residual, narrowed by type shape.**  `TransStrengtheningNarrowT` restricted to a
shared type that is neither a sort nor a Π, and that is not a Prop downstairs.  Both extra
hypotheses are discharged at the call site (`transNarrowT`), so this is a *narrowing of scope*:
it excludes actual instances of the residual rather than adding assumptions to them. -/
def TransStrengtheningNarrowNeutral (env : VEnv) (U : Nat) : Prop :=
  ∀ {n k : Nat} {Γ Γ' : List VExpr} {e1 e2 b T : VExpr}, Ctx.LiftN n k Γ Γ' →
    OnCtx Γ (env.IsType U) → OnCtx Γ' (env.IsType U) →
    ¬ b.Skips n k → T.NeutralTy → ¬ env.HasType U Γ T (.sort .zero) →
    env.HasType U Γ e1 T → env.HasType U Γ e2 T →
    env.IsDefEq U Γ' (e1.liftN n k) b (T.liftN n k) →
    env.IsDefEq U Γ' b (e2.liftN n k) (T.liftN n k) →
    env.IsDefEq U Γ e1 e2 T

/-- The neutral residual is a consequence of the typed residual: two hypotheses dropped. -/
theorem TransStrengtheningNarrowT.neutral (H : TransStrengtheningNarrowT env U) :
    TransStrengtheningNarrowNeutral env U :=
  fun W hΓ hΓ' hb _ _ hT hT2 h1 h2 => H _ W hΓ hΓ' hb hT hT2 h1 h2

/-- **The type-shape induction.**  The neutral residual plus the typing half recovers the whole
typed residual.  Case `sort`: round 6's `at_sort`.  Case `forallE`: §2, at the codomain, which
is where the induction hypothesis is used.  Every remaining case splits off its Prop instances
by §1's `proofIrrel` collapse, which is why `TransStrengtheningNarrowNeutral` may assume
`¬ Γ ⊢ T : Sort 0`. -/
theorem TransStrengtheningNarrowNeutral.transNarrowT (henv : VEnv.WF env)
    (HT : TypingStrengthening env U) (HN : TransStrengtheningNarrowNeutral env U) :
    TransStrengtheningNarrowT env U := by
  intro T
  induction T with
  | sort u =>
    intro n k Γ Γ' e1 e2 b W hΓ hΓ' _ hT _ h1 h2
    exact (TransStrengtheningNarrow.at_sort henv HT W hΓ hΓ' h1 h2).of_l henv hΓ hT
  | forallE A B _ ihB => exact TransStrengtheningNarrowAt.at_pi henv ihB
  -- the four neutral shapes: split off the Prop instances by `proofIrrel`, which given the
  -- endpoints' downstairs typings costs *nothing* -- no `W`, no `HT`, no premise
  | bvar i =>
    intro n k Γ Γ' e1 e2 b W hΓ hΓ' hb hT hT2 h1 h2
    by_cases hp : env.HasType U Γ (.bvar i) (.sort .zero)
    · exact .proofIrrel hp hT hT2
    · exact HN W hΓ hΓ' hb .bvar hp hT hT2 h1 h2
  | const c ls =>
    intro n k Γ Γ' e1 e2 b W hΓ hΓ' hb hT hT2 h1 h2
    by_cases hp : env.HasType U Γ (.const c ls) (.sort .zero)
    · exact .proofIrrel hp hT hT2
    · exact HN W hΓ hΓ' hb .const hp hT hT2 h1 h2
  | app f a _ _ =>
    intro n k Γ Γ' e1 e2 b W hΓ hΓ' hb hT hT2 h1 h2
    by_cases hp : env.HasType U Γ (.app f a) (.sort .zero)
    · exact .proofIrrel hp hT hT2
    · exact HN W hΓ hΓ' hb .app hp hT hT2 h1 h2
  | lam A c _ _ =>
    intro n k Γ Γ' e1 e2 b W hΓ hΓ' hb hT hT2 h1 h2
    by_cases hp : env.HasType U Γ (.lam A c) (.sort .zero)
    · exact .proofIrrel hp hT hT2
    · exact HN W hΓ hΓ' hb .lam hp hT hT2 h1 h2

/-- **The residual, as narrowed by this round.**  `StrengthenNarrow.lean` §1's obligation
follows from its neutral restriction plus the typing half. -/
theorem TransStrengtheningNarrowNeutral.transNarrow (henv : VEnv.WF env)
    (HT : TypingStrengthening env U) (HN : TransStrengtheningNarrowNeutral env U) :
    TransStrengtheningNarrow env U :=
  (HN.transNarrowT henv HT).transNarrow henv HT

/-- **Capstone.**  `StrengtheningTarget.iff_piDescend_narrow` (`StrengthenNarrow.lean` §3) with
the second conjunct replaced by the residual restricted to endpoints whose type is neutral and
not a Prop.  The two conjunctions are equivalent (that is what this `Iff` says); the point is
that the second conjunct's *scope* is smaller, so a prover attacking it may assume the type is
neither a sort nor a Π nor a Prop. -/
theorem strengtheningTarget_iff_piDescend_neutral (henv : VEnv.WF env) :
    StrengtheningTarget env U ↔
      PiDescend env U ∧ TransStrengtheningNarrowNeutral env U := by
  refine ⟨fun H => ?_, fun ⟨HP, HN⟩ => ?_⟩
  · have ⟨h1, h2⟩ := (StrengtheningTarget.iff_piDescend_narrow henv).1 H
    exact ⟨h1, (transNarrowT_of_transNarrow henv h2).neutral⟩
  · have HT : TypingStrengthening env U := (TypingStrengthening.iff_piDescend henv).2 HP
    exact (StrengtheningTarget.iff_piDescend_narrow henv).2 ⟨HP, HN.transNarrow henv HT⟩

/-! ## 4. Negative controls -/

/-- **The `NeutralTy` restriction alone does not exclude Props**, so §1's Prop side condition in
`TransStrengtheningNarrowNeutral` is doing independent work: in a context whose head is `Prop`,
the neutral type `bvar 0` *is* a Prop, in every environment. -/
theorem hasType_bvar0_prop {Γ : List VExpr} :
    env.HasType U (.sort .zero :: Γ) (.bvar 0) (.sort .zero) := .bvar .zero

theorem neutralTy_bvar0 : (VExpr.bvar 0).NeutralTy := .bvar

/-- **§1 does not silently assume the endpoints convertible upstairs.**  Here is the Prop
collapse with the residual's two premises *absent from the statement* — so the proof slice is
degenerate, not merely provable. -/
theorem IsDefEqU.strengthen_at_prop_no_premises (henv : VEnv.WF env)
    (HT : TypingStrengthening env U) {n k : Nat} {Γ Γ' : List VExpr} {e1 e2 T : VExpr}
    (W : Ctx.LiftN n k Γ Γ') (hΓ' : OnCtx Γ' (env.IsType U))
    (hp : env.HasType U Γ T (.sort .zero))
    (h1 : env.HasType U Γ' (e1.liftN n k) (T.liftN n k))
    (h2 : env.HasType U Γ' (e2.liftN n k) (T.liftN n k)) :
    env.IsDefEqU U Γ e1 e2 :=
  ⟨_, IsDefEqU.strengthen_at_prop henv HT W hΓ' hp h1 h2⟩

/-- **Why §2's η step is not `ChurchRosser.lean:1184`'s `hasType_app_bvar0`.**  Given
`Γ ⊢ e : Π A B` downstairs, η-expansion is free — this is the whole of §2's `eta` helper.
`hasType_app_bvar0` has to go the *other* way, producing a Π typing from an application, and
that is where its appeal to the hole sits.  Recorded so the asymmetry is machine-checked. -/
theorem hasType_app_bvar0_of_hasType (henv : VEnv.WF env) {Γ : List VExpr} {A B e : VExpr}
    (H : env.HasType U Γ e (.forallE A B)) :
    env.HasType U (A::Γ) (.app e.lift (.bvar 0)) B := by
  have := (H.weakN henv Ctx.LiftN.one).appDF (.bvar .zero)
  rwa [VExpr.instN_bvar0] at this

end VEnv
end Lean4Lean
