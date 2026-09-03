import Lean4Lean.Theory.Typing.PiDescendSplit

/-!
# `PiDescendFst` is codomain-skipping: the residual is one conversion, not a typing

Round 9 of the `VEnv.IsDefEqU.weakN_iff` line.  Input: `Theory/Typing/PiDescendSplit.lean` and
`docs/handoff-pidescend.md`, whose round-8 result is

    piDescend_iff_fst_sortConv : PiDescend U ↔ PiDescendFst U ∧ SortConvStrengthening U

with the second conjunct a *consequence* of the typing half, so that the whole residual of
`PiDescend` is Π-shape recovery, `PiDescendFst`.  This file replaces `PiDescendFst` by a
statement of a different shape and proves the replacement is exact.

## The result

**`PiDescend U ↔ PiCodLift U ∧ SortConvStrengthening U`** (§3), where `PiCodLift` is

    Ctx.LiftN n k Γ Γ' → OnCtx Γ → OnCtx Γ' →
      Γ ⊢ a : S → Γ' ⊢ f↑ : ∀(S↑).B → VExpr.WF Γ f →
      ∃ B₀, S↑::Γ' ⊢ B ≡ B₀↑

i.e. **the codomain of the upstairs Π is convertible to a lift**.  Four things change:

1. The conclusion is a **conversion**, not a typing.  Nothing has to produce a derivation for
   `f` downstairs.
2. The **domain is gone from the existential**.  `PiDescendFst` asks for `∃ A₀ B₀`; here `A₀`
   is pinned to `S`, the argument's *own* downstairs type, and §1 proves that pinning is free
   (`dom_conv_lift`).  So one of the two existential witnesses of `PiDescendFst` was never
   open.
3. Consequently the second conjunct of `PiDescend` -- `Γ ⊢ a : A₀` -- comes back **for free**
   rather than from `ArgPin`: with `A₀ = S` it *is* the hypothesis `Γ ⊢ a : S`.  §3 therefore
   gets all of `PiDescend`, not just its first conjunct, and `ArgPin` is not used.
4. The conclusion is exactly `∃ B₀, S↑::Γ' ⊢ B ≡ B₀↑`, i.e. **`B` is convertible to something
   that `Skips` the stripped variables** (`VExpr.skips_iff_exists`) -- the vocabulary
   `StrengthenNarrow.lean`'s `¬ b.Skips n k` residual is already stated in.

## What this is and is not

It is an **equivalence**, and it is reported as one: `PiCodLift` is not weaker than
`PiDescendFst`, and §4 proves the round trip (`piDescendFst_iff_codLift_of_sortConv`).  No
strength is gained; what is gained is shape, and the fact that the *domain* half of Π-shape
recovery -- which the round-8 handoff left inside a two-witness existential -- is **free**.

## Rounds 9b: the subject is eliminated, and the split is on the *type*

§5-§10 continue the same line and change the residual's shape twice more.

5. **§5, the subject drops out.**  `f` enters `PiCodLift` only through `uniqU` and `a` only
   through `S`, so `PiCodLift` is *equivalent* (`piCodLift_iff_inhab`) to a statement with no
   subject at all: a conversion `Γ' ⊢ T↑ ≡ ∀(S↑).B` between a lift and a Π, with `T` and `S`
   inhabited downstairs.  Inhabitation is what the two subjects leave behind, and it is kept
   deliberately -- uninhabited entries are the whole difficulty of strengthening
   (`Strengthen.lean` §1).  **This is the cheapest result in the file**: cone 3486, and
   `WF.rigidShapeUniqNS` is *not* in it, only `forallE_inv_stratified`.
6. **§6, the split is on `T`, not on `f`.**  `docs/handoff-pidescend.md` §2.5 splits on the head
   of `f` and reports `.lam` free, `.sort`/`.forallE` needing `sort_forallE_inv`, and three heads
   open.  That is the wrong variable: after §5 there is no `f`, and splitting on the head of the
   *type* discharges three of the six constructors uniformly -- `.forallE` (Π-injectivity),
   `.sort` (`sort_forallE_inv`), `.lam` (`not_isType_lam`, §6, apparently new) -- leaving
   `.bvar`, `.const`, `.app`.  `piDescend_iff_neutral_sortConv` is the resulting decomposition.
7. **§7** removes the `RuleFreeHead`-constant slice of that residual outright
   (`IsDefEqU.const_forallE_inv`), and records a gap in the *instrument*: `RigidShape`
   (`Injectivity.lean:918`) has three entries -- `sort`, `pi`, `app c ls as` -- and **no `bvar`
   entry**, so the variable-headed case has no slot in the shape machinery at all.
8. **§8** bounds the residual above by the target (`PiCodLift.of_typingStrengthening`), and
   `piCodLift_sortConv_iff_typingStrengthening` makes the whole chain an equivalence with the
   typing half of `IsDefEqU.weakN_iff`.  **Nothing is traded**: `weakN_iff` is in no cone here,
   measured on all 28 seeds (25 declarations of this file plus three
   positive controls, `weakN_iff` itself among them).
9. **§11** is the one **hole-free** substantive result here (`const_admits_closed_type`,
   `[propext, Classical.choice, Quot.sound]`): a `.const`-headed subject always admits a *closed*
   type, so it never reaches §7's unsupported variable row.
10. **§9** is anti-vacuity and the controls; **§10** sharpens §6: the instance depends only on
   `T`'s *downstairs conversion class* (`codLift_conv_invariance`), and a Π anywhere in that
   class closes it (`codLift_of_conv_forallE`).  So the residual is "no member of `T`'s
   downstairs class is Π-headed", instance by instance -- and producing such a member is
   `PiDescendFst`, which is the circle of `handoff-pidescend.md` §2.3 seen from this side.

**Nothing here is hole-free.**  Every substantive result carries `sorryAx` through
`IsDefEqU.forallE_inv_stratified`, and most also through `WF.rigidShapeUniqNS` (via
`IsDefEqU.forallE_inv`) or `IsDefEqU.sort_forallE_inv` (§6's `.sort` and `.lam` cases).
`IsDefEqU.weakN_iff` is in no cone of this file, and that is **not** the same as hole-free.
-/

namespace Lean4Lean
namespace VEnv

variable {env : VEnv} {U : Nat}

/-! ## 1. The domain half of Π-shape recovery is free

`PiDescendFst`'s premise `Γ' ⊢ a↑ : A` is not decoration: with `VExpr.WF Γ a` it says the
*domain* `A` of the upstairs Π is convertible to a lift, namely to the lift of `a`'s own
downstairs type.  One `uniqU`. -/

/-- **The upstairs Π's domain is convertible to a lift.**  This is what the argument premise
buys, and it is the whole domain half of Π-shape recovery. -/
theorem dom_conv_lift {n k : Nat} {Γ Γ' : List VExpr} {a S A : VExpr} (henv : VEnv.WF env)
    (hΓ' : OnCtx Γ' (env.IsType U)) (W : Ctx.LiftN n k Γ Γ')
    (haS : env.HasType U Γ a S) (ha : env.HasType U Γ' (a.liftN n k) A) :
    env.IsDefEqU U Γ' (S.liftN n k) A :=
  (haS.weakN henv.ordered W).uniqU henv hΓ' ha

/-! ## 2. `PiCodLift`: the codomain half, and it is the whole residual -/

/-- **The codomain of a lifted function's upstairs Π type is convertible to a lift.**

The domain is already `S.liftN n k` on the nose: §1 makes that free at every call site, so
restricting to it is not an extra hypothesis.  `S` is the argument's own downstairs type. -/
def PiCodLift (env : VEnv) (U : Nat) : Prop :=
  ∀ {n k : Nat} {Γ Γ' : List VExpr} {f a S B : VExpr}, Ctx.LiftN n k Γ Γ' →
    OnCtx Γ (env.IsType U) → OnCtx Γ' (env.IsType U) →
    env.HasType U Γ a S → env.HasType U Γ' (f.liftN n k) (.forallE (S.liftN n k) B) →
    VExpr.WF env U Γ f →
    ∃ B₀ : VExpr, env.IsDefEqU U (S.liftN n k :: Γ') B (B₀.liftN n (k+1))

variable! (henv : VEnv.WF env) in
/-- **The content: `PiCodLift` and sort-typed conversion strengthening give all of
`PiDescend`.**  Not just its first conjunct -- the domain of the Π produced is `a`'s own
downstairs type, so `Γ ⊢ a : A₀` is the hypothesis `Γ ⊢ a : S` and `ArgPin` never appears. -/
theorem PiDescend.of_codLift (H1 : PiCodLift env U) (H2 : SortConvStrengthening env U) :
    PiDescend env U := by
  intro n k Γ Γ' f a A B W hΓ hΓ' hf ha wff wfa
  obtain ⟨S, hS⟩ := wfa
  have haS : env.HasType U Γ a S := hS.hasType.1
  -- §1: the domain is a lift, and we may retype `f↑` at a Π whose domain is that lift
  have hAS : env.IsDefEqU U Γ' (S.liftN n k) A := dom_conv_lift henv hΓ' W haS ha
  have ⟨_, hpity⟩ := hf.isType henv.ordered hΓ'
  have ⟨⟨uA, hA⟩, uB, hB⟩ := hpity.forallE_inv henv.ordered
  have hdom : env.IsDefEq U Γ' A (S.liftN n k) (.sort uA) := hAS.symm.of_l henv hΓ' hA
  have hSA : env.HasType U Γ' (S.liftN n k) (.sort uA) := hdom.hasType.2
  have hΓS : OnCtx (S.liftN n k :: Γ') (env.IsType U) := ⟨hΓ', _, hSA⟩
  have hf' : env.HasType U Γ' (f.liftN n k) (.forallE (S.liftN n k) B) :=
    hf.defeqU_r henv hΓ' ⟨_, .forallEDF hdom hB⟩
  -- §2: the codomain is a lift
  obtain ⟨B₀, hB₀⟩ := H1 W hΓ hΓ' haS hf' wff
  have hB' : env.HasType U (S.liftN n k :: Γ') B (.sort uB) := hB.defeq_l henv.ordered hdom
  have hcod : env.IsDefEq U (S.liftN n k :: Γ') B (B₀.liftN n (k+1)) (.sort uB) :=
    hB₀.of_l henv hΓS hB'
  have hpi2 : env.IsDefEq U Γ' (.forallE (S.liftN n k) B)
      (.forallE (S.liftN n k) (B₀.liftN n (k+1))) (.sort (.imax uA uB)) :=
    .forallEDF hSA hcod
  have hlift : (VExpr.forallE S B₀).liftN n k
      = .forallE (S.liftN n k) (B₀.liftN n (k+1)) := rfl
  have hfPi : env.HasType U Γ' (f.liftN n k) ((VExpr.forallE S B₀).liftN n k) :=
    hlift ▸ hf'.defeqU_r henv hΓ' ⟨_, hpi2⟩
  -- and now subject *and* type are lifts, so the sort-typed conversion slice descends it
  obtain ⟨T, hT⟩ := wff
  have hfT : env.HasType U Γ f T := hT.hasType.1
  have ⟨v, hTv⟩ := hfT.isType henv.ordered hΓ
  have hTv' : env.HasType U Γ' (T.liftN n k) (.sort v) := hTv.weakN henv.ordered W
  obtain ⟨X, hX⟩ : env.IsDefEqU U Γ' (T.liftN n k) ((VExpr.forallE S B₀).liftN n k) :=
    (hfT.weakN henv.ordered W).uniqU henv hΓ' hfPi
  have hXv : env.IsDefEqU U Γ' X (.sort v) := hX.hasType.1.uniqU henv hΓ' hTv'
  have hconv : env.IsDefEq U Γ' (T.liftN n k) ((VExpr.forallE S B₀).liftN n k) (.sort v) :=
    IsDefEqU.defeqDF henv hΓ' hXv hX
  exact ⟨S, B₀, hfT.defeqU_r henv hΓ (H2 W hΓ hΓ' hconv), haS⟩

variable! (henv : VEnv.WF env) in
/-- The same, landing on the first conjunct alone. -/
theorem PiDescendFst.of_codLift (H1 : PiCodLift env U) (H2 : SortConvStrengthening env U) :
    PiDescendFst env U := PiDescend.fst (PiDescend.of_codLift henv H1 H2)

variable! (henv : VEnv.WF env) in
/-- **The converse: `PiDescendFst` gives `PiCodLift`.**  `uniqU` between the two upstairs types
of `f↑`, then Π-injectivity, then the domain conversion moves the codomain's context. -/
theorem PiCodLift.of_piDescendFst (H : PiDescendFst env U) : PiCodLift env U := by
  intro n k Γ Γ' f a S B W hΓ hΓ' haS hf wff
  have ha : env.HasType U Γ' (a.liftN n k) (S.liftN n k) := haS.weakN henv.ordered W
  obtain ⟨A₀, B₀, hf₀⟩ := H W hΓ hΓ' hf ha wff ⟨_, haS⟩
  have hf₀' : env.HasType U Γ' (f.liftN n k)
      (.forallE (A₀.liftN n k) (B₀.liftN n (k+1))) := hf₀.weakN henv.ordered W
  have hpi : env.IsDefEqU U Γ' (.forallE (A₀.liftN n k) (B₀.liftN n (k+1)))
      (.forallE (S.liftN n k) B) := hf₀'.uniqU henv hΓ' hf
  have ⟨⟨_, hdom⟩, _, hcod⟩ := hpi.forallE_inv henv hΓ'
  exact ⟨B₀, _, (hdom.defeqDF_l henv.ordered hcod).symm⟩

/-! ## 3. The decomposition

`PiDescend ↔ PiCodLift ∧ SortConvStrengthening`.  The `←` half is §2's content; the `→` half is
`PiDescend.fst` composed with §2's converse, together with
`SortConvStrengthening.of_piDescend` (`NormalEqStrengthen.lean`), which is round 6's result
that the second conjunct is a *consequence* of the typing half. -/

variable! (henv : VEnv.WF env) in
/-- **The residual of `PiDescend` is codomain-skipping.** -/
theorem piDescend_iff_codLift_sortConv :
    PiDescend env U ↔ PiCodLift env U ∧ SortConvStrengthening env U :=
  ⟨fun HP => ⟨PiCodLift.of_piDescendFst henv (PiDescend.fst HP),
      SortConvStrengthening.of_piDescend henv HP⟩,
   fun ⟨h1, h2⟩ => PiDescend.of_codLift henv h1 h2⟩

/-! ## 4. …and `PiCodLift` is exactly `PiDescendFst`, given the free conjunct -/

variable! (henv : VEnv.WF env) in
/-- **The round trip.**  Read with §3: `PiCodLift` is a reshaping of `PiDescendFst`, not a
weakening of it.  Reported as an equivalence deliberately -- no strength is claimed. -/
theorem piDescendFst_iff_codLift_of_sortConv (H2 : SortConvStrengthening env U) :
    PiDescendFst env U ↔ PiCodLift env U :=
  ⟨PiCodLift.of_piDescendFst henv, (PiDescendFst.of_codLift henv · H2)⟩


/-! ## 5. The subject drops out: the residual is a conversion between a lift and a Π

`PiCodLift` mentions `f` and `a`, but neither does any work beyond supplying a *type*: `f`
enters only through `uniqU`, which turns `Γ ⊢ f : T` together with `Γ' ⊢ f↑ : ∀(S↑).B` into the
conversion `Γ' ⊢ T↑ ≡ ∀(S↑).B`, and `a` enters only as an inhabitant of `S`.  §5 proves that,
as an `iff`: the two statements are the same, so **the whole residual of `PiDescend` is a
conversion, with no subject and no typing to produce**.

What survives of the two subjects is *inhabitation*: `T` and `S` are inhabited downstairs.  That
is not decoration -- it is exactly the slice of strengthening that `Strengthen.lean` §1 leaves
open (uninhabited entries are the whole difficulty), so it is kept in the statement rather than
dropped. -/

/-- **`PiCodLift` with the subjects replaced by the conversion they induce.**  `T` is a
downstairs type of `f`, `S` a downstairs type of `a`; both remain *inhabited*, which is the
only trace either subject leaves. -/
def PiCodLiftInhab (env : VEnv) (U : Nat) : Prop :=
  ∀ {n k : Nat} {Γ Γ' : List VExpr} {f a T S B : VExpr}, Ctx.LiftN n k Γ Γ' →
    OnCtx Γ (env.IsType U) → OnCtx Γ' (env.IsType U) →
    env.HasType U Γ f T → env.HasType U Γ a S →
    env.IsDefEqU U Γ' (T.liftN n k) (.forallE (S.liftN n k) B) →
    ∃ B₀ : VExpr, env.IsDefEqU U (S.liftN n k :: Γ') B (B₀.liftN n (k+1))

variable! (henv : VEnv.WF env) in
/-- One `uniqU`: the subject's own downstairs type converts to the upstairs Π. -/
theorem PiCodLift.of_inhab (H : PiCodLiftInhab env U) : PiCodLift env U := by
  intro n k Γ Γ' f a S B W hΓ hΓ' haS hf wff
  obtain ⟨T, hT⟩ := wff
  have hfT : env.HasType U Γ f T := hT.hasType.1
  exact H W hΓ hΓ' hfT haS ((hfT.weakN henv.ordered W).uniqU henv hΓ' hf)

variable! (henv : VEnv.WF env) in
/-- The converse: retype `f↑` along the conversion. -/
theorem PiCodLiftInhab.of_piCodLift (H : PiCodLift env U) : PiCodLiftInhab env U := by
  intro n k Γ Γ' f a T S B W hΓ hΓ' hfT haS hconv
  exact H W hΓ hΓ' haS ((hfT.weakN henv.ordered W).defeqU_r henv hΓ' hconv) ⟨_, hfT⟩

variable! (henv : VEnv.WF env) in
/-- **The subject is eliminable.**  Read with §3: the entire residual of `PiDescend` is a
*conversion* statement between a lift and a Π, whose two types are inhabited downstairs. -/
theorem piCodLift_iff_inhab : PiCodLift env U ↔ PiCodLiftInhab env U :=
  ⟨PiCodLiftInhab.of_piCodLift henv, PiCodLift.of_inhab henv⟩


/-! ## 6. The case split on the head of the type, machine-checked

`docs/handoff-pidescend.md` §2.5 carries a case split on the head of `f` as prose, and reports
`.lam` free, `.sort`/`.forallE` needing `sort_forallE_inv`, and `.bvar`/`.const`/`.app` open.
**That is the wrong variable to split on.**  After §5 the subject is gone, and the only thing
left to split on is the head of the *type* `T` -- which is what the closed cases were really
about: `f = .lam _ _` was free because a λ's own type is a Π, i.e. because `T` is `.forallE`.

Splitting on `T` instead discharges **three** of the six constructors, uniformly:

* `T = .forallE A' B'`: free.  `T↑` is a Π on the nose, so Π-injectivity hands the codomain
  conversion over and `B₀ := B'`.  (This is §2's converse read backwards.)
* `T = .sort u`: `T↑ = T`, and a sort is not a Π -- `IsDefEqU.sort_forallE_inv`.
* `T = .lam A' b`: a λ is not a type at all (`not_isType_lam`), and `T` types `f`.

leaving `.bvar`, `.const` and `.app`.  §7 removes one more sub-case.  Note what the split is
**not**: it is a case analysis on an *endpoint* of the conversion, exhaustive and with each
closed case genuinely closed.  It is not a syntactic side condition on a `trans` midpoint, which
`docs/vacuity-ledger.md` row 94a proves can never localise anything. -/

/-- The three heads that survive §6: a variable, a constant, an application.  These are exactly
the terms with **no** head constructor of their own to invert -- the neutral types. -/
def _root_.Lean4Lean.VExpr.PiDescendNeutral : VExpr → Prop
  | .bvar _ | .const _ _ | .app _ _ => True
  | _ => False

/-- **`PiCodLiftInhab` restricted to a neutral-headed type.**  §6 proves this is the whole of
it. -/
def PiCodLiftNeutral (env : VEnv) (U : Nat) : Prop :=
  ∀ {n k : Nat} {Γ Γ' : List VExpr} {f a T S B : VExpr}, Ctx.LiftN n k Γ Γ' →
    OnCtx Γ (env.IsType U) → OnCtx Γ' (env.IsType U) → T.PiDescendNeutral →
    env.HasType U Γ f T → env.HasType U Γ a S →
    env.IsDefEqU U Γ' (T.liftN n k) (.forallE (S.liftN n k) B) →
    ∃ B₀ : VExpr, env.IsDefEqU U (S.liftN n k :: Γ') B (B₀.liftN n (k+1))

/-- **A λ is not a type.**  Its own type is a Π (`lam_inv` plus `lamDF`), and a Π is not a sort.
Apparently absent from the tree: no `not_isType_lam` / `isType_lam` anywhere under `Theory/`
before this one. -/
theorem not_isType_lam (henv : VEnv.WF env) {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U))
    {A b : VExpr} : ¬ env.IsType U Γ (.lam A b) := by
  rintro ⟨u, hu⟩
  obtain ⟨⟨uA, hA⟩, Bb, hb⟩ := hu.lam_inv henv.ordered hΓ
  have hnat : env.HasType U Γ (.lam A b) (.forallE A Bb) := IsDefEq.lamDF hA hb
  exact IsDefEqU.sort_forallE_inv henv hΓ (hnat.uniqU henv hΓ hu).symm

variable! (henv : VEnv.WF env) in
/-- **The split, as a reduction.**  Only neutral-headed types are left. -/
theorem PiCodLiftInhab.of_neutral (H : PiCodLiftNeutral env U) : PiCodLiftInhab env U := by
  intro n k Γ Γ' f a T S B W hΓ hΓ' hfT haS hconv
  cases T with
  | bvar i => refine H W hΓ hΓ' ?_ hfT haS hconv; trivial
  | const c ls => refine H W hΓ hΓ' ?_ hfT haS hconv; trivial
  | app g x => refine H W hΓ hΓ' ?_ hfT haS hconv; trivial
  | sort u => exact absurd hconv (IsDefEqU.sort_forallE_inv henv hΓ')
  | lam A' b => exact absurd (hfT.isType henv.ordered hΓ) (not_isType_lam henv hΓ)
  | forallE A' B' =>
    have ⟨⟨_, hdom⟩, _, hcod⟩ := hconv.forallE_inv henv hΓ'
    exact ⟨B', _, (hdom.defeqDF_l henv.ordered hcod).symm⟩

variable! (henv : VEnv.WF env) in
/-- **`PiDescend`'s residual, after §3, §5 and §6.**  A conversion, no subject, and only at a
neutral-headed type. -/
theorem piDescend_iff_neutral_sortConv :
    PiDescend env U ↔ PiCodLiftNeutral env U ∧ SortConvStrengthening env U := by
  refine ⟨fun HP => ⟨fun W hΓ hΓ' _ hfT haS hconv => ?_,
    SortConvStrengthening.of_piDescend henv HP⟩,
   fun ⟨h1, h2⟩ => PiDescend.of_codLift henv
     (PiCodLift.of_inhab henv (PiCodLiftInhab.of_neutral henv h1)) h2⟩
  exact PiCodLiftInhab.of_piCodLift henv
    (PiCodLift.of_piDescendFst henv (PiDescend.fst HP)) W hΓ hΓ' hfT haS hconv


/-! ## 7. One of the three neutral heads is a rule-free constant spine, and that one is closed

`IsDefEqU.const_forallE_inv` (`Injectivity.lean:1376`) already refutes a conversion between a
`RuleFreeHead` constant spine and a Π.  So among §6's three survivors the *content* is:

* `T` a constant or an application whose head constant **carries a δ-rule**, or
* `T` headed by a **variable**.

and nothing else.  The variable case is worth flagging: the tree's shape lattice
(`Injectivity.lean:918`, `RigidShape`) has exactly three entries -- `sort`, `pi`, `app c ls as` --
and **no `bvar` entry**, so a variable-headed type versus a Π is a disjointness fact for which
the injectivity corner's machinery has no slot at all.  That is a gap in the *instrument*, not a
new hole: nothing in this file needs it, but a route that closes §6's residual by shape will
have to add that entry. -/

/-- **A rule-free constant spine is not a Π**, so the whole `.const`-with-`RuleFreeHead` slice of
§6's residual is closed.  Stated for a spine so the `.app` case is covered too. -/
theorem codLift_ruleFreeSpine_absurd (henv : VEnv.WF env) {Γ' : List VExpr}
    (hΓ' : OnCtx Γ' (env.IsType U)) {c : Lean.Name} {ls : List VLevel} {as : List VExpr}
    {D S B : VExpr} (hrf : env.RuleFreeHead c) (hD : D = (VExpr.const c ls).mkApp as)
    (hconv : env.IsDefEqU U Γ' D (.forallE S B)) : False :=
  IsDefEqU.const_forallE_inv henv hΓ' hrf (hD ▸ hconv)

/-- The `.const` case of §6 in the form the split leaves it: the head must carry a δ-rule. -/
theorem codLift_const_ruleFree (henv : VEnv.WF env) {Γ' : List VExpr}
    (hΓ' : OnCtx Γ' (env.IsType U)) {c : Lean.Name} {ls : List VLevel} {n k : Nat} {S B : VExpr}
    (hrf : env.RuleFreeHead c)
    (hconv : env.IsDefEqU U Γ' ((VExpr.const c ls).liftN n k) (.forallE (S.liftN n k) B)) :
    False :=
  codLift_ruleFreeSpine_absurd henv hΓ' (as := []) hrf rfl hconv

/-! ## 8. The residual is bounded above by the target, so it is not an over-ask

`PiCodLift` could be an accident of restatement -- a statement *stronger* than the thing it is
supposed to reduce.  It is not: the typing half implies it, so with §3 it is **equivalent** to
the typing half modulo the free conjunct.  This is the same discipline as `PiDescend.fst` in
round 8: an `iff`, deliberately, with no strength claimed. -/

variable! (henv : VEnv.WF env) in
/-- **Bounded above**: the typing half gives `PiCodLift`. -/
theorem PiCodLift.of_typingStrengthening (HT : TypingStrengthening env U) : PiCodLift env U :=
  PiCodLift.of_piDescendFst henv (PiDescend.fst ((TypingStrengthening.iff_piDescend henv).1 HT))

variable! (henv : VEnv.WF env) in
/-- …and exactly equivalent to it, together with the free conjunct.  So `PiCodLift` is the
typing half of `IsDefEqU.weakN_iff`, reshaped, and **nothing has been traded**. -/
theorem piCodLift_sortConv_iff_typingStrengthening :
    PiCodLift env U ∧ SortConvStrengthening env U ↔ TypingStrengthening env U := by
  refine ⟨fun ⟨h1, h2⟩ => (TypingStrengthening.iff_piDescend henv).2
      (PiDescend.of_codLift henv h1 h2), fun HT => ?_⟩
  have HP : PiDescend env U := (TypingStrengthening.iff_piDescend henv).1 HT
  exact ⟨PiCodLift.of_piDescendFst henv (PiDescend.fst HP),
    SortConvStrengthening.of_piDescend henv HP⟩

/-! ## 9. Anti-vacuity, and the controls

`docs/vacuity-ledger.md` §0.  Every statement introduced above is inhabited at a `VEnv.WF`
environment (§9.1); the conclusion is a *proper* constraint, i.e. not satisfied by every `B` for
shape reasons (§9.2); the excluded region of §6's split is non-empty (§9.3); and at `n = 0`
everything collapses (§9.4).

**What is missing, and it is missing honestly.**  There is no `Ordered`-but-not-`WF`
environment here that *refutes* `PiCodLift`, of the kind `ForallInvPrice.rogueSortPiEnv` is for
`ShapeLinkAgree`.  I did not find one and I do not claim one cannot exist; what I can say is why
the obvious constructions fail, and that is analysis rather than a theorem: a `VDefEq` is
well-formed only with **closed** `lhs`/`rhs` (`VDefEq.WF` types both in the empty context), so
the `extra` constructor's endpoints are closed, hence lifts; `beta`'s right endpoint is a lift
whenever its left one is (`liftN_inst_hi`); `forallEDF`, `lamDF`, `appDF`, `sortDF`, `constDF`,
`eta` and `defeqDF` all relate terms of the same head; and `proofIrrel` cannot fire because a Π
is a type.  **What is left is `trans`** -- an arbitrary midpoint -- which is exactly the node
`docs/vacuity-ledger.md` row 94a proves no syntactic condition can localise.  So a refutation, if
one exists, has to be built at a `trans` node, and I did not build one. -/

/-- **§9.1 Inhabited.**  All three forms hold at a `VEnv.WF` environment, at every `U`.  Read the
scope statement of `PiDescendSplit.lean` §5 with it: that environment declares
`univInhab : ∀ (α : Sort u), α`, so it is inconsistent and has no uninhabited context entry --
it is a satisfiability witness, not evidence that anything here is easy. -/
theorem exists_env_piCodLift :
    ∃ env : VEnv, VEnv.WF env ∧ ∀ U,
      PiCodLift env U ∧ PiCodLiftInhab env U ∧ PiCodLiftNeutral env U := by
  obtain ⟨env, hwf, h⟩ := exists_typingStrengthening_env
  refine ⟨env, hwf, fun U => ?_⟩
  have hp : PiDescend env U := TypingStrengthening.piDescend hwf (h U)
  have h1 : PiCodLift env U := PiCodLift.of_piDescendFst hwf (PiDescend.fst hp)
  have h2 : PiCodLiftInhab env U := PiCodLiftInhab.of_piCodLift hwf h1
  exact ⟨h1, h2, fun W hΓ hΓ' _ hfT haS hconv => h2 W hΓ hΓ' hfT haS hconv⟩

/-- …and the two `iff`s of §5 and §6 fire there with nothing left over. -/
theorem exists_env_piDescend_iff_neutral :
    ∃ env : VEnv, VEnv.WF env ∧ ∀ U,
      (PiCodLift env U ↔ PiCodLiftInhab env U) ∧
      (PiDescend env U ↔ PiCodLiftNeutral env U ∧ SortConvStrengthening env U) := by
  obtain ⟨env, hwf, _⟩ := exists_typingStrengthening_env
  exact ⟨env, hwf, fun _ => ⟨piCodLift_iff_inhab hwf, piDescend_iff_neutral_sortConv hwf⟩⟩

/-- **§9.2 The conclusion is a proper constraint.**  `∃ B₀, B ≡ B₀↑ (n := 1, k+1 := 1)` is not
satisfied by every `B` for shape reasons: `.bvar 1` -- the stripped variable itself -- is not in
the image of `liftN 1 · 1`.  So the conclusion really does say something about `B`, and a proof
of `PiCodLift` has to produce a conversion, not just a witness.  (Companion to
`PiDescendSplit.lean` §6(a), which is the same control one level up.) -/
theorem bvar1_not_liftN_one_one (X : VExpr) : VExpr.bvar 1 ≠ X.liftN 1 1 := by
  cases X with
  | bvar i =>
    simp only [VExpr.liftN, ne_eq, VExpr.bvar.injEq]
    rcases Nat.lt_or_ge i 1 with hi | hi
    · rw [liftVar_lt hi]; omega
    · rw [liftVar_le hi]; omega
  | _ => simp [VExpr.liftN]

/-- **§9.3 The excluded region of §6's split is non-empty.**  Whenever `A` is a type, the λ
`.lam A (.bvar 0)` is typed at a `.forallE`-headed type, so instances of `PiCodLiftInhab` with a
non-neutral `T` genuinely exist -- §6 removed live instances rather than empty ones. -/
theorem forallE_headed_inhabited {Γ : List VExpr} {A : VExpr} {u : VLevel}
    (hA : env.HasType U Γ A (.sort u)) :
    env.HasType U Γ (.lam A (.bvar 0)) (.forallE A A.lift) ∧
      ¬ (VExpr.forallE A A.lift).PiDescendNeutral :=
  ⟨IsDefEq.lamDF hA (.bvar .zero), not_false⟩

/-- …and the split is a genuine restriction in the other direction too: the three surviving
heads are neutral and the three discharged ones are not. -/
theorem piDescendNeutral_proper {A B : VExpr} {u : VLevel} {i : Nat} {c : Lean.Name}
    {ls : List VLevel} :
    ¬ (VExpr.forallE A B).PiDescendNeutral ∧ ¬ (VExpr.sort u).PiDescendNeutral ∧
      ¬ (VExpr.lam A B).PiDescendNeutral ∧ (VExpr.bvar i).PiDescendNeutral ∧
      (VExpr.const c ls).PiDescendNeutral ∧ (VExpr.app A B).PiDescendNeutral :=
  ⟨not_false, not_false, not_false, trivial, trivial, trivial⟩

/-- **§9.4 At `n = 0` the conclusion is its own premise.**  `liftN 0` is the identity, so
`B₀ := B` works with no content: all content lives at `n ≥ 1`.  This is a control and not an
assumption -- `VExpr.liftN_zero` is an equation. -/
theorem piCodLift_at_zero {k : Nat} {Δ B : VExpr} (hB : VExpr.WF env U [Δ] B) :
    ∃ B₀ : VExpr, env.IsDefEqU U [Δ] B (B₀.liftN 0 (k+1)) :=
  ⟨B, by rw [VExpr.liftN_zero]; exact hB⟩


/-! ## 10. The residual depends only on `T`'s *downstairs* conversion class

§6 splits on the head of `T` as written.  But `T` is only a representative: the instance is
invariant under downstairs conversion of `T` (§10.1, one `weakN` and one `trans`), so what
matters is not `T`'s head but whether **any** member of `T`'s downstairs conversion class is
Π-headed (§10.2).  That is the sharp form of the residual, and it is also where the circle of
`docs/handoff-pidescend.md` §2.3 becomes visible from this side: "some member of the class is
Π-headed" *is* `PiDescendFst` at `f`.  §4's `iff` says the two are equivalent globally; §10.2
says they are equivalent **instance by instance**, which is strictly more information and is what
rules out a proof that closes only some instances by exhibiting a Π. -/

variable! (henv : VEnv.WF env) in
/-- **§10.1 Invariance.**  Replacing `T` by anything convertible to it downstairs leaves the
instance unchanged. -/
theorem codLift_conv_invariance {n k : Nat} {Γ Γ' : List VExpr} {T T' S B : VExpr}
    (hΓ' : OnCtx Γ' (env.IsType U)) (W : Ctx.LiftN n k Γ Γ')
    (hTT' : env.IsDefEqU U Γ T T')
    (hconv : env.IsDefEqU U Γ' (T'.liftN n k) (.forallE (S.liftN n k) B)) :
    env.IsDefEqU U Γ' (T.liftN n k) (.forallE (S.liftN n k) B) :=
  (hTT'.weakN henv.ordered W).trans henv hΓ' hconv

variable! (henv : VEnv.WF env) in
/-- **§10.2 A Π anywhere in the downstairs class closes the instance.**  So the residual is not
"`T` is neutral-headed" but the stronger "**no** member of `T`'s downstairs conversion class is
Π-headed" -- and producing such a member is exactly `PiDescendFst`. -/
theorem codLift_of_conv_forallE {n k : Nat} {Γ Γ' : List VExpr} {T A' B' S B : VExpr}
    (hΓ' : OnCtx Γ' (env.IsType U)) (W : Ctx.LiftN n k Γ Γ')
    (hTT' : env.IsDefEqU U Γ T (.forallE A' B'))
    (hconv : env.IsDefEqU U Γ' (T.liftN n k) (.forallE (S.liftN n k) B)) :
    ∃ B₀ : VExpr, env.IsDefEqU U (S.liftN n k :: Γ') B (B₀.liftN n (k+1)) := by
  have hconv' : env.IsDefEqU U Γ' ((VExpr.forallE A' B').liftN n k)
      (.forallE (S.liftN n k) B) :=
    ((hTT'.symm.weakN henv.ordered W).trans henv hΓ' hconv)
  have ⟨⟨_, hdom⟩, _, hcod⟩ := hconv'.forallE_inv henv hΓ'
  exact ⟨B', _, (hdom.defeqDF_l henv.ordered hcod).symm⟩


/-! ### 9.5 The residual's premises cannot be shown satisfiable without settling it

`docs/vacuity-ledger.md`'s standing demand is that a carried hypothesis be discharged or proved
inhabited.  For §6's residual the honest answer is the one `ForallInvPrice.hyp_inhabited_iff`
gives for hole A, and it is a theorem rather than an excuse: **if the residual's premises are
never satisfiable then `PiDescend` follows**, so exhibiting an instance of them is exactly as hard
as refuting the target, and showing there is none is exactly as hard as proving it.

The `hno` below is the negation of the residual's premise set, `∀`-quantified.  Note what this
does *not* say: it is not a claim that no such instance exists (that would be a conjecture, and
`docs/vacuity-ledger.md` §0 kind 4 is about exactly that mistake). -/

variable! (henv : VEnv.WF env) in
/-- **Vacuity of the residual would close `PiDescend`.** -/
theorem piDescend_of_no_neutral_pi (H2 : SortConvStrengthening env U)
    (hno : ∀ {n k : Nat} {Γ Γ' : List VExpr} {f T S B : VExpr}, Ctx.LiftN n k Γ Γ' →
      OnCtx Γ (env.IsType U) → OnCtx Γ' (env.IsType U) → T.PiDescendNeutral →
      env.HasType U Γ f T →
      ¬ env.IsDefEqU U Γ' (T.liftN n k) (.forallE (S.liftN n k) B)) :
    PiDescend env U :=
  PiDescend.of_codLift henv
    (PiCodLift.of_inhab henv (PiCodLiftInhab.of_neutral henv
      fun W hΓ hΓ' hne hfT _ hconv => absurd hconv (hno W hΓ hΓ' hne hfT))) H2


/-! ## 11. A `.const`-headed subject admits a closed type, so it never reaches the unsupported row

`docs/handoff-pidescend.md` §2.5 calls the `.const` case of its (different) split "the sharpest
form … Π-shape descent for a **closed** type, which no lift can touch".  Closedness is real but it
is not what closes anything: §6's split is on the head of `T`, and closedness only says which
*heads* `T` can have.  What it does buy, precisely, is that the one row of §6's residual for which
the tree has **no** machinery -- `T` variable-headed, §7 -- is unreachable from a `.const`-headed
subject, because a closed term is not a variable.  That is this section, machine-checked. -/

/-- **A constant's natural type is closed**, hence lift-invariant, hence not a variable.  So for
`f = .const c ls` the type `T` of §5 may always be taken outside the `.bvar` row of §6. -/
theorem const_admits_closed_type (henv : VEnv.WF env) {Γ : List VExpr}
    (hΓ : OnCtx Γ (env.IsType U)) {c : Lean.Name} {ls : List VLevel} {V : VExpr}
    (hf : env.HasType U Γ (.const c ls) V) :
    ∃ T : VExpr, env.HasType U Γ (.const c ls) T ∧ (∀ n k, T.liftN n k = T) ∧
      ∀ i, T ≠ .bvar i := by
  obtain ⟨ci, h1, h2, h3⟩ := hf.const_inv henv.ordered hΓ
  have hcl : ∀ n k, (ci.type.instL ls).liftN n k = ci.type.instL ls := fun _ _ =>
    (henv.ordered.closedC h1).instL.liftN_eq (Nat.zero_le _)
  refine ⟨ci.type.instL ls, IsDefEq.constDF h1 h2 h2 h3 (VLevel.forall₂_equiv_refl ls), hcl,
    fun i h => ?_⟩
  have := hcl 1 0
  rw [h] at this
  simp only [VExpr.liftN, VExpr.bvar.injEq, liftVar_base'] at this
  omega

end VEnv
end Lean4Lean
