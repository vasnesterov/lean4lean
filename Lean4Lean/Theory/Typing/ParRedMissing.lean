import Lean4Lean.Theory.Typing.DescendRestate

/-!
# What `ParRed` is missing, as two constructors -- and why it cannot be a hypothesis

The rewiring asked for -- delete `NormalEq.descend`, land `NormalEq.parRed` and
`IsDefEq.church_rosser` on the `V`/`VK` route -- **is not reachable today**.  This file
machine-checks why, at the level of the reduction relation rather than by assertion, and
identifies exactly what `ParRed` lacks.

## The trap this file fell into first, recorded because it is the reusable part

The obvious way to state "`ParRed` is missing proof replacement" is as a hypothesis:

```
def ParRedProofRepl : Prop :=
  ∀ {Γ P h h'}, Γ ⊢ P : .sort 0 → Γ ⊢ h : P → Γ ⊢ h' : P → Γ ⊢ h ≫ h'
```

**Every consequence of that hypothesis is vacuous at the only witness instance in the tree.**
`ParRed` is a fixed inductive with eight constructors, so the `Prop` above is a claim *about
that inductive*, and it is **false** at `refParams`: `not_parRedProofRepl` below derives
`ParRed refCtx (.bvar 0) (.const D [])` from it and contradicts `refParRed_bvar`.  Likewise
`not_parRedEtaContract`, against `refParRed_id`.  A first version of this file proved three
"witness repaired" theorems under those hypotheses; all three were vacuous exactly at the
instance they were about, which is `docs/vacuity-ledger.md` §0's failure mode with the
hypothesis, not the conclusion, carrying the falsity.

So a missing reduction step must be stated as a **constructor of an extension**, never as a
property of the relation being extended.  `ParRedP` below is that extension, and every result
in §2-§4 is unconditional.

## §1 What is missing

`ParRed` has eight constructors (`bvar, sort, const, app, lam, forallE, beta, extra`).
`NormalEq` has nine, and two -- `proofIrrel` and `etaL`/`etaR` -- have no counterpart.
`descend`'s conclusion asks a `NormalEq` to be pushed through to a *reduct*, so at exactly
those two it asks for a step the relation does not contain.  `ParRedP` adds the two.

`ParRedP` is deliberately a **sub**relation of the intended extension: it takes all of `ParRed`
through `of`, adds `app` congruence, and adds the two new steps, but no `lam`/`forallE`
congruence over the new steps.  A lower bound is the right shape here -- anything shown to
reduce in `ParRedP` also reduces in the real extension -- so §2's repairs are conservative.

## §2 What each witness needs

| witness | `NormalEq` constructor | needs | repaired by |
|---|---|---|---|
| A (`not_descendStatement`) | `proofIrrel` | proof replacement | `refWitnessA_reduces_to_match` |
| B (`not_descendStatement_etaArg`) | `etaL` | eta-contraction | `refWitnessB_reduces_to_match` |
| C (`not_descendStatement_etaFun`) | `etaL` then `proofIrrel` | `beta` (present) **+** proof replacement | `refWitnessC_reduces_to_match` |

Witness C contributes **no new obligation**: `beta` alone carries `refG3` to `refG`, which is
witness A's left term (`DescendRefute.lean`'s `refParRed_G3` already gives the reduct set as
`{refG3, refG}`).  So the genuinely new obligations are **two**, and they are exactly the two
`NormalEq` constructors with no `ParRed` counterpart -- that is the closure of the analysis,
not a coincidence.

**Necessity, not just sufficiency.**  `DescendRestate.lean`'s `refParRedK_G` shows `refG` is
normal for `ParRedK` -- `ParRed` *plus* the `keta` constructor the K-development already adds --
at every grade.  So no step now in the tree moves it, and any repair must add one.

## §3 The cost, machine-checked -- this is the real blocker

`refParRedP_cycle` (unconditional): in `ParRedP`, `refG` and `refG'` reduce to **each other**,
because `.bvar 0` and `.const D []` are both proofs of `P`.  So the extension is not acyclic,
and every measure-based argument over `ParRed` has to be redone: `ChurchRosser.lean`'s
`ParRed.triangle` (`:1073`) first, which is what `ParRedS.church_rosser` (`:2435`),
`CRDefEq.trans` and `IsDefEq.church_rosser` (`:2480`) rest on.  This is the `ParRed`-side twin
of `KDescend.lean`'s `KDiamond`, whose whole content is likewise the `≡` -> `≡ₚ` upgrade that
confluence exists to deliver.

## §4 Why wiring alone cannot finish it

Three facts, each machine-checked elsewhere, together decisive:

1. **Over `ParRed` the target statement is false.**  `KCanonical.lean`'s
   `not_crStatement_of_kstep` refutes `CRStatement` -- `IsDefEq.church_rosser`'s statement
   verbatim -- from a registered K-redex under an `eta`, using **no `hK`**, only `KStep.defeq`.
   `ParRedPropRefute.lean`'s `not_parRedStatement_of_propMajor` does the same for `parRed`'s
   statement.  Both need a `Params` instance registering an `.app` pattern, so both are refuted
   at instances that **do not exist in this tree yet** (grade of ledger row 33, not row 32).
   "Not reachable today" is not "safe to prove": there is no instance-uniform theorem to
   rewire onto.
2. **The replacement is downstream of the thing that would call it.**
   `NormalEq.appDF_extra_of_descendVK` is unconditional and `descend` is out of its cone
   (measured 3989) -- but the import chain is
   `ChurchRosser -> ... -> HeadRedStuck -> KRule -> KDescend -> KEta -> KMeasure -> KSite7 ->
   KSite7App`, so `NormalEq.parRed` cannot call it without a cycle.  The rewiring is not a
   local edit to `parRed`'s `extra` case.
3. **Moving the conclusion to `ParRedK` needs `KDiamond`.**  `ParRedKS` confluence is the
   residual; `EtaKDiamond` reduces (`KMeasure.etaKDiamond_of_at`) to an equal-height diamond
   plus a λ-congruence induction whose base is again `KDiamond`-shaped.  `KDiamond` is open,
   and `parRedKStatement_of_rows` is additionally gated on `WeakNInvDS` and carries
   `IsDefEqU.weakN_iff` (measured cone 4261).

## §5 The two-sided cost of the rewiring, measured

Requested as a two-sided measurement rather than a net (ledger rows 44, 64a).  Measured on the
Guard + ConeJoin closure, 2026-09-01:

| | |
|---|---|
| `descend` users (would leave) | **193** |
| `IsDefEqU.weakN_iff` users (would arrive) | **296** |
| descend users **already** on `weakN_iff` | **191** |
| descend users that would **newly** acquire `weakN_iff` | **2** |
| `weakN_iff` users not on `descend` | 105 |

And the two are named: `descendStatement_holds` (`DescendRefute.lean`'s anti-strawman check,
which proves `DescendStatement` *by* `descend`) and `NormalEq.appDF_extra_of_descend`
(`ChurchRosser.lean:2271`, the chokepoint).  **Both are deleted by the rewiring itself**, so the
true concentration is **zero**: `descend`'s 193 users are already, to the last surviving
declaration, `weakN_iff` users.

That is the one genuinely encouraging figure here.  The rewiring costs nothing in newly-tainted
declarations, so if §3-§4's blockers are cleared the trade is free and the census drops 13 -> 12
outright.  It does *not* make the trade available today: the blockers are about the *existence*
of the target theorem, not about its cone.

**Verdict.**  `descend` cannot be deleted today, and the census stays at 13.  Deleting it and
carrying the obligation as a hypothesis on `parRed`/`church_rosser` would push a hypothesis
onto all 193 users with no instance-uniform theorem behind it -- and, by this file's own
opening finding, a hypothesis of exactly that shape is *false* at the one instance available,
so its consequences would be vacuous.  That is a vacuity transfer, not a repair, and it is
deliberately not done here.
-/

namespace Lean4Lean
open VExpr

namespace VEnv
section
variable [Params]
open Params

local notation:65 Γ " ⊢ " e " : " A:36 => HasType env univs Γ e A

/-- The proof-replacement step, **as a property of `ParRed`** -- the framing this file's header
records as a trap.  Kept because `not_parRedProofRepl` is about it. -/
def ParRedProofRepl : Prop :=
  ∀ {Γ : List VExpr} {P h h' : VExpr},
    Γ ⊢ P : .sort .zero → Γ ⊢ h : P → Γ ⊢ h' : P → ParRed Γ h h'

/-- The eta-contraction step, likewise as a property of `ParRed`. -/
def ParRedEtaContract : Prop :=
  ∀ {Γ : List VExpr} {A B e : VExpr},
    Γ ⊢ e : .forallE A B → ParRed Γ (.lam A (.app e.lift (.bvar 0))) e

/-- **`ParRed` extended by the two steps `NormalEq` has and it lacks.**  A *lower bound* on the
intended extension: all of `ParRed` via `of`, `app` congruence, and the two new steps.  No
`lam`/`forallE` congruence over new steps, so a reduction exhibited here is a reduction in the
real extension too. -/
inductive ParRedP : List VExpr → VExpr → VExpr → Prop where
  | of {Γ e e'} : ParRed Γ e e' → ParRedP Γ e e'
  | app {Γ f f' a a'} : ParRedP Γ f f' → ParRedP Γ a a' → ParRedP Γ (.app f a) (.app f' a')
  | proofRepl {Γ P h h'} :
      Γ ⊢ P : .sort .zero → Γ ⊢ h : P → Γ ⊢ h' : P → ParRedP Γ h h'
  | etaContract {Γ A B e} :
      Γ ⊢ e : .forallE A B → ParRedP Γ (.lam A (.app e.lift (.bvar 0))) e

def ParRedPS (Γ : List VExpr) : VExpr → VExpr → Prop := ReflTransGen (ParRedP Γ)

end
end VEnv

/-! ## §1 The hypothesis framing is false at the witness instance

Both `Prop`s above are refuted at `refParams`, because `ParRed` is rigid there.  This is why
§2-§4 use `ParRedP` and carry no hypothesis. -/

/-- `ParRedProofRepl` would move `.bvar 0` to `.const D []`; `refParRed_bvar` forbids it. -/
theorem not_parRedProofRepl : ¬ @VEnv.ParRedProofRepl refParams := by
  letI := refParams
  intro HP
  exact absurd (refParRed_bvar (HP refEnv_hasP refEnv_hasBvar refEnv_hasD)) (by simp)

/-- `ParRedEtaContract` would move `refId` to `.const E []`; `refParRed_id` forbids it. -/
theorem not_parRedEtaContract : ¬ @VEnv.ParRedEtaContract refParams := by
  letI := refParams
  intro HE
  exact absurd (refParRed_id (Γ := refCtx)
    (HE (Γ := refCtx) (A := .const `P []) (B := .const `P []) (refEnv_hasE (Γ := refCtx))))
    (by simp)

/-! ## §2 Each witness, repaired unconditionally in `ParRedP` -/

/-- **Witness A.**  Proof replacement carries `refG` to `refG'`, which matches `refQ` -- so the
descent's answer disjunct, which `refNoDescentLam` shows is unavailable over `ParRed`, becomes
available.  No hypothesis. -/
theorem refParRedP_G : @VEnv.ParRedP refParams refCtx refG refG' := by
  letI := refParams
  exact .app (.of .const) (.proofRepl refEnv_hasP refEnv_hasBvar refEnv_hasD)

theorem refWitnessA_reduces_to_match :
    @VEnv.ParRedP refParams refCtx refG refG' ∧ ∃ n1 n2, refQ.Matches refG' n1 n2 :=
  ⟨refParRedP_G, refMatches⟩

/-- **Witness B.**  Eta-contraction carries `refG2` to `refG2'`, which matches `refQ2`. -/
theorem refParRedP_G2 : @VEnv.ParRedP refParams refCtx refG2 refG2' := by
  letI := refParams
  exact .app (.of .const) (.etaContract (A := .const `P []) (B := .const `P []) refEnv_hasE)

theorem refWitnessB_reduces_to_match :
    @VEnv.ParRedP refParams refCtx refG2 refG2' ∧ ∃ n1 n2, refQ2.Matches refG2' n1 n2 :=
  ⟨refParRedP_G2, refMatches2⟩

/-- **Witness C needs nothing new.**  `beta` -- already a `ParRed` constructor -- carries
`refG3` to witness A's `refG`, and witness A's step finishes. -/
theorem refParRed_G3_beta : @VEnv.ParRed refParams refCtx refG3 refG := by
  letI := refParams
  exact .beta (.app .const .bvar) .const

theorem refParRedPS_G3 : @VEnv.ParRedPS refParams refCtx refG3 refG' := by
  letI := refParams
  exact .tail (.tail .rfl (.of refParRed_G3_beta)) refParRedP_G

theorem refWitnessC_reduces_to_match :
    @VEnv.ParRedPS refParams refCtx refG3 refG' ∧ ∃ n1 n2, refQ.Matches refG' n1 n2 :=
  ⟨refParRedPS_G3, refMatches⟩

/-- **Necessity.**  No step in the tree today moves witness A's left term, at any grade
(`DescendRestate.lean`'s `refParRedK_G`), so the two steps above are not a convenience. -/
theorem refWitnessA_needs_new_step {e} (H : @VEnv.ParRedK refParams refCtx refG e) : e = refG :=
  refParRedK_G H

/-! ## §3 The cost: the extension is cyclic -/

/-- **`ParRedP` is not acyclic.**  `.bvar 0` and `.const D []` are both proofs of `P`, so the
proof-replacement step fires in both directions and `refG`, `refG'` reduce to each other.
Unconditional.  Every measure-based argument over the reduction relation therefore has to be
redone -- `ParRed.triangle` (`ChurchRosser.lean:1073`) first, and it is what
`ParRedS.church_rosser` (`:2435`) and `IsDefEq.church_rosser` (`:2480`) rest on. -/
theorem refParRedP_cycle :
    @VEnv.ParRedP refParams refCtx refG refG' ∧ @VEnv.ParRedP refParams refCtx refG' refG := by
  letI := refParams
  exact ⟨refParRedP_G, .app (.of .const) (.proofRepl refEnv_hasP refEnv_hasD refEnv_hasBvar)⟩

end Lean4Lean
