import Lean4Lean.Theory.Typing.ForallInvPrice

/-!
# The price of hole B's three constant-spine conjuncts — and it is hole B itself

`ForallInvPrice.piInvStrat_and_rigidShapeUniqNS_of_shapeLinkAgree` discharges **both** standing
holes of the injectivity corner from one hypothesis set, with hole A
(`Injectivity.IsDefEqU.forallE_inv_stratified`, `Injectivity.lean:261`) using a strict subset:
just `VEnv.WF ∧ ConvStep2 ∧ ShapeLinkAgree`.  Call that subset **the base**.  Hole B
(`Injectivity.VEnv.WF.rigidShapeUniqNS`) additionally consumes `RigidConstAppInv`,
`RigidConstPiDisj` and `RigidConstSortDisj`.  This file prices those three.

## The answer, in the brief's own vocabulary

Not (a) — not free.  Not (c) — not refuted at a `VEnv.WF` environment.  It is **(b), and in
the sharpest possible form: over the base, the three conjuncts are *jointly equivalent to hole
B*** (§3, `constFamily_iff_rigidShapeUniqNS`, `sorryAx`-free, both directions).

    VEnv.WF ∧ ConvStep2 ∧ ShapeLinkAgree ⊢
      (RigidConstAppInv ∧ RigidConstPiDisj ∧ RigidConstSortDisj)  ↔  RigidShapeUniqNS

The `←` half is new here and is what makes it an equivalence.  It needs `SortUniq` and
`ProofTransport`, and **both are supplied by the base**: `SortUniq` by
`PiInvResidual.sortUniq_of_shapeLinkAgree`, and `ProofTransport` by
`proofTransport_of_shapeLinkAgree` (§1) — `InjSpineTransport.proofTransport_of_convInv` composed
with `PiInvResidual.convInv_of_shapeLinkAgree`, so *not* through the `sorryAx`-tainted
`WF.proofTransport`.  Nobody had composed those two either.

### What that costs the plan

`PiInvResidual.rigidShapeUniqNS_of_constSpine` — the theorem the corner's plan of record is
built on — **is a collapse**.  It reduces hole B to a hypothesis set that, over hole A's own
price, *is* hole B.  By the standing rule of `docs/vacuity-ledger.md` rows 51/77b/82b/94a
("test every proposed localisation against its own target first"), this is the eleventh
collapse in this corner, and it is recorded as one.  §4 states the consequence without
hedging:

* `constFamily_free_iff_holeB_free` — quantified over **all** environments and **all** `U` —
  "the three conjuncts are free once hole A is paid" **is** "hole B is free once hole A is
  paid".  So the brief's hoped-for outcome (a) was never a pricing question; it is hole B.
* `piInvStrat_and_rigidShapeUniqNS_iff_constFamily` — over the base, adding the three
  conjuncts is exactly adding hole B, and both holes then follow.

Read positively, this is still worth having: it means the three conjuncts are **not extra
strength beyond hole B**.  Anyone who feared hole B's price was hole A *plus* three unknown
side conditions can stop; the price is hole A plus hole B, and the three are a decomposition
of the latter, not an addition to it.  What it forecloses is the hope that the 460-user hole
was free once the 736-user one was paid.

### Individually

Each of the three, on its own, comes back from hole B over the base (§2), so **none is
stronger than hole B**.  `RigidConstAppInv` needs nothing at all: `RigidShapeUniqNS.constAppInv`
is hypothesis-free (`[propext]`, the cleanest print in the file).  Whether any *one* of them is
free from the base is **not settled here**; all three cannot be, by §4.

## §5 The negative controls, and they are controls

All three fail at an `Ordered` environment, so `VEnv.WF` is load-bearing in any proof of any of
them and no `Ordered`-only argument can work.  The rogue idiom of `InjPiRogue.lean` needs one
extra constant here, because `RuleFreeHead c` is a condition **on `c`**: the two δ-rules that
manufacture the bad conversion are hung on a second constant, the *hub*, leaving `c` rule-free.

* `rcSortEnv` (`rcHub ≡ rcRF.{0}`, `rcHub ≡ Prop`) refutes `RigidConstSortDisj`.
* `rcPiEnv` (`rcHub ≡ rcRF.{0}`, `rcHub ≡ ∀ (_ : Prop), Prop`) refutes `RigidConstPiDisj`.
* `rcLvlEnv` (`rcHub ≡ rcRF.{0}`, `rcHub ≡ rcRF.{1}`) refutes `RigidConstAppInv`'s **level**
  half — outright for the `¬ IsProof`-free variant `RigidConstAppInvNP`, and for the conjunct
  itself conditionally on `¬ IsProof` (§5.4).  See "what is not proved" below.

`not_wf_rcSortEnv` / `not_wf_rcPiEnv` / `not_wf_rcLvlEnv` prove each witness is **not**
`VEnv.WF` (two δ-rules on one constant, `DeltaUnique.WF.defEqHeadsUnique`), so each control is a
control and none is a refutation of the corner — the discipline of
`ForallInvPrice.not_wf_sortPiEnv` and `InjPiRogue.not_wf_roguePiEnv`, copied exactly.

Three witnesses rather than one on purpose: a single environment carrying all four rules would
also link `Prop` to `∀ (_ : Prop), Prop` and hence refute `SortPiDisjUC`, i.e. refute
`ShapeLinkAgree` — which would make it useless as a control *over the base*.  As built, no rule
of any of the three has a sort on one side and a Π on the other.  **Not claimed:** that the
three witnesses *satisfy* `ShapeLinkAgree`; establishing that is the same open induction.

`docs/vacuity-ledger.md` row 148b's antitonicity warning applies and is not evaded: these
counterexamples are built by *adding* rules, so they refute the target at a **stronger**
environment than `VEnv.WF`.  What they establish is exactly that the "at most one δ-rule per
constant" clause is load-bearing, the same thing row 69 established for `ConvPiFromEntry`.

## §6 Anti-vacuity

Unlike hole A's hypothesis — where `ForallInvPrice.hyp_inhabited_iff` proves an absolute
witness *cannot* be given without closing the hole — the three conjuncts do admit one, because
they are guarded by `RuleFreeHead c` and by the spine being typeable.  Both halves are supplied
and both are machine-checked:

* `exists_wf_constFamily`: all three hold at a `VEnv.WF` environment, for every `U`.
* `exists_wf_constFamily_degenerate`: **and that witness is degenerate**, provably — at the
  empty environment no constant spine is typeable at all (`constants_of_isDefEqU_mkApp`, a new
  spine-typing inversion).  So it establishes non-contradiction and nothing else.  The same
  degeneracy afflicts `WeakNProjGate.exists_typingStrengthening_env`'s witness for a different
  reason: its only constant is `univInhab`, which *heads a δ-rule*
  (`StrengthenVerdict.univDV`'s value is the constant itself), so `RuleFreeHead` fails there
  too.
* `constFamily_premises_fire` (§6.1) is the control the degenerate witness cannot be: at
  `rcEnv0` — one axiom `rcRF : Sort 1`, **no δ-rules**, `VEnv.WF` by `wf_rcEnv0` — every head is
  rule-free and the spine is typeable, so all three conjuncts are **non-vacuous at a well-formed
  environment**.  Nothing here proves them there; that is the smallest open instance in this
  corner and it is named as such.

## What is NOT proved, stated as the negatives they are

* **No one of the three is shown free from the base**, and no two of them are shown to imply the
  third.  Only the joint equivalence with hole B is proved.
* **`RigidConstAppInv` is not refuted at `Ordered`**, only `RigidConstAppInvNP` is.  Its
  `¬ IsProof` premise cannot be discharged at `rcLvlEnv`: doing so is `sort_not_proof`-shaped
  and needs `SortUniq`, which is the thing being paid for.  Whether `rcSpine .zero` is a proof
  at `rcLvlEnv` is not decided here in either direction.
* **Nothing here is refuted at a `VEnv.WF` environment.**  The mechanism all three controls use
  — two δ-rules on one constant — is excluded at every `VEnv.WF` environment by
  `DeltaUnique.WF.defEqHeadsUnique`, so a genuine (c) would have to be a non-confluence of
  Lean's own rule set, not a rogue construction.
* **The `PatWF` route is untouched.**  `RigidNodeCircle.lean` §5 records the non-circular route
  to the three (re-derive `Verify/Typing/ConstSpine.lean`'s Church–Rosser argument with `PiInv`
  threaded through in place of its internal `forallE_inv` call and `KCanonical.CRStatement`
  hypothesised rather than applied).  This file does not attempt it and says nothing about
  whether it works.
* **No substitution at either `sorry` site becomes available.**  `Injectivity.lean` is eight
  imports upstream (`docs/vacuity-ledger.md` row 177b); everything here is a downstream
  discharge, cashable only by threading the hypotheses, exactly as hole A's pricing is.

Every headline result is `sorryAx`-free; the `#print axioms` blocks are inline, and no
declaration in this file carries anything outside `{propext, Classical.choice, Quot.sound}`.
-/

namespace Lean4Lean
namespace VEnv

variable {env : VEnv} {U : Nat}

/-! ## §1 What hole A's hypothesis set already supplies -/

/-- `VEnv.ProofTransport` from the base — `sorryAx`-free, unlike `WF.proofTransport`. -/
theorem proofTransport_of_shapeLinkAgree (henv : VEnv.WF env) (hcs : ConvStep2 env U)
    (H : ShapeLinkAgree env U) : env.ProofTransport U :=
  proofTransport_of_convInv henv.ordered (convSortInv_of_shapeLinkAgree hcs H)
    (convPiInv_of_shapeLinkAgree hcs H)

section Audit
#print axioms Lean4Lean.VEnv.proofTransport_of_shapeLinkAgree
end Audit

/-! ## §2 Each of the three comes back from hole B, over the base -/

theorem rigidConstAppInv_of_rigidShapeUniqNS (h : env.RigidShapeUniqNS U) :
    env.RigidConstAppInv U := h.constAppInv

theorem rigidConstPiDisj_of_base (henv : VEnv.WF env) (hcs : ConvStep2 env U)
    (H : ShapeLinkAgree env U) (h : env.RigidShapeUniqNS U) : env.RigidConstPiDisj U :=
  h.constPiDisj (sortUniq_of_shapeLinkAgree henv.ordered hcs H) henv.ordered
    (proofTransport_of_shapeLinkAgree henv hcs H)

theorem rigidConstSortDisj_of_base (henv : VEnv.WF env) (hcs : ConvStep2 env U)
    (H : ShapeLinkAgree env U) (h : env.RigidShapeUniqNS U) : env.RigidConstSortDisj U :=
  h.constSortDisj (sortUniq_of_shapeLinkAgree henv.ordered hcs H) henv.ordered
    (proofTransport_of_shapeLinkAgree henv hcs H)

section Audit
#print axioms Lean4Lean.VEnv.rigidConstAppInv_of_rigidShapeUniqNS
#print axioms Lean4Lean.VEnv.rigidConstPiDisj_of_base
#print axioms Lean4Lean.VEnv.rigidConstSortDisj_of_base
end Audit

/-! ## §3 The headline: over the base, the three ARE hole B -/

/-- **The three constant-spine conjuncts are jointly equivalent to hole B**, over exactly the
hypothesis set hole A costs. -/
theorem constFamily_iff_rigidShapeUniqNS (henv : VEnv.WF env) (hcs : ConvStep2 env U)
    (H : ShapeLinkAgree env U) :
    (env.RigidConstAppInv U ∧ env.RigidConstPiDisj U ∧ env.RigidConstSortDisj U) ↔
      env.RigidShapeUniqNS U :=
  ⟨fun ⟨hca, hcp, hcsd⟩ => rigidShapeUniqNS_of_constSpine henv hcs H hca hcp hcsd,
   fun h => ⟨rigidConstAppInv_of_rigidShapeUniqNS h, rigidConstPiDisj_of_base henv hcs H h,
     rigidConstSortDisj_of_base henv hcs H h⟩⟩

section Audit
#print axioms Lean4Lean.VEnv.constFamily_iff_rigidShapeUniqNS
end Audit

/-! ## §4 The consequence for the brief's question -/

/-- **Outcome (a) for all three at once IS closing hole B from hole A's hypothesis set.**

Quantified over *all* environments and *all* `U`, so this is not an artefact of a fixed
instance.  The left side is "the three constant-spine conjuncts are free once hole A is paid";
the right side is "hole B is free once hole A is paid".  They are the same statement. -/
theorem constFamily_free_iff_holeB_free :
    (∀ (env : VEnv) (U : Nat), VEnv.WF env → ConvStep2 env U → ShapeLinkAgree env U →
      env.RigidConstAppInv U ∧ env.RigidConstPiDisj U ∧ env.RigidConstSortDisj U) ↔
    (∀ (env : VEnv) (U : Nat), VEnv.WF env → ConvStep2 env U → ShapeLinkAgree env U →
      env.RigidShapeUniqNS U) := by
  constructor
  · exact fun h env U henv hcs H =>
      (constFamily_iff_rigidShapeUniqNS henv hcs H).1 (h env U henv hcs H)
  · exact fun h env U henv hcs H =>
      (constFamily_iff_rigidShapeUniqNS henv hcs H).2 (h env U henv hcs H)

/-- The same at the level of *inhabitation*, in the `∃` form `docs/vacuity-ledger.md` §0 asks
for: the hypothesis set of `ForallInvPrice.piInvStrat_and_rigidShapeUniqNS_of_shapeLinkAgree`
is inhabited exactly when the base together with hole B is.  So the three conjuncts cannot be
vacuous unless hole B is unsatisfiable over well-formed environments. -/
theorem constHyp_inhabited_iff :
    (∃ (env : VEnv) (U : Nat), VEnv.WF env ∧ ConvStep2 env U ∧ ShapeLinkAgree env U ∧
      env.RigidConstAppInv U ∧ env.RigidConstPiDisj U ∧ env.RigidConstSortDisj U) ↔
    (∃ (env : VEnv) (U : Nat), VEnv.WF env ∧ ConvStep2 env U ∧ ShapeLinkAgree env U ∧
      env.RigidShapeUniqNS U) := by
  constructor
  · rintro ⟨env, U, henv, hcs, H, h⟩
    exact ⟨env, U, henv, hcs, H, (constFamily_iff_rigidShapeUniqNS henv hcs H).1 h⟩
  · rintro ⟨env, U, henv, hcs, H, h⟩
    exact ⟨env, U, henv, hcs, H, (constFamily_iff_rigidShapeUniqNS henv hcs H).2 h⟩

/-- And the two holes are then equal in price: over the base, hole A is already discharged
(`ForallInvPrice.piInvStrat_of_shapeLinkAgree`), so adding hole B to the base is the same as
adding the three conjuncts, and *both* holes follow. -/
theorem piInvStrat_and_rigidShapeUniqNS_iff_constFamily (henv : VEnv.WF env)
    (hcs : ConvStep2 env U) (H : ShapeLinkAgree env U) :
    (env.RigidConstAppInv U ∧ env.RigidConstPiDisj U ∧ env.RigidConstSortDisj U) ↔
      (PiInvStrat env U ∧ env.RigidShapeUniqNS U) :=
  ⟨fun h => ⟨piInvStrat_of_shapeLinkAgree henv hcs H,
      (constFamily_iff_rigidShapeUniqNS henv hcs H).1 h⟩,
   fun h => (constFamily_iff_rigidShapeUniqNS henv hcs H).2 h.2⟩

section Audit
#print axioms Lean4Lean.VEnv.constFamily_free_iff_holeB_free
#print axioms Lean4Lean.VEnv.constHyp_inhabited_iff
#print axioms Lean4Lean.VEnv.piInvStrat_and_rigidShapeUniqNS_iff_constFamily
end Audit

/-! ## §5 Negative controls: all three fail at an `Ordered` environment

The rogue idiom of `InjPiRogue.lean` needs one extra constant here, because `RuleFreeHead c`
is *about* `c`: the constant whose spine appears in the conjunct must head no rule, so the two
δ-rules that manufacture the bad conversion are hung on a **second** constant, the hub. -/

/-- The rule-free constant of the controls; universe-polymorphic so that the `app`/`app`
control has two distinct level lists available. -/
def rcRF : Lean.Name := `Lean4Lean.rigidConstRuleFree
/-- The hub: the constant that carries both δ-rules.  `RuleFreeHead rcRF` is unaffected. -/
def rcHub : Lean.Name := `Lean4Lean.rigidConstHub

theorem rcRF_ne_rcHub : rcRF ≠ rcHub := by decide

/-- `rcRF : Sort 1`, with one universe parameter the type does not mention. -/
def rcCiU : VConstant := ⟨1, .sort (.succ .zero)⟩
/-- `rcHub : Sort 1`. -/
def rcCiH : VConstant := ⟨0, .sort (.succ .zero)⟩

def rcEnv0 : VEnv where
  constants n := if rcRF = n then some rcCiU else none
  defeqs _ := False

def rcEnv1 : VEnv where
  constants n := if rcHub = n then some rcCiH else if rcRF = n then some rcCiU else none
  defeqs _ := False

theorem rcEnv0_constants : rcEnv0.constants rcRF = some rcCiU := by simp [rcEnv0]
theorem rcEnv1_constants : rcEnv1.constants rcRF = some rcCiU := by
  simp [rcEnv1, rcRF, rcHub]
theorem rcEnv1_hub : rcEnv1.constants rcHub = some rcCiH := by simp [rcEnv1]

theorem addConst_rcEnv0 : VEnv.empty.addConst rcRF rcCiU = some rcEnv0 := by
  simp [VEnv.addConst, VEnv.empty, rcEnv0]

theorem addConst_rcEnv1 : rcEnv0.addConst rcHub rcCiH = some rcEnv1 := by
  simp [VEnv.addConst, rcEnv0, rcEnv1, rcRF_ne_rcHub]

theorem ordered_rcEnv1 : Ordered rcEnv1 :=
  .const (.const .empty ⟨_, rogueSort1Type⟩ addConst_rcEnv0) ⟨_, rogueSort1Type⟩ addConst_rcEnv1

/-- The rule-free spine at level list `[l]`. -/
def rcSpine (l : VLevel) : VExpr := .const rcRF [l]

theorem rcSpine_type {Γ : List VExpr} {l : VLevel} (h : env.constants rcRF = some rcCiU)
    (hl : l.WF U) : env.HasType U Γ (rcSpine l) (.sort (.succ .zero)) := by
  have := IsDefEq.constDF (env := env) (uvars := U) (Γ := Γ) (ls := [l]) (ls' := [l])
    h (by simpa using hl) (by simpa using hl) rfl (by simp [VLevel.equiv_def])
  exact by simpa [rcCiU, rcSpine, VExpr.instL, VLevel.inst, VEnv.HasType] using this

theorem rcHub_type {Γ : List VExpr} (h : env.constants rcHub = some rcCiH) :
    env.HasType U Γ (.const rcHub []) (.sort (.succ .zero)) := by
  have := IsDefEq.constDF (env := env) (uvars := U) (Γ := Γ) (ls := []) (ls' := [])
    h (by simp) (by simp) rfl (by simp)
  exact by simpa [rcCiH, VExpr.instL, VLevel.inst, VEnv.HasType] using this

/-! ### §5.1 The three rogue rule sets

Each control uses **two** δ-rules on the hub and nothing else, so the three witnesses stay as
small as possible and no control refutes more of the base than it has to. -/

/-- `rcHub ≡ rcRF.{0}` -/
def rcDfC : VDefEq := ⟨0, .const rcHub [], rcSpine .zero, .sort (.succ .zero)⟩
/-- `rcHub ≡ Prop` -/
def rcDfS : VDefEq := ⟨0, .const rcHub [], .sort .zero, .sort (.succ .zero)⟩
/-- `rcHub ≡ ∀ (_ : Prop), Prop` -/
def rcDfP : VDefEq := ⟨0, .const rcHub [], roguePi1, .sort (.succ .zero)⟩
/-- `rcHub ≡ rcRF.{1}` -/
def rcDfC' : VDefEq := ⟨0, .const rcHub [], rcSpine (.succ .zero), .sort (.succ .zero)⟩

/-- Control for `RigidConstSortDisj`. -/
def rcSortEnv : VEnv := (rcEnv1.addDefEq rcDfC).addDefEq rcDfS
/-- Control for `RigidConstPiDisj`. -/
def rcPiEnv : VEnv := (rcEnv1.addDefEq rcDfC).addDefEq rcDfP
/-- Control for `RigidConstAppInv` (its level half). -/
def rcLvlEnv : VEnv := (rcEnv1.addDefEq rcDfC).addDefEq rcDfC'

theorem ordered_rcSortEnv : Ordered rcSortEnv :=
  .defeq (.defeq ordered_rcEnv1 ⟨rcHub_type rcEnv1_hub, rcSpine_type rcEnv1_constants trivial⟩)
    ⟨rcHub_type rcEnv1_hub, roguePropType⟩

theorem ordered_rcPiEnv : Ordered rcPiEnv :=
  .defeq (.defeq ordered_rcEnv1 ⟨rcHub_type rcEnv1_hub, rcSpine_type rcEnv1_constants trivial⟩)
    ⟨rcHub_type rcEnv1_hub, roguePi1_type⟩

theorem ordered_rcLvlEnv : Ordered rcLvlEnv :=
  .defeq (.defeq ordered_rcEnv1 ⟨rcHub_type rcEnv1_hub, rcSpine_type rcEnv1_constants trivial⟩)
    ⟨rcHub_type rcEnv1_hub, rcSpine_type rcEnv1_constants trivial⟩

/-! ### §5.2 `rcRF` heads no rule in any of the three -/

theorem ruleFreeHead_rcRF_sort : rcSortEnv.RuleFreeHead rcRF := by
  rintro df (rfl | rfl | h)
  · simp [rcDfS, VExpr.headConst?, rcHub, rcRF]
  · simp [rcDfC, VExpr.headConst?, rcHub, rcRF]
  · exact absurd h not_false

theorem ruleFreeHead_rcRF_pi : rcPiEnv.RuleFreeHead rcRF := by
  rintro df (rfl | rfl | h)
  · simp [rcDfP, VExpr.headConst?, rcHub, rcRF]
  · simp [rcDfC, VExpr.headConst?, rcHub, rcRF]
  · exact absurd h not_false

theorem ruleFreeHead_rcRF_lvl : rcLvlEnv.RuleFreeHead rcRF := by
  rintro df (rfl | rfl | h)
  · simp [rcDfC', VExpr.headConst?, rcHub, rcRF]
  · simp [rcDfC, VExpr.headConst?, rcHub, rcRF]
  · exact absurd h not_false

/-! ### §5.3 The bad conversions -/

theorem rcSortEnv_defeqsC : rcSortEnv.defeqs rcDfC := by
  simp [rcSortEnv, VEnv.addDefEq, rcEnv1]
theorem rcSortEnv_defeqsS : rcSortEnv.defeqs rcDfS := by
  simp [rcSortEnv, VEnv.addDefEq, rcEnv1]
theorem rcPiEnv_defeqsC : rcPiEnv.defeqs rcDfC := by
  simp [rcPiEnv, VEnv.addDefEq, rcEnv1]
theorem rcPiEnv_defeqsP : rcPiEnv.defeqs rcDfP := by
  simp [rcPiEnv, VEnv.addDefEq, rcEnv1]
theorem rcLvlEnv_defeqsC : rcLvlEnv.defeqs rcDfC := by
  simp [rcLvlEnv, VEnv.addDefEq, rcEnv1]
theorem rcLvlEnv_defeqsC' : rcLvlEnv.defeqs rcDfC' := by
  simp [rcLvlEnv, VEnv.addDefEq, rcEnv1]

/-- `rcRF.{0} ≡ Prop` at `rcSortEnv`. -/
theorem rcSort_link : rcSortEnv.IsDefEqU 0 [] (rcSpine .zero) (.sort .zero) := by
  have h1 := IsDefEq.extra (env := rcSortEnv) (uvars := 0) (Γ := ([] : List VExpr))
    (ls := []) (df := rcDfC) rcSortEnv_defeqsC (by simp) rfl
  have h2 := IsDefEq.extra (env := rcSortEnv) (uvars := 0) (Γ := ([] : List VExpr))
    (ls := []) (df := rcDfS) rcSortEnv_defeqsS (by simp) rfl
  simp [rcDfC, rcDfS, rcSpine, VExpr.instL, VLevel.inst] at h1 h2
  exact ⟨_, h1.symm.trans h2⟩

/-- `rcRF.{0} ≡ ∀ (_ : Prop), Prop` at `rcPiEnv`. -/
theorem rcPi_link : rcPiEnv.IsDefEqU 0 [] (rcSpine .zero) roguePi1 := by
  have h1 := IsDefEq.extra (env := rcPiEnv) (uvars := 0) (Γ := ([] : List VExpr))
    (ls := []) (df := rcDfC) rcPiEnv_defeqsC (by simp) rfl
  have h2 := IsDefEq.extra (env := rcPiEnv) (uvars := 0) (Γ := ([] : List VExpr))
    (ls := []) (df := rcDfP) rcPiEnv_defeqsP (by simp) rfl
  simp [rcDfC, rcDfP, rcSpine, roguePi1, VExpr.instL, VLevel.inst] at h1 h2
  exact ⟨_, h1.symm.trans h2⟩

/-- `rcRF.{0} ≡ rcRF.{1}` at `rcLvlEnv` — two *different* level lists on one rule-free head. -/
theorem rcLvl_link : rcLvlEnv.IsDefEqU 0 [] (rcSpine .zero) (rcSpine (.succ .zero)) := by
  have h1 := IsDefEq.extra (env := rcLvlEnv) (uvars := 0) (Γ := ([] : List VExpr))
    (ls := []) (df := rcDfC) rcLvlEnv_defeqsC (by simp) rfl
  have h2 := IsDefEq.extra (env := rcLvlEnv) (uvars := 0) (Γ := ([] : List VExpr))
    (ls := []) (df := rcDfC') rcLvlEnv_defeqsC' (by simp) rfl
  simp [rcDfC, rcDfC', rcSpine, VExpr.instL, VLevel.inst] at h1 h2
  exact ⟨_, h1.symm.trans h2⟩

/-! ### §5.4 The refutations -/

/-- **`RigidConstSortDisj` is false at an `Ordered` environment.** -/
theorem not_rigidConstSortDisj_rcSortEnv : ¬ rcSortEnv.RigidConstSortDisj 0 := fun H =>
  H (Γ := []) (c := rcRF) (ls := [.zero]) (as := []) (u := .zero) trivial
    ruleFreeHead_rcRF_sort rcSort_link

/-- **`RigidConstPiDisj` is false at an `Ordered` environment.** -/
theorem not_rigidConstPiDisj_rcPiEnv : ¬ rcPiEnv.RigidConstPiDisj 0 := fun H =>
  H (Γ := []) (c := rcRF) (ls := [.zero]) (as := []) (A := .sort .zero) (B := .sort .zero)
    trivial ruleFreeHead_rcRF_pi rcPi_link

theorem zero_not_equiv_one : ¬ List.Forall₂ (· ≈ ·) [(VLevel.zero)] [VLevel.succ .zero] := by
  rintro (_ | ⟨h, -⟩)
  exact absurd (congrFun h []) (by simp [VLevel.eval])

/-- `RigidConstAppInv` with its `¬ IsProof` premise dropped.  Exactly `RigidConstAppInv`
otherwise — this is the anti-strawman check for the conditional refutation below. -/
def RigidConstAppInvNP (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {c : Lean.Name} {ls ls' : List VLevel} {as as' : List VExpr},
    OnCtx Γ (env.IsType U) → env.RuleFreeHead c →
    env.IsDefEqU U Γ ((VExpr.const c ls).mkApp as) ((VExpr.const c ls').mkApp as') →
    List.Forall₂ (· ≈ ·) ls ls' ∧ List.Forall₂ (env.IsDefEqU U Γ) as as'

theorem RigidConstAppInvNP.rigidConstAppInv (H : RigidConstAppInvNP env U) :
    env.RigidConstAppInv U := fun hΓ hr _ h => H hΓ hr h

/-- **The `¬ IsProof`-free form of `RigidConstAppInv` is false at an `Ordered` environment**, on
the *level* half: one rule-free head, two non-equivalent level lists. -/
theorem not_rigidConstAppInvNP_rcLvlEnv : ¬ RigidConstAppInvNP rcLvlEnv 0 := fun H =>
  zero_not_equiv_one (H (Γ := []) (c := rcRF) (ls := [.zero]) (ls' := [.succ .zero])
    (as := []) (as' := []) trivial ruleFreeHead_rcRF_lvl rcLvl_link).1

/-- …and `RigidConstAppInv` itself is false there **as soon as the spine is not a proof**.  The
premise is *not* discharged: see §5.6. -/
theorem not_rigidConstAppInv_rcLvlEnv (hnp : ¬ rcLvlEnv.IsProof 0 [] (rcSpine .zero)) :
    ¬ rcLvlEnv.RigidConstAppInv 0 := fun H =>
  zero_not_equiv_one (H (Γ := []) (c := rcRF) (ls := [.zero]) (ls' := [.succ .zero])
    (as := []) (as' := []) trivial ruleFreeHead_rcRF_lvl hnp rcLvl_link).1

section Audit
#print axioms Lean4Lean.VEnv.ordered_rcSortEnv
#print axioms Lean4Lean.VEnv.ordered_rcPiEnv
#print axioms Lean4Lean.VEnv.ordered_rcLvlEnv
#print axioms Lean4Lean.VEnv.not_rigidConstSortDisj_rcSortEnv
#print axioms Lean4Lean.VEnv.not_rigidConstPiDisj_rcPiEnv
#print axioms Lean4Lean.VEnv.not_rigidConstAppInvNP_rcLvlEnv
#print axioms Lean4Lean.VEnv.not_rigidConstAppInv_rcLvlEnv
end Audit

/-! ### §5.5 The controls are controls: none of the three witnesses is `VEnv.WF`

Same discipline as `ForallInvPrice.not_wf_sortPiEnv` and `InjPiRogue.not_wf_roguePiEnv`.  Each
witness hangs **two** δ-rules on one constant, which `DeltaUnique.WF.defEqHeadsUnique` forbids.
Without this half a control is indistinguishable from a refutation of the target. -/

theorem not_wf_rcSortEnv : ¬ VEnv.WF rcSortEnv := fun h =>
  absurd (h.defEqHeadsUnique _ _ rcHub rcSortEnv_defeqsC rcSortEnv_defeqsS ⟨[], rfl⟩ ⟨[], rfl⟩)
    (by simp [rcDfC, rcDfS, rcSpine])

theorem not_wf_rcPiEnv : ¬ VEnv.WF rcPiEnv := fun h =>
  absurd (h.defEqHeadsUnique _ _ rcHub rcPiEnv_defeqsC rcPiEnv_defeqsP ⟨[], rfl⟩ ⟨[], rfl⟩)
    (by simp [rcDfC, rcDfP, rcSpine, roguePi1])

theorem not_wf_rcLvlEnv : ¬ VEnv.WF rcLvlEnv := fun h =>
  absurd (h.defEqHeadsUnique _ _ rcHub rcLvlEnv_defeqsC rcLvlEnv_defeqsC' ⟨[], rfl⟩ ⟨[], rfl⟩)
    (by simp [rcDfC, rcDfC', rcSpine])

section Audit
#print axioms Lean4Lean.VEnv.not_wf_rcSortEnv
#print axioms Lean4Lean.VEnv.not_wf_rcPiEnv
#print axioms Lean4Lean.VEnv.not_wf_rcLvlEnv
end Audit

/-! ## §6 Absolute inhabitation at a `VEnv.WF` environment — and its degeneracy, measured

`docs/vacuity-ledger.md` §0 asks for `∃ x, P x`.  Unlike hole A's hypothesis
(`ForallInvPrice.hyp_inhabited_iff`, where an absolute witness *provably* cannot be given
without closing the hole), the three conjuncts do admit one, because they are guarded by
`RuleFreeHead c` **and** by the spine being typeable at all.  The witness below is therefore
supplied — and its degeneracy is machine-checked in the same breath, so nobody reads it as
evidence that the conjuncts are easy. -/

/-- Typing a spine types its head. -/
theorem hasType_mkApp_head (henv : Ordered env) :
    ∀ {as : List VExpr} {Γ : List VExpr} {f T : VExpr}, OnCtx Γ (env.IsType U) →
      env.HasType U Γ (f.mkApp as) T → ∃ T', env.HasType U Γ f T'
  | [], _, _, _, _, h => ⟨_, h⟩
  | _ :: as, _, _, _, hΓ, h =>
    let ⟨_, h'⟩ := hasType_mkApp_head henv (as := as) hΓ h
    let ⟨_, _, h1, _⟩ := HasType.app_inv henv hΓ h'
    ⟨_, h1⟩

/-- **A typeable constant spine has a declared head**, at any `Ordered` environment. -/
theorem constants_of_isDefEqU_mkApp (henv : Ordered env) {Γ : List VExpr} {c : Lean.Name}
    {ls : List VLevel} {as : List VExpr} {e : VExpr} (hΓ : OnCtx Γ (env.IsType U))
    (h : env.IsDefEqU U Γ ((VExpr.const c ls).mkApp as) e) :
    ∃ ci, env.constants c = some ci := by
  obtain ⟨_, h⟩ := h
  obtain ⟨_, h1⟩ := hasType_mkApp_head henv hΓ h.hasType.1
  obtain ⟨ci, hci, -⟩ := HasType.const_inv henv hΓ h1
  exact ⟨ci, hci⟩

/-- All three conjuncts hold at **any** `Ordered` environment with no constants — vacuously. -/
theorem constFamily_of_no_constants (henv : Ordered env)
    (hc : ∀ c, env.constants c = none) :
    env.RigidConstAppInv U ∧ env.RigidConstPiDisj U ∧ env.RigidConstSortDisj U := by
  refine ⟨fun hΓ _ _ h => ?_, fun hΓ _ h => ?_, fun hΓ _ h => ?_⟩ <;>
    · obtain ⟨ci, hci⟩ := constants_of_isDefEqU_mkApp henv hΓ h
      exact absurd (hc _ ▸ hci) nofun

theorem wf_empty : VEnv.WF (∅ : VEnv) := ⟨[], .empty⟩

/-- **The three conjuncts are inhabited at a `VEnv.WF` environment**, for every `U`, in the
`∃` form the ledger asks for. -/
theorem exists_wf_constFamily :
    ∃ env : VEnv, VEnv.WF env ∧ ∀ U : Nat,
      env.RigidConstAppInv U ∧ env.RigidConstPiDisj U ∧ env.RigidConstSortDisj U :=
  ⟨∅, wf_empty, fun _ => constFamily_of_no_constants .empty (fun _ => rfl)⟩

/-- **…and the witness is degenerate, machine-checked.**  At the witness *no* rule-free spine is
typeable at all, so the conjuncts hold with nothing to say.  This is a satisfiability witness —
it shows the hypothesis is not contradictory — and it is **not** evidence that the conjuncts
have content anywhere, nor that they are easy.  Same reading as
`StrengthenVerdict.univInhab_no_uninhabited_entry` gives its own witness.

The same degeneracy afflicts `WeakNProjGate.exists_typingStrengthening_env`'s witness for a
different reason: its only constant is `univInhab`, which *heads a δ-rule*
(`StrengthenVerdict.univDV`'s value is the constant itself), so `RuleFreeHead` fails there and
the conjuncts are again vacuous.  Neither witness tests anything. -/
theorem exists_wf_constFamily_degenerate :
    ∃ env : VEnv, VEnv.WF env ∧ ∀ (U : Nat) (Γ : List VExpr) (c : Lean.Name) (ls : List VLevel)
      (as : List VExpr) (e : VExpr), OnCtx Γ (env.IsType U) →
      ¬ env.IsDefEqU U Γ ((VExpr.const c ls).mkApp as) e :=
  ⟨∅, wf_empty, by
    intro _ _ _ _ _ _ hΓ h
    obtain ⟨_, hci⟩ := constants_of_isDefEqU_mkApp .empty hΓ h
    exact absurd hci nofun⟩

/-! ### §6.1 A non-degenerate `VEnv.WF` instance: the premises all fire

`rcEnv0` — the first half of §5's construction, **before** the hub and its rules — is a genuine
one-axiom `VEnv.WF` environment with *no* δ-rules at all.  There `RuleFreeHead c` holds for
every `c`, and the spine `rcRF.{0}` is typeable, so all three conjuncts say something.  This is
the control for the *conclusion* that `exists_wf_constFamily` cannot be: it exhibits a
well-formed environment at which the conjuncts are **not** vacuous.

Nothing below proves them there.  That is the open part, and §7 says why. -/

/-- `rcRF : Sort 1` as an axiom step over the empty environment. -/
def rcAxVal : VConstVal := ⟨rcCiU, rcRF⟩

theorem wf_rcEnv0 : VEnv.WF rcEnv0 :=
  ⟨[.axiom rcAxVal], .decl (.axiom ⟨_, rogueSort1Type⟩ addConst_rcEnv0) .empty⟩

/-- At `rcEnv0` there are no rules at all, so **every** head is rule-free. -/
theorem ruleFreeHead_rcEnv0 (c : Lean.Name) : rcEnv0.RuleFreeHead c := fun _ h => absurd h not_false

/-- **The premises of all three conjuncts fire at a `VEnv.WF` environment.**  A rule-free head,
a typeable spine, and a well-formed (empty) context — so none of the three is vacuous there. -/
theorem constFamily_premises_fire :
    ∃ env : VEnv, VEnv.WF env ∧ ∃ c : Lean.Name, ∃ ls : List VLevel,
      env.RuleFreeHead c ∧ env.HasType 0 [] (VExpr.const c ls) (.sort (.succ .zero)) :=
  ⟨rcEnv0, wf_rcEnv0, rcRF, [.zero], ruleFreeHead_rcEnv0 _,
    rcSpine_type rcEnv0_constants trivial⟩

section Audit
#print axioms Lean4Lean.VEnv.wf_rcEnv0
#print axioms Lean4Lean.VEnv.constFamily_premises_fire
#print axioms Lean4Lean.VEnv.constants_of_isDefEqU_mkApp
#print axioms Lean4Lean.VEnv.constFamily_of_no_constants
#print axioms Lean4Lean.VEnv.exists_wf_constFamily
#print axioms Lean4Lean.VEnv.exists_wf_constFamily_degenerate
end Audit

end VEnv
end Lean4Lean
