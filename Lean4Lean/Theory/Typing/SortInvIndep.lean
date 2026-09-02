import Lean4Lean.Theory.Typing.InjOneFact

/-!
# Is there a route to `sort_inv` that avoids `forallE_inv_stratified`?

`Theory/Typing/PiLevelPin.lean`'s closing section names two productive targets for the
714-user hole `IsDefEqU.forallE_inv_stratified`, and the second is "`sort_not_proof` from an
independent source", citing `SetModel/NotProofNoModel.lean`'s
`sortNotProof_of_propTypeAgree` — which delivers `sort_not_proof` from
`SetModel/PropSplitAudit.lean`'s `PropTypeAgree`, a hypothesis that mentions neither
`VEnv.SortUniq` nor `OnCtx`.

**This file cashes that lead in, and the answer to "does it give a route to `sort_inv`" is
NO — with the closing point machine-checked rather than argued.**  What it does give is a
real but *bounded* gain, and the bound is the deliverable:

* §1–§2: the independent source discharges, outright and `sorryAx`-freely, **one** of the two
  residuals `InjOneFact.shapeAgree_of_wf` leaves — `ShapeNotProof`, the `proofIrrel` case —
  for **all three** consumers of the sort/Π corner at once.  `InjOneFact.lean` records that
  residual as "free *given the target*", because the only route to it in the tree
  (`Injectivity.not_isProof_of_defeqU_sort`) runs through `WF.sortUniq'` and hence through the
  hole.  It is now free *outright*.
* §3: the other residual, `ShapeMidShapeless`, is **equivalent** to the target
  (`InjOneFact.shapeMidShapeless_iff`, by the β-manufactured midpoint).  So after §2 the
  corner's residual is exactly one statement and that statement *is* what was to be proved:
  `shapeLinkAgree_iff_shapeMidShapeless_of_propAgreeOn` states the collapse as an `↔`.
  **That is where the route closes, and it closes on the `trans` node, not on `proofIrrel`.**
* §4: the gain that is not a collapse.  The *Π* half of the corner does come off the hole:
  `piInv_of_propAgreeOn` derives unstratified Π-injectivity from `VEnv.WF`,
  `RigidShapeUniqNS` and the independent source, with **no `SortUniq` and no
  `ProofTransport`** — whereas `Injectivity.IsDefEqU.forallE_inv` needs both, i.e. needs
  `forallE_inv_stratified`.  This is a genuine unhooking of `PiInv` from the 714-user hole.
* §5 records what discharging the independent source itself costs, and which of its two
  routes is circular.

## Anti-vacuity, and where the collapse is

`docs/vacuity-ledger.md` rows 51/86/94 are three statements in this corner that were green
because they were *equivalent* to what they claimed to reduce.  §3 of this file is the fourth
such measurement — but stated as the negative result it is, in the direction `↔`, rather than
reported as a reduction.  The positive results (§2, §4) are measured the other way: the
hypothesis `PropAgreeOn` is **not** equivalent to the target, and the reason is visible in its
conclusion — it delivers only `u.eval ls = 0 ↔ u'.eval ls = 0`, the *propositionhood* bit of
two levels, never `u ≈ u'`.  `PiLevelPin.imax_cod_prop_iff` is the same observation on the
Π-level side, and `SetModel/NotProofNoModel.propAgree_pointwise_not_from_equivZero` refutes
the converse step at `nv ≥ 2`.  So `PropAgreeOn` cannot deliver `SortUniq` (which *is* the
target, by `piInvStratApp_iff_sortUniq`), and §2/§4 are not disguised restatements.

## The hypothesis, and why it is restated here rather than imported

`PropAgreeOn` below is `SetModel/NotProofNoModel.lean`'s `PropTypeAgreeOnCtx` — the
`OnCtx`-guarded form, which is the form the model side's `sorryAx`-free route
(`SetModel/PropAgreeWall.propTypeAgreeOnCtx_of_stratifiedN`) actually delivers.  It is
restated rather than imported for two reasons, one structural and one contingent:

* structurally, `Theory/SetModel/*` imports `Theory/Typing/*`, so a `Theory/Typing` file that
  imported the model side would invert the dependency for the whole downstream tree;
* contingently, `Theory/SetModel/PropSplitUp.lean` and `SoundInduction.lean` do not compile on
  this commit (another stream is mid-edit, guarding `PropSplit`'s fields with `OnCtx`), so
  `NotProofNoModel.lean` is not importable here at all today.

The *unguarded* statement was machine-checked definitionally identical to
`SetModel/PropSplitAudit.PropTypeAgree` (`Iff.rfl`, in a scratch file importing both — that
import does build), and the guard added below is textually `PropTypeAgreeOnCtx`'s.
-/

namespace Lean4Lean
namespace VEnv

variable {env : VEnv} {U : Nat}

/-! ## §1 The independent source, and the two "not a proof" facts it buys -/

/-- **The independent source.**  `SetModel/NotProofNoModel.lean`'s `PropTypeAgreeOnCtx`,
restated in `Theory/Typing` (see the module docstring for why it is not imported): *the types
of a term agree on being propositions*, in an `OnCtx`-well-formed context.

Strictly weaker than `VEnv.SortUniq`, and provably so: its conclusion is about whether two
levels *evaluate to zero*, not about whether they are equivalent. -/
def PropAgreeOn (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {e A A' : VExpr} {u u' : VLevel} {ls : List Nat},
    OnCtx Γ (env.IsType U) → u.WF U → u'.WF U →
    env.HasType U Γ e A → env.HasType U Γ e A' →
    env.HasType U Γ A (.sort u) → env.HasType U Γ A' (.sort u') →
    (u.eval ls = 0 ↔ u'.eval ls = 0)

/-- **A sort is not a proof**, from the independent source.

`SetModel/NotProofNoModel.sortNotProof_of_propTypeAgree` with the `OnCtx` guard put back (that
lemma drops it; the guarded hypothesis is the one the model side's hole-free route delivers).
Compare `Theory/Typing/SortUniq.sort_not_proof`, which takes `env.SortUniq U`. -/
theorem sortNotProof_of_propAgreeOn (hord : Ordered env) (hT : PropAgreeOn env U)
    {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U)) {p : VExpr} {a : VLevel}
    (hp : env.HasType U Γ p (.sort .zero)) (hap : env.HasType U Γ (.sort a) p) : False := by
  have ha : a.WF U := hap.sort_inv hord
  have hsa : env.HasType U Γ (.sort (.succ a)) (.sort (.succ (.succ a))) :=
    HasType.sort (show (VLevel.succ a).WF U from ha)
  have key := hT (ls := []) (u := .zero) (u' := .succ (.succ a)) hΓ trivial
    (show (VLevel.succ (.succ a)).WF U from ha) hap (HasType.sort ha) hp hsa
  simp [VLevel.eval] at key

/-- **A Π is not a proof**, from the independent source.

Unlike `SetModel/NotProofNoModel.forallENotProof_of_propTypeAgree`, this does *not* take the
domain and codomain typings as extra premises: `HasType.forallE_inv` recovers them from the
Π's own typing, which is what makes it usable as a residual-slot inhabitant rather than only
at call sites that happen to have them.  Compare `Theory/Typing/NotProof.forallE_not_proof`,
which takes `env.SortUniq U`. -/
theorem forallENotProof_of_propAgreeOn (hord : Ordered env) (hT : PropAgreeOn env U)
    {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U)) {A B p : VExpr}
    (hp : env.HasType U Γ p (.sort .zero)) (hfp : env.HasType U Γ (.forallE A B) p) : False := by
  obtain ⟨⟨u, hA⟩, v, hB⟩ := hfp.forallE_inv hord
  have hu : u.WF U := have ⟨_, t⟩ := hA.isType hord hΓ; t.sort_inv hord
  have hΓ' : OnCtx (A::Γ) (env.IsType U) := ⟨hΓ, _, hA⟩
  have hv : v.WF U := have ⟨_, t⟩ := hB.isType hord hΓ'; t.sort_inv hord
  have hf : env.HasType U Γ (.forallE A B) (.sort (.imax u v)) := IsDefEq.forallEDF hA hB
  have hs : env.HasType U Γ (.sort (.imax u v)) (.sort (.succ (.imax u v))) :=
    HasType.sort (show (VLevel.imax u v).WF U from ⟨hu, hv⟩)
  have key := hT (ls := []) (u := .zero) (u' := .succ (.imax u v)) hΓ trivial
    (show (VLevel.succ (.imax u v)).WF U from ⟨hu, hv⟩) hfp hf hp hs
  simp [VLevel.eval] at key

/-! ## §2 The `proofIrrel` residual of the whole sort/Π corner, discharged

`InjOneFact.shapeAgree_of_wf` runs one induction over `IsDefEqStrong` for all three consumers
of the corner and leaves exactly two residuals: `ShapeMidShapeless` (the `trans` node) and
`ShapeNotProof` (the `proofIrrel` node).  `ShapeNotProof` is *unguarded* — it carries no
context hypothesis — and the independent source is guarded, so the guarded variant is stated
here and the induction is re-run against it.  Threading the guard is free: every case of that
induction whose induction hypothesis is used (`symm`, `trans`, `defeqDF`) keeps the context
fixed, which is why `shapeAgree_of_wf` could already carry `CtxStrong` in its conclusion. -/

/-- `InjOneFact.ShapeNotProof`, guarded by `CtxStrong` — the form the independent source can
inhabit.  `ShapeNotProof.shapeNotProofC` shows the guard only weakens it. -/
def ShapeNotProofC (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {s : SPShape} {p : VExpr}, CtxStrong env U Γ →
    env.IsDefEqStrong U Γ p p (.sort .zero) → env.IsDefEqStrong U Γ s.toExpr s.toExpr p → False

theorem ShapeNotProof.shapeNotProofC (H : ShapeNotProof env U) : ShapeNotProofC env U :=
  fun _ h1 h2 => H h1 h2

/-- **The corner's `proofIrrel` residual, from the independent source.**  `sorryAx`-free, and
this is the point: `InjOneFact.lean` records `ShapeNotProof` as reachable only through
`Injectivity.not_isProof_of_defeqU_sort`, which proves it from `WF.sortUniq'` — i.e. from the
statement being reduced — and therefore does not import it. -/
theorem shapeNotProofC_of_propAgreeOn (hord : Ordered env) (hT : PropAgreeOn env U) :
    ShapeNotProofC env U := by
  intro Γ s p hΓ h1 h2
  cases s with
  | sort a => exact sortNotProof_of_propAgreeOn hord hT hΓ.defeq h1.defeq h2.defeq
  | pi A B => exact forallENotProof_of_propAgreeOn hord hT hΓ.defeq h1.defeq h2.defeq

/-- `InjOneFact.shapeAgree_of_wf` with the guarded `proofIrrel` residual.  Line-for-line that
proof; only the `proofIrrel` case changes, to pass the context guard along. -/
theorem shapeAgreeC_of_wf (henv : VEnv.WF env) (hm : ShapeMidShapeless env U)
    (hp : ShapeNotProofC env U) {Γ : List VExpr} {e1 e2 A : VExpr}
    (h : env.IsDefEqStrong U Γ e1 e2 A) : CtxStrong env U Γ →
      ∀ (s₁ s₂ : SPShape), e1 = s₁.toExpr → e2 = s₂.toExpr → s₁.Agree env U Γ s₂ := by
  induction h with
  | bvar _ _ _ => intro _ s₁ _ e1 _; cases s₁ <;> cases e1
  | constDF _ _ _ _ _ _ _ _ => intro _ s₁ _ e1 _; cases s₁ <;> cases e1
  | appDF _ _ _ _ _ _ _ => intro _ s₁ _ e1 _; cases s₁ <;> cases e1
  | lamDF _ _ _ _ _ _ _ => intro _ s₁ _ e1 _; cases s₁ <;> cases e1
  | beta _ _ _ _ _ _ _ _ => intro _ s₁ _ e1 _; cases s₁ <;> cases e1
  | eta _ _ _ _ _ _ _ _ => intro _ s₁ _ e1 _; cases s₁ <;> cases e1
  | sortDF _ _ h3 =>
    intro _ s₁ s₂ e1 e2
    cases s₁ <;> cases s₂ <;> cases e1 <;> cases e2
    exact h3
  | forallEDF _ _ h3 h4 _ =>
    intro _ s₁ s₂ e1 e2
    cases s₁ <;> cases s₂ <;> cases e1 <;> cases e2
    exact ⟨.one h3, .one h4⟩
  | symm _ ih => exact fun hΓ s₁ s₂ e1 e2 => (ih hΓ s₂ s₁ e2 e1).symm henv.ordered hΓ
  | defeqDF _ _ _ _ ih2 => exact ih2
  | @trans _ _ M _ _ hl hr ihl ihr =>
    intro hΓ s₁ s₂ e1 e2
    subst e1; subst e2
    match M, hl, hr, ihl, ihr with
    | .sort c, hl, hr, ihl, ihr =>
      exact (ihl hΓ s₁ (.sort c) rfl rfl).trans henv.ordered hΓ (ihr hΓ (.sort c) s₂ rfl rfl)
    | .forallE D E, hl, hr, ihl, ihr =>
      exact (ihl hΓ s₁ (.pi D E) rfl rfl).trans henv.ordered hΓ (ihr hΓ (.pi D E) s₂ rfl rfl)
    | .bvar _, hl, hr, _, _ => exact hm hΓ (by rintro c ⟨⟩) (by rintro D E ⟨⟩) hl hr
    | .const _ _, hl, hr, _, _ => exact hm hΓ (by rintro c ⟨⟩) (by rintro D E ⟨⟩) hl hr
    | .app _ _, hl, hr, _, _ => exact hm hΓ (by rintro c ⟨⟩) (by rintro D E ⟨⟩) hl hr
    | .lam _ _, hl, hr, _, _ => exact hm hΓ (by rintro c ⟨⟩) (by rintro D E ⟨⟩) hl hr
  | proofIrrel h1 h2 _ _ _ _ =>
    intro hΓ s₁ _ e1 _; subst e1; exact (hp hΓ h1 h2).elim
  | extra h1 _ _ _ _ _ _ _ _ =>
    intro _ s₁ _ e1 _
    cases s₁
    · exact (henv.instL_lhs_ne_sort h1 _ _ e1).elim
    · exact (henv.instL_lhs_ne_forallE h1 _ _ _ e1).elim

/-- **The one fact, from `VEnv.WF`, the independent source, and the `trans` residual alone.**
The two-residual bound of `InjOneFact.shapeLinkAgree_of` becomes a one-residual bound. -/
theorem shapeLinkAgree_of_propAgreeOn (henv : VEnv.WF env) (hT : PropAgreeOn env U)
    (hm : ShapeMidShapeless env U) : ShapeLinkAgree env U :=
  fun hΓ h =>
    shapeAgreeC_of_wf henv hm (shapeNotProofC_of_propAgreeOn henv.ordered hT) h hΓ _ _ rfl rfl

/-! ## §3 …and that one residual **is** the target: where the route closes

`InjOneFact.shapeMidShapeless_iff` proves `ShapeMidShapeless ↔ ShapeLinkAgree` over `Ordered
env` alone, by the β-manufactured midpoint `betaMid`.  Composed with §2 the statement below is
what the lead asked for and it is negative: with the `proofIrrel` residual paid for from
outside, the corner's remaining obligation is *literally equivalent* to the corner.

So the productive reading of `PiLevelPin.lean`'s "`sort_not_proof` from an independent source"
is **not** "and then `sort_inv` follows": `sort_not_proof` pays for the case that was already
free-given-the-target, and the case that carries the content — `trans` at an arbitrary
midpoint — is untouched by it.  Nothing that constrains the *midpoint syntactically* can help
(`InjOneFact.midShapeless_vacuous`), so what is left has to come from a reduction relation or
a normal-form predicate (`InjOneFact.ShapeCR`), i.e. from the confluence layer. -/

/-- **The collapse, stated as an `↔` rather than reported as a reduction.**  Given the
independent source, the sort/Π corner and its sole remaining residual are the same statement.
This is `docs/vacuity-ledger.md`'s rows 51/86/94 pattern, measured *before* the reduction was
claimed rather than after. -/
theorem shapeLinkAgree_iff_shapeMidShapeless_of_propAgreeOn (henv : VEnv.WF env)
    (hT : PropAgreeOn env U) : ShapeLinkAgree env U ↔ ShapeMidShapeless env U :=
  ⟨ShapeLinkAgree.shapeMidShapeless, shapeLinkAgree_of_propAgreeOn henv hT⟩

/-- **The sort side, end to end** — and the residual is still `ShapeMidShapeless ∧ ConvStep2`.
`ConvStep2` is the chain-to-link collapse (`InjPiRogue.lean` §20) and is the node
`docs/vacuity-ledger.md` §0 identifies as shared by both of the corner's holes; `ConvPiInv` is
the chain form of Π-injectivity, which §4 discharges from `RigidShapeUniqNS`. -/
theorem sortUniq_of_propAgreeOn (henv : VEnv.WF env) (hT : PropAgreeOn env U)
    (hcs : ConvStep2 env U) (hpi : ConvPiInv env U) (hm : ShapeMidShapeless env U) :
    env.SortUniq U :=
  sortUniq_of_convInv henv.ordered
    (convSortInv_of_shapeLinkAgree hcs (shapeLinkAgree_of_propAgreeOn henv hT hm)) hpi

/-- **And that is a collapse too.**  `SortUniq` gives the single-link sort statement for free
(`sort_inv_of_sortUniq`, which never opens the conversion derivation), so `SortLinkInvUC` is
not weaker than `SortUniq`. -/
theorem sortLinkInvUC_of_sortUniq (hord : Ordered env) (hsu : env.SortUniq U) :
    SortLinkInvUC env U :=
  fun hΓ h => sort_inv_of_sortUniq hsu hord hΓ.defeq ⟨_, h.defeq⟩

/-- **The sort side's residual is exactly `SortUniq`, modulo the two chain hypotheses.**

Read with `InjOneFact.sortMidNonSortC_iff_sortLinkInvUC` (`SortMidNonSortC ↔ SortLinkInvUC`,
`Ordered env` only) this says: the sort-flavoured residual left after §2 is equivalent to
`VEnv.SortUniq`, and `PiLevelPin.piInvStratApp_iff_sortUniq` identifies *that* with
`IsDefEqU.forallE_inv_stratified`.  **This is the closing point of the whole lead.** -/
theorem sortLinkInvUC_iff_sortUniq (henv : VEnv.WF env) (hcs : ConvStep2 env U)
    (hpi : ConvPiInv env U) : SortLinkInvUC env U ↔ env.SortUniq U :=
  ⟨fun H => sortUniq_of_convInv henv.ordered
      (convSortInv_of_convStep2_sortLinkInv hcs H.sortLinkInv) hpi,
    sortLinkInvUC_of_sortUniq henv.ordered⟩

/-- The same fact with the residual in the shape §2 leaves it: **`SortMidNonSortC` is
`SortUniq`**, modulo `ConvStep2` and `ConvPiInv`. -/
theorem sortMidNonSortC_iff_sortUniq (henv : VEnv.WF env) (hcs : ConvStep2 env U)
    (hpi : ConvPiInv env U) : SortMidNonSortC env U ↔ env.SortUniq U :=
  (sortMidNonSortC_iff_sortLinkInvUC henv.ordered).trans (sortLinkInvUC_iff_sortUniq henv hcs hpi)

/-! ### §3.1 `PiLevelPin.lean`'s claim, corrected

`PiLevelPin.lean`'s last section says that with `sort_not_proof` from an independent source
"`sort_inv` follows from `WF.rigidShapeUniq` alone".  That reading is **true and circular**, in
two different ways, and both are checkable rather than arguable:

1. `WF.rigidShapeUniq` is a *theorem*, not a hole, and its inhabitant is
   `rigidShapeUniq_of_sortUniq henv (WF.sortUniq' henv) (WF.rigidShapeUniqNS henv)`.  Its cone
   therefore contains `IsDefEqU.forallE_inv_stratified` (forward cone measurement over type and
   value, `allowOpaque := true`: `WF.rigidShapeUniq` has holes
   `[forallE_inv_stratified, rigidShapeUniqNS]`).  So "from `WF.rigidShapeUniq` alone" is
   "from `forallE_inv_stratified`, among other things".
2. At the *hole* level, i.e. with `WF.rigidShapeUniqNS` in place of the theorem, the claim is
   **false**: `RigidShapeUniqNS` carries the premise `¬ s₁.BothSort s₂`, which is exactly
   `False` at two sorts (`bothSort_sort_sort` below).  The `sort`/`sort` entry — the one that
   *is* `sort_inv` — was deliberately deleted from the narrowed hole because
   `sort_inv_of_sortUniq` supplies it from `SortUniq`.  So the narrowed hole says nothing at
   all about two sorts, and `sort_inv` cannot be read out of it with or without
   `sort_not_proof`.

What survives of the claim is §4: `sort_not_proof`'s *Π companion* is what
`RigidShapeUniqNS`'s live entries need, and there the independent source does pay. -/

/-- The premise `RigidShapeUniqNS` adds to `RigidShapeUniq` is `False` at two sorts, so the
narrowed hole has **no** `sort`/`sort` entry to give.  One line, and it is the machine form of
§3.1 item 2. -/
theorem bothSort_sort_sort {u v : VLevel} :
    RigidShape.BothSort (.sort u) (.sort v) := trivial

/-! ## §4 The gain that is **not** a collapse: `PiInv` comes off the 714-user hole

`Injectivity.IsDefEqU.forallE_inv` — unstratified Π-injectivity — is a theorem modulo
`WF.rigidShapeUniqNS`, but its proof spends `VEnv.SortUniq` twice over and therefore carries
`IsDefEqU.forallE_inv_stratified` in its cone:

* `forallE_inv_of_rigidPi` takes `hsu : env.SortUniq U`, used in exactly one place — the
  `proofIrrel` case, through `forallE_not_proof`;
* `RigidShapeUniqNS.piUniq` takes `hsu` *and* `WF.proofTransport`, both used in exactly one
  place — discharging the bridge's `¬ IsProof` premise through `not_isProof_of_forallE'`.

Both are "a Π is not a proof" in disguise, and §1 supplies that from the independent source.
So the two `SortUniq`s and the `ProofTransport` all come out, and what is left is
`RigidShapeUniqNS` — the *other*, smaller hole — plus `PropAgreeOn`:

    VEnv.WF ∧ RigidShapeUniqNS ∧ PropAgreeOn  →  PiInv

with `forallE_inv_stratified` **nowhere in the cone**.  This is not a collapse: `PiInv` is not
equivalent to `PropAgreeOn` (the latter's conclusion is a propositionhood bit, see the module
docstring) and it is not equivalent to `RigidShapeUniqNS` either — `rigidPiUniq_iff_piInv`
identifies `PiInv` with the *one* `pi`/`pi` entry of nine. -/

/-- **A term convertible with a sort is not a proof**, from the independent source — with no
`SortUniq` and, unlike `Injectivity.not_isProof_of_sort'`, no `ProofTransport`.  Proof-ness is
not transported along the conversion at all: the conversion's own type index is shown to be a
proposition, which is what the `PropAgreeOn` conclusion delivers directly. -/
theorem not_isProof_of_defeqU_sort_of_propAgreeOn (hord : Ordered env) (hT : PropAgreeOn env U)
    {Γ : List VExpr} {e : VExpr} {a : VLevel} (hΓ : OnCtx Γ (env.IsType U))
    (h : env.IsDefEqU U Γ e (.sort a)) : ¬ env.IsProof U Γ e := by
  rintro ⟨p, hp0, hep⟩
  obtain ⟨V, hV⟩ := h
  have heV : env.HasType U Γ e V := hV.hasType.1
  obtain ⟨w, hVw⟩ := heV.isType hord hΓ
  have hw : w.WF U := have ⟨_, t⟩ := hVw.isType hord hΓ; t.sort_inv hord
  have hz : w ≈ VLevel.zero := VLevel.equiv_def.2 fun ls =>
    (hT (ls := ls) (u := .zero) hΓ trivial hw hep heV hp0 hVw).1 rfl
  have hV0 : env.HasType U Γ V (.sort .zero) :=
    IsDefEq.defeqDF (.sortDF hw trivial hz) hVw
  exact sortNotProof_of_propAgreeOn hord hT hΓ hV0 hV.hasType.2

/-- **A term convertible with a Π is not a proof**, likewise: no `SortUniq`, no
`ProofTransport`.  Compare `Injectivity.not_isProof_of_forallE'`, which takes both. -/
theorem not_isProof_of_defeqU_forallE_of_propAgreeOn (hord : Ordered env)
    (hT : PropAgreeOn env U) {Γ : List VExpr} {e A B : VExpr}
    (hΓ : OnCtx Γ (env.IsType U)) (h : env.IsDefEqU U Γ e (.forallE A B)) :
    ¬ env.IsProof U Γ e := by
  rintro ⟨p, hp0, hep⟩
  obtain ⟨V, hV⟩ := h
  have heV : env.HasType U Γ e V := hV.hasType.1
  obtain ⟨w, hVw⟩ := heV.isType hord hΓ
  have hw : w.WF U := have ⟨_, t⟩ := hVw.isType hord hΓ; t.sort_inv hord
  have hz : w ≈ VLevel.zero := VLevel.equiv_def.2 fun ls =>
    (hT (ls := ls) (u := .zero) hΓ trivial hw hep heV hp0 hVw).1 rfl
  have hV0 : env.HasType U Γ V (.sort .zero) :=
    IsDefEq.defeqDF (.sortDF hw trivial hz) hVw
  exact forallENotProof_of_propAgreeOn hord hT hΓ hV0 hV.hasType.2

/-- **The bridge's `pi`/`pi` entry, with the `¬ IsProof` premise paid from outside.**
`Injectivity.RigidShapeUniqNS.piUniqOf` with `SortUniq` and `ProofTransport` replaced. -/
theorem rigidPiUniq_of_propAgreeOn (hord : Ordered env) (hT : PropAgreeOn env U)
    (h : env.RigidShapeUniqNS U) : env.RigidPiUniq U := by
  intro Γ e T A B A' B' hΓ h₁ h₂
  exact h (s₁ := .pi A B) (s₂ := .pi A' B') hΓ
    (not_isProof_of_defeqU_forallE_of_propAgreeOn hord hT hΓ ⟨_, h₁⟩) trivial trivial not_false
    h₁ h₂

/-- **Unstratified Π-injectivity, with `forallE_inv_stratified` out of the cone.**

`Injectivity.IsDefEqU.forallE_inv_of_rigidPi`'s induction, with its one use of
`env.SortUniq U` (the `proofIrrel` case) replaced by §1.  Every other case is unchanged. -/
theorem IsDefEqU.forallE_inv_of_propAgreeOn (henv : VEnv.WF env) (hT : PropAgreeOn env U)
    (hrp : env.RigidPiUniq U) {Γ : List VExpr} {A B A' B' : VExpr}
    (hΓ : OnCtx Γ (env.IsType U))
    (h1 : env.IsDefEqU U Γ (.forallE A B) (.forallE A' B')) :
    (∃ u, env.IsDefEq U Γ A A' (.sort u)) ∧ ∃ u, env.IsDefEq U (A::Γ) B B' (.sort u) := by
  have aux : ∀ {Γ : List VExpr} {e1 e2 T : VExpr}, env.IsDefEqStrong U Γ e1 e2 T →
      OnCtx Γ (env.IsType U) →
      ∀ A B A' B', e1 = .forallE A B → e2 = .forallE A' B' →
        (∃ u, env.IsDefEq U Γ A A' (.sort u)) ∧
        ∃ u, env.IsDefEq U (A::Γ) B B' (.sort u) ∧ env.IsDefEq U (A'::Γ) B B' (.sort u) := by
    intro Γ e1 e2 T H
    induction H with
    | forallEDF _ _ h3 h4 h5 =>
      rintro _ _ _ _ _ ⟨⟩ ⟨⟩
      exact ⟨⟨_, h3.defeq⟩, _, h4.defeq, h5.defeq⟩
    | symm _ ih =>
      rintro hΓ' A B A' B' rfl rfl
      obtain ⟨⟨u, ha⟩, v, hb1, hb2⟩ := ih hΓ' A' B' A B rfl rfl
      exact ⟨⟨u, ha.symm⟩, v, hb2.symm, hb1.symm⟩
    | defeqDF _ _ _ _ ih => exact ih
    | extra h1 => exact fun _ A B _ _ h _ => absurd h (henv.instL_lhs_ne_forallE h1 _ A B)
    | trans hd1 hd2 ih1 ih2 =>
      rintro hΓ' A B A' B' rfl rfl
      exact hrp hΓ' hd1.defeq.symm hd2.defeq
    | proofIrrel h1 h2 _ _ _ _ =>
      -- the ONE case that used `env.SortUniq U`; now §1 pays for it.
      rintro hΓ' A B A' B' rfl rfl
      exact absurd (forallENotProof_of_propAgreeOn henv.ordered hT hΓ'
        h1.defeq.hasType.1 h2.defeq.hasType.1) not_false
    | _ => rintro _ A B A' B' ⟨⟩ ⟨⟩
  obtain ⟨_, h1⟩ := h1
  obtain ⟨ha, u, hb, -⟩ := aux (h1.strong henv.ordered hΓ) hΓ _ _ _ _ rfl rfl
  exact ⟨ha, u, hb⟩

/-- **`PiInv` from `RigidShapeUniqNS` and the independent source alone.**  The headline of §4:
`Injectivity.piInv_axiom` (via `WF.sortUniq'`) carries `forallE_inv_stratified`; this does
not. -/
theorem piInv_of_propAgreeOn (henv : VEnv.WF env) (hT : PropAgreeOn env U)
    (h : env.RigidShapeUniqNS U) : env.PiInv U :=
  fun hΓ hd =>
    IsDefEqU.forallE_inv_of_propAgreeOn henv hT
      (rigidPiUniq_of_propAgreeOn henv.ordered hT h) hΓ hd

/-- …and the full bridge's `pi`/`pi` entry is then an equivalence with `PiInv` **without**
`SortUniq`, sharpening `Injectivity.rigidPiUniq_iff_piInv` (which takes it). -/
theorem piInv_of_rigidPiUniq_of_propAgreeOn (henv : VEnv.WF env) (hT : PropAgreeOn env U)
    (hrp : env.RigidPiUniq U) : env.PiInv U :=
  fun hΓ hd => IsDefEqU.forallE_inv_of_propAgreeOn henv hT hrp hΓ hd

@[inherit_doc piInv_of_rigidPiUniq_of_propAgreeOn]
theorem rigidPiUniq_iff_piInv_of_propAgreeOn (henv : VEnv.WF env) (hT : PropAgreeOn env U) :
    env.RigidPiUniq U ↔ env.PiInv U :=
  ⟨piInv_of_rigidPiUniq_of_propAgreeOn henv hT, PiInv.rigidPiUniq henv⟩

/-! ## §5 What discharging `PropAgreeOn` costs, and which route is circular

`PropAgreeOn` is a hypothesis everywhere above, so §2–§4 are reductions.  Two routes to it
exist in the tree, and **only one of them keeps §2–§4 non-circular**:

* **route A** — `SetModel/NotProofNoModel.WF.propTypeAgreeOn` proves the guarded statement for
  every `env.WF`, but through `IsDefEqU.uniqU` and `IsDefEqU.sort_inv`.
  `docs/vacuity-ledger.md` row 131b measured its cone at `preludeEnv`: it contains exactly one
  sorry-carrying declaration and that one is **`IsDefEqU.forallE_inv_stratified`**.  Instantiated
  by route A, everything above becomes circular.
* **route B** — `SetModel/PropAgreeWall.propTypeAgreeOnCtx_of_stratifiedN` is `sorryAx`-free
  and mentions no hole, but it is not hypothesis-free: it takes `∀ n, env.PropTypeAgreeN 0 n`
  and `∀ n, env.PropUniqN 0 n`, which are `Theory/Typing/PropConv.lean`'s and
  `PropShadow.lean`'s **open** targets (only the base index `n = 0` is discharged, by
  `HasTypeN.uniq_zero`).  It is also fixed at `nv = 0`: `equivZero_iff_eval_zero` needs
  `u.WF 0`, and the step is refuted at `nv ≥ 2`
  (`NotProofNoModel.propAgree_pointwise_not_from_equivZero`).

So the honest status of §4's unhooking is: **`PiInv` is off `forallE_inv_stratified` and onto
`RigidShapeUniqNS` plus `PropTypeAgreeN`/`PropUniqN` at every index, at `U = 0`.**  Whether
that is progress depends on `PropTypeAgreeN`, and `Theory/Typing/UniqueTypingN.lean`'s own
audit of it says it is **not self-sufficient** — its `eta` case needs
`SortForallEDisjoint` — so this is a trade between open statements, not a closure.  It is
recorded here because the trade is *away from* the 714-user node and onto nodes with no other
consumer.

## §6 Axiom check

Every declaration in this file is `sorryAx`-free — including §4's, which is the point of §4:
the same conclusions reached through `Injectivity.lean`'s inhabitants
(`IsDefEqU.forallE_inv`, `WF.rigidShapeUniq`) do carry `sorryAx`. -/

/-! ## §7 Anti-vacuity, and the anti-collapse check

`docs/vacuity-ledger.md` §0 asks two things of any reduction in this corner before it is
reported: that the hypotheses are **satisfiable** (instantiate at the degenerate instance), and
that the thing reduced *to* is **not equivalent** to the thing reduced *from*.  Both are done
here, and one of them is done in the negative on purpose (§3 *is* the equivalence).

Note the check inverts for `ShapeNotProofC`: it concludes `False`, so an uninhabited hypothesis
set makes it *true and useful*, not vacuous.  The statement whose premises need firing is
`PropAgreeOn`. -/

/-- **`PropAgreeOn`'s premises fire, non-degenerately, at every environment.**  All seven slots
are satisfied simultaneously at `Γ = []` with the two types **syntactically different** — which
is what stops `PropAgreeOn` from being a hypothesis about an empty class (`u ≈ u'` on the nose
would make its conclusion trivial).  No `VEnv.WF`, no constant: this holds at `∅`. -/
theorem propAgreeOn_premises_fire :
    OnCtx ([] : List VExpr) (env.IsType 0) ∧
    (VExpr.sort (.succ .zero) : VExpr) ≠ .sort (.succ (.imax .zero .zero)) ∧
    env.HasType 0 [] (.sort .zero) (.sort (.succ .zero)) ∧
    env.HasType 0 [] (.sort .zero) (.sort (.succ (.imax .zero .zero))) ∧
    env.HasType 0 [] (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) ∧
    env.HasType 0 [] (.sort (.succ (.imax .zero .zero)))
      (.sort (.succ (.succ (.imax .zero .zero)))) := by
  have hz : (VLevel.zero).WF 0 := trivial
  have hi : (VLevel.imax VLevel.zero VLevel.zero).WF 0 := ⟨trivial, trivial⟩
  have he : VLevel.succ .zero ≈ VLevel.succ (.imax .zero .zero) :=
    VLevel.equiv_def.2 fun _ => by simp [VLevel.eval, Lean.Nat.imax]
  refine ⟨trivial, ?_, HasType.sort hz, ?_, HasType.sort hz, HasType.sort hi⟩
  · intro h; exact absurd h (by simp)
  · exact IsDefEq.defeqDF
      (show env.IsDefEq 0 [] (.sort (.succ .zero)) (.sort (.succ (.imax .zero .zero)))
        (.sort (.succ (.succ .zero))) from IsDefEq.sortDF hz hi he)
      (HasType.sort hz)

/-- **The anti-collapse check: `PropAgreeOn`'s conclusion cannot deliver `SortUniq`'s.**

`SortUniq` concludes `u ≈ u'`; `PropAgreeOn` concludes `u.eval ls = 0 ↔ u'.eval ls = 0` at
every `ls`.  At `u = 1`, `u' = 2` the second holds and the first fails.  So no instantiation of
`PropAgreeOn` — at any subject, in any context — yields universe uniqueness by reading its
conclusion off, which is precisely the move that produced collapses 5, 6 and 7 of
`docs/vacuity-ledger.md` (rows 51, 86, 94: instantiate the "localised" hypothesis at a
cleverly chosen subject and read the target off).

This is the same instrument as `PiLevelPin.imax_cod_not_pinned`, and it is worth being exact
about what it does and does not establish.  **Establishes:** §2 and §4 are not the target
restated *by that route*.  **Does not establish:** that `PropAgreeOn → env.SortUniq U` fails at
every environment — that would need a witness environment satisfying one and not the other, and
none is exhibited here.  Graded accordingly in `docs/handoff-sortinv-route.md`. -/
theorem propAgree_conclusion_not_sortUniq :
    ∃ u u' : VLevel, (∀ ls, (u.eval ls = 0 ↔ u'.eval ls = 0)) ∧ ¬ u ≈ u' := by
  refine ⟨.succ .zero, .succ (.succ .zero), fun ls => by simp [VLevel.eval], ?_⟩
  intro h; exact absurd (congrFun h []) (by simp [VLevel.eval])

/-- **And the residual §3 leaves is not weaker than the target even for the `Prop` bit.**  The
converse of the check above: `u ≈ u'` does give the propositionhood biconditional, so
`PropAgreeOn` really is on the weak side of `SortUniq`'s conclusion and not merely
incomparable. -/
theorem sortUniq_conclusion_gives_propAgree {u u' : VLevel} (h : u ≈ u') (ls : List Nat) :
    u.eval ls = 0 ↔ u'.eval ls = 0 := by rw [VLevel.equiv_def.mp h ls]

section Audit
#print axioms Lean4Lean.VEnv.PropAgreeOn
#print axioms Lean4Lean.VEnv.ShapeNotProofC
#print axioms Lean4Lean.VEnv.ShapeNotProof.shapeNotProofC
#print axioms Lean4Lean.VEnv.sortNotProof_of_propAgreeOn
#print axioms Lean4Lean.VEnv.forallENotProof_of_propAgreeOn
#print axioms Lean4Lean.VEnv.shapeNotProofC_of_propAgreeOn
#print axioms Lean4Lean.VEnv.shapeAgreeC_of_wf
#print axioms Lean4Lean.VEnv.shapeLinkAgree_of_propAgreeOn
#print axioms Lean4Lean.VEnv.shapeLinkAgree_iff_shapeMidShapeless_of_propAgreeOn
#print axioms Lean4Lean.VEnv.sortUniq_of_propAgreeOn
#print axioms Lean4Lean.VEnv.sortLinkInvUC_of_sortUniq
#print axioms Lean4Lean.VEnv.sortLinkInvUC_iff_sortUniq
#print axioms Lean4Lean.VEnv.sortMidNonSortC_iff_sortUniq
#print axioms Lean4Lean.VEnv.not_isProof_of_defeqU_sort_of_propAgreeOn
#print axioms Lean4Lean.VEnv.not_isProof_of_defeqU_forallE_of_propAgreeOn
#print axioms Lean4Lean.VEnv.rigidPiUniq_of_propAgreeOn
#print axioms Lean4Lean.VEnv.IsDefEqU.forallE_inv_of_propAgreeOn
#print axioms Lean4Lean.VEnv.piInv_of_propAgreeOn
#print axioms Lean4Lean.VEnv.piInv_of_rigidPiUniq_of_propAgreeOn
#print axioms Lean4Lean.VEnv.rigidPiUniq_iff_piInv_of_propAgreeOn
#print axioms Lean4Lean.VEnv.propAgreeOn_premises_fire
#print axioms Lean4Lean.VEnv.propAgree_conclusion_not_sortUniq
#print axioms Lean4Lean.VEnv.sortUniq_conclusion_gives_propAgree
#print axioms Lean4Lean.VEnv.bothSort_sort_sort
end Audit

end VEnv
end Lean4Lean
