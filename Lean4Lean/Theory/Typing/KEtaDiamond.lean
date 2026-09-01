import Lean4Lean.Theory.Typing.PatAppParams

/-!
# Does `KDiamond` suffice?  The λ-congruence induction, run

`docs/handoff-confluence.md` §1 item (2) is the open link between "the confluence layer reduces
to a property of the rule table" and that reduction paying: `KDiamond` (`KDescend.lean`) is
derived from `PatMajorCanonical` (`ParRedCycle.kDiamond_of_patMajorCanonical`, `[propext,
Quot.sound]`), and `KMeasure.etaKDiamond_of_at` reduces `EtaKDiamond` (`KEta.lean`) to the
*equal-height* diamond `EtaKDiamondAt` -- "plus a λ-congruence induction whose base is
`KDiamond`-shaped, and that induction is open".

**This file runs that induction, and the answer is no: `KDiamond` does not suffice.**  The
base case is `KDiamond` verbatim; every `under` layer needs one further fact, and it is not a
fact about the rule table:

> **`PiDomAgree`** -- two Π-typings of one term in one context have convertible domains.

That is Π-injectivity at a shared subject.  It is *forced by the shape of `EtaKDiamond`'s
conclusion*, not by the proof strategy: `EtaK.under` reads its λ-domain off a typing
`Γ ⊢ e : .forallE A B` of the subject, so two derivations at one subject carry two domains
constrained only up to conversion (`KEta.EtaK.under_dom` already says this, and
`appParams_etaK_under_dom_distinct` below exhibits two derivations whose domains differ
*syntactically* at a real `.app` rule table).

`NormalEq.lamDF` is what the induction closes the pair with, and it asks for exactly
`Γ ⊢ A ≡ A₁ : .sort u` and `Γ ⊢ A ≡ A₂ : .sort u`.  **[analysis, not a theorem]** that no other
constructor is an escape: `refl` needs the domains syntactically equal, which
`appParams_etaK_under_dom_distinct` denies; `proofIrrel` needs both sides to be proofs of a
`Prop`, which two λs are not in general; and `etaL`/`etaR` demand
`Γ ⊢ .lam A₂ t₄ : .forallE A₁ B`, which needs the same domain conversion in another guise.  The
negative is *not* proved -- treat it as a conjecture, per `docs/vacuity-ledger.md` §0's fourth
overstatement kind.

## SUPERSEDED IN ITS PREMISE (2026-09-01, later): `KDiamond` is FALSE

`Verify/QuotAppParams.lean`'s `quotParams_not_kDiamond` refutes `KDiamond` at the canonical
`.app`-pattern instance (modulo the injectivity corner), and `quotParams_not_patMajorCanonical`
refutes M3 there.  So `etaKDiamondAt_of_kDiamond`, `etaKDiamond_of_kDiamond`,
`etaKDDiamondAt_of_kDiamond` and the three `*_tree`/`*_holes` assemblies below are **true
implications whose premise cannot be discharged**.  Nothing in this file is wrong; it is
unusable as stated.

**The repair is `Theory/Typing/KDiamondJoin.lean`**, which restates `KDiamond` and M3 with a
*joinability* conclusion (`KDiamondJ`, `PatMajorCanonicalJ`) -- the shape `EtaKDiamond` already
uses -- and reshapes every theorem below onto it: `etaKDiamondAt_of_kDiamondJ`,
`etaKDiamond_of_kDiamondJ`, `etaKDiamond_of_kDiamondJ_holes`, `etaKDDiamondAt_of_kDiamondJ`,
with the same axiom sets.  Two things that file establishes and that should be read with the
table below:

* **`EtaKD` is still needed.**  Joinability repairs only the induction's *base* case;
  `PiDomAgreeK` is created by the `under` case and survives it.  Pinning repairs only the
  `under` case; its base case still needs the false `KDiamond`.  The two repairs are
  independent, and `etaKDDiamondAt_of_kDiamondJ` is both at once.
* **The restatement is not a localisation.**  `quotPat_argJoin_of_kDiamondJ` (`sorryAx`-free)
  shows `KDiamondJ` at the quotient rule table implies Church--Rosser at an application, so the
  "confluence reduces to the rule table" reading of `KDiamond` does not survive either.

## What is proved here

| declaration | content |
|---|---|
| `etaKDiamondAt_of_kDiamond` | `KDiamond → PiDomAgreeK → EtaKBodyTyped → ParRedKSDomConv → EtaKDiamondAt` |
| `etaKDiamond_of_kDiamond` | the same with `EtaKDiamond` as conclusion, via `etaKDiamond_of_at` |
| `etaKDiamond_of_kDiamond_tree` | the last two hypotheses discharged from the tree (and thereby `sorryAx`-tainted) |
| `piDomAgree_tree` | `PiDomAgree`, from `IsDefEq.uniqU` + `IsDefEqU.forallE_inv` -- tainted |
| `etaKDiamond_of_kDiamond_holes` | `KDiamond → EtaKDiamond`, everything discharged in-tree |
| `etaKDDiamondAt_of_kDiamond` | with the η-domain **pinned** (`EtaKD`), `KDiamond` suffices outright: `[propext, Quot.sound]`, cone 235, no hypotheses but `KDiamond` |
| `appParams_etaK_under`, `appParams_etaKDiamondAt_nondegenerate` | instrument 7: the `succ` case fires at `appParams`, at height 1, with two syntactically distinct reducts |
| `appParams_etaK_under_dom_distinct` | two `EtaK` reducts at one subject whose λ-domains differ syntactically |

**[measured] `#print axioms`, this file:** `etaKDiamondAt_of_kDiamond` and
`etaKDiamond_of_kDiamond` are `[propext, Classical.choice, Quot.sound]` -- `sorryAx`-free, hole
cone **empty** (3282 / 3379).  `etaKDDiamondAt_of_kDiamond` is `[propext, Quot.sound]`, cone 235,
hole cone empty.  The six in-tree discharges (`etaKBodyTyped_tree`, `parRedKSDomConv_tree`,
`piDomAgree_tree`, `etaKDiamondAt_of_kDiamond_tree`, `etaKDiamond_of_kDiamond_tree`,
`etaKDiamond_of_kDiamond_holes`) are all `[propext, sorryAx, Classical.choice, Quot.sound]`, with
hole cones **exactly** `{IsDefEqU.forallE_inv_stratified, WF.rigidShapeUniqNS}` -- and
`etaKBodyTyped_tree` only `{IsDefEqU.forallE_inv_stratified}` (cone 3505).  These are the same two
holes the `descend` cone carries; in particular **not** `IsDefEqU.weakN_iff` and **not**
`NormalEq.descend`.  So the η-layer is not a new consumer of the 295-user hole, and it does not
depend on `descend`.

`etaKDiamond_of_kDiamond_holes` is the honest bottom line, and it cuts both ways.  **Relative to the holes the
tree already has** -- unique typing (`IsDefEq.uniq`) and Π-injectivity
(`IsDefEqU.forallE_inv_stratified`) -- `KDiamond` *does* finish the η-layer, and no *new*
obligation appears.  But those two holes are on the known Church-Rosser <-> definitional-inversion
cycle (`docs/research-forallE-inv.md` §4: {inversion at n} → {unique typing at n} → {CR at n+1}
→ {inversion at n+1}), so this is a reduction of confluence to injectivity, and injectivity's
own route runs back through confluence.  `PiDomAgree` is where that cycle touches the η-layer,
and it is **not** a property of the rule table.

`PiDomAgreeK` is `PiDomAgree` restricted to subjects at which an `EtaK` step actually fires --
which is all the induction uses, and is therefore the tighter request.  Restricting a
*hypothesis* of a request is not the localisation move `docs/vacuity-ledger.md` row 94a kills
(that is about restricting a `trans` node's *midpoint*); but the restriction is only as useful
as its non-vacuity, so `appParams_piDomAgreeK_hyps_sat` instantiates it.

## What is **not** proved, and must not be read into the above

* Not that `KDiamond` suffices for `ParRedK` confluence.  `EtaKDiamond` is *one* of the four
  things `KSite7App.lean`'s ledger says `church_rosser`-on-`ParRedK` still owes; `ParRed.triangle`
  needs `KDiamond` *and* `EtaKDiamond`, and items 1, 2 and 4 there are untouched by this file.
* Not that `PiDomAgree` is *equivalent* to Π-injectivity.  It is *implied* by it
  (`piDomAgree_tree`); the converse is not proved and looks false in general, since
  `PiDomAgree`'s hypotheses mention an inhabitant of the Π-type and `IsDefEqU.forallE_inv`'s
  do not.  So `PiDomAgree` is a strictly weaker request, and that is the only good news here.
* Not that the η-tower's *height* is the difficulty.  It is not: `KMeasure.EtaKn.height_uniq`
  already pinned it, and this file consumes that through `etaKDiamond_of_at` only.
-/

namespace Lean4Lean

namespace VEnv

open VExpr

section ParamsSection
variable [Params]
open Params

set_option hygiene false
local notation:65 Γ " ⊢ " e " : " A:36 => HasType env univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 " : " A:36 => IsDefEq env univs Γ e1 e2 A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 => IsDefEqU env univs Γ e1 e2
local notation:65 Γ " ⊢ " e1 " ≡ₚ " e2:30 => NormalEq Γ e1 e2

/-! ## The three hypotheses, named

Two of the three are routine metatheory that the tree already has in tainted form; they are
carried as hypotheses so that the *reduction* can be measured independently of the holes, per
`docs/handoff-confluence.md` §6.3.  The third, `PiDomAgree`, is the substantive one. -/

/-- **`PiDomAgree`**: two Π-typings of *one* term in *one* context have convertible domains.
Π-injectivity at a shared subject; implied by `IsDefEqU.forallE_inv` plus unique typing
(`piDomAgree_tree`), and weaker than either, since it can only be invoked at an *inhabited*
Π-type. -/
def PiDomAgree : Prop :=
  ∀ {Γ : List VExpr} {e A₁ B₁ A₂ B₂ : VExpr}, OnCtx Γ (IsType env univs) →
    Γ ⊢ e : .forallE A₁ B₁ → Γ ⊢ e : .forallE A₂ B₂ → ∃ u, Γ ⊢ A₁ ≡ A₂ : .sort u

/-- **`PiDomAgree` at the subjects the induction actually visits.**  An `EtaK.under` layer's
subject is a constant-headed spine at a registered pattern's head
(`EtaK.spineHead_const`, `EtaK.matches_head`), so the induction never needs the domain
agreement at an arbitrary term.  Strictly weaker than `PiDomAgree`, hence a tighter request. -/
def PiDomAgreeK : Prop :=
  ∀ {Γ : List VExpr} {e w A₁ B₁ A₂ B₂ : VExpr}, OnCtx Γ (IsType env univs) → EtaK Γ e w →
    Γ ⊢ e : .forallE A₁ B₁ → Γ ⊢ e : .forallE A₂ B₂ → ∃ u, Γ ⊢ A₁ ≡ A₂ : .sort u

theorem piDomAgreeK_of_piDomAgree (H : PiDomAgree) : PiDomAgreeK :=
  fun hΓ _ h1 h2 => H hΓ h1 h2

/-- **Subject reduction for the η-tower's body.**  In the tree: `EtaK.defeqU` followed by
`IsDefEqU.of_l`, hence tainted through unique typing (`etaKBodyTyped_tree`). -/
def EtaKBodyTyped : Prop :=
  ∀ {Γ : List VExpr} {A B e t : VExpr}, OnCtx Γ (IsType env univs) →
    Γ ⊢ e : .forallE A B → EtaK (A::Γ) (.app e.lift (.bvar 0)) t → (A::Γ) ⊢ t : B

/-- **A development transports along a conversion of the head of the context.**  In the tree
this is `KSite7.ParRedKS.defeqDFC` specialised (`parRedKSDomConv_tree`); it is tainted, through
`ParRedK.defeqDFC`'s `keta` case, which itself uses `IsDefEqU.of_l`. -/
def ParRedKSDomConv : Prop :=
  ∀ {Γ : List VExpr} {A₁ A₂ t t' T : VExpr} {u : VLevel}, OnCtx Γ (IsType env univs) →
    Γ ⊢ A₁ ≡ A₂ : .sort u → (A₁::Γ) ⊢ t : T → ParRedKS (A₁::Γ) t t' → ParRedKS (A₂::Γ) t t'

/-! ## The λ-congruence induction

The one piece of routine metatheory this needed beyond `KEta.lean` -- `ParRedK.defeqDFC` lifted
to the reflexive-transitive closure -- **was already in the tree**, as
`KSite7.ParRedKS.defeqDFC`.  A first draft of this file re-proved it verbatim and the duplicate
name is what caught that. -/

/-- **The equal-height diamond, from `KDiamond` and the three named facts.**  Induction on the
η-tower height.  The base is `KDiamond` verbatim, with both reductions `rfl` -- so the base is
not merely "`KDiamond`-shaped", it *is* `KDiamond`.  Each `under` layer costs: `PiDomAgreeK`
(reconciling the two λ-domains), `EtaKn.defeqDFC` (relocating the second sub-derivation onto
the first domain -- `sorryAx`-free in the tree), `EtaKBodyTyped` and `ParRedKSDomConv`
(relocating the resulting development back), and `NormalEq.lamDF`. -/
theorem etaKDiamondAt_of_kDiamond (HK : KDiamond) (HD : PiDomAgreeK)
    (HB : EtaKBodyTyped) (HC : ParRedKSDomConv) : EtaKDiamondAt := by
  intro k
  induction k with
  | zero =>
    intro Γ e e₁ e₂ hΓ H1 H2
    cases H1 with | here hs1 =>
    cases H2 with | here hs2 =>
    exact ⟨_, _, .rfl, .rfl, HK hΓ hs1 hs2⟩
  | succ k ih =>
    intro Γ e e₁ e₂ hΓ H1 H2
    cases H1 with | @under _ _ A₁ B₁ t₁ _ hty1 h1 =>
    cases H2 with | @under _ _ A₂ B₂ t₂ _ hty2 h2 =>
    obtain ⟨u, hAA⟩ := HD hΓ (EtaKn.toEtaK (.under hty1 h1)) hty1 hty2
    have hΓ₁ : OnCtx (A₁::Γ) (IsType env univs) := ⟨hΓ, _, hAA.hasType.1⟩
    have h2' : EtaKn k (A₁::Γ) (.app e.lift (.bvar 0)) t₂ :=
      h2.defeqDFC hΓ (.succ .zero hAA.symm)
    obtain ⟨t₃, t₄, r1, r2, hne⟩ := ih hΓ₁ h1 h2'
    have ht₂ : (A₁::Γ) ⊢ t₂ : B₁ := HB hΓ hty1 h2'.toEtaK
    exact ⟨.lam A₁ t₃, .lam A₂ t₄, ParRedKS.lam .rfl r1,
      ParRedKS.lam .rfl (HC hΓ hAA ht₂ r2), .lamDF hAA.hasType.1 hAA hne⟩

/-- **The η-layer, from `KDiamond` and the three named facts.** -/
theorem etaKDiamond_of_kDiamond (HK : KDiamond) (HD : PiDomAgreeK)
    (HB : EtaKBodyTyped) (HC : ParRedKSDomConv) : EtaKDiamond :=
  etaKDiamond_of_at (etaKDiamondAt_of_kDiamond HK HD HB HC)

/-! ## Discharging the two routine facts from the tree

Both are `sorryAx`-tainted, and both taints are pre-existing: they go through
`IsDefEqU.of_l`, i.e. unique typing, which is the tree's `IsDefEq.uniq` hole.  Nothing new is
assumed here -- which is the point of having stated them separately above. -/

theorem etaKBodyTyped_tree : EtaKBodyTyped := by
  intro Γ A B e t hΓ hty H
  have ⟨⟨_, hA⟩, _, _⟩ := (have ⟨_, h⟩ := hty.isType henv hΓ; h.forallE_inv henv)
  have hΓ₁ : OnCtx (A::Γ) (IsType env univs) := ⟨hΓ, _, hA⟩
  have hb0 : (A::Γ) ⊢ .app e.lift (.bvar 0) : B := by
    have := HasType.app (hty.weak (B := A) henv) (.bvar .zero)
    simpa [instN_bvar0] using this
  exact ((H.defeqU hΓ₁).of_l henv hΓ₁ hb0).hasType.2

theorem parRedKSDomConv_tree : ParRedKSDomConv :=
  fun hΓ hAA ht H => ParRedKS.defeqDFC hΓ (.succ .zero hAA) ht H

theorem etaKDiamondAt_of_kDiamond_tree (HK : KDiamond) (HD : PiDomAgreeK) : EtaKDiamondAt :=
  etaKDiamondAt_of_kDiamond HK HD etaKBodyTyped_tree parRedKSDomConv_tree

theorem etaKDiamond_of_kDiamond_tree (HK : KDiamond) (HD : PiDomAgreeK) : EtaKDiamond :=
  etaKDiamond_of_at (etaKDiamondAt_of_kDiamond_tree HK HD)

/-! ## And discharging `PiDomAgree` from the tree: the injectivity edge, named

`IsDefEqU.forallE_inv`'s own cone is `WF.rigidShapeUniqNS` and `WF.sortUniq'`, both of which
bottom out in `IsDefEqU.forallE_inv_stratified`; `IsDefEq.uniqU` bottoms out in the same place
(`Injectivity.lean`, `UniqueTyping.lean`).  So this one line is where the η-layer of confluence
becomes a consumer of the injectivity corner. -/

theorem piDomAgree_tree : PiDomAgree := fun hΓ h1 h2 =>
  (IsDefEqU.forallE_inv henv hΓ (h1.uniqU henv hΓ h2)).1

/-- **`KDiamond → EtaKDiamond`, with everything discharged in-tree.**  Tainted, and by
pre-existing holes only: no new obligation is created by the η-layer. -/
theorem etaKDiamond_of_kDiamond_holes (HK : KDiamond) : EtaKDiamond :=
  etaKDiamond_of_kDiamond_tree HK (piDomAgreeK_of_piDomAgree piDomAgree_tree)

end ParamsSection

/-! ## Instrument 7: the `under` layer, and the domain slack, at a real `.app` rule table

Everything above is a reduction; this section instantiates it.  `refParams` is no use --
`KStep` is empty there, so `EtaK` is (`refParams_no_etaK`) and every statement in this file is
vacuous.  `appParams` (`PatAppParams.lean`) is the tree's only `Params` instance registering
`.app` patterns, and it does supply an `under` layer:

`C : P → T` has `appDepth 0` and the registered patterns have function-side `depth 0`, so
`KMeasure.EtaKn.fuel_eq` says every `EtaK` derivation at `.const C []` is a tower of height
exactly `1`.  Both rules fire on the η-expansion `C (.bvar 0)`, the variable being made
definitionally equal to `D` (resp. `D2`) by proof irrelevance -- so the *`succ` case* of the
induction above is instantiated, with two syntactically distinct reducts. -/

section
attribute [local instance] appParams

/-- The other rule at the same η-expanded redex: `C D2 ⟶ C D` fires on `C (.bvar 0)` too, by
proof irrelevance against `D2`. -/
theorem appParams_kstep_bvar_toD : KStep appCtx (.app (.const `C []) (.bvar 0)) cycG :=
  .mk (p₁ := .const `C) (p₂ := .const `D2) (r := appRuleD2)
    AppPat.d2 (.app .const .const) trivial cycEnv_hasC
    (.proofIrrel cycEnv_hasP appCtx_bvar0 cycEnv_hasD2)

theorem appParams_lift_C : (VExpr.const `C []).lift = .const `C [] := rfl

theorem appCtx_eq : appCtx = [VExpr.const `P []] := rfl

/-- **An `EtaK` step with a genuine `under` layer**, at the tree's only `.app` rule table.  This
is what makes the `succ` case of `etaKDiamondAt_of_kDiamond` non-vacuous. -/
theorem appParams_etaK_under : EtaK [] (.const `C []) (.lam (.const `P []) cycG2) :=
  .under cycEnv_hasC (.here appParams_stuck_fires.2)

theorem appParams_etaK_under' : EtaK [] (.const `C []) (.lam (.const `P []) cycG) :=
  .under cycEnv_hasC (.here appParams_kstep_bvar_toD)

/-- Counted, at height `1` -- which `EtaKn.height_uniq` forces, `.const C []` having
`appDepth 0` against a function-side pattern depth of `0`. -/
theorem appParams_etaKn_under : EtaKn 1 [] (.const `C []) (.lam (.const `P []) cycG2) :=
  .under cycEnv_hasC (.here appParams_stuck_fires.2)

theorem appParams_etaKn_under' : EtaKn 1 [] (.const `C []) (.lam (.const `P []) cycG) :=
  .under cycEnv_hasC (.here appParams_kstep_bvar_toD)

/-- **The `succ` case is instantiated, and its conclusion is not an instance of `refl`.**  Two
`EtaKn 1` derivations at one subject, with syntactically distinct reducts, and the `NormalEq`
the diamond must produce is `lamDF` over `proofIrrel` -- exactly the constructor the induction
uses. -/
theorem appParams_etaKDiamondAt_nondegenerate :
    EtaKn 1 [] (.const `C []) (.lam (.const `P []) cycG2) ∧
      EtaKn 1 [] (.const `C []) (.lam (.const `P []) cycG) ∧
      (VExpr.lam (.const `P []) cycG2) ≠ .lam (.const `P []) cycG ∧
      NormalEq [] (.lam (.const `P []) cycG2) (.lam (.const `P []) cycG) :=
  ⟨appParams_etaKn_under, appParams_etaKn_under', by simp,
    .lamDF cycEnv_hasP cycEnv_hasP
      (.appDF cycEnv_hasC cycEnv_hasC cycEnv_hasD2 cycEnv_hasD (.refl cycEnv_hasC)
        (.proofIrrel cycEnv_hasP cycEnv_hasD2 cycEnv_hasD))⟩

/-! ### The domain slack is real *here*, not only in principle

`KEta.EtaK.under_dom` says an `under` layer's λ-domain is determined only up to conversion.
`altP` below is `(fun X : Prop => X) P`: definitionally `P`, syntactically not.  So the same
subject `.const C []` has two `EtaK` reducts whose **domains** differ syntactically, and
`NormalEq.refl` is unavailable for the pair however the bodies are reduced.  That is why
`PiDomAgree` is load-bearing rather than an artefact of the proof. -/

/-- `(fun X : Prop => X) P` -- definitionally `P`, syntactically distinct from it. -/
abbrev altP : VExpr := .app (.lam (.sort .zero) (.bvar 0)) (.const `P [])

theorem altP_ne_P : altP ≠ .const `P [] := by simp

theorem altP_defeq_P : cycEnv.IsDefEq 0 [] altP (.const `P []) (.sort .zero) := by
  have := IsDefEq.beta (env := cycEnv) (uvars := 0) (Γ := []) (A := .sort .zero)
    (e := .bvar 0) (B := .sort .zero) (.bvar .zero) cycEnv_hasP
  simpa [VExpr.inst] using this

/-- **Two `EtaK` derivations at one subject whose λ-domains differ syntactically.**  Same body
`cycG2`; only the domain moves. -/
theorem appParams_etaK_under_dom_distinct :
    EtaK [] (.const `C []) (.lam (.const `P []) cycG2) ∧
      EtaK [] (.const `C []) (.lam altP cycG2) ∧ altP ≠ .const `P [] :=
  ⟨appParams_etaK_under,
    EtaK.under_dom trivial cycEnv_hasC cycEnv_hasT altP_defeq_P.symm
      (.here appParams_stuck_fires.2),
    altP_ne_P⟩

/-! ### `PiDomAgreeK`'s hypotheses are satisfiable, and not only at equal domains

The subject `.const C []` carries the two Π-typings `∀ P. T` and `∀ altP. T` -- the second by
`defeqDF` over `forallEDF` -- and an `EtaK` step fires on it.  So the request is non-vacuous at
`appParams` **with syntactically distinct domains**, which is the case that matters: at equal
domains `PiDomAgreeK` is discharged by `refl` and says nothing. -/

theorem appParams_hasC_altP :
    cycEnv.HasType 0 [] (.const `C []) (.forallE altP (.const `T [])) :=
  .defeqDF (u := .imax .zero (.succ .zero))
    (.forallEDF altP_defeq_P.symm (cycEnv_hasT (Γ := [VExpr.const `P []])))
    cycEnv_hasC

theorem appParams_piDomAgreeK_hyps_sat :
    EtaK [] (.const `C []) (.lam (.const `P []) cycG2) ∧
      cycEnv.HasType 0 [] (.const `C []) (.forallE (.const `P []) (.const `T [])) ∧
      cycEnv.HasType 0 [] (.const `C []) (.forallE altP (.const `T [])) ∧
      altP ≠ .const `P [] :=
  ⟨appParams_etaK_under, cycEnv_hasC, appParams_hasC_altP, altP_ne_P⟩

/-- And the request is **true** at that instantiation, on the nose. -/
theorem appParams_piDomAgreeK_at :
    ∃ u, cycEnv.IsDefEq 0 [] (.const `P []) altP (.sort u) :=
  ⟨_, altP_defeq_P.symm⟩

/-! **What is NOT claimed, and the contrast with M3 is the point.**
`appParams_patMajorCanonical` *proves* M3 at `appParams`; nothing here proves `PiDomAgreeK`
there.  Its `∀` ranges over all Π-typings of all `EtaK` subjects, and typings are closed under
`defeqDF`, so discharging it at `cycEnv` would need Π-injectivity for `cycEnv` -- which is the
open thing.  So the two statements sit at different grades of evidence: M3 survived its first
real rule table, `PiDomAgreeK` has only been shown non-vacuous at one.

At `refParams` the request is vacuous, for the reason everything else in this corner is: `EtaK`
is empty there. -/

theorem refParams_piDomAgreeK : @PiDomAgreeK refParams :=
  fun _ h _ _ => absurd h refParams_no_etaK

theorem refParams_etaKBodyTyped : @EtaKBodyTyped refParams :=
  fun _ _ h => absurd h refParams_no_etaK

/-! ### The degenerate instances

`PiDomAgree` at `A₁ = A₂` is `refl`, so the statement is trivially satisfiable and says nothing
there; the content is entirely at distinct domains, which the witness above supplies.  At the
empty context and at tower height `0` the statement is `KDiamond` itself. -/

theorem piDomAgree_degenerate {Γ : List VExpr} {e A B : VExpr}
    (hΓ : OnCtx Γ (cycEnv.IsType 0)) (h : cycEnv.HasType 0 Γ e (.forallE A B)) :
    ∃ u, cycEnv.IsDefEq 0 Γ A A (.sort u) := by
  obtain ⟨_, h'⟩ := h.isType cycEnv_wf hΓ
  exact (h'.forallE_inv cycEnv_wf).1

end

/-! ## A route past the blocker: pin the η-expansion's domain

`PiDomAgree` is needed for exactly one reason: `EtaK.under` reads its λ-domain off an
*arbitrary* Π-typing of the subject, so two derivations at one subject can disagree on it
(`appParams_etaK_under_dom_distinct` above).  `EtaK` is this development's own design, not
Lean's, so the alternative is to pin the domain.

`EtaKD` below is `EtaKn` with `under` restricted to a domain read off a function `dom` of the
subject.  Then two derivations of equal height at one subject have the *same* domain, the two
sub-derivations live in the *same* context, and the diamond needs **`KDiamond` and nothing
else** -- no `PiDomAgree`, and not even the two routine facts, since nothing has to be
relocated.  `etaKDDiamondAt_of_kDiamond` measures `[propext, Quot.sound]` -- no `sorryAx` and no
`Classical.choice`, the same axiom set as `kDiamond_of_patMajorCanonical`.  (`under` carries the
domain's own sort typing, which `EtaKn.under` leaves to be recovered by inversion; that is what
keeps `Classical.choice` -- entering through `VEnv.WF.ordered` -- out.)

**What this does and does not buy.**  It shows the η-layer's dependence on injectivity is an
artefact of `EtaK`'s statement rather than of confluence, and it says precisely what to change.
It does **not** exhibit a usable `dom`, and the obligation it creates is real: `ParRedK`'s two
refutation-kills (`KEta.not_crStatement_of_kstep_dead`, `not_parRedStatement_of_hK_dead`) build
their `EtaK` step at the domain of a Π-typing *given to them*, so under pinning they need
`dom e` to be defined and Π-typing-derivable at that subject.  For a `dom` computed from the
head constant's declared type that is a statement about spine typing and the rule table -- which
is where §1 wants the residual -- but it is not proved here, and until it is, `EtaKD` is a
*sub*-relation of `EtaKn` (`EtaKD.toEtaKn`) and the kills are stated for the larger one. -/

section ParamsSection2
variable [Params]
open Params

set_option hygiene false
local notation:65 Γ " ⊢ " e " : " A:36 => HasType env univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 " : " A:36 => IsDefEq env univs Γ e1 e2 A

/-- `EtaKn` with the `under` layer's domain pinned by `dom`. -/
inductive EtaKD (dom : VExpr → Option VExpr) : Nat → List VExpr → VExpr → VExpr → Prop where
  | here {Γ : List VExpr} {e t : VExpr} : KStep Γ e t → EtaKD dom 0 Γ e t
  | under {Γ : List VExpr} {e A B t : VExpr} {u : VLevel} {k : Nat} :
      dom e = some A → Γ ⊢ A : .sort u → Γ ⊢ e : .forallE A B →
      EtaKD dom k (A::Γ) (.app e.lift (.bvar 0)) t → EtaKD dom (k+1) Γ e (.lam A t)

/-- Pinning only removes derivations. -/
theorem EtaKD.toEtaKn {dom : VExpr → Option VExpr} {k : Nat} {Γ : List VExpr} {e e' : VExpr}
    (H : EtaKD dom k Γ e e') : EtaKn k Γ e e' := by
  induction H with
  | here h => exact .here h
  | under _ _ h _ ih => exact .under h ih

/-- **With the domain pinned, `KDiamond` suffices outright.**  Compare
`etaKDiamondAt_of_kDiamond`, which needs three further hypotheses; the whole difference is
`Option.some.inj` on the two `dom` equations. -/
theorem etaKDDiamondAt_of_kDiamond (HK : KDiamond) {dom : VExpr → Option VExpr} :
    ∀ {k : Nat} {Γ : List VExpr} {e e₁ e₂ : VExpr}, OnCtx Γ (IsType env univs) →
      EtaKD dom k Γ e e₁ → EtaKD dom k Γ e e₂ →
      ∃ e₃ e₄, ParRedKS Γ e₁ e₃ ∧ ParRedKS Γ e₂ e₄ ∧ NormalEq Γ e₃ e₄ := by
  intro k
  induction k with
  | zero =>
    intro Γ e e₁ e₂ hΓ H1 H2
    cases H1 with | here hs1 =>
    cases H2 with | here hs2 =>
    exact ⟨_, _, .rfl, .rfl, HK hΓ hs1 hs2⟩
  | succ k ih =>
    intro Γ e e₁ e₂ hΓ H1 H2
    cases H1 with | @under _ _ A₁ B₁ t₁ _ _ hd1 hA hty1 h1 =>
    cases H2 with | @under _ _ A₂ B₂ t₂ _ _ hd2 _ hty2 h2 =>
    cases Option.some.inj (hd1.symm.trans hd2)
    have hΓ₁ : OnCtx (A₁::Γ) (IsType env univs) := ⟨hΓ, _, hA⟩
    obtain ⟨t₃, t₄, r1, r2, hne⟩ := ih hΓ₁ h1 h2
    exact ⟨.lam A₁ t₃, .lam A₁ t₄, ParRedKS.lam .rfl r1, ParRedKS.lam .rfl r2,
      .lamDF hA hA hne⟩

end ParamsSection2

section
attribute [local instance] appParams

/-- Non-vacuity of the pinned relation at the real `.app` table: the `under` witness above is
an `EtaKD` derivation for the constant domain function at `P`. -/
theorem appParams_etaKD_under :
    EtaKD (fun _ => some (.const `P [])) 1 [] (.const `C []) (.lam (.const `P []) cycG2) :=
  .under rfl cycEnv_hasP cycEnv_hasC (.here appParams_stuck_fires.2)

theorem appParams_etaKD_under' :
    EtaKD (fun _ => some (.const `P [])) 1 [] (.const `C []) (.lam (.const `P []) cycG) :=
  .under rfl cycEnv_hasP cycEnv_hasC (.here appParams_kstep_bvar_toD)

/-- And the pinned diamond is instantiated at those two, from `appParams_kDiamond` alone. -/
theorem appParams_etaKD_diamond :
    ∃ e₃ e₄, ParRedKS [] (.lam (.const `P []) cycG2) e₃ ∧
      ParRedKS [] (.lam (.const `P []) cycG) e₄ ∧ NormalEq [] e₃ e₄ :=
  etaKDDiamondAt_of_kDiamond appParams_kDiamond trivial
    appParams_etaKD_under appParams_etaKD_under'

end

end VEnv

end Lean4Lean
