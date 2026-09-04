import Lean4Lean.Theory.Typing.ParamsStruct
import Lean4Lean.Theory.Typing.KCanonical
import Lean4Lean.Theory.Typing.PatAppParams
import Lean4Lean.Theory.Typing.DescendSurplus
import Lean4Lean.Verify.QuotAppParams

/-!
# Is Church--Rosser false at a structure environment?  No -- and here is why not

Round of 2026-09-04, `docs/handoff-paramscr.md` (priors, measurements, hypothesis table).

Two rounds converged on one question.  `ParamsStruct.lean` built `MutField.declParams`, a
`VEnv.Params` instance at a positive-field structure environment with **no hypotheses**, and
flagged that it had not discharged `VEnv.not_crStatement_of_kstep`'s 18 hypotheses there --
"if they are dischargeable, this instance is a counterexample generator".  `DescendSurplus.lean`
refuted the confluence frontier and flagged that its refutation might be vacuous, because "no
`Params` instance in the tree registers an `.app` pattern at all".

## Q1: they are NOT dischargeable, and the failing hypothesis is FALSE, not unproved

`hstep : KStep (A::Γ) (.app e.lift (.bvar 0)) t` is false at `declParams` whenever the Π-domain
is either member of `MutField.decl`.  Two of the eighteen hypotheses (`hΓA` and `hstep`) are
already contradictory, so no work on the other nine can rescue the refutation.

* **§1** (general, `sorryAx`-free): a `K⁺` step at a *variable* major premise **is** the demand
  that the variable be definitionally equal to a constructor spine -- at every instance, with no
  hypothesis on the environment.
* **§2** (general): that demand is refutable at any `Type 0`-valued constant type carrying a
  **fresh axiom** inhabitant.  This is `ShapeVar.lean`'s open `VarAppDisj` row at one shape, and
  it needs *none* of `ConstVar.lean`'s `AxiomConservativity`: the axiom is added by hand, so
  `¬ IsProof` is proved at the extended environment instead of transported back to it, and the
  only general instrument is substitution.
* **§3--§6**: at `declParams` the pattern's constructor leaf is a declared `declEnv` constant and
  neither recursor, both members live in `Type 0` -- so proof irrelevance, the only rule that
  identifies a variable with a constructor, is unavailable -- and `MutField.bigEnv`
  (`NoConfRepair.lean`) already supplies a fresh axiom for **both** members.
* **§7** is the verdict, **§8** its one limit: the domain is pinned *syntactically*.

## Q2: yes, two instances register `.app` patterns, and Round B's refutation FIRES

`VEnv.appParams` (`PatAppParams.lean`) and `VEnv.quotParams` (`Verify/QuotAppParams.lean`) both
register `.app` patterns; at `quotParams` the major premise is a proof of the `Prop`
`Quot.{0} α r`.  **§9.2** fires `not_appDFExtraStatement_of_propMajor'` there, so the frontier
statement is false at a real instance rather than at a hypothetical one.  **§9.1** shows the
same refutation is *contradictory* at `appParams`, where `hne` is false -- so the two `.app`
instances split cleanly, and the discriminating property is that `quotParams`' right-hand sides
are not closed.

Note for the record: `CRStatement` was **already** refuted in the tree before this round, at
`quotParams` (`VEnv.quotParams_not_crStatement`).  This file's Q1 result is the complementary
one -- it is *not* refutable at a structure environment by that route.
-/

namespace Lean4Lean

open VExpr

namespace VEnv

variable [Params]
open Params

/-! ## §1 What a `K⁺` step at a variable major premise costs, at **any** `Params` instance -/

/-- **Every registered `.app` pattern is an ι-shape.**  `Params.pat_app_noApp`
(`KDescend.lean`) says the two children contain no `.app`; this says what they *are*.  Same
proof, one line longer. -/
theorem Params.pat_app_iota {p₁ p₂ : Pattern} {r} (h : Pat (.app p₁ p₂) r) :
    ∃ (rc cn : Lean.Name) (m n : Nat),
      p₁ = (Pattern.const rc).varN m ∧ p₂ = (Pattern.const cn).varN n := by
  obtain ⟨sp, hsp⟩ := pat_simple h
  cases sp with
  | defn c => simp [SimplePattern.toPattern] at hsp
  | iota rc m c n =>
    simp [SimplePattern.toPattern] at hsp
    obtain ⟨rfl, rfl⟩ := hsp
    exact ⟨rc, c, m, n, rfl, rfl⟩

/-- **A `K⁺` step whose major premise is a variable forces a variable-to-constructor-spine
conversion.**  This is the whole content of `KStep`'s `hdq` field once the pattern's argument
side is known to be a `.const`-headed chain (`Params.pat_app_iota`).

No hypothesis beyond the step itself, and no property of the environment. -/
theorem kstep_bvar_ctorConv {Γ : List VExpr} {f t : VExpr} {i : Nat}
    (hstep : KStep Γ (.app f (.bvar i)) t) :
    ∃ (cn : Lean.Name) (ls : List VLevel) (as : List VExpr) (A₀ : VExpr),
      IsDefEq env univs Γ (.bvar i) ((VExpr.const cn ls).mkApp as) A₀ := by
  cases hstep with
  | @mk p₁ p₂ r f' h c A₀ B₀ m1 m2 hpat hm hck hf hdq =>
    obtain ⟨rc, cn, m, n, rfl, rfl⟩ := Params.pat_app_iota hpat
    cases hm with
    | app hm1 hm2 =>
      obtain ⟨ls, as, hlen, rfl, -, -⟩ := Pattern.matches_varN_inv cn n hm2
      exact ⟨cn, ls, as, A₀, hdq⟩

/-! ## §2 The fresh-inhabitant refutation of the variable/constructor-spine row

This is `ShapeVar.lean`'s `VarAppDisj` row at one specific shape: a variable declared at a
`Type 0`-valued *constant* type `S` which carries a **fresh axiom** inhabitant `a`.  The row
in general is open in this tree — §3.1 of `ShapeIndep.lean` records that its `¬ IsProof` guard
transports the wrong way along an environment extension, and that turning it round is
`ConstVar.lean`'s `AxiomConservativity`, an open node.  **This shape needs none of that**: the
axiom is added by hand, so `¬ IsProof a` is proved *at the extended environment* rather than
transported back to it, and the only general instrument used is substitution
(`IsDefEq.instN`). -/

omit [Params] in
/-- **A variable declared at `S` is not definitionally equal to a rule-free constant spine
with a different head, when `S : Type 0` carries a fresh axiom inhabitant.**

Substituting the axiom for the variable turns the conversion into one between two constant
spines, where `constNoConf_of_notIsProof` identifies the heads. -/
theorem bvar_ne_constApp_of_freshAxiom {env env' : VEnv} (henv' : env'.WF)
    (hle : env ≤ env') {a S : Lean.Name}
    (ha : env'.constants a = some ⟨0, .const S []⟩)
    (hS : env'.constants S = some ⟨0, .sort (.succ .zero)⟩)
    (hrfa : env'.RuleFreeHead a) {cn : Lean.Name} (hrfc : env'.RuleFreeHead cn) (hne : a ≠ cn)
    {Γ : List VExpr} (hΓ : OnCtx (VExpr.const S [] :: Γ) (env.IsType 0))
    {ls : List VLevel} {as : List VExpr} {A₀ : VExpr}
    (h : env.IsDefEq 0 (VExpr.const S [] :: Γ) (.bvar 0)
      ((VExpr.const cn ls).mkApp as) A₀) : False := by
  have hax : ∀ {Δ : List VExpr}, env'.HasType 0 Δ ((VExpr.const a []).mkApp [])
      ((VExpr.const S []).mkApp []) := fun {_} => .constDF ha nofun nofun rfl .nil
  have hSty : ∀ {Δ : List VExpr}, env'.HasType 0 Δ (VExpr.const S []) (.sort (.succ .zero)) :=
    fun {_} => .constDF hS nofun nofun rfl .nil
  have hnp : ∀ {Δ : List VExpr}, OnCtx Δ (env'.IsType 0) →
      ¬ env'.IsProof 0 Δ ((VExpr.const a []).mkApp []) := by
    rintro Δ hΔ ⟨p, hp, hep⟩
    obtain ⟨w, hw⟩ := VEnv.WF.uniq' henv' hΔ hep hax
    have h1 : env'.HasType 0 Δ (VExpr.const S []) (.sort .zero) :=
      VEnv.HasType.defeqU_l' henv' hΔ ⟨_, hw⟩ hp
    have h2 : (VLevel.zero : VLevel) ≈ VLevel.succ .zero :=
      VEnv.WF.sortUniq' henv' hΔ trivial trivial h1 hSty
    exact absurd (congrFun h2 []) (by simp [VLevel.eval])
  have hΓ' : OnCtx (VExpr.const S [] :: Γ) (env'.IsType 0) := hΓ.mono (VEnv.IsType.mono hle)
  have hsub := VEnv.IsDefEq.instN (env := env') henv'.ordered
    (e₀ := (VExpr.const a []).mkApp []) hax .zero (h.mono hle)
  rw [VExpr.mkApp_inst] at hsub
  exact hne (VEnv.constNoConf_of_notIsProof henv' 0 (VEnv.patWF_of_wf henv' 0)
    hΓ'.1 (c := a) (c' := cn) (ls := []) (ls' := ls) (as := [])
    hrfa hrfc (hnp hΓ'.1) ⟨_, hsub⟩)

end VEnv

/-! ## §3 `declEnv`'s two recursors, and the constructor-leaf name -/

namespace MutField

/-- The block's first recursor, at the type `addInduct'` gave it. -/
theorem declEnv_Arec : declEnv.constants (Lean.mkRecName aTy.name)
    = some ⟨decl.recUvars, decl.recType 0⟩ :=
  VEnv.addInduct'_recs declEnv_eq.choose_spec (by simp [decl])

/-- The block's second recursor. -/
theorem declEnv_Brec : declEnv.constants (Lean.mkRecName bTy.name)
    = some ⟨decl.recUvars, decl.recType 1⟩ :=
  VEnv.addInduct'_recs declEnv_eq.choose_spec (by simp [decl])

/-- **A constant of `declEnv` stored at a *constructor's* type is neither of the block's two
recursors.**  `Lean4Lean.rec_ne_ctor`'s stored-type argument, instantiated twice. -/
theorem declEnv_ctor_ne_recs {D : VInductDecl'} {j : Nat} {C : VIndCtor}
    (h : declEnv.constants C.name = some ⟨D.uvars, C.type D j⟩) :
    C.name ≠ `MutField.A.rec ∧ C.name ≠ `MutField.B.rec :=
  ⟨fun he => rec_ne_ctor (D := decl) (j := 0) (T := aTy) rfl declEnv_Arec h he.symm,
   fun he => rec_ne_ctor (D := decl) (j := 1) (T := bTy) rfl declEnv_Brec h he.symm⟩

/-! ## §4 The fresh-axiom environment — already in the tree

**Measured before building anything, and it saved the build.**  `MutField.bigEnv`
(`Theory/Typing/NoConfRepair.lean` §5) is `declEnv` plus **three** axioms — `foo : A`,
`foo2 : A`, `bar : B` — with `VEnv.WF` proved from `VEnv.empty`, `RuleFreeHead` proved for
every name that is not one of the two recursors, and both members' sort typings.  So the
fresh inhabitant §2 needs exists for **both** members of the block already; a first draft of
this file rebuilt `declEnv + bar : B` from scratch and it was redundant.

`MutField.B` is uninhabited by closed terms — `bCtor`'s one field has type `∀ p : Prop, p` —
which is why the positive-field member needs an *axiom* and not a term. -/

theorem bigEnv_A : bigEnv.constants `MutField.A = some ⟨0, .sort (.succ .zero)⟩ :=
  declEnv_le_bigEnv.constants declEnv_A

theorem bigEnv_B : bigEnv.constants `MutField.B = some ⟨0, .sort (.succ .zero)⟩ :=
  declEnv_le_bigEnv.constants declEnv_B

/-- A constant of `declEnv` is none of `bigEnv`'s three axioms: each was added to a stage that
already contains `declEnv`, so each name was free there. -/
theorem declEnv_contains_ne_axiom {cn : Lean.Name} (h : declEnv.contains cn) :
    cn ≠ `MutField.foo ∧ cn ≠ `MutField.foo2 ∧ cn ≠ `MutField.bar := by
  obtain ⟨ci, hci⟩ := h
  refine ⟨?_, ?_, ?_⟩ <;> rintro rfl
  · exact absurd (hci.symm.trans (VEnv.addConst_constants_none declEnv_addConst)) nofun
  · exact absurd ((declEnv_le_unitEnv.constants hci).symm.trans
      (VEnv.addConst_constants_none unitEnv_addConst_foo2)) nofun
  · exact absurd
      ((unitEnv_le_twoEnv.constants (declEnv_le_unitEnv.constants hci)).symm.trans
        (VEnv.addConst_constants_none twoEnv_addConst_bar)) nofun

/-! ## §5 The variable/constructor-spine row, refuted at **both** members of the block -/

/-- **At the zero-field member `MutField.A`**, with `foo` as the fresh inhabitant. -/
theorem declEnv_bvar_ne_constApp_A {Γ : List VExpr}
    (hΓ : OnCtx (VExpr.const `MutField.A [] :: Γ) (declEnv.IsType 0))
    {cn : Lean.Name} {ls : List VLevel} {as : List VExpr} {A₀ : VExpr}
    (h1 : cn ≠ `MutField.A.rec) (h2 : cn ≠ `MutField.B.rec) (h3 : declEnv.contains cn)
    (h : declEnv.IsDefEq 0 (VExpr.const `MutField.A [] :: Γ) (.bvar 0)
      ((VExpr.const cn ls).mkApp as) A₀) : False :=
  VEnv.bvar_ne_constApp_of_freshAxiom bigEnv_wf declEnv_le_bigEnv
    (unitEnv_le_bigEnv.constants unitEnv_foo) bigEnv_A
    (bigEnv_ruleFreeHead (by decide) (by decide)) (bigEnv_ruleFreeHead h1 h2)
    (fun he => (declEnv_contains_ne_axiom h3).1 he.symm) hΓ h

/-- **At the positive-field member `MutField.B`** — the member `declParams` is advertised for —
with `bar` as the fresh inhabitant. -/
theorem declEnv_bvar_ne_constApp_B {Γ : List VExpr}
    (hΓ : OnCtx (VExpr.const `MutField.B [] :: Γ) (declEnv.IsType 0))
    {cn : Lean.Name} {ls : List VLevel} {as : List VExpr} {A₀ : VExpr}
    (h1 : cn ≠ `MutField.A.rec) (h2 : cn ≠ `MutField.B.rec) (h3 : declEnv.contains cn)
    (h : declEnv.IsDefEq 0 (VExpr.const `MutField.B [] :: Γ) (.bvar 0)
      ((VExpr.const cn ls).mkApp as) A₀) : False :=
  VEnv.bvar_ne_constApp_of_freshAxiom bigEnv_wf declEnv_le_bigEnv bigEnv_bar bigEnv_B
    (bigEnv_ruleFreeHead (by decide) (by decide)) (bigEnv_ruleFreeHead h1 h2)
    (fun he => (declEnv_contains_ne_axiom h3).2.2 he.symm) hΓ h

/-! ## §6 The two halves joined: no `K⁺` step at a variable of either member -/

/-- `declParams`' pattern table **is** `VEnv.Pat declEnv`, by `rfl` — `paramsOfWF` sets the
field to it and `paramsOfPiInv`/`paramsOfWFAx` are `instance_reducible` wrappers. -/
theorem declParams_Pat {p : Pattern} {r : p.RHS × p.Check} :
    @VEnv.Params.Pat declParams p r ↔ Lean4Lean.Pat declEnv p r := Iff.rfl

/-- **The constructor leaf of any `.app` pattern registered at `declParams` is neither of the
block's recursors nor the fresh axiom.**  Three constructors of `VEnv.Pat`, and the δ one
cannot produce an `.app`. -/
theorem declParams_pat_app_leaf {p₁ p₂ : Pattern} {r}
    (h : @VEnv.Params.Pat declParams (.app p₁ p₂) r) :
    ∃ (rc cn : Lean.Name) (m n : Nat),
      p₁ = (Pattern.const rc).varN m ∧ p₂ = (Pattern.const cn).varN n ∧
      cn ≠ `MutField.A.rec ∧ cn ≠ `MutField.B.rec ∧ declEnv.contains cn := by
  cases declParams_Pat.1 h with
  | iota hcl hargs hTj hC hdf hrec hctor hnp hna =>
    exact ⟨_, _, _, _, rfl, rfl, (declEnv_ctor_ne_recs hctor).1,
      (declEnv_ctor_ne_recs hctor).2, _, hctor⟩
  | quot hdf hlift hmk =>
    exact ⟨_, _, 5, 3, rfl, rfl, by decide, by decide, _, hmk⟩

/-- **`KStep` at `declParams` cannot fire on a variable of the zero-field member.**  §1 turns
the step into a variable-to-constructor-spine conversion; §5 refutes that conversion. -/
theorem declParams_no_kstep_bvar_A {Γ : List VExpr}
    (hΓ : OnCtx (VExpr.const `MutField.A [] :: Γ) (declEnv.IsType 0))
    {f t : VExpr}
    (hstep : @VEnv.KStep declParams (VExpr.const `MutField.A [] :: Γ)
      (.app f (.bvar 0)) t) : False := by
  cases hstep with
  | @mk p₁ p₂ r f' h c A₀ B₀ m1 m2 hpat hm hck hf hdq =>
    obtain ⟨rc, cn, m, n, rfl, rfl, h1, h2, h3⟩ := declParams_pat_app_leaf hpat
    cases hm with
    | app hm1 hm2 =>
      obtain ⟨ls, as, hlen, rfl, -, -⟩ := Pattern.matches_varN_inv cn n hm2
      exact declEnv_bvar_ne_constApp_A hΓ h1 h2 h3 hdq

/-- **…and not on a variable of the positive-field member either.** -/
theorem declParams_no_kstep_bvar_B {Γ : List VExpr}
    (hΓ : OnCtx (VExpr.const `MutField.B [] :: Γ) (declEnv.IsType 0))
    {f t : VExpr}
    (hstep : @VEnv.KStep declParams (VExpr.const `MutField.B [] :: Γ)
      (.app f (.bvar 0)) t) : False := by
  cases hstep with
  | @mk p₁ p₂ r f' h c A₀ B₀ m1 m2 hpat hm hck hf hdq =>
    obtain ⟨rc, cn, m, n, rfl, rfl, h1, h2, h3⟩ := declParams_pat_app_leaf hpat
    cases hm with
    | app hm1 hm2 =>
      obtain ⟨ls, as, hlen, rfl, -, -⟩ := Pattern.matches_varN_inv cn n hm2
      exact declEnv_bvar_ne_constApp_B hΓ h1 h2 h3 hdq

/-- **`declParams`' pattern table is not empty**, so the refutation above is not true for the
dull reason that there is nothing to fire.  `Params.extra_pat` turns `decl`'s first ι-rule —
which `declEnv_defeqs_iotaRule` puts in `declEnv.defeqs` — into a registered pattern.

**What this does not say**, and the distinction is the honest one: it does not say the
registered pattern is an `.app`.  `Lean4Lean.Pat.iota` would give that directly, but its
closedness field `(decl.iotaLam 0 aCtor).Closed` has no `Decidable` instance at this reduction
and `VInductDecl'.iotaLam_closed` routes through `D.IotaCtx`, which is more machinery than this
observation is worth.  See `docs/handoff-paramscr.md` §6.3. -/
theorem declParams_pat_nonempty :
    ∃ (p : Pattern) (r : p.RHS × p.Check), @VEnv.Params.Pat declParams p r := by
  obtain ⟨Δ, L, R, p, r, m1, m2, -, -, hpat, -⟩ :=
    @VEnv.Params.extra_pat declParams [] (decl.iotaRule 0 0 aCtor) []
      trivial declEnv_defeqs_iotaRule nofun rfl
  exact ⟨p, r, hpat⟩

/-! ## §7 The Q1 verdict

`VEnv.not_crStatement_of_kstep`'s hypothesis list, written out in full and in its own order,
with the Π-domain pinned to one of the two members of the block.  **The list is contradictory**,
and only `hΓA` and `hstep` are consumed — so nothing that could be done about the other nine
explicit hypotheses can rescue it.

`¬ CRStatement` is therefore **not** obtained at `declParams` by this route, and the reason is
not that a hypothesis is merely unproved: `hstep` is **false** there. -/

theorem declParams_not_crStatement_of_kstep_hyps_absurd
    {Γ : List VExpr} {e A B t : VExpr} {u : VLevel}
    (hAmem : A = VExpr.const `MutField.A [] ∨ A = VExpr.const `MutField.B [])
    (_hΓ : OnCtx Γ (declEnv.IsType 0))
    (hΓA : OnCtx (A :: Γ) (declEnv.IsType 0))
    (_hA : declEnv.HasType 0 Γ A (.sort u))
    (_he : declEnv.HasType 0 Γ e (.forallE A B))
    (hstep : @VEnv.KStep declParams (A :: Γ) (.app e.lift (.bvar 0)) t)
    (_hlam : ∀ A' e', e ≠ .lam A' e')
    (_hnp : ∀ P, declEnv.HasType 0 Γ P (.sort .zero) → ¬ declEnv.HasType 0 Γ e P)
    (_hrig : ∀ o, @VEnv.ParRed declParams Γ e o → o = e)
    (_hrigA : ∀ A', @VEnv.ParRed declParams Γ A A' → A' = A)
    (_hrigT : ∀ t', @VEnv.ParRed declParams (A :: Γ) t t' → t' = t)
    (_hne : ¬ @VEnv.NormalEq declParams (A :: Γ) (.app e.lift (.bvar 0)) t) : False := by
  rcases hAmem with rfl | rfl
  · exact declParams_no_kstep_bvar_A hΓA hstep
  · exact declParams_no_kstep_bvar_B hΓA hstep

/-- **The same verdict with the surplus hypotheses deleted** — two of the eighteen suffice, and
this is the statement to cite. -/
theorem declParams_kstep_absurd_at_members
    {Γ : List VExpr} {A f t : VExpr}
    (hAmem : A = VExpr.const `MutField.A [] ∨ A = VExpr.const `MutField.B [])
    (hΓA : OnCtx (A :: Γ) (declEnv.IsType 0))
    (hstep : @VEnv.KStep declParams (A :: Γ) (.app f (.bvar 0)) t) : False := by
  rcases hAmem with rfl | rfl
  · exact declParams_no_kstep_bvar_A hΓA hstep
  · exact declParams_no_kstep_bvar_B hΓA hstep

/-! ## §8 The limit of §7, stated exactly

`hAmem` is the whole residual.  What §7 does **not** cover is a Π-domain `A` that is only
*definitionally equal* to one of the two members rather than syntactically equal to it — and
also an `A` that is neither.  Closing it needs the chain

* `A₀ ≈ A.lift` from unique typing at `.bvar 0` (`VEnv.WF.uniq'`, available, hole-tainted);
* `A₀ ≈ (the constructor's result type)`, which needs the constructor **named** — i.e. an
  enumeration of `declEnv`'s constants at their stored types, which the tree does not have as a
  single lemma (`VEnv.addInduct'_constants_inv` plus a `decide` over `decl.allConsts` is the
  route, and separating the *type* constants from the *constructor* constants then needs
  "a constructor's stored type is not a sort");
* un-lifting `A.lift ≈ (member).lift` to `A ≈ member` — `VEnv.IsDefEqU.weakN_iff`, a census
  hole.

None of the three is *false*; all three are work.  So the honest Q1 verdict is: **refuted at
both members, open (not false) for a domain merely convertible to one.**  The statement below
is the residual, named so a later round can attack it rather than re-derive it. -/

/-- The residual of §7: the same conclusion for a Π-domain that is only *convertible* to a
member.  **Not proved here** — this is a definition, so that the gap has a name. -/
def KStepBvarFreeAtConvMembers : Prop :=
  ∀ {Γ : List VExpr} {A f t : VExpr},
    OnCtx (A :: Γ) (declEnv.IsType 0) →
    (declEnv.IsDefEqU 0 Γ A (VExpr.const `MutField.A []) ∨
      declEnv.IsDefEqU 0 Γ A (VExpr.const `MutField.B [])) →
    ¬ @VEnv.KStep declParams (A :: Γ) (.app f (.bvar 0)) t

/-- The syntactic case is the convertible case at `IsDefEqU.rfl`, so §7 is a *lower* bound on
the residual and not a different statement. -/
theorem kStepBvarFreeAtConvMembers_of_syntactic
    (H : KStepBvarFreeAtConvMembers) {Γ : List VExpr} {A f t : VExpr}
    (hAmem : A = VExpr.const `MutField.A [] ∨ A = VExpr.const `MutField.B [])
    (hΓA : OnCtx (A :: Γ) (declEnv.IsType 0)) :
    ¬ @VEnv.KStep declParams (A :: Γ) (.app f (.bvar 0)) t := by
  rcases hAmem with rfl | rfl
  · exact H hΓA (.inl ⟨_, .constDF declEnv_A nofun nofun rfl .nil⟩)
  · exact H hΓA (.inr ⟨_, .constDF declEnv_B nofun nofun rfl .nil⟩)

end MutField

/-! ## §9 Q2: does any instance register an `.app` pattern with a `Prop` major premise?

**Yes, and it has since 2026-09-01.**  `VEnv.appParams` (`Theory/Typing/PatAppParams.lean`) is
built over `cycEnv` — `P : Prop`, `D D2 : P`, `T : Type`, `C : P → T` — and registers the two
`.app` patterns `cycQ = C D`, `cycQ2 = C D2`, whose major-premise slot is typed by the `Prop`
`P`.  So `DescendSurplus.lean:103-104`'s "no `Params` instance in this tree registers an `.app`
pattern at all" is a **stale absence claim**, and `KCanonical.lean`'s `refParams_kSmall`
docstring already carried the dated correction at the time it was written.

**But Round B's refutation is still not thereby instantiated**, and the reason is the one
`PatAppParams.lean` already gives for the two older refutations: at `appParams` the `hne`
hypothesis — "the redex is not `NormalEq` to the rule's right-hand side" — is **false**, both
right-hand sides being closed terms that `NormalEq.appDF` plus `NormalEq.proofIrrel` relate to
the redex.  `not_appDFExtraStatement_of_propMajor'` carries an `hne` of exactly that shape, so
it joins items 2 and 3.  Below is that, machine-checked, for the *new* refutation. -/

namespace VEnv

/-- **Round B's refutation cannot be instantiated at `appParams`.**  Its hypothesis list
(`DescendSurplus.lean`'s `not_appDFExtraStatement_of_propMajor'`, `hbrig` included) is
contradictory here: `appParams_normalEq_rhs` refutes `hne`.

So the verdict on the vacuity question Round B asked is **neither of the two it offered**: an
`.app`-registering instance with a `Prop` major premise exists, so the refutation is not
conditional on a shape that does not exist; but at *that* instance `hne` is false, so the
refutation is still uninstantiated.  What would instantiate it is a registered `.app` table
whose right-hand sides are **not** pairwise `NormalEq` to the redex — which is the same gap
`PatAppParams.lean`'s first caveat records for lemma M3. -/
theorem appParams_no_appDFExtra_refutation {Γ : List VExpr} {p₁ p₂ : Pattern}
    {r : (Pattern.app p₁ p₂).RHS × (Pattern.app p₁ p₂).Check} {f a b B : VExpr} {m1 m2}
    (hΓ : OnCtx Γ (cycEnv.IsType 0))
    (r1 : @Params.Pat appParams (.app p₁ p₂) r)
    (r2 : (Pattern.app p₁ p₂).Matches (.app f b) m1 m2)
    (_r3 : r.2.OK (cycEnv.IsDefEqU 0 Γ) m1 m2)
    (hf : cycEnv.HasType 0 Γ f (.forallE (.const `P []) B))
    (_hA : cycEnv.HasType 0 Γ (.const `P []) (.sort .zero))
    (ha : cycEnv.HasType 0 Γ a (.const `P []))
    (_hb : cycEnv.HasType 0 Γ b (.const `P []))
    (_hrig : ∀ o, @ParRed appParams Γ (.app f a) o → o = .app f a)
    (_hbrig : ∀ o, @ParRed appParams Γ b o → o = b)
    (hne : ¬ @NormalEq appParams Γ (.app f a) (Pattern.RHS.apply m1 m2 r.1)) : False :=
  hne (appParams_normalEq_rhs r1 r2 hΓ hf ha)

/-! ### §9.2 …and at `quotParams` it is NOT vacuous — Round B's refutation fires

**Measured, not assumed** (`scripts/shape.lean`, `HEADS="Lean4Lean.VEnv.Params"`, which lists
every `Params`-valued constant in the built population): the tree has **seven** `Params`
instances — `refParams`, `cycParams`, `propLoopParams`, `propLoopParamsOfWF`,
`MutField.unitParams`, `MutField.declParams`, `VEnv.appParams` — and an eighth I had not been
told about, `VEnv.quotParams` (`Verify/QuotAppParams.lean`, commit `a561fa9`).

`quotParams` registers the `.app` pattern `quotPat` at a `VEnv.WF` environment, and — this is
the point `PatAppParams.lean`'s closing note gets wrong and `QuotAppParams.lean` corrects — its
major premise **is** a proof of a `Prop`: `Quot.{0} α r` is a proposition while the motive `β`
is `Type 0`, so the quotient rule supplies the `Eq.rec` shape by itself.  Its right-hand sides
are also **not** closed (`quotRHS_depends_on_match`), so `appParams`' shortcut — the one that
makes `hne` false there — is unavailable.

So Round B's refutation fires.  Below is it, fired. -/

section
attribute [local instance] quotParams

/-- The matched `Quot.mk` spine at a variable argument is `ParRed`-normal: `hbrig`, the one
hypothesis `not_appDFExtraStatement_of_propMajor'` adds over
`not_parRedStatement_of_propMajor`. -/
theorem qParRed_qMk_bvar {Γ : List VExpr} {u : VLevel} {i : Nat} {o}
    (h : ParRed Γ (qMk u (.bvar i)) o) : o = qMk u (.bvar i) :=
  qParRed_app_bvar (fun _ => qParRed_app_bvar
    (fun _ => qParRed_app_bvar (fun _ => qParRed_const) nofun) nofun) nofun h

/-- **`DescendSurplus.lean`'s frontier refutation, instantiated.**  `AppDFExtraStatement` — the
statement of `NormalEq.appDF_extra_of_descend`, the single frontier lemma between
`NormalEq.descend` and `IsDefEq.church_rosser` — is **false** at `quotParams`.

Round B stated `not_appDFExtraStatement_of_propMajor'` and flagged that it might be "false at
instances of a shape that doesn't exist yet".  It is not: the shape exists, the hypotheses are
all satisfied here, and the conclusion follows.  Together with `quotParams_not_crStatement`
(already in the tree) this makes the whole `propMajor` refutation family non-vacuous. -/
theorem quotParams_not_appDFExtraStatement : ¬ AppDFExtraStatement := by
  obtain ⟨m1, m2, hm, hrhs, hck⟩ := quot_matches .zero (.succ .zero) (.bvar 1)
  refine not_appDFExtraStatement_of_propMajor' (a := .bvar 0) (A := qA .zero)
    qc0_wf quotParams_pat_app hm hck qLift0_hasType qA0_isProp qT_prf (qMk0_hasType qT_x)
    (fun o ho => qParRed_app_bvar (fun _ => qParRed_qLift) nofun ho)
    (fun _ ho => qParRed_qMk_bvar ho) ?_
  intro hne
  have h3 : NormalEq qc0 (.app (qLift .zero (.succ .zero)) (.bvar 0))
      (Pattern.RHS.apply m1 m2 quotRHS) := hne
  rw [hrhs] at h3
  exact not_normalEq_redex_rhs h3

end

end VEnv

end Lean4Lean

/-! ## Axiom census for this file -/

#print axioms Lean4Lean.VEnv.Params.pat_app_iota
#print axioms Lean4Lean.VEnv.kstep_bvar_ctorConv
#print axioms Lean4Lean.VEnv.bvar_ne_constApp_of_freshAxiom
#print axioms Lean4Lean.MutField.declEnv_Arec
#print axioms Lean4Lean.MutField.declEnv_ctor_ne_recs
#print axioms Lean4Lean.MutField.declEnv_contains_ne_axiom
#print axioms Lean4Lean.MutField.declEnv_bvar_ne_constApp_A
#print axioms Lean4Lean.MutField.declEnv_bvar_ne_constApp_B
#print axioms Lean4Lean.MutField.declParams_pat_app_leaf
#print axioms Lean4Lean.MutField.declParams_pat_nonempty
#print axioms Lean4Lean.MutField.declParams_no_kstep_bvar_A
#print axioms Lean4Lean.MutField.declParams_no_kstep_bvar_B
#print axioms Lean4Lean.MutField.declParams_not_crStatement_of_kstep_hyps_absurd
#print axioms Lean4Lean.MutField.declParams_kstep_absurd_at_members
#print axioms Lean4Lean.MutField.kStepBvarFreeAtConvMembers_of_syntactic
#print axioms Lean4Lean.VEnv.appParams_no_appDFExtra_refutation
#print axioms Lean4Lean.VEnv.qParRed_qMk_bvar
#print axioms Lean4Lean.VEnv.quotParams_not_appDFExtraStatement
