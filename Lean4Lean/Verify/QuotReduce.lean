import Lean4Lean.Verify.TypeChecker.Reduce
import Lean4Lean.Theory.Typing.PatWF

/-!
# Quotient reduction, abstract side

`quotReduceRec` (`Lean4Lean/Quot.lean`) is the kernel's ι-step for `Quot`: it rewrites
`Quot.lift α r β f h (Quot.mk α' r' a)` to `f a` and `Quot.ind α r β f (Quot.mk α' r' a)` to
`f a`.  `quotReduceRec.WF` (`Verify/TypeChecker/WHNF.lean`) has to justify both against the
abstract theory.  This file supplies the two abstract facts, plus the environment facts they
need, so that the `Verify` side is only spine bookkeeping.

## What is new here, and what is borrowed

`Theory/Typing/PatWF.lean`'s `patWF_quot` already fires `quotDefEq` at an arbitrary match of
`quotPat` — but it **assumes** the reconciliation between the two spines
(`quotCheck.OK`: `α ≡ α'`, `r ≡ r'`, `u ≈ u'`), because a `Pat` obligation comes with its
check discharged by the caller.  The checker has no such gift: `quotReduceRec` fires on a
syntactic match and nothing more.  So the work here is to *derive* the three check clauses
from the typing of the redex alone, which is fact (B) — `IsDefEqU.const_app_inv` at `Quot` —
applied to the two types the major premise carries:

* `Quot α r`, because it sits in `Quot.lift`'s sixth argument slot;
* `Quot α' r'`, because it is a `Quot.mk α' r'` spine.

Uniqueness of typing equates the two, and (B) at `Quot` splits it.  (B)'s side condition is
`VEnv.RuleFreeHead ``Quot``, which `TrEnv.ruleFreeHead_quot`
(`Verify/TypeChecker/Reduce.lean`) supplies from `quotInit = true`.

`Quot.ind` has **no** `VDefEq` in this tree — `addQuot` registers `quotDefEq` only — so its
reduction cannot be a rule firing.  It is `IsDefEq.proofIrrel`: `Quot.ind`'s motive lands in
`Prop`, both sides inhabit propositions, and the same reconciliation shows those two
propositions are defeq.
-/

namespace Lean4Lean

/-! ## Environment facts at `quotInit = true` -/

/-- **`quotInit = true` means an `addQuot` happened, and nothing after it can remove what it
added.**  One induction serving all five quotient facts; each is then a `≤` transport.
Modelled on `TrEnv'.quotInit_contains`, and vacuous in `induct` for the same reason. -/
theorem TrEnv'.quotInit_addQuot (H : TrEnv' safety C true venv) :
    ∃ env₀ env₁ : VEnv, env₀.addQuot = some env₁ ∧ env₁ ≤ venv := by
  generalize hQ : true = Q at H
  induction H with
  | empty => cases hQ
  | ignore _ _ _ ih => exact ih hQ
  | «axiom» _ _ _ hadd _ ih =>
    have ⟨_, _, h, hle⟩ := ih hQ; exact ⟨_, _, h, hle.trans (VEnv.addConst_le hadd)⟩
  | defn _ _ _ hadd _ ih =>
    have ⟨_, _, h, hle⟩ := ih hQ
    exact ⟨_, _, h, hle.trans ((VEnv.addConst_le hadd).trans VEnv.addDefEq_le)⟩
  | thm _ _ _ _ hadd _ ih =>
    have ⟨_, _, h, hle⟩ := ih hQ; exact ⟨_, _, h, hle.trans (VEnv.addConst_le hadd)⟩
  | «opaque» _ _ _ hadd _ ih =>
    have ⟨_, _, h, hle⟩ := ih hQ; exact ⟨_, _, h, hle.trans (VEnv.addConst_le hadd)⟩
  | unsafeDef _ _ _ _ _ hadd _ _ ih =>
    have ⟨_, _, h, hle⟩ := ih hQ
    exact ⟨_, _, h, hle.trans ((VEnv.addConsts_le hadd).trans VEnv.addDefEqs_le)⟩
  | quot _ hadd _ _ => exact ⟨_, _, hadd.to_addQuot, VEnv.LE.rfl⟩
  | induct _ hadd => cases hadd

/-- The five quotient facts, at any `TrEnv'` environment with `quotInit = true`. -/
theorem TrEnv'.quotFacts (H : TrEnv' safety C true venv) :
    venv.constants ``Quot = some quotConst ∧
    venv.constants ``Quot.mk = some quotMkConst ∧
    venv.constants ``Quot.lift = some quotLiftConst ∧
    venv.constants ``Quot.ind = some quotIndConst ∧
    venv.defeqs quotDefEq := by
  obtain ⟨_, _, h, hle⟩ := H.quotInit_addQuot
  exact ⟨hle.1 (VEnv.addQuot_quot h), hle.1 (VEnv.addQuot_quotMk h),
    hle.1 (VEnv.addQuot_quotLift h), hle.1 (VEnv.addQuot_quotInd h),
    hle.2 (VEnv.addQuot_defeq h)⟩

theorem TrEnv.quotFacts (H : TrEnv safety env venv) (hq : env.quotInit = true) :
    venv.constants ``Quot = some quotConst ∧
    venv.constants ``Quot.mk = some quotMkConst ∧
    venv.constants ``Quot.lift = some quotLiftConst ∧
    venv.constants ``Quot.ind = some quotIndConst ∧
    venv.defeqs quotDefEq :=
  TrEnv'.quotFacts (safety := safety) (C := env.constants) (hq ▸ H)

/-! ## The reconciliation, derived rather than assumed -/

namespace VEnv

open VExpr (mkPi mkLams mkApp instAll instTele)

variable {env : VEnv} {U : Nat} {Γ : List VExpr}

/-- **Fact (B) at `Quot`, read off a `Quot.lift`/`Quot.mk` redex.**

The three conclusions are exactly `quotCheck`'s three clauses.  `patWF_quot` receives them as
`quotCheck.OK`; the checker has to earn them, and this is where. -/
theorem quotLift_reconcile (henv : env.WF) (hpi : env.PiInv U)
    (hlift : env.constants ``Quot.lift = some quotLiftConst)
    (hmkc : env.constants ``Quot.mk = some quotMkConst)
    (hquot : env.RuleFreeHead ``Quot)
    (hΓ : OnCtx Γ (env.IsType U))
    {ls ls' : List VLevel} {a1 a2 a3 a4 a5 b1 b2 b3 A : VExpr}
    (hT : env.HasType U Γ ((VExpr.const ``Quot.lift ls).mkApp
      ([a1,a2,a3,a4,a5] ++ [(VExpr.const ``Quot.mk ls').mkApp [b1,b2,b3]])) A) :
    env.IsDefEqU U Γ a1 b1 ∧ env.IsDefEqU U Γ a2 b2 ∧
      (ls.getD 0 .zero ≈ ls'.getD 0 .zero) := by
  -- the recursor's level list
  obtain ⟨T0, hT0⟩ := HasType.mkApp_head henv.ordered hΓ _ _ _ hT
  obtain ⟨ci, hci, hlsWF, hlslen⟩ := HasType.const_inv henv.ordered hΓ hT0
  rw [hlift] at hci; cases hci
  have hfun : env.HasType U Γ (.const ``Quot.lift ls)
      (VExpr.mkPi (quotLiftDoms.map (VExpr.instL ls)) (VExpr.bvar 3)) := by
    have h := HasType.const (env := env) (U := U) (Γ := Γ) hlift hlsWF hlslen
    rwa [quotLift_type_eq, VExpr.instL_mkPi, show (VExpr.bvar 3).instL ls = .bvar 3 from rfl] at h
  have hargsLift : env.HasArgs U Γ (quotLiftDoms.map (VExpr.instL ls))
      ([a1,a2,a3,a4,a5] ++ [(VExpr.const ``Quot.mk ls').mkApp [b1,b2,b3]]) :=
    HasArgs.of_mkApp' henv hpi hΓ _ rfl hfun hT
  rw [quotLiftDoms_eq, List.map_append, List.map_cons, List.map_nil] at hargsLift
  obtain ⟨hAs, hmaj⟩ :=
    HasArgs.concat_inv (env := env) (U := U) (Γ := Γ)
      (As := (quotTele.take 5).map (VExpr.instL ls))
      (A := (((VExpr.const `Quot [VLevel.param 0]).app (VExpr.bvar 4)).app
        (VExpr.bvar 3)).instL ls)
      (as := [a1,a2,a3,a4,a5]) (a := (VExpr.const ``Quot.mk ls').mkApp [b1,b2,b3])
      rfl hargsLift
  rw [show ((((VExpr.const `Quot [VLevel.param 0]).app (VExpr.bvar 4)).app
        (VExpr.bvar 3)).instL ls)
      = (((VExpr.const `Quot [ls.getD 0 .zero]).app (VExpr.bvar 4)).app (VExpr.bvar 3)) from rfl,
    VExpr.instAll_app, VExpr.instAll_app, VExpr.instAll_const,
    instAll_bvar_get0 (t := 0) rfl rfl, instAll_bvar_get0 (t := 1) rfl rfl] at hmaj
  -- the constructor's level list, and the type its own spine gives it
  obtain ⟨T1, hT1⟩ := HasType.mkApp_head henv.ordered hΓ _ _ _ hmaj
  obtain ⟨ci', hci', hls'WF, hls'len⟩ := HasType.const_inv henv.ordered hΓ hT1
  rw [hmkc] at hci'; cases hci'
  have hmkfun : env.HasType U Γ (.const ``Quot.mk ls')
      (VExpr.mkPi (quotMkDoms.map (VExpr.instL ls'))
        ((((VExpr.const `Quot [VLevel.param 0]).app (VExpr.bvar 2)).app
          (VExpr.bvar 1)).instL ls')) := by
    have h := HasType.const (env := env) (U := U) (Γ := Γ) hmkc hls'WF hls'len
    rwa [quotMk_type_eq, VExpr.instL_mkPi] at h
  have hargsMk : env.HasArgs U Γ (quotMkDoms.map (VExpr.instL ls')) [b1,b2,b3] :=
    HasArgs.of_mkApp' henv hpi hΓ _ rfl hmkfun hmaj
  have hmkType := HasType.mkApp' hargsMk hmkfun
  rw [show ((((VExpr.const `Quot [VLevel.param 0]).app (VExpr.bvar 2)).app
        (VExpr.bvar 1)).instL ls')
      = (((VExpr.const `Quot [ls'.getD 0 .zero]).app (VExpr.bvar 2)).app (VExpr.bvar 1)) from rfl,
    VExpr.instAll_app, VExpr.instAll_app, VExpr.instAll_const,
    instAll_bvar_get0 (t := 0) rfl rfl, instAll_bvar_get0 (t := 1) rfl rfl] at hmkType
  -- uniqueness of typing, then fact (B) at `Quot`
  have huniq : env.IsDefEqU U Γ (((VExpr.const `Quot [ls.getD 0 .zero]).app a1).app a2)
      (((VExpr.const `Quot [ls'.getD 0 .zero]).app b1).app b2) :=
    hmaj.uniqU henv hΓ hmkType
  obtain ⟨hlv, hargs⟩ := IsDefEqU.const_app_inv henv hΓ (c := ``Quot)
    (ls := [ls.getD 0 .zero]) (ls' := [ls'.getD 0 .zero]) (as := [a1,a2]) (as' := [b1,b2])
    hquot (hmaj.isType henv.ordered hΓ) huniq
  let .cons h1 (.cons h2 .nil) := hargs
  let .cons hl .nil := hlv
  exact ⟨h1, h2, hl⟩

/-- **The `Quot.lift` ι-step, justified.**  `patWF_quot` does the rule firing; this supplies
the check it assumes, from the redex's typing alone, and reads the right-hand side back as the
term `quotReduceRec` actually builds. -/
theorem quotLift_reduce (henv : env.WF) (hpi : env.PiInv U)
    (hdf : env.defeqs quotDefEq)
    (hlift : env.constants ``Quot.lift = some quotLiftConst)
    (hmkc : env.constants ``Quot.mk = some quotMkConst)
    (hquot : env.RuleFreeHead ``Quot)
    (hΓ : OnCtx Γ (env.IsType U))
    {ls ls' : List VLevel} {a1 a2 a3 a4 a5 b1 b2 b3 A : VExpr}
    (hT : env.HasType U Γ ((VExpr.const ``Quot.lift ls).mkApp
      ([a1,a2,a3,a4,a5] ++ [(VExpr.const ``Quot.mk ls').mkApp [b1,b2,b3]])) A) :
    env.IsDefEqU U Γ ((VExpr.const ``Quot.lift ls).mkApp
      ([a1,a2,a3,a4,a5] ++ [(VExpr.const ``Quot.mk ls').mkApp [b1,b2,b3]])) (.app a4 b3) := by
  obtain ⟨hc1, hc2, hclv⟩ := quotLift_reconcile henv hpi hlift hmkc hquot hΓ hT
  obtain ⟨m1, m2, hm, hm1l, hm1r, hasr0, hbsr0⟩ :=
    matches_iota_paths ``Quot.lift ``Quot.mk ls ls' (m := 5) (n := 3)
      [a1,a2,a3,a4,a5] [b1,b2,b3] rfl rfl
  have hasr := hasr0; have hbsr := hbsr0
  rw [argPaths5] at hasr
  rw [argPaths3] at hbsr
  simp only [List.map_cons, List.map_nil] at hasr hbsr
  injection hasr with ha1 hasr; injection hasr with ha2 hasr
  injection hasr with ha3 hasr; injection hasr with ha4 hasr
  injection hasr with ha5 hasr
  injection hbsr with hb1 hbsr; injection hbsr with hb2 hbsr
  injection hbsr with hb3e hbsr
  have hck : quotCheck.OK (env.IsDefEqU U Γ) m1 m2 := by
    refine iotaCheck_OK.2 ⟨?_, ?_, ?_⟩
    · rw [show ((Pattern.argPaths (.const ``Quot.lift) 5).take 2).zip
            ((Pattern.argPaths (.const ``Quot.mk) 3).take 2)
          = [(some (some (some (some none))), some (some none)),
             (some (some (some none)), some none)] from rfl]
      intro xy hxy
      rcases hxy with _ | ⟨_, hxy⟩
      · show env.IsDefEqU U Γ (m2 (Sum.inl (some (some (some (some none))))))
          (m2 (Sum.inr (some (some none))))
        rw [show m2 (Sum.inl (some (some (some (some none))))) = a1 from ha1,
          show m2 (Sum.inr (some (some none))) = b1 from hb1]
        exact hc1
      · rcases hxy with _ | ⟨_, hxy⟩
        · show env.IsDefEqU U Γ (m2 (Sum.inl (some (some (some none)))))
            (m2 (Sum.inr (some none)))
          rw [show m2 (Sum.inl (some (some (some none)))) = a2 from ha2,
            show m2 (Sum.inr (some none)) = b2 from hb2]
          exact hc2
        · cases hxy
    · intro xy hxy; simp at hxy
    · intro ij hij
      cases hij with
      | tail _ h => cases h
      | head =>
        rw [show (m1 (Pattern.LPath.head (SimplePattern.iota ``Quot.lift 5 ``Quot.mk 3).toPattern))
            = ls from hm1l _,
          show (m1 (iotaLeafCtor ``Quot.lift ``Quot.mk 5 3)) = ls' from hm1r _]
        exact hclv
  have h := patWF_quot henv hpi hdf hlift hmkc hm hΓ hT hck
  have hgoal : Pattern.RHS.apply m1 m2 quotRHS = .app a4 b3 := by
    have hsp := spineRHS_apply (r := ``Quot.lift) (c := ``Quot.mk) (m := 5) (n := 3)
      (head := Pattern.RHS.var (Sum.inl (some none))) (k := 0) (i := 2)
      (m1 := m1) (m2 := m2) hasr0 hbsr0
    refine hsp.trans ?_
    show VExpr.mkApp (m2 (Sum.inl (some none))) [b3] = VExpr.app a4 b3
    rw [show m2 (Sum.inl (some none)) = a4 from ha4]
    rfl
  rw [← hgoal]
  exact h

/-! ## `Quot.ind`: proof irrelevance, not a rule

`addQuot` registers exactly one `VDefEq`, `quotDefEq`, and its left-hand side is a `Quot.lift`
spine.  So `Quot.ind α r β f (Quot.mk α' r' a) ≡ f a` is **not** a rule firing in this theory
and cannot be obtained from `patWF_quot`.  It is `IsDefEq.proofIrrel`: `β` lands in `Prop`, so
both sides are proofs, and the reconciliation of the two spines is what makes them proofs of
the *same* proposition. -/

def quotIndDoms : List VExpr := (VExpr.peelPis quotIndConst.type).1

theorem quotInd_type_eq :
    quotIndConst.type = VExpr.mkPi quotIndDoms ((VExpr.bvar 2).app (VExpr.bvar 0)) := rfl

/-- The major premise slot, split off. -/
theorem quotIndDoms_eq : quotIndDoms = quotIndDoms.take 4 ++
    [((VExpr.const `Quot [VLevel.param 0]).app (VExpr.bvar 3)).app (VExpr.bvar 2)] := rfl

/-- The minor premise `f : ∀ a, β (Quot.mk α r a)`, split off. -/
theorem quotIndDoms_take4 : quotIndDoms.take 4 = quotIndDoms.take 3 ++
    [(VExpr.bvar 2).forallE ((VExpr.bvar 1).app
      ((((VExpr.const `Quot.mk [VLevel.param 0]).app (VExpr.bvar 3)).app
        (VExpr.bvar 2)).app (VExpr.bvar 0)))] := rfl

/-- The motive `β : Quot α r → Prop`, split off. -/
theorem quotIndDoms_take3 : quotIndDoms.take 3 = quotIndDoms.take 2 ++
    [(((VExpr.const `Quot [VLevel.param 0]).app (VExpr.bvar 1)).app
      (VExpr.bvar 0)).forallE (VExpr.sort VLevel.zero)] := rfl

/-- **The `Quot.ind` step, justified by proof irrelevance.** -/
theorem quotInd_reduce (henv : env.WF) (hpi : env.PiInv U)
    (hind : env.constants ``Quot.ind = some quotIndConst)
    (hmkc : env.constants ``Quot.mk = some quotMkConst)
    (hquot : env.RuleFreeHead ``Quot)
    (hΓ : OnCtx Γ (env.IsType U))
    {ls ls' : List VLevel} {a1 a2 a3 a4 b1 b2 b3 A : VExpr}
    (hT : env.HasType U Γ ((VExpr.const ``Quot.ind ls).mkApp
      ([a1,a2,a3,a4] ++ [(VExpr.const ``Quot.mk ls').mkApp [b1,b2,b3]])) A) :
    env.IsDefEqU U Γ ((VExpr.const ``Quot.ind ls).mkApp
      ([a1,a2,a3,a4] ++ [(VExpr.const ``Quot.mk ls').mkApp [b1,b2,b3]])) (.app a4 b3) := by
  -- the recursor's level list and telescope
  obtain ⟨T0, hT0⟩ := HasType.mkApp_head henv.ordered hΓ _ _ _ hT
  obtain ⟨ci, hci, hlsWF, hlslen⟩ := HasType.const_inv henv.ordered hΓ hT0
  rw [hind] at hci; cases hci
  have hfun : env.HasType U Γ (.const ``Quot.ind ls)
      (VExpr.mkPi (quotIndDoms.map (VExpr.instL ls))
        (((VExpr.bvar 2).app (VExpr.bvar 0)).instL ls)) := by
    have h := HasType.const (env := env) (U := U) (Γ := Γ) hind hlsWF hlslen
    rwa [quotInd_type_eq, VExpr.instL_mkPi] at h
  have hargsInd : env.HasArgs U Γ (quotIndDoms.map (VExpr.instL ls))
      ([a1,a2,a3,a4] ++ [(VExpr.const ``Quot.mk ls').mkApp [b1,b2,b3]]) :=
    HasArgs.of_mkApp' henv hpi hΓ _ rfl hfun hT
  -- the whole spine's type, `β q`
  have hlhs := HasType.mkApp' hargsInd hfun
  rw [show (((VExpr.bvar 2).app (VExpr.bvar 0)).instL ls)
      = (VExpr.bvar 2).app (VExpr.bvar 0) from rfl, VExpr.instAll_app,
    instAll_bvar_get0 (t := 2) rfl rfl, instAll_bvar_get0 (t := 4) rfl rfl] at hlhs
  -- peel the major premise, the minor premise and the motive off the telescope
  have hargs4 := hargsInd
  rw [quotIndDoms_eq, List.map_append, List.map_cons, List.map_nil] at hargs4
  obtain ⟨hAs4, hmaj⟩ :=
    HasArgs.concat_inv (env := env) (U := U) (Γ := Γ)
      (As := (quotIndDoms.take 4).map (VExpr.instL ls))
      (A := (((VExpr.const `Quot [VLevel.param 0]).app (VExpr.bvar 3)).app
        (VExpr.bvar 2)).instL ls)
      (as := [a1,a2,a3,a4]) (a := (VExpr.const ``Quot.mk ls').mkApp [b1,b2,b3])
      rfl hargs4
  rw [show ((((VExpr.const `Quot [VLevel.param 0]).app (VExpr.bvar 3)).app
        (VExpr.bvar 2)).instL ls)
      = (((VExpr.const `Quot [ls.getD 0 .zero]).app (VExpr.bvar 3)).app (VExpr.bvar 2)) from rfl,
    VExpr.instAll_app, VExpr.instAll_app, VExpr.instAll_const,
    instAll_bvar_get0 (t := 0) rfl rfl, instAll_bvar_get0 (t := 1) rfl rfl] at hmaj
  rw [quotIndDoms_take4, List.map_append, List.map_cons, List.map_nil] at hAs4
  obtain ⟨hAs3, hmin⟩ :=
    HasArgs.concat_inv (env := env) (U := U) (Γ := Γ)
      (As := (quotIndDoms.take 3).map (VExpr.instL ls))
      (A := ((VExpr.bvar 2).forallE ((VExpr.bvar 1).app
        ((((VExpr.const `Quot.mk [VLevel.param 0]).app (VExpr.bvar 3)).app
          (VExpr.bvar 2)).app (VExpr.bvar 0)))).instL ls)
      (as := [a1,a2,a3]) (a := a4) rfl hAs4
  rw [quotIndDoms_take3, List.map_append, List.map_cons, List.map_nil] at hAs3
  obtain ⟨-, hmot⟩ :=
    HasArgs.concat_inv (env := env) (U := U) (Γ := Γ)
      (As := (quotIndDoms.take 2).map (VExpr.instL ls))
      (A := ((((VExpr.const `Quot [VLevel.param 0]).app (VExpr.bvar 1)).app
        (VExpr.bvar 0)).forallE (VExpr.sort VLevel.zero)).instL ls)
      (as := [a1,a2]) (a := a3) rfl hAs3
  rw [show (((((VExpr.const `Quot [VLevel.param 0]).app (VExpr.bvar 1)).app
        (VExpr.bvar 0)).forallE (VExpr.sort VLevel.zero)).instL ls)
      = ((((VExpr.const `Quot [ls.getD 0 .zero]).app (VExpr.bvar 1)).app
        (VExpr.bvar 0)).forallE (VExpr.sort VLevel.zero)) from rfl,
    VExpr.instAll_forallE, VExpr.instAll_sort, VExpr.instAll_app, VExpr.instAll_app,
    VExpr.instAll_const, instAll_bvar_get0 (t := 0) rfl rfl,
    instAll_bvar_get0 (t := 1) rfl rfl] at hmot
  -- the minor premise's domain is `α`; its codomain, instantiated at `a`, is `β (Quot.mk α r a)`
  rw [show (((VExpr.bvar 2).forallE ((VExpr.bvar 1).app
        ((((VExpr.const `Quot.mk [VLevel.param 0]).app (VExpr.bvar 3)).app
          (VExpr.bvar 2)).app (VExpr.bvar 0)))).instL ls)
      = ((VExpr.bvar 2).forallE ((VExpr.bvar 1).app
        ((((VExpr.const `Quot.mk [ls.getD 0 .zero]).app (VExpr.bvar 3)).app
          (VExpr.bvar 2)).app (VExpr.bvar 0)))) from rfl,
    VExpr.instAll_forallE, instAll_bvar_get0 (t := 0) rfl rfl] at hmin
  -- the constructor's own spine
  obtain ⟨T1, hT1⟩ := HasType.mkApp_head henv.ordered hΓ _ _ _ hmaj
  obtain ⟨ci', hci', hls'WF, hls'len⟩ := HasType.const_inv henv.ordered hΓ hT1
  rw [hmkc] at hci'; cases hci'
  have hmkfun : env.HasType U Γ (.const ``Quot.mk ls')
      (VExpr.mkPi (quotMkDoms.map (VExpr.instL ls'))
        ((((VExpr.const `Quot [VLevel.param 0]).app (VExpr.bvar 2)).app
          (VExpr.bvar 1)).instL ls')) := by
    have h := HasType.const (env := env) (U := U) (Γ := Γ) hmkc hls'WF hls'len
    rwa [quotMk_type_eq, VExpr.instL_mkPi] at h
  have hargsMk0 : env.HasArgs U Γ (quotMkDoms.map (VExpr.instL ls')) [b1,b2,b3] :=
    HasArgs.of_mkApp' henv hpi hΓ _ rfl hmkfun hmaj
  have hmkType := HasType.mkApp' hargsMk0 hmkfun
  rw [show ((((VExpr.const `Quot [VLevel.param 0]).app (VExpr.bvar 2)).app
        (VExpr.bvar 1)).instL ls')
      = (((VExpr.const `Quot [ls'.getD 0 .zero]).app (VExpr.bvar 2)).app (VExpr.bvar 1)) from rfl,
    VExpr.instAll_app, VExpr.instAll_app, VExpr.instAll_const,
    instAll_bvar_get0 (t := 0) rfl rfl, instAll_bvar_get0 (t := 1) rfl rfl] at hmkType
  -- the reconciliation, from uniqueness of typing plus fact (B) at `Quot`
  obtain ⟨hlv, hargs⟩ := IsDefEqU.const_app_inv henv hΓ (c := ``Quot)
    (ls := [ls.getD 0 .zero]) (ls' := [ls'.getD 0 .zero]) (as := [a1,a2]) (as' := [b1,b2])
    hquot (hmaj.isType henv.ordered hΓ) (hmaj.uniqU henv hΓ hmkType)
  let .cons hc1 (.cons hc2 .nil) := hargs
  let .cons hclv .nil := hlv
  -- the constructor spine's congruence
  have hargsMk := hargsMk0
  rw [quotMkDoms_eq, List.map_append, List.map_cons, List.map_nil] at hargsMk
  obtain ⟨-, hb3t⟩ :=
    HasArgs.concat_inv (env := env) (U := U) (Γ := Γ)
      (As := (quotMkDoms.take 2).map (VExpr.instL ls'))
      (A := (VExpr.bvar 1).instL ls') (as := [b1,b2]) (a := b3) rfl hargsMk
  rw [show ((VExpr.bvar 1).instL ls') = .bvar 1 from rfl,
    instAll_bvar_get0 (t := 0) rfl rfl] at hb3t
  have hu0WF : ∀ l ∈ [ls.getD 0 VLevel.zero], l.WF U := by
    have hmem : ls.getD 0 VLevel.zero ∈ ls := by
      match ls, hlslen with | _ :: _, _ => exact .head _
    intro l hl; cases hl with
    | head => exact hlsWF _ hmem
    | tail _ h => cases h
  have hforall2 : List.Forall₂ (· ≈ ·) ls' [ls.getD 0 VLevel.zero] := by
    match ls', hls'len, hclv with
    | [_], _, hclv => exact .cons hclv.symm .nil
  have hconstDF : env.IsDefEq U Γ (.const ``Quot.mk ls')
      (.const ``Quot.mk [ls.getD 0 VLevel.zero]) (quotMkConst.type.instL ls') :=
    .constDF hmkc hls'WF hu0WF hls'len hforall2
  rw [quotMk_type_eq, VExpr.instL_mkPi] at hconstDF
  have hDF : env.HasArgsDF U Γ (quotMkDoms.map (VExpr.instL ls')) [b1,b2,b3] [a1,a2,b3] := by
    let .cons k1 (.cons k2 (.cons k3 .nil)) := hargsMk0
    exact .cons (IsDefEqU.of_l henv hΓ (IsDefEqU.symm hc1) k1)
      (.cons (IsDefEqU.of_l henv hΓ (IsDefEqU.symm hc2) k2) (.cons k3 .nil))
  have hmkDF : env.IsDefEq U Γ ((VExpr.const ``Quot.mk ls').mkApp [b1,b2,b3])
      ((VExpr.const ``Quot.mk [ls.getD 0 VLevel.zero]).mkApp [a1,a2,b3])
      (((VExpr.const `Quot [ls.getD 0 VLevel.zero]).app a1).app a2) :=
    IsDefEqU.of_l henv hΓ ⟨_, IsDefEq.mkAppDF hDF hconstDF⟩ hmaj
  -- both sides are proofs of `β q`
  have hprop : env.HasType U Γ
      (a3.app ((VExpr.const ``Quot.mk ls').mkApp [b1,b2,b3])) (.sort .zero) :=
    HasType.app hmot hmaj
  have hb3a1 : env.HasType U Γ b3 a1 :=
    HasType.defeqU_r henv hΓ (IsDefEqU.symm hc1) hb3t
  have hrhs := HasType.app hmin hb3a1
  rw [show VExpr.inst (VExpr.instAll ((VExpr.bvar 1).app
        ((((VExpr.const `Quot.mk [ls.getD 0 VLevel.zero]).app (VExpr.bvar 3)).app
          (VExpr.bvar 2)).app (VExpr.bvar 0))) [a1,a2,a3] (0+1)) b3
      = VExpr.instAll ((VExpr.bvar 1).app
        ((((VExpr.const `Quot.mk [ls.getD 0 VLevel.zero]).app (VExpr.bvar 3)).app
          (VExpr.bvar 2)).app (VExpr.bvar 0))) ([a1,a2,a3] ++ [b3]) 0 from by
      rw [VExpr.instAll_append]; rfl] at hrhs
  simp only [VExpr.instAll_app, VExpr.instAll_const] at hrhs
  rw [
    instAll_bvar_get0 (t := 2) rfl rfl, instAll_bvar_get0 (t := 0) rfl rfl,
    instAll_bvar_get0 (t := 1) rfl rfl, instAll_bvar_get0 (t := 3) rfl rfl] at hrhs
  have htyDF : env.IsDefEq U Γ
      (a3.app ((VExpr.const ``Quot.mk [ls.getD 0 VLevel.zero]).mkApp [a1,a2,b3]))
      (a3.app ((VExpr.const ``Quot.mk ls').mkApp [b1,b2,b3])) (.sort .zero) :=
    IsDefEq.appDF hmot hmkDF.symm
  exact ⟨_, IsDefEq.proofIrrel hprop hlhs
    (HasType.defeqU_r henv hΓ ⟨_, htyDF⟩ hrhs)⟩

end VEnv

end Lean4Lean
