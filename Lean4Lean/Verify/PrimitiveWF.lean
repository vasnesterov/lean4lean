import Lean4Lean.Verify.Primitive
import Lean4Lean.Verify.Inductive.Add

/-!
# The two well-founded primitive branches: `Nat.gcd` and `Nat.bitwise`

`Lean4Lean/Verify/Primitive.lean` carries the fifteen structural branches and the two fuel
branches (`Nat.mod`, `Nat.div`).  This module carries what the two remaining branches need.

They differ from `Nat.mod` / `Nat.div` in exactly one way that matters: their fuel recursion is
`WellFounded.Nat.fix.go α motive h F`, an *application*, where `Nat.modCore.go` is a constant.
Everything downstream follows from that:

* the fuel recursion's type is not a fixed `VExpr` but `VExpr.goTypeWF A MOT MEAS`, built over
  the carrier, motive and measure the unfolder recovered -- and it has to be *checked*, because
  the recursive call's fuel bound has no type otherwise (`VExpr.WF.app_inv` invents an
  existential domain);
* `α`, `motive`, `h`, `F` and the packing function have to be independent of the variables the
  recursion steps on, or the induction cannot even be stated: the recursive call is at
  *different* arguments, so `GO` and `PACK` must be the same closed terms at every level;
* the argument is packed, so the recursion is on `PACK (natLit x) (natLit y)` rather than on two
  separate numerals.

See `docs/handoff-primitive.md`.
-/

namespace Lean4Lean
open Lean4Lean VEnv

/-- A three-fold application: the shape `WellFounded.Nat.fix.go α motive h F fuel x hlt` has
once the first four arguments are absorbed into the head. -/
def VExpr.app3 (F a b c : VExpr) : VExpr := ((F.app a).app b).app c

/-- `WellFounded.Nat.fix.go α motive h F`'s type: `∀ (fuel : Nat) (x : α), h x < fuel →
motive x`, with `h x < fuel` spelled `Nat.succ (h x) ≤ fuel` so that it is stated with
`VExpr.natLE`, the relation the `Nat.mod` / `Nat.div` fuel telescope already uses.

`A`, `MOT` and `MEAS` are closed (the recognizer checks that the terms they come from have no
free variables, and type-checks them at the base context), which is what makes the two `inst`
steps of `VEnv.goAppWF_typed` collapse. -/
def VExpr.goTypeWF (A MEAS D : VExpr) : VExpr :=
  .forallE .nat (.forallE A
    (.forallE (.natLEApp (.app .natSucc (.app MEAS (.bvar 0))) (.bvar 1)) D))

namespace VEnv
variable {env : VEnv}

/-- **The three arguments of a `go` application, at the head's declared domains.**  This is the
`Nat.gcd` / `Nat.bitwise` analogue of `VEnv.goApp_typed`, and it is what supplies the fuel
induction's step hypothesis: the recursive call's fuel bound is typed by reading it off the
well-typedness of the call, using `go`'s *checked* type. -/
theorem goAppWF_typed (henv : env.WF) {GO A MEAS D u v w : VExpr}
    (hA : A.ClosedN 0) (hMEAS : MEAS.ClosedN 0)
    (hGO : env.HasType 0 [] GO (.goTypeWF A MEAS D))
    (hwt : VExpr.WF env 0 [] (VExpr.app3 GO u v w)) :
    env.HasType 0 [] u .nat ∧ env.HasType 0 [] v A ∧
      env.HasType 0 [] w (.natLEApp (.app .natSucc (.app MEAS v)) u) := by
  have hAi : ∀ {e : VExpr} {j}, A.inst e j = A := fun {_ _} => hA.instN_eq (Nat.zero_le _)
  have hMi : ∀ {e : VExpr} {j}, MEAS.inst e j = MEAS := fun {_ _} => hMEAS.instN_eq (Nat.zero_le _)
  have h1 : VExpr.WF env 0 [] (.app GO u) := (hwt.app_fn' henv).app_fn' henv
  have hu := VExpr.WF.app_arg_typed henv hGO h1
  have huc : u.ClosedN 0 := VExpr.WF.closedN henv.ordered ⟨_, hu⟩ trivial
  have hGOu : env.HasType 0 [] (.app GO u)
      (.forallE A (.forallE (.natLEApp (.app .natSucc (.app MEAS (.bvar 0))) u)
        (D.inst u 2))) := by
    have := hGO.app hu
    simpa [VExpr.goTypeWF, VExpr.inst, VExpr.instVar, VExpr.natLEApp, VExpr.natLE,
      hAi, hMi, huc.liftN_eq (Nat.zero_le _)] using this
  have h2 : VExpr.WF env 0 [] (.app (.app GO u) v) := hwt.app_fn' henv
  have hv := VExpr.WF.app_arg_typed henv hGOu h2
  have hGOuv : env.HasType 0 [] (.app (.app GO u) v)
      (.forallE (.natLEApp (.app .natSucc (.app MEAS v)) u) ((D.inst u 2).inst v 1)) := by
    have := hGOu.app hv
    have hvc : v.ClosedN 0 := VExpr.WF.closedN henv.ordered ⟨_, hv⟩ trivial
    simpa [VExpr.inst, VExpr.instVar, VExpr.natLEApp, VExpr.natLE, hMi,
      huc.instN_eq (Nat.zero_le _), hvc.instN_eq (Nat.zero_le _),
      hvc.liftN_eq (Nat.zero_le _)] using this
  exact ⟨hu, hv, VExpr.WF.app_arg_typed henv hGOuv hwt⟩

/-- **`Nat.gcd`'s fuel induction.**

The shape is `VEnv.reflects_fuel_go`'s, with two differences forced by the well-founded
compilation: the recursion's argument is *packed* (`PACK (natLit x) (natLit y)`), and both
components move at the recursive call, so the induction is on the fuel with the invariant
`x < fuel` -- `x` being the measure.

`Ok` is left to the caller for the same reason as in `reflects_fuel_go`: `hgo`'s left-hand side
asserts a defeq, and `IsDefEqU` entails well-typedness, so the fuel bound `h` must be typed at
`go`'s declared domain for *these* `fuel` and `x`.

`hK` also receives `x < f + 1`, the induction's own invariant at the step.  It is not needed by
the current caller (which reads the recursive call's bound off the right-hand side's
well-formedness) but it is needed by any caller that has to *build* that bound: `y % x + 1 ≤ f`
follows from `x ≠ 0` and `x ≤ f`, and from nothing weaker.  Weakening `hK` this way strengthens
the theorem. -/
theorem reflects_fuel_gcd (henv : env.WF) (hlit : env.NatLits)
    {GO PACK : VExpr} {RHS K : Nat → Nat → Nat → VExpr → VExpr}
    {Ok : Nat → Nat → Nat → VExpr → Prop}
    (hgo : ∀ (f x y : Nat) (h : VExpr), Ok (f+1) x y h →
      env.IsDefEqU 0 []
        (VExpr.app3 GO (.natLit (f+1)) (VExpr.app2' PACK (.natLit x) (.natLit y)) h)
        (RHS f x y h))
    (hsel : ∀ (f x y : Nat) (h : VExpr), Ok (f+1) x y h →
      VExpr.WF env 0 [] (RHS f x y h) →
      env.IsDefEqU 0 [] (RHS f x y h)
        (if x = 0 then .natLit y
          else VExpr.app3 GO (.natLit f)
            (VExpr.app2' PACK (.natLit (y % x)) (.natLit x)) (K f x y h)))
    (hK : ∀ f x y h, x < f+1 → Ok (f+1) x y h → ¬ x = 0 → Ok f (y % x) x (K f x y h)) :
    ∀ (fuel x y : Nat), x < fuel → ∀ h, Ok fuel x y h →
      env.IsDefEqU 0 []
        (VExpr.app3 GO (.natLit fuel) (VExpr.app2' PACK (.natLit x) (.natLit y)) h)
        (.natLit (Nat.gcd x y)) := by
  intro fuel
  induction fuel with
  | zero => intro x y hx; exact absurd hx (by omega)
  | succ f ih =>
    intro x y hx h hok
    have e1 := hgo f x y h hok
    have e2 := hsel f x y h hok e1.wf_r
    refine IsDefEqU.trans henv trivial e1 (IsDefEqU.trans henv trivial e2 ?_)
    by_cases hx0 : x = 0
    · subst hx0
      rw [if_pos rfl, Nat.gcd_zero_left]
      exact IsDefEqU.refl ⟨_, hlit y⟩
    · rw [if_neg hx0, Nat.gcd_rec]
      exact ih (y % x) x (by
        have : y % x < x := Nat.mod_lt _ (Nat.pos_of_ne_zero hx0)
        omega) _ (hK f x y h hx hok hx0)

end VEnv

/-! ## `M`-level specifications for the two reduction steps the unfolder searches with

`Verify/TypeChecker.lean` exports `whnf`, `inferType`, `checkType`, `isDefEq`, `isProp`,
`ensureSort` and `ensureForall` at the `M` level; `whnfCore` and `unfoldDefinition` were only
available at the `RecM` level, and the recognizer calls both. -/

namespace TypeChecker
open Lean hiding Environment Exception
open Kernel

nonrec theorem whnfCore.WF {c : VContext} {s : VState} {e : Expr} {e' : VExpr}
    (he : c.TrExprS e e') : M.WF c s (whnfCore e) fun e₁ _ => c.TrExpr e₁ e' :=
  (Inner.whnfCore.WF he).run.mono fun _ _ _ h => h.2

/-- `TypeChecker.unfoldDefinition` returns its input unchanged when nothing unfolds, so the
`none` half of `UnfoldDefinition.WF` is discharged by the input's own translation. -/
nonrec theorem unfoldDefinition.WF {c : VContext} {s : VState} {e : Expr} {e' : VExpr}
    (he : c.TrExprS e e') : M.WF c s (unfoldDefinition e) fun e₁ _ => c.TrExpr e₁ e' := by
  unfold TypeChecker.unfoldDefinition
  refine M.WF.bind (Inner.unfoldDefinition.WF he).run fun oe _ _ h => ?_
  cases oe with
  | none => exact .pure (he.trExpr c.Ewf c.Δwf)
  | some e₁ => exact .pure h.2

end TypeChecker

/-! ## The two syntactic side conditions the unfolder checks

`TrExprS.IsUnique` and `looseBVarRange' = 0` are what make a term's translation determined by
its context and stable under a `.forallE` binder.  For the recognizer's fixed terms they are
discharged by `simp`; the terms `unfoldNatWellFounded` recovers are arbitrary, so it checks
them, and these two lemmas read the checks back. -/

theorem TrExprS.isUnique_of_anySub : ∀ {e : Lean.Expr},
    anySub Lean4Lean.Environment.isProjNode e = false → TrExprS.IsUnique e := by
  intro e
  induction e with
  | bvar | fvar | sort | const | mvar | lit => intro _; trivial
  | app f a ih1 ih2 =>
    intro h; rw [anySub_eq] at h; simp only [Bool.or_eq_false_iff] at h
    exact ⟨ih1 h.2.1, ih2 h.2.2⟩
  | lam _ d b _ ih1 ih2 =>
    intro h; rw [anySub_eq] at h; simp only [Bool.or_eq_false_iff] at h
    exact ⟨ih1 h.2.1, ih2 h.2.2⟩
  | forallE _ d b _ ih1 ih2 =>
    intro h; rw [anySub_eq] at h; simp only [Bool.or_eq_false_iff] at h
    exact ⟨ih1 h.2.1, ih2 h.2.2⟩
  | letE _ d v b _ _ ih2 ih3 =>
    intro h; rw [anySub_eq] at h; simp only [Bool.or_eq_false_iff] at h
    exact ⟨ih2 h.2.1.2, ih3 h.2.2⟩
  | mdata _ e ih =>
    intro h; rw [anySub_eq] at h; simp only [Bool.or_eq_false_iff] at h
    exact ih h.2
  | proj => intro h; rw [anySub_eq] at h; simp [Lean4Lean.Environment.isProjNode] at h

theorem TrExprS.isUnique_of_noProj {e : Lean.Expr}
    (h : Lean4Lean.Environment.noProj e = true) : TrExprS.IsUnique e := by
  refine TrExprS.isUnique_of_anySub ?_
  rw [← anySubterm_eq]
  simpa [Lean4Lean.Environment.noProj] using h

/-! ### No loose bound variables, read off the translation

`trExprS_weakBV0` -- the step that carries a closed term's translation under a `.forallE`'s
binder -- needs `looseBVarRange' = 0`.  That is *not* checked by the recognizer: it follows from
the term having a translation at the **base** context at all, because `TrExprS.bvar` reads
`VLCtx.find?`, which returns `none` on the empty context. -/

theorem VLCtx.find?_inl_lt : ∀ {Δ : VLCtx} {i : Nat} {x},
    VLCtx.find? Δ (Sum.inl i) = some x → i < Δ.length
  | [], _, _, h => by simp [VLCtx.find?] at h
  | (none, _) :: _, 0, _, _ => by simp
  | (none, _) :: Δ, i+1, _, h => by
    simp only [VLCtx.find?, VLCtx.next] at h
    cases hf : VLCtx.find? Δ (Sum.inl i) with
    | none => rw [hf] at h; simp at h
    | some y => have := VLCtx.find?_inl_lt hf; simp; omega
  | (some _, _) :: Δ, i, _, h => by
    simp only [VLCtx.find?, VLCtx.next] at h
    cases hf : VLCtx.find? Δ (Sum.inl i) with
    | none => rw [hf] at h; simp at h
    | some y => have := VLCtx.find?_inl_lt hf; simp; omega

theorem TrExprS.looseBVarRange_le {env : VEnv} {Us} {Δ : VLCtx} {e : Lean.Expr} {e' : VExpr}
    (h : TrExprS env Us Δ e e') : e.looseBVarRange' ≤ Δ.length := by
  induction h with
  | bvar h => exact VLCtx.find?_inl_lt h
  | fvar | sort | const => exact Nat.zero_le _
  | app _ _ _ _ ih1 ih2 => simp only [Lean.Expr.looseBVarRange']; omega
  | lam _ _ _ ih1 ih2 =>
    simp only [Lean.Expr.looseBVarRange']; simp only [List.length_cons] at ih2; omega
  | forallE _ _ _ _ ih1 ih2 =>
    simp only [Lean.Expr.looseBVarRange']; simp only [List.length_cons] at ih2; omega
  | letE _ _ _ _ _ ih1 ih2 =>
    simp only [Lean.Expr.looseBVarRange']; simp only [List.length_cons] at ih2; omega
  | lit => exact Nat.zero_le _
  | mdata _ ih => simpa [Lean.Expr.looseBVarRange'] using ih
  | proj _ _ ih => simpa [Lean.Expr.looseBVarRange'] using ih

/-- The base-context reading. -/
theorem trExprS_looseBVarRange_nil {env : VEnv} {Us} {e : Lean.Expr} {e' : VExpr}
    (h : TrExprS env Us [] e e') : e.looseBVarRange' = 0 :=
  Nat.le_zero.1 (by simpa using h.looseBVarRange_le)

/-- Everything the caller of `unfoldNatWellFounded` needs about the shape of what it returns:
the pieces have translations at the base context (`FVarsIn`), those translations are determined
(`IsUnique`), and the carrier and measure survive a `.forallE` binder unchanged
(`looseBVarRange' = 0`). -/
structure Environment.NatWFUnfold.Good (u : Environment.NatWFUnfold) : Prop where
  goFV : u.go.FVarsIn fun _ => False
  packFV : u.pack.FVarsIn fun _ => False
  measFV : u.measure.FVarsIn fun _ => False
  alphaFV : u.alpha.FVarsIn fun _ => False
  motiveFV : u.motive.FVarsIn fun _ => False
  prfAFV : u.prfA.FVarsIn fun _ => False
  goU : TrExprS.IsUnique u.go
  packU : TrExprS.IsUnique u.pack
  measU : TrExprS.IsUnique u.measure
  alphaU : TrExprS.IsUnique u.alpha

namespace TypeChecker
open Lean hiding Environment Exception
open Kernel

/-- **What the unfolder's search establishes.**

Deliberately almost nothing: `unfoldNatWellFounded` is search, and every semantic fact its
caller uses is re-established by a check the caller makes.  What the caller cannot re-establish
is that the pieces have translations at the *base* context at all -- `checkType` needs
`FVarsIn`, and the whole point of running the search under its own copy of the binders is that
`go`, `pack` and the measure come back out of them.  That is what the six
`checkNoMVarNoFVar`s buy, and it is this lemma's whole content. -/
theorem unfoldNatWellFounded.WF {c : VContext} {s : VState} {e : Expr} {fvs : Array Expr}
    {nOuter : Nat} {fail : ∀ {α}, TypeChecker.M α}
    (hfail : ∀ {β : Type} {s' : VState} {Q : β → VState → Prop}, M.WF c s' fail Q)
    (he : ∃ e', c.TrExprS (Lean.mkAppN e fvs) e') :
    M.WF c s (Lean4Lean.Environment.unfoldNatWellFounded e fvs nOuter fail) fun u _ =>
      u.Good := by
  obtain ⟨E, hE⟩ := he
  unfold Lean4Lean.Environment.unfoldNatWellFounded
  refine M.WF.bind (whnfCore.WF hE) fun _ _ _ h1 => ?_
  obtain ⟨e1', h1s, -⟩ := h1
  refine M.WF.bind (unfoldDefinition.WF h1s) fun _ _ _ h2 => ?_
  obtain ⟨e2', h2s, -⟩ := h2
  refine M.WF.bind (whnfCore.WF h2s) fun _ _ _ h3 => ?_
  obtain ⟨e3', h3s, -⟩ := h3
  split
  case h_2 => exact hfail
  refine M.WF.bind getLCtx.WF fun _ _ _ _ => ?_
  refine M.WF.bind (unfoldDefinition.WF h3s) fun _ _ _ h4 => ?_
  obtain ⟨e4', h4s, -⟩ := h4
  refine M.WF.bind (whnfCore.WF h4s) fun _ _ _ h5 => ?_
  obtain ⟨e5', h5s, -⟩ := h5
  split
  case h_2 => exact hfail
  split
  case isFalse => exact M.WF.bindThrow hfail
  simp only []
  split
  case isFalse => exact M.WF.bindThrow hfail
  rename_i hchk
  simp only [Bool.and_eq_true] at hchk
  obtain ⟨⟨⟨hgoU, hpkU⟩, hmsU⟩, halU⟩ := hchk
  refine M.WF.bind getEnv.WF fun _ _ _ h => ?_
  obtain ⟨rfl, rfl⟩ := h
  refine M.WF.bind (M.WF.liftExcept (checkNoMVarNoFVar.WF' _ _ _)) fun _ _ _ hgo => ?_
  refine M.WF.bind (M.WF.liftExcept (checkNoMVarNoFVar.WF' _ _ _)) fun _ _ _ hpk => ?_
  refine M.WF.bind (M.WF.liftExcept (checkNoMVarNoFVar.WF' _ _ _)) fun _ _ _ hms => ?_
  refine M.WF.bind (M.WF.liftExcept (checkNoMVarNoFVar.WF' _ _ _)) fun _ _ _ hal => ?_
  refine M.WF.bind (M.WF.liftExcept (checkNoMVarNoFVar.WF' _ _ _)) fun _ _ _ hmo => ?_
  refine M.WF.bind (M.WF.liftExcept (checkNoMVarNoFVar.WF' _ _ _)) fun _ _ _ hpr => ?_
  exact .pure ⟨hgo, hpk, hms, hal, hmo, hpr,
    TrExprS.isUnique_of_noProj hgoU, TrExprS.isUnique_of_noProj hpkU,
    TrExprS.isUnique_of_noProj hmsU, TrExprS.isUnique_of_noProj halU⟩

end TypeChecker

/-! ## Inverting the type `go` is checked against -/

open Lean in
/-- **`NatWFUnfold.goType`'s translation.**  The carrier and the measure are identified with
their base-context translations by `trExprS_weakBV0` (they are closed and have no loose bound
variables -- both checked by the unfolder) plus `TrExprS.unique` (they are `IsUnique`, also
checked); the two bound variables are pinned outright.  The body is left opaque: nothing
downstream reads it, which is why `VExpr.goTypeWF` takes it as a parameter. -/
theorem trExprS_goTypeWF_inv' {env : VEnv} {Us} {Δ : VLCtx} {α meas mot : Lean.Expr}
    {A MEAS : VExpr} {n₁ n₂ n₃ bi₁ bi₂ bi₃} {e' : VExpr} (henv : env.Ordered)
    (hA : TrExprS env Us Δ α A) (hAu : TrExprS.IsUnique α)
    (hAb : α.looseBVarRange' = 0) (hAc : A.ClosedN 0)
    (hM : TrExprS env Us Δ meas MEAS) (hMu : TrExprS.IsUnique meas)
    (hMb : meas.looseBVarRange' = 0) (hMc : MEAS.ClosedN 0)
    (h : TrExprS env Us Δ
      (.forallE n₁ (.const ``Nat [])
        (.forallE n₂ α
          (.forallE n₃
            (.app (.app (.app (.app (.const ``LE.le [.zero]) (.const ``Nat []))
              (.const ``instLENat [])) (.app (.const ``Nat.succ []) (.app meas (.bvar 0))))
              (.bvar 1))
            (.app mot (.bvar 1)) bi₃) bi₂) bi₁) e') :
    ∃ D, e' = .goTypeWF A MEAS D := by
  obtain ⟨_, _, rfl, h1, h2⟩ := trExprS_arrow_inv' h
  cases trExprS_const_nil_inv' h1
  obtain ⟨_, _, rfl, g1, g2⟩ := trExprS_arrow_inv' h2
  cases TrExprS.unique hAu g1 (trExprS_weakBV0 henv hA hAb hAc)
  obtain ⟨_, _, rfl, k1, _⟩ := trExprS_arrow_inv' g2
  obtain ⟨_, _, rfl, m1, m2⟩ := trExprS_natLEApp_inv' k1
  cases trExprS_bvar1_inv' m2
  let .app _ _ p1 p2 := m1
  cases trExprS_const_nil_inv' p1
  let .app _ _ q1 q2 := p2
  cases TrExprS.unique hMu q1
    (trExprS_weakBV0 henv (trExprS_weakBV0 henv hM hMb hMc) hMb hMc)
  cases trExprS_bvar0_inv' q2
  exact ⟨_, rfl⟩

/-! ## `Condition.natEq`, pinned

`Condition.check.WF_natEq` leaves the proposition and the decision instance existential; the
`Nat.gcd` and `Nat.bitwise` branches build their conditionals with `Condition.dite`, i.e. with
`cond.prop` and `cond.dec` in exactly those two slots, so the fuel induction needs them pinned
to the abstract terms it is stated over.  Same collapse test as
`TypeChecker.Condition.check.WF_natLE_pinned`. -/

/-- `@Eq Nat` in the abstract syntax. -/
def VExpr.natEq : VExpr := .app (.const ``Eq [.succ .zero]) .nat

/-- `a = b` at `Nat`. -/
def VExpr.natEqApp (a b : VExpr) : VExpr := .app (.app .natEq a) b

theorem trExprS_natEq_inv' {env : VEnv} {Us Δ} {e' : VExpr}
    (h : TrExprS env Us Δ (.app (.const ``Eq [.succ .zero]) (.const ``Nat [])) e') :
    e' = .natEq := by
  let .app _ _ g3 g4 := h
  cases trExprS_const_nil_inv' g4
  let .const _ h2 _ := g3
  simp [VLevel.ofLevel] at h2
  rw [← h2]; rfl

/-- `a = b` at `Nat`, applied. -/
theorem trExprS_natEqApp_inv' {env : VEnv} {Us Δ} {a b : Lean.Expr} {e' : VExpr}
    (h : TrExprS env Us Δ
      (.app (.app (.app (.const ``Eq [.succ .zero]) (.const ``Nat [])) a) b) e') :
    ∃ a' b', e' = .natEqApp a' b' ∧
      TrExprS env Us Δ a a' ∧ TrExprS env Us Δ b b' := by
  let .app _ _ g3 g4 := h
  let .app _ _ f3 f4 := g3
  cases trExprS_natEq_inv' f3
  exact ⟨_, _, rfl, f4, g4⟩

namespace VEnv
variable {env : VEnv}

/-- The reading the `Nat.gcd` / `Nat.bitwise` recursions want of a `Condition.natEq` `dite`:
`a = b` decides the branch. -/
theorem ReflectsCondAppD.natEq_eq {F P D OT OF PR : VExpr}
    (h : env.ReflectsCondAppD F P D OT OF PR Nat.beq) (a b : Nat) (t e : VExpr)
    (hwt : VExpr.WF env 0 [] (VExpr.condApp F (.app (.app P (.natLit a)) (.natLit b))
      (.app (.app D (.natLit a)) (.natLit b)) t e)) :
    env.IsDefEqU 0 []
      (VExpr.condApp F (.app (.app P (.natLit a)) (.natLit b))
        (.app (.app D (.natLit a)) (.natLit b)) t e)
      (if a = b then
          .app t (.app (.app OT (.app (.app P (.natLit a)) (.natLit b)))
            (.app (.app PR (.natLit a)) (.natLit b)))
        else .app e (.app (.app OF (.app (.app P (.natLit a)) (.natLit b)))
            (.app (.app PR (.natLit a)) (.natLit b)))) := by
  have := h a b t e hwt
  by_cases hab : a = b
  · rw [if_pos hab]
    rwa [show Nat.beq a b = true by subst hab; exact Nat.beq_refl a] at this
  · rw [if_neg hab]
    rwa [show Nat.beq a b = false by
      cases hc : Nat.beq a b
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true hc) hab] at this

end VEnv

namespace TypeChecker
open Lean hiding Environment Exception
open Kernel Lean4Lean.Environment
variable {c : VContext}

theorem primitives_natBEq : Environment.primitives.contains ``Nat.beq = true := by
  simpa using primitives_contains_iff.2 (by simp)

theorem primitives_natMod : Environment.primitives.contains ``Nat.mod = true := by
  simpa using primitives_contains_iff.2 (by simp)

theorem Condition.check.WF_natEq_pinned {s : VState} {fail : ∀ {α}, TypeChecker.M α}
    {iteTypes : List Lean.Expr} {dite : Bool}
    (hfail : ∀ {c' : VContext} {β : Type} {s' : VState} {Q : β → VState → Prop},
      M.WF c' s' fail Q)
    (hnil : c.vlctx = []) (hlp : c.lparams = []) (hsafe : c.safety = .safe)
    (hnat : c.venv.contains ``Nat) (hnatty : c.venv.IsType 0 [] .nat)
    (hbeqE : c.env.contains ``Nat.beq = true)
    (hitefv : ∀ α ∈ iteTypes, α.FVarsIn (· ∈ c.vlctx.fvars) ∧ TrExprS.IsUnique α ∧
      α.looseBVarRange' = 0) :
    M.WF c s (Lean4Lean.Environment.Condition.natEq.check fail iteTypes dite) fun _ _ =>
      (∀ α ∈ iteTypes, ∃ Aα F, c.TrExprS α Aα ∧ Aα.ClosedN 0 ∧
        c.TrExprS (Lean.mkApp (.const ``ite [.succ .zero]) α) F ∧ F.ClosedN 0 ∧
        c.venv.ReflectsCondAppAll F .natEq (.const ``Nat.decEq []) Nat.beq) ∧
      (dite = true → ∃ FD OT OF PR,
        c.TrExprS (Lean.mkApp (.const ``dite [.succ .zero]) (.const ``Nat [])) FD ∧
        c.TrExprS Lean4Lean.Environment.Reflection.defn₂.ofTrue OT ∧
        c.TrExprS Lean4Lean.Environment.Reflection.defn₂.ofFalse OF ∧
        c.venv.ReflectsCondAppDAll FD .natEq (.const ``Nat.decEq []) OT OF PR Nat.beq) := by
  refine (Condition.check.WF_natEq hfail hnil hlp hnat hnatty
    (contains_primConst hsafe hbeqE primitives_natBEq) hitefv).mono fun _ _ _ h => ?_
  obtain ⟨P, D, hP, hD, -, -, hite, hdite⟩ := h
  cases trExprS_natEq_inv' (Us := c.lparams) (Δ := c.vlctx) hP
  cases trExprS_const_nil_inv' (Us := c.lparams) (Δ := c.vlctx) hD
  exact ⟨hite, hdite⟩

end TypeChecker

/-! ## Instantiating the two equations the `Nat.gcd` branch checks -/

/-- The context the fuel recurrence is checked in: `m`, `n`, `fuel`, and the fuel bound
`Nat.succ m ≤ Nat.succ fuel`.  Unlike `VExpr.goCtx` there is no `1 ≤ y` binder -- the measure is
the first argument itself, so the recursion needs no separate positivity witness. -/
def VExpr.gcdCtx (MEAS PACK : VExpr) : List VExpr :=
  [.natLEApp (.app .natSucc (.app MEAS (VExpr.app2' PACK (.bvar 2) (.bvar 1))))
      (.app .natSucc (.bvar 0)),
    .nat, .nat, .nat]

namespace VEnv
variable {env : VEnv}

/-- Instantiate an equation proved in `VExpr.gcdCtx`.  The proof binder is substituted by a term
the caller supplies together with its typing; nothing else about it is needed. -/
theorem IsDefEqU.instGcd (henv : env.WF) (hlit : env.NatLits) {MEAS PACK e₁ e₂ : VExpr}
    (hMEASc : MEAS.ClosedN 0) (hPACKc : PACK.ClosedN 0)
    (H : env.IsDefEqU 0 (VExpr.gcdCtx MEAS PACK) e₁ e₂) (x y f : Nat) {h : VExpr}
    (hh : env.HasType 0 [] h
      (.natLEApp (.app .natSucc (.app MEAS (VExpr.app2' PACK (.natLit x) (.natLit y))))
        (.natLit (f+1)))) :
    env.IsDefEqU 0 []
      ((((e₁.inst (.natLit x) 3).inst (.natLit y) 2).inst (.natLit f) 1).inst h)
      ((((e₂.inst (.natLit x) 3).inst (.natLit y) 2).inst (.natLit f) 1).inst h) := by
  have s1 : env.IsDefEqU 0
      [.natLEApp (.app .natSucc (.app MEAS (VExpr.app2' PACK (.natLit x) (.bvar 1))))
          (.app .natSucc (.bvar 0)), .nat, .nat]
      (e₁.inst (.natLit x) 3) (e₂.inst (.natLit x) 3) := by
    have := IsDefEqU.instN (Γ₀ := []) (A₀ := .nat) (e₀ := .natLit x) henv.ordered
      (.succ (.succ (.succ .zero))) H (hlit x)
    simpa [VExpr.gcdCtx, VExpr.app2', VExpr.inst, VExpr.instVar, VExpr.natLEApp, VExpr.natLE,
      hMEASc.liftN_eq (Nat.zero_le _), hPACKc.liftN_eq (Nat.zero_le _),
      hMEASc.instN_eq (Nat.zero_le _), hPACKc.instN_eq (Nat.zero_le _),
      (VExpr.closedN_natLit x).liftN_eq (Nat.zero_le _)] using this
  have s2 : env.IsDefEqU 0
      [.natLEApp (.app .natSucc (.app MEAS (VExpr.app2' PACK (.natLit x) (.natLit y))))
          (.app .natSucc (.bvar 0)), .nat]
      ((e₁.inst (.natLit x) 3).inst (.natLit y) 2)
      ((e₂.inst (.natLit x) 3).inst (.natLit y) 2) := by
    have := IsDefEqU.instN (Γ₀ := []) (A₀ := .nat) (e₀ := .natLit y) henv.ordered
      (.succ (.succ .zero)) s1 (hlit y)
    simpa [VExpr.app2', VExpr.inst, VExpr.instVar, VExpr.natLEApp, VExpr.natLE,
      hMEASc.liftN_eq (Nat.zero_le _), hPACKc.liftN_eq (Nat.zero_le _),
      hMEASc.instN_eq (Nat.zero_le _), hPACKc.instN_eq (Nat.zero_le _),
      (VExpr.closedN_natLit x).liftN_eq (Nat.zero_le _),
      (VExpr.closedN_natLit y).liftN_eq (Nat.zero_le _)] using this
  have s3 : env.IsDefEqU 0
      [.natLEApp (.app .natSucc (.app MEAS (VExpr.app2' PACK (.natLit x) (.natLit y))))
          (.natLit (f+1))]
      (((e₁.inst (.natLit x) 3).inst (.natLit y) 2).inst (.natLit f) 1)
      (((e₂.inst (.natLit x) 3).inst (.natLit y) 2).inst (.natLit f) 1) := by
    have := IsDefEqU.instN (Γ₀ := []) (A₀ := .nat) (e₀ := .natLit f) henv.ordered
      (.succ .zero) s2 (hlit f)
    simpa [VExpr.app2', VExpr.inst, VExpr.instVar, VExpr.natLEApp, VExpr.natLE,
      VExpr.natLit_succ, hMEASc.liftN_eq (Nat.zero_le _), hPACKc.liftN_eq (Nat.zero_le _),
      hMEASc.instN_eq (Nat.zero_le _), hPACKc.instN_eq (Nat.zero_le _),
      (VExpr.closedN_natLit x).liftN_eq (Nat.zero_le _),
      (VExpr.closedN_natLit y).liftN_eq (Nat.zero_le _),
      (VExpr.closedN_natLit f).liftN_eq (Nat.zero_le _)] using this
  exact IsDefEqU.instN (Γ₀ := []) (e₀ := h) henv.ordered .zero s3 hh

end VEnv

/-- **The context the fuel recurrence is *now* checked in.**  `VExpr.gcdCtx` plus one more
binder, the recursive call's own fuel bound `Nat.succ (h (pack (n % m) m)) ≤ fuel`.

**This context is NOT the one the implementation uses, and the reason is worth reading before
using anything here.**  `Lean4Lean/Primitive.lean`'s `Nat.gcd` branch briefly bound that proof with
`withCheckedLocalDecl` instead of constructing it, on the belief that the six lemmas the
construction used were outside `Nat.gcd`'s constant cone.  **Exactly one of them was**
(`Nat.pos_of_ne_zero`); the other five are in it, and the cone is 238 constants, not the 135 that
belief rested on (`scripts/gcd-cone-probe.lean`, ledger row 121h).  The branch now constructs the
proof again, inside the `dite`'s else-λ where `¬(m = 0)` is in scope, with
`Nat.zero_lt_of_ne_zero` — same statement, same binder kinds, present in both cones, and what
`Nat.gcd`'s own `decreasing_by` uses — in place of the one missing lemma.  Hoisting the proof out
of that λ is what created the `m = 0` gap described below, so the four-binder
`VExpr.gcdCtx` is what `reflects_gcd_of_equations` is proved over and this definition is
**currently unused by the implementation**.  It is kept because it is real machinery for any future
five-binder route.  See `docs/handoff-primitive-natle.md` §1 and §6.

The proposition this binder inhabits is **false in general** (at `m = n = fuel = 0` the
hypothesis `1 ≤ 1` holds and the conclusion `1 ≤ 0` does not), so it cannot be discharged once
and for all: `IsDefEqU.instGcdWF` takes a witness *per instance*.

**And a witness does not exist at every instance the fuel induction visits.**  At `m = 0` the
binder asks for `n + 1 ≤ fuel`, which the induction's invariant (`m < fuel`, i.e. `0 ≤ fuel`)
does not give, and `VEnv.reflects_fuel_gcd` calls `hgo` *before* splitting on `m = 0`.
`scripts/gcd-fuel-zero-gap.lean` exhibits the states: `Nat.gcd 0 5` needs `6 ≤ 0` at its entry
state, and `Nat.gcd 4 6` needs `3 ≤ 2` at `(fuel, m, n) = (3, 0, 2)`.  So this definition and
`instGcdWF` are the machinery a fix will need, but they do **not** on their own let
`reflects_gcd_of_equations` be restated over the five-binder equation.  See
`docs/handoff-primitive-natle.md` §5.2. -/
def VExpr.gcdCtxWF (MEAS PACK : VExpr) : List VExpr :=
  .natLEApp (.app .natSucc (.app MEAS (VExpr.app2' PACK
      (.natOp ``Nat.mod (.bvar 2) (.bvar 3)) (.bvar 3)))) (.bvar 1) :: VExpr.gcdCtx MEAS PACK

namespace VEnv
variable {env : VEnv}

/-- Instantiate an equation proved in `VExpr.gcdCtxWF`.  Both proof binders are substituted by
terms the caller supplies together with their typings; nothing else about them is needed.

The order is forced: the four `m`, `n`, `fuel`, `h` binders must go first, because the fifth
binder's *type* mentions the first three, and a witness for it exists only once they are
numerals. -/
theorem IsDefEqU.instGcdWF (henv : env.WF) (hlit : env.NatLits) {MEAS PACK e₁ e₂ : VExpr}
    (hMEASc : MEAS.ClosedN 0) (hPACKc : PACK.ClosedN 0)
    (H : env.IsDefEqU 0 (VExpr.gcdCtxWF MEAS PACK) e₁ e₂) (x y f : Nat) {h w : VExpr}
    (hh : env.HasType 0 [] h
      (.natLEApp (.app .natSucc (.app MEAS (VExpr.app2' PACK (.natLit x) (.natLit y))))
        (.natLit (f+1))))
    (hw : env.HasType 0 [] w
      (.natLEApp (.app .natSucc (.app MEAS (VExpr.app2' PACK
        (.natOp ``Nat.mod (.natLit y) (.natLit x)) (.natLit x)))) (.natLit f))) :
    env.IsDefEqU 0 []
      (((((e₁.inst (.natLit x) 4).inst (.natLit y) 3).inst (.natLit f) 2).inst h 1).inst w)
      (((((e₂.inst (.natLit x) 4).inst (.natLit y) 3).inst (.natLit f) 2).inst h 1).inst w) := by
  have eM : ∀ {u : VExpr} {j}, MEAS.inst u j = MEAS := fun {_ _} =>
    hMEASc.instN_eq (Nat.zero_le _)
  have eP : ∀ {u : VExpr} {j}, PACK.inst u j = PACK := fun {_ _} =>
    hPACKc.instN_eq (Nat.zero_le _)
  have lM : ∀ {j}, MEAS.liftN j = MEAS := fun {_} => hMEASc.liftN_eq (Nat.zero_le _)
  have lP : ∀ {j}, PACK.liftN j = PACK := fun {_} => hPACKc.liftN_eq (Nat.zero_le _)
  have s1 : env.IsDefEqU 0
      (.natLEApp (.app .natSucc (.app MEAS (VExpr.app2' PACK
          (.natOp ``Nat.mod (.bvar 2) (.natLit x)) (.natLit x)))) (.bvar 1) ::
        [.natLEApp (.app .natSucc (.app MEAS (VExpr.app2' PACK (.natLit x) (.bvar 1))))
          (.app .natSucc (.bvar 0)), .nat, .nat])
      (e₁.inst (.natLit x) 4) (e₂.inst (.natLit x) 4) := by
    have := IsDefEqU.instN (Γ₀ := []) (A₀ := .nat) (e₀ := .natLit x) henv.ordered
      (.succ (.succ (.succ (.succ .zero)))) H (hlit x)
    simpa [VExpr.gcdCtxWF, VExpr.gcdCtx, VExpr.app2', VExpr.natOp, VExpr.inst, VExpr.instVar,
      VExpr.natLEApp, VExpr.natLE, lM, lP, eM, eP,
      (VExpr.closedN_natLit x).liftN_eq (Nat.zero_le _)] using this
  have s2 : env.IsDefEqU 0
      (.natLEApp (.app .natSucc (.app MEAS (VExpr.app2' PACK
          (.natOp ``Nat.mod (.natLit y) (.natLit x)) (.natLit x)))) (.bvar 1) ::
        [.natLEApp (.app .natSucc (.app MEAS (VExpr.app2' PACK (.natLit x) (.natLit y))))
          (.app .natSucc (.bvar 0)), .nat])
      ((e₁.inst (.natLit x) 4).inst (.natLit y) 3)
      ((e₂.inst (.natLit x) 4).inst (.natLit y) 3) := by
    have := IsDefEqU.instN (Γ₀ := []) (A₀ := .nat) (e₀ := .natLit y) henv.ordered
      (.succ (.succ (.succ .zero))) s1 (hlit y)
    simpa [VExpr.app2', VExpr.natOp, VExpr.inst, VExpr.instVar,
      VExpr.natLEApp, VExpr.natLE, lM, lP, eM, eP,
      (VExpr.closedN_natLit x).liftN_eq (Nat.zero_le _),
      (VExpr.closedN_natLit y).liftN_eq (Nat.zero_le _)] using this
  have s3 : env.IsDefEqU 0
      (.natLEApp (.app .natSucc (.app MEAS (VExpr.app2' PACK
          (.natOp ``Nat.mod (.natLit y) (.natLit x)) (.natLit x)))) (.natLit f) ::
        [.natLEApp (.app .natSucc (.app MEAS (VExpr.app2' PACK (.natLit x) (.natLit y))))
          (.natLit (f+1))])
      (((e₁.inst (.natLit x) 4).inst (.natLit y) 3).inst (.natLit f) 2)
      (((e₂.inst (.natLit x) 4).inst (.natLit y) 3).inst (.natLit f) 2) := by
    have := IsDefEqU.instN (Γ₀ := []) (A₀ := .nat) (e₀ := .natLit f) henv.ordered
      (.succ (.succ .zero)) s2 (hlit f)
    simpa [VExpr.app2', VExpr.natOp, VExpr.inst, VExpr.instVar,
      VExpr.natLEApp, VExpr.natLE, VExpr.natLit_succ, lM, lP, eM, eP,
      (VExpr.closedN_natLit x).liftN_eq (Nat.zero_le _),
      (VExpr.closedN_natLit y).liftN_eq (Nat.zero_le _),
      (VExpr.closedN_natLit f).liftN_eq (Nat.zero_le _)] using this
  have hhc : h.ClosedN 0 := VExpr.WF.closedN henv.ordered ⟨_, hh⟩ trivial
  have s4 : env.IsDefEqU 0
      [.natLEApp (.app .natSucc (.app MEAS (VExpr.app2' PACK
          (.natOp ``Nat.mod (.natLit y) (.natLit x)) (.natLit x)))) (.natLit f)]
      ((((e₁.inst (.natLit x) 4).inst (.natLit y) 3).inst (.natLit f) 2).inst h 1)
      ((((e₂.inst (.natLit x) 4).inst (.natLit y) 3).inst (.natLit f) 2).inst h 1) := by
    have := IsDefEqU.instN (Γ₀ := []) (e₀ := h) henv.ordered (.succ .zero) s3 hh
    simpa [VExpr.app2', VExpr.natOp, VExpr.inst, VExpr.instVar,
      VExpr.natLEApp, VExpr.natLE, lM, lP, eM, eP,
      (VExpr.closedN_natLit x).liftN_eq (Nat.zero_le _),
      (VExpr.closedN_natLit y).liftN_eq (Nat.zero_le _),
      (VExpr.closedN_natLit f).liftN_eq (Nat.zero_le _)] using this
  exact IsDefEqU.instN (Γ₀ := []) (e₀ := w) henv.ordered .zero s4 hw

end VEnv

namespace VEnv
variable {env : VEnv}

/-- Replace the first argument of a three-fold application. -/
theorem IsDefEqU.app3_congr_arg1 (henv : env.WF) {F u u' v w : VExpr}
    (hwt : VExpr.WF env 0 [] (VExpr.app3 F u v w)) (h : env.IsDefEqU 0 [] u u') :
    env.IsDefEqU 0 [] (VExpr.app3 F u v w) (VExpr.app3 F u' v w) :=
  IsDefEqU.app_congr_fn' henv hwt
    (IsDefEqU.app_congr_fn' henv (hwt.app_fn' henv)
      (IsDefEqU.app_congr_arg' henv ((hwt.app_fn' henv).app_fn' henv) h))

end VEnv

namespace VEnv
variable {env : VEnv}

/-- **The `Nat.gcd` fuel recurrence at a pair of numerals**, with the four binders
instantiated.  The shape mirrors `VEnv.mod_step2`. -/
theorem gcd_step (henv : env.WF) (hlit : env.NatLits) {GO PACK DEC EA K : VExpr}
    (hgoeq : env.IsDefEqU 0 (VExpr.gcdCtx MEAS PACK)
      (VExpr.app3 GO (.app .natSucc (.bvar 1)) (VExpr.app2' PACK (.bvar 3) (.bvar 2)) (.bvar 0))
      (VExpr.condApp .diteNat (.natEqApp (.bvar 3) .natZero)
        (.app (.app DEC (.bvar 3)) .natZero)
        (.lam (.natEqApp (.bvar 3) .natZero) (.bvar 3))
        (.lam EA (VExpr.app3 GO (.bvar 2)
          (VExpr.app2' PACK (.natOp ``Nat.mod (.bvar 3) (.bvar 4)) (.bvar 4)) K))))
    (hprim : env.HasPrimitives) (hnat : env.contains ``Nat)
    (hGOc : GO.ClosedN 0) (hPACKc : PACK.ClosedN 0) (hDECc : DEC.ClosedN 0)
    (hMEASc : MEAS.ClosedN 0)
    (x y f : Nat) {h : VExpr}
    (hm : env.IsDefEqU 0 [] (.app MEAS (VExpr.app2' PACK (.natLit x) (.natLit y))) (.natLit x))
    (hh : env.HasType 0 [] h (.natLEApp (.natLit (x+1)) (.natLit (f+1)))) :
    env.IsDefEqU 0 []
      (VExpr.app3 GO (.natLit (f+1)) (VExpr.app2' PACK (.natLit x) (.natLit y)) h)
      (VExpr.condApp .diteNat (.natEqApp (.natLit x) .natZero)
        (.app (.app DEC (.natLit x)) .natZero)
        (.lam (.natEqApp (.natLit x) .natZero) (.natLit y))
        (.lam ((((EA.inst (.natLit x) 3).inst (.natLit y) 2).inst (.natLit f) 1).inst h)
          (VExpr.app3 GO (.natLit f)
            (VExpr.app2' PACK (.natOp ``Nat.mod (.natLit y) (.natLit x)) (.natLit x))
            ((((K.inst (.natLit x) 4).inst (.natLit y) 3).inst (.natLit f) 2).inst h 1)))) := by
  have hhc : h.ClosedN 0 := VExpr.WF.closedN henv.ordered ⟨_, hh⟩ trivial
  have hs : env.IsDefEqU 0 []
      (.app .natSucc (.app MEAS (VExpr.app2' PACK (.natLit x) (.natLit y))))
      (.natLit (x+1)) := reflects_succ henv hprim hnat x hm
  have hty : VExpr.WF env 0 [] (.natLEApp (.natLit (x+1)) (.natLit (f+1))) := by
    obtain ⟨_, hw'⟩ := hh.isType henv trivial; exact ⟨_, hw'⟩
  have hh' : env.HasType 0 [] h
      (.natLEApp (.app .natSucc (.app MEAS (VExpr.app2' PACK (.natLit x) (.natLit y))))
        (.natLit (f+1))) :=
    hh.defeqU_r henv trivial (IsDefEqU.app_congr_fn' henv hty
      (IsDefEqU.app_congr_arg' henv (hty.app_fn' henv) (IsDefEqU.symm hs)))
  have key := IsDefEqU.instGcd henv hlit hMEASc hPACKc hgoeq x y f hh'
  simpa [VExpr.condApp, VExpr.app3, VExpr.app2', VExpr.natOp, VExpr.inst, VExpr.instVar,
    VExpr.natEqApp, VExpr.natEq, VExpr.natLEApp, VExpr.natLE, VExpr.diteNat, VExpr.lift,
    VExpr.liftN, Lean4Lean.liftVar, VExpr.natLit_succ, VExpr.natZero,
    hhc.liftN_eq (Nat.zero_le _), hhc.instN_eq (Nat.zero_le _),
    hGOc.liftN_eq (Nat.zero_le _), hGOc.instN_eq (Nat.zero_le _),
    hPACKc.liftN_eq (Nat.zero_le _), hPACKc.instN_eq (Nat.zero_le _),
    hDECc.liftN_eq (Nat.zero_le _), hDECc.instN_eq (Nat.zero_le _),
    (VExpr.closedN_natLit x).liftN_eq (Nat.zero_le _),
    (VExpr.closedN_natLit x).instN_eq (Nat.zero_le _),
    (VExpr.closedN_natLit y).liftN_eq (Nat.zero_le _),
    (VExpr.closedN_natLit y).instN_eq (Nat.zero_le _),
    (VExpr.closedN_natLit f).liftN_eq (Nat.zero_le _),
    (VExpr.closedN_natLit f).instN_eq (Nat.zero_le _)] using key

end VEnv

/-! ## The entry point: `Nat.eager` unfolded -/

/-- `Nat.succ (h x)`: the fuel `WellFounded.Nat.fix` passes, before `Nat.eager`. -/
def VExpr.eagerFuelAt (MEAS V : VExpr) : VExpr := .app .natSucc (.app MEAS V)

/-- `Nat.eager (h x + 1)`, with `Nat.eager` written out as the conditional `Condition.bool`
reflects.  At a numeral the measure check makes the scrutinee `Nat.beq (a+1) (a+1)`, which
`VEnv.HasPrimitives.natBEq` sends to `true`. -/
def VExpr.eagerITEAt (IN PB DB MEAS V : VExpr) : VExpr :=
  VExpr.condApp IN
    (.app PB (VExpr.app2' (.const ``Nat.beq []) (.eagerFuelAt MEAS V) (.eagerFuelAt MEAS V)))
    (.app DB (VExpr.app2' (.const ``Nat.beq []) (.eagerFuelAt MEAS V) (.eagerFuelAt MEAS V)))
    (.eagerFuelAt MEAS V) (.eagerFuelAt MEAS V)

/-- `Nat.succ (h (pack u v))`: the fuel `WellFounded.Nat.fix` passes, before `Nat.eager`. -/
def VExpr.eagerFuelOf (MEAS PACK u v : VExpr) : VExpr :=
  .eagerFuelAt MEAS (VExpr.app2' PACK u v)

/-- `Nat.eager (h (pack u v) + 1)`, with `Nat.eager` written out as the conditional
`Condition.bool` reflects.  At a pair of numerals the measure check makes the scrutinee
`Nat.beq (a+1) (a+1)`, which `VEnv.HasPrimitives.natBEq` sends to `true`. -/
def VExpr.eagerITEOf (IN PB DB MEAS PACK u v : VExpr) : VExpr :=
  .eagerITEAt IN PB DB MEAS (VExpr.app2' PACK u v)

namespace VEnv
variable {env : VEnv}

/-- **The entry equation at a pair of numerals.** -/
theorem gcd_entry (henv : env.WF) (hlit : env.NatLits) {E GO PACK MEAS IN PB DB PRFA : VExpr}
    (hent : env.IsDefEqU 0 [.nat, .nat]
      (VExpr.app2' E (.bvar 1) (.bvar 0))
      (VExpr.app3 GO (.eagerITEOf IN PB DB MEAS PACK (.bvar 1) (.bvar 0))
        (VExpr.app2' PACK (.bvar 1) (.bvar 0)) PRFA))
    (hEc : E.ClosedN 0) (hGOc : GO.ClosedN 0) (hPACKc : PACK.ClosedN 0)
    (hMEASc : MEAS.ClosedN 0) (hINc : IN.ClosedN 0) (hPBc : PB.ClosedN 0) (hDBc : DB.ClosedN 0)
    (a b : Nat) :
    env.IsDefEqU 0 [] (VExpr.app2' E (.natLit a) (.natLit b))
      (VExpr.app3 GO (.eagerITEOf IN PB DB MEAS PACK (.natLit a) (.natLit b))
        (VExpr.app2' PACK (.natLit a) (.natLit b))
        ((PRFA.inst (.natLit b)).inst (.natLit a))) := by
  have key := IsDefEqU.instNat2 henv hlit hent a b
  simpa [VExpr.app3, VExpr.app2', VExpr.eagerITEOf, VExpr.eagerFuelOf, VExpr.eagerITEAt,
    VExpr.eagerFuelAt, VExpr.condApp, VExpr.inst, VExpr.instVar,
    hEc.instN_eq (Nat.zero_le _), hGOc.instN_eq (Nat.zero_le _),
    hPACKc.instN_eq (Nat.zero_le _), hMEASc.instN_eq (Nat.zero_le _),
    hINc.instN_eq (Nat.zero_le _), hPBc.instN_eq (Nat.zero_le _), hDBc.instN_eq (Nat.zero_le _),
    (VExpr.closedN_natLit a).instN_eq (Nat.zero_le _),
    (VExpr.closedN_natLit b).instN_eq (Nat.zero_le _)] using key

/-- `Nat.succ` applied to a term that reflects `n` reflects `n+1`, from the *typing* of
`Nat.succ` rather than from `VEnv.HasPrimitives` -- which is not monotone, and the
`Nat.bitwise` branch needs this at an arbitrary later environment. -/
theorem reflects_succ' (henv : env.WF) (hlit : env.NatLits)
    (hsucc : env.HasType 0 [] .natSucc (.forallE .nat .nat))
    (n : Nat) {u : VExpr} (h : env.IsDefEqU 0 [] u (.natLit n)) :
    env.IsDefEqU 0 [] (.app .natSucc u) (.natLit (n + 1)) :=
  ⟨_, .appDF hsucc (h.of_r henv trivial (hlit n))⟩

/-- **The `Nat.eager` gadget reduces at a numeral.**  This is the step the measure check exists
for: without `h (pack a b) ≡ a` the scrutinee never becomes a literal and the fuel `Nat.rec`
never fires. -/
theorem eagerITE_reduce (henv : env.WF) (hlit : env.NatLits)
    (hsucc : env.HasType 0 [] .natSucc (.forallE .nat .nat))
    (hbeq2 : ∀ a b : Nat, env.IsDefEqU 0 []
      (VExpr.app2' (.const ``Nat.beq []) (.natLit a) (.natLit b)) (.boolLit (Nat.beq a b)))
    {IN PB DB MEAS V : VExpr} (hB1 : env.ReflectsCondApp1 IN PB DB) {a : Nat}
    (hmeas : env.IsDefEqU 0 [] (.app MEAS V) (.natLit a))
    (hwt : VExpr.WF env 0 [] (.eagerITEAt IN PB DB MEAS V)) :
    env.IsDefEqU 0 [] (.eagerITEAt IN PB DB MEAS V) (.natLit (a+1)) := by
  have hX : env.IsDefEqU 0 [] (.eagerFuelAt MEAS V)
      (.natLit (a+1)) := reflects_succ' henv hlit hsucc a hmeas
  have hSCwt : VExpr.WF env 0 []
      (VExpr.app2' (.const ``Nat.beq []) (.eagerFuelAt MEAS V) (.eagerFuelAt MEAS V)) :=
    (hwt.condApp_cond henv).app_arg' henv
  have hSC : env.IsDefEqU 0 []
      (VExpr.app2' (.const ``Nat.beq []) (.eagerFuelAt MEAS V) (.eagerFuelAt MEAS V))
      (.boolLit true) := by
    refine IsDefEqU.trans henv trivial (IsDefEqU.app2_congr_args henv hSCwt hX hX) ?_
    have := hbeq2 (a+1) (a+1)
    rwa [Nat.beq_refl] at this
  have hsel := ReflectsCondApp1.ofDefeq henv hB1 true hSC _ _ hwt
  exact IsDefEqU.trans henv trivial hsel hX

end VEnv

namespace VEnv
variable {env : VEnv}

/-- Replace the second argument of a three-fold application. -/
theorem IsDefEqU.app3_congr_arg2 (henv : env.WF) {F u v v' w : VExpr}
    (hwt : VExpr.WF env 0 [] (VExpr.app3 F u v w)) (h : env.IsDefEqU 0 [] v v') :
    env.IsDefEqU 0 [] (VExpr.app3 F u v w) (VExpr.app3 F u v' w) :=
  IsDefEqU.app_congr_fn' henv hwt
    (IsDefEqU.app_congr_arg' henv (hwt.app_fn' henv) h)

/-- **The fuel bound of a `go` application, typed at the numeral the measure reflects.**  This
is the induction's step hypothesis and its entry condition at once: `goAppWF_typed` reads the
bound's type off `go`'s checked type, and the measure equation turns `h (pack a b)` into `a`. -/
theorem ok_of_goApp (henv : env.WF) (hlit : env.NatLits)
    (hsucc : env.HasType 0 [] .natSucc (.forallE .nat .nat))
    {GO A MEAS D PACK w : VExpr} {x y f : Nat}
    (hAc : A.ClosedN 0) (hMEASc : MEAS.ClosedN 0)
    (hGOty : env.HasType 0 [] GO (.goTypeWF A MEAS D))
    (hm : env.IsDefEqU 0 [] (.app MEAS (VExpr.app2' PACK (.natLit x) (.natLit y))) (.natLit x))
    (hwt : VExpr.WF env 0 []
      (VExpr.app3 GO (.natLit f) (VExpr.app2' PACK (.natLit x) (.natLit y)) w)) :
    env.HasType 0 [] w (.natLEApp (.natLit (x+1)) (.natLit f)) := by
  obtain ⟨-, -, hw⟩ := goAppWF_typed henv hAc hMEASc hGOty hwt
  have hs : env.IsDefEqU 0 []
      (.app .natSucc (.app MEAS (VExpr.app2' PACK (.natLit x) (.natLit y))))
      (.natLit (x+1)) := reflects_succ' henv hlit hsucc x hm
  refine hw.defeqU_r henv trivial ?_
  have hty : VExpr.WF env 0 []
      (.natLEApp (.app .natSucc (.app MEAS (VExpr.app2' PACK (.natLit x) (.natLit y))))
        (.natLit f)) := by
    obtain ⟨_, hw'⟩ := hw.isType henv trivial
    exact ⟨_, hw'⟩
  exact IsDefEqU.app_congr_fn' henv hty
    (IsDefEqU.app_congr_arg' henv (hty.app_fn' henv) hs)

end VEnv

namespace VEnv
variable {env : VEnv}

/-- Replace the first argument of a two-fold application. -/
theorem IsDefEqU.app2'_congr_arg1 (henv : env.WF) {F u u' v : VExpr}
    (hwt : VExpr.WF env 0 [] (VExpr.app2' F u v)) (h : env.IsDefEqU 0 [] u u') :
    env.IsDefEqU 0 [] (VExpr.app2' F u v) (VExpr.app2' F u' v) :=
  IsDefEqU.app_congr_fn' henv hwt
    (IsDefEqU.app_congr_arg' henv (hwt.app_fn' henv) h)

set_option maxHeartbeats 1000000 in
/-- **The `Nat.gcd` reflection, from the three equations the recognizer checks.** -/
theorem reflects_gcd_of_equations (henv : env.WF) (hlit : env.NatLits)
    (hprim : env.HasPrimitives) (hnat : env.contains ``Nat) (hbeq : env.contains ``Nat.beq)
    (hmodC : env.contains ``Nat.mod)
    {E GO PACK MEAS A D DEC OT OF PR IN PB DB EA KA PRFA : VExpr}
    (hEc : E.ClosedN 0) (hGOc : GO.ClosedN 0) (hPACKc : PACK.ClosedN 0)
    (hMEASc : MEAS.ClosedN 0) (hAc : A.ClosedN 0)
    (hINc : IN.ClosedN 0) (hPBc : PB.ClosedN 0) (hDBc : DB.ClosedN 0) (hDECc : DEC.ClosedN 0)
    (hGOty : env.HasType 0 [] GO (.goTypeWF A MEAS D))
    (hRD : env.ReflectsCondAppD .diteNat .natEq DEC OT OF PR Nat.beq)
    (hB1 : env.ReflectsCondApp1 IN PB DB)
    (hmeas : env.IsDefEqU 0 [.nat, .nat]
      (.app MEAS (VExpr.app2' PACK (.bvar 1) (.bvar 0))) (.bvar 1))
    (hent : env.IsDefEqU 0 [.nat, .nat]
      (VExpr.app2' E (.bvar 1) (.bvar 0))
      (VExpr.app3 GO (.eagerITEOf IN PB DB MEAS PACK (.bvar 1) (.bvar 0))
        (VExpr.app2' PACK (.bvar 1) (.bvar 0)) PRFA))
    (hgoeq : env.IsDefEqU 0 (VExpr.gcdCtx MEAS PACK)
      (VExpr.app3 GO (.app .natSucc (.bvar 1)) (VExpr.app2' PACK (.bvar 3) (.bvar 2)) (.bvar 0))
      (VExpr.condApp .diteNat (.natEqApp (.bvar 3) .natZero)
        (.app (.app DEC (.bvar 3)) .natZero)
        (.lam (.natEqApp (.bvar 3) .natZero) (.bvar 3))
        (.lam EA (VExpr.app3 GO (.bvar 2)
          (VExpr.app2' PACK (.natOp ``Nat.mod (.bvar 3) (.bvar 4)) (.bvar 4)) KA)))) :
    ∀ a b : Nat, env.IsDefEqU 0 [] (VExpr.app2' E (.natLit a) (.natLit b))
      (.natLit (Nat.gcd a b)) := by
  have hmeasL : ∀ a b : Nat, env.IsDefEqU 0 []
      (.app MEAS (VExpr.app2' PACK (.natLit a) (.natLit b))) (.natLit a) := by
    intro a b
    have := IsDefEqU.instNat2 henv hlit hmeas a b
    simpa [VExpr.app2', VExpr.inst, VExpr.instVar,
      hMEASc.instN_eq (Nat.zero_le _), hPACKc.instN_eq (Nat.zero_le _),
      (VExpr.closedN_natLit a).instN_eq (Nat.zero_le _),
      (VExpr.closedN_natLit b).instN_eq (Nat.zero_le _)] using this
  have hgo := fun (f x y : Nat) (h : VExpr)
      (hok : env.HasType 0 [] h (.natLEApp (.natLit (x+1)) (.natLit (f+1)))) =>
    gcd_step henv hlit hgoeq hprim hnat hGOc hPACKc hDECc hMEASc x y f (hmeasL x y) hok
  have hsel : ∀ (f x y : Nat) (h : VExpr),
      env.HasType 0 [] h (.natLEApp (.natLit (x+1)) (.natLit (f+1))) →
      VExpr.WF env 0 []
        (VExpr.condApp .diteNat (.natEqApp (.natLit x) .natZero)
          (.app (.app DEC (.natLit x)) .natZero)
          (.lam (.natEqApp (.natLit x) .natZero) (.natLit y))
          (.lam ((((EA.inst (.natLit x) 3).inst (.natLit y) 2).inst (.natLit f) 1).inst h)
            (VExpr.app3 GO (.natLit f)
              (VExpr.app2' PACK (.natOp ``Nat.mod (.natLit y) (.natLit x)) (.natLit x))
              ((((KA.inst (.natLit x) 4).inst (.natLit y) 3).inst (.natLit f) 2).inst h 1)))) →
      env.IsDefEqU 0 []
        (VExpr.condApp .diteNat (.natEqApp (.natLit x) .natZero)
          (.app (.app DEC (.natLit x)) .natZero)
          (.lam (.natEqApp (.natLit x) .natZero) (.natLit y))
          (.lam ((((EA.inst (.natLit x) 3).inst (.natLit y) 2).inst (.natLit f) 1).inst h)
            (VExpr.app3 GO (.natLit f)
              (VExpr.app2' PACK (.natOp ``Nat.mod (.natLit y) (.natLit x)) (.natLit x))
              ((((KA.inst (.natLit x) 4).inst (.natLit y) 3).inst (.natLit f) 2).inst h 1))))
        (if x = 0 then .natLit y
          else VExpr.app3 GO (.natLit f)
            (VExpr.app2' PACK (.natLit (y % x)) (.natLit x))
            (((((KA.inst (.natLit x) 4).inst (.natLit y) 3).inst (.natLit f) 2).inst h 1).inst
              (.app (.app OF (.natEqApp (.natLit x) .natZero))
                (.app (.app PR (.natLit x)) .natZero)))) := by
    intro f x y h hok hwf
    have d := ReflectsCondAppD.natEq_eq (P := .natEq) hRD x 0 _ _ hwf
    simp only [VExpr.natLit_zero] at d
    by_cases hx0 : x = 0
    · rw [if_pos hx0] at d ⊢
      refine IsDefEqU.trans henv trivial d ?_
      have hb := IsDefEqU.beta_wf henv d.wf_r
      simpa [(VExpr.closedN_natLit y).instN_eq (Nat.zero_le _)] using hb
    · rw [if_neg hx0] at d ⊢
      simp only [VExpr.natEqApp] at d ⊢
      refine IsDefEqU.trans henv trivial d ?_
      have hb := IsDefEqU.beta_wf henv d.wf_r
      have hrw : (VExpr.app3 GO (.natLit f)
            (VExpr.app2' PACK (.natOp ``Nat.mod (.natLit y) (.natLit x)) (.natLit x))
            ((((KA.inst (.natLit x) 4).inst (.natLit y) 3).inst (.natLit f) 2).inst h 1)).inst
            (.app (.app OF (.app (.app VExpr.natEq (.natLit x)) .natZero))
              (.app (.app PR (.natLit x)) .natZero))
          = VExpr.app3 GO (.natLit f)
            (VExpr.app2' PACK (.natOp ``Nat.mod (.natLit y) (.natLit x)) (.natLit x))
            (((((KA.inst (.natLit x) 4).inst (.natLit y) 3).inst (.natLit f) 2).inst h 1).inst
              (.app (.app OF (.app (.app VExpr.natEq (.natLit x)) .natZero))
                (.app (.app PR (.natLit x)) .natZero))) := by
        simp only [VExpr.app3, VExpr.app2', VExpr.natOp, VExpr.inst,
          hGOc.instN_eq (Nat.zero_le 0), hPACKc.instN_eq (Nat.zero_le 0),
          (VExpr.closedN_natLit x).instN_eq (Nat.zero_le 0),
          (VExpr.closedN_natLit y).instN_eq (Nat.zero_le 0),
          (VExpr.closedN_natLit f).instN_eq (Nat.zero_le 0)]
      rw [hrw] at hb
      refine IsDefEqU.trans henv trivial hb ?_
      have hmw := hb.wf_r
      exact IsDefEqU.app3_congr_arg2 henv hmw
        (IsDefEqU.app2'_congr_arg1 henv ((hmw.app_fn' henv).app_arg' henv)
          (hprim.natMod hmodC y x))
  have hK : ∀ (f x y : Nat) (h : VExpr), x < f + 1 →
      env.HasType 0 [] h (.natLEApp (.natLit (x+1)) (.natLit (f+1))) → ¬ x = 0 →
      env.HasType 0 []
        (((((KA.inst (.natLit x) 4).inst (.natLit y) 3).inst (.natLit f) 2).inst h 1).inst
          (.app (.app OF (.natEqApp (.natLit x) .natZero))
            (.app (.app PR (.natLit x)) .natZero)))
        (.natLEApp (.natLit (y % x + 1)) (.natLit f)) := by
    intro f x y h _ hok hx0
    have d := hgo f x y h hok
    have s := hsel f x y h hok d.wf_r
    rw [if_neg hx0] at s
    exact ok_of_goApp henv hlit (hprim.natSucc_hasType hnat) hAc hMEASc hGOty
      (hmeasL (y % x) x) s.wf_r
  have hfuel := reflects_fuel_gcd (GO := GO) (PACK := PACK) henv hlit
    (Ok := fun f x _ h => env.HasType 0 [] h (.natLEApp (.natLit (x+1)) (.natLit f)))
    hgo hsel hK
  intro a b
  have e1 := gcd_entry henv hlit hent hEc hGOc hPACKc hMEASc hINc hPBc hDBc a b
  have hwtR := e1.wf_r
  have hite := eagerITE_reduce henv hlit (hprim.natSucc_hasType hnat) (hprim.natBEq hbeq)
    hB1 (hmeasL a b) (((hwtR.app_fn' henv).app_fn' henv).app_arg' henv)
  have e2 := IsDefEqU.app3_congr_arg1 henv hwtR hite
  refine IsDefEqU.trans henv trivial e1 (IsDefEqU.trans henv trivial e2 ?_)
  exact hfuel (a+1) a b (Nat.lt_succ_self a) _
    (ok_of_goApp henv hlit (hprim.natSucc_hasType hnat) hAc hMEASc hGOty (hmeasL a b) e2.wf_r)

end VEnv

/-! ## Inverting the two equations the `Nat.gcd` branch checks

The `Nat.mod` / `Nat.div` analogues (`trExprS_modEq1_inv'`, `trExprS_modEq2_inv'`) can pin every
head outright, because the recursion's `go` is a *constant*.  Here `go`, `pack` and the measure
are arbitrary terms recovered by the unfolder, so they are identified with their base-context
translations by `TrExprS.unique` -- which is what the unfolder's `noProj` check is for -- and
carried under `Condition.dite`'s λ by `trExprS_weakBV0` -- which is what its `bvarsBelow` check
is for. -/

section
open Lean hiding Environment Exception
open Kernel Lean4Lean.Environment

/-- **The entry equation's right-hand side.** -/
theorem trExprS_gcdEntry_inv' {env : VEnv} {Us} {Δ : VLCtx}
    {go pack meas prfA : Lean.Expr} {idm idn : FVarId}
    {GO PACK MEAS PB DB M N e' : VExpr}
    (hgo : TrExprS env Us Δ go GO) (hgou : TrExprS.IsUnique go)
    (hpack : TrExprS env Us Δ pack PACK) (hpacku : TrExprS.IsUnique pack)
    (hmeas : TrExprS env Us Δ meas MEAS) (hmeasu : TrExprS.IsUnique meas)
    (hpb : TrExprS env Us Δ Lean4Lean.Environment.Condition.bool.prop PB)
    (hdb : TrExprS env Us Δ Lean4Lean.Environment.Condition.bool.dec DB)
    (hm : TrExprS env Us Δ (.fvar idm) M) (hn : TrExprS env Us Δ (.fvar idn) N)
    (h : TrExprS env Us Δ
      (Lean.mkApp3 go
        (Lean4Lean.Environment.Condition.bool.ite (.const ``Nat [])
          #[Lean.mkApp2 (.const ``Nat.beq [])
              (Lean.mkApp (.const ``Nat.succ [])
                (Lean.mkApp meas (Lean.mkApp2 pack (.fvar idm) (.fvar idn))))
              (Lean.mkApp (.const ``Nat.succ [])
                (Lean.mkApp meas (Lean.mkApp2 pack (.fvar idm) (.fvar idn))))]
          (Lean.mkApp (.const ``Nat.succ [])
            (Lean.mkApp meas (Lean.mkApp2 pack (.fvar idm) (.fvar idn))))
          (Lean.mkApp (.const ``Nat.succ [])
            (Lean.mkApp meas (Lean.mkApp2 pack (.fvar idm) (.fvar idn)))))
        (Lean.mkApp2 pack (.fvar idm) (.fvar idn))
        (Lean.mkApp2 prfA (.fvar idm) (.fvar idn))) e') :
    ∃ PRFA, e' = VExpr.app3 GO (.eagerITEOf .iteNat PB DB MEAS PACK M N)
      (VExpr.app2' PACK M N) PRFA := by
  have hpk : ∀ {u : VExpr},
      TrExprS env Us Δ (Lean.mkApp2 pack (.fvar idm) (.fvar idn)) u →
      u = VExpr.app2' PACK M N := by
    intro u hu
    obtain ⟨_, _, rfl, p1, p2⟩ := trExprS_app_inv' hu
    obtain ⟨_, _, rfl, p3, p4⟩ := trExprS_app_inv' p1
    cases TrExprS.unique hpacku p3 hpack
    cases trExprS_fvar_uniq p4 hm
    cases trExprS_fvar_uniq p2 hn
    rfl
  have hX : ∀ {u : VExpr},
      TrExprS env Us Δ (Lean.mkApp (.const ``Nat.succ [])
        (Lean.mkApp meas (Lean.mkApp2 pack (.fvar idm) (.fvar idn)))) u →
      u = .eagerFuelOf MEAS PACK M N := by
    intro u hu
    obtain ⟨_, _, rfl, s1, s2⟩ := trExprS_app_inv' hu
    cases trExprS_const_nil_inv' s1
    obtain ⟨_, _, rfl, s3, s4⟩ := trExprS_app_inv' s2
    cases TrExprS.unique hmeasu s3 hmeas
    cases hpk s4
    rfl
  simp only [Lean4Lean.Environment.Condition.ite, Lean4Lean.Environment.Condition.bool, Lean.mkApp5, Lean.mkApp3, Lean.mkApp2,
    Lean.mkApp, Lean.mkAppN] at h
  obtain ⟨_, _, rfl, a1, aPr⟩ := trExprS_app_inv' h
  obtain ⟨_, _, rfl, a2, aPk⟩ := trExprS_app_inv' a1
  obtain ⟨_, _, rfl, a3, aIte⟩ := trExprS_app_inv' a2
  cases TrExprS.unique hgou a3 hgo
  cases hpk aPk
  obtain ⟨_, _, rfl, b1, bE⟩ := trExprS_app_inv' aIte
  obtain ⟨_, _, rfl, b2, bT⟩ := trExprS_app_inv' b1
  obtain ⟨_, _, rfl, b3, bD⟩ := trExprS_app_inv' b2
  obtain ⟨_, _, rfl, b4, bP⟩ := trExprS_app_inv' b3
  cases trExprS_iteNat_inv' b4
  cases hX bE
  cases hX bT
  obtain ⟨_, _, rfl, p1, p2⟩ := trExprS_app_inv' bP
  cases TrExprS.unique (e := Lean4Lean.Environment.Condition.bool.prop)
    (by simp [Lean4Lean.Environment.Condition.bool, TrExprS.IsUnique]) p1 hpb
  obtain ⟨_, _, rfl, q1, q2⟩ := trExprS_app_inv' p2
  obtain ⟨_, _, rfl, q3, q4⟩ := trExprS_app_inv' q1
  cases trExprS_const_nil_inv' q3
  cases hX q4
  cases hX q2
  obtain ⟨_, _, rfl, d1, d2⟩ := trExprS_app_inv' bD
  cases TrExprS.unique (e := Lean4Lean.Environment.Condition.bool.dec)
    (by simp [Lean4Lean.Environment.Condition.bool, TrExprS.IsUnique]) d1 hdb
  obtain ⟨_, _, rfl, e1, e2⟩ := trExprS_app_inv' d2
  obtain ⟨_, _, rfl, e3, e4⟩ := trExprS_app_inv' e1
  cases trExprS_const_nil_inv' e3
  cases hX e4
  cases hX e2
  exact ⟨_, rfl⟩

/-- **The fuel recurrence's right-hand side.** -/
theorem trExprS_gcdGo_inv' {env : VEnv} {Us} {Δ : VLCtx}
    {go pack prf : Lean.Expr} {idm idn idf : FVarId}
    {GO PACK M N FU e' : VExpr} (henv : env.Ordered)
    (hgo : TrExprS env Us Δ go GO) (hgou : TrExprS.IsUnique go)
    (hgob : go.looseBVarRange' = 0) (hGOc : GO.ClosedN 0)
    (hpack : TrExprS env Us Δ pack PACK) (hpacku : TrExprS.IsUnique pack)
    (hpackb : pack.looseBVarRange' = 0) (hPACKc : PACK.ClosedN 0)
    (hm : TrExprS env Us Δ (.fvar idm) M) (hn : TrExprS env Us Δ (.fvar idn) N)
    (hf : TrExprS env Us Δ (.fvar idf) FU)
    (h : TrExprS env Us Δ
      (Lean4Lean.Environment.Condition.natEq.dite #[.fvar idm, .const ``Nat.zero []]
        (.fvar idn)
        (Lean.mkApp3 go (.fvar idf)
          (Lean.mkApp2 pack
            (Lean.mkApp2 (.const ``Nat.mod []) (.fvar idn) (.fvar idm)) (.fvar idm)) prf)) e') :
    ∃ EA K, e' = VExpr.condApp .diteNat (.natEqApp M .natZero)
      (.app (.app (.const ``Nat.decEq []) M) .natZero)
      (.lam (.natEqApp M .natZero) N.lift)
      (.lam EA (VExpr.app3 GO FU.lift
        (VExpr.app2' PACK (.natOp ``Nat.mod N.lift M.lift) M.lift) K)) := by
  simp only [Lean4Lean.Environment.Condition.dite, Lean4Lean.Environment.Condition.natEq,
    Lean.Expr.lam0, Lean.mkApp4, Lean.mkApp3, Lean.mkApp2, Lean.mkAppN] at h
  obtain ⟨_, _, rfl, b1, bE⟩ := trExprS_app_inv' h
  obtain ⟨_, _, rfl, b2, bT⟩ := trExprS_app_inv' b1
  obtain ⟨_, _, rfl, b3, bD⟩ := trExprS_app_inv' b2
  obtain ⟨_, _, rfl, b4, bP⟩ := trExprS_app_inv' b3
  cases trExprS_diteNat_inv' b4
  obtain ⟨_, _, rfl, q1, q2⟩ := trExprS_natEqApp_inv' bP
  cases trExprS_fvar_uniq q1 hm
  cases trExprS_const_nil_inv' q2
  obtain ⟨_, _, rfl, e1, e2⟩ := trExprS_app_inv' bD
  obtain ⟨_, _, rfl, e3, e4⟩ := trExprS_app_inv' e1
  cases trExprS_const_nil_inv' e3
  cases trExprS_fvar_uniq e4 hm
  cases trExprS_const_nil_inv' e2
  obtain ⟨_, _, rfl, t1, t2⟩ := trExprS_lam_inv' bT
  obtain ⟨_, _, rfl, u1, u2⟩ := trExprS_natEqApp_inv' t1
  cases trExprS_fvar_uniq u1 hm
  cases trExprS_const_nil_inv' u2
  cases trExprS_fvar_uniq t2 (trExprS_liftBV0 henv hn rfl)
  obtain ⟨_, _, rfl, z1, z2⟩ := trExprS_lam_inv' bE
  obtain ⟨_, _, rfl, w1, w2⟩ := trExprS_app_inv' z2
  obtain ⟨_, _, rfl, w3, w4⟩ := trExprS_app_inv' w1
  obtain ⟨_, _, rfl, w5, w6⟩ := trExprS_app_inv' w3
  cases TrExprS.unique hgou w5 (trExprS_weakBV0 henv hgo hgob hGOc)
  cases trExprS_fvar_uniq w6 (trExprS_liftBV0 henv hf rfl)
  obtain ⟨_, _, rfl, y1, y2⟩ := trExprS_app_inv' w4
  obtain ⟨_, _, rfl, y3, y4⟩ := trExprS_app_inv' y1
  cases TrExprS.unique hpacku y3 (trExprS_weakBV0 henv hpack hpackb hPACKc)
  obtain ⟨_, _, rfl, v1, v2⟩ := trExprS_app_inv' y4
  obtain ⟨_, _, rfl, v3, v4⟩ := trExprS_app_inv' v1
  cases trExprS_const_nil_inv' v3
  cases trExprS_fvar_uniq v4 (trExprS_liftBV0 henv hn rfl)
  cases trExprS_fvar_uniq v2 (trExprS_liftBV0 henv hm rfl)
  cases trExprS_fvar_uniq y2 (trExprS_liftBV0 henv hm rfl)
  exact ⟨_, _, rfl⟩

namespace TypeChecker
variable {c : VContext}

/-- The packing function applied to two `Nat`s. -/
theorem trExprS_packApp {PACK A M N : VExpr} {pk m n : Lean.Expr}
    (hp : c.TrExprS pk PACK) (hpty : c.HasType PACK (.forallE .nat (.forallE .nat A)))
    (hAc : A.ClosedN 0)
    (hm : c.TrExprS m M) (hmty : c.HasType M .nat)
    (hn : c.TrExprS n N) (hnty : c.HasType N .nat) :
    c.TrExprS (Lean.mkApp2 pk m n) (VExpr.app2' PACK M N) ∧
      c.HasType (VExpr.app2' PACK M N) A := by
  obtain ⟨s1, y1⟩ := trExprS_appD hp hpty hm hmty
  simp only [VExpr.inst, VExpr.inst_nat, hAc.instN_eq (Nat.zero_le _)] at y1
  obtain ⟨s2, y2⟩ := trExprS_appD s1 y1 hn hnty
  simp only [hAc.instN_eq (Nat.zero_le _)] at y2
  exact ⟨s2, y2⟩

/-- The measure applied to a packed argument. -/
theorem trExprS_measApp {MEAS A V : VExpr} {meas v : Lean.Expr}
    (hm : c.TrExprS meas MEAS) (hmty : c.HasType MEAS (.forallE A .nat))
    (hv : c.TrExprS v V) (hvty : c.HasType V A) :
    c.TrExprS (Lean.mkApp meas v) (.app MEAS V) ∧ c.HasType (.app MEAS V) .nat := by
  obtain ⟨s1, y1⟩ := trExprS_appD hm hmty hv hvty
  rw [VExpr.inst_nat] at y1
  exact ⟨s1, y1⟩

/-- **A `WellFounded.Nat.fix.go` application in the shape the recognizer builds**, from the
type `checkedTypeIs` pins.  The `Nat.gcd` / `Nat.bitwise` counterpart of `trExprS_goApp`. -/
theorem trExprS_goAppWF {GO A MEAS D U V W : VExpr} {go a b h : Lean.Expr}
    (hgo : c.TrExprS go GO) (hgoty : c.HasType GO (.goTypeWF A MEAS D))
    (hAc : A.ClosedN 0) (hMEASc : MEAS.ClosedN 0)
    (ha : c.TrExprS a U) (haty : c.HasType U .nat)
    (hb : c.TrExprS b V) (hbty : c.HasType V A)
    (hh : c.TrExprS h W)
    (hhty : c.HasType W (.natLEApp (.app .natSucc (.app MEAS V)) U)) :
    c.TrExprS (Lean.mkApp3 go a b h) (VExpr.app3 GO U V W) := by
  obtain ⟨s1, y1⟩ := trExprS_appD hgo hgoty ha haty
  rw [show ((VExpr.forallE A (.forallE
      (.natLEApp (.app .natSucc (.app MEAS (.bvar 0))) (.bvar 1)) D)).inst U)
      = .forallE A (.forallE (.natLEApp (.app .natSucc (.app MEAS (.bvar 0))) U.lift)
        (D.inst U 2)) by
    simp [VExpr.inst, VExpr.instVar, VExpr.natLEApp, VExpr.natLE,
      hAc.instN_eq (Nat.zero_le _), hMEASc.instN_eq (Nat.zero_le _)]] at y1
  obtain ⟨s2, y2⟩ := trExprS_appD s1 y1 hb hbty
  rw [show ((VExpr.forallE (.natLEApp (.app .natSucc (.app MEAS (.bvar 0))) U.lift)
      (D.inst U 2)).inst V)
      = .forallE (.natLEApp (.app .natSucc (.app MEAS V)) U) ((D.inst U 2).inst V 1) by
    simp [VExpr.inst, VExpr.instVar, VExpr.natLEApp, VExpr.natLE, VExpr.inst_lift,
      hMEASc.instN_eq (Nat.zero_le _)]] at y2
  exact (trExprS_appD s2 y2 hh hhty).1

end TypeChecker

/-! ## `Nat.bitwise`: the fuel recursion -/

/-- `Condition.natEq.decide #[Nat.mod x 2, 1]` at an arbitrary scrutinee.  `VExpr.bitParity` is
this at a numeral. -/
def VExpr.bitParityG (Ib Pe De x : VExpr) : VExpr :=
  VExpr.condApp Ib
    (VExpr.app2' Pe (VExpr.natOp ``Nat.mod x (.natLit 2)) (.natLit 1))
    (VExpr.app2' De (VExpr.natOp ``Nat.mod x (.natLit 2)) (.natLit 1))
    .boolTrue .boolFalse

theorem VExpr.bitParityG_lit {Ib Pe De : VExpr} {a : Nat} :
    VExpr.bitParityG Ib Pe De (.natLit a) = VExpr.bitParity Ib Pe De a := rfl

/-- One `Condition.bool` selection: `if c then t else e` at result type `Nat`. -/
def VExpr.bitSel (In Pb Db c t e : VExpr) : VExpr := VExpr.condApp In (Pb.app c) (Db.app c) t e

/-- The `n = 0` branch of `Nat.bitwise`'s body. -/
def VExpr.bitwiseFuelThen (In Pb Db f : VExpr) (b : Nat) : VExpr :=
  VExpr.bitSel In Pb Db (VExpr.app2' f .boolFalse .boolTrue) (.natLit b) (.natLit 0)

/-- The `n ≠ 0` branch of `Nat.bitwise`'s body, with the recursive call `r` abstracted. -/
def VExpr.bitwiseFuelElse (In Ib Pe De Pb Db f r : VExpr) (a b : Nat) : VExpr :=
  VExpr.condApp In (VExpr.app2' Pe (.natLit b) (.natLit 0))
      (VExpr.app2' De (.natLit b) (.natLit 0))
    (VExpr.bitSel In Pb Db (VExpr.app2' f .boolTrue .boolFalse) (.natLit a) (.natLit 0))
    (VExpr.bitSel In Pb Db
      (VExpr.app2' f (VExpr.bitParity Ib Pe De a) (VExpr.bitParity Ib Pe De b))
      (VExpr.natOp ``Nat.add (VExpr.natOp ``Nat.add r r) (.natLit 1))
      (VExpr.natOp ``Nat.add r r))

/-- **The right-hand side the `Nat.bitwise` fuel recurrence is checked against**, at a pair of
numerals.  Same shape as `VExpr.bitwiseRhs`, with two differences: the outer `n = 0` test is a
`dite` (the recognizer writes it that way so that the recursive call's fuel bound has `n ≠ 0` in
scope), and the recursive call is an explicit `go` application `r` rather than a self-call. -/
def VExpr.bitwiseFuelRhs (In Ib Pe De Pb Db f EA r : VExpr) (a b : Nat) : VExpr :=
  VExpr.condApp .diteNat (VExpr.app2' Pe (.natLit a) (.natLit 0))
      (VExpr.app2' De (.natLit a) (.natLit 0))
    (.lam (VExpr.app2' Pe (.natLit a) (.natLit 0)) (VExpr.bitwiseFuelThen In Pb Db f b))
    (.lam EA (VExpr.bitwiseFuelElse In Ib Pe De Pb Db f r a b))

theorem VExpr.bitwiseFuelThen_inst {In Pb Db f : VExpr} {b : Nat}
    (hInc : In.ClosedN 0) (hPbc : Pb.ClosedN 0) (hDbc : Db.ClosedN 0) (hfc : f.ClosedN 0)
    (w : VExpr) (j : Nat) :
    (VExpr.bitwiseFuelThen In Pb Db f b).inst w j = VExpr.bitwiseFuelThen In Pb Db f b := by
  simp [VExpr.bitwiseFuelThen, VExpr.bitSel, VExpr.condApp, VExpr.app2', VExpr.inst,
    VExpr.boolFalse, VExpr.boolTrue,
    hInc.instN_eq (Nat.zero_le _), hPbc.instN_eq (Nat.zero_le _),
    hDbc.instN_eq (Nat.zero_le _), hfc.instN_eq (Nat.zero_le _),
    (VExpr.closedN_natLit b).instN_eq (Nat.zero_le _),
    (VExpr.closedN_natLit 0).instN_eq (Nat.zero_le _)]

theorem VExpr.bitwiseFuelElse_inst {In Ib Pe De Pb Db f r : VExpr} {a b : Nat}
    (hInc : In.ClosedN 0) (hIbc : Ib.ClosedN 0) (hPec : Pe.ClosedN 0) (hDec : De.ClosedN 0)
    (hPbc : Pb.ClosedN 0) (hDbc : Db.ClosedN 0) (hfc : f.ClosedN 0) (w : VExpr) (j : Nat) :
    (VExpr.bitwiseFuelElse In Ib Pe De Pb Db f r a b).inst w j
      = VExpr.bitwiseFuelElse In Ib Pe De Pb Db f (r.inst w j) a b := by
  simp [VExpr.bitwiseFuelElse, VExpr.bitSel, VExpr.condApp, VExpr.app2', VExpr.natOp,
    VExpr.bitParity, VExpr.inst, VExpr.boolFalse, VExpr.boolTrue,
    hInc.instN_eq (Nat.zero_le _), hIbc.instN_eq (Nat.zero_le _),
    hPec.instN_eq (Nat.zero_le _), hDec.instN_eq (Nat.zero_le _),
    hPbc.instN_eq (Nat.zero_le _), hDbc.instN_eq (Nat.zero_le _),
    hfc.instN_eq (Nat.zero_le _),
    (VExpr.closedN_natLit a).instN_eq (Nat.zero_le _),
    (VExpr.closedN_natLit b).instN_eq (Nat.zero_le _),
    (VExpr.closedN_natLit 0).instN_eq (Nat.zero_le _),
    (VExpr.closedN_natLit 1).instN_eq (Nat.zero_le _),
    (VExpr.closedN_natLit 2).instN_eq (Nat.zero_le _)]

namespace VEnv
variable {env : VEnv}

/-- `VEnv.reflects_natOp` from the *applied* reflection.  `ReflectsNatNatNat.mono` needs
`env'.constants fc = env.constants fc`, which an arbitrary extension does not give; the applied
family is a plain `IsDefEqU` and so is monotone. -/
theorem reflects_natOp' (henv : env.WF) {n : Name} {op : Nat → Nat → Nat}
    (h : ∀ a b : Nat, env.IsDefEqU 0 []
      (VExpr.natOp n (.natLit a) (.natLit b)) (.natLit (op a b)))
    {u v : VExpr} {a b : Nat}
    (hwt : VExpr.WF env 0 [] (VExpr.natOp n u v))
    (hu : env.IsDefEqU 0 [] u (.natLit a)) (hv : env.IsDefEqU 0 [] v (.natLit b)) :
    env.IsDefEqU 0 [] (VExpr.natOp n u v) (.natLit (op a b)) :=
  IsDefEqU.trans henv trivial (IsDefEqU.app2_congr_args henv hwt hu hv) (h a b)

/-- `VEnv.reflects_bitParity` from the applied `Nat.mod` reflection. -/
theorem reflects_bitParity' (henv : env.WF) (hlit : env.NatLits)
    (hmod2 : ∀ a b : Nat, env.IsDefEqU 0 []
      (VExpr.natOp ``Nat.mod (.natLit a) (.natLit b)) (.natLit (a % b)))
    {Ib Pe De : VExpr}
    (hcEb : env.ReflectsCondApp Ib Pe De Nat.beq) (x : Nat)
    (hwt : VExpr.WF env 0 [] (VExpr.bitParity Ib Pe De x)) :
    env.IsDefEqU 0 [] (VExpr.bitParity Ib Pe De x) (.boolLit (decide (x % 2 = 1))) := by
  have h := ReflectsCondApp.ofDefeq henv hcEb (x % 2) 1
    (hmod2 x 2) (IsDefEqU.refl ⟨_, hlit 1⟩) _ _ hwt
  rwa [natBeq_eq_decide, bif_boolLit] at h

set_option maxHeartbeats 1000000 in
/-- **`Nat.bitwise`'s fuel recursion.**  The conditional reasoning is `reflects_natBitwise_go`'s;
what changes is that the recursion goes through `go` at a decreasing fuel rather than through
`Nat.bitwise` itself, so the induction is on the fuel under the invariant `a < fuel`. -/
theorem reflects_fuel_bitwise (henv : env.WF) (hlit : env.NatLits)
    (hadd2 : ∀ a b : Nat, env.IsDefEqU 0 []
      (VExpr.natOp ``Nat.add (.natLit a) (.natLit b)) (.natLit (a + b)))
    (hdiv2 : ∀ a b : Nat, env.IsDefEqU 0 []
      (VExpr.natOp ``Nat.div (.natLit a) (.natLit b)) (.natLit (a / b)))
    (hmod2 : ∀ a b : Nat, env.IsDefEqU 0 []
      (VExpr.natOp ``Nat.mod (.natLit a) (.natLit b)) (.natLit (a % b)))
    {In Ib Pe De Pb Db OT OF PR GO PACK f : VExpr} {g : Bool → Bool → Bool}
    (hInc : In.ClosedN 0) (hIbc : Ib.ClosedN 0) (hPec : Pe.ClosedN 0) (hDec : De.ClosedN 0)
    (hPbc : Pb.ClosedN 0) (hDbc : Db.ClosedN 0) (hGOc : GO.ClosedN 0) (hPACKc : PACK.ClosedN 0)
    (hf : env.ReflectsBoolBoolBool f g)
    (hcE : env.ReflectsCondApp In Pe De Nat.beq)
    (hcEb : env.ReflectsCondApp Ib Pe De Nat.beq)
    (hcB : env.ReflectsCondApp1 In Pb Db)
    (hRD : env.ReflectsCondAppD .diteNat Pe De OT OF PR Nat.beq)
    {EA K : Nat → Nat → Nat → VExpr → VExpr} {Ok : Nat → Nat → Nat → VExpr → Prop}
    (hgo : ∀ (fl a b : Nat) (h : VExpr), Ok (fl+1) a b h →
      env.IsDefEqU 0 []
        (VExpr.app3 GO (.natLit (fl+1)) (VExpr.app3 PACK f (.natLit a) (.natLit b)) h)
        (VExpr.bitwiseFuelRhs In Ib Pe De Pb Db f (EA fl a b h)
          (VExpr.app3 GO (.natLit fl)
            (VExpr.app3 PACK f (.natOp ``Nat.div (.natLit a) (.natLit 2))
              (.natOp ``Nat.div (.natLit b) (.natLit 2))) (K fl a b h)) a b))
    (hOk : ∀ (fl a b : Nat) (w : VExpr),
      VExpr.WF env 0 [] (VExpr.app3 GO (.natLit fl) (VExpr.app3 PACK f (.natLit a) (.natLit b)) w) →
      Ok fl a b w) :
    ∀ (fuel a b : Nat), a < fuel → ∀ h, Ok fuel a b h →
      env.IsDefEqU 0 []
        (VExpr.app3 GO (.natLit fuel) (VExpr.app3 PACK f (.natLit a) (.natLit b)) h)
        (.natLit (Nat.bitwise g a b)) := by
  have hfc : f.ClosedN 0 := VExpr.WF.closedN henv.ordered ⟨_, hf.1⟩ trivial
  have inst0 : ∀ {e : VExpr}, e.ClosedN 0 → ∀ (w : VExpr) (j : Nat), e.inst w j = e :=
    fun hc _ _ => hc.instN_eq (Nat.zero_le _)
  have natOpc : ∀ (k : Name) (x y : Nat) (w : VExpr) (j : Nat),
      (VExpr.natOp k (.natLit x) (.natLit y)).inst w j = VExpr.natOp k (.natLit x) (.natLit y) :=
    fun k x y w j => by
      simp [VExpr.natOp, VExpr.app2', VExpr.inst,
        (VExpr.closedN_natLit x).instN_eq (Nat.zero_le _),
        (VExpr.closedN_natLit y).instN_eq (Nat.zero_le _)]
  intro fuel
  induction fuel with
  | zero => intro a b ha; exact absurd ha (by omega)
  | succ fl ih =>
  intro a b ha h hok
  have e1 := hgo fl a b h hok
  refine IsDefEqU.trans henv trivial e1 ?_
  have hw := e1.wf_r
  have o1 := ReflectsCondAppD.natEq_eq hRD a 0 _ _ hw
  by_cases ha0 : a = 0
  · rw [if_pos ha0] at o1
    refine IsDefEqU.trans henv trivial o1 ?_
    have hb := IsDefEqU.beta_wf henv o1.wf_r
    rw [VExpr.bitwiseFuelThen_inst hInc hPbc hDbc hfc] at hb
    simp only [VExpr.bitwiseFuelThen, VExpr.bitSel] at hb
    refine IsDefEqU.trans henv trivial hb ?_
    have hs := ReflectsCondApp1.ofDefeq henv hcB (g false true) (hf.2 false true) _ _ hb.wf_r
    refine IsDefEqU.trans henv trivial hs ?_
    subst ha0
    rw [Nat.bitwise]
    cases hgb : g false true
    · rw [hgb] at hs
      simp only [cond_false, Bool.false_eq_true, if_false, reduceIte]
      exact IsDefEqU.refl hs.wf_r
    · rw [hgb] at hs
      simp only [cond_true, reduceIte]
      exact IsDefEqU.refl hs.wf_r
  · rw [if_neg ha0] at o1
    refine IsDefEqU.trans henv trivial o1 ?_
    have hb := IsDefEqU.beta_wf henv o1.wf_r
    rw [VExpr.bitwiseFuelElse_inst hInc hIbc hPec hDec hPbc hDbc hfc] at hb
    have rinst : ∀ (w : VExpr) (j : Nat),
        (VExpr.app3 GO (.natLit fl) (VExpr.app3 PACK f
            (VExpr.natOp ``Nat.div (.natLit a) (.natLit 2))
            (VExpr.natOp ``Nat.div (.natLit b) (.natLit 2))) (K fl a b h)).inst w j
          = VExpr.app3 GO (.natLit fl) (VExpr.app3 PACK f
            (VExpr.natOp ``Nat.div (.natLit a) (.natLit 2))
            (VExpr.natOp ``Nat.div (.natLit b) (.natLit 2))) ((K fl a b h).inst w j) := by
      intro w j
      simp only [VExpr.app3, VExpr.inst, inst0 hGOc, inst0 hPACKc, inst0 hfc, natOpc,
        (VExpr.closedN_natLit fl).instN_eq (Nat.zero_le _)]
    rw [rinst] at hb
    simp only [VExpr.bitwiseFuelElse, VExpr.bitSel] at hb
    refine IsDefEqU.trans henv trivial hb ?_
    have o2 := hcE b 0 _ _ hb.wf_r
    rw [natBeq_eq_decide] at o2
    by_cases hb0 : b = 0
    · subst hb0
      simp only [decide_true, cond_true] at o2
      refine IsDefEqU.trans henv trivial o2 ?_
      have hs := ReflectsCondApp1.ofDefeq henv hcB (g true false) (hf.2 true false) _ _ o2.wf_r
      refine IsDefEqU.trans henv trivial hs ?_
      rw [Nat.bitwise]
      cases hgb : g true false
      · rw [hgb] at hs
        simp only [cond_false, if_neg ha0, reduceIte]
        exact IsDefEqU.refl hs.wf_r
      · rw [hgb] at hs
        simp only [cond_true, if_neg ha0, reduceIte]
        exact IsDefEqU.refl hs.wf_r
    · simp only [decide_eq_false hb0, cond_false] at o2
      refine IsDefEqU.trans henv trivial o2 ?_
      have hsel := o2.wf_r
      have hcond := hsel.condApp_cond henv
      have hfab : VExpr.WF env 0 []
          (VExpr.app2' f (VExpr.bitParity Ib Pe De a) (VExpr.bitParity Ib Pe De b)) :=
        hcond.app_arg' henv
      have hp1 := reflects_bitParity' henv hlit hmod2 hcEb a (hfab.app2_arg1 henv)
      have hp2 := reflects_bitParity' henv hlit hmod2 hcEb b (hfab.app2_arg2 henv)
      have hfb : env.IsDefEqU 0 []
          (VExpr.app2' f (VExpr.bitParity Ib Pe De a) (VExpr.bitParity Ib Pe De b))
          (.boolLit (g (decide (a % 2 = 1)) (decide (b % 2 = 1)))) :=
        IsDefEqU.trans henv trivial (IsDefEqU.app2_congr_args henv hfab hp1 hp2) (hf.2 _ _)
      have hrw := hsel.condApp_t henv
      have hrr := hrw.app2_arg1 henv
      have hr := hrr.app2_arg1 henv
      have hltf : a / 2 < fl := by
        have : a / 2 < a := Nat.div_lt_self (Nat.pos_of_ne_zero ha0) (by omega)
        omega
      have hpackwf : VExpr.WF env 0 []
          (VExpr.app3 PACK f (VExpr.natOp ``Nat.div (.natLit a) (.natLit 2))
            (VExpr.natOp ``Nat.div (.natLit b) (.natLit 2))) :=
        (hr.app_fn' henv).app_arg' henv
      have hpk : env.IsDefEqU 0 []
          (VExpr.app3 PACK f (VExpr.natOp ``Nat.div (.natLit a) (.natLit 2))
            (VExpr.natOp ``Nat.div (.natLit b) (.natLit 2)))
          (VExpr.app3 PACK f (.natLit (a / 2)) (.natLit (b / 2))) := by
        refine IsDefEqU.trans henv trivial
          (IsDefEqU.app3_congr_arg2 henv hpackwf (hdiv2 a 2)) ?_
        exact IsDefEqU.app_congr_arg' henv
          (IsDefEqU.app3_congr_arg2 henv hpackwf (hdiv2 a 2)).wf_r (hdiv2 b 2)
      have hstep := IsDefEqU.app3_congr_arg2 henv hr hpk
      have hrec := IsDefEqU.trans henv trivial hstep
        (ih (a / 2) (b / 2) hltf _ (hOk fl (a / 2) (b / 2) _ hstep.wf_r))
      have hsum := reflects_natOp' henv hadd2 hrr hrec hrec
      have hsum1 := reflects_natOp' henv hadd2 hrw hsum (IsDefEqU.refl ⟨_, hlit 1⟩)
      have hs := ReflectsCondApp1.ofDefeq henv hcB _ hfb _ _ hsel
      refine IsDefEqU.trans henv trivial hs ?_
      have hbw : Nat.bitwise g a b =
          (if g (decide (a % 2 = 1)) (decide (b % 2 = 1)) then
            Nat.bitwise g (a / 2) (b / 2) + Nat.bitwise g (a / 2) (b / 2) + 1
          else Nat.bitwise g (a / 2) (b / 2) + Nat.bitwise g (a / 2) (b / 2)) := by
        conv => lhs; rw [Nat.bitwise]
        simp only [if_neg ha0, if_neg hb0]
      rw [hbw]
      cases hgb : g (decide (a % 2 = 1)) (decide (b % 2 = 1))
      · simp only [hgb, cond_false, Bool.false_eq_true, if_false, reduceIte]
        exact hsum
      · simp only [hgb, cond_true, if_true, reduceIte]
        exact hsum1

end VEnv

end

/-! ## Instantiating the two equations the `Nat.bitwise` branch checks

The extra binder over `Nat.gcd`'s is the combinator, and it is the reason the whole assembly is
relativized: the equations are checked at `c.venv`, but `VEnv.ReflectsNatBitwise` quantifies
over an arbitrary later environment and a combinator that lives only there.  `IsDefEqU` is
monotone, so the equations transfer; what does not is `VEnv.ReflectsCondApp`, whose `VExpr.WF`
premise is negative -- hence `VEnv.ReflectsCondAppAll`. -/

/-- `Bool → Bool → Bool`. -/
def VExpr.boolBoolBool : VExpr := .forallE .bool (.forallE .bool .bool)

/-- The context the `Nat.bitwise` fuel recurrence is checked in: the combinator, `n`, `m`,
`fuel`, and the fuel bound. -/
def VExpr.bitwiseCtx (MEAS PACK : VExpr) : List VExpr :=
  [.natLEApp (.app .natSucc (.app MEAS (VExpr.app3 PACK (.bvar 3) (.bvar 2) (.bvar 1))))
      (.app .natSucc (.bvar 0)),
    .nat, .nat, .nat, .boolBoolBool]

namespace VEnv
variable {env : VEnv}

/-- Instantiate an equation proved in `VExpr.bitwiseCtx`. -/
theorem IsDefEqU.instBitwise (henv : env.WF) (hlit : env.NatLits) {MEAS PACK e₁ e₂ : VExpr}
    (hMEASc : MEAS.ClosedN 0) (hPACKc : PACK.ClosedN 0)
    (H : env.IsDefEqU 0 (VExpr.bitwiseCtx MEAS PACK) e₁ e₂) {F₀ : VExpr}
    (hF₀ : env.HasType 0 [] F₀ .boolBoolBool) (hF₀c : F₀.ClosedN 0) (a b fl : Nat) {h : VExpr}
    (hh : env.HasType 0 [] h
      (.natLEApp (.app .natSucc (.app MEAS (VExpr.app3 PACK F₀ (.natLit a) (.natLit b))))
        (.natLit (fl+1)))) :
    env.IsDefEqU 0 []
      (((((e₁.inst F₀ 4).inst (.natLit a) 3).inst (.natLit b) 2).inst (.natLit fl) 1).inst h)
      (((((e₂.inst F₀ 4).inst (.natLit a) 3).inst (.natLit b) 2).inst (.natLit fl) 1).inst h) := by
  have s1 : env.IsDefEqU 0
      [.natLEApp (.app .natSucc (.app MEAS (VExpr.app3 PACK F₀ (.bvar 2) (.bvar 1))))
          (.app .natSucc (.bvar 0)), .nat, .nat, .nat]
      (e₁.inst F₀ 4) (e₂.inst F₀ 4) := by
    have := IsDefEqU.instN (Γ₀ := []) (A₀ := .boolBoolBool) (e₀ := F₀) henv.ordered
      (.succ (.succ (.succ (.succ .zero)))) H hF₀
    simpa [VExpr.bitwiseCtx, VExpr.app3, VExpr.inst, VExpr.instVar, VExpr.natLEApp, VExpr.natLE,
      hMEASc.liftN_eq (Nat.zero_le _), hPACKc.liftN_eq (Nat.zero_le _),
      hMEASc.instN_eq (Nat.zero_le _), hPACKc.instN_eq (Nat.zero_le _),
      hF₀c.liftN_eq (Nat.zero_le _)] using this
  have s2 : env.IsDefEqU 0
      [.natLEApp (.app .natSucc (.app MEAS (VExpr.app3 PACK F₀ (.natLit a) (.bvar 1))))
          (.app .natSucc (.bvar 0)), .nat, .nat]
      ((e₁.inst F₀ 4).inst (.natLit a) 3) ((e₂.inst F₀ 4).inst (.natLit a) 3) := by
    have := IsDefEqU.instN (Γ₀ := []) (A₀ := .nat) (e₀ := .natLit a) henv.ordered
      (.succ (.succ (.succ .zero))) s1 (hlit a)
    simpa [VExpr.app3, VExpr.inst, VExpr.instVar, VExpr.natLEApp, VExpr.natLE,
      hMEASc.liftN_eq (Nat.zero_le _), hPACKc.liftN_eq (Nat.zero_le _),
      hMEASc.instN_eq (Nat.zero_le _), hPACKc.instN_eq (Nat.zero_le _),
      hF₀c.liftN_eq (Nat.zero_le _), hF₀c.instN_eq (Nat.zero_le _),
      (VExpr.closedN_natLit a).liftN_eq (Nat.zero_le _)] using this
  have s3 : env.IsDefEqU 0
      [.natLEApp (.app .natSucc (.app MEAS (VExpr.app3 PACK F₀ (.natLit a) (.natLit b))))
          (.app .natSucc (.bvar 0)), .nat]
      (((e₁.inst F₀ 4).inst (.natLit a) 3).inst (.natLit b) 2)
      (((e₂.inst F₀ 4).inst (.natLit a) 3).inst (.natLit b) 2) := by
    have := IsDefEqU.instN (Γ₀ := []) (A₀ := .nat) (e₀ := .natLit b) henv.ordered
      (.succ (.succ .zero)) s2 (hlit b)
    simpa [VExpr.app3, VExpr.inst, VExpr.instVar, VExpr.natLEApp, VExpr.natLE,
      hMEASc.liftN_eq (Nat.zero_le _), hPACKc.liftN_eq (Nat.zero_le _),
      hMEASc.instN_eq (Nat.zero_le _), hPACKc.instN_eq (Nat.zero_le _),
      hF₀c.liftN_eq (Nat.zero_le _), hF₀c.instN_eq (Nat.zero_le _),
      (VExpr.closedN_natLit a).liftN_eq (Nat.zero_le _),
      (VExpr.closedN_natLit b).liftN_eq (Nat.zero_le _)] using this
  have s4 : env.IsDefEqU 0
      [.natLEApp (.app .natSucc (.app MEAS (VExpr.app3 PACK F₀ (.natLit a) (.natLit b))))
          (.natLit (fl+1))]
      ((((e₁.inst F₀ 4).inst (.natLit a) 3).inst (.natLit b) 2).inst (.natLit fl) 1)
      ((((e₂.inst F₀ 4).inst (.natLit a) 3).inst (.natLit b) 2).inst (.natLit fl) 1) := by
    have := IsDefEqU.instN (Γ₀ := []) (A₀ := .nat) (e₀ := .natLit fl) henv.ordered
      (.succ .zero) s3 (hlit fl)
    simpa [VExpr.app3, VExpr.inst, VExpr.instVar, VExpr.natLEApp, VExpr.natLE, VExpr.natLit_succ,
      hMEASc.liftN_eq (Nat.zero_le _), hPACKc.liftN_eq (Nat.zero_le _),
      hMEASc.instN_eq (Nat.zero_le _), hPACKc.instN_eq (Nat.zero_le _),
      hF₀c.liftN_eq (Nat.zero_le _), hF₀c.instN_eq (Nat.zero_le _),
      (VExpr.closedN_natLit a).liftN_eq (Nat.zero_le _),
      (VExpr.closedN_natLit b).liftN_eq (Nat.zero_le _),
      (VExpr.closedN_natLit fl).liftN_eq (Nat.zero_le _)] using this
  exact IsDefEqU.instN (Γ₀ := []) (e₀ := h) henv.ordered .zero s4 hh

end VEnv

namespace VEnv
variable {env : VEnv}

set_option maxHeartbeats 1000000 in
/-- **The `Nat.bitwise` fuel recurrence at a pair of numerals and a combinator.** -/
theorem bitwise_step (henv : env.WF) (hlit : env.NatLits)
    {In Ib Pe De Pb Db GOABS PACK MEAS EA K F₀ : VExpr}
    (hgoeq : env.IsDefEqU 0 (VExpr.bitwiseCtx MEAS PACK)
      (VExpr.app3 (.app GOABS (.bvar 4)) (.app .natSucc (.bvar 1))
        (VExpr.app3 PACK (.bvar 4) (.bvar 3) (.bvar 2)) (.bvar 0))
      (VExpr.condApp .diteNat (VExpr.app2' Pe (.bvar 3) (.natLit 0))
          (VExpr.app2' De (.bvar 3) (.natLit 0))
        (.lam (VExpr.app2' Pe (.bvar 3) (.natLit 0))
          (VExpr.bitSel In Pb Db (VExpr.app2' (.bvar 5) .boolFalse .boolTrue)
            (.bvar 3) (.natLit 0)))
        (.lam EA
          (VExpr.condApp In (VExpr.app2' Pe (.bvar 3) (.natLit 0))
              (VExpr.app2' De (.bvar 3) (.natLit 0))
            (VExpr.bitSel In Pb Db (VExpr.app2' (.bvar 5) .boolTrue .boolFalse)
              (.bvar 4) (.natLit 0))
            (VExpr.bitSel In Pb Db
              (VExpr.app2' (.bvar 5) (VExpr.bitParityG Ib Pe De (.bvar 4))
                (VExpr.bitParityG Ib Pe De (.bvar 3)))
              (VExpr.natOp ``Nat.add (VExpr.natOp ``Nat.add
                (VExpr.app3 (.app GOABS (.bvar 5)) (.bvar 2)
                  (VExpr.app3 PACK (.bvar 5) (VExpr.natOp ``Nat.div (.bvar 4) (.natLit 2))
                    (VExpr.natOp ``Nat.div (.bvar 3) (.natLit 2))) K)
                (VExpr.app3 (.app GOABS (.bvar 5)) (.bvar 2)
                  (VExpr.app3 PACK (.bvar 5) (VExpr.natOp ``Nat.div (.bvar 4) (.natLit 2))
                    (VExpr.natOp ``Nat.div (.bvar 3) (.natLit 2))) K)) (.natLit 1))
              (VExpr.natOp ``Nat.add
                (VExpr.app3 (.app GOABS (.bvar 5)) (.bvar 2)
                  (VExpr.app3 PACK (.bvar 5) (VExpr.natOp ``Nat.div (.bvar 4) (.natLit 2))
                    (VExpr.natOp ``Nat.div (.bvar 3) (.natLit 2))) K)
                (VExpr.app3 (.app GOABS (.bvar 5)) (.bvar 2)
                  (VExpr.app3 PACK (.bvar 5) (VExpr.natOp ``Nat.div (.bvar 4) (.natLit 2))
                    (VExpr.natOp ``Nat.div (.bvar 3) (.natLit 2))) K)))))))
    (hMEASc : MEAS.ClosedN 0) (hPACKc : PACK.ClosedN 0) (hGOc : GOABS.ClosedN 0)
    (hInc : In.ClosedN 0) (hIbc : Ib.ClosedN 0) (hPec : Pe.ClosedN 0) (hDec : De.ClosedN 0)
    (hPbc : Pb.ClosedN 0) (hDbc : Db.ClosedN 0)
    (hF₀ : env.HasType 0 [] F₀ .boolBoolBool) (hF₀c : F₀.ClosedN 0)
    (a b fl : Nat) {h : VExpr}
    (hh : env.HasType 0 [] h
      (.natLEApp (.app .natSucc (.app MEAS (VExpr.app3 PACK F₀ (.natLit a) (.natLit b))))
        (.natLit (fl+1)))) :
    env.IsDefEqU 0 []
      (VExpr.app3 (.app GOABS F₀) (.natLit (fl+1))
        (VExpr.app3 PACK F₀ (.natLit a) (.natLit b)) h)
      (VExpr.bitwiseFuelRhs In Ib Pe De Pb Db F₀
        (((((EA.inst F₀ 4).inst (.natLit a) 3).inst (.natLit b) 2).inst (.natLit fl) 1).inst h)
        (VExpr.app3 (.app GOABS F₀) (.natLit fl)
          (VExpr.app3 PACK F₀ (VExpr.natOp ``Nat.div (.natLit a) (.natLit 2))
            (VExpr.natOp ``Nat.div (.natLit b) (.natLit 2)))
          (((((K.inst F₀ 5).inst (.natLit a) 4).inst (.natLit b) 3).inst (.natLit fl) 2).inst h 1))
        a b) := by
  have hhc : h.ClosedN 0 := VExpr.WF.closedN henv.ordered ⟨_, hh⟩ trivial
  have key := IsDefEqU.instBitwise henv hlit hMEASc hPACKc hgoeq hF₀ hF₀c a b fl hh
  simpa [VExpr.bitwiseFuelRhs, VExpr.bitwiseFuelThen, VExpr.bitwiseFuelElse, VExpr.bitSel,
    VExpr.bitParityG, VExpr.bitParity, VExpr.condApp, VExpr.app3, VExpr.app2', VExpr.natOp,
    VExpr.inst, VExpr.instVar, VExpr.lift, VExpr.liftN, Lean4Lean.liftVar, VExpr.natLit_succ,
    VExpr.boolTrue, VExpr.boolFalse, VExpr.diteNat,
    hhc.liftN_eq (Nat.zero_le _), hhc.instN_eq (Nat.zero_le _),
    hGOc.liftN_eq (Nat.zero_le _), hGOc.instN_eq (Nat.zero_le _),
    hPACKc.liftN_eq (Nat.zero_le _), hPACKc.instN_eq (Nat.zero_le _),
    hInc.liftN_eq (Nat.zero_le _), hInc.instN_eq (Nat.zero_le _),
    hIbc.liftN_eq (Nat.zero_le _), hIbc.instN_eq (Nat.zero_le _),
    hPec.liftN_eq (Nat.zero_le _), hPec.instN_eq (Nat.zero_le _),
    hDec.liftN_eq (Nat.zero_le _), hDec.instN_eq (Nat.zero_le _),
    hPbc.liftN_eq (Nat.zero_le _), hPbc.instN_eq (Nat.zero_le _),
    hDbc.liftN_eq (Nat.zero_le _), hDbc.instN_eq (Nat.zero_le _),
    hF₀c.liftN_eq (Nat.zero_le _), hF₀c.instN_eq (Nat.zero_le _),
    (VExpr.closedN_natLit a).liftN_eq (Nat.zero_le _),
    (VExpr.closedN_natLit a).instN_eq (Nat.zero_le _),
    (VExpr.closedN_natLit b).liftN_eq (Nat.zero_le _),
    (VExpr.closedN_natLit b).instN_eq (Nat.zero_le _),
    (VExpr.closedN_natLit fl).liftN_eq (Nat.zero_le _),
    (VExpr.closedN_natLit fl).instN_eq (Nat.zero_le _)] using key

end VEnv

namespace VEnv
variable {env : VEnv}

/-- Instantiate an equation proved under the `Nat.bitwise` branch's three outer binders. -/
theorem IsDefEqU.instBw3 (henv : env.WF) (hlit : env.NatLits) {e₁ e₂ F₀ : VExpr}
    (H : env.IsDefEqU 0 [.nat, .nat, .boolBoolBool] e₁ e₂)
    (hF₀ : env.HasType 0 [] F₀ .boolBoolBool) (a b : Nat) :
    env.IsDefEqU 0 [] (((e₁.inst F₀ 2).inst (.natLit a) 1).inst (.natLit b))
      (((e₂.inst F₀ 2).inst (.natLit a) 1).inst (.natLit b)) := by
  have s1 : env.IsDefEqU 0 [.nat, .nat] (e₁.inst F₀ 2) (e₂.inst F₀ 2) := by
    have := IsDefEqU.instN (Γ₀ := []) (A₀ := .boolBoolBool) (e₀ := F₀) henv.ordered
      (.succ (.succ .zero)) H hF₀
    simpa using this
  have s2 : env.IsDefEqU 0 [.nat] ((e₁.inst F₀ 2).inst (.natLit a) 1)
      ((e₂.inst F₀ 2).inst (.natLit a) 1) := by
    have := IsDefEqU.instN (Γ₀ := []) (A₀ := .nat) (e₀ := .natLit a) henv.ordered
      (.succ .zero) s1 (hlit a)
    simpa using this
  exact IsDefEqU.instN (Γ₀ := []) (A₀ := .nat) (e₀ := .natLit b) henv.ordered .zero s2 (hlit b)

/-- **The `Nat.bitwise` entry equation at a combinator and a pair of numerals.** -/
theorem bitwise_entry (henv : env.WF) (hlit : env.NatLits)
    {E GOABS PACK MEAS IN PB DB PRFA F₀ : VExpr}
    (hent : env.IsDefEqU 0 [.nat, .nat, .boolBoolBool]
      (VExpr.app3 E (.bvar 2) (.bvar 1) (.bvar 0))
      (VExpr.app3 (.app GOABS (.bvar 2))
        (.eagerITEAt IN PB DB MEAS (VExpr.app3 PACK (.bvar 2) (.bvar 1) (.bvar 0)))
        (VExpr.app3 PACK (.bvar 2) (.bvar 1) (.bvar 0)) PRFA))
    (hEc : E.ClosedN 0) (hGOc : GOABS.ClosedN 0) (hPACKc : PACK.ClosedN 0)
    (hMEASc : MEAS.ClosedN 0) (hINc : IN.ClosedN 0) (hPBc : PB.ClosedN 0) (hDBc : DB.ClosedN 0)
    (hF₀ : env.HasType 0 [] F₀ .boolBoolBool) (hF₀c : F₀.ClosedN 0) (a b : Nat) :
    env.IsDefEqU 0 [] (VExpr.app3 E F₀ (.natLit a) (.natLit b))
      (VExpr.app3 (.app GOABS F₀)
        (.eagerITEAt IN PB DB MEAS (VExpr.app3 PACK F₀ (.natLit a) (.natLit b)))
        (VExpr.app3 PACK F₀ (.natLit a) (.natLit b))
        (((PRFA.inst F₀ 2).inst (.natLit a) 1).inst (.natLit b))) := by
  have key := IsDefEqU.instBw3 henv hlit hent hF₀ a b
  simpa [VExpr.app3, VExpr.app2', VExpr.eagerITEAt, VExpr.eagerFuelAt, VExpr.condApp,
    VExpr.inst, VExpr.instVar,
    hEc.instN_eq (Nat.zero_le _), hGOc.instN_eq (Nat.zero_le _),
    hPACKc.instN_eq (Nat.zero_le _), hMEASc.instN_eq (Nat.zero_le _),
    hINc.instN_eq (Nat.zero_le _), hPBc.instN_eq (Nat.zero_le _), hDBc.instN_eq (Nat.zero_le _),
    hF₀c.instN_eq (Nat.zero_le _), hF₀c.liftN_eq (Nat.zero_le _),
    hEc.liftN_eq (Nat.zero_le _), hGOc.liftN_eq (Nat.zero_le _),
    hPACKc.liftN_eq (Nat.zero_le _), hMEASc.liftN_eq (Nat.zero_le _),
    hINc.liftN_eq (Nat.zero_le _), hPBc.liftN_eq (Nat.zero_le _), hDBc.liftN_eq (Nat.zero_le _),
    (VExpr.closedN_natLit a).instN_eq (Nat.zero_le _),
    (VExpr.closedN_natLit b).instN_eq (Nat.zero_le _),
    (VExpr.closedN_natLit a).liftN_eq (Nat.zero_le _),
    (VExpr.closedN_natLit b).liftN_eq (Nat.zero_le _)] using key

end VEnv

namespace VEnv
variable {env : VEnv}

set_option maxHeartbeats 1000000 in
/-- **The `Nat.bitwise` reflection, from the three equations the recognizer checks**, at one
combinator in one environment.  The branch applies this at every well-formed extension. -/
theorem reflects_bitwise_of_equations (henv : env.WF) (hlit : env.NatLits)
    (hsucc : env.HasType 0 [] .natSucc (.forallE .nat .nat))
    (hbeq2 : ∀ a b : Nat, env.IsDefEqU 0 []
      (VExpr.app2' (.const ``Nat.beq []) (.natLit a) (.natLit b)) (.boolLit (Nat.beq a b)))
    (hadd2 : ∀ a b : Nat, env.IsDefEqU 0 []
      (VExpr.natOp ``Nat.add (.natLit a) (.natLit b)) (.natLit (a + b)))
    (hdiv2 : ∀ a b : Nat, env.IsDefEqU 0 []
      (VExpr.natOp ``Nat.div (.natLit a) (.natLit b)) (.natLit (a / b)))
    (hmod2 : ∀ a b : Nat, env.IsDefEqU 0 []
      (VExpr.natOp ``Nat.mod (.natLit a) (.natLit b)) (.natLit (a % b)))
    {E GOABS PACK MEAS A D In Ib Pe De Pb Db OT OF PR EA K PRFA F₀ : VExpr}
    {g : Bool → Bool → Bool}
    (hEc : E.ClosedN 0) (hGOc : GOABS.ClosedN 0) (hPACKc : PACK.ClosedN 0)
    (hMEASc : MEAS.ClosedN 0) (hAc : A.ClosedN 0)
    (hInc : In.ClosedN 0) (hIbc : Ib.ClosedN 0) (hPec : Pe.ClosedN 0) (hDec : De.ClosedN 0)
    (hPbc : Pb.ClosedN 0) (hDbc : Db.ClosedN 0)
    (hGOty : env.HasType 0 [] GOABS (.forallE .boolBoolBool (.goTypeWF A MEAS D)))
    (hf : env.ReflectsBoolBoolBool F₀ g)
    (hcE : env.ReflectsCondApp In Pe De Nat.beq)
    (hcEb : env.ReflectsCondApp Ib Pe De Nat.beq)
    (hcB : env.ReflectsCondApp1 In Pb Db)
    (hRD : env.ReflectsCondAppD .diteNat Pe De OT OF PR Nat.beq)
    (hmeas : env.IsDefEqU 0 [.nat, .nat, .boolBoolBool]
      (.app MEAS (VExpr.app3 PACK (.bvar 2) (.bvar 1) (.bvar 0))) (.bvar 1))
    (hent : env.IsDefEqU 0 [.nat, .nat, .boolBoolBool]
      (VExpr.app3 E (.bvar 2) (.bvar 1) (.bvar 0))
      (VExpr.app3 (.app GOABS (.bvar 2))
        (.eagerITEAt In Pb Db MEAS (VExpr.app3 PACK (.bvar 2) (.bvar 1) (.bvar 0)))
        (VExpr.app3 PACK (.bvar 2) (.bvar 1) (.bvar 0)) PRFA))
    (hgoeq : env.IsDefEqU 0 (VExpr.bitwiseCtx MEAS PACK)
      (VExpr.app3 (.app GOABS (.bvar 4)) (.app .natSucc (.bvar 1))
        (VExpr.app3 PACK (.bvar 4) (.bvar 3) (.bvar 2)) (.bvar 0))
      (VExpr.condApp .diteNat (VExpr.app2' Pe (.bvar 3) (.natLit 0))
          (VExpr.app2' De (.bvar 3) (.natLit 0))
        (.lam (VExpr.app2' Pe (.bvar 3) (.natLit 0))
          (VExpr.bitSel In Pb Db (VExpr.app2' (.bvar 5) .boolFalse .boolTrue)
            (.bvar 3) (.natLit 0)))
        (.lam EA
          (VExpr.condApp In (VExpr.app2' Pe (.bvar 3) (.natLit 0))
              (VExpr.app2' De (.bvar 3) (.natLit 0))
            (VExpr.bitSel In Pb Db (VExpr.app2' (.bvar 5) .boolTrue .boolFalse)
              (.bvar 4) (.natLit 0))
            (VExpr.bitSel In Pb Db
              (VExpr.app2' (.bvar 5) (VExpr.bitParityG Ib Pe De (.bvar 4))
                (VExpr.bitParityG Ib Pe De (.bvar 3)))
              (VExpr.natOp ``Nat.add (VExpr.natOp ``Nat.add
                (VExpr.app3 (.app GOABS (.bvar 5)) (.bvar 2)
                  (VExpr.app3 PACK (.bvar 5) (VExpr.natOp ``Nat.div (.bvar 4) (.natLit 2))
                    (VExpr.natOp ``Nat.div (.bvar 3) (.natLit 2))) K)
                (VExpr.app3 (.app GOABS (.bvar 5)) (.bvar 2)
                  (VExpr.app3 PACK (.bvar 5) (VExpr.natOp ``Nat.div (.bvar 4) (.natLit 2))
                    (VExpr.natOp ``Nat.div (.bvar 3) (.natLit 2))) K)) (.natLit 1))
              (VExpr.natOp ``Nat.add
                (VExpr.app3 (.app GOABS (.bvar 5)) (.bvar 2)
                  (VExpr.app3 PACK (.bvar 5) (VExpr.natOp ``Nat.div (.bvar 4) (.natLit 2))
                    (VExpr.natOp ``Nat.div (.bvar 3) (.natLit 2))) K)
                (VExpr.app3 (.app GOABS (.bvar 5)) (.bvar 2)
                  (VExpr.app3 PACK (.bvar 5) (VExpr.natOp ``Nat.div (.bvar 4) (.natLit 2))
                    (VExpr.natOp ``Nat.div (.bvar 3) (.natLit 2))) K)))))))  :
    ∀ a b : Nat, env.IsDefEqU 0 [] (VExpr.app3 E F₀ (.natLit a) (.natLit b))
      (.natLit (Nat.bitwise g a b)) := by
  have hF₀c : F₀.ClosedN 0 := VExpr.WF.closedN henv.ordered ⟨_, hf.1⟩ trivial
  have hGOtyF : env.HasType 0 [] (.app GOABS F₀) (.goTypeWF A MEAS (D.inst F₀ 3)) := by
    have := hGOty.app hf.1
    simpa [VExpr.goTypeWF, VExpr.inst, VExpr.instVar, VExpr.natLEApp, VExpr.natLE,
      hAc.instN_eq (Nat.zero_le _), hMEASc.instN_eq (Nat.zero_le _)] using this
  have hmeasL : ∀ a b : Nat, env.IsDefEqU 0 []
      (.app MEAS (VExpr.app3 PACK F₀ (.natLit a) (.natLit b))) (.natLit a) := by
    intro a b
    have := IsDefEqU.instBw3 henv hlit hmeas hf.1 a b
    simpa [VExpr.app3, VExpr.inst, VExpr.instVar,
      hMEASc.instN_eq (Nat.zero_le _), hPACKc.instN_eq (Nat.zero_le _),
      hF₀c.instN_eq (Nat.zero_le _), hF₀c.liftN_eq (Nat.zero_le _),
      (VExpr.closedN_natLit a).instN_eq (Nat.zero_le _),
      (VExpr.closedN_natLit a).liftN_eq (Nat.zero_le _),
      (VExpr.closedN_natLit b).instN_eq (Nat.zero_le _)] using this
  have hOk : ∀ (fl a b : Nat) (w : VExpr),
      VExpr.WF env 0 [] (VExpr.app3 (.app GOABS F₀) (.natLit fl)
        (VExpr.app3 PACK F₀ (.natLit a) (.natLit b)) w) →
      env.HasType 0 [] w
        (.natLEApp (.app .natSucc (.app MEAS (VExpr.app3 PACK F₀ (.natLit a) (.natLit b))))
          (.natLit fl)) := fun _ _ _ _ hwt =>
    (goAppWF_typed henv hAc hMEASc hGOtyF hwt).2.2
  have _unused := hlit
  have hfuel := reflects_fuel_bitwise (GO := .app GOABS F₀) (PACK := PACK) (f := F₀)
    henv hlit hadd2 hdiv2 hmod2 hInc hIbc hPec hDec hPbc hDbc
    (VExpr.WF.closedN henv.ordered ⟨_, hGOtyF⟩ trivial) hPACKc hf hcE hcEb hcB hRD
    (Ok := fun fl a b w => env.HasType 0 [] w
      (.natLEApp (.app .natSucc (.app MEAS (VExpr.app3 PACK F₀ (.natLit a) (.natLit b))))
        (.natLit fl)))
    (fun fl a b h hok => bitwise_step henv hlit hgoeq hMEASc hPACKc hGOc hInc hIbc hPec hDec
      hPbc hDbc hf.1 hF₀c a b fl hok)
    hOk
  intro a b
  have e1 := bitwise_entry henv hlit hent hEc hGOc hPACKc hMEASc hInc hPbc hDbc hf.1 hF₀c a b
  have hwtR := e1.wf_r
  have hite := eagerITE_reduce henv hlit hsucc hbeq2 hcB (hmeasL a b)
    (((hwtR.app_fn' henv).app_fn' henv).app_arg' henv)
  have e2 := IsDefEqU.app3_congr_arg1 henv hwtR hite
  refine IsDefEqU.trans henv trivial e1 (IsDefEqU.trans henv trivial e2 ?_)
  exact hfuel (a+1) a b (Nat.lt_succ_self a) _ (hOk (a+1) a b _ e2.wf_r)

end VEnv

/-! ## Inverting the two equations the `Nat.bitwise` branch checks -/

section
open Lean hiding Environment Exception
open Kernel Lean4Lean.Environment

/-- `@ite.{1} Bool`, the head `Condition.natEq.decide` builds. -/
def VExpr.iteBool : VExpr := .app (.const ``ite [.succ .zero]) .bool

theorem trExprS_iteBool_inv' {env : VEnv} {Us Δ} {e' : VExpr}
    (h : TrExprS env Us Δ (Lean.mkApp (.const ``ite [.succ .zero]) (.const ``Bool [])) e') :
    e' = .iteBool := by
  obtain ⟨_, _, rfl, h1, h2⟩ := trExprS_app_inv' h
  cases trExprS_const_inv' h1 (us' := [.succ .zero]) rfl
  cases trExprS_const_nil_inv' h2
  rfl

theorem trExprS_two_inv' {env : VEnv} {Us Δ} {e' : VExpr}
    (h : TrExprS env Us Δ (Lean.mkApp (.const ``Nat.succ [])
      (Lean.mkApp (.const ``Nat.succ []) (.const ``Nat.zero []))) e') : e' = .natLit 2 := by
  obtain ⟨_, _, rfl, g1, g2⟩ := trExprS_app_inv' h
  cases trExprS_const_nil_inv' g1
  cases trExprS_one_inv' g2
  rfl

/-- One `Condition.bool` selection at result type `Nat`. -/
theorem trExprS_bitSel_inv' {env : VEnv} {Us} {Δ : VLCtx} {PB DB : VExpr}
    {ce te ee : Lean.Expr} {u : VExpr}
    (hpb : TrExprS env Us Δ Lean4Lean.Environment.Condition.bool.prop PB)
    (hdb : TrExprS env Us Δ Lean4Lean.Environment.Condition.bool.dec DB)
    (h : TrExprS env Us Δ
      (Lean4Lean.Environment.Condition.bool.ite (.const ``Nat []) #[ce] te ee) u)
    (hcu : TrExprS.IsUnique ce) :
    ∃ C T E, u = VExpr.bitSel .iteNat PB DB C T E ∧
      TrExprS env Us Δ ce C ∧ TrExprS env Us Δ te T ∧ TrExprS env Us Δ ee E := by
  simp only [Lean4Lean.Environment.Condition.ite, Lean.mkApp5, Lean.mkAppN, Lean.mkApp] at h
  obtain ⟨_, _, rfl, a1, aE⟩ := trExprS_app_inv' h
  obtain ⟨_, _, rfl, a2, aT⟩ := trExprS_app_inv' a1
  obtain ⟨_, _, rfl, a3, aD⟩ := trExprS_app_inv' a2
  obtain ⟨_, _, rfl, a4, aP⟩ := trExprS_app_inv' a3
  cases trExprS_iteNat_inv' a4
  obtain ⟨_, _, rfl, p1, p2⟩ := trExprS_app_inv' aP
  cases TrExprS.unique (e := Lean4Lean.Environment.Condition.bool.prop)
    (by simp [Lean4Lean.Environment.Condition.bool, TrExprS.IsUnique]) p1 hpb
  obtain ⟨_, _, rfl, d1, d2⟩ := trExprS_app_inv' aD
  cases TrExprS.unique (e := Lean4Lean.Environment.Condition.bool.dec)
    (by simp [Lean4Lean.Environment.Condition.bool, TrExprS.IsUnique]) d1 hdb
  cases TrExprS.unique hcu d2 p2
  exact ⟨_, _, _, rfl, p2, aT, aE⟩

/-- One `Condition.natEq` selection at result type `Nat`. -/
theorem trExprS_natEqIte_inv' {env : VEnv} {Us} {Δ : VLCtx}
    {xe ye te ee : Lean.Expr} {u : VExpr}
    (h : TrExprS env Us Δ
      (Lean4Lean.Environment.Condition.natEq.ite (.const ``Nat []) #[xe, ye] te ee) u)
    (hxu : TrExprS.IsUnique xe) (hyu : TrExprS.IsUnique ye) :
    ∃ X Y T E, u = VExpr.condApp .iteNat (VExpr.app2' .natEq X Y)
        (VExpr.app2' (.const ``Nat.decEq []) X Y) T E ∧
      TrExprS env Us Δ xe X ∧ TrExprS env Us Δ ye Y ∧
      TrExprS env Us Δ te T ∧ TrExprS env Us Δ ee E := by
  simp only [Lean4Lean.Environment.Condition.ite, Lean4Lean.Environment.Condition.natEq,
    Lean.mkApp5, Lean.mkAppN, Lean.mkApp] at h
  obtain ⟨_, _, rfl, a1, aE⟩ := trExprS_app_inv' h
  obtain ⟨_, _, rfl, a2, aT⟩ := trExprS_app_inv' a1
  obtain ⟨_, _, rfl, a3, aD⟩ := trExprS_app_inv' a2
  obtain ⟨_, _, rfl, a4, aP⟩ := trExprS_app_inv' a3
  cases trExprS_iteNat_inv' a4
  obtain ⟨_, _, rfl, p1, p2⟩ := trExprS_natEqApp_inv' aP
  obtain ⟨_, _, rfl, d1, d2⟩ := trExprS_app_inv' aD
  obtain ⟨_, _, rfl, d3, d4⟩ := trExprS_app_inv' d1
  cases trExprS_const_nil_inv' d3
  cases TrExprS.unique hxu d4 p1
  cases TrExprS.unique hyu d2 p2
  exact ⟨_, _, _, _, rfl, p1, p2, aT, aE⟩

/-- The parity bit `Condition.natEq.decide #[Nat.mod x 2, 1]`. -/
theorem trExprS_bitParity_inv' {env : VEnv} {Us} {Δ : VLCtx} {xe : Lean.Expr} {X u : VExpr}
    (hx : TrExprS env Us Δ xe X)
    (h : TrExprS env Us Δ
      (Lean4Lean.Environment.Condition.natEq.decide
        #[Lean.mkApp2 (.const ``Nat.mod []) xe
            (Lean.mkApp (.const ``Nat.succ []) (Lean.mkApp (.const ``Nat.succ [])
              (.const ``Nat.zero []))),
          Lean.mkApp (.const ``Nat.succ []) (.const ``Nat.zero [])]) u)
    (hxu : TrExprS.IsUnique xe) :
    u = VExpr.bitParityG .iteBool .natEq (.const ``Nat.decEq []) X := by
  simp only [Lean4Lean.Environment.Condition.decide, Lean4Lean.Environment.Condition.ite,
    Lean4Lean.Environment.Condition.natEq, Lean.mkApp5, Lean.mkApp2, Lean.mkAppN,
    Lean.mkApp] at h
  obtain ⟨_, _, rfl, a1, aE⟩ := trExprS_app_inv' h
  obtain ⟨_, _, rfl, a2, aT⟩ := trExprS_app_inv' a1
  obtain ⟨_, _, rfl, a3, aD⟩ := trExprS_app_inv' a2
  obtain ⟨_, _, rfl, a4, aP⟩ := trExprS_app_inv' a3
  cases trExprS_iteBool_inv' a4
  cases trExprS_const_nil_inv' aT
  cases trExprS_const_nil_inv' aE
  obtain ⟨_, _, rfl, p1, p2⟩ := trExprS_natEqApp_inv' aP
  obtain ⟨_, _, rfl, q1, q2⟩ := trExprS_app_inv' p1
  obtain ⟨_, _, rfl, q3, q4⟩ := trExprS_app_inv' q1
  cases trExprS_const_nil_inv' q3
  cases TrExprS.unique hxu q4 hx
  cases trExprS_two_inv' q2
  cases trExprS_one_inv' p2
  obtain ⟨_, _, rfl, d1, d2⟩ := trExprS_app_inv' aD
  obtain ⟨_, _, rfl, d3, d4⟩ := trExprS_app_inv' d1
  cases trExprS_const_nil_inv' d3
  obtain ⟨_, _, rfl, e1, e2⟩ := trExprS_app_inv' d4
  obtain ⟨_, _, rfl, e3, e4⟩ := trExprS_app_inv' e1
  cases trExprS_const_nil_inv' e3
  cases TrExprS.unique hxu e4 hx
  cases trExprS_two_inv' e2
  cases trExprS_one_inv' d2
  rfl

/-- **The `Nat.bitwise` entry equation's right-hand side.** -/
theorem trExprS_bitwiseEntry_inv' {env : VEnv} {Us} {Δ : VLCtx}
    {go pack meas prfA : Lean.Expr} {idf idn idm : FVarId}
    {GOABS PACK MEAS PB DB F N M e' : VExpr}
    (hgo : TrExprS env Us Δ go GOABS) (hgou : TrExprS.IsUnique go)
    (hpack : TrExprS env Us Δ pack PACK) (hpacku : TrExprS.IsUnique pack)
    (hmeas : TrExprS env Us Δ meas MEAS) (hmeasu : TrExprS.IsUnique meas)
    (hpb : TrExprS env Us Δ Lean4Lean.Environment.Condition.bool.prop PB)
    (hdb : TrExprS env Us Δ Lean4Lean.Environment.Condition.bool.dec DB)
    (hf : TrExprS env Us Δ (.fvar idf) F) (hn : TrExprS env Us Δ (.fvar idn) N)
    (hm : TrExprS env Us Δ (.fvar idm) M)
    (h : TrExprS env Us Δ
      (Lean.mkApp3 (Lean.mkApp go (.fvar idf))
        (Lean4Lean.Environment.Condition.bool.ite (.const ``Nat [])
          #[Lean.mkApp2 (.const ``Nat.beq [])
              (Lean.mkApp (.const ``Nat.succ []) (Lean.mkApp meas
                (Lean.mkApp3 pack (.fvar idf) (.fvar idn) (.fvar idm))))
              (Lean.mkApp (.const ``Nat.succ []) (Lean.mkApp meas
                (Lean.mkApp3 pack (.fvar idf) (.fvar idn) (.fvar idm))))]
          (Lean.mkApp (.const ``Nat.succ []) (Lean.mkApp meas
            (Lean.mkApp3 pack (.fvar idf) (.fvar idn) (.fvar idm))))
          (Lean.mkApp (.const ``Nat.succ []) (Lean.mkApp meas
            (Lean.mkApp3 pack (.fvar idf) (.fvar idn) (.fvar idm)))))
        (Lean.mkApp3 pack (.fvar idf) (.fvar idn) (.fvar idm))
        (Lean.mkApp3 prfA (.fvar idf) (.fvar idn) (.fvar idm))) e') :
    ∃ PRFA, e' = VExpr.app3 (.app GOABS F)
      (.eagerITEAt .iteNat PB DB MEAS (VExpr.app3 PACK F N M))
      (VExpr.app3 PACK F N M) PRFA := by
  have hpk : ∀ {u : VExpr},
      TrExprS env Us Δ (Lean.mkApp3 pack (.fvar idf) (.fvar idn) (.fvar idm)) u →
      u = VExpr.app3 PACK F N M := by
    intro u hu
    obtain ⟨_, _, rfl, p1, p2⟩ := trExprS_app_inv' hu
    obtain ⟨_, _, rfl, p3, p4⟩ := trExprS_app_inv' p1
    obtain ⟨_, _, rfl, p5, p6⟩ := trExprS_app_inv' p3
    cases TrExprS.unique hpacku p5 hpack
    cases trExprS_fvar_uniq p6 hf
    cases trExprS_fvar_uniq p4 hn
    cases trExprS_fvar_uniq p2 hm
    rfl
  have hX : ∀ {u : VExpr},
      TrExprS env Us Δ (Lean.mkApp (.const ``Nat.succ [])
        (Lean.mkApp meas (Lean.mkApp3 pack (.fvar idf) (.fvar idn) (.fvar idm)))) u →
      u = .eagerFuelAt MEAS (VExpr.app3 PACK F N M) := by
    intro u hu
    obtain ⟨_, _, rfl, s1, s2⟩ := trExprS_app_inv' hu
    cases trExprS_const_nil_inv' s1
    obtain ⟨_, _, rfl, s3, s4⟩ := trExprS_app_inv' s2
    cases TrExprS.unique hmeasu s3 hmeas
    cases hpk s4
    rfl
  simp only [Lean4Lean.Environment.Condition.ite, Lean4Lean.Environment.Condition.bool,
    Lean.mkApp5, Lean.mkApp3, Lean.mkApp2, Lean.mkApp, Lean.mkAppN] at h
  obtain ⟨_, _, rfl, a1, aPr⟩ := trExprS_app_inv' h
  obtain ⟨_, _, rfl, a2, aPk⟩ := trExprS_app_inv' a1
  obtain ⟨_, _, rfl, a3, aIte⟩ := trExprS_app_inv' a2
  obtain ⟨_, _, rfl, a5, a6⟩ := trExprS_app_inv' a3
  cases TrExprS.unique hgou a5 hgo
  cases trExprS_fvar_uniq a6 hf
  cases hpk aPk
  obtain ⟨_, _, rfl, b1, bE⟩ := trExprS_app_inv' aIte
  obtain ⟨_, _, rfl, b2, bT⟩ := trExprS_app_inv' b1
  obtain ⟨_, _, rfl, b3, bD⟩ := trExprS_app_inv' b2
  obtain ⟨_, _, rfl, b4, bP⟩ := trExprS_app_inv' b3
  cases trExprS_iteNat_inv' b4
  cases hX bE
  cases hX bT
  obtain ⟨_, _, rfl, p1, p2⟩ := trExprS_app_inv' bP
  cases TrExprS.unique (e := Lean4Lean.Environment.Condition.bool.prop)
    (by simp [Lean4Lean.Environment.Condition.bool, TrExprS.IsUnique]) p1 hpb
  obtain ⟨_, _, rfl, q1, q2⟩ := trExprS_app_inv' p2
  obtain ⟨_, _, rfl, q3, q4⟩ := trExprS_app_inv' q1
  cases trExprS_const_nil_inv' q3
  cases hX q4
  cases hX q2
  obtain ⟨_, _, rfl, d1, d2⟩ := trExprS_app_inv' bD
  cases TrExprS.unique (e := Lean4Lean.Environment.Condition.bool.dec)
    (by simp [Lean4Lean.Environment.Condition.bool, TrExprS.IsUnique]) d1 hdb
  obtain ⟨_, _, rfl, e1, e2⟩ := trExprS_app_inv' d2
  obtain ⟨_, _, rfl, e3, e4⟩ := trExprS_app_inv' e1
  cases trExprS_const_nil_inv' e3
  cases hX e4
  cases hX e2
  exact ⟨_, rfl⟩

set_option maxHeartbeats 2000000 in
/-- **The `Nat.bitwise` fuel recurrence's right-hand side.** -/
theorem trExprS_bitwiseGo_inv' {env : VEnv} {Us} {Δ : VLCtx}
    {go pack prf : Lean.Expr} {idf idn idm idfu : FVarId}
    {GOABS PACK PB DB F N M FU e' : VExpr} (henv : env.Ordered)
    (hgo : TrExprS env Us Δ go GOABS) (hgou : TrExprS.IsUnique go)
    (hgob : go.looseBVarRange' = 0) (hGOc : GOABS.ClosedN 0)
    (hpack : TrExprS env Us Δ pack PACK) (hpacku : TrExprS.IsUnique pack)
    (hpackb : pack.looseBVarRange' = 0) (hPACKc : PACK.ClosedN 0)
    (hpb : TrExprS env Us Δ Lean4Lean.Environment.Condition.bool.prop PB) (hPBc : PB.ClosedN 0)
    (hdb : TrExprS env Us Δ Lean4Lean.Environment.Condition.bool.dec DB) (hDBc : DB.ClosedN 0)
    (hprfu : TrExprS.IsUnique prf)
    (hf : TrExprS env Us Δ (.fvar idf) F) (hn : TrExprS env Us Δ (.fvar idn) N)
    (hm : TrExprS env Us Δ (.fvar idm) M) (hfu : TrExprS env Us Δ (.fvar idfu) FU)
    (h : TrExprS env Us Δ
      (Lean4Lean.Environment.Condition.natEq.dite #[.fvar idn, .const ``Nat.zero []]
        (Lean4Lean.Environment.Condition.bool.ite (.const ``Nat [])
          #[Lean.mkApp2 (.fvar idf) (.const ``Bool.false []) (.const ``Bool.true [])]
          (.fvar idm) (.const ``Nat.zero []))
        (Lean4Lean.Environment.Condition.natEq.ite (.const ``Nat [])
          #[.fvar idm, .const ``Nat.zero []]
          (Lean4Lean.Environment.Condition.bool.ite (.const ``Nat [])
            #[Lean.mkApp2 (.fvar idf) (.const ``Bool.true []) (.const ``Bool.false [])]
            (.fvar idn) (.const ``Nat.zero []))
          (Lean4Lean.Environment.Condition.bool.ite (.const ``Nat [])
            #[Lean.mkApp2 (.fvar idf)
              (Lean4Lean.Environment.Condition.natEq.decide
                #[Lean.mkApp2 (.const ``Nat.mod []) (.fvar idn)
                    (Lean.mkApp (.const ``Nat.succ [])
                      (Lean.mkApp (.const ``Nat.succ []) (.const ``Nat.zero []))),
                  Lean.mkApp (.const ``Nat.succ []) (.const ``Nat.zero [])])
              (Lean4Lean.Environment.Condition.natEq.decide
                #[Lean.mkApp2 (.const ``Nat.mod []) (.fvar idm)
                    (Lean.mkApp (.const ``Nat.succ [])
                      (Lean.mkApp (.const ``Nat.succ []) (.const ``Nat.zero []))),
                  Lean.mkApp (.const ``Nat.succ []) (.const ``Nat.zero [])])]
            (Lean.mkApp2 (.const ``Nat.add [])
              (Lean.mkApp2 (.const ``Nat.add [])
                (Lean.mkApp3 (Lean.mkApp go (.fvar idf)) (.fvar idfu)
                  (Lean.mkApp3 pack (.fvar idf)
                    (Lean.mkApp2 (.const ``Nat.div []) (.fvar idn)
                      (Lean.mkApp (.const ``Nat.succ [])
                        (Lean.mkApp (.const ``Nat.succ []) (.const ``Nat.zero []))))
                    (Lean.mkApp2 (.const ``Nat.div []) (.fvar idm)
                      (Lean.mkApp (.const ``Nat.succ [])
                        (Lean.mkApp (.const ``Nat.succ []) (.const ``Nat.zero []))))) prf)
                (Lean.mkApp3 (Lean.mkApp go (.fvar idf)) (.fvar idfu)
                  (Lean.mkApp3 pack (.fvar idf)
                    (Lean.mkApp2 (.const ``Nat.div []) (.fvar idn)
                      (Lean.mkApp (.const ``Nat.succ [])
                        (Lean.mkApp (.const ``Nat.succ []) (.const ``Nat.zero []))))
                    (Lean.mkApp2 (.const ``Nat.div []) (.fvar idm)
                      (Lean.mkApp (.const ``Nat.succ [])
                        (Lean.mkApp (.const ``Nat.succ []) (.const ``Nat.zero []))))) prf))
              (Lean.mkApp (.const ``Nat.succ []) (.const ``Nat.zero [])))
            (Lean.mkApp2 (.const ``Nat.add [])
              (Lean.mkApp3 (Lean.mkApp go (.fvar idf)) (.fvar idfu)
                (Lean.mkApp3 pack (.fvar idf)
                  (Lean.mkApp2 (.const ``Nat.div []) (.fvar idn)
                    (Lean.mkApp (.const ``Nat.succ [])
                      (Lean.mkApp (.const ``Nat.succ []) (.const ``Nat.zero []))))
                  (Lean.mkApp2 (.const ``Nat.div []) (.fvar idm)
                    (Lean.mkApp (.const ``Nat.succ [])
                      (Lean.mkApp (.const ``Nat.succ []) (.const ``Nat.zero []))))) prf)
              (Lean.mkApp3 (Lean.mkApp go (.fvar idf)) (.fvar idfu)
                (Lean.mkApp3 pack (.fvar idf)
                  (Lean.mkApp2 (.const ``Nat.div []) (.fvar idn)
                    (Lean.mkApp (.const ``Nat.succ [])
                      (Lean.mkApp (.const ``Nat.succ []) (.const ``Nat.zero []))))
                  (Lean.mkApp2 (.const ``Nat.div []) (.fvar idm)
                    (Lean.mkApp (.const ``Nat.succ [])
                      (Lean.mkApp (.const ``Nat.succ []) (.const ``Nat.zero []))))) prf))))) e') :
    ∃ EA K, e' = VExpr.condApp .diteNat (VExpr.app2' .natEq N (.natLit 0))
        (VExpr.app2' (.const ``Nat.decEq []) N (.natLit 0))
      (.lam (VExpr.app2' .natEq N (.natLit 0))
        (VExpr.bitSel .iteNat PB DB (VExpr.app2' F.lift .boolFalse .boolTrue)
          M.lift (.natLit 0)))
      (.lam EA
        (VExpr.condApp .iteNat (VExpr.app2' .natEq M.lift (.natLit 0))
            (VExpr.app2' (.const ``Nat.decEq []) M.lift (.natLit 0))
          (VExpr.bitSel .iteNat PB DB (VExpr.app2' F.lift .boolTrue .boolFalse)
            N.lift (.natLit 0))
          (VExpr.bitSel .iteNat PB DB
            (VExpr.app2' F.lift
              (VExpr.bitParityG .iteBool .natEq (.const ``Nat.decEq []) N.lift)
              (VExpr.bitParityG .iteBool .natEq (.const ``Nat.decEq []) M.lift))
            (VExpr.natOp ``Nat.add (VExpr.natOp ``Nat.add
              (VExpr.app3 (.app GOABS F.lift) FU.lift
                (VExpr.app3 PACK F.lift (VExpr.natOp ``Nat.div N.lift (.natLit 2))
                  (VExpr.natOp ``Nat.div M.lift (.natLit 2))) K)
              (VExpr.app3 (.app GOABS F.lift) FU.lift
                (VExpr.app3 PACK F.lift (VExpr.natOp ``Nat.div N.lift (.natLit 2))
                  (VExpr.natOp ``Nat.div M.lift (.natLit 2))) K)) (.natLit 1))
            (VExpr.natOp ``Nat.add
              (VExpr.app3 (.app GOABS F.lift) FU.lift
                (VExpr.app3 PACK F.lift (VExpr.natOp ``Nat.div N.lift (.natLit 2))
                  (VExpr.natOp ``Nat.div M.lift (.natLit 2))) K)
              (VExpr.app3 (.app GOABS F.lift) FU.lift
                (VExpr.app3 PACK F.lift (VExpr.natOp ``Nat.div N.lift (.natLit 2))
                  (VExpr.natOp ``Nat.div M.lift (.natLit 2))) K))))) := by
  simp only [Lean4Lean.Environment.Condition.dite, Lean4Lean.Environment.Condition.natEq,
    Lean.Expr.lam0, Lean.mkApp4, Lean.mkApp3, Lean.mkApp2, Lean.mkAppN] at h
  obtain ⟨_, _, rfl, b1, bE⟩ := trExprS_app_inv' h
  obtain ⟨_, _, rfl, b2, bT⟩ := trExprS_app_inv' b1
  obtain ⟨_, _, rfl, b3, bD⟩ := trExprS_app_inv' b2
  obtain ⟨_, _, rfl, b4, bP⟩ := trExprS_app_inv' b3
  cases trExprS_diteNat_inv' b4
  obtain ⟨_, _, rfl, q1, q2⟩ := trExprS_natEqApp_inv' bP
  cases trExprS_fvar_uniq q1 hn
  cases trExprS_const_nil_inv' q2
  obtain ⟨_, _, rfl, e1, e2⟩ := trExprS_app_inv' bD
  obtain ⟨_, _, rfl, e3, e4⟩ := trExprS_app_inv' e1
  cases trExprS_const_nil_inv' e3
  cases trExprS_fvar_uniq e4 hn
  cases trExprS_const_nil_inv' e2
  -- the `n = 0` branch
  obtain ⟨_, _, rfl, t1, t2⟩ := trExprS_lam_inv' bT
  obtain ⟨_, _, rfl, u1, u2⟩ := trExprS_natEqApp_inv' t1
  cases trExprS_fvar_uniq u1 hn
  cases trExprS_const_nil_inv' u2
  obtain ⟨C1, T1, E1, rfl, hc1, ht1, he1⟩ :=
    trExprS_bitSel_inv'
      (trExprS_weakBV0 henv hpb (by simp [Lean4Lean.Environment.Condition.bool,
        Lean.Expr.looseBVarRange']) hPBc)
      (trExprS_weakBV0 henv hdb (by simp [Lean4Lean.Environment.Condition.bool,
        Lean.Expr.looseBVarRange']) hDBc) t2
      (by repeat' first | exact trivial | refine ⟨?_, ?_⟩)
  obtain ⟨_, _, rfl, c1, c2⟩ := trExprS_app_inv' hc1
  obtain ⟨_, _, rfl, c3, c4⟩ := trExprS_app_inv' c1
  cases trExprS_fvar_uniq c3 (trExprS_liftBV0 henv hf rfl)
  cases trExprS_const_nil_inv' c4
  cases trExprS_const_nil_inv' c2
  cases trExprS_fvar_uniq ht1 (trExprS_liftBV0 henv hm rfl)
  cases trExprS_const_nil_inv' he1
  -- the `n ≠ 0` branch
  obtain ⟨EAd, _, rfl, z1, z2⟩ := trExprS_lam_inv' bE
  have hf' := trExprS_liftBV0 (A := EAd) henv hf rfl
  have hn' := trExprS_liftBV0 (A := EAd) henv hn rfl
  have hm' := trExprS_liftBV0 (A := EAd) henv hm rfl
  have hfu' := trExprS_liftBV0 (A := EAd) henv hfu rfl
  have hgo' := trExprS_weakBV0 (A := EAd) henv hgo hgob hGOc
  have hpack' := trExprS_weakBV0 (A := EAd) henv hpack hpackb hPACKc
  have hpb' := trExprS_weakBV0 (A := EAd) henv hpb
    (by simp [Lean4Lean.Environment.Condition.bool, Lean.Expr.looseBVarRange']) hPBc
  have hdb' := trExprS_weakBV0 (A := EAd) henv hdb
    (by simp [Lean4Lean.Environment.Condition.bool, Lean.Expr.looseBVarRange']) hDBc
  obtain ⟨X2, Y2, T2, E2, rfl, hx2, hy2, ht2, he2⟩ :=
    trExprS_natEqIte_inv' z2 (by repeat' first | exact trivial | refine ⟨?_, ?_⟩) (by repeat' first | exact trivial | refine ⟨?_, ?_⟩)
  cases trExprS_fvar_uniq hx2 hm'
  cases trExprS_const_nil_inv' hy2
  obtain ⟨C3, T3, E3, rfl, hc3, ht3, he3⟩ := trExprS_bitSel_inv' hpb' hdb' ht2 (by repeat' first | exact trivial | refine ⟨?_, ?_⟩)
  obtain ⟨_, _, rfl, g1, g2⟩ := trExprS_app_inv' hc3
  obtain ⟨_, _, rfl, g3, g4⟩ := trExprS_app_inv' g1
  cases trExprS_fvar_uniq g3 hf'
  cases trExprS_const_nil_inv' g4
  cases trExprS_const_nil_inv' g2
  cases trExprS_fvar_uniq ht3 hn'
  cases trExprS_const_nil_inv' he3
  obtain ⟨C4, T4, E4, rfl, hc4, ht4, he4⟩ :=
    trExprS_bitSel_inv' hpb' hdb' he2 (by repeat' first | exact trivial | refine ⟨?_, ?_⟩)
  obtain ⟨_, _, rfl, k1, k2⟩ := trExprS_app_inv' hc4
  obtain ⟨_, _, rfl, k3, k4⟩ := trExprS_app_inv' k1
  cases trExprS_fvar_uniq k3 hf'
  cases trExprS_bitParity_inv' hn' k4 (by repeat' first | exact trivial | refine ⟨?_, ?_⟩)
  cases trExprS_bitParity_inv' hm' k2 (by repeat' first | exact trivial | refine ⟨?_, ?_⟩)
  -- the recursive call
  have hrec : ∀ {u : VExpr},
      TrExprS env Us ((none, .vlam EAd) :: Δ)
        (Lean.mkApp3 (Lean.mkApp go (.fvar idf)) (.fvar idfu)
          (Lean.mkApp3 pack (.fvar idf)
            (Lean.mkApp2 (.const ``Nat.div []) (.fvar idn)
              (Lean.mkApp (.const ``Nat.succ [])
                (Lean.mkApp (.const ``Nat.succ []) (.const ``Nat.zero []))))
            (Lean.mkApp2 (.const ``Nat.div []) (.fvar idm)
              (Lean.mkApp (.const ``Nat.succ [])
                (Lean.mkApp (.const ``Nat.succ []) (.const ``Nat.zero []))))) prf) u →
      ∃ K, u = VExpr.app3 (.app GOABS F.lift) FU.lift
        (VExpr.app3 PACK F.lift (VExpr.natOp ``Nat.div N.lift (.natLit 2))
          (VExpr.natOp ``Nat.div M.lift (.natLit 2))) K := by
    intro u hu
    obtain ⟨_, _, rfl, r1, r2⟩ := trExprS_app_inv' hu
    obtain ⟨_, _, rfl, r3, r4⟩ := trExprS_app_inv' r1
    obtain ⟨_, _, rfl, r5, r6⟩ := trExprS_app_inv' r3
    obtain ⟨_, _, rfl, r7, r8⟩ := trExprS_app_inv' r5
    cases TrExprS.unique hgou r7 hgo'
    cases trExprS_fvar_uniq r8 hf'
    cases trExprS_fvar_uniq r6 hfu'
    obtain ⟨_, _, rfl, s1, s2⟩ := trExprS_app_inv' r4
    obtain ⟨_, _, rfl, s3, s4⟩ := trExprS_app_inv' s1
    obtain ⟨_, _, rfl, s5, s6⟩ := trExprS_app_inv' s3
    cases TrExprS.unique hpacku s5 hpack'
    cases trExprS_fvar_uniq s6 hf'
    obtain ⟨_, _, rfl, v1, v2⟩ := trExprS_app_inv' s4
    obtain ⟨_, _, rfl, v3, v4⟩ := trExprS_app_inv' v1
    cases trExprS_const_nil_inv' v3
    cases trExprS_fvar_uniq v4 hn'
    cases trExprS_two_inv' v2
    obtain ⟨_, _, rfl, w1, w2⟩ := trExprS_app_inv' s2
    obtain ⟨_, _, rfl, w3, w4⟩ := trExprS_app_inv' w1
    cases trExprS_const_nil_inv' w3
    cases trExprS_fvar_uniq w4 hm'
    cases trExprS_two_inv' w2
    exact ⟨_, rfl⟩
  have huniq : TrExprS.IsUnique (Lean.mkApp3 (Lean.mkApp go (.fvar idf)) (.fvar idfu)
      (Lean.mkApp3 pack (.fvar idf)
        (Lean.mkApp2 (.const ``Nat.div []) (.fvar idn)
          (Lean.mkApp (.const ``Nat.succ [])
            (Lean.mkApp (.const ``Nat.succ []) (.const ``Nat.zero []))))
        (Lean.mkApp2 (.const ``Nat.div []) (.fvar idm)
          (Lean.mkApp (.const ``Nat.succ [])
            (Lean.mkApp (.const ``Nat.succ []) (.const ``Nat.zero []))))) prf) := by
    simp only [Lean.mkApp3, Lean.mkApp2, Lean.mkApp, TrExprS.IsUnique]
    repeat' apply And.intro
    all_goals first | exact hgou | exact hpacku | exact hprfu | trivial
  obtain ⟨_, _, rfl, y1, y2⟩ := trExprS_app_inv' ht4
  obtain ⟨_, _, rfl, y3, y4⟩ := trExprS_app_inv' y1
  cases trExprS_const_nil_inv' y3
  obtain ⟨_, _, rfl, x1, x2⟩ := trExprS_app_inv' y4
  obtain ⟨_, _, rfl, x3, x4⟩ := trExprS_app_inv' x1
  cases trExprS_const_nil_inv' x3
  obtain ⟨K1, rfl⟩ := hrec x4
  obtain ⟨K2, hK2⟩ := hrec x2
  cases trExprS_one_inv' y2
  obtain ⟨_, _, rfl, z3, z4⟩ := trExprS_app_inv' he4
  obtain ⟨_, _, rfl, z5, z6⟩ := trExprS_app_inv' z3
  cases trExprS_const_nil_inv' z5
  obtain ⟨K3, hK3⟩ := hrec z6
  obtain ⟨K4, hK4⟩ := hrec z4
  cases TrExprS.unique (e := Lean.mkApp3 (Lean.mkApp go (.fvar idf)) (.fvar idfu)
    (Lean.mkApp3 pack (.fvar idf)
      (Lean.mkApp2 (.const ``Nat.div []) (.fvar idn)
        (Lean.mkApp (.const ``Nat.succ [])
          (Lean.mkApp (.const ``Nat.succ []) (.const ``Nat.zero []))))
      (Lean.mkApp2 (.const ``Nat.div []) (.fvar idm)
        (Lean.mkApp (.const ``Nat.succ [])
          (Lean.mkApp (.const ``Nat.succ []) (.const ``Nat.zero []))))) prf)
    huniq x2 x4
  cases TrExprS.unique (e := Lean.mkApp3 (Lean.mkApp go (.fvar idf)) (.fvar idfu)
    (Lean.mkApp3 pack (.fvar idf)
      (Lean.mkApp2 (.const ``Nat.div []) (.fvar idn)
        (Lean.mkApp (.const ``Nat.succ [])
          (Lean.mkApp (.const ``Nat.succ []) (.const ``Nat.zero []))))
      (Lean.mkApp2 (.const ``Nat.div []) (.fvar idm)
        (Lean.mkApp (.const ``Nat.succ [])
          (Lean.mkApp (.const ``Nat.succ []) (.const ``Nat.zero []))))) prf)
    huniq z6 x4
  cases TrExprS.unique (e := Lean.mkApp3 (Lean.mkApp go (.fvar idf)) (.fvar idfu)
    (Lean.mkApp3 pack (.fvar idf)
      (Lean.mkApp2 (.const ``Nat.div []) (.fvar idn)
        (Lean.mkApp (.const ``Nat.succ [])
          (Lean.mkApp (.const ``Nat.succ []) (.const ``Nat.zero []))))
      (Lean.mkApp2 (.const ``Nat.div []) (.fvar idm)
        (Lean.mkApp (.const ``Nat.succ [])
          (Lean.mkApp (.const ``Nat.succ []) (.const ``Nat.zero []))))) prf)
    huniq z4 x4
  exact ⟨_, _, rfl⟩

end

namespace VEnv
variable {env : VEnv}

theorem IsDefEqU.wf_l {a b : VExpr} (h : env.IsDefEqU 0 [] a b) : VExpr.WF env 0 [] a :=
  h.symm.wf_r

/-- Replace the head of a three-fold application. -/
theorem IsDefEqU.app3_congr_fn (henv : env.WF) {F F' u v w : VExpr}
    (hwt : VExpr.WF env 0 [] (VExpr.app3 F u v w)) (h : env.IsDefEqU 0 [] F F') :
    env.IsDefEqU 0 [] (VExpr.app3 F u v w) (VExpr.app3 F' u v w) :=
  IsDefEqU.app_congr_fn' henv hwt
    (IsDefEqU.app_congr_fn' henv (hwt.app_fn' henv)
      (IsDefEqU.app_congr_fn' henv ((hwt.app_fn' henv).app_fn' henv) h))

end VEnv

/-- The shape the `Nat.bitwise` branch's `hrefl` obligation takes: the branch supplies the
reflection at every well-formed extension and every combinator, this transports it to the
constant.  `VEnv.ReflectsNatBitwise` is relativized, so unlike `reflectsNNN_of_open` there is
no numeral-typing step here -- the branch has already done it inside its own quantifier. -/
theorem reflectsNatBitwise_of_open {env₂ : VEnv} {E : VExpr}
    (henv₂ : env₂.WF)
    (hdefF : env₂.IsDefEqU 0 [] (.const ``Nat.bitwise []) E)
    (H : ∀ (env' : VEnv), env₂ ≤ env' → env'.WF → ∀ (F₀ : VExpr) (g : Bool → Bool → Bool),
      env'.ReflectsBoolBoolBool F₀ g → ∀ a b, env'.IsDefEqU 0 []
        (VExpr.app3 E F₀ (.natLit a) (.natLit b)) (.natLit (Nat.bitwise g a b))) :
    env₂.ReflectsNatBitwise := by
  intro _ env' hle F₀ g henv' hf a b
  have hE := H env' hle henv' F₀ g hf a b
  have hd := hdefF.mono hle
  exact VEnv.IsDefEqU.trans henv' trivial
    (VEnv.IsDefEqU.app3_congr_fn henv' (VEnv.IsDefEqU.wf_l hE) hd.symm).symm hE

section
open Lean hiding Environment Exception
open Kernel

namespace TypeChecker
variable {c : VContext}

/-- `Nat` is a type, from `VEnv.HasPrimitives` alone.  The `Nat.bitwise` branch's declared type
does not start with a `Nat` binder, so `NatFacts.of_arrow` does not apply to it. -/
theorem isType_nat (hprim : c.venv.HasPrimitives) (hn : c.venv.contains ``Nat)
    (hlp : c.lparams = []) : c.IsType .nat := by
  obtain ⟨⟨ci, h⟩, -⟩ := hprim.nat hn
  cases hprim.natZero h
  obtain ⟨u, hu⟩ := c.Ewf.ordered.constWF h
  exact ⟨u, by rw [hlp]; exact hu.weak0 c.Ewf.ordered⟩

end TypeChecker

/-- The type `Nat.bitwise` is pinned to: `(Bool → Bool → Bool) → Nat → Nat → Nat`. -/
theorem trExprS_bitwiseType_inv' {env : VEnv} {Us Δ}
    {n₁ n₂ n₃ n₄ n₅ bi₁ bi₂ bi₃ bi₄ bi₅} {e' : VExpr}
    (h : TrExprS env Us Δ
      (.forallE n₁
        (.forallE n₂ (.const ``Bool []) (.forallE n₃ (.const ``Bool []) (.const ``Bool []) bi₃)
          bi₂)
        (.forallE n₄ (.const ``Nat []) (.forallE n₅ (.const ``Nat []) (.const ``Nat []) bi₅) bi₄)
        bi₁) e') :
    e' = .forallE .boolBoolBool (.forallE .nat (.forallE .nat .nat)) := by
  obtain ⟨_, _, rfl, h1, h2⟩ := trExprS_arrow_inv' h
  obtain ⟨_, _, rfl, b1, b2⟩ := trExprS_arrow_inv' h1
  cases trExprS_const_nil_inv' b1
  obtain ⟨_, _, rfl, b3, b4⟩ := trExprS_arrow_inv' b2
  cases trExprS_const_nil_inv' b3
  cases trExprS_const_nil_inv' b4
  obtain ⟨_, _, rfl, k1, k2⟩ := trExprS_arrow_inv' h2
  cases trExprS_const_nil_inv' k1
  obtain ⟨_, _, rfl, k3, k4⟩ := trExprS_arrow_inv' k2
  cases trExprS_const_nil_inv' k3
  cases trExprS_const_nil_inv' k4
  rfl

end

section
open Lean hiding Environment Exception
open Kernel

/-- `Bool → Bool → Bool`, in the `_inv'` family's raw form. -/
theorem trExprS_boolArrow2_inv' {env : VEnv} {Us Δ} {nm₁ nm₂ bi₁ bi₂} {e' : VExpr}
    (h : TrExprS env Us Δ (.forallE nm₁ (.const ``Bool [])
      (.forallE nm₂ (.const ``Bool []) (.const ``Bool []) bi₂) bi₁) e') :
    e' = .boolBoolBool := by
  obtain ⟨_, _, rfl, h1, h3⟩ := trExprS_arrow_inv' h
  cases trExprS_const_nil_inv' h1
  obtain ⟨_, _, rfl, h4, h5⟩ := trExprS_arrow_inv' h3
  cases trExprS_const_nil_inv' h4
  cases trExprS_const_nil_inv' h5
  rfl

end

namespace TypeChecker
variable {c : VContext}

/-- The three-argument packing function applied. -/
theorem trExprS_packApp3 {PACK A FV N M : VExpr} {pk fe ne me : Lean.Expr}
    (hp : c.TrExprS pk PACK)
    (hpty : c.HasType PACK (.forallE .boolBoolBool (.forallE .nat (.forallE .nat A))))
    (hAc : A.ClosedN 0)
    (hfv : c.TrExprS fe FV) (hfty : c.HasType FV .boolBoolBool)
    (hn : c.TrExprS ne N) (hnty : c.HasType N .nat)
    (hm : c.TrExprS me M) (hmty : c.HasType M .nat) :
    c.TrExprS (Lean.mkApp3 pk fe ne me) (VExpr.app3 PACK FV N M) ∧
      c.HasType (VExpr.app3 PACK FV N M) A := by
  obtain ⟨s1, y1⟩ := trExprS_appD hp hpty hfv hfty
  simp only [VExpr.inst, VExpr.inst_nat, hAc.instN_eq (Nat.zero_le _)] at y1
  obtain ⟨s2, y2⟩ := trExprS_appD s1 y1 hn hnty
  simp only [VExpr.inst, VExpr.inst_nat, hAc.instN_eq (Nat.zero_le _)] at y2
  obtain ⟨s3, y3⟩ := trExprS_appD s2 y2 hm hmty
  simp only [hAc.instN_eq (Nat.zero_le _)] at y3
  exact ⟨s3, y3⟩

/-- `go`, applied to the combinator. -/
theorem hasType_goApply {GOABS A MEAS D FV : VExpr}
    (hAc : A.ClosedN 0) (hMEASc : MEAS.ClosedN 0)
    (hGOty : c.HasType GOABS (.forallE .boolBoolBool (.goTypeWF A MEAS D)))
    (hfty : c.HasType FV .boolBoolBool) :
    c.HasType (.app GOABS FV) (.goTypeWF A MEAS (D.inst FV 3)) := by
  have := hGOty.app hfty
  simpa [VExpr.goTypeWF, VExpr.inst, VExpr.instVar, VExpr.natLEApp, VExpr.natLE,
    hAc.instN_eq (Nat.zero_le _), hMEASc.instN_eq (Nat.zero_le _)] using this

end TypeChecker
