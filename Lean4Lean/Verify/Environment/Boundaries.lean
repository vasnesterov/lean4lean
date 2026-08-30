import Lean4Lean.Verify.TypeChecker
import Lean4Lean.Verify.Primitive
import Lean4Lean.Verify.PrimitiveWF
import Lean4Lean.Environment

/-!
This module contains the front-end-specific trust boundary for declaration verification.
The checker, extension, and declaration modules introduce no additional `sorry`-backed
assumptions. The imported type-checker and theory layers retain their own explicit
verification gaps.
-/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel TypeChecker

/-- What the primitive-definition recognizer must establish beyond ordinary type checking.
This is kept separate from declaration checking so that the remaining metatheory does not
depend on the recognizer's syntactic implementation. Primitive semantics are claimed only
in well-formed extensions of the environment in which recognition ran. -/
structure PrimitiveResult (checked : VEnv) (v : DefinitionVal) (allow : Bool) : Prop where
  safe : allow = true → v.safety = .safe
  no_level_params : allow = true → v.levelParams = []
  preserves : allow = true → ∀ {safety : DefinitionSafety} {venv env' : VEnv} {ci' : VDefVal},
    checked ≤ venv → venv.WF →
    venv.HasPrimitives →
    TrDefVal safety venv (.defnInfo v) ci' → ci'.WF venv →
    venv.addConst v.name ci'.toVConstant = some env' →
    (env'.addDefEq ci'.toDefEq).HasPrimitives

set_option maxHeartbeats 4000000 in
/-- Verification boundary for Lean4Lean's syntactic primitive-definition recognizer.

Three refutations of this statement have been closed on the implementation side
(`Lean4Lean/Primitive.lean`):

* the `Char.ofNat` and `String.ofList` branches compare `v.type` with `==` (`Expr.eqv`,
  structural up to binder names and binder info) rather than `isDefEq`, so the `VConstant`
  that `TrConstant` reads off structurally is forced to be the one `VEnv.HasPrimitives`
  demands;
* the `Nat` branches compare open terms under `withLocalDecl`-bound free variables instead of
  wrapping them in the ill-typed pseudo-type `∀ _ : Nat, e`, which had no `TrExprS` witness and
  therefore made every `isDefEq` spec vacuous; and
* the recognizer type-checks its own inputs (`checkPrimValue`, `checkIsType`, `checkedIsDefEq`,
  `checkedTypeIs`) instead of handing untyped terms to `isDefEq`. It runs before
  `checkConstantVal`, so neither `v.type` nor `v.value` had been checked, and neither had the
  other primitives the equations mention -- `VEnv.HasPrimitives` pins their behaviour at
  numerals but not their types. `isDefEq` records its verdict in the `EquivManager`, whose
  well-formedness invariant demands both sides be translatable, so an untyped comparison broke
  `TypeChecker.VState.WF` and with it this theorem's `M.WF` obligation. See `bugs-found.md`.

All nineteen branches are discharged. The two fuel-recursive ones (`Nat.mod`, `Nat.div`) go
through `VEnv.reflects_mod_of_equations` / `VEnv.reflects_div_of_equations`; the two
well-founded ones (`Nat.gcd`, `Nat.bitwise`) through
`VEnv.reflects_gcd_of_equations` / `VEnv.reflects_bitwise_of_equations` in
`Lean4Lean/Verify/PrimitiveWF.lean`; the other fifteen use the reflection theorems and the
`VEnv.PrimField` / `VEnv.HasPrimitives.addDef` plumbing in `Lean4Lean/Verify/Primitive.lean`.

Bug 4 of `bugs-found.md` -- handing untyped terms to `isDefEq`, which records its verdict in
the `EquivManager` and so breaks `VState.WF` -- had been fixed for the other fifteen branches
but not for these four. **It now is.** Every comparison these four make, directly or through
the helpers they share, type-checks both of its sides:

* `Condition.check` uses `checkedTypeIs cond.prop`, not `inferType cond.prop`. (Of the three
  `inferType` calls the previous note listed, only this one was genuinely uncovered: `asBool`
  and `proof` both occur in the term the following `checkType e` checks. The right-hand sides
  it compared against -- `Nat → Nat → Prop`, `Nat → Nat → Bool`, `Bool → Prop` -- were
  unchecked too, and now are not.)
* `Reflection.check`, `Reflection.checkITE` and `Reflection.checkNatDITE` use
  `checkedTypeIs`/`checkedIsDefEq` throughout.
* `unfoldNatWellFounded` uses `checkType` where it used `inferType`, and `checkedIsDefEq` for
  its three comparisons. `unfoldWellFounded`, listed in the previous version of this note, was
  dead code -- nothing in the tree ever called it -- and has been deleted.
* Every free variable these branches introduce is bound by `withCheckedLocalDecl`, which
  `checkIsType`s the domain first. This is a separate gap from the comparison one and was not
  previously recorded: `M.WF.withLocalDecl0` demands a `TrExprS` *and* an `IsType` for the
  binder's domain, and the domains here (`1 ≤ y`, `Nat.succ x ≤ Nat.succ fuel`,
  `r.type p Bool.true`, and the type `unfoldNatWellFounded` recovers from a `whnf`) are built
  from constants that `VEnv.HasPrimitives` requires only to be *present*. The corresponding
  spec is `TypeChecker.M.WF.withCheckedLocalDecl` in `Lean4Lean/Verify/Primitive.lean`.

The recognizer still accepts all eighteen primitives of the current prelude with those checks
in place (the `run_meta` self-test at the foot of `Lean4Lean/Primitive.lean`, and
`Verify/Soundness.lean`'s `stdPrelude accepted by addDecl`), and the Kernel Arena is unchanged
at 185 correct / 6 either / 0 incorrect.

What is left is therefore metatheory, not plumbing, and it is genuinely new: the fifteen
branches all check a *structural* recursion, for which `VEnv.reflects_rec2`,
`reflects_rec2_tail` and `reflects_rec2_diag` suffice. These four do not.

* `Nat.mod` and `Nat.div` needed a fuel induction. Their equations mention `Nat.modCore.go` /
  `Nat.div.go`, whose fuel argument the recognizer constrains only at `Nat.succ fuel`; the
  reflection runs the induction under the `Nat.succ x ≤ fuel` invariant, which is what keeps
  the unconstrained `fuel = 0` case unreachable. Both are now proved: `VEnv.reflects_fuel_mod`
  / `_div` do the induction, `VEnv.reflects_mod_of_equations` / `_div_of_equations` assemble it
  from the two equations the recognizer checks, and `docs/handoff-primitive.md` has the ledger.
* Both also needed a reflection lemma for `Condition`: the equations are stated with
  `Condition.ite`/`Condition.dite`, i.e. `@ite`/`@dite` at the instance `cond.dec`, and what
  `Condition.check` establishes about that instance (`cond.dec ≡ fun x y => r.toDec (prop x y)
  (asBool x y) (proof x y)`, together with `r.ite` selecting on `Bool.true`/`Bool.false`) has
  to be turned into "`Condition.natLE.ite α #[a, b] t e` is `t` when `a ≤ b` and `e`
  otherwise", via `VEnv.HasPrimitives.natBLE`. That is `TypeChecker.Condition.check.WF` and its
  pinned instance `Condition.check.WF_natLE_pinned`.
* `Nat.gcd` and `Nat.bitwise` go through `unfoldNatWellFounded`, and they were **false**, not
  open, until 2026-08-30: nothing constrained the *measure* `h` of `WellFounded.Nat.fix h F`,
  and that fixpoint reduces only once `h x` evaluates to a ground value -- the `Nat.eager`
  gadget in its definition exists to enforce exactly that -- so a `Nat.gcd` whose measure the
  kernel cannot evaluate was accepted while not reducing at numerals at all.
  `scripts/primitive-wf-refutation.lean` is the witness. Four further facts turned out to be
  unavailable and are now checked or derived: `go`'s own *type* (without it the recursive
  call's fuel bound has no type, `VExpr.WF.app_inv` inventing an existential domain);
  independence of `go`/`pack`/the measure from the recursion variables (the induction steps
  them to *different* arguments, so they must be the same closed terms at every level);
  `Condition.bool`'s check moved to the base context, where `Condition.check.WF_bool`'s
  `c.vlctx = []` can be met; and `VEnv.ReflectsCondAppAll`, because `ReflectsCondApp`'s
  `VExpr.WF` premise is negative and so the predicate is **not** monotone, while
  `VEnv.ReflectsNatBitwise` is relativized to an arbitrary later environment carrying the
  combinator. `docs/handoff-primitive.md` has the ledger and the traps. -/
theorem checkPrimitiveDef.WF.rest {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (fuel : FuelConfig)
    (hrest : v.name = ``Nat.mod ∨ v.name = ``Nat.div ∨ v.name = ``Nat.gcd ∨
      v.name = ``Nat.bitwise) :
    (Environment.checkPrimitiveDef v).WF (.mk' wf .safe v.levelParams fuel) {} fun allow _ =>
      PrimitiveResult (ves.venv .safe) v allow := by
  obtain ⟨⟨name, lparams, type⟩, value, hints, safety, all⟩ := v
  have hfail {α : Type} {s' : VState} {Q : α → VState → Prop} {msg} :
      M.WF (.mk' wf .safe lparams fuel) s' (throw (Exception.other msg) : M α) Q := .throw
  unfold Environment.checkPrimitiveDef
  split
  case isFalse => exact .pure { safe := nofun, no_level_params := nofun, preserves := nofun }
  rename_i hsafe
  refine M.WF.bind getEnv.WF fun _ _ _ h => ?_
  obtain ⟨rfl, rfl⟩ := h
  split
  · rename_i hname; subst hname; simp at hrest -- ``Nat.add
  · rename_i hname; subst hname; simp at hrest -- ``Nat.pred
  · rename_i hname; subst hname; simp at hrest -- ``Nat.sub
  · rename_i hname; subst hname; simp at hrest -- ``Nat.mul
  · rename_i hname; subst hname; simp at hrest -- ``Nat.pow
  · -- ``Nat.mod
    rename_i hname
    split
    case isFalse => exact M.WF.bindThrow .throw
    rename_i hguard
    simp only [Bool.and_eq_true, List.isEmpty_iff] at hguard
    obtain ⟨⟨⟨⟨hnatE, hboolE⟩, hsubE⟩, hbleE⟩, rfl⟩ := hguard
    refine (checkPrimValue.WF (fun {_} {_} {_} => hfail) (by simp [FVarsIn])).bind
      fun _ _ _ h => ?_
    obtain ⟨ty', F, hty', hF, hFty⟩ := h
    cases trExprS_natArrow2_inv hty'
    have hnf := NatFacts.of_arrow hty'
    have hnat := hnf.contains
    have hprim := (VContext.mk' wf .safe ([] : List Name) fuel).hasPrimitives
    obtain ⟨hFc, -⟩ := closedN_of_nil rfl hFty
    -- `mod 0 x ≡ 0`
    refine M.WF.bind (M.WF.withLocalDecl0 (name := `x) (bi := .default) hnf.tr hnf.isType
      (Q := fun b _ => b = true → (ves.venv .safe).IsDefEqU 0 [VExpr.nat]
        (.app (.app F .natZero) (.bvar 0)) .natZero) ?_) fun b _ _ hb => ?_
    · intro idx cwfx s'' _ _
      have hF' := TrExprS.weakLam0 cwfx hF hFc
      have hFty' := HasType.weakLam0 cwfx hFty hFc ⟨trivial, trivial, trivial⟩
      have hx := trExprS_lastFVar0 cwfx
      have hxty := hasType_lastFVar0 cwfx trivial
      exact checkedIsDefEq.WF' (trExprS_app2_nat hF' hFty'
        (TrExprS.natZero hprim hnat).1 (TrExprS.natZero hprim hnat).2 hx hxty).1
        (TrExprS.natZero hprim hnat).1
    split
    case isFalse => exact M.WF.bindThrow .throw
    rename_i hb1
    have h0 := hb (by simpa using hb1)
    -- `unless ← checkedTypeIs q(@LE.le Nat _) q(Nat → Nat → Prop)`: the relation the fuel
    -- telescope is stated with.  Its translation is `VExpr.natLE` on the nose.
    refine M.WF.bind (checkedTypeIs.WF (by simp [FVarsIn] <;> rfl) (by simp [FVarsIn] <;> rfl))
      fun _ _ _ hpt => ?_
    split
    case isFalse => exact M.WF.bindThrow .throw
    rename_i hpb
    obtain ⟨P, PA, PT, hP, hPA, hPT, hPd⟩ := hpt
    cases trExprS_natLE_inv' hP
    cases trExprS_natArrowProp_inv' hPT
    have hPty : (ves.venv .safe).HasType 0 [] .natLE
        (.forallE .nat (.forallE .nat (.sort .zero))) :=
      hPA.defeqU_r (VContext.mk' wf .safe ([] : List Name) fuel).Ewf
        (VContext.mk' wf .safe ([] : List Name) fuel).Δwf.toCtx (hPd (by simpa using hpb))
    -- `unless ← checkedTypeIs q(Nat.modCore.go) q(∀ n, 1 ≤ n → ∀ fuel x, x + 1 ≤ fuel → Nat)`.
    -- `trExprS_goType_inv'` pins the telescope; `GO` is the abstract `Nat.modCore.go`.
    refine M.WF.bind (checkedTypeIs.WF (by simp [FVarsIn] <;> rfl) (by simp [FVarsIn] <;> rfl))
      fun _ _ _ hgt => ?_
    split
    case isFalse => exact M.WF.bindThrow .throw
    rename_i hgb
    obtain ⟨GO, GA, GT, hGO, hGA, hGT, hGd⟩ := hgt
    cases trExprS_const_nil_inv' hGO
    cases trExprS_goType_inv' hGT
    have hGOty : (ves.venv .safe).HasType 0 [] (.const ``Nat.modCore.go []) .goType :=
      hGA.defeqU_r (VContext.mk' wf .safe ([] : List Name) fuel).Ewf
        (VContext.mk' wf .safe ([] : List Name) fuel).Δwf.toCtx (hGd (by simpa using hgb))
    refine M.WF.bind (Condition.check.WF_natLE_pinned (c := .mk' wf .safe [] fuel)
      (fun {_ _ _ _} => .throw) rfl rfl rfl hnat (NatFacts.isType0 hnf rfl rfl) hbleE
      (fun α hα => by
        cases List.mem_singleton.1 hα; exact ⟨by simp [FVarsIn], trivial, rfl⟩))
      fun _ _ _ hcond => ?_
    obtain ⟨hite, hditeF⟩ := hcond
    obtain ⟨Anat, FI, hAnat, hAc, hFI, hFIc, hRC⟩ :=
      hite (.const ``Nat []) (List.mem_singleton.2 rfl)
    obtain ⟨FD, OT, OF, PR, hFD, hOT, hOF, hRD⟩ := hditeF rfl
    cases trExprS_iteNat_inv' hFI
    cases trExprS_diteNat_inv' hFD
    have hlit : (ves.venv .safe).NatLits := VEnv.HasPrimitives.natLit_hasType hprim hnat
    have henv0 := (VContext.mk' wf .safe ([] : List Name) fuel).Ewf
    refine M.WF.bind (M.WF.withCheckedLocalDecl (Q := fun _ _ =>
        ∀ a b : Nat, (ves.venv .safe).IsDefEqU 0 []
          (.app (.app F (.natLit a)) (.natLit b)) (.natLit (a % b)))
      (by simp [FVarsIn]) ?_) fun _ _ _ hmod => ?_
    · intro tyx idx cwfx s1 _ htyx _
      cases trExprS_const_nil_inv' htyx
      refine M.WF.withCheckedLocalDecl (by simp [FVarsIn]) ?_
      intro tyy idy cwfy s2 _ htyy _
      cases trExprS_const_nil_inv' htyy
      have hnf1 := NatFacts.weakLam0 cwfx hnf
      have hnf2 := NatFacts.weakLam0 cwfy hnf1
      have hF2 := TrExprS.weakLam0 cwfy (TrExprS.weakLam0 cwfx hF hFc) hFc
      have hFty2 := HasType.weakLam0 cwfy
        (HasType.weakLam0 cwfx hFty hFc ⟨trivial, trivial, trivial⟩) hFc
        ⟨trivial, trivial, trivial⟩
      have hxv := TrExprS.weakLift0 cwfy (trExprS_lastFVar0 cwfx)
      have hxty := hasType_fvar1 cwfx cwfy trivial
      have hyv := trExprS_lastFVar0 cwfy
      have hyty := hasType_lastFVar0 cwfy trivial
      have hsx := trExprS_succ hxv hxty hprim hnat
      refine M.WF.bind (checkedIsDefEq.WFr
        (trExprS_app2_nat hF2 hFty2 hsx.1 hsx.2 hyv hyty).1
        (by
          simp [Environment.Condition.ite, Environment.Condition.dite,
            Environment.Condition.natLE, Lean.Expr.lam0, Lean.mkApp5, Lean.mkApp4,
            Lean.mkAppN, FVarsIn, Lean.Level.hasMVar']
          exact ⟨hyv.fvarsIn, hxv.fvarsIn⟩)) fun r1 _ _ hh1 => ?_
      obtain ⟨R1, hR1, hd1⟩ := hh1
      split
      case isFalse => exact M.WF.bindThrow .throw
      rename_i hr1
      have heq1 := hd1 (by simpa using hr1)
      obtain ⟨EA1, LT1, rfl⟩ := trExprS_modEq1_inv' henv0.ordered hxv hyv hR1
      -- `hy : 1 ≤ y`
      refine M.WF.withCheckedLocalDecl (by
        simp [Lean.mkApp2, Lean.mkAppB, FVarsIn, Lean.Level.hasMVar']
        exact hyv.fvarsIn) ?_
      intro tyhy idhy cwfhy s3 _ htyhy _
      obtain ⟨_, _, rfl, k1, k2⟩ := trExprS_natLEApp_inv' htyhy
      cases trExprS_one_inv' k1
      cases trExprS_fvar_uniq k2 hyv
      -- `fuel : Nat`
      refine M.WF.withCheckedLocalDecl (by simp [FVarsIn]) ?_
      intro tyf idf cwff s4 _ htyf _
      cases trExprS_const_nil_inv' htyf
      have hxv4 := TrExprS.weakLift0 cwff (TrExprS.weakLift0 cwfhy hxv)
      have hfv4 := trExprS_lastFVar0 cwff
      -- `h : succ x ≤ succ fuel`
      refine M.WF.withCheckedLocalDecl (by
        simp [Lean.mkApp2, Lean.mkAppB, FVarsIn, Lean.Level.hasMVar']
        exact ⟨hxv4.fvarsIn, hfv4.fvarsIn⟩) ?_
      intro tyh idh cwfh s5 _ htyh _
      obtain ⟨_, _, rfl, m1, m2⟩ := trExprS_natLEApp_inv' htyh
      cases trExprS_succFvar_inv' hxv4 m1
      cases trExprS_succFvar_inv' hfv4 m2
      have hxv5 := TrExprS.weakLift0 cwfh hxv4
      have hyv5 := TrExprS.weakLift0 cwfh (TrExprS.weakLift0 cwff (TrExprS.weakLift0 cwfhy hyv))
      have hhyv5 := TrExprS.weakLift0 cwfh (TrExprS.weakLift0 cwff (trExprS_lastFVar0 cwfhy))
      have hfv5 := TrExprS.weakLift0 cwfh hfv4
      have hhv5 := trExprS_lastFVar0 cwfh
      have hxty5 := HasType.weakLift0 cwfh (HasType.weakLift0 cwff (HasType.weakLift0 cwfhy
        (hasType_fvar1 cwfx cwfy trivial)))
      have hyty5 := HasType.weakLift0 cwfh (HasType.weakLift0 cwff (HasType.weakLift0 cwfhy
        (hasType_lastFVar0 cwfy trivial)))
      have hhyty5 := HasType.weakLift0 cwfh (HasType.weakLift0 cwff
        (hasType_lastFVar (cwf := cwfhy)))
      have hfty5 := HasType.weakLift0 cwfh (hasType_lastFVar0 cwff trivial)
      have hhty5 := hasType_lastFVar (cwf := cwfh)
      have hsf5 := trExprS_succ hfv5 hfty5 hprim hnat
      have hGO5 := TrExprS.weakLam0 cwfh (TrExprS.weakLam0 cwff (TrExprS.weakLam0 cwfhy
        (TrExprS.weakLam0 cwfy (TrExprS.weakLam0 cwfx hGO trivial) trivial) trivial) trivial)
        trivial
      have hGOty5 := HasType.weakLam0 cwfh (HasType.weakLam0 cwff (HasType.weakLam0 cwfhy
        (HasType.weakLam0 cwfy (HasType.weakLam0 cwfx hGOty trivial VExpr.closedN_goType)
          trivial VExpr.closedN_goType) trivial VExpr.closedN_goType) trivial
        VExpr.closedN_goType) trivial VExpr.closedN_goType
      refine M.WF.bind (checkedIsDefEq.WFr
        (trExprS_goApp hGO5 hGOty5 hyv5 hyty5 hhyv5 hhyty5 hsf5.1 hsf5.2 hxv5 hxty5
          hhv5 hhty5).1
        (by
          simp [Environment.Condition.dite, Environment.Condition.natLE, Lean.Expr.lam0,
            Lean.mkApp5, Lean.mkApp4, Lean.mkApp2, Lean.mkApp6, Lean.mkAppB, Lean.mkAppN,
            FVarsIn, Lean.Level.hasMVar']
          repeat' apply And.intro
          all_goals first
            | exact hxv5.fvarsIn | exact hyv5.fvarsIn | exact hhyv5.fvarsIn
            | exact hfv5.fvarsIn | exact hhv5.fvarsIn | trivial
            | simp [FVarsIn, Lean.Level.hasMVar']))
        fun r2 _ _ hh2 => ?_
      obtain ⟨R2, hR2, hd2⟩ := hh2
      split
      case isFalse => exact .throw
      rename_i hr2
      have heq2 := hd2 (by simpa using hr2)
      obtain ⟨EA2, K2, rfl⟩ := trExprS_modEq2_inv' henv0.ordered hxv5 hyv5 hhyv5 hfv5 hR2
      refine .pure (VEnv.reflects_mod_of_equations henv0 hlit hprim hnat
        (contains_primConst (c := VContext.mk' wf .safe ([] : List Name) fuel) rfl hsubE
          primitives_natSub)
        hFc ?_ ?_ hGOty (hRC.self henv0) (hRD.self henv0) h0 heq1 heq2)
      · trivial
      · trivial
    · refine .pure ⟨fun _ => (by simpa using hsafe), fun _ => rfl, ?_⟩
      intro _ sf venv env'' ci' hle hwf' hprim2 htr hci hadd
      refine preserves_glue (nm := ``Nat.mod) (F := F) hname rfl rfl (by decide) hF ?_
        hle hwf' hprim2 htr hci hadd
      intro venv' env₂ hle' hle₂ henv₂ hprim3 hdefF
      have hle3 := hle'.trans hle₂
      exact VEnv.primField_Nat_mod.2 (reflectsNNN_of_open hle₂ henv₂ hprim3
        (VEnv.contains.mono hle' hnat) hdefF (hFty.mono hle3)
        fun _ a b => (hmod a b).mono hle3)
  · -- ``Nat.div
    rename_i hname
    split
    case isFalse => exact M.WF.bindThrow .throw
    rename_i hguard
    simp only [Bool.and_eq_true, List.isEmpty_iff] at hguard
    obtain ⟨⟨⟨⟨hnatE, hboolE⟩, hsubE⟩, hbleE⟩, rfl⟩ := hguard
    refine (checkPrimValue.WF (fun {_} {_} {_} => hfail) (by simp [FVarsIn])).bind
      fun _ _ _ h => ?_
    obtain ⟨ty', F, hty', hF, hFty⟩ := h
    cases trExprS_natArrow2_inv hty'
    have hnf := NatFacts.of_arrow hty'
    have hnat := hnf.contains
    have hprim := (VContext.mk' wf .safe ([] : List Name) fuel).hasPrimitives
    obtain ⟨hFc, -⟩ := closedN_of_nil rfl hFty
    have hlit : (ves.venv .safe).NatLits := VEnv.HasPrimitives.natLit_hasType hprim hnat
    have henv0 := (VContext.mk' wf .safe ([] : List Name) fuel).Ewf
    -- `Condition.natLE.check` runs *before* the two `checkedTypeIs` in this branch.
    refine M.WF.bind (Condition.check.WF_natLE_pinned (c := .mk' wf .safe [] fuel)
      (fun {_ _ _ _} => .throw) rfl rfl rfl hnat (NatFacts.isType0 hnf rfl rfl) hbleE
      (fun α hα => absurd hα (by simp))) fun _ _ _ hcond => ?_
    obtain ⟨-, hditeF⟩ := hcond
    obtain ⟨FD, OT, OF, PR, hFD, hOT, hOF, hRD⟩ := hditeF rfl
    cases trExprS_diteNat_inv' hFD
    -- `unless ← checkedTypeIs q(@LE.le Nat _) q(Nat → Nat → Prop)`
    refine M.WF.bind (checkedTypeIs.WF (by simp [FVarsIn] <;> rfl) (by simp [FVarsIn] <;> rfl))
      fun _ _ _ hpt => ?_
    split
    case isFalse => exact M.WF.bindThrow .throw
    rename_i hpb
    obtain ⟨P, PA, PT, hP, hPA, hPT, hPd⟩ := hpt
    cases trExprS_natLE_inv' hP
    cases trExprS_natArrowProp_inv' hPT
    -- `unless ← checkedTypeIs q(Nat.div.go) q(∀ y, 1 ≤ y → ∀ fuel x, x + 1 ≤ fuel → Nat)`
    refine M.WF.bind (checkedTypeIs.WF (by simp [FVarsIn] <;> rfl) (by simp [FVarsIn] <;> rfl))
      fun _ _ _ hgt => ?_
    split
    case isFalse => exact M.WF.bindThrow .throw
    rename_i hgb
    obtain ⟨GO, GA, GT, hGO, hGA, hGT, hGd⟩ := hgt
    cases trExprS_const_nil_inv' hGO
    cases trExprS_goType_inv' hGT
    have hGOty : (ves.venv .safe).HasType 0 [] (.const ``Nat.div.go []) .goType :=
      hGA.defeqU_r (VContext.mk' wf .safe ([] : List Name) fuel).Ewf
        (VContext.mk' wf .safe ([] : List Name) fuel).Δwf.toCtx (hGd (by simpa using hgb))
    refine M.WF.bind (M.WF.withCheckedLocalDecl (Q := fun _ _ =>
        ∀ a b : Nat, (ves.venv .safe).IsDefEqU 0 []
          (.app (.app F (.natLit a)) (.natLit b)) (.natLit (a / b)))
      (by simp [FVarsIn]) ?_) fun _ _ _ hdiv => ?_
    · intro tyx idx cwfx s1 _ htyx _
      cases trExprS_const_nil_inv' htyx
      refine M.WF.withCheckedLocalDecl (by simp [FVarsIn]) ?_
      intro tyy idy cwfy s2 _ htyy _
      cases trExprS_const_nil_inv' htyy
      have hnf1 := NatFacts.weakLam0 cwfx hnf
      have hnf2 := NatFacts.weakLam0 cwfy hnf1
      have hF2 := TrExprS.weakLam0 cwfy (TrExprS.weakLam0 cwfx hF hFc) hFc
      have hFty2 := HasType.weakLam0 cwfy
        (HasType.weakLam0 cwfx hFty hFc ⟨trivial, trivial, trivial⟩) hFc
        ⟨trivial, trivial, trivial⟩
      have hxv := TrExprS.weakLift0 cwfy (trExprS_lastFVar0 cwfx)
      have hxty := hasType_fvar1 cwfx cwfy trivial
      have hyv := trExprS_lastFVar0 cwfy
      have hyty := hasType_lastFVar0 cwfy trivial
      refine M.WF.bind (checkedIsDefEq.WFr
        (trExprS_app2_nat hF2 hFty2 hxv hxty hyv hyty).1
        (by
          simp [Environment.Condition.dite, Environment.Condition.natLE, Lean.Expr.lam0,
            Lean.mkApp5, Lean.mkApp4, Lean.mkAppN, Lean.Level.hasMVar']
          repeat' apply And.intro
          all_goals first
            | exact hxv.fvarsIn | exact hyv.fvarsIn | trivial
            | simp [FVarsIn, Lean.Level.hasMVar'])) fun r1 _ _ hh1 => ?_
      obtain ⟨R1, hR1, hd1⟩ := hh1
      split
      case isFalse => exact M.WF.bindThrow .throw
      rename_i hr1
      have heq1 := hd1 (by simpa using hr1)
      obtain ⟨EA1, LT1, rfl⟩ := trExprS_divEq1_inv' henv0.ordered hxv hyv hR1
      -- `hy : 1 ≤ y`
      refine M.WF.withCheckedLocalDecl (by
        simp [Lean.mkApp2, Lean.mkAppB, FVarsIn, Lean.Level.hasMVar']
        exact hyv.fvarsIn) ?_
      intro tyhy idhy cwfhy s3 _ htyhy _
      obtain ⟨_, _, rfl, k1, k2⟩ := trExprS_natLEApp_inv' htyhy
      cases trExprS_one_inv' k1
      cases trExprS_fvar_uniq k2 hyv
      -- `fuel : Nat`
      refine M.WF.withCheckedLocalDecl (by simp [FVarsIn]) ?_
      intro tyf idf cwff s4 _ htyf _
      cases trExprS_const_nil_inv' htyf
      have hxv4 := TrExprS.weakLift0 cwff (TrExprS.weakLift0 cwfhy hxv)
      have hfv4 := trExprS_lastFVar0 cwff
      -- `h : succ x ≤ succ fuel`
      refine M.WF.withCheckedLocalDecl (by
        simp [Lean.mkApp2, Lean.mkAppB, FVarsIn, Lean.Level.hasMVar']
        exact ⟨hxv4.fvarsIn, hfv4.fvarsIn⟩) ?_
      intro tyh idh cwfh s5 _ htyh _
      obtain ⟨_, _, rfl, m1, m2⟩ := trExprS_natLEApp_inv' htyh
      cases trExprS_succFvar_inv' hxv4 m1
      cases trExprS_succFvar_inv' hfv4 m2
      have hxv5 := TrExprS.weakLift0 cwfh hxv4
      have hyv5 := TrExprS.weakLift0 cwfh (TrExprS.weakLift0 cwff (TrExprS.weakLift0 cwfhy hyv))
      have hhyv5 := TrExprS.weakLift0 cwfh (TrExprS.weakLift0 cwff (trExprS_lastFVar0 cwfhy))
      have hfv5 := TrExprS.weakLift0 cwfh hfv4
      have hhv5 := trExprS_lastFVar0 cwfh
      have hxty5 := HasType.weakLift0 cwfh (HasType.weakLift0 cwff (HasType.weakLift0 cwfhy
        (hasType_fvar1 cwfx cwfy trivial)))
      have hyty5 := HasType.weakLift0 cwfh (HasType.weakLift0 cwff (HasType.weakLift0 cwfhy
        (hasType_lastFVar0 cwfy trivial)))
      have hhyty5 := HasType.weakLift0 cwfh (HasType.weakLift0 cwff
        (hasType_lastFVar (cwf := cwfhy)))
      have hfty5 := HasType.weakLift0 cwfh (hasType_lastFVar0 cwff trivial)
      have hhty5 := hasType_lastFVar (cwf := cwfh)
      have hsf5 := trExprS_succ hfv5 hfty5 hprim hnat
      have hGO5 := TrExprS.weakLam0 cwfh (TrExprS.weakLam0 cwff (TrExprS.weakLam0 cwfhy
        (TrExprS.weakLam0 cwfy (TrExprS.weakLam0 cwfx hGO trivial) trivial) trivial) trivial)
        trivial
      have hGOty5 := HasType.weakLam0 cwfh (HasType.weakLam0 cwff (HasType.weakLam0 cwfhy
        (HasType.weakLam0 cwfy (HasType.weakLam0 cwfx hGOty trivial VExpr.closedN_goType)
          trivial VExpr.closedN_goType) trivial VExpr.closedN_goType) trivial
        VExpr.closedN_goType) trivial VExpr.closedN_goType
      refine M.WF.bind (checkedIsDefEq.WFr
        (trExprS_goApp hGO5 hGOty5 hyv5 hyty5 hhyv5 hhyty5 hsf5.1 hsf5.2 hxv5 hxty5
          hhv5 hhty5).1
        (by
          simp [Environment.Condition.dite, Environment.Condition.natLE, Lean.Expr.lam0,
            Lean.mkApp5, Lean.mkApp4, Lean.mkApp2, Lean.mkApp6, Lean.mkAppB, Lean.mkAppN,
            FVarsIn, Lean.Level.hasMVar']
          repeat' apply And.intro
          all_goals first
            | exact hxv5.fvarsIn | exact hyv5.fvarsIn | exact hhyv5.fvarsIn
            | exact hfv5.fvarsIn | exact hhv5.fvarsIn | trivial
            | simp [FVarsIn, Lean.Level.hasMVar']))
        fun r2 _ _ hh2 => ?_
      obtain ⟨R2, hR2, hd2⟩ := hh2
      split
      case isFalse => exact .throw
      rename_i hr2
      have heq2 := hd2 (by simpa using hr2)
      obtain ⟨EA2, K2, rfl⟩ := trExprS_divEq2_inv' henv0.ordered hxv5 hyv5 hhyv5 hfv5 hR2
      refine .pure (VEnv.reflects_div_of_equations henv0 hlit hprim hnat
        (contains_primConst (c := VContext.mk' wf .safe ([] : List Name) fuel) rfl hsubE
          primitives_natSub)
        hFc ?_ ?_ hGOty (hRD.self henv0) heq1 heq2)
      · trivial
      · trivial
    · refine .pure ⟨fun _ => (by simpa using hsafe), fun _ => rfl, ?_⟩
      intro _ sf venv env'' ci' hle hwf' hprim2 htr hci hadd
      refine preserves_glue (nm := ``Nat.div) (F := F) hname rfl rfl (by decide) hF ?_
        hle hwf' hprim2 htr hci hadd
      intro venv' env₂ hle' hle₂ henv₂ hprim3 hdefF
      have hle3 := hle'.trans hle₂
      exact VEnv.primField_Nat_div.2 (reflectsNNN_of_open hle₂ henv₂ hprim3
        (VEnv.contains.mono hle' hnat) hdefF (hFty.mono hle3)
        fun _ a b => (hdiv a b).mono hle3)
  · -- ``Nat.gcd
    rename_i hname
    split
    case isFalse => exact M.WF.bindThrow .throw
    rename_i hguard
    simp only [Bool.and_eq_true, List.isEmpty_iff] at hguard
    obtain ⟨⟨⟨⟨hnatE, hboolE⟩, hmodE⟩, hbeqE⟩, rfl⟩ := hguard
    refine (checkPrimValue.WF (fun {_} {_} {_} => hfail) (by simp [FVarsIn])).bind
      fun _ _ _ h => ?_
    obtain ⟨ty', F, hty', hF, hFty⟩ := h
    cases trExprS_natArrow2_inv hty'
    have hnf := NatFacts.of_arrow hty'
    have hnat := hnf.contains
    have hprim := (VContext.mk' wf .safe ([] : List Name) fuel).hasPrimitives
    obtain ⟨hFc, -⟩ := closedN_of_nil rfl hFty
    have hlit : (ves.venv .safe).NatLits := VEnv.HasPrimitives.natLit_hasType hprim hnat
    have henv0 := (VContext.mk' wf .safe ([] : List Name) fuel).Ewf
    have hbeq : (ves.venv .safe).contains ``Nat.beq :=
      contains_primConst (c := VContext.mk' wf .safe ([] : List Name) fuel) rfl hbeqE
        primitives_natBEq
    have hmodP : (ves.venv .safe).contains ``Nat.mod :=
      contains_primConst (c := VContext.mk' wf .safe ([] : List Name) fuel) rfl hmodE
        primitives_natMod
    refine M.WF.bind (Condition.check.WF_natEq_pinned (c := .mk' wf .safe [] fuel)
      (fun {_ _ _ _} => .throw) rfl rfl rfl hnat (NatFacts.isType0 hnf rfl rfl) hbeqE
      (fun α hα => absurd hα (by simp))) fun _ _ _ hcond => ?_
    obtain ⟨-, hditeF⟩ := hcond
    obtain ⟨FD, OT, OF, PR, hFD, hOT, hOF, hRD⟩ := hditeF rfl
    cases trExprS_diteNat_inv' hFD
    refine M.WF.bind (Condition.check.WF_boolCond (c := .mk' wf .safe [] fuel)
      (fun {_ _ _ _} => .throw) rfl rfl
      (fun α hα => by
        cases List.mem_singleton.1 hα; exact ⟨by simp [FVarsIn], trivial, rfl⟩))
      fun _ _ _ hcondB => ?_
    obtain ⟨PB, DB, hPB, hDB, hPBc, hDBc, hiteB⟩ := hcondB
    obtain ⟨Anat, IN, hAnat, hAnatc, hIN, hINc, hB1⟩ :=
      hiteB (.const ``Nat []) (List.mem_singleton.2 rfl)
    cases trExprS_iteNat_inv' hIN
    refine M.WF.bind (M.WF.withCheckedLocalDecl
      (Q := fun u _ => Environment.NatWFUnfold.Good u) (by simp [FVarsIn]) ?_)
      fun u _ _ hu => ?_
    · intro tym idm cwfm s1 _ htym _
      cases trExprS_const_nil_inv' htym
      refine M.WF.withCheckedLocalDecl (by simp [FVarsIn]) ?_
      intro tyn idn cwfn s2 _ htyn _
      cases trExprS_const_nil_inv' htyn
      have hF2 := TrExprS.weakLam0 cwfn (TrExprS.weakLam0 cwfm hF hFc) hFc
      have hFty2 := HasType.weakLam0 cwfn
        (HasType.weakLam0 cwfm hFty hFc ⟨trivial, trivial, trivial⟩) hFc
        ⟨trivial, trivial, trivial⟩
      have hmv := TrExprS.weakLift0 cwfn (trExprS_lastFVar0 cwfm)
      have hmty := hasType_fvar1 cwfm cwfn trivial
      have hnv := trExprS_lastFVar0 cwfn
      have hnty := hasType_lastFVar0 cwfn trivial
      exact unfoldNatWellFounded.WF (fun {_ _ _} => .throw)
        ⟨_, (trExprS_app2_nat hF2 hFty2 hmv hmty hnv hnty).1⟩
    have hgoFV : u.go.FVarsIn (· ∈ (VContext.mk' wf .safe ([] : List Name) fuel).vlctx.fvars) :=
      hu.goFV.mono nofun
    have halFV : u.alpha.FVarsIn
        (· ∈ (VContext.mk' wf .safe ([] : List Name) fuel).vlctx.fvars) := hu.alphaFV.mono nofun
    have hmsFV : u.measure.FVarsIn
        (· ∈ (VContext.mk' wf .safe ([] : List Name) fuel).vlctx.fvars) := hu.measFV.mono nofun
    have hmoFV : u.motive.FVarsIn
        (· ∈ (VContext.mk' wf .safe ([] : List Name) fuel).vlctx.fvars) := hu.motiveFV.mono nofun
    have hpkFV : u.pack.FVarsIn
        (· ∈ (VContext.mk' wf .safe ([] : List Name) fuel).vlctx.fvars) := hu.packFV.mono nofun
    refine M.WF.bind (checkedTypeIs.WF hgoFV
      (by
        simp only [Lean4Lean.Environment.NatWFUnfold.goType, FVarsIn, Lean.mkApp2, Lean.mkApp]
        repeat' apply And.intro
        all_goals first
          | exact halFV | exact hmsFV | exact hmoFV
          | simp [Lean.Level.hasMVar'] | trivial)) fun _ _ _ hgt => ?_
    split
    case isFalse => exact M.WF.bindThrow .throw
    rename_i hgb
    obtain ⟨GO, GOA, GOTY, hGO, hGOA, hGOTY, hGOd⟩ := hgt
    refine M.WF.bind (checkedTypeIs.WF hmsFV
      (by
        simp only [FVarsIn]
        repeat' apply And.intro
        all_goals first | exact halFV | simp [Lean.Level.hasMVar'] | trivial))
      fun _ _ _ hmt => ?_
    split
    case isFalse => exact M.WF.bindThrow .throw
    rename_i hmb
    obtain ⟨MEAS, MEASA, MTY, hMEAS, hMEASA, hMTY, hMEASd⟩ := hmt
    obtain ⟨A, natA, rfl, hAlpha, hNatA⟩ := trExprS_arrow_inv' hMTY
    cases trExprS_const_nil_inv' hNatA
    have hMEASty : (ves.venv .safe).HasType 0 [] MEAS (.forallE A .nat) :=
      hMEASA.defeqU_r henv0 (VContext.mk' wf .safe ([] : List Name) fuel).Δwf.toCtx
        (hMEASd (by simpa using hmb))
    obtain ⟨hMEASc, hMTYc⟩ := closedN_of_nil (c := VContext.mk' wf .safe ([] : List Name) fuel)
      rfl hMEASty
    have hAc : A.ClosedN 0 := hMTYc.1
    have halB : u.alpha.looseBVarRange' = 0 := trExprS_looseBVarRange_nil hAlpha
    have hmsB : u.measure.looseBVarRange' = 0 := trExprS_looseBVarRange_nil hMEAS
    have hgoB : u.go.looseBVarRange' = 0 := trExprS_looseBVarRange_nil hGO
    refine M.WF.bind (checkedTypeIs.WF hpkFV
      (by
        simp only [FVarsIn]
        repeat' apply And.intro
        all_goals first | exact halFV | simp [Lean.Level.hasMVar'] | trivial))
      fun _ _ _ hpt => ?_
    split
    case isFalse => exact M.WF.bindThrow .throw
    rename_i hpb
    obtain ⟨PACK, PACKA, PTY, hPACK, hPACKA, hPTY, hPACKd⟩ := hpt
    obtain ⟨n1, B1, rfl, hn1, hB1'⟩ := trExprS_arrow_inv' hPTY
    cases trExprS_const_nil_inv' hn1
    obtain ⟨n2, B2, rfl, hn2, hA2⟩ := trExprS_arrow_inv' hB1'
    cases trExprS_const_nil_inv' hn2
    cases TrExprS.unique hu.alphaU hA2
      (trExprS_weakBV0 henv0.ordered
        (trExprS_weakBV0 henv0.ordered hAlpha halB hAc) halB hAc)
    have hPACKty : (ves.venv .safe).HasType 0 [] PACK (.forallE .nat (.forallE .nat A)) :=
      hPACKA.defeqU_r henv0 (VContext.mk' wf .safe ([] : List Name) fuel).Δwf.toCtx
        (hPACKd (by simpa using hpb))
    obtain ⟨hPACKc, -⟩ := closedN_of_nil (c := VContext.mk' wf .safe ([] : List Name) fuel)
      rfl hPACKty
    have hpkB : u.pack.looseBVarRange' = 0 := trExprS_looseBVarRange_nil hPACK
    obtain ⟨D, rfl⟩ := trExprS_goTypeWF_inv' henv0.ordered hAlpha hu.alphaU halB hAc
      hMEAS hu.measU hmsB hMEASc hGOTY
    have hGOty : (ves.venv .safe).HasType 0 [] GO (.goTypeWF A MEAS D) :=
      hGOA.defeqU_r henv0 (VContext.mk' wf .safe ([] : List Name) fuel).Δwf.toCtx
        (hGOd (by simpa using hgb))
    obtain ⟨hGOc, hGOTYc⟩ := closedN_of_nil
      (c := VContext.mk' wf .safe ([] : List Name) fuel) rfl hGOty
    have hAc2 : (VExpr.forallE .nat (.forallE .nat A)).ClosedN 0 :=
      ⟨trivial, trivial, hAc.mono (by omega)⟩
    have hAc1 : (VExpr.forallE A VExpr.nat).ClosedN 0 := ⟨hAc, trivial⟩
    refine M.WF.bind (M.WF.withCheckedLocalDecl (Q := fun _ _ =>
        ∀ a b : Nat, (ves.venv .safe).IsDefEqU 0 []
          (.app (.app F (.natLit a)) (.natLit b)) (.natLit (Nat.gcd a b)))
      (by simp [FVarsIn]) ?_) fun _ _ _ hgcd => ?_
    · intro tym idm cwfm s1 _ htym _
      cases trExprS_const_nil_inv' htym
      refine M.WF.withCheckedLocalDecl (by simp [FVarsIn]) ?_
      intro tyn idn cwfn s2 _ htyn _
      cases trExprS_const_nil_inv' htyn
      have hGO2 := TrExprS.weakLam0 cwfn (TrExprS.weakLam0 cwfm hGO hGOc) hGOc
      have hPACK2 := TrExprS.weakLam0 cwfn (TrExprS.weakLam0 cwfm hPACK hPACKc) hPACKc
      have hMEAS2 := TrExprS.weakLam0 cwfn (TrExprS.weakLam0 cwfm hMEAS hMEASc) hMEASc
      have hPB2 := TrExprS.weakLam0 cwfn (TrExprS.weakLam0 cwfm hPB hPBc) hPBc
      have hDB2 := TrExprS.weakLam0 cwfn (TrExprS.weakLam0 cwfm hDB hDBc) hDBc
      have hPACKty2 := HasType.weakLam0 cwfn
        (HasType.weakLam0 cwfm hPACKty hPACKc hAc2) hPACKc hAc2
      have hMEASty2 := HasType.weakLam0 cwfn
        (HasType.weakLam0 cwfm hMEASty hMEASc hAc1) hMEASc hAc1
      have hF2 := TrExprS.weakLam0 cwfn (TrExprS.weakLam0 cwfm hF hFc) hFc
      have hFty2 := HasType.weakLam0 cwfn
        (HasType.weakLam0 cwfm hFty hFc ⟨trivial, trivial, trivial⟩) hFc
        ⟨trivial, trivial, trivial⟩
      have hmv := TrExprS.weakLift0 cwfn (trExprS_lastFVar0 cwfm)
      have hmty := hasType_fvar1 cwfm cwfn trivial
      have hnv := trExprS_lastFVar0 cwfn
      have hnty := hasType_lastFVar0 cwfn trivial
      obtain ⟨hpk, hpkty⟩ := trExprS_packApp hPACK2 hPACKty2 hAc hmv hmty hnv hnty
      obtain ⟨hmeasApp, hmeasAppTy⟩ := trExprS_measApp hMEAS2 hMEASty2 hpk hpkty
      refine M.WF.bind (checkedIsDefEq.WF' hmeasApp hmv) fun r1 _ _ hd1 => ?_
      split
      case isFalse => exact M.WF.bindThrow .throw
      rename_i hr1
      have hmeas := hd1 (by simpa using hr1)
      obtain ⟨hlhs, hlhsty⟩ := trExprS_app2_nat hF2 hFty2 hmv hmty hnv hnty
      refine M.WF.bind (checkedIsDefEq.WFr hlhs
        (by
          simp only [Lean4Lean.Environment.Condition.ite, Lean4Lean.Environment.Condition.bool,
            Lean.mkApp5, Lean.mkApp3, Lean.mkApp2, Lean.mkApp, Lean.mkAppN, FVarsIn]
          repeat' apply And.intro
          all_goals first
            | exact hu.goFV.mono nofun | exact hu.packFV.mono nofun
            | exact hu.measFV.mono nofun | exact hu.prfAFV.mono nofun
            | exact hmv.fvarsIn | exact hnv.fvarsIn
            | simp [FVarsIn, Lean.Level.hasMVar'] | trivial))
        fun r2 _ _ hh2 => ?_
      obtain ⟨R2, hR2, hd2⟩ := hh2
      split
      case isFalse => exact M.WF.bindThrow .throw
      rename_i hr2
      have hent0 := hd2 (by simpa using hr2)
      obtain ⟨PRFA, rfl⟩ := trExprS_gcdEntry_inv' hGO2 hu.goU hPACK2 hu.packU hMEAS2 hu.measU
        hPB2 hDB2 hmv hnv hR2
      have hGOty2 := HasType.weakLam0 cwfn
        (HasType.weakLam0 cwfm hGOty hGOc hGOTYc) hGOc hGOTYc
      refine M.WF.withCheckedLocalDecl (by simp [FVarsIn]) ?_
      intro tyf idf cwff s3 _ htyf _
      cases trExprS_const_nil_inv' htyf
      have hmv3 := TrExprS.weakLift0 cwff hmv
      have hnv3 := TrExprS.weakLift0 cwff hnv
      have hfv3 := trExprS_lastFVar0 cwff
      have hMEAS3 := TrExprS.weakLam0 cwff hMEAS2 hMEASc
      have hPACK3 := TrExprS.weakLam0 cwff hPACK2 hPACKc
      have hGO3 := TrExprS.weakLam0 cwff hGO2 hGOc
      refine M.WF.withCheckedLocalDecl (by
        simp only [Lean.mkApp2, Lean.mkApp, FVarsIn]
        repeat' apply And.intro
        all_goals first
          | exact hMEAS3.fvarsIn | exact hPACK3.fvarsIn
          | exact hmv3.fvarsIn | exact hnv3.fvarsIn | exact hfv3.fvarsIn
          | simp [FVarsIn, Lean.Level.hasMVar'] | trivial) ?_
      intro tyh idh cwfh s4 _ htyh _
      obtain ⟨XA, FUA, rfl, mh1, mh2⟩ := trExprS_natLEApp_inv' htyh
      obtain ⟨_, _, rfl, k1, k2⟩ := trExprS_app_inv' mh1
      cases trExprS_const_nil_inv' k1
      obtain ⟨_, _, rfl, k3, k4⟩ := trExprS_app_inv' k2
      cases TrExprS.unique hu.measU k3 hMEAS3
      obtain ⟨_, _, rfl, k5, k6⟩ := trExprS_app_inv' k4
      obtain ⟨_, _, rfl, k7, k8⟩ := trExprS_app_inv' k5
      cases TrExprS.unique hu.packU k7 hPACK3
      cases trExprS_fvar_uniq k8 hmv3
      cases trExprS_fvar_uniq k6 hnv3
      cases trExprS_succFvar_inv' hfv3 mh2
      have hGO4 := TrExprS.weakLam0 cwfh hGO3 hGOc
      have hPACK4 := TrExprS.weakLam0 cwfh hPACK3 hPACKc
      have hMEAS4 := TrExprS.weakLam0 cwfh hMEAS3 hMEASc
      have hmv4 := TrExprS.weakLift0 cwfh hmv3
      have hnv4 := TrExprS.weakLift0 cwfh hnv3
      have hfv4 := TrExprS.weakLift0 cwfh hfv3
      have hhv4 := trExprS_lastFVar0 cwfh
      have hmty4 := HasType.weakLift0 cwfh (HasType.weakLift0 cwff hmty)
      have hnty4 := HasType.weakLift0 cwfh (HasType.weakLift0 cwff hnty)
      have hfty4 := HasType.weakLift0 cwfh (hasType_lastFVar0 cwff trivial)
      have hPACKty4 := HasType.weakLam0 cwfh
        (HasType.weakLam0 cwff hPACKty2 hPACKc hAc2) hPACKc hAc2
      have hGOty4 := HasType.weakLam0 cwfh
        (HasType.weakLam0 cwff hGOty2 hGOc hGOTYc) hGOc hGOTYc
      obtain ⟨hpk4, hpkty4⟩ := trExprS_packApp hPACK4 hPACKty4 hAc hmv4 hmty4 hnv4 hnty4
      have hsf := trExprS_succ hfv4 hfty4 hprim hnat
      have hhty4 := hasType_lastFVar (cwf := cwfh)
      simp only [VExpr.natLEApp, VExpr.natLE, VExpr.lift, VExpr.liftN, Lean4Lean.liftVar,
        hMEASc.liftN_eq (Nat.zero_le _), hPACKc.liftN_eq (Nat.zero_le _)] at hhty4
      have hlhsGo := trExprS_goAppWF hGO4 hGOty4 hAc hMEASc hsf.1 hsf.2 hpk4 hpkty4 hhv4 hhty4
      refine M.WF.bind (checkedIsDefEq.WFr hlhsGo
        (by
          simp only [Lean4Lean.Environment.Condition.dite,
            Lean4Lean.Environment.Condition.natEq, Lean.Expr.lam0, Lean.mkApp5, Lean.mkApp4,
            Lean.mkApp3, Lean.mkApp2, Lean.mkApp, Lean.mkAppN, FVarsIn]
          repeat' apply And.intro
          all_goals first
            | exact hu.goFV.mono nofun | exact hu.packFV.mono nofun
            | exact hmv4.fvarsIn | exact hnv4.fvarsIn | exact hfv4.fvarsIn
            | exact hhv4.fvarsIn
            | simp [FVarsIn, Lean.Level.hasMVar'] | trivial))
        fun r3 _ _ hh3 => ?_
      obtain ⟨R3, hR3, hd3⟩ := hh3
      split
      case isFalse => exact .throw
      rename_i hr3
      have hgoeq0 := hd3 (by simpa using hr3)
      obtain ⟨EA, KA, rfl⟩ := trExprS_gcdGo_inv' henv0.ordered hGO4 hu.goU hgoB hGOc
        hPACK4 hu.packU hpkB hPACKc hmv4 hnv4 hfv4 hR3
      exact .pure (VEnv.reflects_gcd_of_equations henv0 hlit hprim hnat hbeq hmodP
        hFc hGOc hPACKc hMEASc hAc hINc hPBc hDBc
        (show VExpr.ClosedN (.const ``Nat.decEq []) 0 from trivial)
        hGOty (hRD.self henv0) (hB1.self henv0) hmeas hent0 hgoeq0)
    · refine .pure ⟨fun _ => (by simpa using hsafe), fun _ => rfl, ?_⟩
      intro _ sf venv env'' ci' hle hwf' hprim2 htr hci hadd
      refine preserves_glue (nm := ``Nat.gcd) (F := F) hname rfl rfl (by decide) hF ?_
        hle hwf' hprim2 htr hci hadd
      intro venv' env₂ hle' hle₂ henv₂ hprim3 hdefF
      have hle3 := hle'.trans hle₂
      exact VEnv.primField_Nat_gcd.2 (reflectsNNN_of_open hle₂ henv₂ hprim3
        (VEnv.contains.mono hle' hnat) hdefF (hFty.mono hle3)
        fun _ a b => (hgcd a b).mono hle3)
  · rename_i hname; subst hname; simp at hrest -- ``Nat.beq
  · rename_i hname; subst hname; simp at hrest -- ``Nat.ble
  · -- ``Nat.bitwise
    rename_i hname
    split
    case isFalse => exact M.WF.bindThrow .throw
    rename_i hguard
    simp only [Bool.and_eq_true, List.isEmpty_iff] at hguard
    obtain ⟨⟨⟨⟨⟨⟨hnatE, hboolE⟩, haddE⟩, hdivE⟩, hmodE⟩, hbeqE⟩, rfl⟩ := hguard
    refine (checkPrimValue.WF (fun {_} {_} {_} => hfail) (by simp [FVarsIn])).bind
      fun _ _ _ h => ?_
    obtain ⟨ty', F, hty', hF, hFty⟩ := h
    cases trExprS_bitwiseType_inv' hty'
    have hprim := (VContext.mk' wf .safe ([] : List Name) fuel).hasPrimitives
    have hnat : (ves.venv .safe).contains ``Nat :=
      contains_primConst (c := VContext.mk' wf .safe ([] : List Name) fuel) rfl hnatE
        primitives_Nat
    have hnf : NatFacts (VContext.mk' wf .safe ([] : List Name) fuel) :=
      ⟨trExprS_primConst rfl hnatE primitives_Nat, isType_nat hprim hnat rfl⟩
    obtain ⟨hFc, -⟩ := closedN_of_nil rfl hFty
    have hlit : (ves.venv .safe).NatLits := VEnv.HasPrimitives.natLit_hasType hprim hnat
    have henv0 := (VContext.mk' wf .safe ([] : List Name) fuel).Ewf
    have hbeq : (ves.venv .safe).contains ``Nat.beq :=
      contains_primConst (c := VContext.mk' wf .safe ([] : List Name) fuel) rfl hbeqE
        primitives_natBEq
    have hmodP : (ves.venv .safe).contains ``Nat.mod :=
      contains_primConst (c := VContext.mk' wf .safe ([] : List Name) fuel) rfl hmodE
        primitives_natMod
    have haddP : (ves.venv .safe).contains ``Nat.add :=
      contains_primConst (c := VContext.mk' wf .safe ([] : List Name) fuel) rfl haddE
        primitives_natAdd
    have hdivP : (ves.venv .safe).contains ``Nat.div :=
      contains_primConst (c := VContext.mk' wf .safe ([] : List Name) fuel) rfl hdivE
        primitives_natDiv
    refine M.WF.bind (Condition.check.WF_natEq_pinned (c := .mk' wf .safe [] fuel)
      (fun {_ _ _ _} => .throw) rfl rfl rfl hnat (isType_nat hprim hnat rfl) hbeqE
      (fun α hα => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hα
        rcases hα with rfl | rfl <;> exact ⟨by simp [FVarsIn], trivial, rfl⟩))
      fun _ _ _ hcond => ?_
    obtain ⟨hiteE, hditeF⟩ := hcond
    obtain ⟨AN, INx, hAN, hANc, hIN, hINc, hRCN⟩ :=
      hiteE (.const ``Nat []) (by simp)
    obtain ⟨AB, IBx, hAB, hABc, hIB, hIBc, hRCB⟩ :=
      hiteE (.const ``Bool []) (by simp)
    cases trExprS_iteNat_inv' hIN
    cases trExprS_iteBool_inv' hIB
    obtain ⟨FD, OT, OF, PR, hFD, hOT, hOF, hRD⟩ := hditeF rfl
    cases trExprS_diteNat_inv' hFD
    refine M.WF.bind (Condition.check.WF_boolCond (c := .mk' wf .safe [] fuel)
      (fun {_ _ _ _} => .throw) rfl rfl
      (fun α hα => by
        cases List.mem_singleton.1 hα; exact ⟨by simp [FVarsIn], trivial, rfl⟩))
      fun _ _ _ hcondB => ?_
    obtain ⟨PB, DB, hPB, hDB, hPBc, hDBc, hiteB⟩ := hcondB
    obtain ⟨Anat2, IN2, hAnat2, hAnatc2, hIN2, hINc2, hB1⟩ :=
      hiteB (.const ``Nat []) (List.mem_singleton.2 rfl)
    cases trExprS_iteNat_inv' hIN2
    refine M.WF.bind (M.WF.withCheckedLocalDecl
      (Q := fun u _ => Environment.NatWFUnfold.Good u) (by simp [FVarsIn]) ?_)
      fun u _ _ hu => ?_
    · intro tyf idf cwff s1 _ htyf _
      cases trExprS_boolArrow2_inv htyf
      refine M.WF.withCheckedLocalDecl (by simp [FVarsIn]) ?_
      intro tyn idn cwfn s2 _ htyn _
      cases trExprS_const_nil_inv' htyn
      refine M.WF.withCheckedLocalDecl (by simp [FVarsIn]) ?_
      intro tym idm cwfm s3 _ htym _
      cases trExprS_const_nil_inv' htym
      have hF3 := TrExprS.weakLam0 cwfm (TrExprS.weakLam0 cwfn
        (TrExprS.weakLam0 cwff hF hFc) hFc) hFc
      have hFty3 := HasType.weakLam0 cwfm (HasType.weakLam0 cwfn
        (HasType.weakLam0 cwff hFty hFc (by repeat' first | exact trivial | refine ⟨?_, ?_⟩)) hFc
        (by repeat' first | exact trivial | refine ⟨?_, ?_⟩)) hFc
        (by repeat' first | exact trivial | refine ⟨?_, ?_⟩)
      have hfv := TrExprS.weakLift0 cwfm (TrExprS.weakLift0 cwfn (trExprS_lastFVar0 cwff))
      have hnv := TrExprS.weakLift0 cwfm (trExprS_lastFVar0 cwfn)
      have hmv := trExprS_lastFVar0 cwfm
      have hbbbc : (VExpr.forallE VExpr.bool (VExpr.forallE VExpr.bool VExpr.bool)).ClosedN 0 := by
        repeat' first | exact trivial | refine ⟨?_, ?_⟩
      have hfty := HasType.weakLift0 cwfm (hasType_fvar1 cwff cwfn hbbbc)
      have hnty := hasType_fvar1 cwfn cwfm trivial
      have hmty := hasType_lastFVar0 cwfm trivial
      have hcl2 : (VExpr.forallE .nat (.forallE .nat .nat)).ClosedN 0 := by
        repeat' first | exact trivial | refine ⟨?_, ?_⟩
      have hcl1 : (VExpr.forallE .nat .nat).ClosedN 0 := by
        repeat' first | exact trivial | refine ⟨?_, ?_⟩
      have hv1 := trExprS_appD hF3 hFty3 hfv hfty
      rw [hcl2.instN_eq (Nat.zero_le _)] at hv1
      have hv2 := trExprS_appD hv1.1 hv1.2 hnv hnty
      rw [hcl1.instN_eq (Nat.zero_le _)] at hv2
      have hv3 := trExprS_appD hv2.1 hv2.2 hmv hmty
      exact unfoldNatWellFounded.WF (fun {_ _ _} => .throw) ⟨_, hv3.1⟩
    have hgoFV : u.go.FVarsIn (· ∈ (VContext.mk' wf .safe ([] : List Name) fuel).vlctx.fvars) :=
      hu.goFV.mono nofun
    have halFV : u.alpha.FVarsIn
        (· ∈ (VContext.mk' wf .safe ([] : List Name) fuel).vlctx.fvars) := hu.alphaFV.mono nofun
    have hmsFV : u.measure.FVarsIn
        (· ∈ (VContext.mk' wf .safe ([] : List Name) fuel).vlctx.fvars) := hu.measFV.mono nofun
    have hmoFV : u.motive.FVarsIn
        (· ∈ (VContext.mk' wf .safe ([] : List Name) fuel).vlctx.fvars) := hu.motiveFV.mono nofun
    have hpkFV : u.pack.FVarsIn
        (· ∈ (VContext.mk' wf .safe ([] : List Name) fuel).vlctx.fvars) := hu.packFV.mono nofun
    refine M.WF.bind (checkedTypeIs.WF hgoFV
      (by
        simp only [Lean4Lean.Environment.NatWFUnfold.goType, FVarsIn, Lean.mkApp2, Lean.mkApp]
        repeat' apply And.intro
        all_goals first
          | exact halFV | exact hmsFV | exact hmoFV
          | simp [Lean.Level.hasMVar'] | trivial)) fun _ _ _ hgt => ?_
    split
    case isFalse => exact M.WF.bindThrow .throw
    rename_i hgb
    obtain ⟨GOABS, GOA, GOTY, hGO, hGOA, hGOTY, hGOd⟩ := hgt
    refine M.WF.bind (checkedTypeIs.WF hmsFV
      (by
        simp only [FVarsIn]
        repeat' apply And.intro
        all_goals first | exact halFV | simp [Lean.Level.hasMVar'] | trivial))
      fun _ _ _ hmt => ?_
    split
    case isFalse => exact M.WF.bindThrow .throw
    rename_i hmb
    obtain ⟨MEAS, MEASA, MTY, hMEAS, hMEASA, hMTY, hMEASd⟩ := hmt
    obtain ⟨A, natA, rfl, hAlpha, hNatA⟩ := trExprS_arrow_inv' hMTY
    cases trExprS_const_nil_inv' hNatA
    have hMEASty : (ves.venv .safe).HasType 0 [] MEAS (.forallE A .nat) :=
      hMEASA.defeqU_r henv0 (VContext.mk' wf .safe ([] : List Name) fuel).Δwf.toCtx
        (hMEASd (by simpa using hmb))
    obtain ⟨hMEASc, hMTYc⟩ := closedN_of_nil (c := VContext.mk' wf .safe ([] : List Name) fuel)
      rfl hMEASty
    have hAc : A.ClosedN 0 := hMTYc.1
    have halB : u.alpha.looseBVarRange' = 0 := trExprS_looseBVarRange_nil hAlpha
    have hmsB : u.measure.looseBVarRange' = 0 := trExprS_looseBVarRange_nil hMEAS
    have hgoB : u.go.looseBVarRange' = 0 := trExprS_looseBVarRange_nil hGO
    refine M.WF.bind (checkedTypeIs.WF hpkFV
      (by
        simp only [FVarsIn]
        repeat' apply And.intro
        all_goals first | exact halFV | simp [Lean.Level.hasMVar'] | trivial))
      fun _ _ _ hpt => ?_
    split
    case isFalse => exact M.WF.bindThrow .throw
    rename_i hpb
    obtain ⟨PACK, PACKA, PTY, hPACK, hPACKA, hPTY, hPACKd⟩ := hpt
    obtain ⟨B0, B1, rfl, hb0, hB1'⟩ := trExprS_arrow_inv' hPTY
    cases trExprS_boolArrow2_inv' hb0
    obtain ⟨n2, B2, rfl, hn2, hB2'⟩ := trExprS_arrow_inv' hB1'
    cases trExprS_const_nil_inv' hn2
    obtain ⟨n3, B3, rfl, hn3, hA3⟩ := trExprS_arrow_inv' hB2'
    cases trExprS_const_nil_inv' hn3
    cases TrExprS.unique hu.alphaU hA3
      (trExprS_weakBV0 henv0.ordered (trExprS_weakBV0 henv0.ordered
        (trExprS_weakBV0 henv0.ordered hAlpha halB hAc) halB hAc) halB hAc)
    have hPACKty : (ves.venv .safe).HasType 0 [] PACK
        (.forallE .boolBoolBool (.forallE .nat (.forallE .nat A))) :=
      hPACKA.defeqU_r henv0 (VContext.mk' wf .safe ([] : List Name) fuel).Δwf.toCtx
        (hPACKd (by simpa using hpb))
    obtain ⟨hPACKc, hPTYc⟩ := closedN_of_nil
      (c := VContext.mk' wf .safe ([] : List Name) fuel) rfl hPACKty
    have hpkB : u.pack.looseBVarRange' = 0 := trExprS_looseBVarRange_nil hPACK
    obtain ⟨BBB, GOTY2, rfl, hbbb, hGOTY2⟩ := trExprS_arrow_inv' hGOTY
    cases trExprS_boolArrow2_inv' hbbb
    obtain ⟨D, rfl⟩ := trExprS_goTypeWF_inv' henv0.ordered
      (trExprS_weakBV0 henv0.ordered hAlpha halB hAc) hu.alphaU halB hAc
      (trExprS_weakBV0 henv0.ordered hMEAS hmsB hMEASc) hu.measU hmsB hMEASc hGOTY2
    have hGOty : (ves.venv .safe).HasType 0 [] GOABS
        (.forallE .boolBoolBool (.goTypeWF A MEAS D)) :=
      hGOA.defeqU_r henv0 (VContext.mk' wf .safe ([] : List Name) fuel).Δwf.toCtx
        (hGOd (by simpa using hgb))
    obtain ⟨hGOc, hGOTYc⟩ := closedN_of_nil
      (c := VContext.mk' wf .safe ([] : List Name) fuel) rfl hGOty
    have hbbbc : (VExpr.forallE VExpr.bool (VExpr.forallE VExpr.bool VExpr.bool)).ClosedN 0 := by
      repeat' first | exact trivial | refine ⟨?_, ?_⟩
    refine M.WF.bind (M.WF.withCheckedLocalDecl (Q := fun _ _ =>
        ∀ env', (ves.venv .safe) ≤ env' → env'.WF →
          ∀ (F₀ : VExpr) (g : Bool → Bool → Bool), env'.ReflectsBoolBoolBool F₀ g →
          ∀ a b : Nat, env'.IsDefEqU 0 [] (VExpr.app3 F F₀ (.natLit a) (.natLit b))
            (.natLit (Nat.bitwise g a b)))
      (by simp [FVarsIn]) ?_) fun _ _ _ hbw => ?_
    · intro tyf idf cwff s1 _ htyf _
      cases trExprS_boolArrow2_inv htyf
      refine M.WF.withCheckedLocalDecl (by simp [FVarsIn]) ?_
      intro tyn idn cwfn s2 _ htyn _
      cases trExprS_const_nil_inv' htyn
      refine M.WF.withCheckedLocalDecl (by simp [FVarsIn]) ?_
      intro tym idm cwfm s3 _ htym _
      cases trExprS_const_nil_inv' htym
      have hGO3 := TrExprS.weakLam0 cwfm (TrExprS.weakLam0 cwfn
        (TrExprS.weakLam0 cwff hGO hGOc) hGOc) hGOc
      have hPACK3 := TrExprS.weakLam0 cwfm (TrExprS.weakLam0 cwfn
        (TrExprS.weakLam0 cwff hPACK hPACKc) hPACKc) hPACKc
      have hMEAS3 := TrExprS.weakLam0 cwfm (TrExprS.weakLam0 cwfn
        (TrExprS.weakLam0 cwff hMEAS hMEASc) hMEASc) hMEASc
      have hPB3 := TrExprS.weakLam0 cwfm (TrExprS.weakLam0 cwfn
        (TrExprS.weakLam0 cwff hPB hPBc) hPBc) hPBc
      have hDB3 := TrExprS.weakLam0 cwfm (TrExprS.weakLam0 cwfn
        (TrExprS.weakLam0 cwff hDB hDBc) hDBc) hDBc
      have hPACKty3 := HasType.weakLam0 cwfm (HasType.weakLam0 cwfn
        (HasType.weakLam0 cwff hPACKty hPACKc hPTYc) hPACKc hPTYc) hPACKc hPTYc
      have hMEASty3 := HasType.weakLam0 cwfm (HasType.weakLam0 cwfn
        (HasType.weakLam0 cwff hMEASty hMEASc hMTYc) hMEASc hMTYc) hMEASc hMTYc
      have hGOty3 := HasType.weakLam0 cwfm (HasType.weakLam0 cwfn
        (HasType.weakLam0 cwff hGOty hGOc hGOTYc) hGOc hGOTYc) hGOc hGOTYc
      have hF3 := TrExprS.weakLam0 cwfm (TrExprS.weakLam0 cwfn
        (TrExprS.weakLam0 cwff hF hFc) hFc) hFc
      have hFty3 := HasType.weakLam0 cwfm (HasType.weakLam0 cwfn
        (HasType.weakLam0 cwff hFty hFc
          (by repeat' first | exact trivial | refine ⟨?_, ?_⟩)) hFc
          (by repeat' first | exact trivial | refine ⟨?_, ?_⟩)) hFc
          (by repeat' first | exact trivial | refine ⟨?_, ?_⟩)
      have hfv := TrExprS.weakLift0 cwfm (TrExprS.weakLift0 cwfn (trExprS_lastFVar0 cwff))
      have hnv := TrExprS.weakLift0 cwfm (trExprS_lastFVar0 cwfn)
      have hmv := trExprS_lastFVar0 cwfm
      have hfty := HasType.weakLift0 cwfm (hasType_fvar1 cwff cwfn hbbbc)
      have hnty := hasType_fvar1 cwfn cwfm trivial
      have hmty := hasType_lastFVar0 cwfm trivial
      obtain ⟨hpk, hpkty⟩ := trExprS_packApp3 hPACK3 hPACKty3 hAc hfv hfty hnv hnty hmv hmty
      obtain ⟨hmeasApp, hmeasAppTy⟩ := trExprS_measApp hMEAS3 hMEASty3 hpk hpkty
      refine M.WF.bind (checkedIsDefEq.WF' hmeasApp hnv) fun r1 _ _ hd1 => ?_
      split
      case isFalse => exact M.WF.bindThrow .throw
      rename_i hr1
      have hmeas := hd1 (by simpa using hr1)
      have hcl2 : (VExpr.forallE .nat (.forallE .nat .nat)).ClosedN 0 := by
        repeat' first | exact trivial | refine ⟨?_, ?_⟩
      have hcl1 : (VExpr.forallE .nat .nat).ClosedN 0 := by
        repeat' first | exact trivial | refine ⟨?_, ?_⟩
      have hw1 := trExprS_appD hF3 hFty3 hfv hfty
      rw [hcl2.instN_eq (Nat.zero_le _)] at hw1
      have hw2 := trExprS_appD hw1.1 hw1.2 hnv hnty
      rw [hcl1.instN_eq (Nat.zero_le _)] at hw2
      have hw3 := trExprS_appD hw2.1 hw2.2 hmv hmty
      refine M.WF.bind (checkedIsDefEq.WFr hw3.1
        (by
          simp only [Lean4Lean.Environment.Condition.ite, Lean4Lean.Environment.Condition.bool,
            Lean.mkApp5, Lean.mkApp3, Lean.mkApp2, Lean.mkApp, Lean.mkAppN, FVarsIn]
          repeat' apply And.intro
          all_goals first
            | exact hu.goFV.mono nofun | exact hu.packFV.mono nofun
            | exact hu.measFV.mono nofun | exact hu.prfAFV.mono nofun
            | exact hfv.fvarsIn | exact hnv.fvarsIn | exact hmv.fvarsIn
            | simp [FVarsIn, Lean.Level.hasMVar'] | trivial))
        fun r2 _ _ hh2 => ?_
      obtain ⟨R2, hR2, hd2⟩ := hh2
      split
      case isFalse => exact M.WF.bindThrow .throw
      rename_i hr2
      have hent0 := hd2 (by simpa using hr2)
      obtain ⟨PRFA, rfl⟩ := trExprS_bitwiseEntry_inv' hGO3 hu.goU hPACK3 hu.packU
        hMEAS3 hu.measU hPB3 hDB3 hfv hnv hmv hR2
      refine M.WF.withCheckedLocalDecl (by simp [FVarsIn]) ?_
      intro tyfu idfu cwffu s4 _ htyfu _
      cases trExprS_const_nil_inv' htyfu
      have hfv4 := TrExprS.weakLift0 cwffu hfv
      have hnv4 := TrExprS.weakLift0 cwffu hnv
      have hmv4 := TrExprS.weakLift0 cwffu hmv
      have hfuv4 := trExprS_lastFVar0 cwffu
      have hMEAS4 := TrExprS.weakLam0 cwffu hMEAS3 hMEASc
      have hPACK4 := TrExprS.weakLam0 cwffu hPACK3 hPACKc
      have hGO4 := TrExprS.weakLam0 cwffu hGO3 hGOc
      refine M.WF.withCheckedLocalDecl (by
        simp only [Lean.mkApp2, Lean.mkApp, FVarsIn]
        repeat' apply And.intro
        all_goals first
          | exact hMEAS4.fvarsIn | exact hPACK4.fvarsIn
          | exact hfv4.fvarsIn | exact hnv4.fvarsIn | exact hmv4.fvarsIn | exact hfuv4.fvarsIn
          | simp [FVarsIn, Lean.Level.hasMVar'] | trivial) ?_
      intro tyh idh cwfh s5 _ htyh _
      obtain ⟨XA, FUA, rfl, mh1, mh2⟩ := trExprS_natLEApp_inv' htyh
      obtain ⟨_, _, rfl, k1, k2⟩ := trExprS_app_inv' mh1
      cases trExprS_const_nil_inv' k1
      obtain ⟨_, _, rfl, k3, k4⟩ := trExprS_app_inv' k2
      cases TrExprS.unique hu.measU k3 hMEAS4
      obtain ⟨_, _, rfl, k5, k6⟩ := trExprS_app_inv' k4
      obtain ⟨_, _, rfl, k7, k8⟩ := trExprS_app_inv' k5
      obtain ⟨_, _, rfl, k9, k10⟩ := trExprS_app_inv' k7
      cases TrExprS.unique hu.packU k9 hPACK4
      cases trExprS_fvar_uniq k10 hfv4
      cases trExprS_fvar_uniq k8 hnv4
      cases trExprS_fvar_uniq k6 hmv4
      cases trExprS_succFvar_inv' hfuv4 mh2
      have hfv5 := TrExprS.weakLift0 cwfh hfv4
      have hnv5 := TrExprS.weakLift0 cwfh hnv4
      have hmv5 := TrExprS.weakLift0 cwfh hmv4
      have hfuv5 := TrExprS.weakLift0 cwfh hfuv4
      have hhv5 := trExprS_lastFVar0 cwfh
      have hMEAS5 := TrExprS.weakLam0 cwfh hMEAS4 hMEASc
      have hPACK5 := TrExprS.weakLam0 cwfh hPACK4 hPACKc
      have hGO5 := TrExprS.weakLam0 cwfh hGO4 hGOc
      have hPB5 := TrExprS.weakLam0 cwfh (TrExprS.weakLam0 cwffu hPB3 hPBc) hPBc
      have hDB5 := TrExprS.weakLam0 cwfh (TrExprS.weakLam0 cwffu hDB3 hDBc) hDBc
      have hfty5 := HasType.weakLift0 cwfh (HasType.weakLift0 cwffu hfty)
      have hnty5 := HasType.weakLift0 cwfh (HasType.weakLift0 cwffu hnty)
      have hmty5 := HasType.weakLift0 cwfh (HasType.weakLift0 cwffu hmty)
      have hfuty5 := HasType.weakLift0 cwfh (hasType_lastFVar0 cwffu trivial)
      have hPACKty5 := HasType.weakLam0 cwfh (HasType.weakLam0 cwffu
        (HasType.weakLam0 cwfm (HasType.weakLam0 cwfn
          (HasType.weakLam0 cwff hPACKty hPACKc hPTYc) hPACKc hPTYc) hPACKc hPTYc)
        hPACKc hPTYc) hPACKc hPTYc
      have hGOty5 := HasType.weakLam0 cwfh (HasType.weakLam0 cwffu
        (HasType.weakLam0 cwfm (HasType.weakLam0 cwfn
          (HasType.weakLam0 cwff hGOty hGOc hGOTYc) hGOc hGOTYc) hGOc hGOTYc)
        hGOc hGOTYc) hGOc hGOTYc
      obtain ⟨hpk5, hpkty5⟩ := trExprS_packApp3 hPACK5 hPACKty5 hAc hfv5 hfty5
        hnv5 hnty5 hmv5 hmty5
      have hsf5 := trExprS_succ hfuv5 hfuty5 hprim hnat
      have hgoapp := trExprS_appD hGO5 hGOty5 hfv5 hfty5
      have hhty5 := hasType_lastFVar (cwf := cwfh)
      simp only [VExpr.natLEApp, VExpr.natLE, VExpr.lift, VExpr.liftN, Lean4Lean.liftVar,
        hMEASc.liftN_eq (Nat.zero_le _), hPACKc.liftN_eq (Nat.zero_le _)] at hhty5
      have hlhsGo := trExprS_goAppWF hgoapp.1
        (hasType_goApply hAc hMEASc hGOty5 hfty5) hAc hMEASc
        hsf5.1 hsf5.2 hpk5 hpkty5 hhv5 hhty5
      refine M.WF.bind (checkedIsDefEq.WFr hlhsGo
        (by
          simp only [Lean4Lean.Environment.Condition.dite, Lean4Lean.Environment.Condition.ite,
            Lean4Lean.Environment.Condition.decide, Lean4Lean.Environment.Condition.natEq,
            Lean4Lean.Environment.Condition.bool, Lean.Expr.lam0, Lean.mkApp5, Lean.mkApp4,
            Lean.mkApp3, Lean.mkApp2, Lean.mkApp, Lean.mkAppN, FVarsIn]
          repeat' apply And.intro
          all_goals first
            | exact hu.goFV.mono nofun | exact hu.packFV.mono nofun
            | exact hfv5.fvarsIn | exact hnv5.fvarsIn | exact hmv5.fvarsIn
            | exact hfuv5.fvarsIn | exact hhv5.fvarsIn
            | simp [FVarsIn, Lean.Level.hasMVar'] | trivial))
        fun r3 _ _ hh3 => ?_
      obtain ⟨R3, hR3, hd3⟩ := hh3
      split
      case isFalse => exact .throw
      rename_i hr3
      have hgoeq0 := hd3 (by simpa using hr3)
      obtain ⟨EA, KA, rfl⟩ := trExprS_bitwiseGo_inv' henv0.ordered hGO5 hu.goU hgoB hGOc
        hPACK5 hu.packU hpkB hPACKc hPB5 hPBc hDB5 hDBc
        (by repeat' first | exact trivial | refine ⟨?_, ?_⟩)
        hfv5 hnv5 hmv5 hfuv5 hR3
      refine .pure fun env' hle henv' F₀ g hf a b => ?_
      exact VEnv.reflects_bitwise_of_equations henv' (hlit.mono hle)
        ((hprim.natSucc_hasType hnat).mono hle)
        (fun a b => ((hprim.natBEq hbeq) a b).mono hle)
        (fun a b => ((hprim.natAdd haddP) a b).mono hle)
        (fun a b => ((hprim.natDiv hdivP) a b).mono hle)
        (fun a b => ((hprim.natMod hmodP) a b).mono hle)
        hFc hGOc hPACKc hMEASc hAc
        (by repeat' first | exact trivial | refine ⟨?_, ?_⟩)
        (by repeat' first | exact trivial | refine ⟨?_, ?_⟩)
        (by repeat' first | exact trivial | refine ⟨?_, ?_⟩)
        (by repeat' first | exact trivial | refine ⟨?_, ?_⟩)
        hPBc hDBc (hGOty.mono hle) hf
        (hRCN env' hle henv') (hRCB env' hle henv') (hB1 env' hle henv') (hRD env' hle henv')
        (hmeas.mono hle) (hent0.mono hle) (hgoeq0.mono hle) a b
    · refine .pure ⟨fun _ => (by simpa using hsafe), fun _ => rfl, ?_⟩
      intro _ sf venv env'' ci' hle hwf' hprim2 htr hci hadd
      refine preserves_glue (nm := ``Nat.bitwise) (F := F) hname rfl rfl (by decide) hF ?_
        hle hwf' hprim2 htr hci hadd
      intro venv' env₂ hle' hle₂ henv₂ hprim3 hdefF
      exact VEnv.primField_Nat_bitwise.2 (reflectsNatBitwise_of_open henv₂ hdefF
        (fun env' hle3 henv' F₀ g hf a b =>
          hbw env' ((hle'.trans hle₂).trans hle3) henv' F₀ g hf a b))
  · rename_i hname; subst hname; simp at hrest -- ``Nat.land
  · rename_i hname; subst hname; simp at hrest -- ``Nat.lor
  · rename_i hname; subst hname; simp at hrest -- ``Nat.xor
  · rename_i hname; subst hname; simp at hrest -- ``Nat.shiftLeft
  · rename_i hname; subst hname; simp at hrest -- ``Nat.shiftRight
  · rename_i hname; subst hname; simp at hrest -- ``Char.ofNat
  · rename_i hname; subst hname; simp at hrest -- ``String.ofList
  · exact .pure ⟨nofun, nofun, nofun⟩

set_option maxHeartbeats 2000000 in
theorem checkPrimitiveDef.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (fuel : FuelConfig := {}) :
    (Environment.checkPrimitiveDef v).WF (.mk' wf .safe v.levelParams fuel) {} fun allow _ =>
      PrimitiveResult (ves.venv .safe) v allow := by
  obtain ⟨⟨name, lparams, type⟩, value, hints, safety, all⟩ := v
  by_cases hrest : name = ``Nat.mod ∨ name = ``Nat.div ∨ name = ``Nat.gcd ∨
      name = ``Nat.bitwise
  · exact checkPrimitiveDef.WF.rest wf _ fuel hrest
  simp only [not_or] at hrest
  obtain ⟨hrmod, hrdiv, hrgcd, hrbit⟩ := hrest
  have hfail {α : Type} {s' : VState} {Q : α → VState → Prop} {msg} :
      M.WF (.mk' wf .safe lparams fuel) s' (throw (Exception.other msg) : M α) Q := .throw
  unfold Environment.checkPrimitiveDef
  split
  case isFalse => exact .pure { safe := nofun, no_level_params := nofun, preserves := nofun }
  rename_i hsafe
  refine M.WF.bind getEnv.WF fun _ _ _ h => ?_
  obtain ⟨rfl, rfl⟩ := h
  split
  · -- Nat.add
    rename_i hname
    split
    case isFalse => exact M.WF.bindThrow .throw
    rename_i hguard
    simp only [Bool.and_eq_true, List.isEmpty_iff] at hguard
    obtain ⟨hnatE, rfl⟩ := hguard
    refine (checkPrimValue.WF (fun {_} {_} {_} => hfail) (by simp [FVarsIn])).bind
      fun _ _ _ h => ?_
    obtain ⟨ty', F, hty', hF, hFty⟩ := h
    cases trExprS_natArrow2_inv hty'
    have hnf := NatFacts.of_arrow hty'
    have hnat := hnf.contains
    have hprim := (VContext.mk' wf .safe ([] : List Name) fuel).hasPrimitives
    obtain ⟨hFc, -⟩ := closedN_of_nil rfl hFty
    -- defeq1 : add x 0 ≡ x
    refine M.WF.bind (M.WF.withLocalDecl0 (name := `x) (bi := .default) hnf.tr hnf.isType
      (Q := fun b _ => b = true → (ves.venv .safe).IsDefEqU 0 [VExpr.nat]
        (.app (.app F (.bvar 0)) .natZero) (.bvar 0)) ?_) fun b _ _ hb => ?_
    · intro idx cwfx s'' _ _
      have hF' := TrExprS.weakLam0 cwfx hF hFc
      have hFty' := HasType.weakLam0 cwfx hFty hFc ⟨trivial, trivial, trivial⟩
      have hx := trExprS_lastFVar0 cwfx
      have hxty := hasType_lastFVar0 cwfx trivial
      exact checkedIsDefEq.WF' (trExprS_app2_nat hF' hFty' hx hxty
        (TrExprS.natZero hprim hnat).1 (TrExprS.natZero hprim hnat).2).1 hx
    split
    case isFalse => exact M.WF.bindThrow .throw
    rename_i hb1
    have h0 := hb (by simpa using hb1)
    refine M.WF.bind (M.WF.withLocalDecl0 (name := `y) (bi := .default) hnf.tr hnf.isType
      (Q := fun b _ => b = true → (ves.venv .safe).IsDefEqU 0 [VExpr.nat, VExpr.nat]
        (.app (.app F (.bvar 1)) (.app .natSucc (.bvar 0)))
        (.app .natSucc (.app (.app F (.bvar 1)) (.bvar 0)))) ?_) fun b2 _ _ hb2 => ?_
    · intro idy cwfy s2 _ _
      have hnf1 := NatFacts.weakLam0 cwfy hnf
      refine M.WF.withLocalDecl0 (name := `x) (bi := .default) hnf1.tr hnf1.isType ?_
      intro idx cwfx s3 _ _
      have hF2 := TrExprS.weakLam0 cwfx (TrExprS.weakLam0 cwfy hF hFc) hFc
      have hFty2 := HasType.weakLam0 cwfx
        (HasType.weakLam0 cwfy hFty hFc ⟨trivial, trivial, trivial⟩) hFc ⟨trivial, trivial, trivial⟩
      have hy := TrExprS.weakLift0 cwfx (trExprS_lastFVar0 cwfy)
      have hyty := hasType_fvar1 cwfy cwfx trivial
      have hx := trExprS_lastFVar0 cwfx
      have hxty := hasType_lastFVar0 cwfx trivial
      have hsx := trExprS_succ hx hxty hprim hnat
      have hyx := trExprS_app2_nat hF2 hFty2 hy hyty hx hxty
      exact checkedIsDefEq.WF' (trExprS_app2_nat hF2 hFty2 hy hyty hsx.1 hsx.2).1
        (trExprS_succ hyx.1 hyx.2 hprim hnat).1
    split
    case isFalse => exact M.WF.bindThrow .throw
    rename_i hb3
    have hS := hb2 (by simpa using hb3)
    refine .pure ?_
    have hfi : ∀ (e : VExpr) (k : Nat), F.inst e k = F := fun _ _ => hFc.instN_eq (Nat.zero_le _)
    refine ⟨fun _ => (by simpa using hsafe), fun _ => rfl, ?_⟩
    intro _ sf venv env'' ci' hle hwf hprim2 htr hci hadd
    refine preserves_glue (nm := ``Nat.add) (F := F) hname rfl rfl (by decide) hF ?_
      hle hwf hprim2 htr hci hadd
    intro venv' env₂ hle' hle₂ henv₂ hprim3 hdefF
    have hle3 := hle'.trans hle₂
    refine VEnv.primField_Nat_add.2 (reflectsNNN_of_open hle₂ henv₂ hprim3
      (VEnv.contains.mono hle' hnat) hdefF (hFty.mono hle3) fun hlit a b => ?_)
    refine VEnv.reflects_natAdd henv₂ hlit ?_ ?_ a b
    · intro a'
      have := VEnv.IsDefEqU.instNat henv₂ hlit (h0.mono hle3) a'
      simpa [VExpr.inst, VExpr.instVar, hfi] using this
    · intro a' b'
      have := VEnv.IsDefEqU.instNat2 henv₂ hlit (hS.mono hle3) a' b'
      simpa [VExpr.inst, VExpr.instVar, hfi] using this
  · -- Nat.pred
    rename_i hname
    split
    case isFalse => exact M.WF.bindThrow .throw
    rename_i hguard
    simp only [Bool.and_eq_true, List.isEmpty_iff] at hguard
    obtain ⟨hnatE, rfl⟩ := hguard
    refine (checkPrimValue.WF (fun {_} {_} {_} => hfail) (by simp [FVarsIn])).bind
      fun _ _ _ h => ?_
    obtain ⟨ty', F, hty', hF, hFty⟩ := h
    cases trExprS_natArrow1_inv hty'
    have hnf := NatFacts.of_arrow hty'
    have hnat := hnf.contains
    have hprim := (VContext.mk' wf .safe ([] : List Name) fuel).hasPrimitives
    obtain ⟨hFc, -⟩ := closedN_of_nil rfl hFty
    have hfi : ∀ (e : VExpr) (k : Nat), F.inst e k = F := fun _ _ => hFc.instN_eq (Nat.zero_le _)
    refine M.WF.bind (checkedIsDefEq.WF'
      (trExprS_app1_nat hF hFty (TrExprS.natZero hprim hnat).1 (TrExprS.natZero hprim hnat).2).1
      (TrExprS.natZero hprim hnat).1) fun b _ _ hb => ?_
    split
    case isFalse => exact M.WF.bindThrow .throw
    rename_i hb1
    have h0 := hb (by simpa using hb1)
    refine M.WF.bind (M.WF.withLocalDecl0 (name := `x) (bi := .default) hnf.tr hnf.isType
      (Q := fun b _ => b = true → (ves.venv .safe).IsDefEqU 0 [VExpr.nat]
        (.app F (.app .natSucc (.bvar 0))) (.bvar 0)) ?_) fun b2 _ _ hb2 => ?_
    · intro idx cwfx s2 _ _
      have hF' := TrExprS.weakLam0 cwfx hF hFc
      have hFty' := HasType.weakLam0 cwfx hFty hFc ⟨trivial, trivial⟩
      have hx := trExprS_lastFVar0 cwfx
      have hxty := hasType_lastFVar0 cwfx trivial
      have hsx := trExprS_succ hx hxty hprim hnat
      exact checkedIsDefEq.WF' (trExprS_app1_nat hF' hFty' hsx.1 hsx.2).1 hx
    split
    case isFalse => exact M.WF.bindThrow .throw
    rename_i hb3
    have hS := hb2 (by simpa using hb3)
    refine .pure ⟨fun _ => (by simpa using hsafe), fun _ => rfl, ?_⟩
    intro _ sf venv env'' ci' hle hwf hprim2 htr hci hadd
    refine preserves_glue (nm := ``Nat.pred) (F := F) hname rfl rfl (by decide) hF ?_
      hle hwf hprim2 htr hci hadd
    intro venv' env₂ hle' hle₂ henv₂ hprim3 hdefF
    have hle3 := hle'.trans hle₂
    refine VEnv.primField_Nat_pred.2 (reflectsNN_of_open hle₂ henv₂ hprim3
      (VEnv.contains.mono hle' hnat) hdefF (hFty.mono hle3) fun hlit => ?_)
    refine VEnv.reflects_natPred (h0.mono hle3) fun a' => ?_
    have := VEnv.IsDefEqU.instNat henv₂ hlit (hS.mono hle3) a'
    simpa [VExpr.inst, VExpr.instVar, hfi] using this
  · -- Nat.sub
    rename_i hname
    split
    case isFalse => exact M.WF.bindThrow .throw
    rename_i hguard
    simp only [Bool.and_eq_true, List.isEmpty_iff] at hguard
    obtain ⟨⟨hnatE, hpredE⟩, rfl⟩ := hguard
    refine (checkPrimValue.WF (fun {_} {_} {_} => hfail) (by simp [FVarsIn])).bind
      fun _ _ _ h => ?_
    obtain ⟨ty', F, hty', hF, hFty⟩ := h
    cases trExprS_natArrow2_inv hty'
    have hnf := NatFacts.of_arrow hty'
    have hnat := hnf.contains
    have hprim := (VContext.mk' wf .safe ([] : List Name) fuel).hasPrimitives
    have hpredC := contains_primConst (c := VContext.mk' wf .safe ([] : List Name) fuel)
      rfl hpredE primitives_natPred
    obtain ⟨hFc, -⟩ := closedN_of_nil rfl hFty
    have hfi : ∀ (e : VExpr) (k : Nat), F.inst e k = F := fun _ _ => hFc.instN_eq (Nat.zero_le _)
    refine M.WF.bind (M.WF.withLocalDecl0 (name := `x) (bi := .default) hnf.tr hnf.isType
      (Q := fun b _ => b = true → (ves.venv .safe).IsDefEqU 0 [VExpr.nat]
        (.app (.app F (.bvar 0)) .natZero) (.bvar 0)) ?_) fun b _ _ hb => ?_
    · intro idx cwfx s'' _ _
      have hF' := TrExprS.weakLam0 cwfx hF hFc
      have hFty' := HasType.weakLam0 cwfx hFty hFc ⟨trivial, trivial, trivial⟩
      have hx := trExprS_lastFVar0 cwfx
      have hxty := hasType_lastFVar0 cwfx trivial
      exact checkedIsDefEq.WF' (trExprS_app2_nat hF' hFty' hx hxty
        (TrExprS.natZero hprim hnat).1 (TrExprS.natZero hprim hnat).2).1 hx
    split
    case isFalse => exact M.WF.bindThrow .throw
    rename_i hb1
    have h0 := hb (by simpa using hb1)
    refine M.WF.bind (M.WF.withLocalDecl0 (name := `y) (bi := .default) hnf.tr hnf.isType
      (Q := fun b _ => b = true → (ves.venv .safe).IsDefEqU 0 [VExpr.nat, VExpr.nat]
        (.app (.app F (.bvar 1)) (.app .natSucc (.bvar 0)))
        (.app (.const ``Nat.pred []) (.app (.app F (.bvar 1)) (.bvar 0)))) ?_) fun b2 _ _ hb2 => ?_
    · intro idy cwfy s2 _ _
      have hnf1 := NatFacts.weakLam0 cwfy hnf
      refine M.WF.withLocalDecl0 (name := `x) (bi := .default) hnf1.tr hnf1.isType ?_
      intro idx cwfx s3 _ _
      have hF2 := TrExprS.weakLam0 cwfx (TrExprS.weakLam0 cwfy hF hFc) hFc
      have hFty2 := HasType.weakLam0 cwfx
        (HasType.weakLam0 cwfy hFty hFc ⟨trivial, trivial, trivial⟩) hFc ⟨trivial, trivial, trivial⟩
      have hy := TrExprS.weakLift0 cwfx (trExprS_lastFVar0 cwfy)
      have hyty := hasType_fvar1 cwfy cwfx trivial
      have hx := trExprS_lastFVar0 cwfx
      have hxty := hasType_lastFVar0 cwfx trivial
      have hsx := trExprS_succ hx hxty hprim hnat
      have hyx := trExprS_app2_nat hF2 hFty2 hy hyty hx hxty
      refine (checkedIsDefEq.WFr (trExprS_app2_nat hF2 hFty2 hy hyty hsx.1 hsx.2).1
        (by refine ⟨nofun, hyx.1.fvarsIn⟩)).mono fun r _ _ h => ?_
      obtain ⟨b', hb', hd⟩ := h
      intro hr
      exact VContext.trans (hd hr) (rhs_const_app hb' hyx.1)
    split
    case isFalse => exact M.WF.bindThrow .throw
    rename_i hb3
    have hS := hb2 (by simpa using hb3)
    refine .pure ⟨fun _ => (by simpa using hsafe), fun _ => rfl, ?_⟩
    intro _ sf venv env'' ci' hle hwf hprim2 htr hci hadd
    refine preserves_glue (nm := ``Nat.sub) (F := F) hname rfl rfl (by decide) hF ?_
      hle hwf hprim2 htr hci hadd
    intro venv' env₂ hle' hle₂ henv₂ hprim3 hdefF
    have hle3 := hle'.trans hle₂
    refine VEnv.primField_Nat_sub.2 (reflectsNNN_of_open hle₂ henv₂ hprim3
      (VEnv.contains.mono hle' hnat) hdefF (hFty.mono hle3) fun hlit a b => ?_)
    refine VEnv.reflects_natSub henv₂
      (fun n => (hprim3.natPred (VEnv.contains.mono hle' hpredC) n).mono hle₂) ?_ ?_ a b
    · intro a'
      have := VEnv.IsDefEqU.instNat henv₂ hlit (h0.mono hle3) a'
      simpa [VExpr.inst, VExpr.instVar, hfi] using this
    · intro a' b'
      have := VEnv.IsDefEqU.instNat2 henv₂ hlit (hS.mono hle3) a' b'
      simpa [VExpr.inst, VExpr.instVar, hfi] using this
  · -- ``Nat.mul
    rename_i hname
    split
    case isFalse => exact M.WF.bindThrow .throw
    rename_i hguard
    simp only [Bool.and_eq_true, List.isEmpty_iff] at hguard
    obtain ⟨⟨hnatE, hauxE⟩, rfl⟩ := hguard
    refine (checkPrimValue.WF (fun {_} {_} {_} => hfail) (by simp [FVarsIn])).bind
      fun _ _ _ h => ?_
    obtain ⟨ty', F, hty', hF, hFty⟩ := h
    cases trExprS_natArrow2_inv hty'
    have hnf := NatFacts.of_arrow hty'
    have hnat := hnf.contains
    have hprim := (VContext.mk' wf .safe ([] : List Name) fuel).hasPrimitives
    have hauxC := contains_primConst (c := VContext.mk' wf .safe ([] : List Name) fuel)
      rfl hauxE primitives_natAdd
    obtain ⟨hFc, -⟩ := closedN_of_nil rfl hFty
    have hfi : ∀ (e : VExpr) (k : Nat), F.inst e k = F := fun _ _ => hFc.instN_eq (Nat.zero_le _)
    refine M.WF.bind (M.WF.withLocalDecl0 (name := `x) (bi := .default) hnf.tr hnf.isType
      (Q := fun b _ => b = true → (ves.venv .safe).IsDefEqU 0 [VExpr.nat]
        (.app (.app F (.bvar 0)) .natZero) VExpr.natZero) ?_) fun b _ _ hb => ?_
    · intro idx cwfx s'' _ _
      have hF' := TrExprS.weakLam0 cwfx hF hFc
      have hFty' := HasType.weakLam0 cwfx hFty hFc ⟨trivial, trivial, trivial⟩
      have hx := trExprS_lastFVar0 cwfx
      have hxty := hasType_lastFVar0 cwfx trivial
      exact checkedIsDefEq.WF' (trExprS_app2_nat hF' hFty' hx hxty
        (TrExprS.natZero hprim hnat).1 (TrExprS.natZero hprim hnat).2).1
        (TrExprS.natZero hprim hnat).1
    split
    case isFalse => exact M.WF.bindThrow .throw
    rename_i hb1
    have h0 := hb (by simpa using hb1)
    refine M.WF.bind (M.WF.withLocalDecl0 (name := `y) (bi := .default) hnf.tr hnf.isType
      (Q := fun b _ => b = true → (ves.venv .safe).IsDefEqU 0 [VExpr.nat, VExpr.nat]
        (.app (.app F (.bvar 1)) (.app .natSucc (.bvar 0)))
        (.app (.app (.const ``Nat.add []) (.app (.app F (.bvar 1)) (.bvar 0)))
          (.bvar 1))) ?_) fun b2 _ _ hb2 => ?_
    · intro idy cwfy s2 _ _
      have hnf1 := NatFacts.weakLam0 cwfy hnf
      refine M.WF.withLocalDecl0 (name := `x) (bi := .default) hnf1.tr hnf1.isType ?_
      intro idx cwfx s3 _ _
      have hF2 := TrExprS.weakLam0 cwfx (TrExprS.weakLam0 cwfy hF hFc) hFc
      have hFty2 := HasType.weakLam0 cwfx
        (HasType.weakLam0 cwfy hFty hFc ⟨trivial, trivial, trivial⟩) hFc ⟨trivial, trivial, trivial⟩
      have hy := TrExprS.weakLift0 cwfx (trExprS_lastFVar0 cwfy)
      have hyty := hasType_fvar1 cwfy cwfx trivial
      have hx := trExprS_lastFVar0 cwfx
      have hxty := hasType_lastFVar0 cwfx trivial
      have hsx := trExprS_succ hx hxty hprim hnat
      have hyx := trExprS_app2_nat hF2 hFty2 hy hyty hx hxty
      refine (checkedIsDefEq.WFr (trExprS_app2_nat hF2 hFty2 hy hyty hsx.1 hsx.2).1
        (by refine ⟨⟨nofun, hyx.1.fvarsIn⟩, hy.fvarsIn⟩)).mono fun r _ _ h => ?_
      obtain ⟨b', hb', hd⟩ := h
      intro hr
      exact VContext.trans (hd hr) (rhs_const_app2 hb' hyx.1 hy)
    split
    case isFalse => exact M.WF.bindThrow .throw
    rename_i hb3
    have hS := hb2 (by simpa using hb3)
    refine .pure ⟨fun _ => (by simpa using hsafe), fun _ => rfl, ?_⟩
    intro _ sf venv env'' ci' hle hwf hprim2 htr hci hadd
    refine preserves_glue (nm := ``Nat.mul) (F := F) hname rfl rfl (by decide) hF ?_
      hle hwf hprim2 htr hci hadd
    intro venv' env₂ hle' hle₂ henv₂ hprim3 hdefF
    have hle3 := hle'.trans hle₂
    refine VEnv.primField_Nat_mul.2 (reflectsNNN_of_open hle₂ henv₂ hprim3
      (VEnv.contains.mono hle' hnat) hdefF (hFty.mono hle3) fun hlit a b => ?_)
    refine VEnv.reflects_natMul henv₂
      (fun n m => (hprim3.natAdd (VEnv.contains.mono hle' hauxC) n m).mono hle₂) ?_ ?_ a b
    · intro a'
      have := VEnv.IsDefEqU.instNat henv₂ hlit (h0.mono hle3) a'
      simpa [VExpr.inst, VExpr.instVar, hfi] using this
    · intro a' b'
      have := VEnv.IsDefEqU.instNat2 henv₂ hlit (hS.mono hle3) a' b'
      simpa [VExpr.inst, VExpr.instVar, hfi] using this
  · -- ``Nat.pow
    rename_i hname
    split
    case isFalse => exact M.WF.bindThrow .throw
    rename_i hguard
    simp only [Bool.and_eq_true, List.isEmpty_iff] at hguard
    obtain ⟨⟨hnatE, hauxE⟩, rfl⟩ := hguard
    refine (checkPrimValue.WF (fun {_} {_} {_} => hfail) (by simp [FVarsIn])).bind
      fun _ _ _ h => ?_
    obtain ⟨ty', F, hty', hF, hFty⟩ := h
    cases trExprS_natArrow2_inv hty'
    have hnf := NatFacts.of_arrow hty'
    have hnat := hnf.contains
    have hprim := (VContext.mk' wf .safe ([] : List Name) fuel).hasPrimitives
    have hauxC := contains_primConst (c := VContext.mk' wf .safe ([] : List Name) fuel)
      rfl hauxE primitives_natMul
    obtain ⟨hFc, -⟩ := closedN_of_nil rfl hFty
    have hfi : ∀ (e : VExpr) (k : Nat), F.inst e k = F := fun _ _ => hFc.instN_eq (Nat.zero_le _)
    refine M.WF.bind (M.WF.withLocalDecl0 (name := `x) (bi := .default) hnf.tr hnf.isType
      (Q := fun b _ => b = true → (ves.venv .safe).IsDefEqU 0 [VExpr.nat]
        (.app (.app F (.bvar 0)) .natZero)
        (.app VExpr.natSucc VExpr.natZero)) ?_) fun b _ _ hb => ?_
    · intro idx cwfx s'' _ _
      have hF' := TrExprS.weakLam0 cwfx hF hFc
      have hFty' := HasType.weakLam0 cwfx hFty hFc ⟨trivial, trivial, trivial⟩
      have hx := trExprS_lastFVar0 cwfx
      have hxty := hasType_lastFVar0 cwfx trivial
      refine checkedIsDefEq.WF' (trExprS_app2_nat hF' hFty' hx hxty
        (TrExprS.natZero hprim hnat).1 (TrExprS.natZero hprim hnat).2).1
        (trExprS_succ ?_ ?_ ?_ ?_).1
      · exact (TrExprS.natZero hprim hnat).1
      · exact (TrExprS.natZero hprim hnat).2
      · exact hprim
      · exact hnat
    split
    case isFalse => exact M.WF.bindThrow .throw
    rename_i hb1
    have h0 := hb (by simpa using hb1)
    refine M.WF.bind (M.WF.withLocalDecl0 (name := `y) (bi := .default) hnf.tr hnf.isType
      (Q := fun b _ => b = true → (ves.venv .safe).IsDefEqU 0 [VExpr.nat, VExpr.nat]
        (.app (.app F (.bvar 1)) (.app .natSucc (.bvar 0)))
        (.app (.app (.const ``Nat.mul []) (.app (.app F (.bvar 1)) (.bvar 0)))
          (.bvar 1))) ?_) fun b2 _ _ hb2 => ?_
    · intro idy cwfy s2 _ _
      have hnf1 := NatFacts.weakLam0 cwfy hnf
      refine M.WF.withLocalDecl0 (name := `x) (bi := .default) hnf1.tr hnf1.isType ?_
      intro idx cwfx s3 _ _
      have hF2 := TrExprS.weakLam0 cwfx (TrExprS.weakLam0 cwfy hF hFc) hFc
      have hFty2 := HasType.weakLam0 cwfx
        (HasType.weakLam0 cwfy hFty hFc ⟨trivial, trivial, trivial⟩) hFc ⟨trivial, trivial, trivial⟩
      have hy := TrExprS.weakLift0 cwfx (trExprS_lastFVar0 cwfy)
      have hyty := hasType_fvar1 cwfy cwfx trivial
      have hx := trExprS_lastFVar0 cwfx
      have hxty := hasType_lastFVar0 cwfx trivial
      have hsx := trExprS_succ hx hxty hprim hnat
      have hyx := trExprS_app2_nat hF2 hFty2 hy hyty hx hxty
      refine (checkedIsDefEq.WFr (trExprS_app2_nat hF2 hFty2 hy hyty hsx.1 hsx.2).1
        (by refine ⟨⟨nofun, hyx.1.fvarsIn⟩, hy.fvarsIn⟩)).mono fun r _ _ h => ?_
      obtain ⟨b', hb', hd⟩ := h
      intro hr
      exact VContext.trans (hd hr) (rhs_const_app2 hb' hyx.1 hy)
    split
    case isFalse => exact M.WF.bindThrow .throw
    rename_i hb3
    have hS := hb2 (by simpa using hb3)
    refine .pure ⟨fun _ => (by simpa using hsafe), fun _ => rfl, ?_⟩
    intro _ sf venv env'' ci' hle hwf hprim2 htr hci hadd
    refine preserves_glue (nm := ``Nat.pow) (F := F) hname rfl rfl (by decide) hF ?_
      hle hwf hprim2 htr hci hadd
    intro venv' env₂ hle' hle₂ henv₂ hprim3 hdefF
    have hle3 := hle'.trans hle₂
    refine VEnv.primField_Nat_pow.2 (reflectsNNN_of_open hle₂ henv₂ hprim3
      (VEnv.contains.mono hle' hnat) hdefF (hFty.mono hle3) fun hlit a b => ?_)
    refine VEnv.reflects_natPow henv₂
      (fun n m => (hprim3.natMul (VEnv.contains.mono hle' hauxC) n m).mono hle₂) ?_ ?_ a b
    · intro a'
      have := VEnv.IsDefEqU.instNat henv₂ hlit (h0.mono hle3) a'
      simpa [VExpr.inst, VExpr.instVar, hfi] using this
    · intro a' b'
      have := VEnv.IsDefEqU.instNat2 henv₂ hlit (hS.mono hle3) a' b'
      simpa [VExpr.inst, VExpr.instVar, hfi] using this
  · rename_i hname; exact absurd hname hrmod
  · rename_i hname; exact absurd hname hrdiv
  · rename_i hname; exact absurd hname hrgcd
  · -- ``Nat.beq
    rename_i hname
    split
    case isFalse => exact M.WF.bindThrow .throw
    rename_i hguard
    simp only [Bool.and_eq_true, List.isEmpty_iff] at hguard
    obtain ⟨⟨hnatE, hboolE⟩, rfl⟩ := hguard
    refine (checkPrimValue.WF (fun {_} {_} {_} => hfail) (by simp [FVarsIn])).bind
      fun _ _ _ h => ?_
    obtain ⟨ty', F, hty', hF, hFty⟩ := h
    cases trExprS_natArrowBool_inv hty'
    have hnf := NatFacts.of_arrow hty'
    have hnat := hnf.contains
    have hprim := (VContext.mk' wf .safe ([] : List Name) fuel).hasPrimitives
    have hbool := contains_primConst (c := VContext.mk' wf .safe ([] : List Name) fuel)
      rfl hboolE primitives_Bool
    obtain ⟨hFc, -⟩ := closedN_of_nil rfl hFty
    have hfi : ∀ (e : VExpr) (k : Nat), F.inst e k = F := fun _ _ => hFc.instN_eq (Nat.zero_le _)
    refine M.WF.bind (checkedIsDefEq.WF'
      (trExprS_app2_bool hF hFty (TrExprS.natZero hprim hnat).1 (TrExprS.natZero hprim hnat).2
        (TrExprS.natZero hprim hnat).1 (TrExprS.natZero hprim hnat).2)
      (TrExprS.boolTrue hprim hbool).1) fun b0 _ _ hb0 => ?_
    split
    case isFalse => exact M.WF.bindThrow .throw
    rename_i hbe0
    have h00 := hb0 (by simpa using hbe0)
    refine M.WF.bind (M.WF.withLocalDecl0 (name := `x) (bi := .default) hnf.tr hnf.isType
      (Q := fun b _ => b = true → (ves.venv .safe).IsDefEqU 0 [VExpr.nat]
        (.app (.app F .natZero) (.app .natSucc (.bvar 0))) VExpr.boolFalse) ?_) fun b1 _ _ hb1 => ?_
    · intro idx cwfx s2 _ _
      have hF' := TrExprS.weakLam0 cwfx hF hFc
      have hFty' := HasType.weakLam0 cwfx hFty hFc ⟨trivial, trivial, trivial⟩
      have hx := trExprS_lastFVar0 cwfx
      have hxty := hasType_lastFVar0 cwfx trivial
      refine checkedIsDefEq.WF' (trExprS_app2_bool hF' hFty' ?_ ?_
        (trExprS_succ hx hxty hprim hnat).1 (trExprS_succ hx hxty hprim hnat).2) ?_
      · exact (TrExprS.natZero hprim hnat).1
      · exact (TrExprS.natZero hprim hnat).2
      · exact (TrExprS.boolFalse hprim hbool).1
    split
    case isFalse => exact M.WF.bindThrow .throw
    rename_i hbe1
    have h0S := hb1 (by simpa using hbe1)
    refine M.WF.bind (M.WF.withLocalDecl0 (name := `x) (bi := .default) hnf.tr hnf.isType
      (Q := fun b _ => b = true → (ves.venv .safe).IsDefEqU 0 [VExpr.nat]
        (.app (.app F (.app .natSucc (.bvar 0))) .natZero) VExpr.boolFalse) ?_) fun b2 _ _ hb2 => ?_
    · intro idx cwfx s2 _ _
      have hF' := TrExprS.weakLam0 cwfx hF hFc
      have hFty' := HasType.weakLam0 cwfx hFty hFc ⟨trivial, trivial, trivial⟩
      have hx := trExprS_lastFVar0 cwfx
      have hxty := hasType_lastFVar0 cwfx trivial
      refine checkedIsDefEq.WF' (trExprS_app2_bool hF' hFty'
        (trExprS_succ hx hxty hprim hnat).1 (trExprS_succ hx hxty hprim hnat).2 ?_ ?_) ?_
      · exact (TrExprS.natZero hprim hnat).1
      · exact (TrExprS.natZero hprim hnat).2
      · exact (TrExprS.boolFalse hprim hbool).1
    split
    case isFalse => exact M.WF.bindThrow .throw
    rename_i hbe2
    have hS0 := hb2 (by simpa using hbe2)
    refine M.WF.bind (M.WF.withLocalDecl0 (name := `y) (bi := .default) hnf.tr hnf.isType
      (Q := fun b _ => b = true → (ves.venv .safe).IsDefEqU 0 [VExpr.nat, VExpr.nat]
        (.app (.app F (.app .natSucc (.bvar 1))) (.app .natSucc (.bvar 0)))
        (.app (.app F (.bvar 1)) (.bvar 0))) ?_) fun b3 _ _ hb3 => ?_
    · intro idy cwfy s2 _ _
      have hnf1 := NatFacts.weakLam0 cwfy hnf
      refine M.WF.withLocalDecl0 (name := `x) (bi := .default) hnf1.tr hnf1.isType ?_
      intro idx cwfx s3 _ _
      have hF2 := TrExprS.weakLam0 cwfx (TrExprS.weakLam0 cwfy hF hFc) hFc
      have hFty2 := HasType.weakLam0 cwfx
        (HasType.weakLam0 cwfy hFty hFc ⟨trivial, trivial, trivial⟩) hFc ⟨trivial, trivial, trivial⟩
      have hy := TrExprS.weakLift0 cwfx (trExprS_lastFVar0 cwfy)
      have hyty := hasType_fvar1 cwfy cwfx trivial
      have hx := trExprS_lastFVar0 cwfx
      have hxty := hasType_lastFVar0 cwfx trivial
      have hsy := trExprS_succ hy hyty hprim hnat
      have hsx := trExprS_succ hx hxty hprim hnat
      exact checkedIsDefEq.WF' (trExprS_app2_bool hF2 hFty2 hsy.1 hsy.2 hsx.1 hsx.2)
        (trExprS_app2_bool hF2 hFty2 hy hyty hx hxty)
    split
    case isFalse => exact M.WF.bindThrow .throw
    rename_i hbe3
    have hSS := hb3 (by simpa using hbe3)
    refine .pure ⟨fun _ => (by simpa using hsafe), fun _ => rfl, ?_⟩
    intro _ sf venv env'' ci' hle hwf hprim2 htr hci hadd
    refine preserves_glue (nm := ``Nat.beq) (F := F) hname rfl rfl (by decide) hF ?_
      hle hwf hprim2 htr hci hadd
    intro venv' env₂ hle' hle₂ henv₂ hprim3 hdefF
    have hle3 := hle'.trans hle₂
    refine VEnv.primField_Nat_beq.2 (reflectsNNB_of_open hle₂ henv₂ hprim3
      (VEnv.contains.mono hle' hnat) hdefF (hFty.mono hle3) fun hlit a b => ?_)
    refine VEnv.reflects_natBEq henv₂ (h00.mono hle3) ?_ ?_ ?_ a b
    · intro b'
      have := VEnv.IsDefEqU.instNat henv₂ hlit (h0S.mono hle3) b'
      simpa [VExpr.inst, VExpr.instVar, hfi] using this
    · intro a'
      have := VEnv.IsDefEqU.instNat henv₂ hlit (hS0.mono hle3) a'
      simpa [VExpr.inst, VExpr.instVar, hfi] using this
    · intro a' b'
      have := VEnv.IsDefEqU.instNat2 henv₂ hlit (hSS.mono hle3) a' b'
      simpa [VExpr.inst, VExpr.instVar, hfi] using this
  · -- ``Nat.ble
    rename_i hname
    split
    case isFalse => exact M.WF.bindThrow .throw
    rename_i hguard
    simp only [Bool.and_eq_true, List.isEmpty_iff] at hguard
    obtain ⟨⟨hnatE, hboolE⟩, rfl⟩ := hguard
    refine (checkPrimValue.WF (fun {_} {_} {_} => hfail) (by simp [FVarsIn])).bind
      fun _ _ _ h => ?_
    obtain ⟨ty', F, hty', hF, hFty⟩ := h
    cases trExprS_natArrowBool_inv hty'
    have hnf := NatFacts.of_arrow hty'
    have hnat := hnf.contains
    have hprim := (VContext.mk' wf .safe ([] : List Name) fuel).hasPrimitives
    have hbool := contains_primConst (c := VContext.mk' wf .safe ([] : List Name) fuel)
      rfl hboolE primitives_Bool
    obtain ⟨hFc, -⟩ := closedN_of_nil rfl hFty
    have hfi : ∀ (e : VExpr) (k : Nat), F.inst e k = F := fun _ _ => hFc.instN_eq (Nat.zero_le _)
    refine M.WF.bind (checkedIsDefEq.WF'
      (trExprS_app2_bool hF hFty (TrExprS.natZero hprim hnat).1 (TrExprS.natZero hprim hnat).2
        (TrExprS.natZero hprim hnat).1 (TrExprS.natZero hprim hnat).2)
      (TrExprS.boolTrue hprim hbool).1) fun b0 _ _ hb0 => ?_
    split
    case isFalse => exact M.WF.bindThrow .throw
    rename_i hbe0
    have h00 := hb0 (by simpa using hbe0)
    refine M.WF.bind (M.WF.withLocalDecl0 (name := `x) (bi := .default) hnf.tr hnf.isType
      (Q := fun b _ => b = true → (ves.venv .safe).IsDefEqU 0 [VExpr.nat]
        (.app (.app F .natZero) (.app .natSucc (.bvar 0))) VExpr.boolTrue) ?_) fun b1 _ _ hb1 => ?_
    · intro idx cwfx s2 _ _
      have hF' := TrExprS.weakLam0 cwfx hF hFc
      have hFty' := HasType.weakLam0 cwfx hFty hFc ⟨trivial, trivial, trivial⟩
      have hx := trExprS_lastFVar0 cwfx
      have hxty := hasType_lastFVar0 cwfx trivial
      refine checkedIsDefEq.WF' (trExprS_app2_bool hF' hFty' ?_ ?_
        (trExprS_succ hx hxty hprim hnat).1 (trExprS_succ hx hxty hprim hnat).2) ?_
      · exact (TrExprS.natZero hprim hnat).1
      · exact (TrExprS.natZero hprim hnat).2
      · exact (TrExprS.boolTrue hprim hbool).1
    split
    case isFalse => exact M.WF.bindThrow .throw
    rename_i hbe1
    have h0S := hb1 (by simpa using hbe1)
    refine M.WF.bind (M.WF.withLocalDecl0 (name := `x) (bi := .default) hnf.tr hnf.isType
      (Q := fun b _ => b = true → (ves.venv .safe).IsDefEqU 0 [VExpr.nat]
        (.app (.app F (.app .natSucc (.bvar 0))) .natZero) VExpr.boolFalse) ?_) fun b2 _ _ hb2 => ?_
    · intro idx cwfx s2 _ _
      have hF' := TrExprS.weakLam0 cwfx hF hFc
      have hFty' := HasType.weakLam0 cwfx hFty hFc ⟨trivial, trivial, trivial⟩
      have hx := trExprS_lastFVar0 cwfx
      have hxty := hasType_lastFVar0 cwfx trivial
      refine checkedIsDefEq.WF' (trExprS_app2_bool hF' hFty'
        (trExprS_succ hx hxty hprim hnat).1 (trExprS_succ hx hxty hprim hnat).2 ?_ ?_) ?_
      · exact (TrExprS.natZero hprim hnat).1
      · exact (TrExprS.natZero hprim hnat).2
      · exact (TrExprS.boolFalse hprim hbool).1
    split
    case isFalse => exact M.WF.bindThrow .throw
    rename_i hbe2
    have hS0 := hb2 (by simpa using hbe2)
    refine M.WF.bind (M.WF.withLocalDecl0 (name := `y) (bi := .default) hnf.tr hnf.isType
      (Q := fun b _ => b = true → (ves.venv .safe).IsDefEqU 0 [VExpr.nat, VExpr.nat]
        (.app (.app F (.app .natSucc (.bvar 1))) (.app .natSucc (.bvar 0)))
        (.app (.app F (.bvar 1)) (.bvar 0))) ?_) fun b3 _ _ hb3 => ?_
    · intro idy cwfy s2 _ _
      have hnf1 := NatFacts.weakLam0 cwfy hnf
      refine M.WF.withLocalDecl0 (name := `x) (bi := .default) hnf1.tr hnf1.isType ?_
      intro idx cwfx s3 _ _
      have hF2 := TrExprS.weakLam0 cwfx (TrExprS.weakLam0 cwfy hF hFc) hFc
      have hFty2 := HasType.weakLam0 cwfx
        (HasType.weakLam0 cwfy hFty hFc ⟨trivial, trivial, trivial⟩) hFc ⟨trivial, trivial, trivial⟩
      have hy := TrExprS.weakLift0 cwfx (trExprS_lastFVar0 cwfy)
      have hyty := hasType_fvar1 cwfy cwfx trivial
      have hx := trExprS_lastFVar0 cwfx
      have hxty := hasType_lastFVar0 cwfx trivial
      have hsy := trExprS_succ hy hyty hprim hnat
      have hsx := trExprS_succ hx hxty hprim hnat
      exact checkedIsDefEq.WF' (trExprS_app2_bool hF2 hFty2 hsy.1 hsy.2 hsx.1 hsx.2)
        (trExprS_app2_bool hF2 hFty2 hy hyty hx hxty)
    split
    case isFalse => exact M.WF.bindThrow .throw
    rename_i hbe3
    have hSS := hb3 (by simpa using hbe3)
    refine .pure ⟨fun _ => (by simpa using hsafe), fun _ => rfl, ?_⟩
    intro _ sf venv env'' ci' hle hwf hprim2 htr hci hadd
    refine preserves_glue (nm := ``Nat.ble) (F := F) hname rfl rfl (by decide) hF ?_
      hle hwf hprim2 htr hci hadd
    intro venv' env₂ hle' hle₂ henv₂ hprim3 hdefF
    have hle3 := hle'.trans hle₂
    refine VEnv.primField_Nat_ble.2 (reflectsNNB_of_open hle₂ henv₂ hprim3
      (VEnv.contains.mono hle' hnat) hdefF (hFty.mono hle3) fun hlit a b => ?_)
    refine VEnv.reflects_natBLE henv₂ (h00.mono hle3) ?_ ?_ ?_ a b
    · intro b'
      have := VEnv.IsDefEqU.instNat henv₂ hlit (h0S.mono hle3) b'
      simpa [VExpr.inst, VExpr.instVar, hfi] using this
    · intro a'
      have := VEnv.IsDefEqU.instNat henv₂ hlit (hS0.mono hle3) a'
      simpa [VExpr.inst, VExpr.instVar, hfi] using this
    · intro a' b'
      have := VEnv.IsDefEqU.instNat2 henv₂ hlit (hSS.mono hle3) a' b'
      simpa [VExpr.inst, VExpr.instVar, hfi] using this
  · rename_i hname; exact absurd hname hrbit
  · -- ``Nat.land
    rename_i hname
    split
    case h_2 =>
      split
      · refine M.WF.bind (checkPrimValue.WF (fun {_} {_} {_} => hfail) (by simp [FVarsIn]))
          fun _ _ _ _ => ?_
        exact M.WF.bindThrow .throw
      · exact M.WF.bindThrow .throw
    rename_i andE heqv
    split
    case isFalse => exact M.WF.bindThrow .throw
    rename_i hguard
    simp only [Bool.and_eq_true, List.isEmpty_iff] at hguard
    obtain ⟨⟨⟨hnatE, hboolE⟩, hbwE⟩, rfl⟩ := hguard
    refine (checkPrimValue.WF (fun {_} {_} {_} => hfail) (by simp [FVarsIn])).bind
      fun _ _ _ h => ?_
    obtain ⟨ty', F, hty', hF, hFty⟩ := h
    cases trExprS_natArrow2_inv hty'
    have hnf := NatFacts.of_arrow hty'
    have hnat := hnf.contains
    have hprim := (VContext.mk' wf .safe ([] : List Name) fuel).hasPrimitives
    have hbool := contains_primConst (c := VContext.mk' wf .safe ([] : List Name) fuel)
      rfl hboolE primitives_Bool
    have hbwC := contains_primConst (c := VContext.mk' wf .safe ([] : List Name) fuel)
      rfl hbwE primitives_natBitwise
    obtain ⟨hFc, -⟩ := closedN_of_nil rfl hFty
    have hFv := hF
    rw [heqv] at hFv
    obtain ⟨G, hFeq, hG⟩ := trExprS_bitwiseApp_inv hFv
    subst hFeq
    -- `unless ← checkedTypeIs _ q(Bool → Bool → Bool)`: the combinator's own type, which
    -- `VEnv.ReflectsBoolBoolBool` carries and `VEnv.ReflectsNatBitwise` needs.
    refine M.WF.bind (checkedTypeIs.WF' hG ?hfvB1) fun _ _ _ hbt => ?_
    case hfvB1 => simp [FVarsIn]
    split
    case isFalse => exact M.WF.bindThrow .throw
    rename_i hbty
    obtain ⟨tyB, htyB, hGtyF⟩ := hbt
    cases trExprS_boolArrow2_inv htyB
    have hGty := hGtyF (by simpa using hbty)
    have hGc : G.ClosedN 0 := hFc.2
    have hgi : ∀ (e : VExpr) (k : Nat), G.inst e k = G := fun _ _ => hGc.instN_eq (Nat.zero_le _)
    refine M.WF.bind (M.WF.withLocalDecl0 (name := `x) (bi := .default) (ty' := VExpr.bool)
      (trExprS_bool rfl hboolE) (isType_bool hprim hbool rfl)
      (Q := fun b _ => b = true → (ves.venv .safe).IsDefEqU 0 [VExpr.bool]
        (.app (.app G .boolFalse) (.bvar 0)) VExpr.boolFalse) ?_) fun b1 _ _ hb1 => ?_
    · intro idx cwfx s2 _ _
      have hG' := TrExprS.weakLam0 cwfx hG hGc
      have hx := trExprS_lastFVar0 cwfx
      refine M.WF.mono (checkedIsDefEq.WFl ?hfv (TrExprS.boolFalse hprim hbool).1)
        fun r _ _ h => ?_
      case hfv => exact ⟨⟨hG'.fvarsIn, nofun⟩, hx.fvarsIn⟩
      obtain ⟨a', ha', hd⟩ := h
      intro hr
      refine VContext.trans ?_ (hd hr)
      exact (app2_uniq ha' hG'
        (fun Z hZ => trExprS_uniq hZ (TrExprS.boolFalse hprim hbool).1)
        (fun Z hZ => trExprS_uniq hZ hx)).symm
    split
    case isFalse => exact M.WF.bindThrow .throw
    rename_i hbe1
    have hL0 := hb1 (by simpa using hbe1)
    refine M.WF.bind (M.WF.withLocalDecl0 (name := `x) (bi := .default) (ty' := VExpr.bool)
      (trExprS_bool rfl hboolE) (isType_bool hprim hbool rfl)
      (Q := fun b _ => b = true → (ves.venv .safe).IsDefEqU 0 [VExpr.bool]
        (.app (.app G .boolTrue) (.bvar 0)) (.bvar 0)) ?_) fun b2 _ _ hb2 => ?_
    · intro idx cwfx s2 _ _
      have hG' := TrExprS.weakLam0 cwfx hG hGc
      have hx := trExprS_lastFVar0 cwfx
      refine M.WF.mono (checkedIsDefEq.WFl ?hfv hx) fun r _ _ h => ?_
      case hfv => exact ⟨⟨hG'.fvarsIn, nofun⟩, hx.fvarsIn⟩
      obtain ⟨a', ha', hd⟩ := h
      intro hr
      refine VContext.trans ?_ (hd hr)
      exact (app2_uniq ha' hG'
        (fun Z hZ => trExprS_uniq hZ (TrExprS.boolTrue hprim hbool).1)
        (fun Z hZ => trExprS_uniq hZ hx)).symm
    split
    case isFalse => exact M.WF.bindThrow .throw
    rename_i hbe2
    have hL1 := hb2 (by simpa using hbe2)
    refine .pure ⟨fun _ => (by simpa using hsafe), fun _ => rfl, ?_⟩
    intro _ sf venv env'' ci' hle hwf hprim2 htr hci hadd
    refine preserves_glue (nm := ``Nat.land) (F := _) hname rfl rfl (by decide) hF ?_
      hle hwf hprim2 htr hci hadd
    intro venv' env₂ hle' hle₂ henv₂ hprim3 hdefF
    have hle3 := hle'.trans hle₂
    have hblit : (ves.venv .safe).BoolLits := hprim.boolLits hbool
    refine VEnv.primField_Nat_land.2 (reflectsNNN_of_open hle₂ henv₂ hprim3
      (VEnv.contains.mono hle' hnat) hdefF (hFty.mono hle3) fun hlit a b => ?_)
    refine hprim3.natBitwise (VEnv.contains.mono hle' hbwC) env₂ hle₂ G and henv₂ ?_ a b
    refine VEnv.reflectsBoolBoolBool_and (hGty.mono hle3) ?_ ?_
    · intro bb
      have := VEnv.IsDefEqU.instBool henv₂ (hblit.mono hle3) (hL0.mono hle3) bb
      simpa [VExpr.inst, VExpr.instVar, hgi] using this
    · intro bb
      have := VEnv.IsDefEqU.instBool henv₂ (hblit.mono hle3) (hL1.mono hle3) bb
      simpa [VExpr.inst, VExpr.instVar, hgi] using this
  · -- ``Nat.lor
    rename_i hname
    split
    case h_2 =>
      split
      · refine M.WF.bind (checkPrimValue.WF (fun {_} {_} {_} => hfail) (by simp [FVarsIn]))
          fun _ _ _ _ => ?_
        exact M.WF.bindThrow .throw
      · exact M.WF.bindThrow .throw
    rename_i andE heqv
    split
    case isFalse => exact M.WF.bindThrow .throw
    rename_i hguard
    simp only [Bool.and_eq_true, List.isEmpty_iff] at hguard
    obtain ⟨⟨⟨hnatE, hboolE⟩, hbwE⟩, rfl⟩ := hguard
    refine (checkPrimValue.WF (fun {_} {_} {_} => hfail) (by simp [FVarsIn])).bind
      fun _ _ _ h => ?_
    obtain ⟨ty', F, hty', hF, hFty⟩ := h
    cases trExprS_natArrow2_inv hty'
    have hnf := NatFacts.of_arrow hty'
    have hnat := hnf.contains
    have hprim := (VContext.mk' wf .safe ([] : List Name) fuel).hasPrimitives
    have hbool := contains_primConst (c := VContext.mk' wf .safe ([] : List Name) fuel)
      rfl hboolE primitives_Bool
    have hbwC := contains_primConst (c := VContext.mk' wf .safe ([] : List Name) fuel)
      rfl hbwE primitives_natBitwise
    obtain ⟨hFc, -⟩ := closedN_of_nil rfl hFty
    have hFv := hF
    rw [heqv] at hFv
    obtain ⟨G, hFeq, hG⟩ := trExprS_bitwiseApp_inv hFv
    subst hFeq
    -- `unless ← checkedTypeIs _ q(Bool → Bool → Bool)`: the combinator's own type, which
    -- `VEnv.ReflectsBoolBoolBool` carries and `VEnv.ReflectsNatBitwise` needs.
    refine M.WF.bind (checkedTypeIs.WF' hG ?hfvB2) fun _ _ _ hbt => ?_
    case hfvB2 => simp [FVarsIn]
    split
    case isFalse => exact M.WF.bindThrow .throw
    rename_i hbty
    obtain ⟨tyB, htyB, hGtyF⟩ := hbt
    cases trExprS_boolArrow2_inv htyB
    have hGty := hGtyF (by simpa using hbty)
    have hGc : G.ClosedN 0 := hFc.2
    have hgi : ∀ (e : VExpr) (k : Nat), G.inst e k = G := fun _ _ => hGc.instN_eq (Nat.zero_le _)
    refine M.WF.bind (M.WF.withLocalDecl0 (name := `x) (bi := .default) (ty' := VExpr.bool)
      (trExprS_bool rfl hboolE) (isType_bool hprim hbool rfl)
      (Q := fun b _ => b = true → (ves.venv .safe).IsDefEqU 0 [VExpr.bool]
        (.app (.app G .boolFalse) (.bvar 0)) (.bvar 0)) ?_) fun b1 _ _ hb1 => ?_
    · intro idx cwfx s2 _ _
      have hG' := TrExprS.weakLam0 cwfx hG hGc
      have hx := trExprS_lastFVar0 cwfx
      refine M.WF.mono (checkedIsDefEq.WFl ?hfv hx) fun r _ _ h => ?_
      case hfv => exact ⟨⟨hG'.fvarsIn, nofun⟩, hx.fvarsIn⟩
      obtain ⟨a', ha', hd⟩ := h
      intro hr
      refine VContext.trans ?_ (hd hr)
      exact (app2_uniq ha' hG'
        (fun Z hZ => trExprS_uniq hZ (TrExprS.boolFalse hprim hbool).1)
        (fun Z hZ => trExprS_uniq hZ hx)).symm
    split
    case isFalse => exact M.WF.bindThrow .throw
    rename_i hbe1
    have hL0 := hb1 (by simpa using hbe1)
    refine M.WF.bind (M.WF.withLocalDecl0 (name := `x) (bi := .default) (ty' := VExpr.bool)
      (trExprS_bool rfl hboolE) (isType_bool hprim hbool rfl)
      (Q := fun b _ => b = true → (ves.venv .safe).IsDefEqU 0 [VExpr.bool]
        (.app (.app G .boolTrue) (.bvar 0)) VExpr.boolTrue) ?_) fun b2 _ _ hb2 => ?_
    · intro idx cwfx s2 _ _
      have hG' := TrExprS.weakLam0 cwfx hG hGc
      have hx := trExprS_lastFVar0 cwfx
      refine M.WF.mono (checkedIsDefEq.WFl ?hfv (TrExprS.boolTrue hprim hbool).1)
        fun r _ _ h => ?_
      case hfv => exact ⟨⟨hG'.fvarsIn, nofun⟩, hx.fvarsIn⟩
      obtain ⟨a', ha', hd⟩ := h
      intro hr
      refine VContext.trans ?_ (hd hr)
      exact (app2_uniq ha' hG'
        (fun Z hZ => trExprS_uniq hZ (TrExprS.boolTrue hprim hbool).1)
        (fun Z hZ => trExprS_uniq hZ hx)).symm
    split
    case isFalse => exact M.WF.bindThrow .throw
    rename_i hbe2
    have hL1 := hb2 (by simpa using hbe2)
    refine .pure ⟨fun _ => (by simpa using hsafe), fun _ => rfl, ?_⟩
    intro _ sf venv env'' ci' hle hwf hprim2 htr hci hadd
    refine preserves_glue (nm := ``Nat.lor) (F := _) hname rfl rfl (by decide) hF ?_
      hle hwf hprim2 htr hci hadd
    intro venv' env₂ hle' hle₂ henv₂ hprim3 hdefF
    have hle3 := hle'.trans hle₂
    have hblit : (ves.venv .safe).BoolLits := hprim.boolLits hbool
    refine VEnv.primField_Nat_lor.2 (reflectsNNN_of_open hle₂ henv₂ hprim3
      (VEnv.contains.mono hle' hnat) hdefF (hFty.mono hle3) fun hlit a b => ?_)
    refine hprim3.natBitwise (VEnv.contains.mono hle' hbwC) env₂ hle₂ G or henv₂ ?_ a b
    refine VEnv.reflectsBoolBoolBool_or (hGty.mono hle3) ?_ ?_
    · intro bb
      have := VEnv.IsDefEqU.instBool henv₂ (hblit.mono hle3) (hL0.mono hle3) bb
      simpa [VExpr.inst, VExpr.instVar, hgi] using this
    · intro bb
      have := VEnv.IsDefEqU.instBool henv₂ (hblit.mono hle3) (hL1.mono hle3) bb
      simpa [VExpr.inst, VExpr.instVar, hgi] using this
  · -- ``Nat.xor
    rename_i hname
    split
    case h_2 =>
      split
      · refine M.WF.bind (checkPrimValue.WF (fun {_} {_} {_} => hfail) (by simp [FVarsIn]))
          fun _ _ _ _ => ?_
        exact M.WF.bindThrow .throw
      · exact M.WF.bindThrow .throw
    rename_i andE heqv
    split
    case isFalse => exact M.WF.bindThrow .throw
    rename_i hguard
    simp only [Bool.and_eq_true, List.isEmpty_iff] at hguard
    obtain ⟨⟨⟨hnatE, hboolE⟩, hbwE⟩, rfl⟩ := hguard
    refine (checkPrimValue.WF (fun {_} {_} {_} => hfail) (by simp [FVarsIn])).bind
      fun _ _ _ h => ?_
    obtain ⟨ty', F, hty', hF, hFty⟩ := h
    cases trExprS_natArrow2_inv hty'
    have hnf := NatFacts.of_arrow hty'
    have hnat := hnf.contains
    have hprim := (VContext.mk' wf .safe ([] : List Name) fuel).hasPrimitives
    have hbool := contains_primConst (c := VContext.mk' wf .safe ([] : List Name) fuel)
      rfl hboolE primitives_Bool
    have hbwC := contains_primConst (c := VContext.mk' wf .safe ([] : List Name) fuel)
      rfl hbwE primitives_natBitwise
    obtain ⟨hFc, -⟩ := closedN_of_nil rfl hFty
    have hFv := hF
    rw [heqv] at hFv
    obtain ⟨G, hFeq, hG⟩ := trExprS_bitwiseApp_inv hFv
    subst hFeq
    -- `unless ← checkedTypeIs _ q(Bool → Bool → Bool)`: the combinator's own type, which
    -- `VEnv.ReflectsBoolBoolBool` carries and `VEnv.ReflectsNatBitwise` needs.
    refine M.WF.bind (checkedTypeIs.WF' hG ?hfvB3) fun _ _ _ hbt => ?_
    case hfvB3 => simp [FVarsIn]
    split
    case isFalse => exact M.WF.bindThrow .throw
    rename_i hbty
    obtain ⟨tyB, htyB, hGtyF⟩ := hbt
    cases trExprS_boolArrow2_inv htyB
    have hGty := hGtyF (by simpa using hbty)
    refine M.WF.bind (M.WF.mono (R := fun rr _ => rr = true →
        (ves.venv .safe).IsDefEqU 0 []
          (.app (.app G VExpr.boolFalse) VExpr.boolFalse) VExpr.boolFalse)
      (checkedIsDefEq.WFl ?hfvq1 (TrExprS.boolFalse hprim hbool).1)
      fun rr _ _ h => ?gq1) fun _ _ _ q1 => ?_
    case hfvq1 => exact ⟨⟨hG.fvarsIn, nofun⟩, nofun⟩
    case gq1 =>
      obtain ⟨a', ha', hd⟩ := h
      intro hr
      exact VContext.trans (app2_uniq ha' hG
        (fun Z hZ => trExprS_uniq hZ (TrExprS.boolFalse hprim hbool).1)
        (fun Z hZ => trExprS_uniq hZ (TrExprS.boolFalse hprim hbool).1)).symm (hd hr)
    split
    case isFalse => exact M.WF.bindThrow .throw
    rename_i heq1
    have hq1 := q1 (by simpa using heq1)
    refine M.WF.bind (M.WF.mono (R := fun rr _ => rr = true →
        (ves.venv .safe).IsDefEqU 0 []
          (.app (.app G VExpr.boolTrue) VExpr.boolFalse) VExpr.boolTrue)
      (checkedIsDefEq.WFl ?hfvq2 (TrExprS.boolTrue hprim hbool).1)
      fun rr _ _ h => ?gq2) fun _ _ _ q2 => ?_
    case hfvq2 => exact ⟨⟨hG.fvarsIn, nofun⟩, nofun⟩
    case gq2 =>
      obtain ⟨a', ha', hd⟩ := h
      intro hr
      exact VContext.trans (app2_uniq ha' hG
        (fun Z hZ => trExprS_uniq hZ (TrExprS.boolTrue hprim hbool).1)
        (fun Z hZ => trExprS_uniq hZ (TrExprS.boolFalse hprim hbool).1)).symm (hd hr)
    split
    case isFalse => exact M.WF.bindThrow .throw
    rename_i heq2
    have hq2 := q2 (by simpa using heq2)
    refine M.WF.bind (M.WF.mono (R := fun rr _ => rr = true →
        (ves.venv .safe).IsDefEqU 0 []
          (.app (.app G VExpr.boolFalse) VExpr.boolTrue) VExpr.boolTrue)
      (checkedIsDefEq.WFl ?hfvq3 (TrExprS.boolTrue hprim hbool).1)
      fun rr _ _ h => ?gq3) fun _ _ _ q3 => ?_
    case hfvq3 => exact ⟨⟨hG.fvarsIn, nofun⟩, nofun⟩
    case gq3 =>
      obtain ⟨a', ha', hd⟩ := h
      intro hr
      exact VContext.trans (app2_uniq ha' hG
        (fun Z hZ => trExprS_uniq hZ (TrExprS.boolFalse hprim hbool).1)
        (fun Z hZ => trExprS_uniq hZ (TrExprS.boolTrue hprim hbool).1)).symm (hd hr)
    split
    case isFalse => exact M.WF.bindThrow .throw
    rename_i heq3
    have hq3 := q3 (by simpa using heq3)
    refine M.WF.bind (M.WF.mono (R := fun rr _ => rr = true →
        (ves.venv .safe).IsDefEqU 0 []
          (.app (.app G VExpr.boolTrue) VExpr.boolTrue) VExpr.boolFalse)
      (checkedIsDefEq.WFl ?hfvq4 (TrExprS.boolFalse hprim hbool).1)
      fun rr _ _ h => ?gq4) fun _ _ _ q4 => ?_
    case hfvq4 => exact ⟨⟨hG.fvarsIn, nofun⟩, nofun⟩
    case gq4 =>
      obtain ⟨a', ha', hd⟩ := h
      intro hr
      exact VContext.trans (app2_uniq ha' hG
        (fun Z hZ => trExprS_uniq hZ (TrExprS.boolTrue hprim hbool).1)
        (fun Z hZ => trExprS_uniq hZ (TrExprS.boolTrue hprim hbool).1)).symm (hd hr)
    split
    case isFalse => exact M.WF.bindThrow .throw
    rename_i heq4
    have hq4 := q4 (by simpa using heq4)
    refine .pure ⟨fun _ => (by simpa using hsafe), fun _ => rfl, ?_⟩
    intro _ sf venv env'' ci' hle hwf hprim2 htr hci hadd
    refine preserves_glue (nm := ``Nat.xor) (F := _) hname rfl rfl (by decide) hF ?_
      hle hwf hprim2 htr hci hadd
    intro venv' env₂ hle' hle₂ henv₂ hprim3 hdefF
    have hle3 := hle'.trans hle₂
    refine VEnv.primField_Nat_xor.2 (reflectsNNN_of_open hle₂ henv₂ hprim3
      (VEnv.contains.mono hle' hnat) hdefF (hFty.mono hle3) fun hlit a b => ?_)
    refine hprim3.natBitwise (VEnv.contains.mono hle' hbwC) env₂ hle₂ G bne henv₂ ?_ a b
    exact VEnv.reflectsBoolBoolBool_bne (hGty.mono hle3) (hq1.mono hle3) (hq2.mono hle3)
      (hq3.mono hle3) (hq4.mono hle3)
  · -- ``Nat.shiftLeft
    rename_i hname
    split
    case isFalse => exact M.WF.bindThrow .throw
    rename_i hguard
    simp only [Bool.and_eq_true, List.isEmpty_iff] at hguard
    obtain ⟨⟨hnatE, hauxE⟩, rfl⟩ := hguard
    refine (checkPrimValue.WF (fun {_} {_} {_} => hfail) (by simp [FVarsIn])).bind
      fun _ _ _ h => ?_
    obtain ⟨ty', F, hty', hF, hFty⟩ := h
    cases trExprS_natArrow2_inv hty'
    have hnf := NatFacts.of_arrow hty'
    have hnat := hnf.contains
    have hprim := (VContext.mk' wf .safe ([] : List Name) fuel).hasPrimitives
    have hauxC := contains_primConst (c := VContext.mk' wf .safe ([] : List Name) fuel)
      rfl hauxE primitives_natMul
    obtain ⟨hFc, -⟩ := closedN_of_nil rfl hFty
    have hfi : ∀ (e : VExpr) (k : Nat), F.inst e k = F := fun _ _ => hFc.instN_eq (Nat.zero_le _)
    have htwo : _ ∧ _ := trExprS_succ (trExprS_succ (TrExprS.natZero hprim hnat).1
      (TrExprS.natZero hprim hnat).2 hprim hnat).1
      (trExprS_succ (TrExprS.natZero hprim hnat).1 (TrExprS.natZero hprim hnat).2 hprim hnat).2
      hprim hnat
    refine M.WF.bind (M.WF.withLocalDecl0 (name := `x) (bi := .default) hnf.tr hnf.isType
      (Q := fun b _ => b = true → (ves.venv .safe).IsDefEqU 0 [VExpr.nat]
        (.app (.app F (.bvar 0)) .natZero) (.bvar 0)) ?_) fun b _ _ hb => ?_
    · intro idx cwfx s'' _ _
      have hF' := TrExprS.weakLam0 cwfx hF hFc
      have hFty' := HasType.weakLam0 cwfx hFty hFc ⟨trivial, trivial, trivial⟩
      have hx := trExprS_lastFVar0 cwfx
      have hxty := hasType_lastFVar0 cwfx trivial
      exact checkedIsDefEq.WF' (trExprS_app2_nat hF' hFty' hx hxty
        (TrExprS.natZero hprim hnat).1 (TrExprS.natZero hprim hnat).2).1 hx
    split
    case isFalse => exact M.WF.bindThrow .throw
    rename_i hb1
    have h0 := hb (by simpa using hb1)
    refine M.WF.bind (M.WF.withLocalDecl0 (name := `y) (bi := .default) hnf.tr hnf.isType
      (Q := fun b _ => b = true → (ves.venv .safe).IsDefEqU 0 [VExpr.nat, VExpr.nat]
        (.app (.app F (.bvar 0)) (.app .natSucc (.bvar 1)))
        (.app (.app F (.app (.app (.const ``Nat.mul []) (.natLit 2)) (.bvar 0)))
          (.bvar 1))) ?_) fun b2 _ _ hb2 => ?_
    · intro idy cwfy s2 _ _
      have hnf1 := NatFacts.weakLam0 cwfy hnf
      refine M.WF.withLocalDecl0 (name := `x) (bi := .default) hnf1.tr hnf1.isType ?_
      intro idx cwfx s3 _ _
      have hF2 := TrExprS.weakLam0 cwfx (TrExprS.weakLam0 cwfy hF hFc) hFc
      have hFty2 := HasType.weakLam0 cwfx
        (HasType.weakLam0 cwfy hFty hFc ⟨trivial, trivial, trivial⟩) hFc ⟨trivial, trivial, trivial⟩
      have hy := TrExprS.weakLift0 cwfx (trExprS_lastFVar0 cwfy)
      have hyty := hasType_fvar1 cwfy cwfx trivial
      have hx := trExprS_lastFVar0 cwfx
      have hxty := hasType_lastFVar0 cwfx trivial
      have hsy := trExprS_succ hy hyty hprim hnat
      have hz1 := TrExprS.weakLam0 cwfy htwo.1 (VExpr.closedN_natLit 2)
      have hz2 := HasType.weakLam0 cwfy htwo.2 (VExpr.closedN_natLit 2) trivial
      have hz : _ ∧ _ := ⟨TrExprS.weakLam0 cwfx hz1 (VExpr.closedN_natLit 2),
        HasType.weakLam0 cwfx hz2 (VExpr.closedN_natLit 2) trivial⟩
      have hxy := trExprS_app2_nat hF2 hFty2 hx hxty hy hyty
      refine (checkedIsDefEq.WFr (trExprS_app2_nat hF2 hFty2 hx hxty hsy.1 hsy.2).1
        (by refine ⟨⟨hF2.fvarsIn, ⟨⟨nofun, hz.1.fvarsIn⟩, hx.fvarsIn⟩⟩, hy.fvarsIn⟩)).mono
        fun r _ _ h => ?_
      obtain ⟨b', hb', hd⟩ := h
      intro hr
      refine VContext.trans (hd hr) (rhs_val_app2 hb' hF2 ?_ hy)
      exact fun Z hZ => rhs_const_app2 hZ hz.1 hx
    split
    case isFalse => exact M.WF.bindThrow .throw
    rename_i hb3
    have hS := hb2 (by simpa using hb3)
    refine .pure ⟨fun _ => (by simpa using hsafe), fun _ => rfl, ?_⟩
    intro _ sf venv env'' ci' hle hwf hprim2 htr hci hadd
    refine preserves_glue (nm := ``Nat.shiftLeft) (F := F) hname rfl rfl (by decide) hF ?_
      hle hwf hprim2 htr hci hadd
    intro venv' env₂ hle' hle₂ henv₂ hprim3 hdefF
    have hle3 := hle'.trans hle₂
    refine VEnv.primField_Nat_shiftLeft.2 (reflectsNNN_of_open hle₂ henv₂ hprim3
      (VEnv.contains.mono hle' hnat) hdefF (hFty.mono hle3) fun hlit a b => ?_)
    refine VEnv.reflects_natShiftLeft henv₂
      (fun n m => (hprim3.natMul (VEnv.contains.mono hle' hauxC) n m).mono hle₂) ?_ ?_ a b
    · intro a'
      have := VEnv.IsDefEqU.instNat henv₂ hlit (h0.mono hle3) a'
      simpa [VExpr.inst, VExpr.instVar, hfi] using this
    · intro a' b'
      have := VEnv.IsDefEqU.instNat2 henv₂ hlit (hS.mono hle3) b' a'
      simpa [VExpr.inst, VExpr.instVar, hfi] using this
  · -- ``Nat.shiftRight
    rename_i hname
    split
    case isFalse => exact M.WF.bindThrow .throw
    rename_i hguard
    simp only [Bool.and_eq_true, List.isEmpty_iff] at hguard
    obtain ⟨⟨hnatE, hauxE⟩, rfl⟩ := hguard
    refine (checkPrimValue.WF (fun {_} {_} {_} => hfail) (by simp [FVarsIn])).bind
      fun _ _ _ h => ?_
    obtain ⟨ty', F, hty', hF, hFty⟩ := h
    cases trExprS_natArrow2_inv hty'
    have hnf := NatFacts.of_arrow hty'
    have hnat := hnf.contains
    have hprim := (VContext.mk' wf .safe ([] : List Name) fuel).hasPrimitives
    have hauxC := contains_primConst (c := VContext.mk' wf .safe ([] : List Name) fuel)
      rfl hauxE primitives_natDiv
    obtain ⟨hFc, -⟩ := closedN_of_nil rfl hFty
    have hfi : ∀ (e : VExpr) (k : Nat), F.inst e k = F := fun _ _ => hFc.instN_eq (Nat.zero_le _)
    have htwo : _ ∧ _ := trExprS_succ (trExprS_succ (TrExprS.natZero hprim hnat).1
      (TrExprS.natZero hprim hnat).2 hprim hnat).1
      (trExprS_succ (TrExprS.natZero hprim hnat).1 (TrExprS.natZero hprim hnat).2 hprim hnat).2
      hprim hnat
    refine M.WF.bind (M.WF.withLocalDecl0 (name := `x) (bi := .default) hnf.tr hnf.isType
      (Q := fun b _ => b = true → (ves.venv .safe).IsDefEqU 0 [VExpr.nat]
        (.app (.app F (.bvar 0)) .natZero) (.bvar 0)) ?_) fun b _ _ hb => ?_
    · intro idx cwfx s'' _ _
      have hF' := TrExprS.weakLam0 cwfx hF hFc
      have hFty' := HasType.weakLam0 cwfx hFty hFc ⟨trivial, trivial, trivial⟩
      have hx := trExprS_lastFVar0 cwfx
      have hxty := hasType_lastFVar0 cwfx trivial
      exact checkedIsDefEq.WF' (trExprS_app2_nat hF' hFty' hx hxty
        (TrExprS.natZero hprim hnat).1 (TrExprS.natZero hprim hnat).2).1 hx
    split
    case isFalse => exact M.WF.bindThrow .throw
    rename_i hb1
    have h0 := hb (by simpa using hb1)
    refine M.WF.bind (M.WF.withLocalDecl0 (name := `y) (bi := .default) hnf.tr hnf.isType
      (Q := fun b _ => b = true → (ves.venv .safe).IsDefEqU 0 [VExpr.nat, VExpr.nat]
        (.app (.app F (.bvar 0)) (.app .natSucc (.bvar 1)))
        (.app (.app (.const ``Nat.div []) (.app (.app F (.bvar 0)) (.bvar 1)))
          (.natLit 2))) ?_) fun b2 _ _ hb2 => ?_
    · intro idy cwfy s2 _ _
      have hnf1 := NatFacts.weakLam0 cwfy hnf
      refine M.WF.withLocalDecl0 (name := `x) (bi := .default) hnf1.tr hnf1.isType ?_
      intro idx cwfx s3 _ _
      have hF2 := TrExprS.weakLam0 cwfx (TrExprS.weakLam0 cwfy hF hFc) hFc
      have hFty2 := HasType.weakLam0 cwfx
        (HasType.weakLam0 cwfy hFty hFc ⟨trivial, trivial, trivial⟩) hFc ⟨trivial, trivial, trivial⟩
      have hy := TrExprS.weakLift0 cwfx (trExprS_lastFVar0 cwfy)
      have hyty := hasType_fvar1 cwfy cwfx trivial
      have hx := trExprS_lastFVar0 cwfx
      have hxty := hasType_lastFVar0 cwfx trivial
      have hsy := trExprS_succ hy hyty hprim hnat
      have hz1 := TrExprS.weakLam0 cwfy htwo.1 (VExpr.closedN_natLit 2)
      have hz2 := HasType.weakLam0 cwfy htwo.2 (VExpr.closedN_natLit 2) trivial
      have hz : _ ∧ _ := ⟨TrExprS.weakLam0 cwfx hz1 (VExpr.closedN_natLit 2),
        HasType.weakLam0 cwfx hz2 (VExpr.closedN_natLit 2) trivial⟩
      have hxy := trExprS_app2_nat hF2 hFty2 hx hxty hy hyty
      refine (checkedIsDefEq.WFr (trExprS_app2_nat hF2 hFty2 hx hxty hsy.1 hsy.2).1
        (by refine ⟨⟨nofun, hxy.1.fvarsIn⟩, hz.1.fvarsIn⟩)).mono fun r _ _ h => ?_
      obtain ⟨b', hb', hd⟩ := h
      intro hr
      exact VContext.trans (hd hr) (rhs_const_app2 hb' hxy.1 hz.1)
    split
    case isFalse => exact M.WF.bindThrow .throw
    rename_i hb3
    have hS := hb2 (by simpa using hb3)
    refine .pure ⟨fun _ => (by simpa using hsafe), fun _ => rfl, ?_⟩
    intro _ sf venv env'' ci' hle hwf hprim2 htr hci hadd
    refine preserves_glue (nm := ``Nat.shiftRight) (F := F) hname rfl rfl (by decide) hF ?_
      hle hwf hprim2 htr hci hadd
    intro venv' env₂ hle' hle₂ henv₂ hprim3 hdefF
    have hle3 := hle'.trans hle₂
    refine VEnv.primField_Nat_shiftRight.2 (reflectsNNN_of_open hle₂ henv₂ hprim3
      (VEnv.contains.mono hle' hnat) hdefF (hFty.mono hle3) fun hlit a b => ?_)
    refine VEnv.reflects_natShiftRight henv₂
      (fun n m => (hprim3.natDiv (VEnv.contains.mono hle' hauxC) n m).mono hle₂) ?_ ?_ a b
    · intro a'
      have := VEnv.IsDefEqU.instNat henv₂ hlit (h0.mono hle3) a'
      simpa [VExpr.inst, VExpr.instVar, hfi] using this
    · intro a' b'
      have := VEnv.IsDefEqU.instNat2 henv₂ hlit (hS.mono hle3) b' a'
      simpa [VExpr.inst, VExpr.instVar, hfi] using this
  · -- ``Char.ofNat
    rename_i hname
    split
    · rename_i htyeq
      split
      · rename_i hguard
        simp only [Bool.and_eq_true, List.isEmpty_iff] at hguard
        obtain ⟨hnatE, rfl⟩ := hguard
        refine M.WF.bind (checkIsType.WF (by simp [FVarsIn])) fun _ _ _ _ => ?_
        refine .pure ⟨fun _ => (by simpa using hsafe), fun _ => rfl, ?_⟩
        intro _ sf venv env'' ci' hle hwf hprim2 htr hci hadd
        refine preserves_glue_const (nm := ``Char.ofNat) hname rfl (by decide) ?_
          hle hwf hprim2 htr hci hadd
        intro venv2 ci2 hle2 hprim4 htype huv0 env₂ hle₂ hconst
        have hteq := trExprS_natChar_inv' (htype.eqv htyeq)
        rw [VEnv.primField_Char_ofNat]
        intro ci hci2
        rw [hconst] at hci2
        cases hci2
        show (⟨ci2.uvars, ci2.type⟩ : VConstant) = _
        rw [huv0, hteq]
      · exact M.WF.bindThrow .throw
    · split
      · refine M.WF.bind (checkIsType.WF (by simp [FVarsIn])) fun _ _ _ _ => ?_
        exact M.WF.bindThrow .throw
      · exact M.WF.bindThrow .throw
  · -- ``String.ofList
    rename_i hname
    split
    · rename_i htyeq
      split
      · rename_i hguard
        simp only [Bool.and_eq_true, List.isEmpty_iff] at hguard
        obtain ⟨-, rfl⟩ := hguard
        refine M.WF.bind (checkIsType.WF (by simp [FVarsIn] <;> rfl)) fun _ _ _ _ => ?_
        refine M.WF.bind (checkIsType.WF (by simp [FVarsIn] <;> rfl)) fun _ _ _ _ => ?_
        refine M.WF.bind (checkedTypeIs.WF (by simp [FVarsIn] <;> rfl) (by simp [FVarsIn] <;> rfl))
          fun _ _ _ ⟨nil', A1, ty1, hnil, hnilT, hty1, hb1⟩ => ?_
        split <;> [skip; exact M.WF.bindThrow .throw]
        rename_i hb1t
        refine M.WF.bind (checkedTypeIs.WF (by simp [FVarsIn] <;> rfl) (by simp [FVarsIn] <;> rfl))
          fun _ _ _ ⟨cons', A2, ty2, hcons, hconsT, hty2, hb2⟩ => ?_
        split <;> [skip; exact M.WF.bindThrow .throw]
        rename_i hb2t
        -- the two typing facts `PrimField ``String.ofList` needs, read off the two checked
        -- comparisons the recognizer performed
        cases trExprS_constAppChar_inv' hnil
        cases trExprS_listChar_inv' hty1
        cases trExprS_constAppChar_inv' hcons
        cases trExprS_consType_inv' hty2
        have hnilTy : (ves.venv .safe).HasType 0 [] .listCharNil .listChar :=
          hnilT.defeqU_r (VContext.mk' wf .safe [] fuel).Ewf
            (VContext.mk' wf .safe [] fuel).Δwf.toCtx (hb1 hb1t)
        have hconsTy : (ves.venv .safe).HasType 0 []
            .listCharCons (.forallE .char (.forallE .listChar .listChar)) :=
          hconsT.defeqU_r (VContext.mk' wf .safe [] fuel).Ewf
            (VContext.mk' wf .safe [] fuel).Δwf.toCtx (hb2 hb2t)
        refine .pure ⟨fun _ => (by simpa using hsafe), fun _ => rfl, ?_⟩
        intro _ sf venv env'' ci' hle hwf hprim2 htr hci hadd
        refine preserves_glue_const (nm := ``String.ofList) hname rfl (by decide) ?_
          hle hwf hprim2 htr hci hadd
        intro venv2 ci2 hle2 hprim4 htype huv0 env₂ hle₂ hconst
        have hteq := trExprS_listCharString_inv' (htype.eqv htyeq)
        have hmono : ves.venv .safe ≤ env₂ := hle2.trans hle₂
        rw [VEnv.primField_String_ofList]
        intro ci hci2
        rw [hconst] at hci2
        cases hci2
        refine ⟨?_, hnilTy.mono hmono, hconsTy.mono hmono⟩
        show (⟨ci2.uvars, ci2.type⟩ : VConstant) = _
        rw [huv0, hteq]
      · exact M.WF.bindThrow .throw
    · split
      · refine M.WF.bind (checkIsType.WF (by simp [FVarsIn] <;> rfl)) fun _ _ _ _ => ?_
        refine M.WF.bind (checkIsType.WF (by simp [FVarsIn] <;> rfl)) fun _ _ _ _ => ?_
        refine M.WF.bind (checkedTypeIs.WF (by simp [FVarsIn] <;> rfl) (by simp [FVarsIn] <;> rfl))
          fun _ _ _ _ => ?_
        split <;> [skip; exact M.WF.bindThrow .throw]
        refine M.WF.bind (checkedTypeIs.WF (by simp [FVarsIn] <;> rfl) (by simp [FVarsIn] <;> rfl))
          fun _ _ _ _ => ?_
        split <;> exact M.WF.bindThrow .throw
      · exact M.WF.bindThrow .throw
  · exact .pure ⟨nofun, nofun, nofun⟩
