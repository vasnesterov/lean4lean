import Lean4Lean.Verify.TypeChecker
import Lean4Lean.Verify.Primitive
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

What remains is the four operations whose equations the recognizer verifies through fuel
recursion (`Nat.mod`, `Nat.div`) or `WellFounded.Nat.fix` (`Nat.gcd`, `Nat.bitwise`). The other
fifteen branches are discharged below, using the reflection theorems and the `VEnv.PrimField` /
`VEnv.HasPrimitives.addDef` plumbing in `Lean4Lean/Verify/Primitive.lean`.

Those four are not merely unproved. Bug 4 of `bugs-found.md` -- handing untyped terms to
`isDefEq`, which records its verdict in the `EquivManager` and so breaks `VState.WF` -- was
fixed for the other fifteen branches by `checkPrimValue`/`checkIsType`/`checkedIsDefEq`/
`checkedTypeIs`, but *not* for these four. They still compare terms neither side of which has
been type-checked, both directly and through the helpers they share:

* `Condition.check` (`Primitive.lean:125,133,134`) runs `inferType`, not `checkType`, on
  `cond.prop`, `asBool` and `proof` -- and `inferType` assumes its argument is already
  well-typed, which is the precondition the recognizer cannot have;
* `Reflection.check` (`:50`), `Reflection.checkITE` (`:94,98,100`) and
  `Reflection.checkNatDITE` (`:103-118`) compare against unchecked literal right-hand sides;
* `unfoldWellFounded` (`:169-173`) and `unfoldNatWellFounded` (`:205,211,213,221,237,245`)
  likewise;
* and the branches themselves: `Nat.mod` (`:374,376,386,393`), `Nat.div` (`:401,403,410,417`),
  `Nat.gcd` (`:427,428`), `Nat.bitwise` (`:470`).

So this statement cannot be proved the way the other fifteen are, and the first step is to
extend the same remedy to these sites. Whether a declaration exists that *exploits* the gap --
passing the recognizer while leaving an untranslatable term in the `EquivManager` -- has not
been established either way; the fifteen fixed branches were each closed without needing such a
witness. Beyond that the four need genuinely new reflection arguments (fuel recursion for
`mod`/`div`, `WellFounded.Nat.fix` for `gcd`/`bitwise`), which the fifteen did not. -/
theorem checkPrimitiveDef.WF.rest {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (fuel : FuelConfig)
    (hrest : v.name = ``Nat.mod ∨ v.name = ``Nat.div ∨ v.name = ``Nat.gcd ∨
      v.name = ``Nat.bitwise) :
    (Environment.checkPrimitiveDef v).WF (.mk' wf .safe v.levelParams fuel) {} fun allow _ =>
      PrimitiveResult (ves.venv .safe) v allow := sorry

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
    refine hprim3.natBitwise (VEnv.contains.mono hle' hbwC) env₂ hle₂ G and ?_ a b
    refine VEnv.reflectsBoolBoolBool_and ?_ ?_
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
    refine hprim3.natBitwise (VEnv.contains.mono hle' hbwC) env₂ hle₂ G or ?_ a b
    refine VEnv.reflectsBoolBoolBool_or ?_ ?_
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
    refine hprim3.natBitwise (VEnv.contains.mono hle' hbwC) env₂ hle₂ G bne ?_ a b
    exact VEnv.reflectsBoolBoolBool_bne (hq1.mono hle3) (hq2.mono hle3)
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
