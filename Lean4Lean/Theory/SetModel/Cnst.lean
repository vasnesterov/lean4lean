import Lean4Lean.Theory.SetModel.SoundInduction
import Lean4Lean.Theory.Typing.Env

/-!
# Building the constant assignment

`ModelData.cnst` is supplied rather than computed, which is what made the term
recursion in `SetModel/Interp.lean` structural.  This file discharges that
trade: `cnstOf` builds the assignment by recursion on the declaration list, and
the coherence obligations are met one declaration at a time.

## Shape

Every declaration form extends the environment in exactly two ways — a fold of
`addConst` and a fold of `addDefEq` — so the whole construction goes through two
step lemmas, `coherentOn_addConst` and `coherentOn_addDefEq`
(`SetModel/InterpSound.lean`), lifted here to lists.  Nothing is special-cased
per constructor beyond *where each value comes from*:

| Declaration | Value of `cnst` |
|---|---|
| `.def`, `.opaque` | `⟦value⟧` at the earlier stage — `defExtend` |
| `.example` | nothing; the environment is unchanged |
| `.axiom`, `.quot`, `.induct` | the oracle — `oracleExtend` |

The oracle is a parameter with an obligation (`OracleOK`), so the three forms
whose values the model must *supply* rather than *compute* are handled
uniformly. `.axiom`'s obligation is discharged by the axiom-freedom hypothesis
of the main theorem together with the three standard axioms' model-side
validations; `.quot`'s and `.induct`'s by `SetModel/Universe.lean` and
`SetModel/IndStage.lean`/`IndCard.lean` respectively.
-/

namespace Lean4Lean.SetModel

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ} {L : LevelAssign envF nv} {κ : ℕ → V} {ls : List ℕ}

/-- Extend an assignment along a list of names, each value taken from the
oracle.  Every declaration form that adds a *block* of constants — `quot`,
`induct` — goes through this, so the constructor list is not hardcoded anywhere
but in `cnstOf` itself. -/
noncomputable def oracleExtend (o : Name → List VLevel → V) :
    List Name → (Name → List VLevel → V) → (Name → List VLevel → V)
  | [], c => c
  | n :: ns, c => oracleExtend o ns (cnstUpdate c n (o n))

/-! ## Definitions: the value is the body's denotation -/

/-- `cnst` for a definition: the denotation of its body, at the assignment the
earlier declarations produced. -/
noncomputable def defExtend (L : LevelAssign envF nv) (κ : ℕ → V) (ls : List ℕ)
    (c : Name → List VLevel → V) (ci : VDefVal) : Name → List VLevel → V :=
  cnstUpdate c ci.name fun us ↦ (interp ⟨κ, ls, c⟩ L [] (ci.value.instL us)).toFun ∅

section Step

variable {env env' : VEnv} {c : Name → List VLevel → V} {R : List VExpr → List VExpr → Prop}
variable (hle : env ≤ envF) (henv : env.Ordered) (hS : L.Stable)
  (hC : CoherentOn ⟨κ, ls, c⟩ L env) (hR : CtxInvariant L R)
  (hRd : ∀ {Γ : List VExpr} {A A' : VExpr} {u : VLevel},
    env.IsDefEq nv Γ A A' (.sort u) → R (A' :: Γ) (A :: Γ))

include hle henv hS hC hR hRd in
/-- **The constant a definition or an opaque declaration adds.**

Both obligations come straight from soundness at the *earlier* environment:
`const_congr` from `IsDefEq.instL_r` (instantiating at pointwise-equivalent
level lists gives definitionally equal terms), `const_type` from `IsDefEq.instL`
together with `VDefVal.WF`. -/
theorem coherentOn_defConst {ci : VDefVal} (hci : ci.WF env)
    (hadd : env.addConst ci.name ci.toVConstant = some env') :
    CoherentOn ⟨κ, ls, defExtend L κ ls c ci⟩ L env' := by
  have hocc := VEnv.IsDefEq.constsIn henv.constsIn hci trivial
  refine coherentOn_addConst L henv.constsClosed hadd hC (fun {us us'} hw hw' hdd ↦ ?_)
    (fun {us} hw hlen ↦ ?_)
  · exact Above.imp (sound_nil hle henv hS hC hR hRd
      (VEnv.IsDefEq.instL_r (Γ := []) henv trivial hw hw' hdd hci)) fun h ↦ h.1
  · have key : interp ⟨κ, ls, defExtend L κ ls c ci⟩ L [] (ci.type.instL us)
        = interp ⟨κ, ls, c⟩ L [] (ci.type.instL us) :=
      interp_cnst_congr L _ [] <| ConstsAgree.of_constsIn <|
        (VExpr.ConstsIn.instL.2 hocc.2.2).mono fun m hm _ ↦ by
          have hne : m ≠ ci.name := fun h ↦ by
            obtain ⟨_, hmm⟩ := hm
            rw [h, (VEnv.addConst_spec hadd).1] at hmm; exact absurd hmm nofun
          simp only [defExtend, cnstUpdate, if_neg hne]
    show Above _ (_ ∈ (interp ⟨κ, ls, defExtend L κ ls c ci⟩ L [] _).toFun ∅)
    rw [key]
    exact Above.imp (sound_nil hle henv hS hC hR hRd (hci.instL hw)) fun h ↦ h.2

include hle henv hS hC hR hRd in
/-- **The defining equation a definition adds.**  `VDefVal.toDefEq` equates
`.const c (params)` with the body; at a level instantiation of the right length
`VLevel.inst_map_id` turns the parameter list into the instantiation itself, so
the left-hand side is exactly the value `defExtend` assigned. -/
theorem coherentOn_defEq {ci : VDefVal} (hci : ci.WF env)
    (hadd : env.addConst ci.name ci.toVConstant = some env') :
    CoherentOn ⟨κ, ls, defExtend L κ ls c ci⟩ L (env'.addDefEq ci.toDefEq) := by
  have hocc := VEnv.IsDefEq.constsIn henv.constsIn hci trivial
  have hstep := coherentOn_defConst hle henv hS hC hR hRd hci hadd
  have hfresh : ∀ {m : Name}, env.contains m → m ≠ ci.name := fun {m} hm h ↦ by
    obtain ⟨_, hmm⟩ := hm
    rw [h, (VEnv.addConst_spec hadd).1] at hmm; exact absurd hmm nofun
  have key : ∀ {e : VExpr}, e.ConstsIn env.contains →
      interp ⟨κ, ls, defExtend L κ ls c ci⟩ L [] e = interp ⟨κ, ls, c⟩ L [] e := fun he ↦
    interp_cnst_congr L _ [] <| ConstsAgree.of_constsIn <| he.mono fun m hm _ ↦ by
      simp only [defExtend, cnstUpdate, if_neg (hfresh hm)]
  -- the left-hand side's denotation *is* the assigned value
  have hlhs : ∀ {us : List VLevel}, us.length = ci.uvars →
      (interp ⟨κ, ls, defExtend L κ ls c ci⟩ L [] (ci.toDefEq.lhs.instL us)).toFun ∅
        = (interp ⟨κ, ls, c⟩ L [] (ci.value.instL us)).toFun ∅ := by
    intro us hlen
    show (interp ⟨κ, ls, defExtend L κ ls c ci⟩ L []
      (.const ci.name ((VLevel.params ci.uvars).map (VLevel.inst us)))).toFun ∅ = _
    rw [VLevel.inst_map_id hlen, interp_const]
    show defExtend L κ ls c ci ci.name us = _
    unfold defExtend cnstUpdate
    rw [if_pos rfl]
  refine coherentOn_addDefEq hstep (fun {us} hw hlen ↦ ?_) (fun {us} hw hlen ↦ ?_)
  · refine Above.pure ?_
    show _ = (interp ⟨κ, ls, defExtend L κ ls c ci⟩ L [] (ci.value.instL us)).toFun ∅
    rw [hlhs hlen, key (VExpr.ConstsIn.instL.2 hocc.1)]
  · show Above _ (_ ∈ (interp ⟨κ, ls, defExtend L κ ls c ci⟩ L [] (ci.type.instL us)).toFun ∅)
    rw [hlhs hlen, key (VExpr.ConstsIn.instL.2 hocc.2.2)]
    exact Above.imp (sound_nil hle henv hS hC hR hRd (hci.instL hw)) fun h ↦ h.2

end Step

/-! ## The assignment

`cnstOf` is a structural recursion on the declaration list, matching the order
`VEnv.WF'` gives.  `interp_cnst_congr` is what makes it *extend* rather than
revisit: a term already interpreted keeps its denotation, because the
interpretation depends on `cnst` only at the constants that occur in it. -/

/-- The names `VEnv.addQuot` declares, in the order it declares them. -/
def quotNames : List Name := [``Quot, ``Quot.mk, ``Quot.lift, ``Quot.ind]

/-- **The constant assignment of a declaration list.**

`o` is the oracle: it supplies the values the model cannot compute — axioms,
the `Quot` primitives, and whatever an inductive declaration introduces.  Its
obligations are `OracleOK`; everything else is computed. -/
noncomputable def cnstOf (L : LevelAssign envF nv) (κ : ℕ → V) (ls : List ℕ)
    (o : Name → List VLevel → V) : List VDecl → (Name → List VLevel → V)
  | [] => fun _ _ ↦ ∅
  | .axiom ci :: ds => cnstUpdate (cnstOf L κ ls o ds) ci.name (o ci.name)
  | .def ci :: ds => defExtend L κ ls (cnstOf L κ ls o ds) ci
  | .opaque ci :: ds => defExtend L κ ls (cnstOf L κ ls o ds) ci
  | .example _ :: ds => cnstOf L κ ls o ds
  | .quot :: ds => oracleExtend o quotNames (cnstOf L κ ls o ds)
  | .induct D :: ds => oracleExtend o D.allNames (cnstOf L κ ls o ds)
  -- `mutualDef` has no image: a self-referential block has no assignment at
  -- all (`Theory/MutualDefUnsound.lean`), and the constructor is being removed.
  | .mutualDef _ :: ds => cnstOf L κ ls o ds

end Lean4Lean.SetModel
