import Lean4Lean.Theory.Inductive.NestedHead

/-!
# The restoration operator, measured at the block that refuted `Canonical`

Ledger ruling **116d**: `VIndField.typeR`'s `some` branch restores the *stored* type instead of
replacing it by `VIndRecArg.canonTypeR`, and `VInductDecl'.Canonical` is dropped.  This file
measures the ruling at the witness that produced it, and it does so in the one form that
cannot be faked: **the same block, the old equation and the new one side by side.**

The block is `CGMRedexWit.cgmBlock` (`Verify/Inductive/CanonGapMeasure.lean` §1) transported to
`VInductDecl'`:

```lean
inductive roT : Type where | mk : ((fun x : Type => roT) Prop) → roT
```

`AddInductive.run`, `Environment.addInductive` and `Lean4Lean.addDecl` all **accept** it from the
empty environment and store the field's type as the β-redex verbatim (executed, `cgm/accept`), and
`AddInductive.isRecArg` classifies the field as **recursive** because it looks at `whnf`.  So
`TrIndDecl.trCtors` forces `F.type` to be the redex while `F.recArg = some r`, and
`VIndCtor.Canonical` — which demands `F.type = r.canonType D i` *syntactically* — is false.

Every name here is prefixed `ro`/`RO`: ledger row 113f records that inside this closure a short
name silently resolves elsewhere, and that the failure mode is a confident wrong measurement.

**What is not claimed.**  This file does not build a `VIndField.WF` at the block — that needs the
block declared in a `VEnv` and is `ntreeAux_WF`-scale.  What it proves is the two things the
ruling turns on: the collapse equation now holds *at a non-canonical block* (`ro_typeR_id`), where
under the old definition it was **false** (`ro_old_typeR_ne`); and the conjunct row 113 showed
`Canonical` was blocking is discharged by a **single β step** (`ro_pos_beta`), with no
Church–Rosser and no escape hypothesis.
-/

namespace Lean4Lean
namespace ROWit

open VExpr (mkPi mkLams mkApp bvars)

/-- `roT`, the block's single member: `Type`, no parameters, no indices. -/
def roName : Lean.Name := `roT

/-- `(fun x : Type => roT) Prop` — the field's **stored** type, an `.app`-headed β-redex whose
`whnf` is the block constant. -/
def roRedex : VExpr := .app (.lam (.sort (.succ .zero)) (.const roName [])) (.sort .zero)

/-- The recursive-field data `isRecArg` computes: empty binder telescope, member `0`, no
indices. -/
def roRec : VIndRecArg := { binders := [], idx := 0, args := [] }

def roField : VIndField :=
  { type := roRedex, lvl := .succ .zero, recArg := some roRec }

def roCtor : VIndCtor :=
  { name := `roT.mk, params := [], fields := [roField], args := [] }

def roType : VIndType :=
  { name := roName, type := .sort (.succ .zero), indices := [], ctors := [roCtor] }

def roDecl : VInductDecl' :=
  { uvars := 0, params := [], lvl := .succ .zero, types := [roType], isLE := false }

/-! ## 1. `Canonical` is false here, and the canonical type is the block constant -/

theorem ro_canonType : roRec.canonType roDecl 0 = .const roName [] := rfl

/-- **`VIndCtor.Canonical` is false at this constructor** — the abstract half of
`CGMAbstract.cgm_not_canonical`, at a block small enough to `decide`. -/
theorem ro_not_canonical : ¬ roCtor.Canonical roDecl := by
  intro h
  exact absurd (h 0 roField roRec rfl rfl) (by decide)

theorem ro_not_canonical_block : ¬ roDecl.Canonical :=
  fun h => ro_not_canonical (h 0 roCtor (by exact List.mem_cons_self))

/-! ## 2. The payoff: the collapse equation holds anyway

`VIndCtor.typeR_id` (`Theory/Inductive/NestedHead.lean` Part 3) is now **unconditional**, so it
applies here — at a block where its former hypothesis is false. -/

/-- **The collapse, at the non-canonical block.**  This is ruling 116d's payoff in one line: the
former hypothesis of this equation is refuted at this very block (`ro_not_canonical`), and the
equation holds. -/
theorem ro_typeR_id : roCtor.typeR roDecl roDecl.idRestore 0 = roCtor.type roDecl 0 :=
  VIndCtor.typeR_id

/-- …and `VIndField.typeR` returns the **stored** redex, not the canonical constant. -/
theorem ro_field_typeR : roField.typeR roDecl roDecl.idRestore 0 = roRedex := rfl

/-- **The old definition made the collapse FALSE here.**  `typeROld` is `VIndCtor.typeR` with
`VIndField.typeR`'s pre-116d `some` branch (`r.canonTypeR D R i`) spliced in; the two sides differ
syntactically, and `TrConstant` goes through `TrExprS`, which has no defeq slack. So the old
specification declared `roT.mk` at a type the kernel does not store. -/
def roTypeROld (C : VIndCtor) (D : VInductDecl') (R : VIndRestore) (j : Nat) : VExpr :=
  mkPi (C.params ++ C.fields.zipIdx.map (fun (F, i) =>
    match F.recArg with
    | none => F.type
    | some r => r.canonTypeR D R i)) (D.tyAppR R j C.fields.length C.args)

theorem ro_old_typeR_ne :
    roTypeROld roCtor roDecl roDecl.idRestore 0 ≠ roCtor.type roDecl 0 := by decide

/-- …and the new one *is* the stored type, on the nose. -/
theorem ro_new_typeR_eq_stored :
    roCtor.typeR roDecl roDecl.idRestore 0
      = mkPi [roRedex] (VExpr.const roName []) := by decide

/-! ## 3. The residue row 113 blamed on `Canonical`, discharged by one β step

`VIndField.WF.pos`'s `some` branch ends in `env.IsDefEqType D.uvars Γ F.type (r.canonType D i)`.
At this block that is `redex ≡ roT`, and it is `IsDefEq.beta` — nothing else.  The hypothesis is
that the block's own type constant is declared at `Sort 1`, which is exactly what
`VInductDecl'.WF`'s constructor clause has in hand (it is stated over `env₁ = env.addIndTypes D`).

Compare `CGMAbstract.CGMEscape` (`Verify/Inductive/CanonGapMeasure.lean` §6), the residue the
*old* apparatus left: a **block-free** `A` definitionally equal to the redex, which is
Church–Rosser strength to refute and had no known inhabitant.  It arose only because
`D.Canonical` forced `recArg = none`, and `Canonical` is no longer a conjunct of
`VEnv.AddNested`. -/

theorem ro_pos_beta {env : VEnv} {Γ : List VExpr}
    (hT : env.HasType 0 (VExpr.sort (.succ .zero) :: Γ)
      (.const roName []) (.sort (.succ .zero))) :
    env.IsDefEqType 0 Γ roField.type (roRec.canonType roDecl 0) :=
  ⟨.succ .zero, .beta hT (.sortDF trivial trivial rfl)⟩

/-- The block's own type constant, declared by the type stage, has exactly that type — so
`ro_pos_beta`'s hypothesis is `IsDefEq.constDF` at `env.addIndTypes roDecl` and nothing more. -/
theorem ro_typeConsts : roDecl.typeConsts = [(roName, ⟨0, .sort (.succ .zero)⟩)] := rfl

/-! ### 3.1 …and then **every** conjunct of `VIndField.WF` holds at the redex field

This is the ruling's payoff claim in full: at the redex block, with `Canonical` gone, the field is
well-formed on the `some` branch — `binders_indep` vacuous (`pre = []`), the index and freshness
clauses `decide`-able, `OnCtx`/`HasArgs` trivial at the empty context, and the two typing clauses
`constDF`/`sortDF`/`appDF`/`lamDF` plus **one `beta`**.  No Church–Rosser, no escape hypothesis,
and no `sorryAx` (see the axiom prints below).

The single hypothesis is that the environment holds the block's own type constant at the type the
type stage declares it at (`ro_typeConsts`), which is what `VInductDecl'.WF.ctors` is stated over. -/

/-- The block's own type constant, at the type the type stage declares it at. -/
theorem ro_const_hasType {env : VEnv} {Γ : List VExpr}
    (hc : env.constants roName = some ⟨0, .sort (.succ .zero)⟩) :
    env.HasType 0 Γ (.const roName []) (.sort (.succ .zero)) :=
  .constDF hc nofun nofun rfl .nil

theorem ro_field_hasType {env : VEnv} {Γ : List VExpr}
    (hc : env.constants roName = some ⟨0, .sort (.succ .zero)⟩) :
    env.HasType 0 Γ roRedex (.sort (.succ .zero)) :=
  VEnv.IsDefEq.appDF (A := .sort (.succ .zero)) (B := .sort (.succ .zero))
    (.lamDF (u := .succ (.succ .zero)) (.sortDF trivial trivial rfl) (ro_const_hasType hc))
    (.sortDF trivial trivial rfl)

theorem ro_field_WF {env : VEnv} (hc : env.constants roName = some ⟨0, .sort (.succ .zero)⟩) :
    VIndField.WF env roDecl [] [] 0 roField where
  hasType := ro_field_hasType hc
  level := fun _ => Nat.le_refl _
  pos := by
    refine ⟨by decide, by decide, nofun, nofun, trivial, ?_, ?_, ro_pos_beta (ro_const_hasType hc), by decide⟩
    · exact ro_const_hasType hc
    · rintro T' hT'; cases hT'; exact .nil
  binders_indep := by rintro r - i' t F' ⟨⟩

/-! ## 4. Instrument 7 and its dual

**Instrument 7** (a statement green because its hypotheses are unsatisfiable at the degenerate
instance): `ro_typeR_id`, `ro_field_typeR`, `ro_new_typeR_eq_stored`, `ro_old_typeR_ne`,
`ro_canonType`, `ro_typeConsts` have **no hypotheses at all**, so there is nothing to be
unsatisfiable.  `ro_not_canonical`/`ro_not_canonical_block` are negations of closed statements.
`ro_pos_beta`'s single hypothesis is inhabited: it is `IsDefEq.constDF` against
`ro_typeConsts`'s entry, whose level list is empty and whose `uvars` is `0`.

**Its dual** (a statement green because the difficulty moved into a hypothesis with no known
inhabitant — ledger row 116g): the honest accounting is that ruling 116d moves conditionality out
of `NestedHead.lean` Part 3 and into exactly two places, both named and both *inhabited*:

* `VIndRestore.typeR_canonical` (`Theory/Inductive/Restore.lean`) — canonicity plus block-free
  binders plus `Nodup`, for the statements that genuinely read `canonTypeR` off the restored field
  telescope.  Its binder clause is a `VIndField.WF.pos` conjunct
  (`VIndField.WF.recArg_noBlock`), so no consumer holding `D.WF env` pays for it; its `Nodup` is
  what `VEnv.addConstList`'s success already forces.  **Canonicity itself is still owed there**,
  and `ro_not_canonical` is where it fails — but nothing in `VEnv.AddNested`,
  `VEnv.AddNestedB` or `NestedHead.lean` Part 3 asks for it any more.
* `VInductDecl'.Built.fields_noK` (`Theory/Inductive/NestedBuild.lean`) — the price paid by
  `VNestedOcc.field_typeR`, which used to hold with no hypotheses because the old `typeR`
  *discarded* the stored type. It is discharged at both nested witnesses
  (`ntreeAux_built`, `nfnAux_built`, `nfnAuxDirty_built`), so it is not vacuous, and it is a
  statement about the freshness of the auxiliary names rather than about the shape of a field.
-/

#print axioms Lean4Lean.ROWit.ro_not_canonical
#print axioms Lean4Lean.ROWit.ro_typeR_id
#print axioms Lean4Lean.ROWit.ro_old_typeR_ne
#print axioms Lean4Lean.ROWit.ro_new_typeR_eq_stored
#print axioms Lean4Lean.ROWit.ro_pos_beta
#print axioms Lean4Lean.ROWit.ro_const_hasType
#print axioms Lean4Lean.ROWit.ro_field_hasType
#print axioms Lean4Lean.ROWit.ro_field_WF
#print axioms Lean4Lean.VIndRestore.restore_id
#print axioms Lean4Lean.VIndCtor.typeR_id
#print axioms Lean4Lean.VEnv.addInductR_eq_addInduct'
#print axioms Lean4Lean.VEnv.AddNested_nil
#print axioms Lean4Lean.VIndRestore.restore_canonType
#print axioms Lean4Lean.VIndRestore.restore_noK

end ROWit
end Lean4Lean
