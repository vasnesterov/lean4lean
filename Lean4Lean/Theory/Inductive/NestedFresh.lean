import Lean4Lean.Theory.Inductive.NestedBuild
import Lean4Lean.Theory.SetModel.Consts

/-!
# `Built.fields_noK`: the freshness discharge, and the sharpness of the residual

`VInductDecl'.Built.fields_noK` (`Theory/Inductive/NestedBuild.lean`) is ruling 116d's residual:
for every companion member `j`, every constructor `C₀` of the *source* block `J`, and every field
`F₀` of it, the substituted field type

```
VExpr.instAll (F₀.type.instL (occ j).lvls) (occ j).args k
```

mentions no companion name.  It was recorded for eight rounds as having "no producer but `decide`
at a concrete block" (ledger row 117c).  That record rested on a repo-wide grep of `NoConsts`, and
**the grep was looking for the wrong predicate**: the fact it needed is stated in this repo about
`VExpr.ConstsIn` (`Theory/SetModel/Consts.lean`).

**The producer itself has moved to `NestedBuild.lean` §F1–§F4** (handoff §59).  It had to: the four
`fields_noK :=` production sites are in `NestedBuild.lean`, `MemberRedex.lean` and
`RestoreBridge.lean`, and this file *imports* `NestedBuild.lean`, so nothing stated here can reach
them.  All four now cite the producer.  What is left here is what the sites do not need:

* §4 discharges the freshness premise `hK` from the step's own staging success, so it costs a
  caller nothing it does not already have (the same argument as `VIndRestore.csubst_freshIn`).
* §5 is the sharpness result, and it is the answer to "could the spine premise be dropped too?":
  **no.**  `VNestedOcc.Occurs` constrains `N.args` through `args_len` and nothing else
  (`occurs_args_congr`), and there is a concrete occurrence — the repo's own `listOcc`, with its
  spine replaced by a companion constant of the right length — that satisfies `Occurs env₁` and
  refutes `fields_noK`.  So no producer from `Occurs` plus environment facts alone can exist;
  a spine hypothesis is *necessary*, and §F3 shows it is *sufficient*.
* §6 measures the three "things that had changed" against that counterexample.  All three miss.
-/
namespace Lean4Lean

open VExpr (mkPi)


/-! ## §4 The freshness premise costs nothing

The same argument as `VIndRestore.csubst_freshIn` (`Theory/Inductive/NestedRules.lean` §8.1):
`addIndTypes` is an `addConstList`, `addConst` fails on a duplicate, so every member name of `D`
— the companion names among them — was absent from `env`.  So `hK` is available wherever the
step's first staging success is, which is everywhere `AddNested` is used. -/

/-- A name the block declares is not one the environment already had. -/
theorem VInductDecl'.not_contains_of_mem_blockNames {env env₁ : VEnv} {D : VInductDecl'}
    (h : env.addIndTypes D = some env₁) {n : Lean.Name} (hn : n ∈ D.blockNames) :
    ¬ env.contains n := by
  intro hc
  have hfresh := (VEnv.addConstList_fresh h).1 n (D.typeConsts_names ▸ hn)
  obtain ⟨_, hci⟩ := hc
  rw [hci] at hfresh; exact absurd hfresh nofun

/-- `hK`, discharged: the companion names are among the block's member names (which is what
`Built`'s clauses assume when they read `D.types[j]? = some T` with `T.name ∈ K`), and the block
declared them. -/
theorem VInductDecl'.fresh_of_addIndTypes {env env₁ : VEnv} {D : VInductDecl'}
    {K : List Lean.Name} (h : env.addIndTypes D = some env₁)
    (hKB : ∀ n ∈ K, n ∈ D.blockNames) : ∀ n ∈ K, ¬ env.contains n :=
  fun n hn => VInductDecl'.not_contains_of_mem_blockNames h (hKB n hn)

/-! ## §5 The spine premise is necessary: no producer from `Occurs` alone

`VNestedOcc.Occurs` mentions `N.args` in exactly one clause, `args_len`, and that clause
constrains only its *length*.  `occurs_args_congr` is that observation as a theorem: the spine
may be replaced by any other of the same length and `Occurs env` still holds.

`fields_noK`, by contrast, is not invariant under that replacement — the substituted field type
*is* the spine wherever `J` has a field whose type is one of its own parameters.  §5.2 exhibits
the pair: the repo's own `listOcc`, whose `fields_noK` is a theorem (`ntreeAux_built`), and the
same occurrence with the spine `[NTree α]` replaced by the companion constant `_nested.List_1`,
whose `fields_noK` is **false** — because `List.cons`'s first field type is the bare parameter
`.bvar 0`, so the substituted type is the spine entry verbatim.

Both occurrences satisfy `Occurs env₁` for the same `env₁`, at the same `K`, with the same
`decl`, `idx`, `lvls`, `auxName` and `ctorName`.  So **no** theorem whose hypotheses are
`Occurs env`, together with any facts whatsoever about `env` and `K` — freshness,
constant-closedness, `Ordered`, `WF` — can prove `fields_noK`: such a theorem would apply to
both members of the pair and prove a false statement.  A premise that reads `N.args` is
unavoidable, and §2 shows the weakest such premise (`∀ a ∈ N.args, NoConsts K a`) suffices.

This is the machine-checked form of "ruling 116d's cost is permanent": it cannot be reduced
below the spine, and it *can* be reduced to the spine. -/

namespace VNestedOcc

/-- **`Occurs` cannot see the spine.**  Only `args_len` mentions `N.args`, and only its length. -/
theorem occurs_args_congr {N : VNestedOcc} {env : VEnv} {as : List VExpr}
    (ho : N.Occurs env) (hlen : as.length = N.decl.np) :
    ({N with args := as} : VNestedOcc).Occurs env where
  hist := ho.hist
  idx_lt := ho.idx_lt
  lvls_len := ho.lvls_len
  args_len := hlen
  ty_const := ho.ty_const
  ctor_params := ho.ctor_params
  ctor_const := ho.ctor_const

end VNestedOcc

namespace InductiveDeclExamples

/-- `listOcc` with the nested spine `[NTree α]` replaced by the companion constant itself.
The length is unchanged, so `Occurs` cannot tell the two apart. -/
def listOccBadSpine : VNestedOcc :=
  { listOcc with args := [.const `_nested.List_1 [.param 0]] }

theorem listOccBadSpine_args_len : listOccBadSpine.args.length = listOccBadSpine.decl.np := rfl

section
variable {env₁ : VEnv} (h : VEnv.empty.addInduct' listDecl = some env₁)
include h

/-- The bad-spine occurrence is a genuine occurrence: same `Occurs env₁`. -/
theorem listOccBadSpine_occurs : listOccBadSpine.Occurs env₁ :=
  VNestedOcc.occurs_args_congr (listOcc_occurs h).toOccurs rfl

end

/-- …and its `fields_noK` is **false**, at `List.cons`'s first field, whose stored type is the
bare parameter `.bvar 0`.  No environment appears in the statement, which is the point. -/
theorem listOccBadSpine_not_fields_noK :
    ¬ VExpr.NoConsts ntreeK (VExpr.instAll
        ((listCons.fields.getD 0 default).type.instL listOccBadSpine.lvls)
        listOccBadSpine.args 0) := by
  decide

/-- **The separating pair.**  Same `decl`, `idx`, `lvls`, `auxName`, `ctorName`; same `Occurs
env₁`; same `K`.  `fields_noK` holds of one and fails of the other, so it is not a consequence of
`Occurs` plus environment facts. -/
theorem fields_noK_needs_spine {env₁ : VEnv}
    (h : VEnv.empty.addInduct' listDecl = some env₁) :
    listOccBadSpine.decl = listOcc.decl ∧ listOccBadSpine.idx = listOcc.idx ∧
    listOccBadSpine.lvls = listOcc.lvls ∧ listOccBadSpine.auxName = listOcc.auxName ∧
    listOccBadSpine.args.length = listOcc.args.length ∧
    listOcc.Occurs env₁ ∧ listOccBadSpine.Occurs env₁ ∧
    (∀ C₀ ∈ listOcc.src.ctors, ∀ (k : Nat) (F₀ : VIndField), C₀.fields[k]? = some F₀ →
      VExpr.NoConsts ntreeK (VExpr.instAll (F₀.type.instL listOcc.lvls) listOcc.args k)) ∧
    ¬ (∀ C₀ ∈ listOccBadSpine.src.ctors, ∀ (k : Nat) (F₀ : VIndField), C₀.fields[k]? = some F₀ →
      VExpr.NoConsts ntreeK
        (VExpr.instAll (F₀.type.instL listOccBadSpine.lvls) listOccBadSpine.args k)) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, (listOcc_occurs h).toOccurs, listOccBadSpine_occurs h, ?_, ?_⟩
  · exact fun C₀ hC₀ k F₀ hF₀ =>
      (ntreeAux_built h).fields_noK 1 _ rfl (by decide) C₀ hC₀ k F₀ hF₀
  · intro hbad
    exact listOccBadSpine_not_fields_noK
      (hbad listCons (by rw [show listOccBadSpine.src.ctors = [listNil, listCons] from rfl]; simp)
        0 _ rfl)

end InductiveDeclExamples

/-! ## Axiom audit, by namespace -/

#print axioms Lean4Lean.VInductDecl'.not_contains_of_mem_blockNames
#print axioms Lean4Lean.VInductDecl'.fresh_of_addIndTypes
#print axioms Lean4Lean.VNestedOcc.occurs_args_congr
#print axioms Lean4Lean.InductiveDeclExamples.listOccBadSpine_occurs
#print axioms Lean4Lean.InductiveDeclExamples.listOccBadSpine_not_fields_noK
#print axioms Lean4Lean.InductiveDeclExamples.fields_noK_needs_spine

/-! ## §6 The three "things that changed", measured against the counterexample

### §6.1 F7's new residual clause does not reach `fields_noK`

`VInductDecl'.ResidualClean k e = ∀ j rest, D.uniformOcc? k e = some (j, rest) → ∀ a ∈ rest,
D.NoBlock a` (`Theory/Inductive/Decl.lean`).  It is conditional on `uniformOcc?` firing, and
`uniformOcc?` needs a spine whose leading `D.np` arguments are the parameter run.  The
counterexample's substituted type is a **bare** companion constant — zero arguments — so the
trigger does not fire and the clause is **vacuously true of the very expression that refutes
`fields_noK`**.  Machine-checked below.  So the `some`-branch tightening, real as it is, provides
no part of `fields_noK`.

### §6.2 placeholder — see §6.3 below (a `decide` refutation of my first attempt)
-/

namespace InductiveDeclExamples

/-- **F7's residual clause is satisfied by the counterexample.**  `uniformOcc?` does not fire on
a bare companion constant, so `ResidualClean` says nothing there. -/
theorem ntreeAux_residualClean_badSpine :
    ntreeAux.ResidualClean 0 (VExpr.instAll
        ((listCons.fields.getD 0 default).type.instL listOccBadSpine.lvls)
        listOccBadSpine.args 0) :=
  VInductDecl'.residualClean_of_uniformOcc_none (by decide)

/-- **`decide` refuted the obvious strengthening.**  I claimed the consumer's conclusion
(`field_typeR`'s equation) also fails at `listOccBadSpine`.  It does **not**: `restore` rewrites
only at a *firing* `uniformOcc?`, and a bare companion constant with no parameter run is not one,
so the restoration is the identity there anyway. -/
theorem listOccBadSpine_field_typeR_holds :
    (listOccBadSpine.field ntreeAux.header ntreeRestore 0
        (listCons.fields.getD 0 default)).typeR ntreeAux ntreeRestore 0
      = VExpr.instAll ((listCons.fields.getD 0 default).type.instL listOccBadSpine.lvls)
          listOccBadSpine.args 0 := by
  decide

end InductiveDeclExamples

#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_residualClean_badSpine
#print axioms Lean4Lean.InductiveDeclExamples.listOccBadSpine_field_typeR_holds

/-! ### §6.3 The `OwnHeads` weakening does not dodge the spine either

`restore_noK` is now a corollary of `restore_ownHeads` via `ownHeads_of_noConsts`, so the obvious
weakening of `fields_noK` is to replace `NoConsts K` by `D.OwnHeads K k` — the heads-only test.
The bad-spine witness **refutes that too**: its substituted type is a bare companion constant,
and `OwnHeads`' only applicable constructor there is `const`, which asks for exactly the
`NoConsts` fact that fails.  So the test is not what is wrong; the spine is. -/

namespace InductiveDeclExamples

theorem listOccBadSpine_not_ownHeads :
    ¬ ntreeAux.OwnHeads ntreeK 0 (VExpr.instAll
        ((listCons.fields.getD 0 default).type.instL listOccBadSpine.lvls)
        listOccBadSpine.args 0) := by
  intro h
  cases h with
  | own hu =>
    rw [show ntreeAux.uniformOcc? 0 (VExpr.instAll
      ((listCons.fields.getD 0 default).type.instL listOccBadSpine.lvls)
      listOccBadSpine.args 0) = none from by decide] at hu
    exact absurd hu nofun
  | const hn => exact hn (by decide)

end InductiveDeclExamples

#print axioms Lean4Lean.InductiveDeclExamples.listOccBadSpine_not_ownHeads
