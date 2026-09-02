import Lean4Lean.Verify.Inductive.NestedRestoreWit
import Lean4Lean.Theory.Inductive.NestedFresh

/-!
# The general bridge, with `BuiltFresh` reduced to the spine

`ElimNestedInductive.Result.RestoreData.mkRestore_built` (`Verify/Inductive/NestedRestoreWit.lean`
§6) takes `VInductDecl'.BuiltFresh` as a hypothesis, with the note that ruling 116d's cost sits
there and that **nothing in `RestoreData` or `OccData` mentions it**, "since both bundles are
about the checker's `Lean.Name`s".

Half of that is now out of date.  `Theory/Inductive/NestedFresh.lean` derives `BuiltFresh`'s
`fields_noK` clause from

* `env.ConstsClosed` — an environment invariant (`VEnv.Ordered.constsClosed`), not a side
  condition;
* `OccResidue.occurs` — which the bridge already takes;
* freshness of `K` in `env` — free from the step's `addIndTypes` success
  (`VInductDecl'.fresh_of_addIndTypes`);
* cleanliness of the **spine**, and the spine is `as`, which **is** one of `RestoreData`'s own
  parameters.

So the residual hypothesis is a statement about `as j`, a list of `D.np` expressions the checker
produces, decidable by `VExpr.decidableNoConsts` — not about a foreign block's constructors and
fields.  `nodup` is unchanged and is still the other half of `BuiltFresh`.

These are **additive**: the originals are untouched, so nothing downstream moves.
-/

namespace Lean4Lean
namespace ElimNestedInductive.Result.RestoreData

variable {r : Result} {types : List Lean.InductiveType} {D : VInductDecl'} {K : List Lean.Name}
  {ls : Nat → List VLevel} {as : Nat → List VExpr} {env : VEnv} {occ : Nat → VNestedOcc}
  (h : r.RestoreData types D K as)

include h

/-- **`Built` with `fields_noK` discharged, leaving the spine.**  Compare `mkRestore_built`: the
`BuiltFresh` argument is replaced by `nodup` plus three facts a caller already has and one about
`as`. -/
theorem mkRestore_built_of_spine (hcc : env.ConstsClosed) (hnd : D.blockNames.Nodup)
    (hK : ∀ n ∈ K, ¬ env.contains n)
    (hspine : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K →
      ∀ a ∈ as j, VExpr.NoConsts K a)
    (hl : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K → ls j = (occ j).lvls)
    (ha : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K → as j = (occ j).args)
    (hres : r.OccResidue types D K env (r.mkRestore types D.uvars D.np ls as) occ) :
    D.Built (r.mkRestore types D.uvars D.np ls as) K env occ :=
  h.mkRestore_built
    (VInductDecl'.builtFresh_of_occurs hcc hnd hres.occurs hK
      fun j T hT hKT a hmem =>
        hspine j T hT hKT a (by rw [ha j T hT hKT]; exact hmem))
    hl ha hres

/-- …and the whole step.  `hadd`'s own `addIndTypes` success is what would discharge `hK`
(`VInductDecl'.fresh_of_addIndTypes`), given `K ⊆ D.blockNames`. -/
theorem mkRestore_AddNested_of_spine {env' : VEnv} (hwf : D.WF env) (hcc : env.ConstsClosed)
    (hnd : D.blockNames.Nodup) (hK : ∀ n ∈ K, ¬ env.contains n)
    (hspine : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K →
      ∀ a ∈ as j, VExpr.NoConsts K a)
    (hl : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K → ls j = (occ j).lvls)
    (ha : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K → as j = (occ j).args)
    (hres : r.OccResidue types D K env (r.mkRestore types D.uvars D.np ls as) occ)
    (hadd : env.addInductR D K (r.mkRestore types D.uvars D.np ls as) = some env') :
    VEnv.AddNested env D K (r.mkRestore types D.uvars D.np ls as)
      (fun j => (occ j).decl.np) env' :=
  VEnv.AddNestedB.toAddNested
    ⟨hwf, h.mkRestore_built_of_spine hcc hnd hK hspine hl ha hres, hadd⟩

end ElimNestedInductive.Result.RestoreData

#print axioms Lean4Lean.ElimNestedInductive.Result.RestoreData.mkRestore_built_of_spine
#print axioms Lean4Lean.ElimNestedInductive.Result.RestoreData.mkRestore_AddNested_of_spine

end Lean4Lean
