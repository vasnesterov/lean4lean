import Lean4Lean.Verify.Inductive.NestedRestoreWit
import Lean4Lean.Theory.Inductive.NestedFresh

/-!
# The general bridge, with `BuiltFresh` reduced to the spine

`ElimNestedInductive.Result.RestoreData.mkRestore_built` (`Verify/Inductive/NestedRestoreWit.lean`
§6) takes `VInductDecl'.BuiltFresh` as a hypothesis, with the note that ruling 116d's cost sits
there and that **nothing in `RestoreData` or `OccData` mentions it**, "since both bundles are
about the checker's `Lean.Name`s".

Half of that is now out of date.  `Theory/Inductive/NestedBuild.lean` §F3 derives `BuiltFresh`'s
`fields_noK` clause from

* `env.ConstsClosedC` — an environment invariant, in the weakest strength that is used (the
  *constants* half only): free from `VEnv.Ordered.constsClosed`, and also from
  `VInductDecl'.constsClosedC_addInduct'_of_B` with **no** `WF` proof at all
  (`Theory/Inductive/NestedBuild.lean` §F2);
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
theorem mkRestore_built_of_spine (hcc : env.ConstsClosedC) (hnd : D.blockNames.Nodup)
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
theorem mkRestore_AddNested_of_spine {env' : VEnv} (hwf : D.WF env) (hcc : env.ConstsClosedC)
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

/-! ## The bridge, consumed

`mkRestore_built_of_spine` had **zero consumers** (handoff §58.7).  It has one now, at the same
witness `nfnAux_built'` (`Verify/Inductive/NestedRestoreWit.lean` §7) uses the unreduced
`mkRestore_built` at: same conclusion, same `Result`, same restoration, with `BuiltFresh` replaced
by the four reduced facts.  What the two proofs let us compare is exactly what ruling 116d costs:

| `mkRestore_built` (old) | `mkRestore_built_of_spine` (here) |
| --- | --- |
| `nfnAux_builtFresh h` — `fields_noK` over `PFn`'s constructors and fields | `env₂.ConstsClosedC`, from `pfnDecl` alone (`pfnEnv_constsClosedC`) |
| | `nfnK_not_contains h` — the step's own freshness |
| | `nfnAs`-cleanliness: **one `decide` over `RestoreData`'s own parameter** |

The third row is the residual, and `nfnAs` is a `Nat → List VExpr` the *checker's* data determines
(`nfnResult`'s `aux2nested` entry), not a fact about `PFn`.  That is the whole of what §58.3
claimed and could not exhibit. -/

namespace NestedWit
open InductiveDeclExamples ElimNestedInductive

section
variable {env₂ : VEnv} (h : VEnv.empty.addInduct' pfnDecl = some env₂)

/-- **The spine obligation, discharged at the concrete `Result`.**  `nfnAs` is
`fun j => if j = 1 then [.const ``NFn []] else []`, so the whole of ruling 116d's residual at this
witness is: `NFn` is not a companion name. -/
theorem nfnAs_noK : ∀ (j : Nat) (T : VIndType), nfnAux.types[j]? = some T → T.name ∈ nfnK →
    ∀ a ∈ nfnAs j, VExpr.NoConsts nfnK a := by
  rintro (_ | _ | j) T hT hK
  · cases hT; exact absurd hK (by decide)
  · decide
  · simp [nfnAux] at hT

include h in
/-- **`Built` through the reduced bridge.**  Identical statement to `nfnAux_built'`; the
`BuiltFresh` hypothesis is gone, and what replaces it is `nfnAs_noK`. -/
theorem nfnAux_built'_of_spine : nfnAux.Built nfnRestore' nfnK env₂ (fun _ => pfnOcc) :=
  nfnResult_restoreData.mkRestore_built_of_spine (ls := nfnLs) (occ := fun _ => pfnOcc)
    (pfnEnv_constsClosedC h) (by decide) (nfnK_not_contains h) nfnAs_noK
    (fun _ _ _ _ => rfl)
    (by rintro (_ | _ | j) T hT hK
        · cases hT; exact absurd hK (by decide)
        · rfl
        · simp [nfnAux] at hT)
    (nfnResult_occResidue h)

end
end NestedWit

#print axioms Lean4Lean.NestedWit.nfnAs_noK
#print axioms Lean4Lean.NestedWit.nfnAux_built'_of_spine

/-! ## The spine obligation over `ElimNestedInductive.run`: **refuted at that scope**

Handoff §58.6 filed this as the one thing "read off, not verified":

> that `ElimNestedInductive.run` never puts an auxiliary name into a *spine* — I read
> `replaceIfNested`/`run` and the argument is that `args` always comes from a term that predates
> the replacement pass, so the spine premise should be *true* of what the checker builds.

It is **false as stated**, and the machine says so below.  `run` is called by
`Lean4Lean.Environment.addInductive` *after* a gate, and the gate is load-bearing: pass `run` an
input the gate would have rejected and it records a spine mentioning the auxiliary name the same
call invents.

Concretely, `inductive T : Type | mk : List (_nested.List_1 T) → T` fed straight to `run` yields

```
aux2nested = [(`_nested.List_1, List (_nested.List_1 T))]
```

— the key and a constant inside the stored spine are the *same name*, so
`∀ a ∈ as j, VExpr.NoConsts K a` fails at `K = [_nested.List_1]`.  Nothing about the replacement
pass is violated: `_nested.List_1` here came from the **input**, not from a replacement, and
`mkUniqueName` then generated it because `nextIdx` starts at `1` and the environment does not
contain it (`env.contains _nested.List_1 = false`, measured).

So the correct statement of the obligation has **two** premises, not one:

1. *pass ordering* — `replaceNoCacheT` is top-down and does not revisit a replaced node, and
   `newTypes[i]`'s stored constructor types are built before index `i` is processed; this is what
   §58.6 named, and it rules out aux names that replacement introduces; and
2. *the gate* — `checkNoNestedAux` (`Lean4Lean/Inductive/Add.lean`), which rejects any input member
   or constructor type mentioning a `_nested`-prefixed constant; this is what rules out aux names
   the **input** supplies, and §58.6 did not name it.

Premise 2 is not a fact about `run`; it is a fact about its caller.  That is why the obligation
belongs on `Result` (as `spineNoAuxB` below, a `Bool` in `OccData`'s style) with a separate
`addInductive`-level theorem, rather than being provable from `run` alone.

**Still open, and this is the next round's work**: the `Bool` below is about `Lean.Expr`s in
`aux2nested`; `mkRestore_built_of_spine`'s `hspine` is about `VExpr`s in `as`.  Bridging them needs
the translation link (`TrExprS` preserves constant occurrences) plus `RestoreData`-level agreement
between `aux2nested`'s stored args and `as j` — neither of which `RestoreData` or `OccData` carries
today.  `nfnAs_noK` above discharges `hspine` at the concrete witness *without* that bridge, by
`decide` on the `VExpr` side. -/

namespace ElimNestedInductive.Result

/-- **The spine obligation, as a decidable fact about the checker's own data.**  For every
`aux2nested` entry, no argument of the stored `J Ds` mentions a name in `K`.  A `Bool`, in the
style of `OccData`'s six clauses: no `VEnv`, no `TrExprS`, no typing judgement. -/
def spineNoAuxB (r : Result) (K : List Lean.Name) : Bool :=
  r.aux2nested.all fun p => p.2.getAppArgs.all fun a =>
    !Lean4Lean.anySubterm (fun
      | .const c _ => K.contains c
      | .proj s _ _ => K.contains s
      | _ => false) a

/-- `spineNoAuxB` as a `Prop`, for use as a hypothesis. -/
def SpineNoAux (r : Result) (K : List Lean.Name) : Prop := r.spineNoAuxB K = true

instance (r : Result) (K : List Lean.Name) : Decidable (r.SpineNoAux K) :=
  inferInstanceAs (Decidable (_ = true))

end ElimNestedInductive.Result

namespace NestedWit

/-- `inductive T : Type | mk : List (_nested.List_1 T) → T`, the input the gate rejects. -/
def spineBadTypes : List Lean.InductiveType :=
  let T : Lean.Expr := .const `T []
  let inner : Lean.Expr := .app (.const `_nested.List_1 [.zero]) T
  let ctorTy : Lean.Expr := .forallE `x (.app (.const ``List [.zero]) inner) T .default
  [{ name := `T, type := .sort (.succ .zero),
     ctors := [{ name := `T.mk, type := ctorTy }] }]

/-! **Self-checking refutation.**  Three assertions, all of which must hold for the account above
to be the right one:

1. `run` accepts `spineBadTypes` and its `aux2nested` **violates** `spineNoAuxB` at
   `K = [_nested.List_1]` — the read-off claim of §58.6 is false at the scope it was stated;
2. `checkNoNestedAux` **rejects** the constructor type — so the obligation is true *relative to the
   gate*, which is premise 2 above;
3. `Environment.addInductive` rejects it with the reserved-prefix error — so the guard is the real
   function's, not a modelled one.  (That third assertion is what `NestedOccData.lean` §10.1's own
   note says a regression test of this kind must include; without it the `#eval` would pass with
   the gate removed.)

This `#eval` fails the build if any of the three stops holding. -/
#eval show Lean.CoreM Unit from do
  let kenv := (← Lean.getEnv).toKernelEnv
  if kenv.contains `_nested.List_1 then
    throwError "witness void: the environment already declares `_nested.List_1`"
  let .ok r := (ElimNestedInductive.run 1000 0 spineBadTypes kenv).run'
      { lvls := [], newTypes := spineBadTypes.toArray }
    | throwError "witness void: `run` rejected the block, so it records no spine"
  unless r.aux2nested.map (·.1) = [`_nested.List_1] do
    throwError "witness void: aux2nested keys = {r.aux2nested.map (·.1)}"
  if r.spineNoAuxB [`_nested.List_1] then
    throwError "the spine obligation HOLDS of `run` here -- \
      §58.6's read-off claim would be true at its stated scope"
  for it in spineBadTypes do
    for c in it.ctors do
      if (Lean4Lean.checkNoNestedAux c.name c.type).toOption.isSome then
        throwError "the gate ACCEPTS the refuting input -- the obligation is false outright"
  if (Lean4Lean.Environment.addInductive kenv [] 0 spineBadTypes false false).toOption.isSome then
    throwError "`Environment.addInductive` ACCEPTS the refuting input"
  IO.println "witness: `run` records spine `_nested.List_1 T` under key `_nested.List_1`, \
    refuting the spine obligation at `run`'s scope; `checkNoNestedAux` and \
    `Environment.addInductive` both reject the input, so the obligation holds only relative to \
    the gate ✓"

end NestedWit

end Lean4Lean
