import Lean4Lean.Verify.Inductive.NoNestedAll

/-!
# What `MutualNamesGate` was missing — the residue, located, after the gate was removed

`Verify/Inductive/NoNestedAll.lean` used to leave the `mutualDefnDecl` branch of
`addDecl_noNestedEnv` resting on a residual `Prop`, `MutualNamesGate`, whose docstring said it was
*"**unproved, not false**: every conjunct is a postcondition of a check the loop actually performs
(`Lean4Lean/Environment.lean`:86-104)"*, and whose author recorded in
`docs/handoff-nonestedall.md` §4 that it was *"the one place I chose a gate over a proof for reasons
of time rather than of difficulty"*.

Both halves of that were right about `addMutual` and wrong about the gate.  The loop's postcondition
is a theorem, and the branch it gated now stands with no gate at all — both in
`NoNestedAll.lean` §3.1, where this file's §1-§3 were transplanted on 2026-09-04
(`docs/handoff-migrate2.md`), because this file *imports* that one and so could not be cited from
the branch.  What could not be proved was `MutualNamesGate` **verbatim**, for a reason that has
nothing to do with the loop: it asserted `env.find? v.name = none` while carrying no hypothesis on
`env.constants`, and the only check that can supply it — `checkName` — gives
`env.contains v.name = false`.  Bridging `contains` to `find?` needs `env.constants.WF`, because at
`SMap` stage 2 the two go through `PersistentHashMap.containsAux` and `findAux`, both `partial def`
upstream and hence body-less opaques.

So the gate was not open, it was **defective as stated**, and it is gone.  What this file keeps is
the part that is about the *residue* rather than about the branch: §4 exhibits it as a hypothesis
(`mutualNamesGate_of_contains`) and discharges it from `WF` (`find?_none_of_contains_false`), so the
gap is *located*, not asserted.  §6 lists every limit; §5 fires the whole thing at a real two-member
block and checks that each rejection the postcondition rests on actually happens.
-/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

/-! ## §1-§3 Migrated to `Verify/Inductive/NoNestedAll.lean` §3.1 (2026-09-04)

The header loop (`forIn_ok_fresh`), its postcondition (`addMutual_header_post_gen`,
`addMutual_header_post`, `addMutual_header_post_contains`), the two `contains`/`find?` bridges
(`checkName_ok_contains`, `checkConstantVal_contains_false`, `contains_false_of_wf`,
`find?_none_of_contains_false`) and the gate-free branch itself all live in
`Verify/Inductive/NoNestedAll.lean` now — see `docs/handoff-migrate2.md`.  They had to move rather
than be cited, because **this file imports `NoNestedAll.lean`**, so the branch's own definition site
could not reach them; there is no import-direction fix.

`MutualNamesGate` is **gone**, and with it `MutualNamesGateWF`/`mutualNamesGateWF`, whose only
purpose was to be the shape the gate should have had.  `addMutual_noNestedEnv` in `NoNestedAll.lean`
is now unconditional and is exactly what `addMutual_noNestedEnv'` used to say here, so the primed
copy is gone too.

What remains here is what does **not** belong at the branch: §4, the located residue (kept because it
records *where* the old gate was wrong, not merely that it was); §5, the firing that makes every
implication above non-vacuous and checks that each rejection the postcondition rests on actually
happens; and §6, the limits. -/

/-! ## §4 What the gate as stated is missing, and where exactly -/

/-- **`MutualNamesGate` verbatim was exactly one `SMap`-level fact away**, and that fact is not
about `addMutual` at all.

The conclusion below is `MutualNamesGate` **delta-expanded**: the abbreviation is gone from
`NoNestedAll.lean`, so the same proposition is written out.  Nothing about the statement or the proof
term changed — only the name it used to hide behind.  Everything the header loop can be asked for is in
`addMutual_header_post_contains`; the residue is `contains n = false → find? n = none` at an
arbitrary `Environment`, which at `SMap` stage 2 is a statement about `PersistentHashMap.containsAux`
and `findAux` — two `partial def`s upstream, hence body-less opaques.  With
`env.constants.WF` it is `find?_none_of_contains_false`; without it, it is neither provable
nor refutable. -/
theorem mutualNamesGate_of_contains
    (H : ∀ (e : Environment) (n : Name), e.contains n = false → e.find? n = none) :
    ∀ {env env' : Environment} {vs : List DefinitionVal} {fuel : FuelConfig},
      addMutual env vs true fuel = .ok env' →
        (∀ v ∈ vs, ¬ IsNestedName v.name ∧ env.find? v.name = none) ∧
          (vs.map (·.name)).Nodup := fun h =>
  ⟨fun v hm => ⟨((addMutual_header_post_contains h).1 v hm).1,
      H _ _ ((addMutual_header_post_contains h).1 v hm).2⟩,
    (addMutual_header_post_contains h).2⟩

/-- And the converse direction, so the reduction is tight at every environment the kernel
actually builds: on `WF` maps the residue is discharged. -/
theorem mutualNamesGate_at_wf {env env' : Environment} {vs : List DefinitionVal}
    {fuel : FuelConfig} (mapWF : env.constants.WF)
    (h : addMutual env vs true fuel = .ok env') :
    (∀ v ∈ vs, ¬ IsNestedName v.name ∧ env.find? v.name = none) ∧ (vs.map (·.name)).Nodup :=
  ⟨fun v hm => ⟨((addMutual_header_post_contains h).1 v hm).1,
      find?_none_of_contains_false mapWF _ ((addMutual_header_post_contains h).1 v hm).2⟩,
    (addMutual_header_post_contains h).2⟩

/-! ## §5 The firings — the branch's hypotheses are satisfiable, and each check is load-bearing

"Instantiate, don't admire."  `addMutual_noNestedEnv` and `addMutual_header_post` (both in
`NoNestedAll.lean` §3.1) are implications; if `addMutual` rejected every block, they and §4 would be
about nothing.  The gate
below fails the build if that is ever true, and it also checks that each of the two rejections the
postcondition rests on really fires: the duplicate-name check (the `Nodup` conjunct) and
`checkNoNestedAuxName` (the `¬ IsNestedName` conjunct). -/

/-- A `partial` definition `n : Type := Prop`, which type-checks from the empty environment: no
inductive types, no universe parameters, no constants at all. -/
def mutWit (n : Name) : DefinitionVal :=
  { name := n, levelParams := [], type := .sort (.succ .zero), value := .sort .zero,
    hints := .opaque, safety := .partial }

#eval show Lean.CoreM Unit from do
  let kenv := Lean.Kernel.Environment.empty `main
  let ok := Lean4Lean.addDecl kenv (.mutualDefnDecl [mutWit `f, mutWit `g])
  let dup := Lean4Lean.addDecl kenv (.mutualDefnDecl [mutWit `f, mutWit `f])
  let nested := Lean4Lean.addDecl kenv (.mutualDefnDecl [mutWit `f, mutWit `_nested.g])
  let unchecked := Lean4Lean.addDecl kenv (.mutualDefnDecl [mutWit `f, mutWit `_nested.g]) false
  let safeTag := Lean4Lean.addDecl kenv (.mutualDefnDecl
    [{ mutWit `f with safety := .safe }, { mutWit `g with safety := .safe }])
  match ok with
  | .error _ =>
    throwError "MutualNames §5: Lean4Lean.addDecl REJECTS the two-member partial block \
      [f : Type := Prop, g : Type := Prop] from the empty environment -- \
      addMutual_noNestedEnv's hypothesis is unsatisfiable and §4 is void"
  | .ok env' =>
    let names := env'.constants.toList.map (·.1)
    unless names.contains `f && names.contains `g do
      throwError "MutualNames §5: the accepted block did not declare both f and g: {names}"
    unless names.all (fun n => !(`_nested).isPrefixOf n) do
      throwError "MutualNames §5: the accepted block left a _nested-prefixed constant \
        in the map: {names}"
  unless dup.toOption.isNone do
    throwError "MutualNames §5: Lean4Lean.addDecl ACCEPTS a mutual block with a DUPLICATE name \
      -- addMutual's `found.contains` check is gone, so the Nodup conjunct of \
      addMutual_header_post is false"
  unless nested.toOption.isNone do
    throwError "MutualNames §5: Lean4Lean.addDecl ACCEPTS a mutual member named _nested.g -- \
      checkNoNestedAuxName is gone from checkConstantVal, so the ¬IsNestedName conjunct is false"
  unless safeTag.toOption.isNone do
    throwError "MutualNames §5: Lean4Lean.addDecl ACCEPTS a `safe`-tagged mutual block -- \
      the safety gate at Environment.lean:82 is gone"
  unless unchecked.toOption.isSome do
    throwError "MutualNames §5: the _nested.g block is rejected even with check := false, so \
      the rejection is not attributable to the checks addMutual_header_post reads"
  Lean.logInfo m!"MutualNames §5: the two-member partial block is ACCEPTED and declares f and g \
    with no _nested name in the map; the duplicate-name block, the _nested.g block and the \
    safe-tagged block are all REJECTED, while with check := false the _nested.g block is ACCEPTED \
    (so the rejection is the checker's, not the fold's) ✓"

/-! ## §6 The limits of this result, each one measured

1. **`MutualNamesGate` verbatim was never proved, and cannot be — which is why it is gone rather
   than discharged.**  Its middle conjunct is
   `env.find? v.name = none` at an environment carrying no hypothesis.  The only check that can
   supply it is `checkName`, whose success gives `env.contains v.name = false`
   (`checkName_ok_contains`, which needs nothing).  Bridging the two is
   `Lean.SMap.WF.find?_isSome` and `.find?'_eq_find?` (`Lean4Lean/Std/SMap.lean`:90,84), **both of
   which require `env.constants.WF`**; at `SMap` stage 2 the bridge is a statement about
   `PersistentHashMap.containsAux` and `findAux`, `partial def`s upstream and therefore body-less
   opaques, so it is neither provable nor refutable.  `mutualNamesGate_of_contains` exhibits the
   residue, and `find?_none_of_contains_false` discharges it on `WF` maps.  This is a defect in the
   gate's *statement*, not in `addMutual`: every neighbour in `NoNestedAll.lean` carries `mapWF`
   (`checkConstantVal_find?_none`, `NoNestedMap.add`, `checkName.WF`), and the gate's only consumer
   has it (`NoNestedEnv.wf`).

   Note that "**unproved, not false**" — the gate's own docstring — is not the right verdict either.
   At a stage-2 environment whose `containsAux` answers `false` where `findAux` answers `some`, the
   gate is **false**; at one where they agree, it is true; and which of those obtains cannot be
   settled from the definitions, because both functions are body-less.  So the gate is *independent*,
   and its truth value is a question about two upstream `partial def`s rather than about the kernel.
   This paragraph is an argument from opacity, not a Lean theorem — Lean cannot state it — and it is
   flagged as such in `docs/handoff-mutualnames.md` §4.
2. **What replaced it is strictly stronger for the consumer**: `addMutual_noNestedEnv`
   (`NoNestedAll.lean` §3.1) takes the same `NoNestedEnv env` it always took and needs no gate at
   all.  It could *not* have been obtained by supplying the old gate as an argument, because
   `MutualNamesGate` quantified over `env` universally while the proof needs `hC.wf` — which is the
   precise sense in which the gate was the wrong statement rather than an unproved one.
3. **`forIn_ok_fresh` assumes the loop body always `yield`s.**  A `break` or `return` inside
   `addMutual`'s header loop would make the hypothesis `r = .yield (v.name :: found)` unprovable and
   the lemma inapplicable — it would not become *false*, it would stop matching.  `addMutual` has
   no `break`; the same restriction is stated for `M.WF.forIn`
   (`Verify/TypeChecker.lean`:112) and is a property of every loop in this kernel.
4. **Nothing here goes through `TypeChecker.M.WF`.**  `M.WF.forInFresh`
   (`Verify/TypeChecker.lean`:137) is the *same* loop rule and was already in the tree, but it is
   stated at a `VContext`, reachable only via `M.WF.run wf` with `wf : ves.WF env` — and
   `VEnvs.WF` is refuted by a single `.inductInfo` (`venvsWF_refuted_at_inductInfo`,
   `NoNestedAll.lean` §4).  So it would have been vacuous at every environment with an inductive
   in it.  `forIn_ok_fresh` is that lemma redone at the raw monadic value.
5. **The `check := false` path is not covered and must not be**: §5's gate checks that with
   `check := false` the `_nested.g` block is *accepted*, so the postcondition is a property of the
   checked path only.
-/

#print axioms Lean4Lean.forIn_ok_fresh
#print axioms Lean4Lean.addMutual_header_post_gen
#print axioms Lean4Lean.addMutual_header_post
#print axioms Lean4Lean.addMutual_noNestedEnv
#print axioms Lean4Lean.checkName_ok_contains
#print axioms Lean4Lean.checkConstantVal_contains_false
#print axioms Lean4Lean.contains_false_of_wf
#print axioms Lean4Lean.find?_none_of_contains_false
#print axioms Lean4Lean.addMutual_header_post_contains
#print axioms Lean4Lean.mutualNamesGate_of_contains
#print axioms Lean4Lean.mutualNamesGate_at_wf

end Lean4Lean
