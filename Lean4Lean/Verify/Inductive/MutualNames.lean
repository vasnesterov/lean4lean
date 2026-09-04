import Lean4Lean.Verify.Inductive.NoNestedAll

/-!
# `addMutual`'s header loop, extracted — and what `MutualNamesGate` is actually missing

`Verify/Inductive/NoNestedAll.lean`:353 leaves the `mutualDefnDecl` branch of
`addDecl_noNestedEnv` resting on one residual `Prop`, `MutualNamesGate`, whose docstring says it is
*"**unproved, not false**: every conjunct is a postcondition of a check the loop actually performs
(`Lean4Lean/Environment.lean`:86-104)"*, and whose author recorded in
`docs/handoff-nonestedall.md` §4 that it was *"the one place I chose a gate over a proof for reasons
of time rather than of difficulty"*.

Both halves of that are right about `addMutual` and wrong about the gate.  The loop's postcondition
is proved here, unconditionally (§1-§2), and the branch it gates now stands with no gate at all
(§3).  But `MutualNamesGate` **verbatim** cannot be proved, for a reason that has nothing to do with
the loop: it asserts `env.find? v.name = none` while carrying no hypothesis on `env.constants`, and
the only check that can supply it — `checkName` — gives `env.contains v.name = false`.  Bridging
`contains` to `find?` needs `env.constants.WF`, because at `SMap` stage 2 the two go through
`PersistentHashMap.containsAux` and `findAux`, both `partial def` upstream and hence body-less
opaques.  §4 exhibits that residue as a hypothesis (`mutualNamesGate_of_contains`) and discharges it
from `WF` (`find?_none_of_contains_false`), so the gap is *located*, not asserted.  §6 lists every
limit; §5 fires the whole thing at a real two-member block and checks that each rejection the
postcondition rests on actually happens.

The exact `NoNestedAll.lean` edit this implies is written out in `docs/handoff-mutualnames.md` §3.
It is **not made here**: that file is not this stream's to edit.
-/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

/-! ## §1 The header loop, at the raw monadic value -/

theorem forIn_ok_fresh {P : DefinitionVal → Prop}
    {f : DefinitionVal → List Name → TypeChecker.M (ForInStep (List Name))}
    (H : ∀ v found ctx s r s', f v found ctx s = .ok (r, s') →
      found.contains v.name = false ∧ P v ∧ r = .yield (v.name :: found)) :
    ∀ {vs : List DefinitionVal} {found : List Name} {ctx : TypeChecker.Context}
      {s : TypeChecker.State} {r : List Name × TypeChecker.State},
      (ForIn.forIn vs found f) ctx s = .ok r →
        (∀ v ∈ vs, P v) ∧ (vs.map (·.name)).Nodup ∧ ∀ v ∈ vs, found.contains v.name = false
  | [], _, _, _, _, _ => ⟨nofun, by simp, nofun⟩
  | v :: vs, found, ctx, s, r, h => by
    rw [List.forIn_cons] at h
    obtain ⟨r₁, s₁, hb, h⟩ := M_bind_ok h
    obtain ⟨hfr, hP, rfl⟩ := H v found ctx s _ _ hb
    dsimp only at h
    obtain ⟨hPs, hnd, hmem⟩ := forIn_ok_fresh H h
    refine ⟨?_, ?_, ?_⟩
    · intro w hw
      rcases List.mem_cons.1 hw with rfl | hw
      · exact hP
      · exact hPs w hw
    · rw [List.map_cons, List.nodup_cons]
      refine ⟨fun hm => ?_, hnd⟩
      obtain ⟨w, hw, hwn⟩ := List.mem_map.1 hm
      have := hmem w hw
      rw [← hwn] at this
      simp at this
    · intro w hw
      rcases List.mem_cons.1 hw with rfl | hw
      · exact hfr
      · have := hmem w hw
        simp at this
        exact by simpa using this.2

/-! ## §2 The header loop's postcondition -/

theorem addMutual_header_post_gen {P : DefinitionVal → Prop} {env env' : Environment}
    {vs : List DefinitionVal} {fuel : FuelConfig}
    (hP : ∀ (v : DefinitionVal) (ctx : TypeChecker.Context) (s : TypeChecker.State)
      (r : Unit × TypeChecker.State),
      checkConstantVal env v.toConstantVal false ctx s = .ok r → P v)
    (h : addMutual env vs true fuel = .ok env') :
    (∀ v ∈ vs, P v) ∧ (vs.map (·.name)).Nodup := by
  obtain _ | ⟨v₀, rest⟩ := vs
  · unfold addMutual at h; exact absurd h nofun
  unfold addMutual at h
  simp only [if_true, bind, Except.bind, pure, Except.pure] at h
  split at h
  · exact absurd h nofun
  · split at h
    · exact absurd h nofun
    · rename_i hrun
      obtain ⟨s₀, hrun⟩ := M_run_ok hrun
      obtain ⟨_, s₁, hloop, _⟩ := M_bind_ok' hrun
      refine (fun key => ⟨key.1, key.2.1⟩)
        (forIn_ok_fresh (P := P) ?_ hloop)
      intro v found ctx s r s' hb
      split at hb
      · obtain ⟨_, _, ht, _⟩ := M_bind_ok' hb; exact absurd ht nofun
      · split at hb
        · obtain ⟨_, _, ht, _⟩ := M_bind_ok' hb; exact absurd ht nofun
        · split at hb
          · obtain ⟨_, _, ht, _⟩ := M_bind_ok' hb; exact absurd ht nofun
          · rename_i hfound
            obtain ⟨_, s₂, hcv, hp⟩ := M_bind_ok' hb
            refine ⟨by simpa using hfound, hP v ctx s _ hcv, ?_⟩
            cases hp; rfl

/-- The postcondition with `find? = none`, which needs `env.constants.WF`: see §4. -/
theorem addMutual_header_post {env env' : Environment} {vs : List DefinitionVal}
    {fuel : FuelConfig} (mapWF : env.constants.WF)
    (h : addMutual env vs true fuel = .ok env') :
    (∀ v ∈ vs, ¬ IsNestedName v.name ∧ env.find? v.name = none) ∧ (vs.map (·.name)).Nodup :=
  addMutual_header_post_gen
    (fun _ _ _ _ hcv => ⟨checkConstantVal_noNestedName hcv,
      checkConstantVal_find?_none mapWF hcv⟩) h

/-! ## §3 The `mutualDefnDecl` branch, with no gate -/

theorem addMutual_noNestedEnv' {env env' : Environment} {vs : List DefinitionVal}
    {fuel : FuelConfig} (hC : NoNestedEnv env)
    (h : addMutual env vs true fuel = .ok env') : NoNestedEnv env' := by
  obtain ⟨hv, hnd⟩ := addMutual_header_post hC.wf h
  unfold addMutual at h
  simp only [if_true, bind, Except.bind, pure, Except.pure] at h
  split at h
  · split at h
    · exact absurd h nofun
    · split at h
      · exact absurd h nofun
      · split at h
        · exact absurd h nofun
        · cases h
          exact NoNestedEnv.foldl_add hC (fun v hm => (hv v hm).1) (fun v hm => (hv v hm).2) hnd
  · exact absurd h nofun

/-! ## §4 What the gate as stated is missing, and where exactly -/

/-- **`MutualNamesGate` with the hypothesis its statement is missing.**  Everything else about it
is unchanged; this is the form that is a theorem, and the form the gate should have had.  See §6.1
for why the hypothesis cannot be dropped, and `docs/handoff-mutualnames.md` §3.2 for the two-line
`NoNestedAll.lean` edit that would make the existing gate suppliable. -/
def MutualNamesGateWF : Prop :=
  ∀ {env env' : Environment} {vs : List DefinitionVal} {fuel : FuelConfig},
    env.constants.WF → addMutual env vs true fuel = .ok env' →
      (∀ v ∈ vs, ¬ IsNestedName v.name ∧ env.find? v.name = none) ∧ (vs.map (·.name)).Nodup

/-- **The gate, discharged in the form that admits a proof.** -/
theorem mutualNamesGateWF : MutualNamesGateWF := fun mapWF h => addMutual_header_post mapWF h

/-- `checkName`'s success, with **no** hypothesis on the constant map: this is everything the check
itself buys, and it is `contains`, not `find?`. -/
theorem checkName_ok_contains {env : Environment} {n : Name} {ap : Bool} {u : Unit}
    (h : Environment.checkName env n ap = .ok u) : env.contains n = false := by
  cases hc : env.contains n
  · rfl
  · simp [Environment.checkName, hc, (· >>= ·), Except.bind] at h

theorem checkConstantVal_contains_false {env : Environment} {v : ConstantVal} {ap : Bool}
    {ctx : TypeChecker.Context} {s : TypeChecker.State} {r : Unit × TypeChecker.State}
    (h : checkConstantVal env v ap ctx s = .ok r) : env.contains v.name = false := by
  unfold checkConstantVal at h
  obtain ⟨u, hk, -⟩ := liftExcept_bind_ok h
  exact checkName_ok_contains hk

theorem contains_false_of_wf {env : Environment} (mapWF : env.constants.WF) (n : Name)
    (h : env.find? n = none) : env.contains n = false := by
  change env.constants.contains n = false
  rw [mapWF.find?_isSome, ← mapWF.find?'_eq_find?]
  rw [show env.constants.find?' n = env.find? n from rfl, h]
  rfl

theorem find?_none_of_contains_false {env : Environment} (mapWF : env.constants.WF) (n : Name)
    (h : env.contains n = false) : env.find? n = none := by
  change env.constants.contains n = false at h
  rw [mapWF.find?_isSome] at h
  rw [show env.find? n = env.constants.find?' n from rfl, mapWF.find?'_eq_find?]
  cases hf : env.constants.find? n <;> simp_all

/-- **The strongest `WF`-free postcondition.**  Both name facts, and `Nodup`, with no
hypothesis on the constant map at all — `contains` in place of `find?`. -/
theorem addMutual_header_post_contains {env env' : Environment} {vs : List DefinitionVal}
    {fuel : FuelConfig} (h : addMutual env vs true fuel = .ok env') :
    (∀ v ∈ vs, ¬ IsNestedName v.name ∧ env.contains v.name = false) ∧
      (vs.map (·.name)).Nodup :=
  addMutual_header_post_gen
    (fun _ _ _ _ hcv => ⟨checkConstantVal_noNestedName hcv,
      checkConstantVal_contains_false hcv⟩) h

/-- **`MutualNamesGate` verbatim is exactly one `SMap`-level fact away**, and that fact is not
about `addMutual` at all.  Everything the header loop can be asked for is in
`addMutual_header_post_contains`; the residue is `contains n = false → find? n = none` at an
arbitrary `Environment`, which at `SMap` stage 2 is a statement about `PersistentHashMap.containsAux`
and `findAux` — two `partial def`s upstream, hence body-less opaques.  With
`env.constants.WF` it is `find?_none_of_contains_false`; without it, it is neither provable
nor refutable. -/
theorem mutualNamesGate_of_contains
    (H : ∀ (e : Environment) (n : Name), e.contains n = false → e.find? n = none) :
    MutualNamesGate := fun h =>
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

"Instantiate, don't admire."  `addMutual_noNestedEnv'` and `addMutual_header_post` are
implications; if `addMutual` rejected every block, all of §2-§4 would be about nothing.  The gate
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
      addMutual_noNestedEnv''s hypothesis is unsatisfiable and §2-§4 are void"
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

1. **`MutualNamesGate` verbatim is *not* proved here, and cannot be.**  Its middle conjunct is
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
2. **What replaces it is strictly stronger for the consumer**: `addMutual_noNestedEnv'`, which
   takes the same `NoNestedEnv env` that `addMutual_noNestedEnv` already takes and needs no gate
   at all.  It cannot be obtained by *supplying* `addMutual_noNestedEnv`'s `G`, because
   `MutualNamesGate` quantifies over `env` universally while the proof needs `hC.wf`.
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
   in it.  §1 is that lemma redone at the raw monadic value.
5. **The `check := false` path is not covered and must not be**: §5's gate checks that with
   `check := false` the `_nested.g` block is *accepted*, so the postcondition is a property of the
   checked path only.
-/

#print axioms Lean4Lean.forIn_ok_fresh
#print axioms Lean4Lean.addMutual_header_post_gen
#print axioms Lean4Lean.addMutual_header_post
#print axioms Lean4Lean.addMutual_noNestedEnv'
#print axioms Lean4Lean.mutualNamesGateWF
#print axioms Lean4Lean.checkName_ok_contains
#print axioms Lean4Lean.checkConstantVal_contains_false
#print axioms Lean4Lean.contains_false_of_wf
#print axioms Lean4Lean.find?_none_of_contains_false
#print axioms Lean4Lean.addMutual_header_post_contains
#print axioms Lean4Lean.mutualNamesGate_of_contains
#print axioms Lean4Lean.mutualNamesGate_at_wf

end Lean4Lean
