import Lean4Lean.Verify.SoundnessAssembly

/-!
# What does `kernel_sound` actually depend on?

The sorry census (`scripts/sorry-census.lean`) counts every hole in the census import cone.
That is the right global number, but it does not say which holes are on the **critical path to
the main theorem** — and it turns out not all of them are.

This script walks the forward cone (same `deps` walker as `scripts/hole-cone.lean`:
`allowOpaque := true`, type *and* value) of `Bridge.kernel_sound_of`, which is `kernel_sound`
modulo its two named hypotheses, and of the four intermediate lemmas it is built from.

    ~/.elan/bin/lake env lean scripts/kernel-sound-path.lean

Reading as of 2026-08-31 (census TOTAL 14):

* `kernel_sound_of` reaches **9** holes.
* **All 9** enter through `addDeclWF`, i.e. through the checker-refinement layer.
  `hasType_falseProp` — the `False`-witness transport — has a cone of 7244 and **0** holes.
* The 5 census holes it does *not* reach are `kernel_sound` and `kernel_complete` themselves,
  `leanTT_equiconsistent_zfc_omega_inaccessibles`, `VIndRecArg.exists_indep` (0 users), and
  ~~`NormalEq.descend` (47 users).~~  **STALE, CORRECTED 2026-09-02 — and this docstring is the
  one everyone reads while reproducing the cone, so the error propagated further than most.**
  `NormalEq.descend` has **200** transitive users and is **ON** `Bridge.kernel_sound_of`'s cone,
  entering through Church-Rosser / constant-application injectivity; the cone's hole set is
  **nine** and contains it.  So the list below is **four** off-cone holes of **13**, not five of
  14.  `docs/critical-path.md` corrected its copy of this line on 2026-09-01 and this twin was
  missed for a day (`docs/audit-doc-claims.md`).

Two of those five need care rather than celebration:

* `leanTT_equiconsistent_zfc_omega_inaccessibles` is off the *cone* only because
  `kernel_sound_of` takes the upper bound as a **hypothesis** instead of applying the theorem.
  It is squarely on the path; the cone cannot see hypotheses.
* `NormalEq.descend` is off-cone because the results it supplies (`ParRed.weakN_inv` and the
  rest of confluence) are needed to *prove* `IsDefEqU.weakN_iff`, which is currently itself a
  hole — and a hole's cone contains nothing.  So `descend` is off-cone precisely because its
  consumer has not been proved yet, not because the confluence work is idle.  It re-enters the
  cone the moment `weakN_iff` stops being a `sorry`.

`VIndRecArg.exists_indep` and `kernel_complete` are genuinely not blocking (`kernel_complete`
says so in its own doc comment).
-/
open Lean
def deps (ci : ConstantInfo) : NameSet :=
  let s := ci.type.getUsedConstantsAsSet
  match ci.value? (allowOpaque := true) with
  | some v => s.union v.getUsedConstantsAsSet
  | none => s
partial def go (env : Environment) : List Name → NameSet → NameSet
  | [], seen => seen
  | n :: rest, seen =>
    if seen.contains n then go env rest seen else
    let seen := seen.insert n
    match env.find? n with
    | some ci => go env ((deps ci).toList ++ rest) seen
    | none => go env rest seen
def main : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{module := `Lean4Lean.Verify.SoundnessAssembly}] {}
  for s in [``Lean4Lean.Bridge.kernel_sound_of, ``Lean4Lean.Bridge.not_leanTTConsistent_of_kernel_proves_false,
            ``Lean4Lean.Bridge.foldAddDecl_tr, ``Lean4Lean.Bridge.addDeclWF, ``Lean4Lean.Bridge.hasType_falseProp] do
    let c := go env [s] {}
    let holes := c.toList.filter fun n =>
      match env.find? n with
      | some ci => (deps ci).contains ``sorryAx
      | none => false
    IO.println s!"{s}: cone {c.size}, holes ({holes.length}) {holes}"
#eval! main
