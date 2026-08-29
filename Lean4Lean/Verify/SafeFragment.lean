import Lean4Lean.Verify.Environment.Extension
import Lean4Lean.Verify.TypeChecker

/-!
# The safe fragment: what the non-`.safe` path owes, and what `.safe` buys

`kernel_sound` (`Verify/Soundness.lean`) reads exactly one model out of the refinement layer:
`Bridge.foldAddDecl_tr` projects `ves.venv .safe` and `wf.tr` at `.safe`, and nothing else.
This file machine-checks two consequences of that, and records one obligation the current
proof of `addQuot.WF` hides behind a vacuity argument.

## 1. The non-`.safe` path carries no `.safe`-model obligation (§1 below)

`Lean4Lean.addMutual` rejects a `.safe` block outright (`Environment.lean:78-80`), so every
mutual block is `.partial` or `.unsafe`; `addDefinition`/`addAxiom` run the checker at
`.unsafe` exactly for `unsafe` declarations. In all of those cases the constants the step adds
are invisible at `.safe`, so the `.safe`-level step is `TrEnv'.ignore` -- **the model is
literally unchanged**.

`VEnvAt.ignore` and `VEnvAt.ignoreDefs` below state that with *no* hypothesis mentioning the
type checker: no `TrDefBlock`, no `TrConstVal`, no `VDefVal`, no `inferType`. Their premises
are name freshness, non-primitivity, nodup, and the safety tag -- all of which the executable
code checks and none of which is a soundness fact.

Combined with `Except.WF x Q = ∀ a, x = .ok a → Q a` (`Verify/TypeChecker/Basic.lean:7`) --
partial correctness, so *no* totality obligation exists anywhere in this development -- the
conclusion is sharper than "total but not sound": **on the non-`.safe` path the checker owes
the `.safe` model nothing at all.**

## 2. What `.safe` buys: `noUnsafe`, at a `VContext` (§2 below)

`VContext` (`Verify/TypeChecker/Basic.lean`) carries `safety : DefinitionSafety`
unconstrained, and `VContext.Ewf` is `c.trenv.wf : VEnv.WF c.venv`, which holds at every
level. `TrEnv'.wf_noUnsafe` needs `safety = .safe` as a literal. `VContext.EwfNoUnsafe` is the
one-line bridge: **a `VContext` at `.safe` does deliver the `noUnsafe` environment class**, so
an `Injectivity.lean` restated over that class would serve its `Verify/` consumers, provided
they are reached only at `.safe`.

## 3. The obligation this exposes: `quotInit` forces `Eq` to be *visible* (§3 below)

`TrEnv'` is indexed by `quotInit : Bool` and the only constructor that turns it from `false`
to `true` is `TrEnv'.quot`, whose first premise is `VEnv.QuotReady env`, i.e.
`env.constants ``Eq = some eqConst`. Hence `TrEnv safety env venv` with `env.quotInit = true`
forces `Eq` into `venv` and therefore forces `Eq` to be *visible at `safety`*
(`TrEnv.eq_visible_of_quotInit`); at `safety = .safe` that means `Eq` must be a **safe**
declaration.

`Lean4Lean.checkEqType` (`Quot.lean`) does not check that, and neither does the C++ kernel's
`check_eq_type` (`~/lean4/src/kernel/quot.cpp`): an `unsafe inductive Eq` of the right shape
passes both (`Eq` is not in `Environment.primitives`, so `checkName` admits it, and
`checkPrimitiveInductive` recognises only `Bool` and `Nat`, so `allowPrimitive` plays no part).
Worse than "the `.safe` model lacks it": `Theory/Inductive/Decl.lean`'s design note records
that `TrEnv'.induct` will be **gated to safe blocks** -- positivity is skipped when
`isUnsafe`, so `VIndField.WF.pos` has no witness and `TrEnv'.ignore` takes those declarations
instead. So an unsafe `Eq` will be in **no** model at **any** safety level, and
`∃ venv, TrEnv safety env venv` after the `.quotDecl` step is then false at every level -- not
merely unproved.

This does not bite today only because `addQuot.WF` discharges the non-initialized branch with
`checkEqType.WF`, whose conclusion is `False`, proved from `TrEnv'.no_inductInfo` at
`safety = .unsafe` -- a vacuity crutch that dies the moment `AddInduct` gains constructors
(and which `Verify/TypeChecker/Reduce.lean`'s `no_inductInfo_false_at_safe` already refutes at
`.safe`). `Theory/Inductive/Decl.lean` already predicts `checkEqType.WF`/`addQuot.WF` go
non-vacuous; what it does not record is that the honest replacement is **not provable from the
checker as written**. The fix is a checker change -- `checkEqType` must reject an `Eq` whose
`ConstantInfo` is not `.safe` -- and it is a divergence from the C++ kernel, so it belongs in
`divergences.md`. Recorded live here so it cannot rot.

## 4. Where the injectivity obligation actually enters `Verify/` -- a cone measurement

Recorded here because it names the same three sites §2 is about. Machine-checked over the
import closure of `Verify/TypeChecker.lean` + `Verify/Typing/Lemmas.lean` (transitive
`getUsedConstantsAsSet` fixpoint, internal names included; theorem values read by an explicit
match, since `ConstantInfo.value?` returns `none` for `.thmInfo` on this toolchain -- a scan
trap worth recording, it silently reports a cone of size 0).

* `IsDefEqU.sort_inv` has **129** transitive users in that closure and exactly **one** direct
  consumer, `IsDefEq.uniq`.
* `IsDefEq.uniq` has exactly **four** direct consumers: `IsDefEq.trans_l`, `IsDefEq.trans_r`,
  `isDefEq_iff`, `IsDefEq.uniqU`.
* `IsDefEq.uniqU` has exactly **four** direct consumers:
  `TypeChecker.Inner.inferApp.loop.WF`, `TypeChecker.Inner.inferType.WF_uniq`,
  `TrExpr.beta`, and `IsDefEq.weakN_iff'`.

The first three are **the same three sites** that take their environment from `VContext.Ewf`
(`handoff-stratified.md` §14.5) and the same three that consume `IsDefEqU.forallE_inv`
(`docs/backward-analysis.md` §3). Counterfactual cone scans, cutting each family in turn:

| edges cut | users of `sort_inv` remaining |
|---|---|
| none | 129 |
| `IsDefEqU.trans`, `IsDefEqU.defeqDF` (what enlargement (E) genuinely makes into rules) | **122** |
| + `IsDefEqU.of_l/of_r` | 83 |
| + `HasType.defeqU_l/_r`, `IsType.defeqU_l` | 83 |
| + `IsDefEq.trans_l/trans_r/transU_l/transU_r` | 67 |
| + `isDefEq_iff` | **66** |
| + `IsDefEq.uniq` | 0 |

So `docs/backward-analysis.md` §5's "with (E), `sort_inv` ... leave[s] `kernel_sound`'s cone
entirely: 174 declarations' worth of dependence becomes four constructors" is **too strong**.
(E) enlarges `IsDefEqU` and the *conversion* rule; that makes `IsDefEqU.trans` and
`IsDefEqU.defeqDF` free, and 122 of 129 users survive. `IsDefEqU.of_l/of_r` and
`HasType.defeqU_*` are *not* free under (E): their base case needs `IsDefEqU' Γ A B` from
`Γ ⊢ e : A` and `Γ ⊢ e : B`, which is unique typing. Granting all twelve leaves **66** users,
all through `IsDefEq.uniqU` -- two types of one term are convertible -- which is a statement
about *typing*, not about conversion, and which no enlargement of the definitional-equality
judgment can turn into a rule. To reach zero one must make the four-place judgment *derived*
(`IsDefEq Γ e₁ e₂ A := IsDefEqU' Γ e₁ e₂ ∧ Γ ⊢ e₁ : A ∧ Γ ⊢ e₂ : A`), i.e. adopt the
reference's three-place judgment wholesale, which invalidates every induction on `IsDefEq` in
the tree (155 `induction`/`cases` sites).

**The lead this leaves, and it is on this stream's side.** Gateway A is not 129 declarations;
it is three proof sites, and each uses `uniqU` in one shape: reconciling a type the proof
*constructed* with a type it was *given* for the same term. `inferApp.loop.WF` gets `fty''`
from its `AppStack` and `fty'` from its own hypothesis `hety`; `inferType.WF_uniq` gets one
from `inferType.WF` and one from `hty`; `TrExpr.beta` gets one from `hf` and one from
`hA.lam hb`. If the two can be made *the same type by construction* -- threading one type
through the invariant instead of reconciling two -- `uniqU` is not needed at those sites, and
with (E) on top of that `sort_inv` leaves the cone for real. Not attempted here; not priced.
-/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

open private Lean.Kernel.Environment.add from Lean.Environment

/-! ## 1. A step invisible at `safety` costs the model nothing -/

/-- Adding one constant that is invisible at `safety` leaves the model **unchanged**.

No premise mentions the type checker: this is the whole `.safe`-level obligation of an
`unsafe` axiom or an `unsafe` definition. -/
theorem VEnvAt.ignore {env : Environment} {venv : VEnv} {ci : ConstantInfo}
    (H : VEnvAt env safety venv)
    (hfresh : env.find? ci.name = none)
    (hvis : ¬ safety ≤ ci.safety)
    (hnp : Environment.primitives.contains ci.name = false) :
    VEnvAt (env.add ci) safety venv where
  tr := TrEnv'.ignore (by rw [← H.tr.map_wf.find?'_eq_find?]; exact hfresh) hvis H.tr
  hasPrimitives := H.hasPrimitives
  safePrimitives h hp := H.safePrimitives_add ci hfresh (by simp [hnp]) h hp

/-- `VEnvs.WF.safePrimitives_addDefs` at a single safety level. -/
theorem VEnvAt.safePrimitives_addDefs {env : Environment} {venv : VEnv}
    (wf : VEnvAt env safety venv) {vs : List DefinitionVal}
    (hfresh : ∀ v ∈ vs, env.find? v.name = none)
    (hnd : (vs.map (·.name)).Nodup)
    (hnonprim : ∀ v ∈ vs, Environment.primitives.contains v.name = false)
    (hfind : (vs.foldl (fun e v => e.add (.defnInfo v)) env).find? n = some ci)
    (hp : Environment.primitives.contains n) : ci.safety = .safe ∧ ci.levelParams = [] := by
  have mapWF := wf.tr.map_wf
  have hfr : ∀ d ∈ vs, env.constants.find? d.name = none := fun d hd => by
    rw [← mapWF.find?'_eq_find?]; exact hfresh d hd
  rw [Kernel.Environment.find?, Environment.constants_addDefs,
    (insertDefs_wf mapWF hfr hnd).find?'_eq_find?] at hfind
  rcases insertDefs_find? mapWF hfr hnd hfind with h | ⟨d, hd, rfl, rfl⟩
  · exact wf.safePrimitives (by rwa [Kernel.Environment.find?, mapWF.find?'_eq_find?]) hp
  · exact absurd hp (by simp [hnonprim d hd])

/-- **Step 1, machine-checked.** A whole mutual block that is invisible at `safety` leaves the
model **unchanged**, and the statement mentions nothing the type checker produces.

`addMutual`'s return value is `vs.foldl (fun e v => e.add (.defnInfo v)) env` -- note it folds
over the *original* `env`, so the block's temporary safe-tagged axioms are gone. Compare
`addMutualBlock.WF`, which needs `TrDefBlock`, `hwfc`, `hci` and `hbase`: every one of those
serves the `sf ≤ bs` branch, i.e. the `.partial`/`.unsafe` models, which
`Bridge.foldAddDecl_tr` discards. -/
theorem VEnvAt.ignoreDefs {env : Environment} {venv : VEnv} {vs : List DefinitionVal}
    (H : VEnvAt env safety venv)
    (hvis : ∀ v ∈ vs, ¬ safety ≤ (ConstantInfo.defnInfo v).safety)
    (hfresh : ∀ v ∈ vs, env.find? v.name = none)
    (hnd : (vs.map (·.name)).Nodup)
    (hnp : ∀ v ∈ vs, Environment.primitives.contains v.name = false) :
    VEnvAt (vs.foldl (fun e v => e.add (.defnInfo v)) env) safety venv where
  tr := by
    show TrEnv' safety _ _ _
    rw [Environment.constants_addDefs, Environment.quotInit_addDefs]
    exact TrEnv'.ignoreDefs hvis
      (fun v hv => by rw [← H.tr.map_wf.find?'_eq_find?]; exact hfresh v hv) hnd H.tr
  hasPrimitives := H.hasPrimitives
  safePrimitives h hp := H.safePrimitives_addDefs hfresh hnd hnp h hp

/-- The `.safe` specialisation, with the safety premise in the form `addMutual` actually
establishes: it throws unless `v₀.safety ≠ .safe`, and checks every member carries `v₀`'s tag.

**The `.safe` model of the environment after a `partial`/`unsafe` mutual block is the `.safe`
model of the environment before it.** -/
theorem VEnvAt.safe_mutual {env : Environment} {venv : VEnv} {vs : List DefinitionVal}
    (H : VEnvAt env .safe venv)
    (hns : ∀ v ∈ vs, v.safety ≠ .safe)
    (hfresh : ∀ v ∈ vs, env.find? v.name = none)
    (hnd : (vs.map (·.name)).Nodup)
    (hnp : ∀ v ∈ vs, Environment.primitives.contains v.name = false) :
    VEnvAt (vs.foldl (fun e v => e.add (.defnInfo v)) env) .safe venv :=
  H.ignoreDefs (fun v hv h => by
    rw [ConstantInfo.defnInfo_safety] at h
    exact hns v hv (DefinitionSafety.le_antisymm DefinitionSafety.le_safe h)) hfresh hnd hnp

/-! ## 2. What a `.safe` `VContext` buys -/

namespace TypeChecker

/-- **The `noUnsafe` environment class, delivered at a `VContext`.**

`VContext.Ewf` gives only `VEnv.WF c.venv`, which holds at every safety level and admits the
`.unsafeDef` cycle. At `c.safety = .safe` the stronger class is immediate. This is the
statement an `Injectivity.lean` restated over `noUnsafe` would need at its three `Verify/`
consumers (`inferApp.loop.WF`, `inferType.WF_uniq`, `TrExpr.beta`).

Note what it does *not* say: nothing here makes those consumers reachable only at `.safe`.
That is the restructuring, and §1 is its evidence. -/
theorem VContext.EwfNoUnsafe (c : VContext) (h : c.safety = .safe) :
    ∃ ds, VEnv.WF' ds c.venv ∧ ∀ d ∈ ds, VDecl.noUnsafe d :=
  TrEnv.wf_noUnsafe (h ▸ c.trenv)

end TypeChecker

/-- **The `.safe` model is the *smallest* of the three.**

This is `VEnvs.WF.mono` read at `safety' := .safe`, and it refutes the second of the two
restructurings named in `handoff-stratified.md` §14.6 -- "route the injectivity obligation
through the `.safe` member of `VEnvs`". A `VContext` built at `.partial` has
`c.venv = ves.venv .partial`, which *contains* `ves.venv .safe`; and `noUnsafe` is a property
of the `VDecl` list that builds an environment, not a property closed under `≤`. So there is
no transport in the direction that shape needs.

The first shape ("`VContext` gains a `noUnsafe` field forcing `c.safety = .safe`") is not
buildable as stated either, for a reason recorded in `VEnvAt`'s own docstring: a mutual
block's bodies are checked in an environment whose members are present as `safe`-tagged
axioms typed only at `.partial`, which has no `.safe` model at all, so `VContext.mk1` at
`.safe` cannot be constructed there. The move that does work is to delete the non-`.safe`
components of `VEnvs.WF` -- which §1 shows costs the `.safe` model nothing -- and only then
constrain `VContext`. -/
theorem VEnvs.WF.safe_le {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (safety : DefinitionSafety) : ves.venv .safe ≤ ves.venv safety :=
  wf.mono DefinitionSafety.le_safe

/-! ## 3. `quotInit` forces `Eq` into the model, at every safety level -/

/-- `AddQuot` only extends the model, so `QuotReady` survives it. -/
theorem VEnv.QuotReady.mono {env env' : VEnv} (h : env.QuotReady) (le : env ≤ env') :
    env'.QuotReady := le.constants h

/-- `AddInduct` only ever *extends* the model -- but it has no constructors today, so this is
the one place in this file that leans on that emptiness.  **When `AddInduct` gains
constructors this must be reproved**, and it will be true, because every inductive step adds
constants and rules and removes none. -/
theorem AddInduct.le {C C' : ConstMap} {env env' : VEnv} {decl : VInductDecl'}
    (H : AddInduct C env decl C' env') : env ≤ env' := nomatch H

/-- **The `quot` step is the only way to `quotInit = true`, and it demands `Eq` in the model.**

Every other `TrEnv'` constructor either preserves `quotInit` while extending the model, or
(`empty`) produces `false`. -/
theorem TrEnv'.quotReady_of_quotInit {C : ConstMap} {venv : VEnv} :
    TrEnv' safety C true venv → venv.QuotReady := by
  generalize hQ : true = Q
  intro H
  induction H with
  | empty => exact absurd hQ (by simp)
  | ignore _ _ _ ih => exact ih hQ
  | «axiom» _ _ _ hadd _ ih => exact (ih hQ).mono (VEnv.addConst_le hadd)
  | defn _ _ _ hadd _ ih =>
    exact ((ih hQ).mono (VEnv.addConst_le hadd)).mono VEnv.addDefEq_le
  | unsafeDef _ _ _ _ _ hadd _ _ ih =>
    exact ((ih hQ).mono (VEnv.addConsts_le hadd)).mono VEnv.addDefEqs_le
  | thm _ _ _ _ hadd _ ih => exact (ih hQ).mono (VEnv.addConst_le hadd)
  | «opaque» _ _ _ hadd _ ih => exact (ih hQ).mono (VEnv.addConst_le hadd)
  | quot hq hadd _ _ => exact hq.mono hadd.le
  | induct _ hadd _ ih => exact (ih hQ).mono hadd.le

/-- **The obligation `checkEqType.WF`'s vacuity argument hides.**

If the kernel environment has run quotient initialization, then `Eq` is present in the model
at *every* safety level, hence -- by `TrEnv.find?_iff` -- `Eq`'s `ConstantInfo` is visible at
that safety. At `safety = .safe` this says `Eq` must be tagged `.safe`.

`checkEqType` does not check it; nor does the C++ kernel's `check_eq_type`. So the `.safe`
component of `addDecl.WF` at a `.quotDecl` step, after an `unsafe inductive Eq`, is not merely
unproved: it is **false**. It is masked today only because `AddInduct` has no constructors,
which makes `TrEnv'.no_inductInfo` (at `.unsafe`) prove `False` from the presence of any
`.inductInfo` at all. -/
theorem TrEnv.eq_visible_of_quotInit {env : Environment} {venv : VEnv}
    (H : TrEnv safety env venv) (hq : env.quotInit = true)
    (hfind : env.find? ``Eq = some ci) : safety ≤ ci.safety := by
  have H' : TrEnv' safety env.constants true venv :=
    hq ▸ (H : TrEnv' safety env.constants env.quotInit venv)
  have hready : venv.QuotReady := TrEnv'.quotReady_of_quotInit H'
  obtain ⟨ci', hci', hs⟩ := H.find?_iff.2 ⟨_, hready⟩
  cases hfind.symm.trans hci'
  exact hs

/-- At `.safe`, spelled out: quotient initialization forces `Eq` to be a safe declaration. -/
theorem TrEnv.eq_safe_of_quotInit {env : Environment} {venv : VEnv}
    (H : TrEnv .safe env venv) (hq : env.quotInit = true)
    (hfind : env.find? ``Eq = some ci) : ci.safety = .safe :=
  DefinitionSafety.le_antisymm DefinitionSafety.le_safe (H.eq_visible_of_quotInit hq hfind)

end Lean4Lean
