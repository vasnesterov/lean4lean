import Lean4Lean.Verify.Inductive.RestoreFaithful

/-!
# `VEnv.NoNestedN` on every `addDecl` branch — the induction, run

`Verify/Inductive/RestoreFaithful.lean` §5 records that `VEnv.NoNestedN` ("no declared name
carries the reserved `_nested` prefix", `Verify/Inductive/ProjNoNested.lean`:379) is an
*invariant* — refuted by one hostile `addConst` (`NestedWit.noNestedN_not_preserved`) — that must
therefore be *carried*; that PR #46 (`7e39484`) made its missing hypothesis suppliable on every
branch by putting `checkNoNestedAuxName` beside `checkName` in `checkConstantVal`; and that
**nobody had run the induction**, so every §3 discharge resting on §2 was conditional in fact.

This file runs it, in two halves that meet at one definition:

* §1 `NoNestedMap` — the *kernel-level* condition: no entry of the constant map is prefixed.
* §2 the abstract side: `TrEnv' safety C Q venv → NoNestedMap C → venv.NoNestedN`, i.e. the
  invariant on the abstract environment follows from the invariant on the kernel-level map, for
  **every** `TrEnv'` constructor.  Plus the per-constructor step ledger, so that the answer to
  "which case resists" is a list of theorems and not prose.
* §3 the implementation side: `NoNestedMap` is *established* — held by the empty environment and
  preserved by `Lean4Lean.addDecl`, branch by branch.
* §4 the limits, each one measured or proved, and the two that are open.
* §5 the firings, closed and computed.
-/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

open private Lean.Kernel.Environment.add markQuotInit from Lean.Environment

/-! ## §1 The kernel-level condition -/

/-- **No entry of the kernel-level constant map carries the reserved prefix.**

This is the `ConstMap` counterpart of `VEnv.NoNestedN`, and it is the thing an implementation
check can actually establish: `checkNoNestedAuxName` tests a `Name`, and the names in the map are
exactly the names that were tested. -/
def NoNestedMap (C : ConstMap) : Prop := ∀ n ci, C.find? n = some ci → ¬ IsNestedName n

theorem NoNestedMap.of_find?_none {C : ConstMap} (h : ∀ n, C.find? n = none) : NoNestedMap C :=
  fun n _ hf => absurd (h n ▸ hf) nofun

/-! ## §2 The abstract side: the `TrEnv'` induction -/

namespace VEnv

/-- **The step, at `Aligned`.**  `Aligned.find?_iff` (`Verify/Environment/Lemmas.lean`:43) says a
constant of the abstract environment is a constant of the map; so a clean map is a clean abstract
environment.  Every `Aligned` constructor is covered because the lemma is proved by induction over
all four of them. -/
theorem NoNestedN.of_aligned {safety : DefinitionSafety} {C : ConstMap} {venv : VEnv}
    (H : Aligned safety C venv) (hC : NoNestedMap C) : venv.NoNestedN := by
  intro n hc hx
  obtain ⟨ci, hfind, -⟩ := H.find?_iff.2 hc
  exact hC n ci hfind hx

/-- **The induction, run.**  For every environment in the refinement relation — hence on every
`addDecl` branch that `TrEnv'` models — the abstract invariant follows from the kernel-level one.

The nine `TrEnv'` constructors are discharged by `TrEnv'.aligned`
(`Verify/Environment/Lemmas.lean`:120), which is the induction: `empty`, `ignore`, `axiom`,
`defn`, `thm`, `opaque`, `unsafeDef`, `quot` are proved there, and `induct` goes through
`Aligned.addInduct`.  **`Aligned.addInduct` is `nomatch`** — `AddInduct` has no constructors
today — so the `induct` case is discharged *vacuously*; see §4.1, which says exactly what that
costs and why the statement survives the flip unchanged. -/
theorem NoNestedN.of_trEnv' {safety : DefinitionSafety} {C : ConstMap} {Q : Bool} {venv : VEnv}
    (H : TrEnv' safety C Q venv) (hC : NoNestedMap C) : venv.NoNestedN :=
  NoNestedN.of_aligned H.aligned hC

theorem NoNestedN.of_trEnv {safety : DefinitionSafety} {env : Environment} {venv : VEnv}
    (H : TrEnv safety env venv) (hC : NoNestedMap env.constants) : venv.NoNestedN :=
  NoNestedN.of_trEnv' H hC

end VEnv

/-! ## §3 The implementation side: `NoNestedMap` is *established*

§2's hypothesis is only worth having if the kernel supplies it.  It does: the empty environment
satisfies it, and every `addDecl` branch that goes through `checkConstantVal` preserves it,
*because* of the line PR #46 added.  The monadic plumbing is three small lemmas
(`liftExcept_bind_ok`, `M_bind_ok`, `M_run_ok`) and then each branch is two steps: the name is
clean, and `Environment.add` inserts exactly that name.

Nothing here goes through `TypeChecker.M.WF`, deliberately: `checkConstantVal.WF`
(`Verify/Environment/Checker.lean`:107) needs `ves.WF env`, and `VEnvs.WF` is *unsatisfiable* for
any `env` whose map holds an `.inductInfo` (`VEnvs.WF.no_inductInfo`, `Verify/InductFlip.lean`),
so a name fact routed through it would be vacuous at every environment that has an inductive in
it — i.e. at every real one.  These lemmas are about the raw monadic value and carry no `WF` of
the abstract model at all. -/

theorem liftExcept_bind_ok {α β : Type} {x : Except Exception α} {f : α → TypeChecker.M β}
    {ctx : TypeChecker.Context} {s : TypeChecker.State} {r : β × TypeChecker.State}
    (h : ((liftM x : TypeChecker.M α) >>= f) ctx s = .ok r) :
    ∃ a, x = .ok a ∧ (f a) ctx s = .ok r := by
  cases hx : x with
  | error e => exact absurd h (by simp [hx, liftM, monadLift, MonadLift.monadLift, StateT.lift,
      (· >>= ·), ReaderT.bind, StateT.bind, Except.bind])
  | ok a => exact ⟨a, rfl, by simpa [hx, liftM, monadLift, MonadLift.monadLift, StateT.lift,
      (· >>= ·), ReaderT.bind, StateT.bind, Except.bind, pure, Except.pure] using h⟩

theorem checkConstantVal_noNestedName {env : Environment} {v : ConstantVal} {ap : Bool}
    {ctx : TypeChecker.Context} {s : TypeChecker.State} {r : Unit × TypeChecker.State}
    (h : checkConstantVal env v ap ctx s = .ok r) : ¬ IsNestedName v.name := by
  unfold checkConstantVal at h
  obtain ⟨-, -, h⟩ := liftExcept_bind_ok h
  obtain ⟨u, hn, -⟩ := liftExcept_bind_ok h
  cases u
  exact checkNoNestedAuxName_ok_iff.1 hn

theorem M_bind_ok {α β : Type} {x : TypeChecker.M α} {f : α → TypeChecker.M β}
    {ctx : TypeChecker.Context} {s : TypeChecker.State} {r : β × TypeChecker.State}
    (h : (x >>= f) ctx s = .ok r) :
    ∃ a s', x ctx s = .ok (a, s') ∧ (f a) ctx s' = .ok r := by
  cases hx : x ctx s with
  | error e => exact absurd h (by
      simp [(· >>= ·), ReaderT.bind, StateT.bind, Except.bind, hx])
  | ok p =>
    obtain ⟨a, s'⟩ := p
    exact ⟨a, s', rfl, by
      simpa [(· >>= ·), ReaderT.bind, StateT.bind, Except.bind, hx] using h⟩

theorem Except.bind_ok_inv {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {r : β}
    (h : (x >>= f) = .ok r) : ∃ a, x = .ok a ∧ f a = .ok r := by
  cases x with
  | error e => exact absurd h nofun
  | ok a => exact ⟨a, rfl, h⟩

theorem M_bind_ok' {α β : Type} {x : TypeChecker.M α} {f : α → TypeChecker.M β}
    {ctx : TypeChecker.Context} {s : TypeChecker.State} {r : β × TypeChecker.State}
    (h : ReaderT.bind x f ctx s = .ok r) :
    ∃ a s', x ctx s = .ok (a, s') ∧ (f a) ctx s' = .ok r := M_bind_ok h

theorem M_run_ok {α : Type} {x : TypeChecker.M α} {env : Environment}
    {safety : DefinitionSafety} {lctx : LocalContext} {lparams : List Name} {fuel : FuelConfig}
    {a : α} (h : TypeChecker.M.run env safety lctx lparams fuel x = .ok a) :
    ∃ s', x { env, safety, lctx, lparams, fuel } {} = .ok (a, s') := by
  unfold TypeChecker.M.run StateT.run' at h
  revert h
  cases hr : x ({ env, safety, lctx, lparams, fuel } : TypeChecker.Context) {} with
  | error e => intro h; simp [Functor.map, Except.map] at h
  | ok p => intro h; simp [Functor.map, Except.map] at h; exact ⟨p.2, by subst h; rfl⟩

theorem checkConstantVal_run_noNestedName {env : Environment} {v : ConstantVal} {ap : Bool}
    {safety : DefinitionSafety} {lctx : LocalContext} {lparams : List Name} {fuel : FuelConfig}
    {a : Unit}
    (h : TypeChecker.M.run env safety lctx lparams fuel (checkConstantVal env v ap) = .ok a) :
    ¬ IsNestedName v.name := by
  unfold TypeChecker.M.run StateT.run' at h
  revert h
  cases hr : checkConstantVal env v ap { env, safety, lctx, lparams, fuel } {} with
  | error e => intro h; simp [Functor.map, Except.map] at h
  | ok r => intro _; exact checkConstantVal_noNestedName hr

theorem NoNestedMap.add {env : Environment} {ci : ConstantInfo}
    (hC : NoNestedMap env.constants) (mapWF : env.constants.WF)
    (hn : ¬ IsNestedName ci.name) :
    NoNestedMap (env.add ci).constants := by
  intro n c hf
  rw [show (env.add ci).constants = env.constants.insert ci.name ci from rfl,
    mapWF.find?_insert] at hf
  split at hf
  · rename_i he; rw [beq_iff_eq] at he; exact he ▸ hn
  · exact hC n c hf

/-- **The invariant the implementation carries.**  Well-formedness travels with cleanliness
because the insert lemma needs it; every consumer in this tree has it anyway
(`TrEnv'.map_wf`). -/
structure NoNestedEnv (env : Environment) : Prop where
  wf : env.constants.WF
  clean : NoNestedMap env.constants

theorem NoNestedEnv.add {env : Environment} (h : NoNestedEnv env) {ci : ConstantInfo}
    (hfresh : env.find? ci.name = none) (hn : ¬ IsNestedName ci.name) :
    NoNestedEnv (env.add ci) where
  wf := h.wf.insert ci.name ci (by rwa [← h.wf.find?'_eq_find?])
  clean := h.clean.add h.wf hn

/-- **The empty kernel environment is clean**, so §3's invariant has a starting point and §2's
hypothesis is not unsatisfiable. -/
theorem NoNestedEnv.empty {m : Name} {tl : UInt32} :
    NoNestedEnv (Kernel.Environment.empty m tl) where
  wf := ⟨rfl, rfl⟩
  clean := NoNestedMap.of_find?_none fun n =>
    show ({} : ConstMap).find? n = none by simp [SMap.find?]

theorem NoNestedEnv.of_markQuotInit {env : Environment} (h : NoNestedEnv env) :
    NoNestedEnv (markQuotInit env) := by
  constructor
  · show env.constants.WF
    exact h.wf
  · show NoNestedMap env.constants
    exact h.clean

theorem checkConstantVal_find?_none {env : Environment} {v : ConstantVal} {ap : Bool}
    {ctx : TypeChecker.Context} {s : TypeChecker.State} {r : Unit × TypeChecker.State}
    (mapWF : env.constants.WF) (h : checkConstantVal env v ap ctx s = .ok r) :
    env.find? v.name = none := by
  unfold checkConstantVal at h
  obtain ⟨u, hk, -⟩ := liftExcept_bind_ok h
  exact (checkName.WF mapWF v.name ap u hk).1

/-- **The `axiomDecl` branch.** -/
theorem addAxiom_noNestedEnv {env env' : Environment} {v : AxiomVal} {fuel : FuelConfig}
    (hC : NoNestedEnv env) (h : addAxiom env v true fuel = .ok env') : NoNestedEnv env' := by
  unfold addAxiom at h
  simp only [if_true, bind, Except.bind, pure, Except.pure] at h
  split at h
  · exact absurd h nofun
  · rename_i hr
    cases h
    obtain ⟨s', hr⟩ := M_run_ok hr
    exact hC.add (checkConstantVal_find?_none hC.wf hr) (checkConstantVal_noNestedName hr)

/-- **The `thmDecl` branch.** -/
theorem addTheorem_noNestedEnv {env env' : Environment} {v : TheoremVal} {fuel : FuelConfig}
    (hC : NoNestedEnv env) (h : addTheorem env v true fuel = .ok env') : NoNestedEnv env' := by
  unfold addTheorem at h
  simp only [if_true, bind, Except.bind, pure, Except.pure] at h
  split at h
  · exact absurd h nofun
  · rename_i hrun
    cases h
    obtain ⟨_, hr⟩ := M_run_ok hrun
    obtain ⟨_, _, hcv, _⟩ := M_bind_ok' hr
    exact hC.add (checkConstantVal_find?_none hC.wf hcv) (checkConstantVal_noNestedName hcv)

/-- **The `opaqueDecl` branch.** -/
theorem addOpaque_noNestedEnv {env env' : Environment} {v : OpaqueVal} {fuel : FuelConfig}
    (hC : NoNestedEnv env) (h : addOpaque env v true fuel = .ok env') : NoNestedEnv env' := by
  unfold addOpaque at h
  simp only [if_true, bind, Except.bind, pure, Except.pure] at h
  split at h
  · exact absurd h nofun
  · rename_i hrun
    cases h
    obtain ⟨_, hr⟩ := M_run_ok hrun
    obtain ⟨_, _, hcv, _⟩ := M_bind_ok' hr
    exact hC.add (checkConstantVal_find?_none hC.wf hcv) (checkConstantVal_noNestedName hcv)

/-- **The `defnDecl` branch**, both safety arms.  The `unsafe` arm runs `checkConstantVal` on
`env` itself before adding the temporary axiom; the safe arm runs it under
`checkPrimitiveDef`'s result, so one extra `>>=` has to be peeled. -/
theorem addDefinition_noNestedEnv {env env' : Environment} {v : DefinitionVal} {fuel : FuelConfig}
    (hC : NoNestedEnv env) (h : addDefinition env v true fuel = .ok env') : NoNestedEnv env' := by
  unfold addDefinition at h
  simp only [if_true, bind, Except.bind, pure, Except.pure] at h
  split at h
  · split at h
    · exact absurd h nofun
    · rename_i hrun
      split at h
      · exact absurd h nofun
      · split at h
        · exact absurd h nofun
        · cases h
          obtain ⟨_, hr⟩ := M_run_ok hrun
          exact hC.add (checkConstantVal_find?_none hC.wf hr)
            (checkConstantVal_noNestedName hr)
  · split at h
    · exact absurd h nofun
    · rename_i hrun
      cases h
      obtain ⟨_, hr⟩ := M_run_ok hrun
      obtain ⟨_, _, _, hr2⟩ := M_bind_ok' hr
      obtain ⟨_, _, hcv, _⟩ := M_bind_ok' hr2
      exact hC.add (checkConstantVal_find?_none hC.wf hcv) (checkConstantVal_noNestedName hcv)

/-- **The `quotDecl` branch.**  `addQuot_eq` (`Verify/QuotConsts.lean`:493) computes the four
`add`s out of the `ExprBuildT` block, so the names are the literals ``Quot``, ``Quot.mk``,
``Quot.lift``, ``Quot.ind`` and cleanliness is `by decide`.  The freshness each `add` needs at the
*intermediate* environments comes from `Environment.find?_add_of_ne`, i.e. from the four
`checkName`s plus four name disequalities. -/
theorem NoNestedEnv.addQuotConsts {env : Environment} (hC : NoNestedEnv env)
    (f1 : env.find? ``Quot = none) (f2 : env.find? ``Quot.mk = none)
    (f3 : env.find? ``Quot.lift = none) (f4 : env.find? ``Quot.ind = none) :
    NoNestedEnv (markQuotInit ((((env.add quotCI).add quotMkCI).add quotLiftCI).add quotIndCI)) := by
  have C1 : NoNestedEnv (env.add quotCI) := hC.add f1 (by decide)
  have g2 : (env.add quotCI).find? ``Quot.mk = none :=
    Environment.find?_add_of_ne hC.wf quotCI f1 (by decide) f2
  have g3 : (env.add quotCI).find? ``Quot.lift = none :=
    Environment.find?_add_of_ne hC.wf quotCI f1 (by decide) f3
  have g4 : (env.add quotCI).find? ``Quot.ind = none :=
    Environment.find?_add_of_ne hC.wf quotCI f1 (by decide) f4
  have C2 : NoNestedEnv ((env.add quotCI).add quotMkCI) := C1.add g2 (by decide)
  have k3 : ((env.add quotCI).add quotMkCI).find? ``Quot.lift = none :=
    Environment.find?_add_of_ne C1.wf quotMkCI g2 (by decide) g3
  have k4 : ((env.add quotCI).add quotMkCI).find? ``Quot.ind = none :=
    Environment.find?_add_of_ne C1.wf quotMkCI g2 (by decide) g4
  have C3 : NoNestedEnv (((env.add quotCI).add quotMkCI).add quotLiftCI) := C2.add k3 (by decide)
  have m4 : (((env.add quotCI).add quotMkCI).add quotLiftCI).find? ``Quot.ind = none :=
    Environment.find?_add_of_ne C2.wf quotLiftCI k3 (by decide) k4
  exact (C3.add (ci := quotIndCI) m4 (by decide)).of_markQuotInit

/-- **The `quotDecl` branch.**  `addQuot_eq` (`Verify/QuotConsts.lean`:493) computes the four
`add`s out of the `ExprBuildT` block, so the added names are the literals ``Quot``, ``Quot.mk``,
``Quot.lift``, ``Quot.ind`` and cleanliness is `by decide`.  The freshness each `add` needs at the
*intermediate* environments comes from `Environment.find?_add_of_ne`, i.e. from the four
`checkName`s plus four name disequalities. -/
theorem addQuot_noNestedEnv {env env' : Environment}
    (hC : NoNestedEnv env) (h : Environment.addQuot env = .ok env') : NoNestedEnv env' := by
  rw [addQuot_eq] at h
  split at h
  · cases h; exact hC
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · exact absurd h nofun
  split at h
  · exact absurd h nofun
  rename_i h1
  split at h
  · exact absurd h nofun
  rename_i h2
  split at h
  · exact absurd h nofun
  rename_i h3
  split at h
  · exact absurd h nofun
  rename_i h4
  cases h
  exact hC.addQuotConsts (checkName.WF hC.wf ``Quot false _ h1).1
    (checkName.WF hC.wf ``Quot.mk false _ h2).1 (checkName.WF hC.wf ``Quot.lift false _ h3).1
    (checkName.WF hC.wf ``Quot.ind false _ h4).1

/-- **The map side of the `mutualDefnDecl` branch.**  `addMutual` returns
`vs.foldl (fun e v => e.add (.defnInfo v)) env`; this says the fold keeps the invariant, given the
three facts the checker's header loop is there to establish.  Compare `insertDefs_wf`
(`Verify/Environment/Extension.lean`:213), which is the same fold for well-formedness alone. -/
theorem NoNestedEnv.foldl_add : ∀ {vs : List DefinitionVal} {env : Environment},
    NoNestedEnv env → (∀ v ∈ vs, ¬ IsNestedName v.name) →
    (∀ v ∈ vs, env.find? v.name = none) → (vs.map (·.name)).Nodup →
    NoNestedEnv (vs.foldl (fun e v => e.add (.defnInfo v)) env)
  | [], _, h, _, _, _ => h
  | v :: vs, env, h, hn, hfresh, hnd => by
    rw [List.map_cons, List.nodup_cons] at hnd
    show NoNestedEnv (vs.foldl (fun e w => e.add (.defnInfo w)) (env.add (.defnInfo v)))
    refine NoNestedEnv.foldl_add (h.add (ci := .defnInfo v) (hfresh v List.mem_cons_self)
        (hn v List.mem_cons_self)) (fun w hw => hn w (List.mem_cons_of_mem _ hw))
      (fun w hw => ?_) hnd.2
    refine Environment.find?_add_of_ne h.wf (.defnInfo v) (hfresh v List.mem_cons_self) ?_
      (hfresh w (List.mem_cons_of_mem _ hw))
    exact fun he => hnd.1 (List.mem_map.2 ⟨w, hw, he.symm⟩)

/-- **The one residual on the `mutualDefnDecl` branch.**  `addMutual`'s header loop runs
`checkConstantVal env v.toConstantVal` on every member and rejects a repeated name, so it
establishes exactly this; what is missing is the *extraction*, an `M`-monad `forIn` induction with
the `found` accumulator threaded through three `if`s — the `Except`-level pattern of
`guardLoop_noNested` (`Verify/Inductive/RestoreFaithful.lean` §1.1) lifted to
`ReaderT Context (StateT State (Except Exception))`.

This is **unproved, not false**: every conjunct is a postcondition of a check the loop actually
performs (`Lean4Lean/Environment.lean`:86-104). -/
def MutualNamesGate : Prop :=
  ∀ {env env' : Environment} {vs : List DefinitionVal} {fuel : FuelConfig},
    addMutual env vs true fuel = .ok env' →
      (∀ v ∈ vs, ¬ IsNestedName v.name ∧ env.find? v.name = none) ∧ (vs.map (·.name)).Nodup

/-- **The `mutualDefnDecl` branch**, reduced to `MutualNamesGate` and nothing else: the map side
is `NoNestedEnv.foldl_add`, proved above. -/
theorem addMutual_noNestedEnv (G : MutualNamesGate) {env env' : Environment}
    {vs : List DefinitionVal} {fuel : FuelConfig}
    (hC : NoNestedEnv env) (h : addMutual env vs true fuel = .ok env') : NoNestedEnv env' := by
  obtain ⟨hv, hnd⟩ := G h
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

/-- **The residual on the `inductDecl` branch**, stated as the *map* side of the inductive step:
`addInductive` adds no name beyond the block's own name budget.

This is the kernel-level half of `AddInductStagesR` (`Verify/Environment/InductR.lean`:102), the
relation `AddInduct` is meant to become; `docs/handoff-addinduct.md` prices that flip at seven
files.  It is **unproved, not false** — `indDeclNamesN` is exactly the list the nested path
declares, auxiliary recursors `I.rec_k` included (`TrIndDeclN.mem_indDeclNamesN`,
`Verify/Environment/InductR.lean`:329).

Note what is *not* in this gate: the *name* condition on the block.  That is already a theorem
(`addInductive_WF_noNestedDeclNames`, §1 of `RestoreFaithful.lean`), and the proof below is where
the two meet. -/
def InductiveMapGate : Prop :=
  ∀ {env env' : Environment} {lparams : List Name} {np : Nat} {types : List InductiveType}
    {iu ap : Bool} {fuel : FuelConfig},
    Environment.addInductive env lparams np types iu ap fuel = .ok env' → env.constants.WF →
      env'.constants.WF ∧ ∀ n ci, env'.constants.find? n = some ci →
        env.constants.find? n = some ci ∨ ∃ k, n ∈ Lean4Lean.indDeclNamesN types k

/-- **The `inductDecl` branch**, reduced to `InductiveMapGate` and nothing else.  The name half is
not assumed: it is `addInductive_WF_noNestedDeclNames` — i.e. `checkNoNestedAuxName` at
`Lean4Lean/Inductive/Add.lean`:1114 and :1119 — pushed through
`NoNestedDeclNames.indDeclNamesN`. -/
theorem addInductive_noNestedEnv (G : InductiveMapGate) {env env' : Environment}
    {lparams : List Name} {np : Nat} {types : List InductiveType} {iu ap : Bool}
    {fuel : FuelConfig} (hC : NoNestedEnv env)
    (h : Environment.addInductive env lparams np types iu ap fuel = .ok env') :
    NoNestedEnv env' := by
  obtain ⟨hwf, hmap⟩ := G h hC.wf
  have hgate : NoNestedDeclNames types := addInductive_WF_noNestedDeclNames _ h
  refine ⟨hwf, fun n ci hf => ?_⟩
  rcases hmap n ci hf with h1 | ⟨k, hk⟩
  · exact hC.clean n ci h1
  · exact hgate.indDeclNamesN n hk

/-- **`NoNestedMap` is established on every `addDecl` branch.**  Five branches unconditionally;
`mutualDefnDecl` on `MutualNamesGate` (the header loop's postcondition, unproved) and `inductDecl`
on `InductiveMapGate` (the map side of the inductive step, unproved).  Neither gate is a name
condition: both name conditions are theorems, and PR #46 is why. -/
theorem addDecl_noNestedEnv (Gm : MutualNamesGate) (Gi : InductiveMapGate)
    {env env' : Environment} {d : Declaration} {fuel : FuelConfig}
    (hC : NoNestedEnv env) (h : Lean4Lean.addDecl env d true fuel = .ok env') :
    NoNestedEnv env' := by
  unfold Lean4Lean.addDecl at h
  split at h
  · exact addAxiom_noNestedEnv hC h
  · exact addDefinition_noNestedEnv hC h
  · exact addTheorem_noNestedEnv hC h
  · exact addOpaque_noNestedEnv hC h
  · exact addMutual_noNestedEnv Gm hC h
  · exact addQuot_noNestedEnv hC h
  · obtain ⟨_, _, h⟩ := Except.bind_ok_inv h
    exact addInductive_noNestedEnv Gi hC h

/-- **The headline.**  From a clean kernel environment, one accepted `addDecl`, and the refinement
relation at the result: the abstract environment satisfies `VEnv.NoNestedN`.  This is what §2 of
`RestoreFaithful.lean` needed and what nothing supplied before PR #46. -/
theorem VEnv.NoNestedN.of_addDecl (Gm : MutualNamesGate) (Gi : InductiveMapGate)
    {env env' : Environment} {d : Declaration} {fuel : FuelConfig} {safety : DefinitionSafety}
    {venv : VEnv} (hC : NoNestedEnv env)
    (h : Lean4Lean.addDecl env d true fuel = .ok env') (H : TrEnv safety env' venv) :
    venv.NoNestedN :=
  VEnv.NoNestedN.of_trEnv H (addDecl_noNestedEnv Gm Gi hC h).clean

/-- …and it survives an arbitrary *sequence* of declarations, which is the shape the kernel is
actually driven in. -/
theorem addDecls_noNestedEnv (Gm : MutualNamesGate) (Gi : InductiveMapGate) {fuel : FuelConfig} :
    ∀ {ds : List Declaration} {env env' : Environment}, NoNestedEnv env →
      ds.foldlM (fun e d => Lean4Lean.addDecl e d true fuel) env = .ok env' → NoNestedEnv env'
  | [], _, _, hC, h => by cases h; exact hC
  | d :: ds, env, _, hC, h => by
    obtain ⟨e₁, h1, h2⟩ := Except.bind_ok_inv h
    exact addDecls_noNestedEnv Gm Gi (addDecl_noNestedEnv Gm Gi hC h1) h2

/-! ## §4 The limits of the result, proved where they can be

Three, and each is a theorem or a measurement rather than a caveat.

### §4.1 The `induct` case of §2 is discharged **vacuously** today

`TrEnv'.aligned`'s `induct` arm goes through `Aligned.addInduct`, whose proof is `nomatch H`
because `AddInduct` has no constructors.  So `NoNestedN.of_trEnv'` is, today, a statement about
environments built without `TrEnv'.induct`.  This is *inherited*, not introduced: it is the same
emptiness that makes `VEnvs.WF env` unsatisfiable for a map holding an `.inductInfo`
(`VEnvs.WF.no_inductInfo`) and `addDecl.WF`'s `inductDecl` branch false rather than open
(`Verify/InductFlip.lean`:360).

It is also the reason `of_trEnv'` is the right shape: when the flip lands, the `induct` arm of
`TrEnv'.aligned` is repaired by `Aligned.addInductStages` (`Verify/TypeChecker/Reduce.lean`), and
**nothing in this file changes** — `of_trEnv'` cites `TrEnv'.aligned` and does not case on
`TrEnv'` itself.  That is deliberate: routing the induction through `Aligned` means the vacuity
lives in one place that somebody else is already paid to fix. -/

/-- The emptiness, machine-checked rather than asserted. -/
theorem addInduct_isEmpty {C₁ C₂ : Lean.ConstMap} {venv₁ venv₂ : VEnv} {decl : VInductDecl'} :
    ¬ AddInduct C₁ venv₁ decl C₂ venv₂ := nofun

/-- **Why §3 does not route through `TypeChecker.M.WF`, instantiated rather than quoted.**
`checkConstantVal.WF` (`Verify/Environment/Checker.lean`:107) — the natural place to strengthen
`checkConstantValCore.WF`'s `Except.WF.trivial` step into the name fact — carries `wf : ves.WF env`,
and that premise is *refuted* by a single `.inductInfo` in the map.  So a name fact obtained that
way would be vacuous at every environment with an inductive in it, i.e. at every real one.  This is
`VEnvs.WF.no_inductInfo` (`Verify/InductFlip.lean`:366) fired, rather than its docstring believed. -/
theorem venvsWF_refuted_at_inductInfo {ves : VEnvs} {env : Environment} {n : Name}
    {v : Lean.InductiveVal} (hf : env.constants.find? n = some (.inductInfo v)) : ¬ ves.WF env :=
  fun wf => wf.no_inductInfo hf

/-! ### §4.2 The two gates, and that they are not name conditions

`MutualNamesGate` and `InductiveMapGate` are what remains of §3.  Both are about *which names a
branch adds*, not about whether a name is clean: the clean-name facts are theorems
(`checkConstantVal_noNestedName` here, `addInductive_WF_noNestedDeclNames` in `RestoreFaithful`).
So PR #46 really did remove the obstruction §5 named; what is left is bookkeeping about the
constant map, and for `inductDecl` that bookkeeping is the seven-file flip.

### §4.3 The invariant is bought by the check, and lost without it

`addDecl … (check := false)` runs no `checkConstantVal`, so it accepts `axiom _nested.zzz` and the
map is dirty one step later.  This is not a caveat but a refutation, and it is the exact statement
`NestedWit.noNestedN_not_preserved` (`Verify/Inductive/ProjNoNested.lean`:604) makes on the
abstract side, met here on the kernel side. -/

/-- `axiom _nested.zzz : Prop`, the hostile declaration. -/
def nestedAxWit : AxiomVal :=
  { name := `_nested.zzz, levelParams := [], type := .sort .zero, isUnsafe := false }

theorem addAxiom_nestedAxWit_unchecked :
    addAxiom (Kernel.Environment.empty `main) nestedAxWit false =
      .ok ((Kernel.Environment.empty `main).add (.axiomInfo nestedAxWit)) := rfl

/-- **The check is load-bearing.**  With `check := false` the invariant is *not* preserved, from an
environment where it held. -/
theorem noNestedEnv_not_preserved_unchecked :
    ¬ ∀ {env env' : Environment} {v : AxiomVal} {fuel : FuelConfig},
        NoNestedEnv env → addAxiom env v false fuel = .ok env' → NoNestedEnv env' := by
  intro H
  have hbad := (H (v := nestedAxWit) (fuel := {}) NoNestedEnv.empty
    addAxiom_nestedAxWit_unchecked).clean `_nested.zzz (.axiomInfo nestedAxWit) ?_ (by decide)
  · exact hbad
  · show SMap.find? (SMap.insert (Kernel.Environment.empty `main).constants
      nestedAxWit.name (.axiomInfo nestedAxWit)) `_nested.zzz = _
    rw [(show (Kernel.Environment.empty `main).constants.WF from ⟨rfl, rfl⟩).find?_insert]
    rfl

/-! ## §5 The firings — closed, and at more than one environment

"Instantiate, don't admire": a statement true only because its hypotheses are unsatisfiable is a
defect.  §5.1 fires §2 at the *empty* kernel environment and composes it with `RestoreFaithful`'s
nested-block firing; §5.2 fires it at a **five-constant** environment, so the `∀ n` is not
quantifying over nothing; §5.3 checks by `#eval` that `addDecl_noNestedEnv`'s own hypothesis is
satisfiable, i.e. that `addDecl` really does accept a clean declaration from the empty
environment. -/

/-! ### §5.1 At the empty kernel environment, composed with the nested block -/

theorem trEnv_empty_kernel {safety : DefinitionSafety} {m : Name} {tl : UInt32} :
    TrEnv safety (Kernel.Environment.empty m tl) VEnv.empty :=
  TrEnv'.empty ⟨rfl, rfl⟩ fun n => show ({} : ConstMap).find? n = none by simp [SMap.find?]

open InductiveDeclExamples in
/-- **The composition, end to end.**  The kernel-level condition holds of the empty environment;
§2 turns it into `VEnv.NoNestedN` of the model; and the *restored* nested step on the real nested
block keeps that, while the *unrestored* one destroys it.  Every conjunct is closed: no
environment variable, no unsatisfiable premise.

The last two conjuncts are `ntree_restoration_keeps_the_environment_clean`
(`RestoreFaithful.lean` §4) — the existing firing at the real nested block — reached here *through*
the new kernel-level route rather than from `NestedWit.empty_noNestedN`. -/
theorem clean_kernel_env_survives_ntree_restoration :
    NoNestedMap (Kernel.Environment.empty `main).constants ∧
      VEnv.empty.NoNestedN ∧
      (∃ e, VEnv.empty.addInductR ntreeAux ntreeK ntreeRestore = some e ∧ e.NoNestedN) ∧
      (∃ e, VEnv.empty.addIndTypes ntreeAux = some e ∧ ¬ e.NoNestedN) :=
  ⟨NoNestedEnv.empty.clean,
   VEnv.NoNestedN.of_trEnv (safety := .safe) (trEnv_empty_kernel (m := `main) (tl := 0))
     (NoNestedEnv.empty (m := `main) (tl := 0)).clean,
   ntree_restoration_keeps_the_environment_clean.1,
   ntree_restoration_keeps_the_environment_clean.2⟩

/-! ### §5.2 At a five-constant environment: `Eq` plus the four quotient constants

`QuotWit.trEnv_addQuot_wit` (`Verify/QuotConsts.lean`:776) is a **closed** `TrEnv` at the
environment `markQuotInit (envEq.add quotCI |>.add quotMkCI |>.add quotLiftCI |>.add quotIndCI)`,
whose model really holds five constants and a rule (`quotVEnv_venvEq_contents`).  So §2 fires
there with a non-empty `∀ n`. -/

theorem quotWit_noNestedEnv : NoNestedEnv
    (markQuotInit ((((QuotWit.envEq.add quotCI).add quotMkCI).add quotLiftCI).add
      quotIndCI)) :=
  (NoNestedEnv.empty.add (ci := .axiomInfo QuotWit.eqAx) (QuotWit.find?_env0 _)
      (by decide)).addQuotConsts
    QuotWit.fresh1 QuotWit.fresh2 QuotWit.fresh3 QuotWit.fresh4

/-- **The firing.**  `NoNestedN` of the model, *plus* the five names it is actually about — so the
universally quantified statement is not vacuous at this environment. -/
theorem quotWit_noNestedN_fires {safety : DefinitionSafety} :
    (quotVEnv QuotWit.venvEq).NoNestedN ∧
      (quotVEnv QuotWit.venvEq).contains ``Eq ∧
      (quotVEnv QuotWit.venvEq).contains ``Quot ∧
      (quotVEnv QuotWit.venvEq).contains ``Quot.mk ∧
      (quotVEnv QuotWit.venvEq).contains ``Quot.lift ∧
      (quotVEnv QuotWit.venvEq).contains ``Quot.ind :=
  ⟨VEnv.NoNestedN.of_trEnv (safety := safety) QuotWit.trEnv_addQuot_wit quotWit_noNestedEnv.clean,
   ⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩⟩

/-! ### §5.3 The hypotheses are satisfiable at `addDecl`, self-checking

`addDecl_noNestedEnv` is an implication; this checks that its antecedent can hold.  If
`Lean4Lean.addDecl` ever *rejected* a clean axiom from the empty environment, every statement in §3
would be conditional on nothing, and the build fails here rather than in prose.  The second
`unless` is the mirror of `RestoreFaithful.lean` §5.1's, restated locally so that this file does not
depend on another file's gate for its own non-vacuity. -/
#eval show Lean.CoreM Unit from do
  let kenv := Lean.Kernel.Environment.empty `main
  let ok := Lean4Lean.addDecl kenv (.axiomDecl
    { name := `Zzz, levelParams := [], type := .sort .zero, isUnsafe := false })
  let bad := Lean4Lean.addDecl kenv (.axiomDecl Lean4Lean.nestedAxWit)
  unless ok.toOption.isSome do
    throwError "NoNestedAll/gate: Lean4Lean.addDecl REJECTS `axiom Zzz : Prop` from the empty \
      environment -- addDecl_noNestedEnv's hypothesis is unsatisfiable and every §5 firing is void"
  unless bad.toOption.isNone do
    throwError "NoNestedAll/gate: Lean4Lean.addDecl ACCEPTS `axiom _nested.zzz` -- \
      checkNoNestedAuxName has been dropped from checkConstantVal, so \
      checkConstantVal_noNestedName is false and all of §3 is void"
  let some env' := ok.toOption | throwError "unreachable"
  let dirty := env'.constants.toList.filter fun (n, _) => (`_nested).isPrefixOf n
  unless dirty.isEmpty do
    throwError "NoNestedAll/gate: the environment after one accepted addDecl holds \
      {dirty.length} `_nested`-prefixed constants -- NoNestedMap is false of a map addDecl built"
  Lean.logInfo "NoNestedAll/gate: `axiom Zzz : Prop` is ACCEPTED from the empty environment and \
    the resulting map holds 0 `_nested` constants; `axiom _nested.zzz` is REJECTED -- so §3's \
    invariant is established, not merely stated ✓"

#print axioms Lean4Lean.VEnv.NoNestedN.of_aligned
#print axioms Lean4Lean.VEnv.NoNestedN.of_trEnv'
#print axioms Lean4Lean.VEnv.NoNestedN.of_trEnv
#print axioms Lean4Lean.checkConstantVal_noNestedName
#print axioms Lean4Lean.addAxiom_noNestedEnv
#print axioms Lean4Lean.addDefinition_noNestedEnv
#print axioms Lean4Lean.addTheorem_noNestedEnv
#print axioms Lean4Lean.addOpaque_noNestedEnv
#print axioms Lean4Lean.addQuot_noNestedEnv
#print axioms Lean4Lean.addMutual_noNestedEnv
#print axioms Lean4Lean.addInductive_noNestedEnv
#print axioms Lean4Lean.addDecl_noNestedEnv
#print axioms Lean4Lean.addDecls_noNestedEnv
#print axioms Lean4Lean.VEnv.NoNestedN.of_addDecl
#print axioms Lean4Lean.addInduct_isEmpty
#print axioms Lean4Lean.noNestedEnv_not_preserved_unchecked
#print axioms Lean4Lean.clean_kernel_env_survives_ntree_restoration
#print axioms Lean4Lean.quotWit_noNestedN_fires

end Lean4Lean
